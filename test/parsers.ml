(* ai-disclosure: autonomous *)

(* The parsers the tests compare, each a function from djot to HTML: the
   extracted Gallina parser, called directly, and djot.js, run as a node
   subprocess. *)

let root =
  (* tests run from _build/default/test; walk up to the repo root *)
  let rec find dir =
    if Sys.file_exists (Filename.concat dir "dune-project")
       && Sys.file_exists (Filename.concat dir "djot.js")
    then dir
    else
      let parent = Filename.dirname dir in
      if parent = dir then failwith "repo root not found" else find parent
  in
  find (Sys.getcwd ())

let ( / ) = Filename.concat

(* stdin via a temp file rather than a pipe: no write/read interleaving,
   no deadlock risk regardless of input size *)
let run_process argv input =
  let tmp = Filename.temp_file "djotv" ".in" in
  let oc = open_out_bin tmp in
  output_string oc input;
  close_out oc;
  let fd_in = Unix.openfile tmp [ Unix.O_RDONLY ] 0 in
  let stdout_r, stdout_w = Unix.pipe () in
  let pid = Unix.create_process argv.(0) argv fd_in stdout_w Unix.stderr in
  Unix.close fd_in;
  Unix.close stdout_w;
  let ic = Unix.in_channel_of_descr stdout_r in
  let buf = Buffer.create 1024 in
  (try
     while true do
       Buffer.add_channel buf ic 1
     done
   with End_of_file -> ());
  close_in ic;
  let _, status = Unix.waitpid [] pid in
  Sys.remove tmp;
  match status with
  | Unix.WEXITED 0 -> Ok (Buffer.contents buf)
  | Unix.WEXITED n -> Error (Printf.sprintf "exit %d" n)
  | _ -> Error "killed"

(* Length-delimited framing, for a whole batch in one process: for each
   document, "<byte-length>\n" then that many bytes.  Byte lengths rather
   than a separator: a djot document may contain any bytes, so no
   sentinel is safe.  `djotjs.mjs --batch` and `convert --batch` both
   speak it. *)
let frame docs =
  let buf = Buffer.create 4096 in
  List.iter
    (fun d ->
      Buffer.add_string buf (string_of_int (String.length d));
      Buffer.add_char buf '\n';
      Buffer.add_string buf d)
    docs;
  Buffer.contents buf

(* Stops at the first malformed or truncated frame. *)
let unframe s =
  let n = String.length s in
  let rec go acc at =
    if at >= n then List.rev acc
    else
      match String.index_from_opt s at '\n' with
      | None -> List.rev acc
      | Some nl ->
        match int_of_string_opt (String.sub s at (nl - at)) with
        | Some len when nl + 1 + len <= n ->
          go (String.sub s (nl + 1) len :: acc) (nl + 1 + len)
        | _ -> List.rev acc
  in
  go [] 0

type t = {
  name : string;
  run : string -> (string, string) result;
  (* whole batch in one process, when the parser supports it; the fallback
     is one process per document, which node startup makes untenable at
     corpus scale *)
  run_batch : (string list -> (string, string) result list) option;
}

let gallina =
  { name = "gallina";
    run = (fun s -> Ok (Djot.Html.convert s));
    run_batch = None }

let djotjs =
  let script = root / "test" / "djotjs" / "djotjs.mjs" in
  { name = "djotjs";
    run = (fun s -> run_process [| "node"; script |] s);
    run_batch =
      Some
        (fun docs ->
          match run_process [| "node"; script; "--batch" |] (frame docs) with
          | Error e -> List.map (fun _ -> Error e) docs
          | Ok out ->
            let outs = unframe out in
            if List.length outs <> List.length docs then
              List.map
                (fun _ ->
                  Error
                    (Printf.sprintf "batch returned %d of %d"
                       (List.length outs) (List.length docs)))
                docs
            else List.map (fun o -> Ok o) outs) }

let run_all p docs =
  match p.run_batch with
  | Some f -> f docs
  | None -> List.map p.run docs
