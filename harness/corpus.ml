(* Parser for the djot.js ".test" corpus format.

   A case is:
     <pretext lines>
     ```[options]        <- fence of >= 3 backticks, optional option string
     <djot input>
     .                   <- or "!" introducing filters (unsupported here)
     <expected HTML>
     ```                 <- fence of the same length
   Mirrors parseTests in djot.js/src/functional.spec.ts. *)

type case = {
  file : string;
  linenum : int;
  options : string;
  input : string;
  expected : string;
}

let read_lines path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  String.split_on_char '\n' s

let fence_of line =
  let len = String.length line in
  let rec ticks i = if i < len && line.[i] = '`' then ticks (i + 1) else i in
  let n = ticks 0 in
  if n >= 3 then Some (n, String.trim (String.sub line n (len - n))) else None

let parse_file path =
  let lines = Array.of_list (read_lines path) in
  let total = Array.length lines in
  let cases = ref [] in
  let idx = ref 0 in
  let buf = Buffer.create 256 in
  let collect stop =
    Buffer.clear buf;
    while !idx < total && not (stop lines.(!idx)) do
      Buffer.add_string buf lines.(!idx);
      Buffer.add_char buf '\n';
      incr idx
    done;
    Buffer.contents buf
  in
  while !idx < total do
    (* skip pretext until a fence line *)
    while !idx < total && fence_of lines.(!idx) = None do incr idx done;
    if !idx < total then begin
      let n, options =
        match fence_of lines.(!idx) with Some f -> f | None -> assert false
      in
      let linenum = !idx + 1 in
      incr idx;
      let input = collect (fun l -> l = "." || l = "!") in
      (* filters ("!") unsupported: skip to closing fence and drop the case *)
      let filtered = !idx < total && lines.(!idx) = "!" in
      if !idx < total then incr idx;
      let closing l =
        match fence_of l with Some (m, "") -> m >= n | _ -> false
      in
      let expected = collect closing in
      if !idx < total then incr idx;
      if not filtered then
        cases := { file = path; linenum; options; input; expected } :: !cases
    end
  done;
  List.rev !cases
