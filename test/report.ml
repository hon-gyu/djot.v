(* ai-disclosure: autonomous *)

(* Output that goes to stdout and, with --report FILE, to a file too. *)

type t = { buf : Buffer.t; path : string }

let create path = { buf = Buffer.create 4096; path }

let out r fmt =
  Printf.ksprintf (fun s -> print_string s; Buffer.add_string r.buf s) fmt

let save r =
  if r.path <> "" then
    Out_channel.with_open_text r.path (fun oc ->
      Out_channel.output_string oc (Buffer.contents r.buf))
