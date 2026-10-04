(* ai-disclosure: ai-generated *)

open Djot
module Switch = Profile.Switch
module Delimiter = Profile.Delimiter

let options (p : Profile.t) = (p :> Kernel.Profile.options)
let presets = [ "djot", Profile.djot; "markdown-like", Profile.markdown_like ]

let preset p =
  List.find_map (fun (name, q) -> if Profile.equal p q then Some name else None) presets
;;

let syntaxes = [ "bare", `Bare; "braced", `Braced; "off", `Off ]

let spelling d p =
  let c, width, syntax = Delimiter.spelling d p in
  String.make width c, fst (List.find (fun (_, s) -> s = syntax) syntaxes)
;;

let respell d run syntax p =
  match List.assoc_opt syntax syntaxes with
  | None -> Error (Printf.sprintf "%s: bare, braced or off" syntax)
  | Some syntax ->
    if run = "" || String.exists (fun c -> c <> run.[0]) run
    then Error "a delimiter is one character, repeated"
    else Profile.with_delimiter d run.[0] ~width:(String.length run) syntax p
;;

let to_string p =
  let switch s =
    let v = Switch.get s p in
    if v = Switch.get s Profile.djot
    then None
    else Some (Switch.name s ^ "=" ^ if v then "on" else "off")
  in
  let delimiter d =
    let run, syntax = spelling d p in
    if (run, syntax) = spelling d Profile.djot
    then None
    else Some (Printf.sprintf "%s=%s:%s" (Delimiter.name d) run syntax)
  in
  String.concat
    " "
    (List.filter_map switch Profile.switches
     @ List.filter_map delimiter Profile.delimiters)
;;

let ( let* ) = Result.bind

let of_string s =
  let words = List.filter (fun w -> w <> "") (String.split_on_char ' ' s) in
  let word w =
    match String.index_opt w '=' with
    | None -> Error (w ^ ": expected name=value")
    | Some i -> Ok (String.sub w 0 i, String.sub w (i + 1) (String.length w - i - 1))
  in
  let switch p (name, value) =
    match List.find_opt (fun s -> Switch.name s = name) Profile.switches, value with
    | Some s, "on" -> Ok (Switch.set s true p)
    | Some s, "off" -> Ok (Switch.set s false p)
    | Some _, _ -> Error (name ^ ": on or off")
    | None, _ -> Error (name ^ ": no such setting")
  in
  let delimiter (name, value) =
    match
      ( List.find_opt (fun d -> Delimiter.name d = name) Profile.delimiters
      , String.rindex_opt value ':' )
    with
    | Some d, Some i ->
      Some (d, String.sub value 0 i, String.sub value (i + 1) (String.length value - i - 1))
    | _ -> None
  in
  let rec pairs = function
    | [] -> Ok []
    | w :: ws ->
      let* p = word w in
      let* ps = pairs ws in
      Ok (p :: ps)
  in
  let* pairs = pairs words in
  let delimiters = List.filter_map delimiter pairs in
  let switches = List.filter (fun p -> delimiter p = None) pairs in
  let* p = List.fold_left (fun p s -> Result.bind p (fun p -> switch p s)) (Ok Profile.djot) switches in
  (* Rows are switched off before any is respelled, so that two rows can
     swap characters. *)
  let off p (d, _, _) =
    let run, _ = spelling d p in
    Result.value (respell d run "off" p) ~default:p
  in
  let p = List.fold_left off p delimiters in
  List.fold_left
    (fun p (d, run, syntax) -> Result.bind p (respell d run syntax))
    (Ok p)
    delimiters
;;
