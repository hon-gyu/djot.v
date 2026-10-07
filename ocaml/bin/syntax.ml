(* ai-disclosure: ai-generated *)

(* The syntax the options and DJOT_SYNTAX select, as edits of a profile. Independent of
   the command line. *)

module P = Djot.Profile

type edit = P.t -> (P.t, string) result

let profiles : (string * P.t) list =
  [ "djot", P.djot; "markdown-like", P.markdown_like ]
;;

(** The name of [s] as an option and as a word of DJOT_SYNTAX: [ext-keyed]. *)
let switch_name (s : P.Switch.t) : string =
  String.map
    (function
      | '_' -> '-'
      | c -> c)
    (P.Switch.name s)
;;

(** A spelling as an option takes it: the delimiter itself, as in [**]; in braces, as in
    [{=}], when only the braced form is read; or [off]. *)
let spelling_to_string ((c, width, syntax) : char * int * P.Delimiter.syntax) : string =
  match syntax with
  | `Off -> "off"
  | `Bare -> String.make width c
  | `Braced -> Printf.sprintf "{%s}" (String.make width c)
;;

(** [respell d s] spells [d] as [s], read as {!spelling_to_string} writes it. *)
let respell (d : P.Delimiter.t) (s : string) : edit =
  fun p ->
  let name = P.Delimiter.name d in
  let len = String.length s in
  let run, (syntax : P.Delimiter.syntax) =
    if len >= 2 && s.[0] = '{' && s.[len - 1] = '}'
    then String.sub s 1 (len - 2), `Braced
    else s, `Bare
  in
  if s = "off"
  then (
    let c, width, _ = P.Delimiter.spelling d p in
    P.with_delimiter d c ~width `Off p)
  else if run = "" || String.exists (fun c -> c <> run.[0]) run
  then
    Error
      (Printf.sprintf
         "%s=%s: expected one character, repeated or not, alone or in braces, or off"
         name
         s)
  else
    P.with_delimiter d run.[0] ~width:(String.length run) syntax p
    |> Result.map_error (Printf.sprintf "%s=%s: %s" name s)
;;

let edit_of_word (w : string) : (edit, string) result =
  let switch (name : string) : P.Switch.t option =
    List.find_opt (fun s -> switch_name s = name) P.switches
  in
  let delimiter (name : string) : P.Delimiter.t option =
    List.find_opt (fun d -> P.Delimiter.name d = name) P.delimiters
  in
  let set (b : bool) (s : P.Switch.t) : edit = fun p -> Ok (P.Switch.set s b p) in
  let cut (sep : char) : (string * string) option =
    Option.map
      (fun i -> String.sub w 0 i, String.sub w (i + 1) (String.length w - i - 1))
      (String.index_opt w sep)
  in
  let found =
    match switch w, cut '=' with
    | Some s, _ -> Some (set true s)
    | None, Some (name, spelling) ->
      Option.map (fun d -> respell d spelling) (delimiter name)
    | None, None ->
      (match cut '-' with
       | Some ("no", name) -> Option.map (set false) (switch name)
       | _ -> None)
  in
  Option.to_result
    found
    ~none:
      (Printf.sprintf
         "%s: expected a profile as the first word, then NAME or no-NAME for a \
          construct, or NAME=SPELLING for a delimiter"
         w)
;;

(** The profile that the words of a DJOT_SYNTAX value give: a profile name first, {!djot}
    without one, then [NAME] or [no-NAME] for a switch and [NAME=SPELLING] for a
    delimiter, applied in order. *)
let of_words (words : string) : (P.t, string) result =
  let words = List.filter (( <> ) "") (String.split_on_char ' ' words) in
  let base, words =
    match words with
    | w :: rest when List.mem_assoc w profiles -> List.assoc w profiles, rest
    | words -> P.djot, words
  in
  List.fold_left
    (fun acc w -> Result.bind acc (fun p -> Result.bind (edit_of_word w) (fun e -> e p)))
    (Ok base)
    words
;;
