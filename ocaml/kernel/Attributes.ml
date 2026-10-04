open Ast
open Datatypes
open List0
open ListDef
open Strings

(** val bslash : char **)

let bslash =
  '\\'

(** val dquote : char **)

let dquote =
  '"'

(** val is_key_char : char -> bool **)

let is_key_char c =
  let n = Char.code c in
  (||)
    ((||)
      ((||)
        ((||)
          ((||)
            ((&&)
              (( <= ) (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ
                0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                n)
              (( <= ) n (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ
                0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            ((&&)
              (( <= ) (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ
                0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                n)
              (( <= ) n (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                (Stdlib.succ (Stdlib.succ
                0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          ((&&)
            (( <= ) (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              0)))))))))))))))))))))))))))))))))))))))))))))))) n)
            (( <= ) n (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
              (Stdlib.succ
              0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        ((=) c '_'))
      ((=) c ':'))
    ((=) c '-')

(** val attr_ws : char -> bool **)

let attr_ws c =
  (||) ((||) ((||) (is_ws c) ((=) c '\n')) ((=) c '\012')) ((=) c '\011')

(** val is_id_char : char -> bool **)

let is_id_char c =
  (&&) (negb (attr_ws c))
    (negb
      (existsb ((=) c)
        (']' :: ('[' :: ('~' :: ('!' :: ('@' :: ('#' :: ('$' :: ('%' :: ('^' :: ('&' :: ('*' :: ('(' :: (')' :: ('{' :: ('}' :: ('`' :: (',' :: ('.' :: ('<' :: ('>' :: (bslash :: ('|' :: ('=' :: ('+' :: ('/' :: ('?' :: []))))))))))))))))))))))))))))

(** val is_attr_class_char : char -> bool **)

let is_attr_class_char =
  is_key_char

(** val collapse_from : bool -> string -> string **)

let rec collapse_from = (fun skip s ->
     let b = Buffer.create (String.length s) in
     let skip = ref skip in
     String.iter (fun c ->
       if c = ' ' || c = '\r' || c = '\n' then
         (if not !skip then Buffer.add_char b ' '; skip := true)
       else (Buffer.add_char b c; skip := false)) s;
     Buffer.contents b)

(** val collapse_ws : string -> string **)

let collapse_ws s =
  collapse_from false s

(** val unescape : string -> string **)

let rec unescape = (fun s ->
     let n = String.length s in
     let b = Buffer.create n in
     let escapable = function
       | '.' | ',' | '\\' | '/' | '#' | '!' | '$' | '%' | '^' | '&' | '*'
       | ';' | ':' | '{' | '}' | '=' | '-' | '_' | '`' | '~' | '+' | '['
       | ']' | '(' | ')' | '\'' | '"' | '?' | '|' -> true
       | _ -> false in
     let rec go i =
       if i < n then
         if s.[i] = '\\' && i + 1 < n && escapable s.[i + 1]
         then (Buffer.add_char b s.[i + 1]; go (i + 2))
         else (Buffer.add_char b s.[i]; go (i + 1)) in
     go 0; Buffer.contents b)

(** val norm_value : string -> string **)

let norm_value s =
  unescape (collapse_ws s)

type astate =
| AScan
| AId
| AClass
| AKey
| AVal
| ABare
| AQuot
| AEsc
| AComment
| AFail
| ADone

type aparser = { ap_st : astate; ap_tok : char list; ap_key : string;
                 ap_attrs : attr }

(** val ap_init : aparser **)

let ap_init =
  { ap_st = AScan; ap_tok = []; ap_key = ""; ap_attrs = [] }

(** val ap_token : aparser -> string **)

let ap_token p =
  rev_chars p.ap_tok

(** val ap_push : char -> aparser -> aparser **)

let ap_push c p =
  { ap_st = p.ap_st; ap_tok = (c :: p.ap_tok); ap_key = p.ap_key; ap_attrs =
    p.ap_attrs }

(** val ap_goto : astate -> aparser -> aparser **)

let ap_goto s p =
  { ap_st = s; ap_tok = p.ap_tok; ap_key = p.ap_key; ap_attrs = p.ap_attrs }

(** val ap_begin : astate -> aparser -> aparser **)

let ap_begin s p =
  { ap_st = s; ap_tok = []; ap_key = p.ap_key; ap_attrs = p.ap_attrs }

(** val ap_commit_id : astate -> aparser -> aparser **)

let ap_commit_id s p =
  let t = ap_token p in
  { ap_st = s; ap_tok = []; ap_key = p.ap_key; ap_attrs =
  (if (=) t "" then p.ap_attrs else Attr.set "id" t p.ap_attrs) }

(** val ap_commit_class : astate -> aparser -> aparser **)

let ap_commit_class s p =
  let t = ap_token p in
  { ap_st = s; ap_tok = []; ap_key = p.ap_key; ap_attrs =
  (if (=) t "" then p.ap_attrs else Attr.add_class t p.ap_attrs) }

(** val ap_commit_value : astate -> aparser -> aparser **)

let ap_commit_value s p =
  { ap_st = s; ap_tok = []; ap_key = p.ap_key; ap_attrs =
    (Attr.set p.ap_key (norm_value (ap_token p)) p.ap_attrs) }

(** val astep : aparser -> char -> aparser **)

let astep p c =
  match p.ap_st with
  | AScan ->
    if attr_ws c
    then p
    else if (=) c '}'
         then ap_goto ADone p
         else if (=) c '#'
              then ap_begin AId p
              else if (=) c '%'
                   then ap_begin AComment p
                   else if (=) c '.'
                        then ap_begin AClass p
                        else if is_key_char c
                             then ap_push c (ap_begin AKey p)
                             else ap_goto AFail p
  | AId ->
    if is_id_char c
    then ap_push c p
    else if (=) c '}'
         then ap_commit_id ADone p
         else if attr_ws c then ap_commit_id AScan p else ap_goto AFail p
  | AClass ->
    if is_attr_class_char c
    then ap_push c p
    else if (=) c '}'
         then ap_commit_class ADone p
         else if attr_ws c then ap_commit_class AScan p else ap_goto AFail p
  | AKey ->
    if (=) c '='
    then { ap_st = AVal; ap_tok = []; ap_key = (ap_token p); ap_attrs =
           p.ap_attrs }
    else if is_key_char c then ap_push c p else ap_goto AFail p
  | AVal ->
    if (=) c dquote
    then ap_begin AQuot p
    else if is_key_char c
         then ap_push c (ap_begin ABare p)
         else ap_goto AFail p
  | ABare ->
    if is_key_char c
    then ap_push c p
    else if (=) c '}'
         then ap_commit_value ADone p
         else if attr_ws c then ap_commit_value AScan p else ap_goto AFail p
  | AQuot ->
    if (=) c dquote
    then ap_commit_value AScan p
    else if (=) c bslash then ap_goto AEsc (ap_push c p) else ap_push c p
  | AEsc -> ap_goto AQuot (ap_push c p)
  | AComment ->
    if (=) c '%'
    then ap_begin AScan p
    else if (=) c '}' then ap_goto ADone p else p
  | _ -> p

(** val afeed : string -> aparser -> aparser * string **)

let rec afeed = (fun s p ->
     let n = String.length s in
     let rec go i p =
       if i >= n then (p, "")
       else match p.ap_st with
         | ADone | AFail -> (p, if i = 0 then s else String.sub s i (n - i))
         | _ -> go (i + 1) (astep p s.[i]) in
     go 0 p)

(** val ap_done : aparser -> bool **)

let ap_done p =
  match p.ap_st with
  | ADone -> true
  | _ -> false

(** val ap_failed : aparser -> bool **)

let ap_failed p =
  match p.ap_st with
  | AFail -> true
  | _ -> false

(** val attr_nl : string **)

let attr_nl =
  "\n"

(** val blank_to_eol : string -> bool **)

let rec blank_to_eol = (fun s -> String.for_all (fun c ->
     c = ' ' || c = '\t' || c = '\r' || c = '\n' || c = '\012' || c = '\011') s)

(** val attr_open : string -> aparser option **)

let attr_open l =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun a body ->
    (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
      (fun b b0 b1 b2 b3 b4 b5 b6 ->
      if b
      then if b0
           then if b1
                then None
                else if b2
                     then if b3
                          then if b4
                               then if b5
                                    then if b6
                                         then None
                                         else let (p, rest) =
                                                afeed ((^) body attr_nl)
                                                  ap_init
                                              in
                                              if ap_failed p
                                              then None
                                              else if (&&) (ap_done p)
                                                        (negb
                                                          (blank_to_eol rest))
                                                   then None
                                                   else Some p
                                    else None
                               else None
                          else None
                     else None
           else None
      else None)
      a)
    (drop_leading_ws l)

(** val attr_feed : string -> aparser -> aparser **)

let attr_feed l p =
  fst (afeed ((^) (drop_leading_ws l) attr_nl) p)

(** val id_chars_ok : string -> bool **)

let rec id_chars_ok id =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> true)
    (fun c rest -> (&&) (is_id_char c) (id_chars_ok rest))
    id

(** val explicit_id_ok : string -> bool **)

let explicit_id_ok id =
  (&&) (nonempty_str id) (id_chars_ok id)

(** val class_words_ok : bool -> string -> bool **)

let rec class_words_ok after_space s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> negb after_space)
    (fun c rest ->
    if (=) c ' '
    then (&&) (negb after_space) (class_words_ok true rest)
    else (&&) (is_attr_class_char c) (class_words_ok false rest))
    s

(** val classes_ok : string -> bool **)

let classes_ok s =
  (&&) (nonempty_str s) (class_words_ok true s)

(** val class_chars_ok : string -> bool **)

let rec class_chars_ok s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> true)
    (fun c rest -> (&&) (is_attr_class_char c) (class_chars_ok rest))
    s

(** val class_word_ok : string -> bool **)

let class_word_ok s =
  (&&) (nonempty_str s) (class_chars_ok s)

(** val dot_words : string -> string **)

let rec dot_words s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun c rest ->
    if (=) c ' '
    then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c,
           ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           ('.', (dot_words rest))))
    else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, (dot_words rest)))
    s

(** val escape_value : string -> string **)

let rec escape_value s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun c rest ->
    if (||) ((=) c dquote) ((=) c bslash)
    then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (bslash,
           ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, (escape_value rest))))
    else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, (escape_value rest)))
    s

(** val attr_part : (string * string) -> string **)

let attr_part = function
| (k, v) ->
  if (&&) ((=) k "id") (explicit_id_ok v)
  then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

         ('#', v)
  else if (&&) ((=) k "class") (classes_ok v)
       then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

              ('.', (dot_words v))
       else (^) k
              ((^) "="
                ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                (dquote,
                ((^) (escape_value v)
                  ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                  (dquote, ""))))))

(** val attr_spec : attr -> string **)

let attr_spec a = match a with
| [] -> ""
| _ :: _ -> (^) "{" ((^) (String.concat " " (map attr_part a)) "}")

(** val key_ok : string -> bool **)

let key_ok =
  class_word_ok

(** val attr_ok : attr -> bool **)

let rec attr_ok = function
| [] -> true
| p :: rest ->
  let (k, _) = p in
  (&&) (key_ok k)
    (match alist_lookup k rest with
     | Some _ -> false
     | None -> attr_ok rest)
