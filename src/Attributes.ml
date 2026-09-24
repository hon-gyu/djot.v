open Ascii
open Ast
open Datatypes
open List0
open Nat0
open Strings

(** val bslash : char **)

let bslash =
  '\\'

(** val dquote : char **)

let dquote =
  '"'

(** val is_key_char : char -> bool **)

let is_key_char c =
  let n = nat_of_ascii c in
  (||)
    ((||)
      ((||)
        ((||)
          ((||)
            ((&&)
              (leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                n)
              (leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S
                O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            ((&&)
              (leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S
                O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                n)
              (leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S
                O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          ((&&)
            (leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))))))))))))))))))) n)
            (leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
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

(** val collapse_char : char -> bool **)

let collapse_char c =
  (||) ((||) ((=) c ' ') ((=) c '\r')) ((=) c '\n')

(** val collapse_from : bool -> string -> string **)

let rec collapse_from skip s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun c s' ->
    if collapse_char c
    then if skip
         then collapse_from true s'
         else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                (' ', (collapse_from true s'))
    else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, (collapse_from false s')))
    s

(** val collapse_ws : string -> string **)

let collapse_ws s =
  collapse_from false s

(** val is_escapable : char -> bool **)

let is_escapable c =
  existsb ((=) c)
    ('.' :: (',' :: (bslash :: ('/' :: ('#' :: ('!' :: ('$' :: ('%' :: ('^' :: ('&' :: ('*' :: (';' :: (':' :: ('{' :: ('}' :: ('=' :: ('-' :: ('_' :: ('`' :: ('~' :: ('+' :: ('[' :: (']' :: ('(' :: (')' :: ('\'' :: (dquote :: ('?' :: ('|' :: [])))))))))))))))))))))))))))))

(** val unescape : string -> string **)

let rec unescape s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun c s' ->
    if (=) c bslash
    then ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

            (fun _ ->
            (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

            (c, ""))
            (fun d s'' ->
            if is_escapable d
            then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                   (d, (unescape s''))
            else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                   (c, (unescape s')))
            s')
    else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, (unescape s')))
    s

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

type aparser = { ap_st : astate; ap_tok : string; ap_key : string;
                 ap_attrs : attr }

(** val ap_init : aparser **)

let ap_init =
  { ap_st = AScan; ap_tok = ""; ap_key = ""; ap_attrs = [] }

(** val ap_token : aparser -> string **)

let ap_token p =
  rev_string p.ap_tok

(** val ap_push : char -> aparser -> aparser **)

let ap_push c p =
  { ap_st = p.ap_st; ap_tok =
    ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (c, p.ap_tok)); ap_key = p.ap_key; ap_attrs = p.ap_attrs }

(** val ap_goto : astate -> aparser -> aparser **)

let ap_goto s p =
  { ap_st = s; ap_tok = p.ap_tok; ap_key = p.ap_key; ap_attrs = p.ap_attrs }

(** val ap_begin : astate -> aparser -> aparser **)

let ap_begin s p =
  { ap_st = s; ap_tok = ""; ap_key = p.ap_key; ap_attrs = p.ap_attrs }

(** val ap_commit_id : astate -> aparser -> aparser **)

let ap_commit_id s p =
  let t = ap_token p in
  { ap_st = s; ap_tok = ""; ap_key = p.ap_key; ap_attrs =
  (if (=) t "" then p.ap_attrs else Attr.set "id" t p.ap_attrs) }

(** val ap_commit_class : astate -> aparser -> aparser **)

let ap_commit_class s p =
  let t = ap_token p in
  { ap_st = s; ap_tok = ""; ap_key = p.ap_key; ap_attrs =
  (if (=) t "" then p.ap_attrs else Attr.add_class t p.ap_attrs) }

(** val ap_commit_value : astate -> aparser -> aparser **)

let ap_commit_value s p =
  { ap_st = s; ap_tok = ""; ap_key = p.ap_key; ap_attrs =
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
    then { ap_st = AVal; ap_tok = ""; ap_key = (ap_token p); ap_attrs =
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

let rec afeed s p =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> (p, ""))
    (fun c s' ->
    match p.ap_st with
    | AFail -> (p, s)
    | ADone -> (p, s)
    | _ -> afeed s' (astep p c))
    s

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

let rec blank_to_eol s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> true)
    (fun c s' -> (&&) (attr_ws c) (blank_to_eol s'))
    s

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
