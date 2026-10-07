open Ascii
open Ast
open Attributes
open Datatypes
open InlineTable
open Line
open List0
open ListDef
open Strings

(** val dchar : dtable -> dstyle -> char **)

let dchar t k =
  t.dc_char k

(** val dsyntax_of : dtable -> dstyle -> dsyntax **)

let dsyntax_of t k =
  t.dc_syntax k

(** val dwidth : dtable -> dstyle -> int **)

let dwidth t k =
  t.dc_width k

(** val smart_typography : dtable -> bool **)

let smart_typography t =
  t.dc_smart_typography

(** val raw_inline_enabled : dtable -> bool **)

let raw_inline_enabled t =
  t.dc_raw_inline

(** val math_enabled : dtable -> bool **)

let math_enabled t =
  t.dc_math

(** val dollar_math_enabled : dtable -> bool **)

let dollar_math_enabled t =
  t.dc_dollar_math

(** val inline_attrs_enabled : dtable -> bool **)

let inline_attrs_enabled t =
  t.dc_attrs

(** val notes_enabled : dtable -> bool **)

let notes_enabled t =
  t.dc_footnotes

(** val wikilinks_enabled : dtable -> bool **)

let wikilinks_enabled t =
  t.dc_wikilinks

(** val tags_enabled : dtable -> bool **)

let tags_enabled t =
  t.dc_tags

(** val holes_enabled : dtable -> bool **)

let holes_enabled t =
  t.dc_holes

(** val denabled_of : dtable -> dstyle -> bool **)

let denabled_of =
  denabled

(** val dstyle_of : dtable -> char -> dstyle option **)

let dstyle_of =
  dstyle_at_fast

(** val dtoken : dtable -> dstyle -> string **)

let dtoken t k =
  chars (dchar t k) (dwidth t k)

(** val is_space : char -> bool **)

let is_space c =
  (||) ((||) ((||) ((=) c ' ') ((=) c '\t')) ((=) c '\r')) ((=) c '\n')

(** val nonspace_at : char option -> bool **)

let nonspace_at = function
| Some c -> negb (is_space c)
| None -> false

(** val dopens_after : char option -> bool **)

let dopens_after = function
| Some ch ->
  (||)
    ((||)
      ((||) ((||) ((||) (is_space ch) ((=) ch sqchar)) ((=) ch dqchar))
        ((=) ch hyphen))
      ((=) ch lparen))
    ((=) ch lbrack)
| None -> true

(** val ddecay_str : dtable -> dstyle -> bool -> bool -> string **)

let ddecay_str t k openmark closemark =
  match t.dc_decay k with
  | DDSelf ->
    (^) (if openmark then one lbrace else "")
      ((^) (dtoken t k)
        (if (&&) closemark (negb openmark) then one rbrace else ""))
  | DDPair (dfl, l, r) ->
    if dfl then if closemark then r else l else if openmark then l else r

(** val dbare : dtable -> dstyle -> char option -> bool **)

let dbare t k before =
  match dsyntax_of t k with
  | DBare -> true
  | DBareAfterBreak -> dopens_after before
  | _ -> false

(** val is_delim : dtable -> char -> bool **)

let is_delim t c =
  match dstyle_of t c with
  | Some _ -> true
  | None -> false

(** val marked_open : dtable -> dstyle -> string **)

let marked_open t k =
  (^) (one lbrace) (dtoken t k)

(** val marked_close : dtable -> dstyle -> string -> string **)

let marked_close t k tail =
  (^) (dtoken t k) ((^) (one rbrace) tail)

(** val needs_escape : dtable -> char -> bool **)

let needs_escape t c =
  (||)
    ((||)
      ((||) ((||) ((||) (dreserved c) (is_delim t c)) ((=) c hat))
        ((=) c hyphen))
      ((=) c ':'))
    ((&&) (holes_enabled t) ((=) c percent))

(** val needs_escape_dest : char -> bool **)

let needs_escape_dest c =
  (||) ((||) ((||) (is_bslash c) (is_tick c)) ((=) c lparen)) ((=) c rparen)

(** val marker_core : string -> bool **)

let marker_core pre =
  (&&) (nonempty_str pre)
    ((||)
      ((||)
        ((||) (str_forallb is_digit pre)
          ((&&) (( = ) (String.length pre) (Stdlib.succ 0))
            (str_forallb is_alnum pre)))
        (str_forallb is_roman_lo pre))
      (str_forallb is_roman_up pre))

(** val delim_alone : dtable -> char -> char -> char -> bool **)

let delim_alone t p c d =
  match dstyle_of t c with
  | Some k ->
    (&&)
      ((&&)
        ((&&)
          ((&&) (( = ) (dwidth t k) (Stdlib.succ 0))
            (match t.dc_decay k with
             | DDSelf -> true
             | DDPair (_, _, _) -> false))
          (negb ((=) c hyphen)))
        (is_space p))
      (is_space d)
  | None -> false

(** val bare_ok : dtable -> bool -> string -> char -> string -> bool **)

let bare_ok t at_end pre c rest =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> false)
    (fun p _ ->
    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

      (fun _ ->
      (&&) at_end
        ((||)
          ((||) ((&&) ((=) c period) (negb (marker_core pre))) ((=) c bang))
          ((=) c hyphen)))
      (fun d _ ->
      (||)
        ((||)
          ((||)
            ((&&) ((&&) ((=) c period) (negb ((=) d period)))
              (negb ((&&) (marker_core pre) ((=) d ' '))))
            ((=) c bang))
          ((&&) ((=) c hyphen) (negb ((=) d hyphen))))
        (delim_alone t p c d))
      rest)
    pre

(** val escape_from : dtable -> bool -> string -> string -> string **)

let rec escape_from t at_end pre s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun c rest ->
    if (&&) (needs_escape t c) (negb (bare_ok t at_end pre c rest))
    then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           ('\\',
           ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c,
           (escape_from t at_end
             ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

             (c, pre)) rest))))
    else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c,
           (escape_from t at_end
             ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

             (c, pre)) rest)))
    s

(** val escape_str : dtable -> string -> string **)

let escape_str t s =
  escape_from t false "" s

(** val escape_dest : string -> string **)

let rec escape_dest s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun c rest ->
    if needs_escape_dest c
    then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           ('\\',
           ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, (escape_dest rest))))
    else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, (escape_dest rest)))
    s

(** val tick_runs_from : int -> string -> int list **)

let rec tick_runs_from run s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> if ( = ) run 0 then [] else run :: [])
    (fun c rest ->
    if is_tick c
    then tick_runs_from (Stdlib.succ run) rest
    else if ( = ) run 0
         then tick_runs_from 0 rest
         else run :: (tick_runs_from 0 rest))
    s

(** val tick_runs : string -> int list **)

let tick_runs s =
  tick_runs_from 0 s

(** val first_missing : int -> int -> int list -> int **)

let rec first_missing fuel candidate runs =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> candidate)
    (fun fuel' ->
    if existsb (( = ) candidate) runs
    then first_missing fuel' (Stdlib.succ candidate) runs
    else candidate)
    fuel

(** val verb_ticks : string -> int **)

let verb_ticks s =
  first_missing (Stdlib.succ (String.length s)) (Stdlib.succ 0) (tick_runs s)

(** val starts_tick : string -> bool **)

let starts_tick s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> false)
    (fun c _ -> is_tick c)
    s

(** val ends_tick : string -> bool **)

let ends_tick s =
  starts_tick (rev_string s)

(** val pad_verb : string -> string **)

let pad_verb s =
  let left = if starts_tick s then " " else "" in
  let right = if ends_tick s then " " else "" in (^) left ((^) s right)

(** val ticks : int -> string **)

let rec ticks n =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> "")
    (fun k ->
    (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (tick, (ticks k)))
    n

(** val verb_text : string -> string **)

let verb_text s =
  let d = ticks (verb_ticks s) in (^) d ((^) (pad_verb s) d)

(** val verb_safe_from : int -> int -> string -> bool **)

let rec verb_safe_from n run s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> negb (( = ) run n))
    (fun c rest ->
    if is_tick c
    then verb_safe_from n (Stdlib.succ run) rest
    else (&&) (negb (( = ) run n)) (verb_safe_from n 0 rest))
    s

(** val verb_safe : int -> string -> bool **)

let verb_safe n s =
  verb_safe_from n 0 s

(** val starts_space_tick : string -> bool **)

let starts_space_tick s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> false)
    (fun c s0 ->
    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

      (fun _ -> false)
      (fun d _ -> (&&) ((=) c ' ') (is_tick d))
      s0)
    s

(** val verb_content_ok : string -> bool **)

let verb_content_ok s =
  (&&)
    ((&&) ((&&) (no_nl s) (negb (starts_space_tick s)))
      (negb (starts_space_tick (rev_string s))))
    (verb_safe (verb_ticks s) (pad_verb s))

(** val bracket_open : bool -> string **)

let bracket_open = function
| true ->
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (bang, (one lbrack))
| false -> one lbrack

(** val tag_open : string -> string **)

let tag_open name =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> one lbrack)
    (fun _ _ ->
    (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (':', ((^) name (one lbrack))))
    name

(** val link_close : string -> string -> string **)

let link_close dst tail =
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (rbrack,
    ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (lparen,
    ((^) (escape_dest dst)
      ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      (rparen, tail))))))

(** val ref_close : string -> string -> string **)

let ref_close label tail =
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (rbrack,
    ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (lbrack,
    ((^) label
      ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      (rbrack, tail))))))

(** val wiki_text : bool -> string -> string option -> string **)

let wiki_text embed t al =
  (^) (bracket_open embed)
    ((^) (one lbrack)
      ((^) t
        ((^)
          (match al with
           | Some a ->
             (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

               (vbar, a)
           | None -> "")
          ((^) (one rbrack) (one rbrack)))))

(** val note_text : string -> string **)

let note_text label =
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (lbrack,
    ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (hat, ((^) label (one rbrack)))))

(** val note_label_safe_from : bool -> string -> bool **)

let rec note_label_safe_from esc label =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> negb esc)
    (fun c rest ->
    if esc
    then note_label_safe_from false rest
    else if (=) c rbrack
         then false
         else note_label_safe_from (is_bslash c) rest)
    label

(** val note_label_safe : string -> bool **)

let note_label_safe =
  note_label_safe_from false

(** val auto_email : string -> bool **)

let auto_email = (fun s ->
     let rec scan i =
       i < String.length s &&
       ((i > 0 && s.[i] = '@' && s.[i-1] <> ':') || scan (i + 1))
     in scan 0)

(** val is_alpha : char -> bool **)

let is_alpha c =
  (||) ((&&) (leb 'a' c) (leb c 'z')) ((&&) (leb 'A' c) (leb c 'Z'))

(** val symbol_char : char -> bool **)

let symbol_char c =
  (||)
    ((||)
      ((||) ((||) (is_alpha c) ((&&) (leb '0' c) (leb c '9'))) ((=) c '_'))
      ((=) c '+'))
    ((=) c '-')

(** val auto_node : string -> inline **)

let auto_node s =
  if auto_email s then EmailLink s else UrlLink s

(** val auto_kind_ok : string -> bool **)

let auto_kind_ok = (fun s ->
     let alpha c =
       (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') in
     let rec scheme i =
       i + 1 < String.length s &&
       ((alpha s.[i] && s.[i+1] = ':') || scheme (i + 1)) in
     auto_email s || scheme 0)

(** val auto_text : string -> string **)

let auto_text s =
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (lt, ((^) s (one gt)))

(** val auto_body_ok : string -> bool **)

let auto_body_ok = (fun s ->
     s <> "" && String.for_all (fun c ->
       c <> ' ' && c <> '\t' && c <> '\r' && c <> '\n' &&
       c <> '<' && c <> '>') s)

(** val eqchar : char **)

let eqchar =
  '='

(** val raw_spec_ok : string -> bool **)

let raw_spec_ok spec =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> false)
    (fun c rest -> (&&) ((=) c eqchar) (nonempty_str rest))
    spec

(** val raw_fmt_ok : string -> bool **)

let raw_fmt_ok fmt =
  (&&)
    ((&&) ((&&) ((&&) (nonempty_str fmt) (no_ws fmt)) (no_char lbrace fmt))
      (no_char rbrace fmt))
    (no_char tick fmt)

(** val raw_format : string -> string **)

let raw_format spec =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun _ rest -> rest)
    spec

(** val raw_stop : char -> bool **)

let raw_stop c =
  (||) ((||) (is_ws c) (is_tick c)) ((=) c lbrace)

(** val raw_text : string -> string -> string **)

let raw_text fmt s =
  (^) (verb_text s)
    ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (lbrace,
    ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    ('=', ((^) fmt (one rbrace))))))

(** val hole_text : string -> string **)

let rec hole_text = (fun s ->
     if not (String.contains s '\\') then s else
     let n = String.length s in
     let b = Buffer.create n and i = ref 0 in
     while !i < n do
       let c = s.[!i] in
       if c = '\\' && !i + 1 < n
          && (let d = s.[!i + 1] in d = '{' || d = '}' || d = '\\')
       then (Buffer.add_char b s.[!i + 1]; i := !i + 2)
       else (Buffer.add_char b c; incr i)
     done;
     Buffer.contents b)

(** val hole_src : string -> string **)

let rec hole_src s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun c rest ->
    if (||) ((=) c lbrace) ((=) c rbrace)
    then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (bslash,
           ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, (hole_src rest))))
    else if is_bslash c
         then ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                 (fun _ ->
                 (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                 (bslash,
                 ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                 (c, ""))))
                 (fun d _ ->
                 if (||) ((||) ((=) d lbrace) ((=) d rbrace)) (is_bslash d)
                 then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                        (bslash,
                        ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                        (c, (hole_src rest))))
                 else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                        (c, (hole_src rest)))
                 rest)
         else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                (c, (hole_src rest)))
    s

(** val hole_spell : string -> string **)

let hole_spell s =
  (^) (one percent) ((^) (one lbrace) ((^) (hole_src s) (one rbrace)))

type cinline =
| CIStr of string
| CIVerb of string
| CIDelim of dstyle * cinline list
| CILink of bool * cinline list * string
| CIRef of bool * cinline list * string
| CINote of string
| CIAuto of string
| CIRaw of string * string
| CIWiki of bool * string * string option
| CITag of string * cinline list

(** val str_last : string -> char option -> char option **)

let rec str_last = (fun s prev ->
     let n = String.length s in if n = 0 then prev else Some s.[n - 1])

(** val tag_may_follow : string -> bool **)

let tag_may_follow txt =
  match str_last txt None with
  | Some c -> negb ((||) (is_alnum c) ((=) c ':'))
  | None -> true

(** val ci_src : dtable -> cinline -> string **)

let rec ci_src t ci =
  let go =
    let rec go = function
    | [] -> ""
    | c :: rest -> (^) (ci_src t c) (go rest)
    in go
  in
  (match ci with
   | CIStr s -> escape_str t s
   | CIVerb s -> verb_text s
   | CIDelim (k, kids) ->
     (^) (marked_open t k) ((^) (go kids) (marked_close t k ""))
   | CILink (img, kids, dst) ->
     (^) (bracket_open img) ((^) (go kids) (link_close dst ""))
   | CIRef (img, kids, label) ->
     (^) (bracket_open img) ((^) (go kids) (ref_close label ""))
   | CINote label -> note_text label
   | CIAuto s -> auto_text s
   | CIRaw (fmt, s) -> raw_text fmt s
   | CIWiki (embed, t0, al) -> wiki_text embed t0 al
   | CITag (name, kids) -> (^) (tag_open name) ((^) (go kids) (one rbrack)))

(** val ci_text : dtable -> cinline list -> string **)

let rec ci_text t = function
| [] -> ""
| ci :: rest -> (^) (ci_src t ci) (ci_text t rest)

(** val ci_text_at : dtable -> bool -> cinline list -> string **)

let rec ci_text_at t at_end = function
| [] -> ""
| ci :: rest ->
  (match ci with
   | CIStr s ->
     (match rest with
      | [] -> escape_from t at_end "" s
      | _ :: _ -> (^) (ci_src t ci) (ci_text_at t at_end rest))
   | _ -> (^) (ci_src t ci) (ci_text_at t at_end rest))

(** val ci_line : dtable -> cinline list -> string **)

let ci_line t cis =
  ci_text_at t true cis

(** val ci_ast : cinline -> inline node **)

let rec ci_ast ci =
  let go =
    let rec go = function
    | [] -> []
    | c :: rest -> (ci_ast c) :: (go rest)
    in go
  in
  (match ci with
   | CIStr s -> mk (Str s)
   | CIVerb s -> mk (Verbatim s)
   | CIDelim (k, kids) -> mk (dnode k (go kids))
   | CILink (img, kids, dst) -> mk (bnode img (go kids) (Direct dst))
   | CIRef (img, kids, label) -> mk (bnode img (go kids) (Reference label))
   | CINote label -> mk (FootnoteReference label)
   | CIAuto s -> mk (auto_node s)
   | CIRaw (fmt, s) -> mk (RawInline (fmt, s))
   | CIWiki (embed, t, al) -> mk (Ext_wikilink (embed, t, al))
   | CITag (name, kids) -> mk (Span (name, (go kids))))

(** val ci_inlines : cinline list -> inlines **)

let ci_inlines cis =
  map ci_ast cis

(** val ci_pair_ok : dtable -> cinline -> cinline -> bool **)

let ci_pair_ok t a b =
  match a with
  | CIStr s ->
    (match b with
     | CIStr _ -> false
     | CITag (_, _) -> tag_may_follow s
     | _ -> true)
  | CIVerb _ ->
    (match b with
     | CIVerb _ -> false
     | CIDelim (k, _) -> negb ((=) (dchar t k) eqchar)
     | CIRaw (_, _) -> false
     | _ -> true)
  | _ -> true

(** val ci_lbrack_head : cinline -> bool **)

let ci_lbrack_head = function
| CILink (img, _, _) -> if img then false else true
| CIRef (img, _, _) -> if img then false else true
| CINote _ -> true
| CIWiki (embed, _, _) -> if embed then false else true
| _ -> false

(** val cis_lbrack_head : cinline list -> bool **)

let cis_lbrack_head = function
| [] -> false
| c :: _ -> ci_lbrack_head c

(** val bracket_kids_ok : dtable -> cinline list -> bool **)

let bracket_kids_ok t kids =
  negb ((&&) (wikilinks_enabled t) (cis_lbrack_head kids))

(** val wiki_part_ok : string -> bool **)

let wiki_part_ok s =
  (&&) ((&&) ((&&) (no_char rbrack s) (no_char vbar s)) (no_char bslash s))
    (no_nl s)

(** val tag_name_ok : string -> bool **)

let tag_name_ok name =
  (&&) (nonempty_str name) (str_forallb symbol_char name)

(** val ci_ok : dtable -> cinline -> bool **)

let rec ci_ok t ci =
  let go =
    let rec go = function
    | [] -> true
    | c :: rest -> (&&) (ci_ok t c) (go rest)
    in go
  in
  let sep =
    let rec sep = function
    | [] -> true
    | a :: rest ->
      (match rest with
       | [] -> true
       | b :: _ -> (&&) (ci_pair_ok t a b) (sep rest))
    in sep
  in
  (match ci with
   | CIStr s -> (&&) (nonempty_str s) (no_nl s)
   | CIVerb s -> (&&) (nonempty_str s) (verb_content_ok s)
   | CIDelim (k, kids) ->
     (&&) ((&&) ((&&) (denabled_of t k) (nonempty kids)) (go kids)) (sep kids)
   | CILink (_, kids, dst) ->
     (&&) ((&&) ((&&) (no_nl dst) (go kids)) (sep kids))
       (bracket_kids_ok t kids)
   | CIRef (_, kids, label) ->
     (&&)
       ((&&)
         ((&&)
           ((&&) ((&&) (nonempty_str label) (no_char rbrack label))
             ((=) (normalize_label label) label))
           (go kids))
         (sep kids))
       (bracket_kids_ok t kids)
   | CINote label ->
     (&&) ((&&) (notes_enabled t) (note_label_safe label))
       ((=) (normalize_label label) label)
   | CIAuto s -> (&&) (auto_body_ok s) (auto_kind_ok s)
   | CIRaw (fmt, s) ->
     (&&)
       ((&&) ((&&) (raw_inline_enabled t) (nonempty_str s))
         (verb_content_ok s))
       (raw_fmt_ok fmt)
   | CIWiki (_, t0, al) ->
     (&&)
       ((&&) ((&&) (wikilinks_enabled t) (nonempty_str t0)) (wiki_part_ok t0))
       (match al with
        | Some a -> wiki_part_ok a
        | None -> true)
   | CITag (name, kids) ->
     (&&) ((&&) ((&&) (tags_enabled t) (tag_name_ok name)) (go kids))
       (sep kids))

(** val ci_sep_ok : dtable -> cinline list -> bool **)

let rec ci_sep_ok t = function
| [] -> true
| a :: rest ->
  (match rest with
   | [] -> true
   | b :: _ -> (&&) (ci_pair_ok t a b) (ci_sep_ok t rest))

(** val cis_ok : dtable -> cinline list -> bool **)

let cis_ok t cis =
  (&&) (forallb (ci_ok t) cis) (ci_sep_ok t cis)

(** val ci_para : cinline list list -> inlines **)

let rec ci_para = function
| [] -> []
| cis :: rest ->
  (match rest with
   | [] -> ci_inlines cis
   | _ :: _ -> app (ci_inlines cis) ((mk SoftBreak) :: (ci_para rest)))

(** val inline_text : dtable -> inline -> string **)

let rec inline_text t il =
  let go =
    let rec go = function
    | [] -> ""
    | n :: rest ->
      let Node (_, a, x) = n in
      (match a with
       | [] -> (^) (inline_text t x) (go rest)
       | _ :: _ -> (^) (inline_text t x) ((^) (attr_spec a) (go rest)))
    in go
  in
  let marked = fun k ns ->
    (^) (marked_open t k) ((^) (go ns) (marked_close t k ""))
  in
  (match il with
   | Str s -> escape_str t s
   | Emph ns -> marked DEmph ns
   | Strong ns -> marked DStrong ns
   | Highlight ns -> marked DMark ns
   | Insert ns -> marked DInsert ns
   | Delete ns -> marked DDelete ns
   | Superscript ns -> marked DSuper ns
   | Subscript ns -> marked DSub ns
   | Verbatim s -> verb_text s
   | Symbol s -> (^) (one ':') ((^) s (one ':'))
   | Math (style, s) ->
     (match style with
      | DisplayMath -> (^) (one '$') ((^) (one '$') (verb_text s))
      | InlineMath -> (^) (one '$') (verb_text s))
   | Link (ns, tgt) ->
     (match tgt with
      | Direct dst ->
        (^) (bracket_open false) ((^) (go ns) (link_close dst ""))
      | Reference label ->
        (^) (bracket_open false) ((^) (go ns) (ref_close label "")))
   | Image (ns, tgt) ->
     (match tgt with
      | Direct dst ->
        (^) (bracket_open true) ((^) (go ns) (link_close dst ""))
      | Reference label ->
        (^) (bracket_open true) ((^) (go ns) (ref_close label "")))
   | Span (name, ns) -> (^) (tag_open name) ((^) (go ns) (one ']'))
   | FootnoteReference label -> note_text label
   | UrlLink s -> auto_text s
   | EmailLink s -> auto_text s
   | RawInline (fmt, s) -> raw_text fmt s
   | NonBreakingSpace ->
     (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

       (bslash, (one ' '))
   | Quoted (qt, ns) ->
     (match qt with
      | SingleQuotes -> marked DSQuote ns
      | DoubleQuotes -> marked DDQuote ns)
   | SoftBreak -> one '\n'
   | HardBreak ->
     (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

       (bslash, (one '\n'))
   | Ext_wikilink (embed, t0, al) -> wiki_text embed t0 al
   | Hole s -> hole_spell s)

(** val line_ends : inlines -> bool **)

let line_ends = function
| [] -> true
| n :: _ ->
  let Node (_, _, x) = n in (match x with
                             | SoftBreak -> true
                             | _ -> false)

(** val inline_lines : dtable -> inlines -> string -> string list **)

let rec inline_lines t ils cur =
  match ils with
  | [] -> cur :: []
  | n :: rest ->
    let Node (_, a, il) = n in
    (match a with
     | [] ->
       (match il with
        | Str s ->
          inline_lines t rest ((^) cur (escape_from t (line_ends rest) "" s))
        | SoftBreak -> cur :: (inline_lines t rest "")
        | HardBreak -> ((^) cur (one bslash)) :: (inline_lines t rest "")
        | _ -> inline_lines t rest ((^) cur (inline_text t il)))
     | _ :: _ ->
       (match il with
        | SoftBreak -> cur :: (inline_lines t rest "")
        | HardBreak -> ((^) cur (one bslash)) :: (inline_lines t rest "")
        | _ ->
          inline_lines t rest ((^) cur ((^) (inline_text t il) (attr_spec a)))))
