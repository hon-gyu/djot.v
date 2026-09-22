open Ascii
open Ast
open Attributes
open Bool0
open Datatypes
open List0
open ListDef
open Nat0
open PeanoNat
open String0
open Strings

(** val is_punct : char -> bool **)

let is_punct c =
  let n = nat_of_ascii c in
  (||)
    ((||)
      ((||)
        ((&&)
          (Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))) n)
          (Nat.leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))))))))))))))))))
        ((&&)
          (Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) n)
          (Nat.leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S
            O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      ((&&)
        (Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          n)
        (Nat.leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    ((&&)
      (Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        n)
      (Nat.leb n (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val tick : char **)

let tick =
  '`'

(** val is_tick : char -> bool **)

let is_tick c =
  (=) c tick

(** val bslash : char **)

let bslash =
  '\\'

(** val is_bslash : char -> bool **)

let is_bslash c =
  (=) c bslash

(** val lbrace : char **)

let lbrace =
  '{'

(** val rbrace : char **)

let rbrace =
  '}'

(** val one : char -> string **)

let one c =
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (c, "")

(** val dollar : char **)

let dollar =
  '$'

(** val sqchar : char **)

let sqchar =
  '\''

(** val dqchar : char **)

let dqchar =
  '"'

(** val hyphen : char **)

let hyphen =
  '-'

(** val bang : char **)

let bang =
  '!'

(** val period : char **)

let period =
  '.'

(** val lbrack : char **)

let lbrack =
  '['

(** val rbrack : char **)

let rbrack =
  ']'

(** val vbar : char **)

let vbar =
  '|'

(** val hat : char **)

let hat =
  '^'

(** val lparen : char **)

let lparen =
  '('

(** val rparen : char **)

let rparen =
  ')'

(** val lt : char **)

let lt =
  '<'

(** val gt : char **)

let gt =
  '>'

(** val nl_char : char **)

let nl_char =
  '\n'

(** val dreserved : char -> bool **)

let dreserved c =
  (||)
    ((||)
      ((||)
        ((||)
          ((||)
            ((||)
              ((||)
                ((||) ((||) ((||) (is_bslash c) (is_tick c)) ((=) c lbrace))
                  ((=) c rbrace))
                ((=) c lbrack))
              ((=) c rbrack))
            ((=) c bang))
          ((=) c dollar))
        ((=) c lt))
      ((=) c ':'))
    ((=) c period)

type dstyle =
| DEmph
| DStrong
| DSuper
| DSub
| DMark
| DInsert
| DDelete
| DSQuote
| DDQuote

type dsyntax =
| DOff
| DBraced
| DBare
| DBareAfterBreak

type ddecay =
| DDSelf
| DDPair of bool * string * string

type dconfig = { dc_char : (dstyle -> char); dc_width : (dstyle -> nat);
                 dc_syntax : (dstyle -> dsyntax);
                 dc_decay : (dstyle -> ddecay); dc_smart_typography : 
                 bool; dc_raw_inline : bool; dc_math : bool; dc_attrs : 
                 bool; dc_footnotes : bool; dc_wikilinks : bool }

(** val djot_dchar : dstyle -> char **)

let djot_dchar = function
| DEmph -> '_'
| DStrong -> '*'
| DSuper -> '^'
| DSub -> '~'
| DMark -> '='
| DInsert -> '+'
| DDelete -> '-'
| DSQuote -> '\''
| DDQuote -> '"'

(** val djot_dsyntax : dstyle -> dsyntax **)

let djot_dsyntax = function
| DMark -> DBraced
| DInsert -> DBraced
| DDelete -> DBraced
| DSQuote -> DBareAfterBreak
| _ -> DBare

(** val lsquo : string **)

let lsquo =
  "\226\128\152"

(** val rsquo : string **)

let rsquo =
  "\226\128\153"

(** val ldquo : string **)

let ldquo =
  "\226\128\156"

(** val rdquo : string **)

let rdquo =
  "\226\128\157"

(** val djot_ddecay : dstyle -> ddecay **)

let djot_ddecay = function
| DSQuote -> DDPair (false, lsquo, rsquo)
| DDQuote -> DDPair (true, ldquo, rdquo)
| _ -> DDSelf

(** val djot_dwidth : dstyle -> nat **)

let djot_dwidth _ =
  S O

(** val djot_config : dconfig **)

let djot_config =
  { dc_char = djot_dchar; dc_width = djot_dwidth; dc_syntax = djot_dsyntax;
    dc_decay = djot_ddecay; dc_smart_typography = true; dc_raw_inline = true;
    dc_math = true; dc_attrs = true; dc_footnotes = true; dc_wikilinks =
    false }

(** val chars : char -> nat -> string **)

let rec chars c = function
| O -> ""
| S m ->
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (c, (chars c m))

(** val dstyles : dstyle list **)

let dstyles =
  DEmph :: (DStrong :: (DSuper :: (DSub :: (DMark :: (DInsert :: (DDelete :: (DSQuote :: (DDQuote :: []))))))))

(** val denabled : dconfig -> dstyle -> bool **)

let denabled c k =
  match c.dc_syntax k with
  | DOff -> false
  | _ -> true

(** val dstyle_at : dconfig -> char -> dstyle option **)

let dstyle_at c c0 =
  find (fun k -> (&&) (denabled c k) ((=) (c.dc_char k) c0)) dstyles

(** val with_wikilinks : bool -> dconfig -> dconfig **)

let with_wikilinks enabled c =
  { dc_char = c.dc_char; dc_width = c.dc_width; dc_syntax = c.dc_syntax;
    dc_decay = c.dc_decay; dc_smart_typography = c.dc_smart_typography;
    dc_raw_inline = c.dc_raw_inline; dc_math = c.dc_math; dc_attrs =
    c.dc_attrs; dc_footnotes = c.dc_footnotes; dc_wikilinks = enabled }

(** val bnode : bool -> inlines -> target -> inline **)

let bnode image ns tgt =
  if image then Image (ns, tgt) else Link (ns, tgt)

(** val reference_text : inline -> string **)

let rec reference_text il =
  let go =
    let rec go = function
    | [] -> ""
    | n :: rest -> (^) (reference_text (node_contents n)) (go rest)
    in go
  in
  (match il with
   | Str s -> s
   | Emph ns -> go ns
   | Strong ns -> go ns
   | Highlight ns -> go ns
   | Insert ns -> go ns
   | Delete ns -> go ns
   | Superscript ns -> go ns
   | Subscript ns -> go ns
   | Verbatim s -> s
   | Math (_, s) -> s
   | Link (ns, _) -> go ns
   | Image (ns, _) -> go ns
   | Span ns -> go ns
   | Wikilink (_, t, al) -> wiki_display t al
   | RawInline (_, s) -> s
   | Quoted (_, ns) -> go ns
   | SoftBreak -> nl
   | HardBreak -> nl
   | _ -> "")

(** val reference_inlines_text : inlines -> string **)

let reference_inlines_text ns =
  String.concat "" (map (fun n -> reference_text (node_contents n)) ns)

(** val dnode : dstyle -> inlines -> inline **)

let dnode k ns =
  match k with
  | DEmph -> Emph ns
  | DStrong -> Strong ns
  | DSuper -> Superscript ns
  | DSub -> Subscript ns
  | DMark -> Highlight ns
  | DInsert -> Insert ns
  | DDelete -> Delete ns
  | DSQuote -> Quoted (SingleQuotes, ns)
  | DDQuote -> Quoted (DoubleQuotes, ns)

type dtable = dconfig
  (* singleton inductive, whose constructor was DTable *)

(** val dchar : dtable -> dstyle -> char **)

let dchar t k =
  t.dc_char k

(** val dsyntax_of : dtable -> dstyle -> dsyntax **)

let dsyntax_of t k =
  t.dc_syntax k

(** val dwidth : dtable -> dstyle -> nat **)

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

(** val inline_attrs_enabled : dtable -> bool **)

let inline_attrs_enabled t =
  t.dc_attrs

(** val notes_enabled : dtable -> bool **)

let notes_enabled t =
  t.dc_footnotes

(** val wikilinks_enabled : dtable -> bool **)

let wikilinks_enabled t =
  t.dc_wikilinks

(** val denabled_of : dtable -> dstyle -> bool **)

let denabled_of =
  denabled

(** val dstyle_of : dtable -> char -> dstyle option **)

let dstyle_of =
  dstyle_at

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
    ((||) ((||) ((||) (dreserved c) (is_delim t c)) ((=) c hat))
      ((=) c hyphen))
    ((=) c ':')

(** val needs_escape_dest : dtable -> char -> bool **)

let needs_escape_dest t c =
  (||) ((||) (needs_escape t c) ((=) c lparen)) ((=) c rparen)

(** val escape_str : dtable -> string -> string **)

let rec escape_str t s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun c rest ->
    if needs_escape t c
    then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           ('\\',
           ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, (escape_str t rest))))
    else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, (escape_str t rest)))
    s

(** val escape_dest : dtable -> string -> string **)

let rec escape_dest t s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun c rest ->
    if needs_escape_dest t c
    then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           ('\\',
           ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, (escape_dest t rest))))
    else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, (escape_dest t rest)))
    s

(** val tick_runs_from : nat -> string -> nat list **)

let rec tick_runs_from run s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> if Nat.eqb run O then [] else run :: [])
    (fun c rest ->
    if is_tick c
    then tick_runs_from (S run) rest
    else if Nat.eqb run O
         then tick_runs_from O rest
         else run :: (tick_runs_from O rest))
    s

(** val tick_runs : string -> nat list **)

let tick_runs s =
  tick_runs_from O s

(** val first_missing : nat -> nat -> nat list -> nat **)

let rec first_missing fuel candidate runs =
  match fuel with
  | O -> candidate
  | S fuel' ->
    if existsb (Nat.eqb candidate) runs
    then first_missing fuel' (S candidate) runs
    else candidate

(** val verb_ticks : string -> nat **)

let verb_ticks s =
  first_missing (S (length s)) (S O) (tick_runs s)

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

(** val ticks : nat -> string **)

let rec ticks = function
| O -> ""
| S k ->
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (tick, (ticks k))

(** val verb_text : string -> string **)

let verb_text s =
  let d = ticks (verb_ticks s) in (^) d ((^) (pad_verb s) d)

(** val verb_safe_from : nat -> nat -> string -> bool **)

let rec verb_safe_from n run s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> negb (Nat.eqb run n))
    (fun c rest ->
    if is_tick c
    then verb_safe_from n (S run) rest
    else (&&) (negb (Nat.eqb run n)) (verb_safe_from n O rest))
    s

(** val verb_safe : nat -> string -> bool **)

let verb_safe n s =
  verb_safe_from n O s

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

(** val link_close : dtable -> string -> string -> string **)

let link_close t dst tail =
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (rbrack,
    ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (lparen,
    ((^) (escape_dest t dst)
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

(** val auto_email_from : char option -> string -> bool **)

let rec auto_email_from prev s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> false)
    (fun c rest ->
    match prev with
    | Some p ->
      if (&&) ((=) c '@') (negb ((=) p ':'))
      then true
      else auto_email_from (Some c) rest
    | None -> auto_email_from (Some c) rest)
    s

(** val auto_email : string -> bool **)

let auto_email s =
  auto_email_from None s

(** val is_alpha : char -> bool **)

let is_alpha c =
  (||) ((&&) (Ascii.leb 'a' c) (Ascii.leb c 'z'))
    ((&&) (Ascii.leb 'A' c) (Ascii.leb c 'Z'))

(** val symbol_char : char -> bool **)

let symbol_char c =
  (||)
    ((||)
      ((||) ((||) (is_alpha c) ((&&) (Ascii.leb '0' c) (Ascii.leb c '9')))
        ((=) c '_'))
      ((=) c '+'))
    ((=) c '-')

(** val auto_scheme : string -> bool **)

let rec auto_scheme s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> false)
    (fun c rest ->
    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

      (fun _ -> false)
      (fun d _ ->
      if (&&) (is_alpha c) ((=) d ':') then true else auto_scheme rest)
      rest)
    s

(** val auto_node : string -> inline **)

let auto_node s =
  if auto_email s then EmailLink s else UrlLink s

(** val auto_kind_ok : string -> bool **)

let auto_kind_ok s =
  (||) (auto_email s) (auto_scheme s)

(** val auto_text : string -> string **)

let auto_text s =
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (lt, ((^) s (one gt)))

(** val auto_region : string -> bool **)

let auto_region s =
  (&&) ((&&) (no_ws s) (no_char lt s)) (no_char gt s)

(** val auto_body_ok : string -> bool **)

let auto_body_ok s =
  (&&) (nonempty_str s) (auto_region s)

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

(** val str_last : string -> char option -> char option **)

let rec str_last s prev =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> prev)
    (fun c rest -> str_last rest (Some c))
    s

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
     (^) (bracket_open img) ((^) (go kids) (link_close t dst ""))
   | CIRef (img, kids, label) ->
     (^) (bracket_open img) ((^) (go kids) (ref_close label ""))
   | CINote label -> note_text label
   | CIAuto s -> auto_text s
   | CIRaw (fmt, s) -> raw_text fmt s
   | CIWiki (embed, t0, al) -> wiki_text embed t0 al)

(** val ci_text : dtable -> cinline list -> string **)

let rec ci_text t = function
| [] -> ""
| ci :: rest -> (^) (ci_src t ci) (ci_text t rest)

(** val ci_line : dtable -> cinline list -> string **)

let ci_line =
  ci_text

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
   | CIWiki (embed, t, al) -> mk (Wikilink (embed, t, al)))

(** val ci_inlines : cinline list -> inlines **)

let ci_inlines cis =
  map ci_ast cis

(** val ci_pair_ok : dtable -> cinline -> cinline -> bool **)

let ci_pair_ok t a b =
  match a with
  | CIStr _ -> (match b with
                | CIStr _ -> false
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
        | None -> true))

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

(** val strip_pad : string -> string **)

let strip_pad s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> s)
    (fun c rest -> if (&&) ((=) c ' ') (starts_tick rest) then rest else s)
    s

(** val trim_verb : string -> string **)

let trim_verb s =
  rev_string (strip_pad (rev_string (strip_pad s)))

type oitem =
| OIn of inline node
| OMark of attr * span * spot option

type oitems = oitem list

type frame_kind =
| FKDelim of dstyle * bool
| FKBracket of bool
| FKDest of bool

type frame = { fr_kind : frame_kind; fr_marked : bool; fr_open : span;
               fr_out : oitems }

(** val fr_src : dtable -> frame -> string **)

let fr_src t f =
  match f.fr_kind with
  | FKDelim (k, cm) -> ddecay_str t k f.fr_marked cm
  | FKBracket image -> bracket_open image
  | FKDest image -> bracket_open image

(** val fr_barrier : frame -> bool **)

let fr_barrier f =
  match f.fr_kind with
  | FKDest _ -> true
  | _ -> false

type ostate = { os_out : oitems; os_stk : frame list;
                os_word_start : spot option }

(** val ostart : ostate **)

let ostart =
  { os_out = []; os_stk = []; os_word_start = None }

(** val spot_later : spot -> spot -> spot **)

let spot_later a b =
  if Nat.ltb a.spot_line b.spot_line
  then b
  else if Nat.ltb b.spot_line a.spot_line
       then a
       else if Nat.ltb a.spot_rem b.spot_rem then a else b

(** val roles_stop : provenance -> spot **)

let roles_stop p =
  fold_left (fun acc e -> spot_later acc (snd e).span_stop) p.syntax_spans
    p.node_span.span_stop

(** val node_stop : spot -> inline node -> spot **)

let node_stop fallback n =
  match node_provenance n with
  | Some p -> roles_stop p
  | None -> fallback

(** val items_stop : spot -> oitems -> spot **)

let rec items_stop fallback = function
| [] -> fallback
| o :: _ ->
  (match o with
   | OIn n -> node_stop fallback n
   | OMark (_, spec, _) -> spec.span_stop)

(** val text_start : coq_InlineCursor -> ostate -> spot **)

let text_start h o =
  match o.os_stk with
  | [] -> items_stop h.cursor_origin o.os_out
  | f :: _ -> items_stop f.fr_open.span_stop f.fr_out

(** val remember_word_start :
    coq_PosPolicy -> coq_InlineCursor -> char -> ostate -> ostate **)

let remember_word_start h h0 c o =
  if (&&) h.pos_records (is_ws c)
  then { os_out = o.os_out; os_stk = o.os_stk; os_word_start = (Some
         h0.cursor_stop) }
  else o

(** val oword_reset : ostate -> ostate **)

let oword_reset o =
  { os_out = o.os_out; os_stk = o.os_stk; os_word_start = None }

(** val inline_prov : spot -> spot -> provenance **)

let inline_prov start stop =
  prov_at { span_start = start; span_stop = stop }

(** val imk : coq_PosPolicy -> spot -> spot -> inline -> inline node **)

let imk h start stop x =
  if h.pos_records then posnode h (inline_prov start stop) x else mk x

(** val imk_here :
    coq_PosPolicy -> coq_InlineCursor -> inline -> inline node **)

let imk_here h h0 x =
  imk h h0.cursor_start h0.cursor_stop x

(** val fr_lit : dtable -> coq_PosPolicy -> frame -> inline node **)

let fr_lit t h f =
  imk h f.fr_open.span_start f.fr_open.span_stop (Str (fr_src t f))

(** val add_inline_role :
    coq_PosPolicy -> syntax_role -> span -> inline node -> inline node **)

let add_inline_role h role r n =
  add_roles h ((role, r) :: []) n

(** val dstyle_eqb : dstyle -> dstyle -> bool **)

let dstyle_eqb a b =
  match a with
  | DEmph -> (match b with
              | DEmph -> true
              | _ -> false)
  | DStrong -> (match b with
                | DStrong -> true
                | _ -> false)
  | DSuper -> (match b with
               | DSuper -> true
               | _ -> false)
  | DSub -> (match b with
             | DSub -> true
             | _ -> false)
  | DMark -> (match b with
              | DMark -> true
              | _ -> false)
  | DInsert -> (match b with
                | DInsert -> true
                | _ -> false)
  | DDelete -> (match b with
                | DDelete -> true
                | _ -> false)
  | DSQuote -> (match b with
                | DSQuote -> true
                | _ -> false)
  | DDQuote -> (match b with
                | DDQuote -> true
                | _ -> false)

(** val dmatch : dstyle -> bool -> frame -> bool **)

let dmatch k m f =
  match f.fr_kind with
  | FKDelim (k', _) -> (&&) (dstyle_eqb k k') (Bool0.eqb m f.fr_marked)
  | _ -> false

(** val merge_text_pos : pos -> pos -> pos **)

let merge_text_pos left right =
  match left with
  | NoPos -> left
  | SomePos p ->
    (match right with
     | NoPos -> left
     | SomePos q ->
       SomePos { node_span = { span_start = p.node_span.span_start;
         span_stop = q.node_span.span_stop }; syntax_spans =
         (app p.syntax_spans q.syntax_spans); part_spans = PNone })

(** val isnoc : inline node -> inlines -> inlines **)

let isnoc n out = match out with
| [] -> n :: out
| n0 :: rest ->
  let Node (p, a, x) = n0 in
  (match a with
   | [] ->
     (match x with
      | Str t ->
        let Node (q, a0, x0) = n in
        (match a0 with
         | [] ->
           (match x0 with
            | Str s ->
              (Node ((merge_text_pos p q), [], (Str ((^) t s)))) :: rest
            | _ -> n :: out)
         | _ :: _ -> n :: out)
      | _ -> n :: out)
   | _ :: _ -> n :: out)

(** val istarts_str : inlines -> bool **)

let istarts_str = function
| [] -> false
| n :: _ ->
  let Node (_, a, x) = n in
  (match a with
   | [] -> (match x with
            | Str _ -> true
            | _ -> false)
   | _ :: _ -> false)

(** val osnoc : oitem -> oitems -> oitems **)

let osnoc n out = match out with
| [] -> n :: out
| o :: rest ->
  (match o with
   | OIn n0 ->
     let Node (p, a, x) = n0 in
     (match a with
      | [] ->
        (match x with
         | Str t ->
           (match n with
            | OIn n1 ->
              let Node (q, a0, x0) = n1 in
              (match a0 with
               | [] ->
                 (match x0 with
                  | Str s ->
                    (OIn (Node ((merge_text_pos p q), [], (Str
                      ((^) t s))))) :: rest
                  | _ -> n :: out)
               | _ :: _ -> n :: out)
            | OMark (_, _, _) -> n :: out)
         | _ -> n :: out)
      | _ :: _ -> n :: out)
   | OMark (_, _, _) -> n :: out)

(** val oapp : oitems -> oitems -> oitems **)

let rec oapp cur out =
  match cur with
  | [] -> out
  | n :: rest ->
    (match rest with
     | [] -> osnoc n out
     | _ :: _ -> n :: (oapp rest out))

(** val oemit : inline node -> ostate -> ostate **)

let oemit n o =
  let word = o.os_word_start in
  (match o.os_stk with
   | [] ->
     { os_out = ((OIn n) :: o.os_out); os_stk = []; os_word_start = word }
   | f :: rest ->
     { os_out = o.os_out; os_stk = ({ fr_kind = f.fr_kind; fr_marked =
       f.fr_marked; fr_open = f.fr_open; fr_out = ((OIn
       n) :: f.fr_out) } :: rest); os_word_start = word })

(** val omark : attr -> span -> ostate -> ostate **)

let omark a spec o =
  match o.os_stk with
  | [] ->
    { os_out = ((OMark (a, spec, o.os_word_start)) :: o.os_out); os_stk = [];
      os_word_start = None }
  | f :: rest ->
    { os_out = o.os_out; os_stk = ({ fr_kind = f.fr_kind; fr_marked =
      f.fr_marked; fr_open = f.fr_open; fr_out = ((OMark (a, spec,
      o.os_word_start)) :: f.fr_out) } :: rest); os_word_start = None }

(** val flush_text_at :
    coq_PosPolicy -> coq_InlineCursor -> string -> ostate -> ostate **)

let flush_text_at h h0 txt o =
  if nonempty_str txt
  then oemit (imk h (text_start h0 o) h0.cursor_start (Str txt)) o
  else o

(** val flush_text_to_at :
    coq_PosPolicy -> coq_InlineCursor -> spot -> string -> ostate -> ostate **)

let flush_text_to_at h h0 stop txt o =
  if nonempty_str txt
  then oemit (imk h (text_start h0 o) stop (Str txt)) o
  else o

(** val opush_at : dstyle -> bool -> bool -> span -> ostate -> ostate **)

let opush_at k m cm open0 o =
  { os_out = o.os_out; os_stk = ({ fr_kind = (FKDelim (k, cm)); fr_marked =
    m; fr_open = open0; fr_out = [] } :: o.os_stk); os_word_start =
    o.os_word_start }

(** val previous_spot : spot -> spot **)

let previous_spot p =
  { spot_line = p.spot_line; spot_rem = (S p.spot_rem) }

(** val source_shape : string -> (nat * nat) * nat **)

let rec source_shape s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> ((O, O), O))
    (fun c rest ->
    let (p, total) = source_shape rest in
    let (lines, first) = p in
    if (=) c nl_char
    then (((S lines), O), (S total))
    else ((lines, (S first)), (S total)))
    s

(** val spot_before : spot -> string -> spot **)

let spot_before p s =
  let (p0, total) = source_shape s in
  let (lines, first) = p0 in
  if Nat.eqb lines O
  then { spot_line = p.spot_line; spot_rem = (add p.spot_rem total) }
  else { spot_line = (sub p.spot_line lines); spot_rem = first }

(** val spot_plus : nat -> spot -> spot **)

let spot_plus n p =
  { spot_line = p.spot_line; spot_rem = (add p.spot_rem n) }

(** val dtoken_span :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> dstyle -> bool -> span **)

let dtoken_span t h h0 k marked =
  pspan h { span_start =
    (spot_before h0.cursor_start
      ((^) (if marked then one lbrace else "") (dtoken t k)));
    span_stop = h0.cursor_start }

(** val opush :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> dstyle -> bool -> ostate
    -> ostate **)

let opush t h h0 k m o =
  opush_at k m false (dtoken_span t h h0 k m) o

(** val bpush :
    coq_PosPolicy -> coq_InlineCursor -> bool -> ostate -> ostate **)

let bpush h h0 image o =
  let start = if image then previous_spot h0.cursor_start else h0.cursor_start
  in
  { os_out = o.os_out; os_stk = ({ fr_kind = (FKBracket image); fr_marked =
  false; fr_open =
  (pspan h { span_start = start; span_stop = h0.cursor_stop }); fr_out =
  [] } :: o.os_stk); os_word_start = o.os_word_start }

(** val dpush : bool -> span -> ostate -> ostate **)

let dpush image open0 o =
  { os_out = o.os_out; os_stk = ({ fr_kind = (FKDest image); fr_marked =
    false; fr_open = open0; fr_out = [] } :: o.os_stk); os_word_start =
    o.os_word_start }

(** val last_ws_split : string -> string * string **)

let rec last_ws_split s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> ("", ""))
    (fun c rest ->
    let (pre, w) = last_ws_split rest in
    ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

       (fun _ ->
       if is_ws c
       then ((one c), w)
       else ("",
              ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

              (c, w))))
       (fun _ _ ->
       (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

       (c, pre)), w))
       pre))
    s

(** val split_text_pos : pos -> spot option -> pos * pos **)

let split_text_pos p word_start =
  match p with
  | NoPos -> (p, p)
  | SomePos pr ->
    (match word_start with
     | Some w ->
       ((SomePos
         (prov_at { span_start = pr.node_span.span_start; span_stop = w })),
         (SomePos
         (prov_at { span_start = w; span_stop = pr.node_span.span_stop })))
     | None -> (p, p))

(** val oattach_list :
    coq_PosPolicy -> attr -> span -> spot option -> inlines -> inlines **)

let oattach_list h a spec word_start out = match out with
| [] -> out
| n :: rest ->
  let Node (p, a0, x) = n in
  (match a0 with
   | [] ->
     (match x with
      | Str s ->
        let (pre, w) = last_ws_split s in
        if nonempty_str w
        then (match a with
              | [] -> out
              | _ :: _ ->
                let (pp, wp) = split_text_pos p word_start in
                let out1 =
                  if nonempty_str pre
                  then isnoc (Node (pp, [], (Str pre))) rest
                  else rest
                in
                isnoc
                  (add_inline_role h RAttrSpec spec (Node (wp, a, (Str w))))
                  out1)
        else out
      | SoftBreak -> out
      | _ ->
        (add_inline_role h RAttrSpec spec
          (let Node (p0, a', v) = n in Node (p0, (attr_merge a a'), v))) :: rest)
   | _ :: _ ->
     (match x with
      | SoftBreak -> out
      | _ ->
        (add_inline_role h RAttrSpec spec
          (let Node (p0, a', v) = n in Node (p0, (attr_merge a a'), v))) :: rest))

(** val oresolve_go : coq_PosPolicy -> oitems -> inlines * bool **)

let rec oresolve_go h = function
| [] -> ([], false)
| o :: rest ->
  (match o with
   | OIn n ->
     let (out, m) = oresolve_go h rest in
     ((if m then isnoc n out else n :: out), false)
   | OMark (a, spec, word_start) ->
     let (out, _) = oresolve_go h rest in
     let out' = oattach_list h a spec word_start out in
     (out', (istarts_str out')))

(** val oresolve : coq_PosPolicy -> oitems -> inlines **)

let oresolve h l =
  fst (oresolve_go h l)

(** val oclose_go :
    dtable -> coq_PosPolicy -> dstyle -> bool -> oitems -> frame list ->
    ((oitems * span) * frame list) option **)

let rec oclose_go t h k m pend = function
| [] -> None
| f :: rest ->
  let content = oapp pend f.fr_out in
  if dmatch k m f
  then if nonempty content then Some ((content, f.fr_open), rest) else None
  else if fr_barrier f
       then None
       else oclose_go t h k m (oapp content ((OIn (fr_lit t h f)) :: [])) rest

(** val oclose_barred_go : dstyle -> bool -> bool -> frame list -> bool **)

let rec oclose_barred_go k m past = function
| [] -> false
| f :: rest ->
  if dmatch k m f
  then past
  else oclose_barred_go k m ((||) past (fr_barrier f)) rest

(** val oclose_barred : dstyle -> bool -> ostate -> bool **)

let oclose_barred k m o =
  oclose_barred_go k m false o.os_stk

(** val oclose :
    dtable -> coq_PosPolicy -> dstyle -> bool -> spot -> ostate -> ostate
    option **)

let oclose t h k m stop o =
  match oclose_go t h k m [] o.os_stk with
  | Some p ->
    let (p0, rest) = p in
    let (content, open0) = p0 in
    Some
    (oemit (imk h open0.span_start stop (dnode k (rev (oresolve h content))))
      { os_out = o.os_out; os_stk = rest; os_word_start = o.os_word_start })
  | None -> None

(** val bclose_go :
    dtable -> coq_PosPolicy -> oitems -> frame list ->
    (((oitems * bool) * span) * frame list) option **)

let rec bclose_go t h pend = function
| [] -> None
| f :: rest ->
  let content = oapp pend f.fr_out in
  (match f.fr_kind with
   | FKDelim (_, _) ->
     bclose_go t h (oapp content ((OIn (fr_lit t h f)) :: [])) rest
   | FKBracket image -> Some (((content, image), f.fr_open), rest)
   | FKDest _ -> None)

(** val bclose :
    dtable -> coq_PosPolicy -> ostate -> (((inlines * bool) * span) * ostate)
    option **)

let bclose t h o =
  match bclose_go t h [] o.os_stk with
  | Some p ->
    let (p0, rest) = p in
    let (p1, open0) = p0 in
    let (content, image) = p1 in
    Some ((((rev (oresolve h content)), image), open0), { os_out = o.os_out;
    os_stk = rest; os_word_start = o.os_word_start })
  | None -> None

(** val bunpush : ostate -> ((bool * span) * ostate) option **)

let bunpush o =
  match o.os_stk with
  | [] -> None
  | f :: rest ->
    let { fr_kind = fr_kind0; fr_marked = _; fr_open = open0; fr_out =
      fr_out0 } = f
    in
    (match fr_kind0 with
     | FKBracket image ->
       (match fr_out0 with
        | [] ->
          Some ((image, open0), { os_out = o.os_out; os_stk = rest;
            os_word_start = o.os_word_start })
        | _ :: _ -> None)
     | _ -> None)

(** val opop_str : ostate -> string * ostate **)

let opop_str o =
  match o.os_stk with
  | [] ->
    (match o.os_out with
     | [] -> ("", o)
     | o0 :: rest ->
       (match o0 with
        | OIn n ->
          let Node (_, a, x) = n in
          (match a with
           | [] ->
             (match x with
              | Str s ->
                (s, { os_out = rest; os_stk = []; os_word_start =
                  o.os_word_start })
              | _ -> ("", o))
           | _ :: _ -> ("", o))
        | OMark (_, _, _) -> ("", o)))
  | f :: fs ->
    (match f.fr_out with
     | [] -> ("", o)
     | o0 :: rest ->
       (match o0 with
        | OIn n ->
          let Node (_, a, x) = n in
          (match a with
           | [] ->
             (match x with
              | Str s ->
                (s, { os_out = o.os_out; os_stk = ({ fr_kind = f.fr_kind;
                  fr_marked = f.fr_marked; fr_open = f.fr_open; fr_out =
                  rest } :: fs); os_word_start = o.os_word_start })
              | _ -> ("", o))
           | _ :: _ -> ("", o))
        | OMark (_, _, _) -> ("", o)))

(** val bflat :
    coq_PosPolicy -> coq_InlineCursor -> inlines -> string -> ostate ->
    string * ostate **)

let rec bflat h h0 kids txt o =
  match kids with
  | [] -> (txt, o)
  | n :: rest ->
    let Node (_, a, x) = n in
    (match a with
     | [] ->
       (match x with
        | Str s -> bflat h h0 rest ((^) txt s) o
        | _ -> bflat h h0 rest "" (oemit n (flush_text_at h h0 txt o)))
     | _ :: _ -> bflat h h0 rest "" (oemit n (flush_text_at h h0 txt o)))

(** val bsplit_nl :
    coq_PosPolicy -> coq_InlineCursor -> string -> string -> ostate ->
    string * ostate **)

let rec bsplit_nl h h0 s txt o =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> (txt, o))
    (fun c rest ->
    if (=) c nl_char
    then bsplit_nl h h0 rest ""
           (oemit (imk_here h h0 SoftBreak) (flush_text_at h h0 txt o))
    else bsplit_nl h h0 rest ((^) txt (one c)) o)
    s

(** val bclosed_lit :
    coq_PosPolicy -> coq_InlineCursor -> inlines -> bool -> ostate ->
    string * ostate **)

let bclosed_lit h h0 kids image o =
  let (pre, o1) = opop_str o in
  let (txt, o2) = bflat h h0 kids ((^) pre (bracket_open image)) o1 in
  (((^) txt (one rbrack)), o2)

(** val bspan_lit :
    coq_PosPolicy -> coq_InlineCursor -> inlines -> bool -> string -> ostate
    -> string * ostate **)

let bspan_lit h h0 kids image src o =
  let (txt, o') = bclosed_lit h h0 kids image o in
  bsplit_nl h h0 src ((^) txt (one lbrace)) o'

(** val battr_lit :
    coq_PosPolicy -> coq_InlineCursor -> string -> string -> ostate ->
    string * ostate **)

let battr_lit h h0 src txt o =
  bsplit_nl h h0 src ((^) txt (one lbrace)) o

(** val blit_prev : string -> char option **)

let blit_prev t =
  str_last t (Some nl_char)

(** val bref_lit :
    coq_PosPolicy -> coq_InlineCursor -> inlines -> bool -> string -> ostate
    -> string * ostate **)

let bref_lit h h0 kids image label o =
  let (txt, o') = bclosed_lit h h0 kids image o in
  (((^) txt ((^) (one lbrack) label)), o')

(** val drop_nl : string -> string **)

let rec drop_nl s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun c rest ->
    if (=) c nl_char
    then drop_nl rest
    else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, (drop_nl rest)))
    s

(** val oflatten :
    dtable -> coq_PosPolicy -> oitems -> frame list -> oitems -> oitems **)

let rec oflatten t h pend stk bottom =
  match stk with
  | [] -> oapp pend bottom
  | f :: rest ->
    oflatten t h (oapp (oapp pend f.fr_out) ((OIn (fr_lit t h f)) :: []))
      rest bottom

(** val oitems_of : dtable -> coq_PosPolicy -> ostate -> oitems **)

let oitems_of t h o =
  oflatten t h [] o.os_stk o.os_out

(** val ofinish : dtable -> coq_PosPolicy -> ostate -> inlines **)

let ofinish t h o =
  oresolve h (oitems_of t h o)

type vkind =
| VVerb
| VMath of math_style

(** val vnode : vkind -> string -> inline **)

let vnode vk s =
  match vk with
  | VVerb -> Verbatim s
  | VMath st -> Math (st, s)

(** val vkind_verb : vkind -> bool **)

let vkind_verb = function
| VVerb -> true
| VMath _ -> false

type iscan =
| IText of bool * string * char option * ostate
| IEscWs of string * string * char option * ostate
| IBrace of string * char option * ostate
| IDelim of dstyle * nat * string * char option * bool * ostate
| IOpen of nat * vkind * ostate
| IVerb of nat * nat * string * vkind * ostate
| IDollar of bool * string * char option * ostate
| IPeriod of bool * string * char option * ostate
| IDash of nat * string * char option * ostate
| IBang of string * char option * ostate
| IClosed of string * ostate
| ISpan of inlines * bool * span * aparser * string * ostate
| IAttr of aparser * string * string * char option * iscan * ostate
| IReference of inlines * bool * span * string * ostate
| INote of bool * bool * string * span * ostate
| IWiki of bool * bool * bool * string * span * ostate
| IDest of inlines * bool * span * bool * nat * string * iscan * ostate
| IAuto of string * string * ostate
| ISymbol of string * string * iscan * ostate
| IRaw of string * string * ostate

(** val note_pos : string -> char option -> bool **)

let note_pos txt prev =
  (&&) (negb (nonempty_str txt))
    (match prev with
     | Some p -> (=) p lbrack
     | None -> false)

(** val ilead :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> string -> char
    option -> ostate -> iscan **)

let ilead t h h0 c txt prev o =
  if is_bslash c
  then IText (true, txt, (Some c), o)
  else if is_tick c
       then IOpen ((S O), VVerb, (flush_text_at h h0 txt o))
       else if (=) c dollar
            then IDollar (false, txt, prev, o)
            else if (=) c period
                 then IPeriod (false, txt, prev, o)
                 else if (=) c hyphen
                      then IDash ((S O), txt, prev, o)
                      else if (=) c lbrace
                           then IBrace (txt, prev, o)
                           else if (=) c bang
                                then IBang (txt, prev, o)
                                else if (=) c lt
                                     then IAuto ("", txt, o)
                                     else if (=) c ':'
                                          then ISymbol ("", txt, (IText
                                                 (false, ((^) txt (one c)),
                                                 (Some c),
                                                 (remember_word_start h h0 c
                                                   o))),
                                                 o)
                                          else if (=) c lbrack
                                               then (match if (&&)
                                                                (note_pos txt
                                                                  prev)
                                                                (wikilinks_enabled
                                                                  t)
                                                           then bunpush o
                                                           else None with
                                                     | Some p ->
                                                       let (p0, o') = p in
                                                       let (image, open0) = p0
                                                       in
                                                       IWiki (false, false,
                                                       image, "", open0, o')
                                                     | None ->
                                                       IText (false, "",
                                                         (Some lbrack),
                                                         (bpush h h0 false
                                                           (flush_text_at h
                                                             h0 txt o))))
                                               else if (=) c rbrack
                                                    then IClosed (txt, o)
                                                    else (match if (&&)
                                                                    ((&&)
                                                                    ((=) c
                                                                    hat)
                                                                    (note_pos
                                                                    txt prev))
                                                                    (notes_enabled
                                                                    t)
                                                                then bunpush o
                                                                else None with
                                                          | Some p ->
                                                            let (p0, o') = p
                                                            in
                                                            let (image, open0) =
                                                              p0
                                                            in
                                                            INote (false,
                                                            image, "", open0,
                                                            o')
                                                          | None ->
                                                            (match dstyle_of
                                                                    t c with
                                                             | Some k ->
                                                               IDelim (k, O,
                                                                 txt, prev,
                                                                 false, o)
                                                             | None ->
                                                               IText (false,
                                                                 ((^) txt
                                                                   (one c)),
                                                                 (Some c),
                                                                 (remember_word_start
                                                                   h h0 c o))))

(** val idest_open :
    coq_PosPolicy -> coq_InlineCursor -> inlines -> bool -> span -> ostate ->
    iscan **)

let idest_open h h0 kids image open0 o =
  let (txt, o') = bflat h h0 kids "" (dpush image open0 o) in
  IText (false, ((^) txt ((^) (one rbrack) (one lparen))), (Some lparen), o')

(** val null : 'a1 list -> bool **)

let null = function
| [] -> true
| _ :: _ -> false

(** val ellipsis : string **)

let ellipsis =
  "\226\128\166"

(** val endash : string **)

let endash =
  "\226\128\147"

(** val emdash : string **)

let emdash =
  "\226\128\148"

(** val periods : bool -> string **)

let periods = function
| true ->
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (period, (one period))
| false -> one period

(** val typography_ellipsis : dtable -> string **)

let typography_ellipsis t =
  if smart_typography t then ellipsis else chars period (S (S (S O)))

(** val srep : string -> nat -> string **)

let rec srep s = function
| O -> ""
| S m -> (^) s (srep s m)

(** val dash_counts : nat -> (nat * nat) * nat **)

let dash_counts n =
  if Nat.eqb (Nat.modulo n (S (S (S O)))) O
  then (((Nat.div n (S (S (S O)))), O), O)
  else if Nat.eqb (Nat.modulo n (S (S O))) O
       then ((O, (Nat.div n (S (S O)))), O)
       else if Nat.eqb n (S O)
            then ((O, O), (S O))
            else if Nat.eqb (Nat.modulo n (S (S (S (S (S (S O))))))) (S (S (S
                      (S (S O)))))
                 then (((Nat.div (sub n (S (S O))) (S (S (S O)))), (S O)), O)
                 else (((Nat.div (sub n (S (S (S (S O))))) (S (S (S O)))), (S
                        (S O))), O)

(** val dashes : nat -> string **)

let dashes n =
  let (p, lit) = dash_counts n in
  let (em, en) = p in
  (^) (srep emdash em) ((^) (srep endash en) (chars hyphen lit))

(** val typography_dashes : dtable -> nat -> string **)

let typography_dashes t n =
  if smart_typography t then dashes n else chars hyphen n

(** val dollars : bool -> string **)

let dollars = function
| true -> (^) (one dollar) (one dollar)
| false -> one dollar

(** val auto_lit : string -> string -> string **)

let auto_lit src txt =
  (^) txt
    ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (lt, src))

(** val islice_end : dtable -> iscan -> iscan **)

let rec islice_end t st = match st with
| IText (esc, txt, _, o) ->
  if esc then IText (false, ((^) txt (one bslash)), (Some bslash), o) else st
| IBrace (txt, _, o) ->
  IText (false, ((^) txt (one lbrace)), (Some lbrace), o)
| IPeriod (two, txt, _, o) ->
  IText (false, ((^) txt (periods two)), (Some period), o)
| IDash (n, txt, _, o) ->
  IText (false, ((^) txt (typography_dashes t n)), (Some hyphen), o)
| IClosed (txt, o) -> IText (false, ((^) txt (one rbrack)), (Some rbrack), o)
| IAuto (src, txt, o) ->
  IText (false, (auto_lit src txt), (blit_prev (auto_lit src txt)), o)
| ISymbol (_, _, sh, _) -> islice_end t sh
| _ -> st

(** val iattr_mark :
    coq_PosPolicy -> coq_InlineCursor -> string -> attr -> string -> ostate
    -> iscan **)

let iattr_mark h h0 src a txt o =
  let spec_start =
    spot_before h0.cursor_start
      ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      (lbrace, src))
  in
  let spec = pspan h { span_start = spec_start; span_stop = h0.cursor_stop }
  in
  IText (false, "", (Some rbrace),
  (omark a spec (flush_text_to_at h h0 spec_start txt o)))

(** val iattr_feed :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> aparser -> string
    -> string -> char option -> iscan -> ostate -> iscan **)

let iattr_feed t h h0 c p src txt prev sh o =
  let p' = astep p c in
  if ap_failed p'
  then sh
  else if ap_done p'
       then iattr_mark h h0 src p'.ap_attrs txt o
       else IAttr (p', ((^) src (one c)), txt, prev, (islice_end t sh), o)

(** val idelim_marked : dstyle -> nat -> string -> ostate -> iscan **)

let idelim_marked k extra txt o =
  IDelim (k, extra, txt, None, true, o)

(** val oopen_marked :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> dstyle -> bool -> string
    -> ostate -> ostate **)

let oopen_marked t h h0 k cm txt o =
  let open0 = dtoken_span t h h0 k true in
  opush_at k true cm open0 (flush_text_to_at h h0 open0.span_start txt o)

(** val idelim_open_marked :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> dstyle -> bool -> string
    -> ostate -> iscan **)

let idelim_open_marked t h h0 k cm txt o =
  IText (false, "", (Some (dchar t k)), (oopen_marked t h h0 k cm txt o))

(** val idelim_run : dtable -> dstyle -> nat -> bool -> string **)

let idelim_run t k extra marked =
  (^) (if marked then one lbrace else "") (chars (dchar t k) (S extra))

(** val ibrace_step_at :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> bool -> char -> string ->
    char option -> ostate -> iscan **)

let ibrace_step_at t h h0 attrs_enabled c txt prev o =
  match dstyle_of t c with
  | Some k -> idelim_marked k O txt o
  | None ->
    if attrs_enabled
    then iattr_feed t h h0 c ap_init "" txt prev
           (ilead t h h0 c ((^) txt (one lbrace)) (Some lbrace) o) o
    else let (t0, o') = battr_lit h h0 "" txt o in
         ilead t h h0 c t0 (blit_prev t0) o'

(** val ospan_bang :
    coq_PosPolicy -> coq_InlineCursor -> bool -> ostate -> ostate **)

let ospan_bang h h0 image o =
  if image
  then let (pre, o1) = opop_str o in
       flush_text_at h h0 ((^) pre (one bang)) o1
  else o

(** val ispan_feed :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> inlines -> bool ->
    span -> aparser -> string -> ostate -> iscan **)

let ispan_feed t h h0 c kids image open0 p src o =
  let p' = astep p c in
  if ap_failed p'
  then let (txt, o') = bspan_lit h h0 kids image src o in
       ilead t h h0 c txt (blit_prev txt) o'
  else if ap_done p'
       then let spec_start =
              spot_before h0.cursor_start
                ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                (lbrace, src))
            in
            let spec = { span_start = spec_start; span_stop = h0.cursor_stop }
            in
            IText (false, "", (Some rbrace),
            (oemit
              (add_inline_role h RAttrSpec spec (Node
                ((h.mkpos (inline_prov open0.span_start spec_start)),
                p'.ap_attrs, (Span kids))))
              (ospan_bang h h0 image o)))
       else ISpan (kids, image, open0, p', ((^) src (one c)), o)

(** val inote_step :
    coq_PosPolicy -> coq_InlineCursor -> char -> bool -> bool -> string ->
    span -> ostate -> iscan **)

let inote_step h h0 c esc image label open0 o =
  if esc
  then INote (false, image, ((^) label ((^) (one bslash) (one c))), open0, o)
  else if is_bslash c
       then INote (true, image, label, open0, o)
       else if (=) c rbrack
            then IText (false, "", (Some rbrack),
                   (oemit
                     (imk h open0.span_start h0.cursor_stop
                       (FootnoteReference (normalize_label label)))
                     (ospan_bang h h0 image o)))
            else INote (false, image, ((^) label (one c)), open0, o)

(** val iauto_step :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> string -> string
    -> ostate -> iscan **)

let iauto_step t h h0 c src txt o =
  if (&&) ((&&) ((=) c gt) (auto_body_ok src)) (auto_kind_ok src)
  then let start =
         spot_before h0.cursor_start
           ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (lt, src))
       in
       IText (false, "", (Some gt),
       (oemit (imk h start h0.cursor_stop (auto_node src))
         (flush_text_to_at h h0 start txt o)))
  else if (||) ((||) ((=) c gt) (is_ws c)) ((=) c lt)
       then ilead t h h0 c (auto_lit src txt) (blit_prev (auto_lit src txt)) o
       else IAuto (((^) src (one c)), txt, o)

(** val isymbol_step :
    coq_PosPolicy -> coq_InlineCursor -> char -> string -> string -> ostate
    -> iscan -> iscan **)

let isymbol_step h h0 c alias txt o sh' =
  if symbol_char c
  then ISymbol (((^) alias (one c)), txt, sh', o)
  else if (&&) ((=) c ':') (nonempty_str alias)
       then let start = spot_before h0.cursor_start ((^) (one ':') alias) in
            IText (false, "", (Some c),
            (oemit (imk h start h0.cursor_stop (Symbol alias))
              (flush_text_to_at h h0 start txt o)))
       else sh'

(** val iraw_lit : string -> string **)

let iraw_lit spec =
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (lbrace, spec)

(** val iraw_step_at :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> bool -> char -> string ->
    string -> ostate -> iscan **)

let iraw_step_at t h h0 attrs_enabled c spec txt o =
  let vstop =
    spot_before h0.cursor_start
      ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      (lbrace, spec))
  in
  if (&&) ((=) c rbrace) (raw_spec_ok spec)
  then if raw_inline_enabled t
       then IText (false, "", (Some rbrace),
              (oemit
                (imk h (text_start h0 o) h0.cursor_stop (RawInline
                  ((raw_format spec), txt)))
                o))
       else ilead t h h0 c (iraw_lit spec) (blit_prev (iraw_lit spec))
              (oemit (imk h (text_start h0 o) vstop (Verbatim txt)) o)
  else if (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

            (fun _ -> negb ((=) c eqchar))
            (fun _ _ -> (||) ((=) c rbrace) (raw_stop c))
            spec
       then let closed =
              oemit (imk h (text_start h0 o) vstop (Verbatim txt)) o
            in
            ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

               (fun _ ->
               ibrace_step_at t h h0 attrs_enabled c "" (Some tick) closed)
               (fun _ _ ->
               ilead t h h0 c (iraw_lit spec) (blit_prev (iraw_lit spec))
                 closed)
               spec)
       else IRaw (((^) spec (one c)), txt, o)

(** val bnote_lit :
    coq_PosPolicy -> coq_InlineCursor -> bool -> bool -> string -> ostate ->
    string * ostate **)

let bnote_lit _ _ esc image label o =
  let (pre, o1) = opop_str o in
  (((^) pre
     ((^) (bracket_open image)
       ((^) (one hat) ((^) label (if esc then one bslash else ""))))),
  o1)

(** val wiki_split : string -> string * string option **)

let rec wiki_split s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> ("", None))
    (fun c rest ->
    if is_bslash c
    then ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

            (fun _ -> ((one c), None))
            (fun c' rest' ->
            let (t, al) = wiki_split rest' in
            (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

            (c,
            ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

            (c', t)))), al))
            rest)
    else if (=) c vbar
         then ("", (Some rest))
         else let (t, al) = wiki_split rest in
              (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

              (c, t)), al))
    s

(** val wiki_lit : bool -> bool -> bool -> string -> string **)

let wiki_lit esc rb image region =
  (^) (bracket_open image)
    ((^) (one lbrack)
      ((^) region
        ((^) (if rb then one rbrack else "") (if esc then one bslash else ""))))

(** val bwiki_lit :
    bool -> bool -> bool -> string -> ostate -> string * ostate **)

let bwiki_lit esc rb image region o =
  let (pre, o1) = opop_str o in (((^) pre (wiki_lit esc rb image region)), o1)

(** val iwiki_close :
    coq_PosPolicy -> coq_InlineCursor -> bool -> string -> span -> ostate ->
    iscan **)

let iwiki_close h h0 image region open0 o =
  let (t, al) = wiki_split region in
  ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

     (fun _ ->
     let (txt, o') = bwiki_lit false true image region o in
     IText (false, ((^) txt (one rbrack)), (Some rbrack), o'))
     (fun _ _ -> IText (false, "", (Some rbrack),
     (oemit (imk h open0.span_start h0.cursor_stop (Wikilink (image, t, al)))
       o)))
     t)

(** val iwiki_step :
    coq_PosPolicy -> coq_InlineCursor -> char -> bool -> bool -> bool ->
    string -> span -> ostate -> iscan **)

let iwiki_step h h0 c esc rb image region open0 o =
  if esc
  then IWiki (false, false, image, ((^) region ((^) (one bslash) (one c))),
         open0, o)
  else if (&&) rb ((=) c rbrack)
       then iwiki_close h h0 image region open0 o
       else let region' = if rb then (^) region (one rbrack) else region in
            if is_bslash c
            then IWiki (true, false, image, region', open0, o)
            else if (=) c rbrack
                 then IWiki (false, true, image, region', open0, o)
                 else IWiki (false, false, image, ((^) region' (one c)),
                        open0, o)

(** val ibang_step :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> string -> char
    option -> ostate -> iscan **)

let ibang_step t h h0 c txt _ o =
  if (=) c lbrack
  then IText (false, "", (Some lbrack),
         (bpush h h0 true
           (flush_text_to_at h h0 (previous_spot h0.cursor_start) txt o)))
  else ilead t h h0 c ((^) txt (one bang)) (Some bang) o

(** val idelim_lit : dtable -> dstyle -> string -> bool -> string **)

let idelim_lit t k txt marker =
  (^) txt (ddecay_str t k false marker)

(** val idelim_lit_prev : dtable -> dstyle -> bool -> char option **)

let idelim_lit_prev t k marker =
  Some (if marker then rbrace else dchar t k)

(** val idelim_done :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> dstyle -> string -> char
    option -> bool -> char option -> ostate -> iscan **)

let idelim_done t h h0 k txt before marker next o =
  if (&&) ((&&) (dbare t k before) (negb marker)) (nonspace_at next)
  then IText (false, "", (Some (dchar t k)),
         (opush t h h0 k false
           (flush_text_to_at h h0 (dtoken_span t h h0 k false).span_start txt
             o)))
  else IText (false, (idelim_lit t k txt marker),
         (idelim_lit_prev t k marker), o)

(** val idelim_resolve :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> dstyle -> string -> char
    option -> bool -> char option -> ostate -> iscan **)

let idelim_resolve t h h0 k txt before marker next o =
  if (||) (nonspace_at before) marker
  then (match oclose t h k marker
                (if marker then h0.cursor_stop else h0.cursor_start)
                (flush_text_to_at h h0
                  (dtoken_span t h h0 k false).span_start txt o) with
        | Some o' ->
          IText (false, "", (Some (if marker then rbrace else dchar t k)), o')
        | None ->
          if oclose_barred k marker o
          then IText (false, (idelim_lit t k txt marker),
                 (idelim_lit_prev t k marker), o)
          else idelim_done t h h0 k txt before marker next o)
  else idelim_done t h h0 k txt before marker next o

(** val idollar_step :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> bool -> string ->
    char option -> ostate -> iscan **)

let idollar_step t h h0 c two txt prev o =
  if (=) c dollar
  then if two
       then IDollar (true, ((^) txt (one dollar)), prev, o)
       else IDollar (true, txt, prev, o)
  else if (&&) (is_tick c) (math_enabled t)
       then IOpen ((S O), (VMath (if two then DisplayMath else InlineMath)),
              (flush_text_to_at h h0
                (spot_before h0.cursor_start (dollars two)) txt o))
       else ilead t h h0 c ((^) txt (dollars two)) (Some dollar) o

(** val iperiod_step :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> bool -> string ->
    char option -> ostate -> iscan **)

let iperiod_step t h h0 c two txt prev o =
  if (=) c period
  then if two
       then IText (false, ((^) txt (typography_ellipsis t)), (Some c), o)
       else IPeriod (true, txt, prev, o)
  else ilead t h h0 c ((^) txt (periods two)) (Some period) o

(** val idash_step :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> nat -> string ->
    char option -> ostate -> iscan **)

let idash_step t h h0 c n txt prev o =
  if (=) c hyphen
  then IDash ((S n), txt, prev, o)
  else if (=) c rbrace
       then (match dstyle_of t hyphen with
             | Some k ->
               if Nat.leb (dwidth t k) n
               then idelim_resolve t h h0 k
                      ((^) txt (typography_dashes t (sub n (dwidth t k))))
                      None true (Some c) o
               else IText (false,
                      ((^) txt ((^) (typography_dashes t n) (one rbrace))),
                      (Some rbrace), o)
             | None ->
               IText (false,
                 ((^) txt ((^) (typography_dashes t n) (one rbrace))), (Some
                 rbrace), o))
       else ilead t h h0 c ((^) txt (typography_dashes t n)) (Some hyphen) o

(** val iresolve :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> iscan -> iscan **)

let iresolve t h h0 st = match st with
| IBrace (txt, _, o) ->
  IText (false, ((^) txt (one lbrace)), (Some lbrace), o)
| IDelim (k, extra, txt, before, marked, o) ->
  if Nat.ltb (S extra) (dwidth t k)
  then IText (false, ((^) txt (idelim_run t k extra marked)), (Some
         (dchar t k)), o)
  else if marked
       then idelim_open_marked t h h0 k false txt o
       else idelim_resolve t h h0 k txt before false None o
| IDollar (two, txt, _, o) ->
  IText (false, ((^) txt (dollars two)), (Some dollar), o)
| IPeriod (two, txt, _, o) ->
  IText (false, ((^) txt (periods two)), (Some period), o)
| IDash (n, txt, _, o) ->
  IText (false, ((^) txt (typography_dashes t n)), (Some hyphen), o)
| IBang (txt, _, o) -> IText (false, ((^) txt (one bang)), (Some bang), o)
| IClosed (txt, o) -> IText (false, ((^) txt (one rbrack)), (Some rbrack), o)
| _ -> st

(** val iescws_resolve :
    coq_PosPolicy -> coq_InlineCursor -> string -> string -> char option ->
    ostate -> (string * char option) * ostate **)

let iescws_resolve h h0 ws txt prev o =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> ((((^) txt (one bslash)), (Some bslash)), o))
    (fun c rest ->
    if (=) c ' '
    then ((rest, (str_last rest (Some c))),
           (oemit
             (imk h (spot_before h0.cursor_start ws)
               (spot_before h0.cursor_start rest) NonBreakingSpace)
             (flush_text_to_at h h0
               (spot_before h0.cursor_start ((^) (one bslash) ws)) txt o)))
    else ((((^) txt ((^) (one bslash) ws)), (str_last ws prev)), o))
    ws

(** val iesc_hard :
    coq_PosPolicy -> coq_InlineCursor -> string -> string -> ostate -> ostate **)

let iesc_hard h h0 ws txt o =
  let kept = strip_trailing_ws txt in
  let over = S (add (length ws) (sub (length txt) (length kept))) in
  oemit (imk_here h h0 HardBreak)
    (flush_text_to_at h h0 (spot_plus over h0.cursor_start) kept o)

(** val istep_at :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> bool -> char -> iscan ->
    iscan **)

let rec istep_at t h h0 attrs_enabled c = function
| IText (esc, txt, prev, o) ->
  if esc
  then if is_ws c
       then IEscWs ((one c), txt, prev, o)
       else IText (false,
              ((^) txt
                (if is_punct c
                 then one c
                 else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                        ('\\', (one c)))),
              (Some c), o)
  else ilead t h h0 c txt prev o
| IEscWs (ws, txt, prev, o) ->
  if is_ws c
  then IEscWs (((^) ws (one c)), txt, prev, o)
  else let (p, o') = iescws_resolve h h0 ws txt prev o in
       let (txt', prev') = p in ilead t h h0 c txt' prev' o'
| IBrace (txt, prev, o) -> ibrace_step_at t h h0 attrs_enabled c txt prev o
| IDelim (k, extra, txt, before, marked, o) ->
  if Nat.ltb (S extra) (dwidth t k)
  then if (=) c (dchar t k)
       then if marked
            then idelim_marked k (S extra) txt o
            else IDelim (k, (S extra), txt, before, false, o)
       else ilead t h h0 c ((^) txt (idelim_run t k extra marked)) (Some
              (dchar t k)) o
  else if marked
       then ilead t h h0 c "" (Some (dchar t k))
              (oopen_marked t h h0 k ((=) c rbrace) txt o)
       else let marker = (=) c rbrace in
            let st' = idelim_resolve t h h0 k txt before marker (Some c) o in
            if marker
            then st'
            else (match st' with
                  | IText (esc, txt', prev', o') ->
                    if esc then st' else ilead t h h0 c txt' prev' o'
                  | _ -> st')
| IOpen (n, vk, o) ->
  if is_tick c then IOpen ((S n), vk, o) else IVerb (n, O, (one c), vk, o)
| IVerb (n, run, txt, vk, o) ->
  if is_tick c
  then IVerb (n, (S run), txt, vk, o)
  else if Nat.eqb run n
       then if (&&) ((=) c lbrace) (vkind_verb vk)
            then IRaw ("", (trim_verb txt), o)
            else ilead t h h0 c "" (Some tick)
                   (oemit
                     (imk h (text_start h0 o) h0.cursor_start
                       (vnode vk (trim_verb txt)))
                     o)
       else IVerb (n, O, ((^) txt ((^) (ticks run) (one c))), vk, o)
| IDollar (two, txt, prev, o) -> idollar_step t h h0 c two txt prev o
| IPeriod (two, txt, prev, o) -> iperiod_step t h h0 c two txt prev o
| IDash (n, txt, prev, o) -> idash_step t h h0 c n txt prev o
| IBang (txt, prev, o) -> ibang_step t h h0 c txt prev o
| IClosed (txt, o) ->
  (match if (||) ((||) ((=) c lparen) ((=) c lbrack))
              ((&&) ((=) c lbrace) attrs_enabled)
         then bclose t h
                (flush_text_to_at h h0 (previous_spot h0.cursor_start) txt o)
         else None with
   | Some p ->
     let (p0, o') = p in
     let (p1, open0) = p0 in
     let (kids, image) = p1 in
     if (=) c lparen
     then IDest (kids, image, open0, false, O, "",
            (idest_open h h0 kids image open0 o'), o')
     else if (=) c lbrack
          then IReference (kids, image, open0, "", o')
          else ISpan (kids, image, open0, ap_init, "", o')
   | None -> ilead t h h0 c ((^) txt (one rbrack)) (Some rbrack) o)
| ISpan (kids, image, open0, p, src, o) ->
  ispan_feed t h h0 c kids image open0 p src o
| IAttr (p, src, txt, prev, sh, o) ->
  if ap_failed (astep p c)
  then istep_at t h h0 false c sh
  else iattr_feed t h h0 c p src txt prev (istep_at t h h0 false c sh) o
| IReference (kids, image, open0, label, o) ->
  if (=) c rbrack
  then let key =
         (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

           (fun _ -> reference_inlines_text kids)
           (fun _ _ -> label)
           label
       in
       IText (false, "", (Some rbrack),
       (oemit
         (imk h open0.span_start h0.cursor_stop
           (bnode image kids (Reference (normalize_label key))))
         o))
  else IReference (kids, image, open0, ((^) label (one c)), o)
| INote (esc, image, label, open0, o) ->
  inote_step h h0 c esc image label open0 o
| IWiki (esc, rb, image, region, open0, o) ->
  iwiki_step h h0 c esc rb image region open0 o
| IDest (kids, image, open0, esc, depth, dst, sh, o) ->
  if esc
  then IDest (kids, image, open0, false, depth,
         ((^) dst
           (if is_punct c
            then one c
            else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                   (bslash, (one c)))),
         (istep_at t h h0 attrs_enabled c sh), o)
  else if is_bslash c
       then IDest (kids, image, open0, true, depth, dst,
              (istep_at t h h0 attrs_enabled c sh), o)
       else if (=) c lparen
            then IDest (kids, image, open0, false, (S depth),
                   ((^) dst (one lparen)),
                   (istep_at t h h0 attrs_enabled c sh), o)
            else if (=) c rparen
                 then (match depth with
                       | O ->
                         IText (false, "", (Some rparen),
                           (oemit
                             (imk h open0.span_start h0.cursor_stop
                               (bnode image kids (Direct (drop_nl dst))))
                             o))
                       | S d ->
                         IDest (kids, image, open0, false, d,
                           ((^) dst (one rparen)),
                           (istep_at t h h0 attrs_enabled c sh), o))
                 else IDest (kids, image, open0, false, depth,
                        ((^) dst (one c)),
                        (istep_at t h h0 attrs_enabled c sh), o)
| IAuto (src, txt, o) -> iauto_step t h h0 c src txt o
| ISymbol (alias, txt, sh, o) ->
  isymbol_step h h0 c alias txt o (istep_at t h h0 attrs_enabled c sh)
| IRaw (spec, txt, o) -> iraw_step_at t h h0 attrs_enabled c spec txt o

(** val istep :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> iscan -> iscan **)

let istep t h h0 c st =
  istep_at t h h0 (inline_attrs_enabled t) c st

(** val ifinish_ostate_flat :
    coq_PosPolicy -> coq_InlineCursor -> iscan -> ostate **)

let ifinish_ostate_flat h h0 = function
| IText (esc, txt, _, o) ->
  if esc then iesc_hard h h0 "" txt o else flush_text_at h h0 txt o
| IEscWs (ws, txt, _, o) -> iesc_hard h h0 ws txt o
| IBrace (_, _, o) -> o
| IDelim (_, _, _, _, _, o) -> o
| IOpen (_, vk, o) ->
  oemit (imk h (text_start h0 o) h0.cursor_start (vnode vk "")) o
| IVerb (n, run, txt, vk, o) ->
  oemit
    (imk h (text_start h0 o) h0.cursor_start
      (vnode vk
        (trim_verb (if Nat.eqb run n then txt else (^) txt (ticks run)))))
    o
| IDollar (_, _, _, o) -> o
| IPeriod (_, _, _, o) -> o
| IDash (_, _, _, o) -> o
| IBang (_, _, o) -> o
| IClosed (_, o) -> o
| ISpan (kids, image, _, _, src, o) ->
  let (txt, o') = bspan_lit h h0 kids image src o in flush_text_at h h0 txt o'
| IAttr (_, src, txt, _, _, o) ->
  let (t, o') = battr_lit h h0 src txt o in flush_text_at h h0 t o'
| IReference (kids, image, _, label, o) ->
  let (txt, o') = bref_lit h h0 kids image label o in
  flush_text_at h h0 txt o'
| INote (esc, image, label, _, o) ->
  let (txt, o') = bnote_lit h h0 esc image label o in
  flush_text_at h h0 txt o'
| IWiki (esc, rb, image, region, _, o) ->
  let (txt, o') = bwiki_lit esc rb image region o in flush_text_at h h0 txt o'
| IDest (_, _, _, _, _, _, _, o) -> o
| IAuto (src, txt, o) -> flush_text_at h h0 (auto_lit src txt) o
| ISymbol (_, _, _, o) -> o
| IRaw (spec, txt, o) ->
  let spec_start =
    spot_before h0.cursor_start
      ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      (lbrace, spec))
  in
  flush_text_at h h0 (iraw_lit spec)
    (oemit (imk h (text_start h0 o) spec_start (Verbatim txt)) o)

(** val ifinish_ostate :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> iscan -> ostate **)

let rec ifinish_ostate t h h0 st = match st with
| IAttr (_, _, _, _, sh, _) -> ifinish_ostate t h h0 sh
| IDest (_, _, _, _, _, _, sh, _) -> ifinish_ostate t h h0 sh
| ISymbol (_, _, sh, _) -> ifinish_ostate t h h0 sh
| _ -> ifinish_ostate_flat h h0 (iresolve t h h0 st)

(** val ifinish_rev :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> iscan -> inlines **)

let ifinish_rev t h h0 st =
  ofinish t h (ifinish_ostate t h h0 st)

(** val ifinish :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> iscan -> inlines **)

let ifinish t h h0 st =
  rev (ifinish_rev t h h0 st)

(** val ibreak_flat :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> iscan -> iscan **)

let rec ibreak_flat t h h0 st = match st with
| IText (esc, txt, _, o) ->
  if esc
  then IText (false, "", None, (oword_reset (iesc_hard h h0 "" txt o)))
  else IText (false, "", None,
         (oword_reset
           (oemit (imk_here h h0 SoftBreak) (flush_text_at h h0 txt o))))
| IEscWs (ws, txt, _, o) ->
  IText (false, "", None, (oword_reset (iesc_hard h h0 ws txt o)))
| IOpen (n, vk, o) -> IVerb (n, O, nl, vk, o)
| IVerb (n, run, txt, vk, o) ->
  if Nat.eqb run n
  then IText (false, "", None,
         (oword_reset
           (oemit (imk_here h h0 SoftBreak)
             (oemit
               (imk h (text_start h0 o) h0.cursor_start
                 (vnode vk (trim_verb txt)))
               o))))
  else IVerb (n, O, ((^) txt ((^) (ticks run) nl)), vk, o)
| ISpan (kids, image, open0, p, src, o) ->
  ispan_feed t h h0 nl_char kids image open0 p src o
| IAttr (p, src, txt, prev, sh, o) ->
  iattr_feed t h h0 nl_char p src txt prev sh o
| IReference (kids, image, open0, label, o) ->
  IReference (kids, image, open0, ((^) label nl), o)
| INote (esc, image, label, open0, o) ->
  INote (false, image, ((^) label ((^) (if esc then one bslash else "") nl)),
    open0, o)
| IWiki (esc, rb, image, region, _, o) ->
  let (txt, o') = bwiki_lit esc rb image region o in
  IText (false, "", None,
  (oword_reset (oemit (imk_here h h0 SoftBreak) (flush_text_at h h0 txt o'))))
| IAuto (src, txt, o) ->
  IText (false, "", None,
    (oword_reset
      (oemit (imk_here h h0 SoftBreak)
        (flush_text_at h h0 (auto_lit src txt) o))))
| ISymbol (_, _, sh, _) -> ibreak_flat t h h0 sh
| IRaw (spec, txt, o) ->
  let spec_start =
    spot_before h0.cursor_start
      ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      (lbrace, spec))
  in
  IText (false, "", None,
  (oword_reset
    (oemit (imk_here h h0 SoftBreak)
      (flush_text_at h h0 (iraw_lit spec)
        (oemit (imk h (text_start h0 o) spec_start (Verbatim txt)) o)))))
| _ -> st

(** val ibreak_at :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> bool -> iscan -> iscan **)

let rec ibreak_at t h h0 attrs_enabled st = match st with
| IAttr (p, src, txt, prev, sh, o) ->
  iattr_feed t h h0 nl_char p src txt prev (ibreak_at t h h0 false sh) o
| IDest (kids, image, open0, esc, depth, dst, sh, o) ->
  IDest (kids, image, open0, false, depth,
    ((^) dst ((^) (if esc then one bslash else "") nl)),
    (ibreak_at t h h0 attrs_enabled sh), o)
| ISymbol (_, _, sh, _) -> ibreak_at t h h0 attrs_enabled sh
| _ -> ibreak_flat t h h0 (iresolve t h h0 st)

(** val ibreak :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> iscan -> iscan **)

let ibreak t h h0 st =
  ibreak_at t h h0 (inline_attrs_enabled t) st

(** val iclosed_at : iscan -> bool **)

let iclosed_at = function
| IText (esc, _, _, o) -> (&&) (negb esc) (null o.os_stk)
| IVerb (n, run, _, _, o) -> (&&) (Nat.eqb run n) (null o.os_stk)
| IWiki (_, _, _, _, _, o) -> null o.os_stk
| IAuto (_, _, o) -> null o.os_stk
| IRaw (_, _, o) -> null o.os_stk
| _ -> false

(** val iresolve_next :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> iscan -> iscan **)

let iresolve_next t h h0 c st = match st with
| IDelim (k, extra, txt, before, marked, o) ->
  if Nat.ltb (S extra) (dwidth t k)
  then IText (false, ((^) txt (idelim_run t k extra marked)), (Some
         (dchar t k)), o)
  else if marked
       then idelim_open_marked t h h0 k ((=) c rbrace) txt o
       else idelim_resolve t h h0 k txt before false (Some c) o
| _ -> iresolve t h h0 st

(** val iscan_settled :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> iscan -> bool **)

let iscan_settled t h h0 c st =
  iclosed_at (iresolve_next t h h0 c st)

(** val iscan_str : dtable -> string -> iscan -> iscan **)

let rec iscan_str t s st =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> st)
    (fun c rest ->
    iscan_str t rest (istep t semantic_pos semantic_inline_cursor c st))
    s

(** val iscan_lines : dtable -> string list -> iscan -> iscan **)

let rec iscan_lines t l st =
  match l with
  | [] -> st
  | x :: rest ->
    (match rest with
     | [] -> iscan_str t (strip_trailing_ws x) st
     | _ :: _ ->
       iscan_lines t rest
         (ibreak t semantic_pos semantic_inline_cursor (iscan_str t x st)))

(** val iscan_str_off : dtable -> string -> iscan -> iscan **)

let rec iscan_str_off t s st =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> st)
    (fun c rest ->
    iscan_str_off t rest
      (istep_at t semantic_pos semantic_inline_cursor false c st))
    s

(** val iscan_lines_off : dtable -> nat -> string list -> iscan -> iscan **)

let rec iscan_lines_off t k l st =
  match k with
  | O -> iscan_lines t l st
  | S k' ->
    (match l with
     | [] -> st
     | x :: rest ->
       (match rest with
        | [] -> iscan_str_off t (strip_trailing_ws x) st
        | _ :: _ ->
          iscan_lines_off t k' rest
            (ibreak_at t semantic_pos semantic_inline_cursor false
              (iscan_str_off t x st))))

(** val cursor_in : nat -> nat -> spot -> coq_InlineCursor **)

let cursor_in k rem origin =
  { cursor_start = { spot_line = k; spot_rem = rem }; cursor_stop =
    { spot_line = k; spot_rem = (pred rem) }; cursor_origin = origin }

(** val iscan_str_located :
    dtable -> coq_PosPolicy -> bool -> nat -> spot -> nat -> string -> iscan
    -> iscan **)

let rec iscan_str_located t h allow k origin rem s st =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> st)
    (fun c rest ->
    iscan_str_located t h allow k origin (pred rem) rest
      (istep_at t h (cursor_in k rem origin) allow c st))
    s

(** val lines_start : (nat * string) list -> spot **)

let lines_start = function
| [] -> { spot_line = O; spot_rem = O }
| p :: _ -> let (k, x) = p in { spot_line = k; spot_rem = (length x) }

(** val lines_stop : (nat * string) list -> spot **)

let rec lines_stop = function
| [] -> { spot_line = O; spot_rem = O }
| p :: rest ->
  let (k, x) = p in
  (match rest with
   | [] ->
     { spot_line = k; spot_rem =
       (sub (length x) (length (strip_trailing_ws x))) }
   | _ :: _ -> lines_stop rest)

(** val allow_attrs : dtable -> nat -> bool **)

let allow_attrs t = function
| O -> inline_attrs_enabled t
| S _ -> false

(** val iscan_lines_located :
    dtable -> coq_PosPolicy -> nat -> spot -> (nat * string) list -> iscan ->
    iscan **)

let rec iscan_lines_located t h off origin l st =
  match l with
  | [] -> st
  | p :: rest ->
    let (k, x) = p in
    (match rest with
     | [] ->
       iscan_str_located t h (allow_attrs t off) k origin (length x)
         (strip_trailing_ws x) st
     | _ :: _ ->
       iscan_lines_located t h (pred off) origin rest
         (ibreak_at t h { cursor_start = { spot_line = k; spot_rem = O };
           cursor_stop = (lines_start rest); cursor_origin = { spot_line = k;
           spot_rem = (length x) } } (allow_attrs t off)
           (iscan_str_located t h (allow_attrs t off) k origin (length x) x
             st)))

(** val ifinish_located :
    dtable -> coq_PosPolicy -> (nat * string) list -> iscan -> inlines **)

let ifinish_located t h l st =
  ifinish t h { cursor_start = (lines_stop l); cursor_stop = (lines_stop l);
    cursor_origin = (lines_start l) } st

(** val istart : iscan **)

let istart =
  IText (false, "", None, ostart)

(** val parse_inline_line : dtable -> string -> inlines **)

let parse_inline_line t s =
  ifinish t semantic_pos semantic_inline_cursor (iscan_str t s istart)

(** val para_inlines : dtable -> string list -> inlines **)

let para_inlines t l =
  ifinish t semantic_pos semantic_inline_cursor (iscan_lines t l istart)

(** val para_inlines_off : dtable -> nat -> string list -> inlines **)

let para_inlines_off t k l =
  ifinish t semantic_pos semantic_inline_cursor (iscan_lines_off t k l istart)

(** val para_inlines_located :
    dtable -> coq_PosPolicy -> nat -> (nat * string) list -> inlines **)

let para_inlines_located t h off l =
  ifinish_located t h l (iscan_lines_located t h off (lines_start l) l istart)

(** val para_inlines_at :
    dtable -> coq_PosPolicy -> nat -> (nat * string) list -> inlines **)

let para_inlines_at t h off l =
  if h.pos_records
  then para_inlines_located t h off l
  else para_inlines_off t off (map snd l)

(** val parse_inline_line_located :
    dtable -> coq_PosPolicy -> nat -> nat -> string -> inlines **)

let parse_inline_line_located t h k rem s =
  let stop = { spot_line = k; spot_rem = (sub rem (length s)) } in
  ifinish t h { cursor_start = stop; cursor_stop = stop; cursor_origin =
    { spot_line = k; spot_rem = rem } }
    (iscan_str_located t h (inline_attrs_enabled t) k { spot_line = k;
      spot_rem = rem } rem s istart)

(** val key_before : char option -> bool **)

let key_before = function
| Some c -> negb (is_ws c)
| None -> false

(** val key_after : string -> bool **)

let key_after rest =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> true)
    (fun c _ -> (=) c ' ')
    rest

(** val key_scan :
    dtable -> string -> string -> char option -> iscan -> (string * string)
    option **)

let rec key_scan t s lbl prev st =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c rest ->
    if (&&) ((&&) ((&&) ((=) c ':') (key_before prev)) (key_after rest))
         (iscan_settled t semantic_pos semantic_inline_cursor c st)
    then Some ((rev_string lbl), (drop_leading_ws rest))
    else key_scan t rest
           ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, lbl)) (Some c)
           (istep t semantic_pos semantic_inline_cursor c st))
    s

(** val key_point : dtable -> string -> (string * string) option **)

let key_point t l =
  key_scan t (drop_leading_ws l) "" None istart

(** val key_label_ok : dtable -> string -> bool **)

let key_label_ok t lbl =
  match para_inlines t (lbl :: []) with
  | [] -> false
  | _ :: l -> (match l with
               | [] -> true
               | _ :: _ -> false)

(** val key_split : dtable -> string -> (string * string) option **)

let key_split t l =
  match key_point t l with
  | Some p ->
    let (lbl, v) = p in if key_label_ok t lbl then Some (lbl, v) else None
  | None -> None

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
    | n :: rest -> let Node (_, _, x) = n in (^) (inline_text t x) (go rest)
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
   | Link (ns, tgt) ->
     (match tgt with
      | Direct dst ->
        (^) (bracket_open false) ((^) (go ns) (link_close t dst ""))
      | Reference label ->
        (^) (bracket_open false) ((^) (go ns) (ref_close label "")))
   | Image (ns, tgt) ->
     (match tgt with
      | Direct dst ->
        (^) (bracket_open true) ((^) (go ns) (link_close t dst ""))
      | Reference label ->
        (^) (bracket_open true) ((^) (go ns) (ref_close label "")))
   | FootnoteReference label -> note_text label
   | UrlLink s -> auto_text s
   | EmailLink s -> auto_text s
   | Wikilink (embed, t0, al) -> wiki_text embed t0 al
   | RawInline (fmt, s) -> raw_text fmt s
   | Quoted (qt, ns) ->
     (match qt with
      | SingleQuotes -> marked DSQuote ns
      | DoubleQuotes -> marked DDQuote ns)
   | _ -> "")

(** val inline_lines : dtable -> inlines -> string -> string list **)

let rec inline_lines t ils cur =
  match ils with
  | [] -> cur :: []
  | n :: rest ->
    let Node (_, _, il) = n in
    (match il with
     | SoftBreak -> cur :: (inline_lines t rest "")
     | _ -> inline_lines t rest ((^) cur (inline_text t il)))

(** val djot_table : dtable **)

let djot_table =
  djot_config
