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
              ((||) ((||) ((||) (is_bslash c) (is_tick c)) ((=) c lbrace))
                ((=) c rbrace))
              ((=) c lbrack))
            ((=) c rbrack))
          ((=) c bang))
        ((=) c dollar))
      ((=) c lt))
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
                 bool; dc_footnotes : bool }

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
    dc_math = true; dc_attrs = true; dc_footnotes = true }

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
   | CIRaw (fmt, s) -> raw_text fmt s)

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
   | CIRaw (fmt, s) -> mk (RawInline (fmt, s)))

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
   | CILink (_, kids, dst) -> (&&) ((&&) (no_nl dst) (go kids)) (sep kids)
   | CIRef (_, kids, label) ->
     (&&)
       ((&&)
         ((&&) ((&&) (nonempty_str label) (no_char rbrack label))
           ((=) (normalize_label label) label))
         (go kids))
       (sep kids)
   | CINote label ->
     (&&) ((&&) (notes_enabled t) (note_label_safe label))
       ((=) (normalize_label label) label)
   | CIAuto s -> (&&) (auto_body_ok s) (auto_kind_ok s)
   | CIRaw (fmt, s) ->
     (&&)
       ((&&) ((&&) (raw_inline_enabled t) (nonempty_str s))
         (verb_content_ok s))
       (raw_fmt_ok fmt))

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
| OMark of attr

type oitems = oitem list

type frame_kind =
| FKDelim of dstyle * bool
| FKBracket of bool
| FKDest of bool

type frame = { fr_kind : frame_kind; fr_marked : bool; fr_out : oitems }

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

type ostate = { os_out : oitems; os_stk : frame list }

(** val ostart : ostate **)

let ostart =
  { os_out = []; os_stk = [] }

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

(** val isnoc : inline node -> inlines -> inlines **)

let isnoc n out = match out with
| [] -> n :: out
| n0 :: rest ->
  let Node (p, a, x) = n0 in
  (match a with
   | [] ->
     (match x with
      | Str t ->
        let Node (_, a0, x0) = n in
        (match a0 with
         | [] ->
           (match x0 with
            | Str s -> (Node (p, [], (Str ((^) t s)))) :: rest
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
              let Node (_, a0, x0) = n1 in
              (match a0 with
               | [] ->
                 (match x0 with
                  | Str s -> (OIn (Node (p, [], (Str ((^) t s))))) :: rest
                  | _ -> n :: out)
               | _ :: _ -> n :: out)
            | OMark _ -> n :: out)
         | _ -> n :: out)
      | _ :: _ -> n :: out)
   | OMark _ -> n :: out)

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
  match o.os_stk with
  | [] -> { os_out = ((OIn n) :: o.os_out); os_stk = [] }
  | f :: rest ->
    { os_out = o.os_out; os_stk = ({ fr_kind = f.fr_kind; fr_marked =
      f.fr_marked; fr_out = ((OIn n) :: f.fr_out) } :: rest) }

(** val omark : attr -> ostate -> ostate **)

let omark a o =
  match o.os_stk with
  | [] -> { os_out = ((OMark a) :: o.os_out); os_stk = [] }
  | f :: rest ->
    { os_out = o.os_out; os_stk = ({ fr_kind = f.fr_kind; fr_marked =
      f.fr_marked; fr_out = ((OMark a) :: f.fr_out) } :: rest) }

(** val flush_text : string -> ostate -> ostate **)

let flush_text txt o =
  if nonempty_str txt then oemit (mk (Str txt)) o else o

(** val opush_at : dstyle -> bool -> bool -> ostate -> ostate **)

let opush_at k m cm o =
  { os_out = o.os_out; os_stk = ({ fr_kind = (FKDelim (k, cm)); fr_marked =
    m; fr_out = [] } :: o.os_stk) }

(** val opush : dstyle -> bool -> ostate -> ostate **)

let opush k m o =
  opush_at k m false o

(** val bpush : bool -> ostate -> ostate **)

let bpush image o =
  { os_out = o.os_out; os_stk = ({ fr_kind = (FKBracket image); fr_marked =
    false; fr_out = [] } :: o.os_stk) }

(** val dpush : bool -> ostate -> ostate **)

let dpush image o =
  { os_out = o.os_out; os_stk = ({ fr_kind = (FKDest image); fr_marked =
    false; fr_out = [] } :: o.os_stk) }

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

(** val oattach_list : attr -> inlines -> inlines **)

let oattach_list a out = match out with
| [] -> out
| n :: rest ->
  let Node (p, a', v) = n in
  (match a' with
   | [] ->
     (match v with
      | Str s ->
        let (pre, w) = last_ws_split s in
        if nonempty_str w
        then (match a with
              | [] -> out
              | _ :: _ ->
                let out1 =
                  if nonempty_str pre then isnoc (mk (Str pre)) rest else rest
                in
                isnoc (Node (NoPos, a, (Str w))) out1)
        else out
      | SoftBreak -> out
      | _ -> (Node (p, (attr_merge a a'), v)) :: rest)
   | _ :: _ ->
     (match v with
      | SoftBreak -> out
      | _ -> (Node (p, (attr_merge a a'), v)) :: rest))

(** val oresolve_go : oitems -> inlines * bool **)

let rec oresolve_go = function
| [] -> ([], false)
| o :: rest ->
  (match o with
   | OIn n ->
     let (out, m) = oresolve_go rest in
     ((if m then isnoc n out else n :: out), false)
   | OMark a ->
     let (out, _) = oresolve_go rest in
     let out' = oattach_list a out in (out', (istarts_str out')))

(** val oresolve : oitems -> inlines **)

let oresolve l =
  fst (oresolve_go l)

(** val oclose_go :
    dtable -> dstyle -> bool -> oitems -> frame list -> (oitems * frame list)
    option **)

let rec oclose_go t k m pend = function
| [] -> None
| f :: rest ->
  let content = oapp pend f.fr_out in
  if dmatch k m f
  then if nonempty content then Some (content, rest) else None
  else if fr_barrier f
       then None
       else oclose_go t k m
              (oapp content ((OIn (mk (Str (fr_src t f)))) :: [])) rest

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

(** val oclose : dtable -> dstyle -> bool -> ostate -> ostate option **)

let oclose t k m o =
  match oclose_go t k m [] o.os_stk with
  | Some p ->
    let (content, rest) = p in
    Some
    (oemit (mk (dnode k (rev (oresolve content)))) { os_out = o.os_out;
      os_stk = rest })
  | None -> None

(** val bclose_go :
    dtable -> oitems -> frame list -> ((oitems * bool) * frame list) option **)

let rec bclose_go t pend = function
| [] -> None
| f :: rest ->
  let content = oapp pend f.fr_out in
  (match f.fr_kind with
   | FKDelim (_, _) ->
     bclose_go t (oapp content ((OIn (mk (Str (fr_src t f)))) :: [])) rest
   | FKBracket image -> Some ((content, image), rest)
   | FKDest _ -> None)

(** val bclose : dtable -> ostate -> ((inlines * bool) * ostate) option **)

let bclose t o =
  match bclose_go t [] o.os_stk with
  | Some p ->
    let (p0, rest) = p in
    let (content, image) = p0 in
    Some (((rev (oresolve content)), image), { os_out = o.os_out; os_stk =
    rest })
  | None -> None

(** val bunpush : ostate -> (bool * ostate) option **)

let bunpush o =
  match o.os_stk with
  | [] -> None
  | f :: rest ->
    let { fr_kind = fr_kind0; fr_marked = _; fr_out = fr_out0 } = f in
    (match fr_kind0 with
     | FKBracket image ->
       (match fr_out0 with
        | [] -> Some (image, { os_out = o.os_out; os_stk = rest })
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
              | Str s -> (s, { os_out = rest; os_stk = [] })
              | _ -> ("", o))
           | _ :: _ -> ("", o))
        | OMark _ -> ("", o)))
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
                  fr_marked = f.fr_marked; fr_out = rest } :: fs) })
              | _ -> ("", o))
           | _ :: _ -> ("", o))
        | OMark _ -> ("", o)))

(** val bflat : inlines -> string -> ostate -> string * ostate **)

let rec bflat kids txt o =
  match kids with
  | [] -> (txt, o)
  | n :: rest ->
    let Node (_, a, x) = n in
    (match a with
     | [] ->
       (match x with
        | Str s -> bflat rest ((^) txt s) o
        | _ -> bflat rest "" (oemit n (flush_text txt o)))
     | _ :: _ -> bflat rest "" (oemit n (flush_text txt o)))

(** val bsplit_nl : string -> string -> ostate -> string * ostate **)

let rec bsplit_nl s txt o =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> (txt, o))
    (fun c rest ->
    if (=) c nl_char
    then bsplit_nl rest "" (oemit (mk SoftBreak) (flush_text txt o))
    else bsplit_nl rest ((^) txt (one c)) o)
    s

(** val bclosed_lit : inlines -> bool -> ostate -> string * ostate **)

let bclosed_lit kids image o =
  let (pre, o1) = opop_str o in
  let (txt, o2) = bflat kids ((^) pre (bracket_open image)) o1 in
  (((^) txt (one rbrack)), o2)

(** val bspan_lit : inlines -> bool -> string -> ostate -> string * ostate **)

let bspan_lit kids image src o =
  let (txt, o') = bclosed_lit kids image o in
  bsplit_nl src ((^) txt (one lbrace)) o'

(** val battr_lit : string -> string -> ostate -> string * ostate **)

let battr_lit src txt o =
  bsplit_nl src ((^) txt (one lbrace)) o

(** val blit_prev : string -> char option **)

let blit_prev t =
  str_last t (Some nl_char)

(** val bref_lit : inlines -> bool -> string -> ostate -> string * ostate **)

let bref_lit kids image label o =
  let (txt, o') = bclosed_lit kids image o in
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

(** val oflatten : dtable -> oitems -> frame list -> oitems -> oitems **)

let rec oflatten t pend stk bottom =
  match stk with
  | [] -> oapp pend bottom
  | f :: rest ->
    oflatten t
      (oapp (oapp pend f.fr_out) ((OIn (mk (Str (fr_src t f)))) :: [])) rest
      bottom

(** val oitems_of : dtable -> ostate -> oitems **)

let oitems_of t o =
  oflatten t [] o.os_stk o.os_out

(** val ofinish : dtable -> ostate -> inlines **)

let ofinish t o =
  oresolve (oitems_of t o)

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
| ISpan of inlines * bool * aparser * string * ostate
| IAttr of aparser * string * string * char option * iscan * ostate
| IReference of inlines * bool * string * ostate
| INote of bool * bool * string * ostate
| IDest of inlines * bool * bool * nat * string * iscan * ostate
| IAuto of string * string * ostate
| IRaw of string * string * ostate

(** val note_pos : string -> char option -> bool **)

let note_pos txt prev =
  (&&) (negb (nonempty_str txt))
    (match prev with
     | Some p -> (=) p lbrack
     | None -> false)

(** val ilead : dtable -> char -> string -> char option -> ostate -> iscan **)

let ilead t c txt prev o =
  if is_bslash c
  then IText (true, txt, (Some c), o)
  else if is_tick c
       then IOpen ((S O), VVerb, (flush_text txt o))
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
                                     else if (=) c lbrack
                                          then IText (false, "", (Some
                                                 lbrack),
                                                 (bpush false
                                                   (flush_text txt o)))
                                          else if (=) c rbrack
                                               then IClosed (txt, o)
                                               else (match if (&&)
                                                                ((&&)
                                                                  ((=) c hat)
                                                                  (note_pos
                                                                    txt prev))
                                                                (notes_enabled
                                                                  t)
                                                           then bunpush o
                                                           else None with
                                                     | Some p ->
                                                       let (image, o') = p in
                                                       INote (false, image,
                                                       "", o')
                                                     | None ->
                                                       (match dstyle_of t c with
                                                        | Some k ->
                                                          IDelim (k, O, txt,
                                                            prev, false, o)
                                                        | None ->
                                                          IText (false,
                                                            ((^) txt (one c)),
                                                            (Some c), o)))

(** val idest_open : inlines -> bool -> ostate -> iscan **)

let idest_open kids image o =
  let (txt, o') = bflat kids "" (dpush image o) in
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

let islice_end t st = match st with
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
| _ -> st

(** val iattr_mark : attr -> string -> ostate -> iscan **)

let iattr_mark a txt o =
  IText (false, "", (Some rbrace), (omark a (flush_text txt o)))

(** val iattr_feed :
    dtable -> char -> aparser -> string -> string -> char option -> iscan ->
    ostate -> iscan **)

let iattr_feed t c p src txt prev sh o =
  let p' = astep p c in
  if ap_failed p'
  then sh
  else if ap_done p'
       then iattr_mark p'.ap_attrs txt o
       else IAttr (p', ((^) src (one c)), txt, prev, (islice_end t sh), o)

(** val idelim_marked : dstyle -> nat -> string -> ostate -> iscan **)

let idelim_marked k extra txt o =
  IDelim (k, extra, txt, None, true, o)

(** val oopen_marked : dstyle -> bool -> string -> ostate -> ostate **)

let oopen_marked k cm txt o =
  opush_at k true cm (flush_text txt o)

(** val idelim_open_marked :
    dtable -> dstyle -> bool -> string -> ostate -> iscan **)

let idelim_open_marked t k cm txt o =
  IText (false, "", (Some (dchar t k)), (oopen_marked k cm txt o))

(** val idelim_run : dtable -> dstyle -> nat -> bool -> string **)

let idelim_run t k extra marked =
  (^) (if marked then one lbrace else "") (chars (dchar t k) (S extra))

(** val ibrace_step_at :
    dtable -> bool -> char -> string -> char option -> ostate -> iscan **)

let ibrace_step_at t attrs_enabled c txt prev o =
  match dstyle_of t c with
  | Some k -> idelim_marked k O txt o
  | None ->
    if attrs_enabled
    then iattr_feed t c ap_init "" txt prev
           (ilead t c ((^) txt (one lbrace)) (Some lbrace) o) o
    else let (t0, o') = battr_lit "" txt o in ilead t c t0 (blit_prev t0) o'

(** val ospan_bang : bool -> ostate -> ostate **)

let ospan_bang image o =
  if image
  then let (pre, o1) = opop_str o in flush_text ((^) pre (one bang)) o1
  else o

(** val ispan_feed :
    dtable -> char -> inlines -> bool -> aparser -> string -> ostate -> iscan **)

let ispan_feed t c kids image p src o =
  let p' = astep p c in
  if ap_failed p'
  then let (txt, o') = bspan_lit kids image src o in
       ilead t c txt (blit_prev txt) o'
  else if ap_done p'
       then IText (false, "", (Some rbrace),
              (oemit (Node (NoPos, p'.ap_attrs, (Span kids)))
                (ospan_bang image o)))
       else ISpan (kids, image, p', ((^) src (one c)), o)

(** val inote_step : char -> bool -> bool -> string -> ostate -> iscan **)

let inote_step c esc image label o =
  if esc
  then INote (false, image, ((^) label ((^) (one bslash) (one c))), o)
  else if is_bslash c
       then INote (true, image, label, o)
       else if (=) c rbrack
            then IText (false, "", (Some rbrack),
                   (oemit (mk (FootnoteReference (normalize_label label)))
                     (ospan_bang image o)))
            else INote (false, image, ((^) label (one c)), o)

(** val iauto_step : dtable -> char -> string -> string -> ostate -> iscan **)

let iauto_step t c src txt o =
  if (&&) ((&&) ((=) c gt) (auto_body_ok src)) (auto_kind_ok src)
  then IText (false, "", (Some gt),
         (oemit (mk (auto_node src)) (flush_text txt o)))
  else if (||) ((||) ((=) c gt) (is_ws c)) ((=) c lt)
       then ilead t c (auto_lit src txt) (blit_prev (auto_lit src txt)) o
       else IAuto (((^) src (one c)), txt, o)

(** val iraw_lit : string -> string **)

let iraw_lit spec =
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (lbrace, spec)

(** val iraw_step_at :
    dtable -> bool -> char -> string -> string -> ostate -> iscan **)

let iraw_step_at t attrs_enabled c spec txt o =
  if (&&) ((=) c rbrace) (raw_spec_ok spec)
  then if raw_inline_enabled t
       then IText (false, "", (Some rbrace),
              (oemit (mk (RawInline ((raw_format spec), txt))) o))
       else ilead t c (iraw_lit spec) (blit_prev (iraw_lit spec))
              (oemit (mk (Verbatim txt)) o)
  else if (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

            (fun _ -> negb ((=) c eqchar))
            (fun _ _ -> (||) ((=) c rbrace) (raw_stop c))
            spec
       then let closed = oemit (mk (Verbatim txt)) o in
            ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

               (fun _ ->
               ibrace_step_at t attrs_enabled c "" (Some tick) closed)
               (fun _ _ ->
               ilead t c (iraw_lit spec) (blit_prev (iraw_lit spec)) closed)
               spec)
       else IRaw (((^) spec (one c)), txt, o)

(** val bnote_lit : bool -> bool -> string -> ostate -> string * ostate **)

let bnote_lit esc image label o =
  let (pre, o1) = opop_str o in
  (((^) pre
     ((^) (bracket_open image)
       ((^) (one hat) ((^) label (if esc then one bslash else ""))))),
  o1)

(** val ibang_step :
    dtable -> char -> string -> char option -> ostate -> iscan **)

let ibang_step t c txt _ o =
  if (=) c lbrack
  then IText (false, "", (Some lbrack), (bpush true (flush_text txt o)))
  else ilead t c ((^) txt (one bang)) (Some bang) o

(** val idelim_lit : dtable -> dstyle -> string -> bool -> string **)

let idelim_lit t k txt marker =
  (^) txt (ddecay_str t k false marker)

(** val idelim_lit_prev : dtable -> dstyle -> bool -> char option **)

let idelim_lit_prev t k marker =
  Some (if marker then rbrace else dchar t k)

(** val idelim_done :
    dtable -> dstyle -> string -> char option -> bool -> char option ->
    ostate -> iscan **)

let idelim_done t k txt before marker next o =
  if (&&) ((&&) (dbare t k before) (negb marker)) (nonspace_at next)
  then IText (false, "", (Some (dchar t k)),
         (opush k false (flush_text txt o)))
  else IText (false, (idelim_lit t k txt marker),
         (idelim_lit_prev t k marker), o)

(** val idelim_resolve :
    dtable -> dstyle -> string -> char option -> bool -> char option ->
    ostate -> iscan **)

let idelim_resolve t k txt before marker next o =
  if (||) (nonspace_at before) marker
  then (match oclose t k marker (flush_text txt o) with
        | Some o' ->
          IText (false, "", (Some (if marker then rbrace else dchar t k)), o')
        | None ->
          if oclose_barred k marker o
          then IText (false, (idelim_lit t k txt marker),
                 (idelim_lit_prev t k marker), o)
          else idelim_done t k txt before marker next o)
  else idelim_done t k txt before marker next o

(** val idollar_step :
    dtable -> char -> bool -> string -> char option -> ostate -> iscan **)

let idollar_step t c two txt prev o =
  if (=) c dollar
  then if two
       then IDollar (true, ((^) txt (one dollar)), prev, o)
       else IDollar (true, txt, prev, o)
  else if (&&) (is_tick c) (math_enabled t)
       then IOpen ((S O), (VMath (if two then DisplayMath else InlineMath)),
              (flush_text txt o))
       else ilead t c ((^) txt (dollars two)) (Some dollar) o

(** val iperiod_step :
    dtable -> char -> bool -> string -> char option -> ostate -> iscan **)

let iperiod_step t c two txt prev o =
  if (=) c period
  then if two
       then IText (false, ((^) txt (typography_ellipsis t)), (Some c), o)
       else IPeriod (true, txt, prev, o)
  else ilead t c ((^) txt (periods two)) (Some period) o

(** val idash_step :
    dtable -> char -> nat -> string -> char option -> ostate -> iscan **)

let idash_step t c n txt prev o =
  if (=) c hyphen
  then IDash ((S n), txt, prev, o)
  else if (=) c rbrace
       then (match dstyle_of t hyphen with
             | Some k ->
               if Nat.leb (dwidth t k) n
               then idelim_resolve t k
                      ((^) txt (typography_dashes t (sub n (dwidth t k))))
                      None true (Some c) o
               else IText (false,
                      ((^) txt ((^) (typography_dashes t n) (one rbrace))),
                      (Some rbrace), o)
             | None ->
               IText (false,
                 ((^) txt ((^) (typography_dashes t n) (one rbrace))), (Some
                 rbrace), o))
       else ilead t c ((^) txt (typography_dashes t n)) (Some hyphen) o

(** val iresolve : dtable -> iscan -> iscan **)

let iresolve t st = match st with
| IBrace (txt, _, o) ->
  IText (false, ((^) txt (one lbrace)), (Some lbrace), o)
| IDelim (k, extra, txt, before, marked, o) ->
  if Nat.ltb (S extra) (dwidth t k)
  then IText (false, ((^) txt (idelim_run t k extra marked)), (Some
         (dchar t k)), o)
  else if marked
       then idelim_open_marked t k false txt o
       else idelim_resolve t k txt before false None o
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
    string -> string -> char option -> ostate -> (string * char
    option) * ostate **)

let iescws_resolve ws txt prev o =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> ((((^) txt (one bslash)), (Some bslash)), o))
    (fun c rest ->
    if (=) c ' '
    then ((rest, (str_last rest (Some c))),
           (oemit (mk NonBreakingSpace) (flush_text txt o)))
    else ((((^) txt ((^) (one bslash) ws)), (str_last ws prev)), o))
    ws

(** val iesc_hard : string -> ostate -> ostate **)

let iesc_hard txt o =
  oemit (mk HardBreak) (flush_text (strip_trailing_ws txt) o)

(** val istep_at : dtable -> bool -> char -> iscan -> iscan **)

let rec istep_at t attrs_enabled c = function
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
  else ilead t c txt prev o
| IEscWs (ws, txt, prev, o) ->
  if is_ws c
  then IEscWs (((^) ws (one c)), txt, prev, o)
  else let (p, o') = iescws_resolve ws txt prev o in
       let (txt', prev') = p in ilead t c txt' prev' o'
| IBrace (txt, prev, o) -> ibrace_step_at t attrs_enabled c txt prev o
| IDelim (k, extra, txt, before, marked, o) ->
  if Nat.ltb (S extra) (dwidth t k)
  then if (=) c (dchar t k)
       then if marked
            then idelim_marked k (S extra) txt o
            else IDelim (k, (S extra), txt, before, false, o)
       else ilead t c ((^) txt (idelim_run t k extra marked)) (Some
              (dchar t k)) o
  else if marked
       then ilead t c "" (Some (dchar t k))
              (oopen_marked k ((=) c rbrace) txt o)
       else let marker = (=) c rbrace in
            let st' = idelim_resolve t k txt before marker (Some c) o in
            if marker
            then st'
            else (match st' with
                  | IText (esc, txt', prev', o') ->
                    if esc then st' else ilead t c txt' prev' o'
                  | _ -> st')
| IOpen (n, vk, o) ->
  if is_tick c then IOpen ((S n), vk, o) else IVerb (n, O, (one c), vk, o)
| IVerb (n, run, txt, vk, o) ->
  if is_tick c
  then IVerb (n, (S run), txt, vk, o)
  else if Nat.eqb run n
       then if (&&) ((=) c lbrace) (vkind_verb vk)
            then IRaw ("", (trim_verb txt), o)
            else ilead t c "" (Some tick)
                   (oemit (mk (vnode vk (trim_verb txt))) o)
       else IVerb (n, O, ((^) txt ((^) (ticks run) (one c))), vk, o)
| IDollar (two, txt, prev, o) -> idollar_step t c two txt prev o
| IPeriod (two, txt, prev, o) -> iperiod_step t c two txt prev o
| IDash (n, txt, prev, o) -> idash_step t c n txt prev o
| IBang (txt, prev, o) -> ibang_step t c txt prev o
| IClosed (txt, o) ->
  (match if (||) ((||) ((=) c lparen) ((=) c lbrack))
              ((&&) ((=) c lbrace) attrs_enabled)
         then bclose t (flush_text txt o)
         else None with
   | Some p ->
     let (p0, o') = p in
     let (kids, image) = p0 in
     if (=) c lparen
     then IDest (kids, image, false, O, "", (idest_open kids image o'), o')
     else if (=) c lbrack
          then IReference (kids, image, "", o')
          else ISpan (kids, image, ap_init, "", o')
   | None -> ilead t c ((^) txt (one rbrack)) (Some rbrack) o)
| ISpan (kids, image, p, src, o) -> ispan_feed t c kids image p src o
| IAttr (p, src, txt, prev, sh, o) ->
  if ap_failed (astep p c)
  then istep_at t false c sh
  else iattr_feed t c p src txt prev (istep_at t false c sh) o
| IReference (kids, image, label, o) ->
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
       (oemit (mk (bnode image kids (Reference (normalize_label key)))) o))
  else IReference (kids, image, ((^) label (one c)), o)
| INote (esc, image, label, o) -> inote_step c esc image label o
| IDest (kids, image, esc, depth, dst, sh, o) ->
  if esc
  then IDest (kids, image, false, depth,
         ((^) dst
           (if is_punct c
            then one c
            else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                   (bslash, (one c)))),
         (istep_at t attrs_enabled c sh), o)
  else if is_bslash c
       then IDest (kids, image, true, depth, dst,
              (istep_at t attrs_enabled c sh), o)
       else if (=) c lparen
            then IDest (kids, image, false, (S depth),
                   ((^) dst (one lparen)), (istep_at t attrs_enabled c sh), o)
            else if (=) c rparen
                 then (match depth with
                       | O ->
                         IText (false, "", (Some rparen),
                           (oemit
                             (mk (bnode image kids (Direct (drop_nl dst)))) o))
                       | S d ->
                         IDest (kids, image, false, d,
                           ((^) dst (one rparen)),
                           (istep_at t attrs_enabled c sh), o))
                 else IDest (kids, image, false, depth, ((^) dst (one c)),
                        (istep_at t attrs_enabled c sh), o)
| IAuto (src, txt, o) -> iauto_step t c src txt o
| IRaw (spec, txt, o) -> iraw_step_at t attrs_enabled c spec txt o

(** val istep : dtable -> char -> iscan -> iscan **)

let istep t c st =
  istep_at t (inline_attrs_enabled t) c st

(** val ifinish_ostate_flat : iscan -> ostate **)

let ifinish_ostate_flat = function
| IText (esc, txt, _, o) -> if esc then iesc_hard txt o else flush_text txt o
| IEscWs (_, txt, _, o) -> iesc_hard txt o
| IBrace (_, _, o) -> o
| IDelim (_, _, _, _, _, o) -> o
| IOpen (_, vk, o) -> oemit (mk (vnode vk "")) o
| IVerb (n, run, txt, vk, o) ->
  oemit
    (mk
      (vnode vk
        (trim_verb (if Nat.eqb run n then txt else (^) txt (ticks run)))))
    o
| IDollar (_, _, _, o) -> o
| IPeriod (_, _, _, o) -> o
| IDash (_, _, _, o) -> o
| IBang (_, _, o) -> o
| IClosed (_, o) -> o
| ISpan (kids, image, _, src, o) ->
  let (txt, o') = bspan_lit kids image src o in flush_text txt o'
| IAttr (_, src, txt, _, _, o) ->
  let (t, o') = battr_lit src txt o in flush_text t o'
| IReference (kids, image, label, o) ->
  let (txt, o') = bref_lit kids image label o in flush_text txt o'
| INote (esc, image, label, o) ->
  let (txt, o') = bnote_lit esc image label o in flush_text txt o'
| IDest (_, _, _, _, _, _, o) -> o
| IAuto (src, txt, o) -> flush_text (auto_lit src txt) o
| IRaw (spec, txt, o) ->
  flush_text (iraw_lit spec) (oemit (mk (Verbatim txt)) o)

(** val ifinish_ostate : dtable -> iscan -> ostate **)

let rec ifinish_ostate t st = match st with
| IAttr (_, _, _, _, sh, _) -> ifinish_ostate t sh
| IDest (_, _, _, _, _, sh, _) -> ifinish_ostate t sh
| _ -> ifinish_ostate_flat (iresolve t st)

(** val ifinish_rev : dtable -> iscan -> inlines **)

let ifinish_rev t st =
  ofinish t (ifinish_ostate t st)

(** val ifinish : dtable -> iscan -> inlines **)

let ifinish t st =
  rev (ifinish_rev t st)

(** val ibreak_flat : dtable -> iscan -> iscan **)

let ibreak_flat t st = match st with
| IText (esc, txt, _, o) ->
  if esc
  then IText (false, "", None, (iesc_hard txt o))
  else IText (false, "", None, (oemit (mk SoftBreak) (flush_text txt o)))
| IEscWs (_, txt, _, o) -> IText (false, "", None, (iesc_hard txt o))
| IOpen (n, vk, o) -> IVerb (n, O, nl, vk, o)
| IVerb (n, run, txt, vk, o) ->
  if Nat.eqb run n
  then IText (false, "", None,
         (oemit (mk SoftBreak) (oemit (mk (vnode vk (trim_verb txt))) o)))
  else IVerb (n, O, ((^) txt ((^) (ticks run) nl)), vk, o)
| ISpan (kids, image, p, src, o) -> ispan_feed t nl_char kids image p src o
| IAttr (p, src, txt, prev, sh, o) -> iattr_feed t nl_char p src txt prev sh o
| IReference (kids, image, label, o) ->
  IReference (kids, image, ((^) label nl), o)
| INote (esc, image, label, o) ->
  INote (false, image, ((^) label ((^) (if esc then one bslash else "") nl)),
    o)
| IAuto (src, txt, o) ->
  IText (false, "", None,
    (oemit (mk SoftBreak) (flush_text (auto_lit src txt) o)))
| IRaw (spec, txt, o) ->
  IText (false, "", None,
    (oemit (mk SoftBreak)
      (flush_text (iraw_lit spec) (oemit (mk (Verbatim txt)) o))))
| _ -> st

(** val ibreak_at : dtable -> bool -> iscan -> iscan **)

let rec ibreak_at t attrs_enabled st = match st with
| IAttr (p, src, txt, prev, sh, o) ->
  iattr_feed t nl_char p src txt prev (ibreak_at t false sh) o
| IDest (kids, image, esc, depth, dst, sh, o) ->
  IDest (kids, image, false, depth,
    ((^) dst ((^) (if esc then one bslash else "") nl)),
    (ibreak_at t attrs_enabled sh), o)
| _ -> ibreak_flat t (iresolve t st)

(** val ibreak : dtable -> iscan -> iscan **)

let ibreak t st =
  ibreak_at t (inline_attrs_enabled t) st

(** val iclosed_at : iscan -> bool **)

let iclosed_at = function
| IText (esc, _, _, o) -> (&&) (negb esc) (null o.os_stk)
| IVerb (n, run, _, _, o) -> (&&) (Nat.eqb run n) (null o.os_stk)
| IAuto (_, _, o) -> null o.os_stk
| IRaw (_, _, o) -> null o.os_stk
| _ -> false

(** val iresolve_next : dtable -> char -> iscan -> iscan **)

let iresolve_next t c st = match st with
| IDelim (k, extra, txt, before, marked, o) ->
  if Nat.ltb (S extra) (dwidth t k)
  then IText (false, ((^) txt (idelim_run t k extra marked)), (Some
         (dchar t k)), o)
  else if marked
       then idelim_open_marked t k ((=) c rbrace) txt o
       else idelim_resolve t k txt before false (Some c) o
| _ -> iresolve t st

(** val iscan_settled : dtable -> char -> iscan -> bool **)

let iscan_settled t c st =
  iclosed_at (iresolve_next t c st)

(** val iscan_str : dtable -> string -> iscan -> iscan **)

let rec iscan_str t s st =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> st)
    (fun c rest -> iscan_str t rest (istep t c st))
    s

(** val iscan_lines : dtable -> string list -> iscan -> iscan **)

let rec iscan_lines t l st =
  match l with
  | [] -> st
  | x :: rest ->
    (match rest with
     | [] -> iscan_str t (strip_trailing_ws x) st
     | _ :: _ -> iscan_lines t rest (ibreak t (iscan_str t x st)))

(** val iscan_str_off : dtable -> string -> iscan -> iscan **)

let rec iscan_str_off t s st =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> st)
    (fun c rest -> iscan_str_off t rest (istep_at t false c st))
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
          iscan_lines_off t k' rest (ibreak_at t false (iscan_str_off t x st))))

(** val istart : iscan **)

let istart =
  IText (false, "", None, ostart)

(** val parse_inline_line : dtable -> string -> inlines **)

let parse_inline_line t s =
  ifinish t (iscan_str t s istart)

(** val para_inlines : dtable -> string list -> inlines **)

let para_inlines t l =
  ifinish t (iscan_lines t l istart)

(** val para_inlines_off : dtable -> nat -> string list -> inlines **)

let para_inlines_off t k l =
  ifinish t (iscan_lines_off t k l istart)

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
         (iscan_settled t c st)
    then Some ((rev_string lbl), (drop_leading_ws rest))
    else key_scan t rest
           ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, lbl)) (Some c) (istep t c st))
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
