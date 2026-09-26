open Ast
open Attributes
open ListDef
open Strings

(** val is_punct : char -> bool **)

let is_punct c =
  let n = Char.code c in
  (||)
    ((||)
      ((||)
        ((&&)
          (( <= ) (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            0))))))))))))))))))))))))))))))))) n)
          (( <= ) n (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ
            0)))))))))))))))))))))))))))))))))))))))))))))))))
        ((&&)
          (( <= ) (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))) n)
          (( <= ) n (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
            0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      ((&&)
        (( <= ) (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ
          0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          n)
        (( <= ) n (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
          (Stdlib.succ (Stdlib.succ
          0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    ((&&)
      (( <= ) (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        0)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        n)
      (( <= ) n (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
        (Stdlib.succ (Stdlib.succ
        0))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

(** val tick : char **)

let tick =
  '`'

(** val is_tick : char -> bool **)

let is_tick c =
  (=) c tick

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

(** val period : char **)

let period =
  '.'

(** val bang : char **)

let bang =
  '!'

(** val lbrack : char **)

let lbrack =
  '['

(** val rbrack : char **)

let rbrack =
  ']'

(** val lparen : char **)

let lparen =
  '('

(** val rparen : char **)

let rparen =
  ')'

(** val vbar : char **)

let vbar =
  '|'

(** val hat : char **)

let hat =
  '^'

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

type dconfig = { dc_char : (dstyle -> char); dc_width : (dstyle -> int);
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

(** val djot_dwidth : dstyle -> int **)

let djot_dwidth _ =
  Stdlib.succ 0

(** val djot_config : dconfig **)

let djot_config =
  { dc_char = djot_dchar; dc_width = djot_dwidth; dc_syntax = djot_dsyntax;
    dc_decay = djot_ddecay; dc_smart_typography = true; dc_raw_inline = true;
    dc_math = true; dc_attrs = true; dc_footnotes = true; dc_wikilinks =
    false }

(** val chars : char -> int -> string **)

let rec chars c n =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> "")
    (fun m ->
    (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (c, (chars c m)))
    n

(** val dstyle_eq : dstyle -> dstyle -> bool **)

let dstyle_eq a b =
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

(** val denabled : dconfig -> dstyle -> bool **)

let denabled c k =
  match c.dc_syntax k with
  | DOff -> false
  | _ -> true

(** val dstyle_at_fast : dconfig -> char -> dstyle option **)

let dstyle_at_fast c c0 =
  let hit = fun k -> (&&) (denabled c k) ((=) (c.dc_char k) c0) in
  if hit DEmph
  then Some DEmph
  else if hit DStrong
       then Some DStrong
       else if hit DSuper
            then Some DSuper
            else if hit DSub
                 then Some DSub
                 else if hit DMark
                      then Some DMark
                      else if hit DInsert
                           then Some DInsert
                           else if hit DDelete
                                then Some DDelete
                                else if hit DSQuote
                                     then Some DSQuote
                                     else if hit DDQuote
                                          then Some DDQuote
                                          else None

(** val with_wikilinks : bool -> dconfig -> dconfig **)

let with_wikilinks enabled c =
  { dc_char = c.dc_char; dc_width = c.dc_width; dc_syntax = c.dc_syntax;
    dc_decay = c.dc_decay; dc_smart_typography = c.dc_smart_typography;
    dc_raw_inline = c.dc_raw_inline; dc_math = c.dc_math; dc_attrs =
    c.dc_attrs; dc_footnotes = c.dc_footnotes; dc_wikilinks = enabled }

(** val bnode : bool -> inlines -> target -> inline **)

let bnode image ns tgt =
  if image then Image (ns, tgt) else Link (ns, tgt)

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

(** val wiki_display : string -> string option -> string **)

let wiki_display target0 = function
| Some d -> d
| None -> target0

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

type dtable = dconfig
  (* singleton inductive, whose constructor was DTable *)
