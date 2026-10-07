(* ai-disclosure: autonomous *)

(** * Readable Djot rendering

   AST -> djot text meant to be read, for trees built by hand or mapped.
   `Render.v` writes text that parses back to the tree; this writes the
   text a person would type.  A `Str` is written as it is, so text that
   spells syntax (`- x`, `*a*`) reads back as that syntax, and nothing
   here is proved.

   What differs from `Render.render_lines`:
   - no escapes, in text or in a link's destination;
   - a delimiter is written bare where it reads back as one (`bare_ok`);
   - a blank line inside a list item, a quote or a footnote is empty;
   - a table's columns are padded to one width;
   - a footnote that starts with a paragraph starts on its label's line.

   The fences, markers, attribute lines and document assembly are
   `Render.v`'s. *)

From Stdlib Require Import String Ascii List Bool PeanoNat.
From DjotV Require Import Strings Line Ast Attributes InlineTable InlineView
  Parser Render.
From DjotV Require Document.
Import ListNotations.

Local Open Scope string_scope.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(*
Inlines
=======
*)

(* Whether a span of row [k] can be written with bare delimiters, given
   the byte before it, its contents' text, and the rows of the bare spans
   around it.  Otherwise both delimiters take their brace, since a bare
   token and a braced one do not match.  This follows
   `InlineScan.idelim_resolve`:

   - a bare token opens only where its row lets it (`dbare`) and a
     nonspace byte follows;
   - it closes rather than opens when a nonspace byte precedes it and a
     bare opener of its row is waiting, so inside such a span an opener
     has to follow a space;
   - a bare token closes only after a nonspace byte;
   - a neighbour that is the row's own character would join the token's
     run and be cut with it. *)
Local Definition own_char (k : dstyle) (c : option ascii) : bool :=
  match c with Some ch => Ascii.eqb ch (dchar k) | None => false end.

Local Definition bare_ok (k : dstyle) (before : option ascii) (body : string)
  (around : list dstyle) : bool :=
  let first := match body with String c _ => Some c | EmptyString => None end in
  let last := str_last body None in
  dbare k before
  && nonspace_at first && nonspace_at last
  && negb (nonspace_at before && existsb (dstyle_eq k) around)
  && negb (own_char k before || own_char k first || own_char k last).

Local Definition direct_close (dst : string) : string :=
  ("](" ++ dst ++ ")")%string.

(* An inline's text.  [before] is the byte written before it on its line
   and [around] the rows of the bare spans it sits in. *)
Fixpoint readable_text (il : inline) (before : option ascii)
  (around : list dstyle) : string :=
  let go :=
    fix go (ns : inlines) (before : option ascii) (around : list dstyle)
      : string :=
      match ns with
      | [] => EmptyString
      | Node _ a x :: rest =>
          let s :=
            (readable_text x before around
             ++ match a with [] => EmptyString | _ => attr_spec a end)%string in
          (s ++ go rest (str_last s before) around)%string
      end in
  let marked (k : dstyle) (ns : inlines) :=
    let body := go ns (Some (dchar k)) (k :: around) in
    if bare_ok k before body around
    then (dtoken k ++ body ++ dtoken k)%string
    else (marked_open k ++ body ++ marked_close k EmptyString)%string in
  let inside (ns : inlines) := go ns (Some lbrack) around in
  match il with
  | Str s => s
  | Verbatim s => verb_text s
  | Symbol s => (one ":"%char ++ s ++ one ":"%char)%string
  | Emph ns => marked DEmph ns
  | Strong ns => marked DStrong ns
  | Superscript ns => marked DSuper ns
  | Subscript ns => marked DSub ns
  | Highlight ns => marked DMark ns
  | Insert ns => marked DInsert ns
  | Delete ns => marked DDelete ns
  | Quoted SingleQuotes ns => marked DSQuote ns
  | Quoted DoubleQuotes ns => marked DDQuote ns
  | Link ns (Direct dst) => (bracket_open false ++ inside ns ++ direct_close dst)%string
  | Image ns (Direct dst) => (bracket_open true ++ inside ns ++ direct_close dst)%string
  | Link ns (Reference label) =>
      (bracket_open false ++ inside ns ++ ref_close label EmptyString)%string
  | Image ns (Reference label) =>
      (bracket_open true ++ inside ns ++ ref_close label EmptyString)%string
  | FootnoteReference label => note_text label
  | UrlLink s | EmailLink s => auto_text s
  | RawInline fmt s => raw_text fmt s
  | Ext_wikilink embed t al => wiki_text embed t al
  | Math InlineMath s => (one "$"%char ++ verb_text s)%string
  | Math DisplayMath s => (one "$"%char ++ one "$"%char ++ verb_text s)%string
  | Span name ns => (tag_open name ++ inside ns ++ one "]"%char)%string
  | NonBreakingSpace => String bslash (one " "%char)
  | SoftBreak => one "010"%char
  | HardBreak => String bslash (one "010"%char)
  | Hole s => hole_spell s
  end.

Local Fixpoint readable_nodes (ns : inlines) (before : option ascii) : string :=
  match ns with
  | [] => EmptyString
  | Node _ a x :: rest =>
      let s :=
        (readable_text x before []
         ++ match a with [] => EmptyString | _ => attr_spec a end)%string in
      (s ++ readable_nodes rest (str_last s before))%string
  end.

(* The inlines' source lines: a break at any depth ends a line. *)
Definition readable_inline_lines (ils : inlines) : list string :=
  split_lines (readable_nodes ils None).

(*
Blocks
======
*)

(* A container's prefix on one of its lines.  A blank line stays empty. *)
Local Definition prefixed (p l : string) : string :=
  match l with EmptyString => EmptyString | _ => (p ++ l)%string end.

Local Definition quoted (l : string) : string :=
  match l with EmptyString => ">" | _ => quote_line l end.

Local Definition first_then (first rest : string) (ls : list string)
  : list string :=
  match ls with
  | [] => []
  | l :: more => (first ++ l)%string :: map (prefixed rest) more
  end.

Local Definition item_lines (it : litem) : list string :=
  match snd it with
  | [] => [strip_trailing_ws (mk_open (fst it))]
  | ls => first_then (mk_open (fst it)) (mk_cont (fst it)) ls
  end.

Local Definition task_lines (it : task_status * list string) : list string :=
  let box := match fst it with Complete => "- [x]" | Incomplete => "- [ ]" end in
  match snd it with
  | [] => [box]
  | ls => first_then (box ++ " ") (blanks 6) ls
  end.

(* A footnote's lines.  A paragraph's first line goes after the label. *)
Local Definition note_lines (label : string) (para : bool) (ls : list string)
  : list string :=
  let open := ("[^" ++ label ++ "]:")%string in
  match para, ls with
  | true, _ :: _ => first_then (open ++ " ") "  " ls
  | _, _ => open :: map (prefixed "  ") ls
  end.

Local Definition caption_lines (ls : list string) : list string :=
  match ls with
  | [] => ["^"]
  | l :: rest => ("^ " ++ l)%string :: rest
  end.

(*
Tables
------

Widths are in bytes, so a column holding non-ASCII text is padded short.
*)

Local Definition cell_text (c : cell) : string :=
  match c with Cell _ _ ils => hd EmptyString (readable_inline_lines ils) end.

Local Definition cell_align (c : cell) : align :=
  match c with Cell _ al _ => al end.

Local Fixpoint max_zip (a b : list nat) : list nat :=
  match a, b with
  | [], l | l, [] => l
  | x :: a', y :: b' => Nat.max x y :: max_zip a' b'
  end.

Local Definition col_widths (rows : list (list string)) : list nat :=
  fold_right (fun r ws => max_zip (map (fun c => Nat.max 3 (String.length c)) r) ws)
    [] rows.

Local Fixpoint row_body (ws : list nat) (cs : list string) : string :=
  match cs with
  | [] => EmptyString
  | c :: rest =>
      (" " ++ c ++ blanks (hd 0 ws - String.length c) ++ " |"
       ++ row_body (tl ws) rest)%string
  end.

(* A separator cell spans its column and the space on each side. *)
Local Definition sep_cell (w : nat) (a : align) : string :=
  match a with
  | AlignDefault => chars "-" (w + 2)
  | AlignLeft => (":" ++ chars "-" (w + 1))%string
  | AlignRight => (chars "-" (w + 1) ++ ":")%string
  | AlignCenter => (":" ++ chars "-" w ++ ":")%string
  end.

Local Fixpoint sep_row_body (ws : list nat) (als : list align) : string :=
  match als with
  | [] => EmptyString
  | a :: rest =>
      (sep_cell (Nat.max 3 (hd 0 ws)) a ++ "|" ++ sep_row_body (tl ws) rest)%string
  end.

(* The separators sit where `Render.table_lines` puts them. *)
Local Definition table_lines (rows : list (list cell)) : list string :=
  let ws := col_widths (map (map cell_text) rows) in
  let sep (r : list cell) := ("|" ++ sep_row_body ws (map cell_align r))%string in
  let row (r : list cell) :=
    (("|" ++ row_body ws (map cell_text r))%string
     :: match r with
        | Cell HeadCell _ _ :: _ => [sep r]
        | _ => []
        end)%list in
  ((match rows with
    | (Cell BodyCell a _ :: _) as r :: _ =>
        if align_eqb a AlignDefault then [] else [sep r]
    | _ => []
    end) ++ flat_map row rows)%list.

(* A block with its attributes [a], to lines.  The cases follow
   `Render.render_lines`. *)
Fixpoint readable_lines (a : attr) (b : block) : list string :=
  let itemss :=
    fix goitems (items : list (node blocks)) : list (list string) :=
      match items with
      | [] => []
      | Node _ _ it :: rest =>
          sep_lines (map (fun n => readable_lines (node_attrs n) (node_contents n)) it)
          :: goitems rest
      end in
  let taskitemss :=
    fix gotasks (items : list (node (task_status * blocks)))
      : list (task_status * list string) :=
      match items with
      | [] => []
      | Node _ _ (chk, it) :: rest =>
          (chk, sep_lines
                  (map (fun n => readable_lines (node_attrs n) (node_contents n)) it))
          :: gotasks rest
      end in
  let defitemss :=
    fix godefs (its : list (node (node inlines * node blocks))) : list (list string) :=
      match its with
      | [] => []
      | Node _ _ (Node _ _ term, Node _ _ it) :: rest =>
          sep_lines
            ((match term with
              | [] => []
              | _ => [readable_inline_lines term]
              end)
             ++ map (fun n => readable_lines (node_attrs n) (node_contents n)) it)%list
          :: godefs rest
      end in
  let cls := fence_class a b in
  (attr_lines (drop_class cls a) ++
   match b with
   | Para ils => readable_inline_lines ils
   | Heading lvl ils => map (heading_line lvl) (readable_inline_lines ils)
   | ThematicBreak => [thematic_line]
   | CodeBlock lang text =>
       (code_open lang :: split_lines text ++ [code_close])%list
   | RawBlock fmt text =>
       (code_open ("=" ++ fmt)%string :: split_lines text ++ [code_close])%list
   | BlockQuote bs =>
       map quoted
         (sep_lines (map (fun n => readable_lines (node_attrs n) (node_contents n)) bs))
   | Ext_callout kind fold title bs =>
       (quote_line
          (callout_header_line kind fold
             (String.concat " " (readable_inline_lines title)))
        :: map quoted
          (sep_lines (map (fun n => readable_lines (node_attrs n) (node_contents n)) bs)))%list
   | Div name bs =>
       let body := sep_lines (map (fun n => readable_lines (node_attrs n) (node_contents n)) bs) in
       let word := match name with EmptyString => cls | _ => name end in
       (div_open_line (div_fence_for body) word :: body ++ [div_fence_for body])%list
   | Section bs =>
       sep_lines (map (fun n => readable_lines (node_attrs n) (node_contents n)) bs)
   | BulletList bc sp items =>
       list_lines sp (map item_lines (same_marker (MBullet bc) (itemss items)))
   | DefinitionList sp its =>
       list_lines sp (map item_lines (ck_items LKDef (defitemss its)))
   | OrderedList oa sp items =>
       list_lines sp (map item_lines (ck_items (Render.lk_of_ol oa) (itemss items)))
   | TaskList sp items =>
       list_lines sp (map task_lines (taskitemss items))
   | RefDef label dest => [ref_line label dest]
   | FootnoteDef label bs =>
       note_lines label
         (match bs with Node _ [] (Para _) :: _ => true | _ => false end)
         (sep_lines (map (fun n => readable_lines (node_attrs n) (node_contents n)) bs))
   | Ext_keyed label inner =>
       key_lines
         (readable_nodes label None)
         (match inner with Node _ [] (Para _) => true | _ => false end)
         (readable_lines (node_attrs inner) (node_contents inner))
   | Table cap rows =>
       (table_lines (map (fun r => map node_contents (node_contents r)) rows)
        ++ match node_contents cap with
           | [] => []
           | c => caption_lines (readable_inline_lines c)
           end)%list
   end)%list.

Definition readable_djot (bs : blocks) : string :=
  String.concat nl
    (sep_lines (map (fun n => readable_lines (node_attrs n) (node_contents n)) bs)).

(* A parsed document: derived heading ids left out, as
   `Render.render_doc` has them. *)
Definition readable_doc (d : doc) : string :=
  readable_djot (doc_source_blocks d).

End WithTable.
