(* ai-disclosure: autonomous *)

(** * Rendering with escapes decided by the scanner

   `Render.render_djot` with one change: a paragraph's text escapes a
   byte of a `Str` only where the paragraph would read differently with
   it bare (`.project/261007.plan.irredundant-escapes.md`).

   The test for a byte is against the rest of the paragraph spelled with
   every escape (`full`): writing it bare must give the paragraph's text,
   parsed on its own, the reading that the fully escaped spelling gives.  So the paragraph's
   reading is preserved byte by byte, whatever the later bytes turn out
   to be.  The start of a line is a block question the scanner does not
   answer, and is decided as `Render` decides it.

   Nothing here is proved yet.  The tests run it against the round-trip
   pools and the escape count (`test/roundtrip.ml`, `test/escapes.ml`). *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Strings Ast Attributes InlineTable InlineView
  InlineScan Parser Render.
Import ListNotations.

Local Open Scope string_scope.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(*
Equality of inlines
===================

Positions are not compared: the scan runs at `semantic_pos`, where every
node has none.
*)

Local Fixpoint attr_eqb (a b : attr) : bool :=
  match a, b with
  | [], [] => true
  | (k, v) :: a', (l, w) :: b' => String.eqb k l && String.eqb v w && attr_eqb a' b'
  | _, _ => false
  end.

Local Definition target_eqb (x y : target) : bool :=
  match x, y with
  | Direct s, Direct t | Reference s, Reference t => String.eqb s t
  | _, _ => false
  end.

Local Definition opt_eqb (x y : option string) : bool :=
  match x, y with
  | Some s, Some t => String.eqb s t
  | None, None => true
  | _, _ => false
  end.

Fixpoint inline_eqb (x y : inline) : bool :=
  let fix go (xs ys : inlines) : bool :=
    match xs, ys with
    | [], [] => true
    | Node _ a x' :: xs', Node _ b y' :: ys' =>
        attr_eqb a b && inline_eqb x' y' && go xs' ys'
    | _, _ => false
    end in
  match x, y with
  | Str s, Str t | Verbatim s, Verbatim t | Symbol s, Symbol t
  | FootnoteReference s, FootnoteReference t | UrlLink s, UrlLink t
  | EmailLink s, EmailLink t | Hole s, Hole t => String.eqb s t
  | Emph xs, Emph ys | Strong xs, Strong ys | Highlight xs, Highlight ys
  | Insert xs, Insert ys | Delete xs, Delete ys
  | Superscript xs, Superscript ys | Subscript xs, Subscript ys => go xs ys
  | Math DisplayMath s, Math DisplayMath t | Math InlineMath s, Math InlineMath t =>
      String.eqb s t
  | Link xs u, Link ys v | Image xs u, Image ys v => target_eqb u v && go xs ys
  | Span m xs, Span n ys => String.eqb m n && go xs ys
  | RawInline f s, RawInline g t => String.eqb f g && String.eqb s t
  | Quoted SingleQuotes xs, Quoted SingleQuotes ys
  | Quoted DoubleQuotes xs, Quoted DoubleQuotes ys => go xs ys
  | NonBreakingSpace, NonBreakingSpace | SoftBreak, SoftBreak
  | HardBreak, HardBreak => true
  | Ext_wikilink e s a, Ext_wikilink f t b =>
      Bool.eqb e f && String.eqb s t && opt_eqb a b
  | _, _ => false
  end.

Local Fixpoint inlines_eqb (xs ys : inlines) : bool :=
  match xs, ys with
  | [], [] => true
  | Node _ a x :: xs', Node _ b y :: ys' =>
      attr_eqb a b && inline_eqb x y && inlines_eqb xs' ys'
  | _, _ => false
  end.

(*
A paragraph's bytes
===================

A paragraph's source as `Render.text_lines` writes it, one byte at a
time, before any escape: `true` marks a byte of a `Str`, which the
spelling below may escape, and `false` a byte of the syntax around it.
The cases follow `InlineView.inline_text` and `inline_lines`.
*)

Local Open Scope list_scope.

Local Fixpoint text_bytes (s : string) : list (bool * ascii) :=
  match s with
  | EmptyString => []
  | String c rest => (true, c) :: text_bytes rest
  end.

Local Fixpoint fixed (s : string) : list (bool * ascii) :=
  match s with
  | EmptyString => []
  | String c rest => (false, c) :: fixed rest
  end.

Local Fixpoint inline_bytes (il : inline) : list (bool * ascii) :=
  let go :=
    fix go (ns : inlines) : list (bool * ascii) :=
      match ns with
      | [] => []
      | Node _ [] x :: rest => inline_bytes x ++ go rest
      | Node _ a x :: rest => inline_bytes x ++ fixed (attr_spec a) ++ go rest
      end in
  let marked (k : dstyle) (ns : inlines) :=
    fixed (marked_open k) ++ go ns ++ fixed (marked_close k EmptyString) in
  match il with
  | Str s => text_bytes s
  | Emph ns => marked DEmph ns
  | Strong ns => marked DStrong ns
  | Superscript ns => marked DSuper ns
  | Subscript ns => marked DSub ns
  | Highlight ns => marked DMark ns
  | Insert ns => marked DInsert ns
  | Delete ns => marked DDelete ns
  | Quoted SingleQuotes ns => marked DSQuote ns
  | Quoted DoubleQuotes ns => marked DDQuote ns
  | Link ns (Direct dst) =>
      fixed (bracket_open false) ++ go ns ++ fixed (link_close dst EmptyString)
  | Image ns (Direct dst) =>
      fixed (bracket_open true) ++ go ns ++ fixed (link_close dst EmptyString)
  | Link ns (Reference label) =>
      fixed (bracket_open false) ++ go ns ++ fixed (ref_close label EmptyString)
  | Image ns (Reference label) =>
      fixed (bracket_open true) ++ go ns ++ fixed (ref_close label EmptyString)
  | Span name ns => fixed (tag_open name) ++ go ns ++ fixed (one "]"%char)
  | _ => fixed (inline_text il)
  end.

Local Fixpoint para_bytes (ils : inlines) : list (bool * ascii) :=
  match ils with
  | [] => []
  | Node _ _ SoftBreak :: rest => fixed nl ++ para_bytes rest
  | Node _ _ HardBreak :: rest => fixed (String bslash nl) ++ para_bytes rest
  | Node _ [] il :: rest => inline_bytes il ++ para_bytes rest
  | Node _ a il :: rest => inline_bytes il ++ fixed (attr_spec a) ++ para_bytes rest
  end.

Local Open Scope string_scope.

(*
The spelling
============
*)

(* Every punctuation byte of a `Str` escaped. *)
Local Fixpoint full (bs : list (bool * ascii)) : string :=
  match bs with
  | [] => EmptyString
  | (d, c) :: rest =>
      if d && is_punct c then String bslash (String c (full rest))
      else String c (full rest)
  end.

(* The line `s` ends on, reversed, onto `acc`. *)
Local Fixpoint line_rev (s acc : string) : string :=
  match s with
  | EmptyString => acc
  | String c rest =>
      if Ascii.eqb c "010"%char then line_rev rest EmptyString
      else line_rev rest (String c acc)
  end.

(* Whether the block layer needs `c` escaped, after `pre` (the line so far,
   reversed) and before `rest`: a line's first byte when it may open a
   block, and a period or a parenthesis that could end a list number
   (`InlineView.escapes`). *)
Local Definition line_forced (pre : string) (c : ascii) (rest : string) : bool :=
  match pre with
  | EmptyString => needs_escape c || opens_line c
  | _ =>
      (Ascii.eqb c period || Ascii.eqb c rparen) && marker_core pre
      && match rest with
         | EmptyString => true
         | String d _ => is_ws d || Ascii.eqb d "010"%char
         end
  end.

(* What a paragraph's text reads as on its own: its inlines when it is one
   paragraph.  Read through the block parser, since a bare byte can turn
   a line into a block (`{_=a_}` is an attribute line). *)
Local Definition reads (s : string) : option inlines :=
  match parse_blocks s with
  | [Node _ [] (Para ils)] => Some ils
  | _ => None
  end.

Local Definition reads_eqb (x y : option inlines) : bool :=
  match x, y with
  | Some xs, Some ys => inlines_eqb xs ys
  | None, None => true
  | _, _ => false
  end.

(* [out] is what is written so far and [want] the reading of the fully
   escaped spelling.  A text the parser does not read as one paragraph on
   its own (`want = None`) is spelled with every escape. *)
Local Fixpoint spell (want : option inlines) (out : string)
  (bs : list (bool * ascii)) : string :=
  match bs with
  | [] => out
  | (d, c) :: rest =>
      let tail := full rest in
      let esc :=
        d && is_punct c
        && (match want with None => true | Some _ => false end
            || line_forced (line_rev out EmptyString) c tail
            || negb (reads_eqb (reads (out ++ String c tail)) want)) in
      spell want (out ++ if esc then String bslash (one c) else one c) rest
  end.

Definition text_lines_scan (ils : inlines) : list string :=
  let bs := para_bytes ils in
  split_lines (spell (reads (full bs)) EmptyString bs).

Definition render_djot_scan (bs : blocks) : string :=
  String.concat nl
    (sep_lines
       (map (fun n => render_lines_with text_lines_scan (node_attrs n) (node_contents n))
          bs)).

End WithTable.
