(* ai-disclosure: autonomous *)

(* The inline pass: the single-pass scanner over a paragraph's text, its
   scope stack, the line-level drivers, `para_inlines`, and the key
   connective (`.project/keyed-blocks.md`). *)

From Stdlib Require Import String Ascii List Bool Lia Wf_nat Arith.
From DjotV Require Import Config Strings Ast Attributes InlineTable InlineView.
Import ListNotations.

Local Open Scope string_scope.

(*
Inline text buffers
===================

Pending text and source kept by an open construct use one abstract
buffer. The scanner is written once against these operations. At
`string` it is the specification: `tpush` is `++` and `tval` is the
identity. An instance that appends without copying (`InlineBuffer.v`)
runs it, and `map_text` relates the two.
*)
#[projections(primitive)]
Class TextOps (Buf : Type) : Type := {
  tnil : Buf;
  tpush : Buf -> string -> Buf;
  tof : string -> Buf;
  tval : Buf -> string;
  tnonempty : Buf -> bool
}.

(* The string instance is a literal record rather than a named constant,
   so a restricted `cbn` reduces `tpush txt s` to `txt ++ s` without
   being told to unfold it.  It is also the instance chosen when `Buf` is
   undetermined, which keeps a binder such as `forall st, ... st ...`
   reading as the specification scanner. *)
#[export] Hint Extern 100 (TextOps _) =>
  exact ({| tnil := EmptyString;
            tpush := fun t s => (t ++ s)%string;
            tof := fun s => s;
            tval := fun t => t;
            tnonempty := nonempty_str |}) : typeclass_instances.

(* The string instance's operations, rewritten to what they mean, in the
   goal and every hypothesis.  For proofs that `unfold` a scanner
   definition, which leaves the projections unreduced. *)
Ltac tred :=
  repeat match goal with
  | |- context [@tval string ?I ?t] => change (@tval string I t) with t
  | |- context [@tpush string ?I ?a ?b] => change (@tpush string I a b) with (a ++ b)%string
  | |- context [@tof string ?I ?s] => change (@tof string I s) with s
  | |- context [@tnil string ?I] => change (@tnil string I) with EmptyString
  | |- context [@tnonempty string ?I ?t] => change (@tnonempty string I t) with (nonempty_str t)
  | H : context [@tval string ?I ?t] |- _ => change (@tval string I t) with t in H
  | H : context [@tpush string ?I ?a ?b] |- _ => change (@tpush string I a b) with (a ++ b)%string in H
  | H : context [@tof string ?I ?s] |- _ => change (@tof string I s) with s in H
  | H : context [@tnil string ?I] |- _ => change (@tnil string I) with EmptyString in H
  | H : context [@tnonempty string ?I ?t] |- _ => change (@tnonempty string I t) with (nonempty_str t) in H
  end.

(*
Chunks
======

Text or source as the pieces appended so far, newest first. Appending
conses one piece; the value is joined when a rule needs it. No piece is
empty, so `existsb` answers at the head.
*)
Definition chunks := list string.

Definition chunks_push (b : chunks) (s : string) : chunks :=
  if nonempty_str s then s :: b else b.

Definition chunks_value (b : chunks) : string :=
  String.concat EmptyString (List.rev b).

(* Below the string default, so an undetermined buffer stays `string`. *)
#[export] Instance chunks_text : TextOps chunks | 200 := {|
  tnil := [];
  tpush := chunks_push;
  tof := chunks_push [];
  tval := chunks_value;
  tnonempty := existsb nonempty_str
|}.


Section WithTable.
Context {T : dtable}.

(*
The inline pass
===============
*)

(* Verbatim content is trimmed of one padding space at each end, but only
   where it sits against a backtick.  A space not adjacent to a backtick
   is content: `` ` a ` `` really is " a ".  Reversed, "ends with a
   backtick then a space" is "starts with a space then a backtick", so
   one function does both ends. *)

Local Definition strip_pad (s : string) : string :=
  match s with
  | String c rest =>
      if (Ascii.eqb c " "%char && starts_tick rest)%bool then rest else s
  | EmptyString => s
  end.

Definition trim_verb (s : string) : string :=
  rev_string (strip_pad (rev_string (strip_pad s))).

Local Lemma strip_pad_added :
  forall s, starts_tick s = true -> strip_pad (" " ++ s) = s.
Proof.
  intros [|c s] H; [discriminate|].
  cbn [starts_tick] in H. cbn [strip_pad append starts_tick].
  rewrite H. reflexivity.
Qed.

Local Lemma strip_pad_stable :
  forall s, negb (starts_space_tick s) = true -> strip_pad s = s.
Proof.
  intros [|c s] H; [reflexivity|]. destruct s as [|d s].
  - cbn [strip_pad starts_tick]. destruct (Ascii.eqb c " "%char); reflexivity.
  - cbn [starts_space_tick strip_pad] in H |- *.
    destruct (Ascii.eqb c " "%char) eqn:Hc; [|reflexivity].
    destruct (is_tick d) eqn:Hd; [discriminate|].
    cbn [starts_tick]. rewrite Hd. reflexivity.
Qed.

Local Lemma strip_pad_pad_verb :
  forall s, negb (starts_space_tick s) = true ->
    strip_pad (pad_verb s)
    = (s ++ if ends_tick s then " " else EmptyString)%string.
Proof.
  intros [|c [|d s]] H; unfold pad_verb;
    cbn [starts_tick starts_space_tick append] in H |- *.
  - reflexivity.
  - destruct (is_tick c) eqn:Hc;
      destruct (ends_tick (String c EmptyString)) eqn:He;
      cbn [append strip_pad starts_tick].
    + rewrite Hc. reflexivity.
    + rewrite Hc. reflexivity.
    + unfold ends_tick, rev_string, starts_tick in He.
      cbn [rev_string_aux] in He. rewrite Hc in He. discriminate.
    + destruct (Ascii.eqb c " "%char); reflexivity.
  - destruct (is_tick c) eqn:Hc;
      destruct (ends_tick (String c (String d s))) eqn:He;
      cbn [append strip_pad starts_tick].
    + rewrite Hc. reflexivity.
    + rewrite Hc. reflexivity.
    + apply negb_true_iff in H. rewrite H. reflexivity.
    + apply negb_true_iff in H. rewrite H. reflexivity.
Qed.

Lemma trim_verb_pad :
  forall s, verb_content_ok s = true -> trim_verb (pad_verb s) = s.
Proof.
  intros s H. unfold verb_content_ok in H.
  repeat rewrite andb_true_iff in H.
  destruct H as [[[Hnl Hleft] Hright] Hsafe].
  unfold trim_verb. rewrite strip_pad_pad_verb by exact Hleft.
  destruct (ends_tick s) eqn:He.
  - rewrite rev_string_app. cbn [rev_string rev_string_aux append].
    change (rev_string (strip_pad (" " ++ rev_string s)) = s).
    rewrite strip_pad_added.
    + apply rev_string_involutive.
    + exact He.
  - rewrite append_empty_r. rewrite strip_pad_stable by exact Hright.
    apply rev_string_involutive.
Qed.

(*
The scanner
-----------

One character at a time, structurally recursive on the remaining input,
so the scan never feeds a source position back through tokenization
(`.project/no-backtracking.md`).  This is not a linear-time claim:
resolving one byte may still walk the opener stack.

A verbatim closer is a run of exactly the opening width, so a run cannot
be resolved until the character after it arrives: `IVerb` carries a
pending run count rather than closing eagerly.  A run of the wrong width
is content, which is how `` ` `` ` `` holds two backticks inside a
one-backtick fence. *)

Lemma nat_eqb_refl : forall n, Nat.eqb n n = true.
Proof. induction n; [reflexivity|exact IHn]. Qed.

(*
The scope stack
---------------

A stack of open scopes, each carrying its own accumulated inlines.
djot.js instead rewrites a flat event list; the two agree
(`.project/archived/260811.inline-parser.md`), and the stack is what the proofs
can induct on.

Closing pops a scope and emits its node.  Abandoning replaces a scope by
literal text: its opener's spelling, then its content, spliced into the
level below. *)

(* What a scope accumulates: a finished node, or an attribute spec whose
   target is not settled yet.

   A spec attaches to what precedes it once openers are resolved, when an
   opener that never closed is already text.  At the `}` the answer is not
   yet available (`a *b{.c}o` attaches to `b`, not `*b`, and whether the
   `*` closes is not known), so the spec waits here and `oresolve`
   settles it when the scope does. *)
Inductive oitem : Type :=
  | OIn (n : node inline)
  | OMark (a : attr) (spec : span) (word_start : option spot).

Definition oitems : Type := list oitem.

Inductive frame_kind : Type :=
  (* `closemark` is a `}` immediately after a marked opener.  It does not
     stop the token opening, and the `}` stays as text; it changes only
     the abandoned spelling (`fr_src`).  A marked double quote with a `}`
     after it opens a scope whose abandoned spelling is the right curly
     quote. *)
  | FKDelim (style : dstyle) (closemark : bool)
  (* `image` records the `!` before the `[`.  It cannot be read back at
     the close: the text before the bracket has been flushed by then, and
     an escaped `\!` looks like a bare one. *)
  | FKBracket (image : bool)
  (* The scope an unterminated destination decays into.  `](` does not
     end the bracket construct: the `[` stays open until the balanced `)`,
     so the destination is scanned as ordinary content that only becomes
     literal at the close.  This frame is that opener, with the label and
     the `](` already inside it as text, so its decay is the bracket's own
     byte and not the whole region.

     Unlike `FKBracket`, a delimiter closer inside a destination may not
     reach an opener from outside the link, so this frame stops the walk.
     `[u](a ]{.c}`, where djot.js re-enters the bracket, is not matched
     (`.project/exact-html-gaps.md`). *)
  | FKDest (image : bool)
  (* A named bracket, `:name[` (`.project/custom-tags.md`).  Its `]`
     closes it at once, so no byte after the `]` is waited for and the
     frame is never handed to `bclose`. *)
  | FKTag (name : string).

Record frame : Type := Frame {
  fr_kind : frame_kind;
  fr_marked : bool;          (* delimiter opened as `{d`; false for `[` *)
  fr_open : span;            (* the opener token, for the node it closes *)
  fr_out : oitems            (* this scope's items, reversed *)
}.

(* The opener's source text, which is what it decays to when abandoned. *)
Definition fr_src (f : frame) : string :=
  match fr_kind f with
  | FKDelim k cm => ddecay_str k (fr_marked f) cm
  | FKBracket image | FKDest image => bracket_open image
  | FKTag name => tag_open name
  end.

(* Whether a closer's search out through the open scopes stops here
   rather than abandoning this one and carrying on. *)
Definition fr_barrier (f : frame) : bool :=
  match fr_kind f with
  | FKDest _ => true
  | FKDelim _ _ | FKBracket _ | FKTag _ => false
  end.

Record ostate : Type := OState {
  os_out : oitems;           (* the outermost scope, reversed *)
  os_stk : list frame;       (* open scopes, innermost first *)
  os_word_start : option spot
}.

Definition ostart : ostate := OState [] [] None.

(* Which of two points is further into the source. *)
Local Definition spot_later (a b : spot) : spot :=
  if Nat.ltb (spot_line a) (spot_line b) then b
  else if Nat.ltb (spot_line b) (spot_line a) then a
  else if Nat.ltb (spot_rem a) (spot_rem b) then a else b.

(* Where a node's source ends, for the text that follows it: its own stop,
   or the end of the authored syntax it carries but does not cover.  An
   attribute spec sits after the node it attaches to and is not part of
   its range (`RAttrSpec`). *)
Local Definition roles_stop (p : provenance) : spot :=
  fold_left (fun acc e => spot_later acc (span_stop (snd e)))
    (syntax_spans p) (span_stop (node_span p)).

Local Definition node_stop (fallback : spot) (n : node inline) : spot :=
  match node_provenance n with
  | Some p => roles_stop p
  | None => fallback
  end.

Local Fixpoint items_stop (fallback : spot) (l : oitems) : spot :=
  match l with
  | [] => fallback
  | OIn n :: _ => node_stop fallback n
  | OMark _ spec _ :: _ => span_stop spec
  end.

Definition text_start `{InlineCursor} (o : ostate) : spot :=
  match os_stk o with
  | [] => items_stop cursor_origin (os_out o)
  | f :: _ => items_stop (span_stop (fr_open f)) (fr_out f)
  end.

Definition remember_word_start `{PosPolicy} `{InlineCursor}
  (c : ascii) (o : ostate) : ostate :=
  if pos_records && is_ws c then
    OState (os_out o) (os_stk o) (Some cursor_stop)
  else o.

(* A line break ends the pending word: the spot after this line's last
   whitespace byte names no start on the next one, and the text node the
   break separates begins there. *)
Definition oword_reset (o : ostate) : ostate :=
  OState (os_out o) (os_stk o) None.

Local Definition inline_prov (start stop : spot) : provenance :=
  prov_at (SrcSpan start stop).

Definition imk `{PosPolicy} (start stop : spot) (x : inline) : node inline :=
  if pos_records
  then posnode (inline_prov start stop) x
  else mk x.

Lemma imk_semantic : forall start stop x,
  @imk semantic_pos start stop x = mk x.
Proof. reflexivity. Qed.

Lemma remember_word_start_semantic : forall c o,
  @remember_word_start semantic_pos semantic_inline_cursor c o = o.
Proof. reflexivity. Qed.

Definition imk_here `{PosPolicy} `{InlineCursor} (x : inline) : node inline :=
  imk cursor_start cursor_stop x.

(* An abandoned opener, put back as text.  It covers the source the
   opener was written in, which is not the length of what the decay
   spells: a smart quote is written `'` and decays to a curly quote. *)
Definition fr_lit `{PosPolicy} (f : frame) : node inline :=
  imk (span_start (fr_open f)) (span_stop (fr_open f)) (Str (fr_src f)).

Local Lemma fr_lit_semantic : forall f,
  @fr_lit semantic_pos f = mk (Str (fr_src f)).
Proof. reflexivity. Qed.

Lemma imk_here_semantic : forall x,
  @imk_here semantic_pos semantic_inline_cursor x = mk x.
Proof. reflexivity. Qed.

Definition add_inline_role `{PosPolicy} (role : syntax_role) (r : span)
  (n : node inline) : node inline := add_roles [(role, r)] n.

Lemma add_inline_role_semantic : forall role r n,
  @add_inline_role semantic_pos role r n = n.
Proof. reflexivity. Qed.

(* The scope emissions land in: the innermost open one, or the bottom. *)
Definition ocur (o : ostate) : oitems :=
  match os_stk o with [] => os_out o | f :: _ => fr_out f end.

(* ...and the same scope, written back.  Only attachment needs it: every
   other writer pushes rather than replaces. *)
Definition oset_cur (l : oitems) (o : ostate) : ostate :=
  match os_stk o with
  | [] => OState l [] (os_word_start o)
  | f :: rest =>
      OState (os_out o)
        (Frame (fr_kind f) (fr_marked f) (fr_open f) l :: rest)
        (os_word_start o)
  end.

(* A closer matches an opener when the character and the marking agree,
   so `{_a_` does not close and neither does `_a_}`. *)
Definition dmatch (k : dstyle) (m : bool) (f : frame) : bool :=
  match fr_kind f with
  | FKDelim k' _ => (dstyle_eq k k' && Bool.eqb m (fr_marked f))%bool
  | FKBracket _ | FKDest _ | FKTag _ => false
  end.

(* An attribute-less `Str` -- the kind a neighbour merges with. *)
Definition plain_str (n : node inline) : bool :=
  match n with Node _ [] (Str _) => true | _ => false end.

(* No two of them adjacent.  Defined here because `oresolve` is the
   identity exactly on lists that satisfy it, and the equations about
   closing a scope need to say so. *)
Fixpoint no_adjacent_str (ns : list (node inline)) : bool :=
  match ns with
  | n1 :: ((n2 :: _) as rest) =>
      negb (plain_str n1 && plain_str n2) && no_adjacent_str rest
  | _ => true
  end.

(* The range of two merged text nodes: the first's start to the second's
   stop. *)
Definition merge_text_pos (left right : pos) : pos :=
  match left, right with
  | SomePos p, SomePos q =>
      SomePos (Provenance
        (SrcSpan (span_start (node_span p)) (span_stop (node_span q)))
        (syntax_spans p ++ syntax_spans q)%list)
  | _, _ => left
  end.

(* Push onto a reversed list of resolved nodes, merging two plain `Str`s
   at the seam. *)
Definition isnoc (n : node inline) (out : inlines) : inlines :=
  match out, n with
  | Node p [] (Str t) :: rest, Node q [] (Str s) =>
      (Node (merge_text_pos p q) [] (Str (t ++ s)) :: rest)%list
  | _, _ => (n :: out)%list
  end.

(* The same question `starts_str` asks, of a resolved list. *)
Definition istarts_str (out : inlines) : bool :=
  match out with Node _ [] (Str _) :: _ => true | _ => false end.

(* `base_ok` of a resolved list: what a previous line always looks like
   once it is settled. *)
Definition ibase_ok (out : inlines) : bool :=
  match out with
  | [] => true
  | Node _ _ SoftBreak :: _ => true
  | _ => false
  end.

Lemma ibase_ok_starts_str :
  forall out, ibase_ok out = true -> istarts_str out = false.
Proof.
  intros [|[p [|kv a] v] out] H; try reflexivity.
  destruct v; try reflexivity. discriminate.
Qed.

Local Lemma isnoc_nonstr :
  forall n out, istarts_str out = false -> isnoc n out = (n :: out)%list.
Proof.
  intros n [|[a [|x xs] i] out'] H; try reflexivity.
  cbn [istarts_str] in H. destruct i; try reflexivity.
  destruct n as [c [|y ys] j]; try reflexivity.
  destruct j; try reflexivity. discriminate.
Qed.

Lemma isnoc_nonplain :
  forall n out, plain_str n = false -> isnoc n out = (n :: out)%list.
Proof.
  intros [p a v] out H. unfold isnoc.
  destruct out as [|[q [|kv b] w] l]; try reflexivity.
  destruct w; try reflexivity.
  unfold plain_str in H. destruct a; [|reflexivity].
  destruct v; try reflexivity. discriminate.
Qed.

Lemma isnoc_app :
  forall n out base,
    istarts_str base = false ->
    isnoc n (out ++ base)%list = (isnoc n out ++ base)%list.
Proof.
  intros n [|x out] base H; cbn [app]; [apply isnoc_nonstr, H|].
  unfold isnoc. destruct x as [p [|kv a] v]; [|reflexivity].
  destruct v; try reflexivity.
  destruct n as [q [|lv b] w]; [|reflexivity].
  destruct w; reflexivity.
Qed.

(* The same push on a scope's items. *)
Definition osnoc (n : oitem) (out : oitems) : oitems :=
  match out, n with
  | OIn (Node p [] (Str t)) :: rest, OIn (Node q [] (Str s)) =>
      (OIn (Node (merge_text_pos p q) [] (Str (t ++ s))) :: rest)%list
  | _, _ => (n :: out)%list
  end.

(* Whether the seam could merge: the head is a plain `Str`.  A `Str` with
   attributes is a node in its own right and never merges. *)
Definition starts_str (out : oitems) : bool :=
  match out with OIn (Node _ [] (Str _)) :: _ => true | _ => false end.

Fixpoint oapp (cur out : oitems) : oitems :=
  match cur with
  | [] => out
  | [n] => osnoc n out
  | n :: rest => n :: oapp rest out
  end.

Definition oemit (n : node inline) (o : ostate) : ostate :=
  let word := os_word_start o in
  match os_stk o with
  | [] => OState (OIn n :: os_out o) [] word
  | f :: rest =>
      OState (os_out o)
        (Frame (fr_kind f) (fr_marked f) (fr_open f)
           (OIn n :: fr_out f) :: rest)
        word
  end.

(* A spec waiting for its target, emitted the same way. *)
Definition omark (a : attr) (spec : span) (o : ostate) : ostate :=
  match os_stk o with
  | [] => OState (OMark a spec (os_word_start o) :: os_out o) [] None
  | f :: rest =>
      OState (os_out o)
        (Frame (fr_kind f) (fr_marked f) (fr_open f)
           (OMark a spec (os_word_start o) :: fr_out f) :: rest)
        None
  end.

(* Emit, merging a plain-`Str` seam.  Used where a state is rebuilt from
   source fragments (abandoned frames, the bracket's literal fallback);
   ordinary emission leaves the seam obligation to `iscan_wf`. *)
Definition oemit_merge (n : node inline) (o : ostate) : ostate :=
  match os_stk o with
  | [] => OState (osnoc (OIn n) (os_out o)) [] (os_word_start o)
  | f :: rest =>
      OState (os_out o)
        (Frame (fr_kind f) (fr_marked f) (fr_open f)
           (osnoc (OIn n) (fr_out f)) :: rest)
        (os_word_start o)
  end.

Fixpoint oemit_all_merge (ns : inlines) (o : ostate) : ostate :=
  match ns with
  | [] => o
  | n :: rest => oemit_all_merge rest (oemit_merge n o)
  end.

Fixpoint oemit_all (ns : inlines) (o : ostate) : ostate :=
  match ns with
  | [] => o
  | n :: rest => oemit_all rest (oemit n o)
  end.

Definition flush_text_at `{PosPolicy} `{InlineCursor}
  (txt : string) (o : ostate) : ostate :=
  if nonempty_str txt
  then oemit (imk (text_start o) cursor_start (Str txt)) o
  else o.

Definition flush_text_to_at `{PosPolicy} `{InlineCursor}
  (stop : spot) (txt : string) (o : ostate) : ostate :=
  if nonempty_str txt
  then oemit (imk (text_start o) stop (Str txt)) o
  else o.

(* The equational theory below is the semantic scanner's.  Keep its
   familiar names definitionally position-free; the located driver and
   the shared transition use the [_at] forms explicitly. *)
Definition flush_text (txt : string) (o : ostate) : ostate :=
  @flush_text_at semantic_pos semantic_inline_cursor txt o.

Local Lemma flush_text_at_semantic : forall txt o,
  @flush_text_at semantic_pos semantic_inline_cursor txt o = flush_text txt o.
Proof. reflexivity. Qed.

(* A stop the policy discards is a stop the semantic reading cannot see,
   so at that instance the two flushes are one function. *)
Local Lemma flush_text_to_at_semantic : forall stop txt o,
  @flush_text_to_at semantic_pos semantic_inline_cursor stop txt o =
  flush_text txt o.
Proof. reflexivity. Qed.

Definition opush_at
  (k : dstyle) (m cm : bool) (open : span) (o : ostate) : ostate :=
  OState (os_out o)
    (Frame (FKDelim k cm) m open [] :: os_stk o)
    (os_word_start o).

Definition previous_spot (p : spot) : spot :=
  Spot (spot_line p) (S (spot_rem p)).

(* How much source a string covers, as (line breaks, bytes before the
   first of them, bytes in all). *)
Local Fixpoint source_shape (s : string) : nat * nat * nat :=
  match s with
  | EmptyString => (0, 0, 0)
  | String c rest =>
      let '(lines, first, total) := source_shape rest in
      if Ascii.eqb c nl_char
      then (S lines, 0, S total)
      else (lines, S first, S total)
  end.

(* The point [s] bytes to the left of [p].  This is how a construct whose
   role is decided by a later byte recovers where it began: the token's
   own source is in the state, and stepping the cursor back over it is
   the token's first byte -- which is also where the text before it
   stopped.  Sound only for a token that cannot contain a line break,
   which is every construct resolved this way; a verbatim's content can,
   and reads its start off the scope instead (`text_start`). *)
Definition spot_before (p : spot) (s : string) : spot :=
  let '(lines, first, total) := source_shape s in
  if Nat.eqb lines 0
  then Spot (spot_line p) (spot_rem p + total)
  else Spot (spot_line p - lines) first.

(* [n] bytes to the left, on the same line.  The counted form of
   `spot_before`, for a token whose source is known by length. *)
Local Definition spot_plus (n : nat) (p : spot) : spot :=
  Spot (spot_line p) (spot_rem p + n).

(* Where a delimiter token being resolved began, and so where the text
   before it stopped: the run of the row's character, with the `{` of a
   marked opener in front of it.  The token is complete and the byte
   after it is the one in hand, so the cursor is its end. *)
Definition dtoken_span `{PosPolicy} `{InlineCursor}
  (k : dstyle) (marked : bool) : span :=
  pspan (SrcSpan
    (spot_before cursor_start
       ((if marked then one lbrace else EmptyString) ++ dtoken k)%string)
    cursor_start).

(* The common case: no `}` follows the opener, which is every unmarked
   one and every marked one whose next byte is anything else. *)
Definition opush `{PosPolicy} `{InlineCursor}
  (k : dstyle) (m : bool) (o : ostate) : ostate :=
  opush_at k m false (dtoken_span k m) o.

Definition bpush `{PosPolicy} `{InlineCursor} (image : bool) (o : ostate)
  : ostate :=
  let start := if image then previous_spot cursor_start else cursor_start in
  OState (os_out o)
    (Frame (FKBracket image) false (pspan (SrcSpan start cursor_stop)) []
       :: os_stk o)
    (os_word_start o).

(* The same push for a `](`: the bracket's opener stays open, and what
   goes into it is the label put back as text. *)
Definition dpush (image : bool) (open : span) (o : ostate) : ostate :=
  OState (os_out o)
    (Frame (FKDest image) false open [] :: os_stk o)
    (os_word_start o).

(* A named bracket's push.  Its opener starts at the colon, `start`, and
   ends after the `[`. *)
Definition tag_push `{PosPolicy} `{InlineCursor} (name : string) (start : spot)
  (o : ostate) : ostate :=
  OState (os_out o)
    (Frame (FKTag name) false (pspan (SrcSpan start cursor_stop)) []
       :: os_stk o)
    (os_word_start o).

Lemma oemit_all_app :
  forall a b o, oemit_all (a ++ b)%list o = oemit_all b (oemit_all a o).
Proof.
  induction a as [|n a IH]; intros b o; cbn [oemit_all];
    [reflexivity|apply IH].
Qed.

Lemma oemit_all_frame :
  forall ns out kind m open acc stk word,
    oemit_all ns (OState out (Frame kind m open acc :: stk) word)
    = OState out
        (Frame kind m open (List.rev (List.map OIn ns) ++ acc)%list :: stk)
        word.
Proof.
  induction ns as [|n ns IH]; intros out kind m open acc stk word;
    cbn [oemit_all List.map List.rev app]; [reflexivity|].
  change (oemit_all ns
            (OState out (Frame kind m open (OIn n :: acc) :: stk) word)
          = OState out
              (Frame kind m open
                 ((List.rev (List.map OIn ns) ++ [OIn n]) ++ acc)%list
               :: stk) word).
  rewrite IH, <- List.app_assoc. reflexivity.
Qed.

(* The run an attribute spec attaches to when text precedes it:
   everything after the last whitespace.  The split is on whitespace, not
   on word characters: `foo bar{.a}` attributes `bar`, and `a-b{.a}` all
   of `a-b`.  The result satisfies `s = pre ++ w` with `w`
   whitespace-free, so an attributed `Str` never contains a space. *)
Fixpoint last_ws_split (s : string) : string * string :=
  match s with
  | EmptyString => (EmptyString, EmptyString)
  | String c rest =>
      match last_ws_split rest with
      | (EmptyString, w) =>
          if is_ws c then (one c, w) else (EmptyString, String c w)
      | (pre, w) => (String c pre, w)
      end
  end.

(* A last word can only come from text there was. *)
Local Lemma last_ws_split_nonempty :
  forall s, nonempty_str (snd (last_ws_split s)) = true -> nonempty_str s = true.
Proof. intros [|c s] H; [exact H|reflexivity]. Qed.

(* A text node's range, split at the start of its last word. *)
Definition split_text_pos (p : pos) (word_start : option spot)
  : pos * pos :=
  match p, word_start with
  | SomePos pr, Some w =>
      (SomePos (prov_at (SrcSpan (span_start (node_span pr)) w)),
       SomePos (prov_at (SrcSpan w (span_stop (node_span pr)))))
  | _, _ => (p, p)
  end.

(* Where a waiting spec lands, given the list the scope has resolved so
   far, whose head is what sits immediately before the spec.  Openers
   that never closed are text by then.

   - A plain `Str` takes the spec on its last word.  An empty spec keeps
     the run whole, since cutting it would only produce two plain `Str`s.
   - A run ending in whitespace has no last word, and the spec is
     dropped rather than attached across the gap.
   - Any other node takes it (`*e*{.a}`, `[l](u){}`, `x{.a}{.b}`).
   - Nothing before it drops the spec, and so does a `SoftBreak`.  These
     two move together: the head below a spec is a `SoftBreak` exactly
     when `oout_app` spliced a previous line there, and every `_app`
     lemma rests on attachment not seeing the splice. *)
Definition oattach_list `{PosPolicy}
  (a : attr) (spec : span) (word_start : option spot) (out : inlines)
  : inlines :=
  match out with
  | Node p [] (Str s) :: rest =>
      let '(pre, w) := last_ws_split s in
      if nonempty_str w
      then match a with
           | [] => out
           | _ =>
               let '(pp, wp) := split_text_pos p word_start in
               let out1 := if nonempty_str pre
                           then isnoc (Node pp [] (Str pre)) rest else rest in
               isnoc (add_inline_role RAttrSpec spec (Node wp a (Str w))) out1
           end
      else out
  | Node _ _ SoftBreak :: _ | [] => out
  | n :: rest => add_inline_role RAttrSpec spec
                   (match n with
                    | Node p a' v => Node p (Attr.merge a a') v
                    end) :: rest
  end.

(* A scope's items, settled.  Walking the tail first is what puts the
   already-resolved neighbours in front of each spec.

   The boolean is why the merge is not simply applied to every node: a
   spec that resolves to nothing leaves the run it sat between split in
   two, and only *there* do the neighbours have to be rejoined.  Merging
   unconditionally would be just as correct and would cost every
   equation of the form "a scope closes back to what was emitted into it"
   a `no_adjacent_str` side condition, since resolution would no longer
   be the identity on a settled list.  Carrying one bit keeps it the
   identity definitionally. *)
Fixpoint oresolve_go `{PosPolicy} (l : oitems) : inlines * bool :=
  match l with
  | [] => ([], false)
  | OIn n :: rest =>
      let '(out, m) := oresolve_go rest in
      ((if m then isnoc n out else (n :: out)%list), false)
  | OMark a spec word_start :: rest =>
      let '(out, _) := oresolve_go rest in
      let out' := oattach_list a spec word_start out in
      (out', istarts_str out')
  end.

Definition oresolve `{PosPolicy} (l : oitems) : inlines :=
  fst (oresolve_go l).

(* Nothing waiting: resolution gives the list back, with no side
   condition. *)
Local Lemma oresolve_go_map : forall `{PosPolicy} ns,
  oresolve_go (List.map OIn ns) = (ns, false).
Proof.
  intros P ns. induction ns as [|n ns IH]; [reflexivity|].
  cbn [List.map oresolve_go]. rewrite IH. reflexivity.
Qed.

(* A node that cannot merge is simply put in front. *)
Lemma oresolve_cons_nonplain : forall `{PosPolicy} n l,
  plain_str n = false -> oresolve (OIn n :: l)%list = (n :: oresolve l)%list.
Proof.
  intros P n l H. unfold oresolve; cbn [oresolve_go].
  destruct (oresolve_go l) as [out m]; cbn [fst].
  destruct m; [apply isnoc_nonplain, H|reflexivity].
Qed.

Lemma oresolve_map : forall `{PosPolicy} ns,
  oresolve (List.map OIn ns) = ns.
Proof. intros P ns. unfold oresolve. rewrite oresolve_go_map. reflexivity. Qed.

Local Lemma oresolve_map_rev : forall `{PosPolicy} ns,
  oresolve (List.rev (List.map OIn ns)) = List.rev ns.
Proof.
  intros P ns. rewrite <- List.map_rev. apply oresolve_map.
Qed.

(* Walk out through the open scopes looking for one this closer matches,
   abandoning each scope it passes.  `pend` carries what the abandoned
   scopes contributed, ready to splice into the next level down.

   A matching scope with no content stops the walk: the closer fails to
   close and may become an opener instead.  Abandoning the empty scope
   would dissolve its opener into text and keep searching, which would
   make `___a___` `<em>_</em>a<em>_</em>` rather than three nested spans.

   The test is on the items, not on what they resolve to: a scope holding
   only an attribute spec with nothing to attach to closes, onto
   nothing.  That is the one source of an empty delimiter node. *)
Fixpoint oclose_go `{PosPolicy} (k : dstyle) (m : bool) (pend : oitems)
  (stk : list frame)
  : option (oitems * span * list frame) :=
  match stk with
  | [] => None
  | f :: rest =>
      let content := oapp pend (fr_out f) in
      if dmatch k m f
      then (if nonempty content then Some (content, fr_open f, rest) else None)
      else if fr_barrier f then None
      else oclose_go k m (oapp content [OIn (fr_lit f)]) rest
  end.

(* Whether the search above stopped at a barrier with a scope this closer
   would have matched below it.  An opener barred by a destination makes
   the token text, where no opener at all lets it become one. *)
Fixpoint oclose_barred_go (k : dstyle) (m : bool) (past : bool)
  (stk : list frame) : bool :=
  match stk with
  | [] => false
  | f :: rest =>
      if dmatch k m f then past
      else oclose_barred_go k m (past || fr_barrier f)%bool rest
  end.

Definition oclose_barred (k : dstyle) (m : bool) (o : ostate) : bool :=
  oclose_barred_go k m false (os_stk o).

(* The node runs from the opener the search matched to the end of the
   closing token, which the caller has in hand: the closer is complete
   and its last byte is either the one before the cursor or, for a marked
   close, the `}` in it. *)
Definition oclose `{PosPolicy} (k : dstyle) (m : bool) (stop : spot)
  (o : ostate) : option ostate :=
  match oclose_go k m [] (os_stk o) with
  | None => None
  | Some (content, open, rest) =>
      Some (oemit
              (imk (span_start open) stop
                 (dnode k (List.rev (oresolve content))))
              (OState (os_out o) rest (os_word_start o)))
  end.

(* Whether the search above can match: a matching frame with no barrier
   above it.  It reads only frame kinds, which flushing text into the top
   frame keeps, so a closer that cannot match skips joining the pending
   text for a flush the failed close would discard. *)
Fixpoint oclose_reaches (k : dstyle) (m : bool) (stk : list frame) : bool :=
  match stk with
  | [] => false
  | f :: rest =>
      (dmatch k m f || negb (fr_barrier f) && oclose_reaches k m rest)%bool
  end.

Local Lemma oclose_go_unreached : forall `{PosPolicy} k m stk pend,
  oclose_reaches k m stk = false -> oclose_go k m pend stk = None.
Proof.
  intros P k m stk. induction stk as [|f rest IH]; intros pend H; [reflexivity|].
  cbn [oclose_reaches] in H. apply orb_false_iff in H as [Hd Hr].
  cbn [oclose_go]. rewrite Hd.
  destruct (fr_barrier f); [reflexivity|]. apply IH, Hr.
Qed.

Lemma oclose_guard : forall `{PosPolicy} `{InlineCursor} k m stop fstop t o,
  (if oclose_reaches k m (os_stk o)
   then oclose k m stop (flush_text_to_at fstop t o) else None)
  = oclose k m stop (flush_text_to_at fstop t o).
Proof.
  intros P C k m stop fstop t o.
  destruct (oclose_reaches k m (os_stk o)) eqn:E; [reflexivity|].
  unfold oclose. rewrite oclose_go_unreached; [reflexivity|].
  unfold flush_text_to_at. destruct (nonempty_str t); [|exact E].
  unfold oemit. destruct (os_stk o) as [|f rest]; [exact E|]. exact E.
Qed.

(* The semantic reading of a close: the node is `mk`-wrapped whatever
   span it is handed, so the canonical scan lemmas below are stated
   without one. *)
Definition sclose (k : dstyle) (m : bool) (o : ostate) : option ostate :=
  @oclose semantic_pos k m (Spot 0 0) o.

Local Lemma oclose_semantic : forall k m stop o,
  @oclose semantic_pos k m stop o = sclose k m o.
Proof. reflexivity. Qed.

(* Unfolding a generic definition at the semantic instances leaves the
   [_at] spellings, which [rewrite] and [destruct] do not match against
   the names the equational theory is stated in. *)
Ltac sem_flush :=
  try change (@flush_text_at semantic_pos semantic_inline_cursor)
    with flush_text;
  repeat match goal with
  | |- context [@flush_text_to_at semantic_pos semantic_inline_cursor
                  ?stop ?txt ?o] =>
      change (@flush_text_to_at semantic_pos semantic_inline_cursor
                stop txt o)
        with (flush_text txt o)
  end;
  (* the same for a close, whose node the semantic policy builds without
     reading the span it is handed *)
  repeat match goal with
  | |- context [@oclose semantic_pos ?k ?m ?stop ?o] =>
      change (@oclose semantic_pos k m stop o) with (sclose k m o)
  end.

Lemma oclose_oemit_all_marked :
  forall `{P : PosPolicy} k cm ns open stop base,
    nonempty ns = true ->
    oclose k true stop (oemit_all ns (opush_at k true cm open base))
    = Some (oemit (imk (span_start open) stop (dnode k ns)) base).
Proof.
  intros P k cm ns open stop [out stk] Hne. unfold opush_at.
  rewrite oemit_all_frame.
  unfold oclose. cbn [os_stk os_out oclose_go oapp dmatch fr_kind
    fr_marked fr_out]. rewrite !app_nil_r.
  assert (Hrev : nonempty (List.rev (List.map OIn ns)) = true).
  { destruct ns as [|n rest]; [discriminate|].
    cbn [List.map List.rev]. destruct (List.rev (List.map OIn rest));
      reflexivity. }
  rewrite Hrev. destruct k;
    cbn [dmatch dstyle_eq fr_kind fr_marked andb_true_l].
  all: cbn -[oresolve List.rev List.map];
       rewrite oresolve_map_rev, List.rev_involutive; reflexivity.
Qed.

(* Brackets share the scope stack with delimiters: finding a bracket
   abandons the delimiter frames above it.  Unlike a delimiter close this
   only extracts the label content, since the next byte still decides
   link, reference, span, or literal brackets. *)
Fixpoint bclose_go `{PosPolicy} (pend : oitems) (stk : list frame)
  : option (oitems * bool * span * list frame) :=
  match stk with
  | [] => None
  | f :: rest =>
      let content := oapp pend (fr_out f) in
      match fr_kind f with
      | FKBracket image => Some (content, image, fr_open f, rest)
      (* the destination's own opener is not offered back; see the
         constructor's comment *)
      | FKDest _ => None
      (* `tag_close` has already closed a named bracket at its `]` *)
      | FKTag _ => None
      | FKDelim _ _ =>
          bclose_go (oapp content [OIn (fr_lit f)]) rest
      end
  end.

Definition bclose `{PosPolicy} (o : ostate)
  : option (inlines * bool * span * ostate) :=
  match bclose_go [] (os_stk o) with
  | None => None
  | Some (content, image, open, rest) =>
      Some (List.rev (oresolve content), image, open,
              OState (os_out o) rest (os_word_start o))
  end.

(* A `]` closes a named bracket when that is the innermost bracket,
   abandoning the delimiter frames above it as `bclose_go` does.  Any
   other bracket, or none, leaves the `]` to `IClosed`. *)
Fixpoint tag_close_go `{PosPolicy} (pend : oitems) (stk : list frame)
  : option (oitems * string * span * list frame) :=
  match stk with
  | [] => None
  | f :: rest =>
      let content := oapp pend (fr_out f) in
      match fr_kind f with
      | FKTag name => Some (content, name, fr_open f, rest)
      | FKBracket _ | FKDest _ => None
      | FKDelim _ _ => tag_close_go (oapp content [OIn (fr_lit f)]) rest
      end
  end.

Definition tag_close `{PosPolicy} (o : ostate)
  : option (inlines * string * span * ostate) :=
  match tag_close_go [] (os_stk o) with
  | None => None
  | Some (content, name, open, rest) =>
      Some (List.rev (oresolve content), name, open,
              OState (os_out o) rest (os_word_start o))
  end.

(* Whether a named bracket is innermost is a fact about the frames'
   kinds, so emitting into the current scope cannot change it. *)
Local Lemma tag_close_go_none :
  forall `{PosPolicy} stk pend pend',
    tag_close_go pend stk = None -> tag_close_go pend' stk = None.
Proof.
  intros P stk. induction stk as [|f rest IH]; intros pend pend' H; [reflexivity|].
  cbn [tag_close_go] in H |- *.
  destruct (fr_kind f); try reflexivity; [exact (IH _ _ H)|discriminate H].
Qed.

Lemma tag_close_oemit :
  forall `{PosPolicy} n o, tag_close o = None -> tag_close (oemit n o) = None.
Proof.
  intros P n [out [|f rest] word] H; [reflexivity|].
  unfold tag_close, oemit in *. cbn [os_stk os_out os_word_start] in *.
  cbn [tag_close_go fr_kind fr_out] in H |- *.
  destruct (fr_kind f); try reflexivity.
  - destruct (tag_close_go _ rest) as [[[[? ?] ?] ?]|] eqn:E; [discriminate H|].
    rewrite (tag_close_go_none _ _ _ E). reflexivity.
  - discriminate H.
Qed.

Lemma tag_close_flush :
  forall `{PosPolicy} `{InlineCursor} txt o,
    tag_close o = None -> tag_close (flush_text_at txt o) = None.
Proof.
  intros P C txt o H. unfold flush_text_at.
  destruct (nonempty_str txt); [apply tag_close_oemit|]; exact H.
Qed.

(* Take back a bracket the previous byte pushed.  Only an empty bracket
   frame can be taken back, which is exactly what a `[` leaves and
   nothing else does, so a caller may ask without knowing the stack.  A
   marked close has a delimiter frame on top, so there it is `None`. *)
Definition bunpush (o : ostate) : option (bool * span * ostate) :=
  match os_stk o with
  | Frame (FKBracket image) _ open [] :: rest =>
      Some (image, open, OState (os_out o) rest (os_word_start o))
  | _ => None
  end.

Local Lemma bunpush_opush :
  forall k m o, bunpush (opush k m o) = None.
Proof. intros k m [out stk word]. reflexivity. Qed.

Lemma bunpush_bpush :
  forall image o,
    bunpush (bpush image o) =
      Some (image,
        null_span, o).
Proof. intros image [out stk word]. destruct image; reflexivity. Qed.

Lemma bclose_oemit_all :
  forall ns image base,
    bclose (oemit_all ns (bpush image base)) =
      Some (ns, image,
        null_span, base).
Proof.
  intros ns image [out stk word]. unfold bpush. rewrite oemit_all_frame.
  unfold bclose. cbn [os_stk os_out bclose_go fr_out fr_kind oapp].
  rewrite app_nil_r, oresolve_map_rev, List.rev_involutive.
  destruct image; reflexivity.
Qed.

Lemma tag_close_oemit_all :
  forall ns name start base,
    tag_close (oemit_all ns (tag_push name start base)) =
      Some (ns, name, null_span, base).
Proof.
  intros ns name start [out stk word]. unfold tag_push. rewrite oemit_all_frame.
  unfold tag_close. cbn [os_stk os_out tag_close_go fr_out fr_kind oapp].
  rewrite app_nil_r, oresolve_map_rev, List.rev_involutive.
  reflexivity.
Qed.

(*
Putting a bracket back as text
------------------------------

A bracket's role is decided long after its label is scanned, so the
literal fallback has to reconstruct source from children that are
already classified.  Three operations do it, and between them they keep
the two invariants the text states carry: pending text never sits on a
`Str`, and no two `Str` nodes are adjacent.

None of the three re-reads a byte.  They rewrite state that is already
built, which is the same family as abandoning a scope. *)

(* Undoing a flush.  The text before a `[` was flushed into the current
   scope when the bracket opened; if the bracket decays to text that
   `Str` has to come back out, or the reconstructed text would flush on
   top of it. *)
Definition opop_str (o : ostate) : string * ostate :=
  match os_stk o with
  | [] =>
      match os_out o with
      | OIn (Node _ [] (Str s)) :: rest =>
          (s, OState rest [] (os_word_start o))
      | _ => (EmptyString, o)
      end
  | f :: fs =>
      match fr_out f with
      | OIn (Node _ [] (Str s)) :: rest =>
          (s, OState (os_out o)
                (Frame (fr_kind f) (fr_marked f) (fr_open f) rest :: fs)
                (os_word_start o))
      | _ => (EmptyString, o)
      end
  end.

Section Text.
Context {Buf : Type} {X : TextOps Buf}.

(* Children back into the buffer.  A plain `Str` child is text and joins
   it; anything else is emitted, flushing the buffer first.  So emissions
   alternate `Str` and non-`Str` and the seam obligation holds by
   construction -- this is why the fallback needs no merging emission. *)
Fixpoint bflat `{PosPolicy} `{InlineCursor}
  (kids : inlines) (txt : Buf) (o : ostate) : Buf * ostate :=
  match kids with
  | [] => (txt, o)
  | Node _ [] (Str s) :: rest => bflat rest (tpush txt s) o
  | n :: rest => bflat rest tnil (oemit n (flush_text_at (tval txt) o))
  end.

(* Text that spans a line break.  A `SoftBreak` is a node, so such text
   cannot go back into the buffer whole.  The three buffers that survive
   `ibreak` need it: a destination, and either kind of attribute spec. *)
Fixpoint bsplit_nl `{PosPolicy} `{InlineCursor}
  (s : string) (txt : Buf) (o : ostate) : Buf * ostate :=
  match s with
  | EmptyString => (txt, o)
  | String c rest =>
      if Ascii.eqb c nl_char
      then bsplit_nl rest tnil
             (oemit (imk_here SoftBreak)
               (flush_text_at (tval txt) o))
      else bsplit_nl rest (tpush txt (one c)) o
  end.

(* A closed bracket that turns out to be literal: `[`, the label, `]`. *)
Definition bclosed_lit `{PosPolicy} `{InlineCursor}
  (kids : inlines) (image : bool) (o : ostate)
  : Buf * ostate :=
  let '(pre, o1) := opop_str o in
  let '(txt, o2) := bflat kids (tof (pre ++ bracket_open image)%string) o1 in
  (tpush txt (one rbrack), o2).

(* A span whose spec failed, or that ran out of paragraph: the bracket's
   own literal text, then the `{` and everything the machine read,
   breaks included. *)
Definition bspan_lit `{PosPolicy} `{InlineCursor}
  (kids : inlines) (image : bool) (src : string)
  (o : ostate) : Buf * ostate :=
  let '(txt, o') := bclosed_lit kids image o in
  bsplit_nl src (tpush txt (one lbrace)) o'.

(* The same for a spec with no bracket before it, where the pending text
   the spec would have attached to is the buffer it goes back into. *)
Definition battr_lit `{PosPolicy} `{InlineCursor}
  (src : string) (txt : Buf) (o : ostate) : Buf * ostate :=
  bsplit_nl src (tpush txt (one lbrace)) o.

(* The byte to the left of the one being dispatched, when a construct
   hands back what it ate as text.  Every fallback puts back a fragment
   headed by the construct's own opening byte, so the fragment alone
   decides it: its last byte is the last byte of the text it joins, and
   the pending text before it is never read.  A newline in the fragment
   is where `bsplit_nl` cut it, and a fragment ending in one yields that
   newline, as an empty residue does (`blit_prev_fragment`,
   `blit_prev_bsplit_nl`). *)
Local Definition blit_prev (t : string) : option ascii := str_last t (Some nl_char).

Definition bref_lit `{PosPolicy} `{InlineCursor}
  (kids : inlines) (image : bool) (label : string)
  (o : ostate) : Buf * ostate :=
  let '(txt, o') := bclosed_lit kids image o in
  (tpush txt (one lbrack ++ label)%string, o').

(* A destination drops its line breaks, which are kept as characters
   until it is known to close. *)
Fixpoint drop_nl (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if Ascii.eqb c nl_char then drop_nl rest else String c (drop_nl rest)
  end.

(* Everything still open when the paragraph ends is abandoned. *)
Fixpoint oflatten `{PosPolicy} (pend : oitems) (stk : list frame)
  (bottom : oitems) : oitems :=
  match stk with
  | [] => oapp pend bottom
  | f :: rest =>
      oflatten (oapp (oapp pend (fr_out f)) [OIn (fr_lit f)])
        rest bottom
  end.

(* Append a scope to a reversed accumulator.  Only the last item of the
   accumulated scope can meet the first item of [out]; [osnoc] performs
   that merge in exactly the order used by [oapp]. *)
Definition oapp_rev (acc out : oitems) : oitems :=
  match acc with
  | [] => List.rev out
  | n :: rest => (List.rev (osnoc n out) ++ rest)%list
  end.

Lemma oapp_snoc : forall cur n out,
  oapp (cur ++ [n])%list out = (cur ++ osnoc n out)%list.
Proof.
  induction cur as [|x cur IH]; intros n out; [reflexivity|].
  destruct cur as [|y ys]; cbn [app oapp]; [reflexivity|].
  f_equal. apply IH.
Qed.

Lemma oapp_rev_correct : forall cur out,
  oapp_rev (List.rev cur) out = List.rev (oapp cur out).
Proof.
  intros cur out. induction cur using rev_ind.
  - reflexivity.
  - rewrite List.rev_app_distr. cbn [List.rev oapp_rev].
    rewrite oapp_snoc, List.rev_app_distr. reflexivity.
Qed.

Fixpoint oflatten_rev `{PosPolicy} (acc : oitems) (stk : list frame)
  (bottom : oitems) : oitems :=
  match stk with
  | [] => oapp_rev acc bottom
  | f :: rest =>
      oflatten_rev
        (oapp_rev (oapp_rev acc (fr_out f)) [OIn (fr_lit f)])
        rest bottom
  end.

Lemma oflatten_rev_correct : forall `{P : PosPolicy} pend stk bottom,
  @oflatten_rev P (List.rev pend) stk bottom =
    List.rev (@oflatten P pend stk bottom).
Proof.
  intros P pend stk. revert pend.
  induction stk as [|f stk IH]; intros pend bottom; cbn [oflatten_rev oflatten].
  - apply oapp_rev_correct.
  - rewrite !oapp_rev_correct. apply IH.
Qed.

(* Everything a state holds, as items: the open scopes abandoned into the
   one below, with each opener's spelling put back as text.  Splitting
   this out of `ofinish` is what lets a line boundary name the state it
   leaves without resolving it -- a spec may still be waiting. *)
Definition oitems_of `{PosPolicy} (o : ostate) : oitems :=
  match os_stk o with
  | [] => os_out o
  | stk => List.rev (oflatten_rev [] stk (os_out o))
  end.

Lemma oitems_of_spec : forall `{P : PosPolicy} o,
  @oitems_of P o = @oflatten P [] (os_stk o) (os_out o).
Proof.
  intros P o. unfold oitems_of.
  destruct (os_stk o) as [|f stk] eqn:Hstk;
    [reflexivity|].
  rewrite <- (List.rev_involutive (@oflatten P [] (f :: stk) (os_out o))).
  f_equal. change [] with (List.rev ([] : oitems)).
  apply oflatten_rev_correct.
Qed.

Definition ofinish `{PosPolicy} (o : ostate) : inlines :=
  oresolve (oitems_of o).

(* What a backtick run closes into, decided at the opening run: the `$`
   or `%` prefix has already been read by then. *)
Inductive vkind : Type :=
  | VVerb | VMath (style : math_style)
  | VMaybeDollarMath (prefix : string)
  | VHole.

Definition vnode (vk : vkind) (s : string) : inline :=
  match vk with
  | VVerb | VMaybeDollarMath _ => Verbatim s
  | VMath st => Math st s
  | VHole => Hole s
  end.

(* Only a verbatim may take a raw format: `` $`x`{=html} `` is math
   followed by literal text, and `` %`x`{=html} `` a hole. *)
Definition vkind_verb (vk : vkind) : bool :=
  match vk with
  | VVerb | VMaybeDollarMath _ => true
  | VMath _ | VHole => false
  end.

(* Every state below that carries pending text carries `prev`: the last
   byte of source read so far, `None` at the start of a paragraph or of a
   line.

   It is not the last byte of `txt`.  An unmatched smart quote, an
   ellipsis and a dash put bytes in the buffer that were never in the
   source, and the delimiter rules read the source: `'` after `a''` opens
   where it would not after a curly quote
   (`decay_does_not_hide_the_source_byte`).  Each construct that rewrites
   the buffer names the byte it consumed; the states that hold an
   undecided prefix (`IBrace`, `IDollar`, `IPeriod`, `IDash`, `IBang`)
   carry the byte from before the prefix. *)
Inductive iscan_g : Type :=
  (* accumulating literal text; `esc` is a pending backslash *)
  | IText (esc : bool) (txt : Buf) (prev : option ascii) (o : ostate)
  (* a backslash followed by a run of spaces and tabs, whose role the
     next byte decides: the end of the line makes the whole run a hard
     break, and anything else makes the first byte a non-breaking space
     (or, if it was a tab, a literal backslash).  `ws` is that run, never
     empty.  It has to be a state for the same reason `IDollar` does --
     the decision needs a byte the buffer has not seen yet -- and the run
     is kept rather than counted because only its *first* byte decides,
     while the rest is ordinary text. *)
  | IEscWs (ws : Buf) (txt : Buf) (prev : option ascii) (o : ostate)
  (* a `{` whose role the next byte decides: open marker, or text *)
  | IBrace (txt : Buf) (prev : option ascii) (o : ostate)
  (* a delimiter being spelled; `before` is the byte to its left, which
     decides whether it may close and, for a row whose bare opener needs
     a word boundary, whether it may open.  Kept as the byte rather than a
     predicate of it, because two rows can ask two different questions of
     it.  `extra` counts the row's characters that have arrived after the
     first, so the token so far is `S extra` of them: short of `dwidth` it
     is still being spelled, and at `dwidth` it is complete and the next
     byte decides its role.  Counting from the second character keeps the
     state from holding an empty token.

     `marked` says the token is the one after a `{`.  Its role needs no
     byte after it (a marked token can open and cannot close), but the
     side its decay would take does, because a `}` right after it flips
     the row's default.  So a complete marked token waits here too, and
     the byte that arrives pushes the scope and is then dispatched into
     it; only `fr_src` learns which side it chose.  What such a state
     decays to keeps the `{`. *)
  | IDelim (k : dstyle) (extra : nat) (txt : Buf) (before : option ascii)
           (marked : bool) (o : ostate)
  (* counting an opening backtick run.  `vk` is what the run will close
     into: a `$` or `$$` immediately before it makes the span math, and a
     `%` with holes on makes it a hole, so both are modes of verbatim
     rather than constructs of their own. *)
  | IOpen (n : nat) (vk : vkind) (o : ostate)
  (* inside a width-`n` verbatim, with `run` unresolved trailing ticks *)
  | IVerb (n run : nat) (txt : Buf) (vk : vkind) (o : ostate)
  (* one or two dollars whose role the next byte decides: a backtick run
     makes them a math prefix, anything else makes them text.  A state
     rather than a look-back into the buffer, because an *escaped* `$`
     must not count and the buffer cannot tell the two apart -- the same
     reason `!` has `IBang`. *)
  | IDollar (two : bool) (txt : Buf) (prev : option ascii) (o : ostate)
  (* A dollar-delimited math candidate and the ordinary reading of the
     same bytes.  The latter is selected if no valid closer arrives. *)
  | IDollarMath (two escaped : bool) (src txt : Buf)
                (last : option ascii) (sh : iscan_g) (o : ostate)
  (* One possible closing dollar, awaiting the next byte. *)
  | IDollarMathClose (two : bool) (src txt : Buf)
                     (last : option ascii) (sh : iscan_g) (o : ostate)
  (* one or two periods whose role the next byte decides: a third makes
     the three an ellipsis, anything else makes them text.  `IDollar`'s
     shape exactly, and for `IDollar`'s reason -- an escaped `\.` must not
     count towards the run, and the text buffer cannot tell it from a
     bare one. *)
  | IPeriod (two : bool) (txt : Buf) (prev : option ascii) (o : ostate)
  (* a run of `n` hyphens whose cut into dashes the next byte decides.
     Unlike `IPeriod` the run is unbounded, and unlike every other run in
     this scanner it is not a delimiter token: `dashes` cuts it by
     arithmetic and the result is text.  The one byte that is not just the
     run's end is `}`, which takes the last hyphen back for a delete
     closer. *)
  | IDash (n : nat) (txt : Buf) (prev : option ascii) (o : ostate)
  (* a `!` whose role the next byte decides: `[` opens an image, and
     anything else makes it text.  An *escaped* `!` never reaches here,
     which is what keeps `\![a](u)` a link. *)
  | IBang (txt : Buf) (prev : option ascii) (o : ostate)
  (* a `]` whose role the next byte decides: `(` enters a destination,
     `[` a reference, `{` a span, and anything else leaves the `]` as
     text with the bracket scope still open, so a later `]` can close it:
     `[u]b](c)` is a link labelled `u]b`.  Nothing is closed here: `txt`
     is the text pending when the `]` arrived, still unflushed, and `o` is
     the scope stack untouched. *)
  | IClosed (txt : Buf) (o : ostate)
  (* a closed bracket followed by `{`: a span, if the spec parses.  The
     spec is read with the machine block attributes use, a byte at a
     time; `src` is what it has eaten, kept so the whole region can be put
     back as text when the machine fails.  `image` is carried only for
     that reconstruction: a span ignores it, so `![x]{.a}` is a `!`
     followed by a span. *)
  | ISpan (kids : inlines) (image : bool) (open : span)
          (p : aparser) (src : Buf)
          (o : ostate)
  (* an attribute spec, which attaches to whatever precedes it.  `txt` is
     the text pending when the `{` arrived and, on success, what the spec
     attaches to.  `sh` is the ordinary reading of the same source,
     advanced with attribute recognition off and selected if the
     candidate never closes. *)
  | IAttr (p : aparser) (src : Buf) (txt : Buf) (prev : option ascii)
          (sh : iscan_g) (o : ostate)
  (* inside the second bracket of `[text][label]`.  The label is source
     text, not inline content.  `esc` is a pending backslash, which
     protects a `]` without being decoded, as in a footnote label:
     `[a][b\]c]` labels `b\]c`. *)
  | IReference (kids : inlines) (image : bool) (open : span)
          (esc : bool) (label : Buf) (o : ostate)
  (* inside a `[^`.  The label is raw source, not inline content: nothing
     inside the brackets is classified.  `esc` is a pending backslash,
     which protects a `]` without being decoded: `[^a\]b]` labels `a\]b`.
     `image` is what the bracket this took back was opened with, kept
     only to spell the literal fallback. *)
  | INote (esc image : bool) (label : Buf) (open : span) (o : ostate)
  (* inside a `[[`, recognised at the second `[` the way `[^` is at the
     `^`.  The region is source kept with its escapes: `esc` is a pending
     backslash and `rb` a pending `]`, the first half of a possible
     closer, neither yet in `region`.  `image` is what the bracket this
     took back was opened with: the embed bit on success, the `!` of the
     literal fallback otherwise. *)
  | IWiki (esc rb image : bool) (region : Buf) (open : span) (o : ostate)
  (* inside a `](`.  `depth` counts unclosed inner parentheses, `dst`
     accumulates the destination with its escapes decoded, and `esc` is a
     pending backslash, as in text mode.  A destination survives a line
     break.

     Two readings of the same bytes run here.  `kids`, `dst` and `o` are
     the destination reading, used by the balanced `)` and nothing else.
     `sh` is the ordinary reading (the same scanner, fed the same bytes,
     inside the `FKDest` scope this state opened), which the end of the
     paragraph keeps, since the region turns literal only at the close.
     Neither replays the other: both advance on each byte, and the byte
     that ends the state picks one. *)
  | IDest (kids : inlines) (image : bool) (open : span)
          (esc : bool) (depth : nat) (dst : Buf)
          (sh : iscan_g) (o : ostate)
  (* inside a `<`, holding the region read so far.  The region is raw
     source, so a backtick or a delimiter inside a successful autolink is
     content (`<a:b`c>` links to ``a:b`c``).

     `txt` is the text pending when the `<` arrived, kept because a failed
     candidate is put back as literal text.  djot.js instead scans a failed
     candidate as ordinary inline content; an ordinary-reading shadow, as
     `IDest` carries, would do that without replay
     (`.project/no-backtracking.md`). *)
  | IAuto (src : Buf) (txt : Buf) (o : ostate)
  (* A colon and the symbol alias read so far.  The ordinary-inline
     shadow advances over the same bytes; a failed or unfinished
     candidate selects it without replaying source. *)
  | ISymbol (alias : Buf) (txt : Buf) (sh : iscan_g) (o : ostate)
  (* a verbatim span that closed onto a `{`, holding its content and the
     spec source read since.  The node is not emitted yet: whether it is
     `Verbatim` or `RawInline` is what the spec decides.  Only a verbatim
     reaches here, never math. *)
  | IRaw (spec : Buf) (txt : string) (o : ostate)
  (* a `%` whose role the next byte decides: a backtick run makes it a
     hole's prefix, and anything else makes it text.  `IDollar`'s shape,
     for `IDollar`'s reason. *)
  | IPercent (txt : Buf) (prev : option ascii) (o : ostate).
Local Notation iscan := iscan_g.

(* The one position in which the table does not get the byte: right
   inside a bracket that has just opened, where a `^` marks a footnote
   rather than a superscript. *)
Definition note_pos (txt : Buf) (prev : option ascii) : bool :=
  (negb (tnonempty txt)
   && match prev with Some p => Ascii.eqb p lbrack | None => false end)%bool.

(* One byte in text mode.  The delimiter arm is a table lookup.  `prev`
   is the source byte to the left of `c`, not the last byte of `txt` (see
   `iscan`). *)
Definition ilead `{PosPolicy} `{InlineCursor}
  (c : ascii) (txt : Buf) (prev : option ascii) (o : ostate)
  : iscan :=
  if is_bslash c then IText true txt (Some c) o
  else if is_tick c then IOpen 1 VVerb (flush_text_at (tval txt) o)
  else if Ascii.eqb c dollar then IDollar false txt prev o
  else if Ascii.eqb c period then IPeriod false txt prev o
  (* The hyphen, like the footnote marker, is claimed by position rather
     than by the table: a run of them is smart dashes whatever row the
     table spells with `-`, and the delete row is reached from `{` on the
     left (through `IBrace`) or from `}` on the right (through `IDash`).
     `needs_escape` claims it unconditionally for exactly this reason. *)
  else if Ascii.eqb c hyphen then IDash 1 txt prev o
  else if Ascii.eqb c lbrace then IBrace txt prev o
  (* A `!` waits for the next byte.  A `[` opens a scope on the stack the
     delimiters use, so their relative order is kept and the label needs
     no second parser.  A `]` decides nothing on its own: it hands the
     pending text to `IClosed`, which closes the innermost bracket scope
     only if the byte after it makes a construct. *)
  else if Ascii.eqb c bang then IBang txt prev o
  (* A `<` opens an autolink candidate, which is neither a scope nor a
     lookahead: it accumulates the region and decides at the `>`.  The
     pending text stays pending, since a candidate that fails hands it
     back with the `<` on the end. *)
  else if Ascii.eqb c lt then IAuto tnil txt o
  else if Ascii.eqb c ":"%char
       then ISymbol tnil txt
              (IText false (tpush txt (one c)) (Some c)
                (remember_word_start c o)) o
  (* A `[` right inside a bracket that has just opened is the second
     bracket of a wikilink.  The same guard as the footnote marker's
     below, with `[` in place of `^`. *)
  else if Ascii.eqb c lbrack
  then match (if (note_pos txt prev && wikilinks_enabled)%bool
              then bunpush o else None) with
       | Some (image, open, o') => IWiki false false image tnil open o'
       | None =>
           IText false tnil (Some lbrack)
             (bpush false (flush_text_at (tval txt) o))
       end
  (* With names on, a `]` that closes a named bracket builds its span
     here; see `tag_close`. *)
  else if Ascii.eqb c rbrack
  then match (if tags_enabled then tag_close (flush_text_at (tval txt) o)
              else None) with
       | Some (kids, name, open, o') =>
           IText false tnil (Some rbrack)
             (oemit (imk (span_start open) cursor_stop (Span name kids)) o')
       | None => IClosed txt o
       end
  (* A `^` right inside a bracket that has just opened marks a footnote:
     the bracket is taken back and the label read as source.  Written as a
     guard on `bunpush`, so a `^` anywhere else falls through to the
     table, where it is the superscript row. *)
  else match (if (Ascii.eqb c hat && note_pos txt prev && notes_enabled)%bool
              then bunpush o else None) with
       | Some (image, open, o') => INote false image tnil open o'
       | None =>
           match dstyle_of c with
           | Some k => IDelim k 0 txt prev false o
           (* With holes on, a `%` waits for the byte after it.  Asked
              after the table, so a table that spells a row with `%`
              keeps it, and has no holes. *)
           | None =>
               if (holes_enabled && Ascii.eqb c percent)%bool
               then IPercent txt prev o
               else IText false (tpush txt (one c)) (Some c)
                      (remember_word_start c o)
           end
       end.

(* The ordinary reading of a `](`, as a state.  The bracket's opener is
   pushed back as `FKDest`, so a delimiter closer cannot reach past it,
   and the label goes into it as text through `bflat`, which keeps a
   classified child classified and merges the `Str` seam by construction.
   The two bytes that opened the destination are the head of the buffer,
   so a spec that attaches here attaches to `[u](a` whole.  `fr_src`
   supplies the `[` at the flatten. *)
Definition idest_open `{PosPolicy} `{InlineCursor}
  (kids : inlines) (image : bool) (open : span)
  (o : ostate) : iscan :=
  let '(txt, o') := bflat kids tnil (dpush image open o) in
  IText false (tpush txt (one rbrack ++ one lparen)) (Some lparen) o'.

Definition null {A} (l : list A) : bool :=
  match l with [] => true | _ => false end.

(* The ellipsis and the two dashes, as UTF-8.  Three bytes each, like the
   curly quotes, and nothing downstream looks inside. *)
Definition ellipsis : string :=
  String "226"%char (String "128"%char (String "166"%char EmptyString)).
Definition endash : string :=
  String "226"%char (String "128"%char (String "147"%char EmptyString)).
Definition emdash : string :=
  String "226"%char (String "128"%char (String "148"%char EmptyString)).

Local Definition periods (two : bool) : string :=
  if two then String period (one period) else one period.

Local Definition typography_ellipsis : string :=
  if smart_typography then ellipsis else chars period 3.

Local Fixpoint srep (s : string) (n : nat) : string :=
  match n with O => EmptyString | S m => (s ++ srep s m)%string end.

(* How a run of `n` hyphens is cut: a run divisible by three is all em
   dashes and an even one all en dashes; otherwise em dashes greedily,
   finishing with one or two en dashes.  A lone hyphen is literal.

   Spelled as the arithmetic rather than as djot.js's loop, whose
   recursive call is duplicated across four branches: such a recursion
   has no normal form at an unknown `n`, so every `Compute` would pass
   while every general lemma stayed unprovable
   (`.project/project-engineering-lessons.md`). *)
Local Definition dash_counts (n : nat) : nat * nat * nat :=
  if Nat.eqb (Nat.modulo n 3) 0 then (Nat.div n 3, 0, 0)
  else if Nat.eqb (Nat.modulo n 2) 0 then (0, Nat.div n 2, 0)
  else if Nat.eqb n 1 then (0, 0, 1)
  else if Nat.eqb (Nat.modulo n 6) 5 then (Nat.div (n - 2) 3, 1, 0)
  else (Nat.div (n - 4) 3, 2, 0).

Definition dashes (n : nat) : string :=
  let '(em, en, lit) := dash_counts n in
  (srep emdash em ++ srep endash en ++ chars hyphen lit)%string.

Definition typography_dashes (n : nat) : string :=
  if smart_typography then dashes n else chars hyphen n.

(* The counts pinned on the runs that decide the arithmetic: the two
   homogeneous cases, the two remainders, and the lone hyphen. *)
Example dashes_1 : dashes 1 = one hyphen. Proof. reflexivity. Qed.
Example dashes_2 : dashes 2 = endash. Proof. reflexivity. Qed.
Example dashes_3 : dashes 3 = emdash. Proof. reflexivity. Qed.
Example dashes_4 : dashes 4 = (endash ++ endash)%string. Proof. reflexivity. Qed.
Example dashes_5 : dashes 5 = (emdash ++ endash)%string. Proof. reflexivity. Qed.
Example dashes_7 :
  dashes 7 = (emdash ++ endash ++ endash)%string. Proof. reflexivity. Qed.
Example dashes_13 :
  dashes 13 = (emdash ++ emdash ++ emdash ++ endash ++ endash)%string.
Proof. reflexivity. Qed.

(** The syntax reference's rule, for every run: "Longer sequences of
    hyphens are divided into em-dashes, en-dashes, and hyphens;
    uniformly, if possible, and preferring em-dashes, when uniformity can
    be achieved either way."  Divided: the pieces' widths add up to the
    run.  Uniformly, preferring em dashes: all em dashes when three
    divides the run, else all en dashes when two does.  A hyphen is left
    only when the run is one hyphen long. *)
Theorem dashes_divide :
  forall n, 1 <= n ->
  exists em en lit,
    dashes n = (srep emdash em ++ srep endash en ++ chars hyphen lit)%string /\
    3 * em + 2 * en + lit = n /\
    (lit = 0 \/ n = 1) /\
    (Nat.modulo n 3 = 0 -> en = 0 /\ lit = 0) /\
    (Nat.modulo n 3 <> 0 -> Nat.modulo n 2 = 0 -> em = 0 /\ lit = 0).
Proof.
  intros n Hn. unfold dashes, dash_counts.
  pose proof (Nat.div_mod_eq n 3) as D3.
  pose proof (Nat.mod_upper_bound n 3 ltac:(lia)) as M3.
  pose proof (Nat.div_mod_eq n 2) as D2.
  pose proof (Nat.mod_upper_bound n 2 ltac:(lia)) as M2.
  pose proof (Nat.div_mod_eq n 6) as D6.
  pose proof (Nat.mod_upper_bound n 6 ltac:(lia)) as M6.
  destruct (Nat.eqb (n mod 3) 0) eqn:E3;
    [apply Nat.eqb_eq in E3|apply Nat.eqb_neq in E3].
  { eexists _, _, _. split; [reflexivity|]. lia. }
  destruct (Nat.eqb (n mod 2) 0) eqn:E2;
    [apply Nat.eqb_eq in E2|apply Nat.eqb_neq in E2].
  { eexists _, _, _. split; [reflexivity|]. lia. }
  destruct (Nat.eqb n 1) eqn:E1; [apply Nat.eqb_eq in E1|apply Nat.eqb_neq in E1].
  { eexists _, _, _. split; [reflexivity|]. lia. }
  destruct (Nat.eqb (n mod 6) 5) eqn:E6;
    [apply Nat.eqb_eq in E6|apply Nat.eqb_neq in E6].
  - pose proof (Nat.div_mod_eq (n - 2) 3) as D.
    pose proof (Nat.mod_upper_bound (n - 2) 3 ltac:(lia)) as M.
    eexists _, _, _. split; [reflexivity|]. lia.
  - pose proof (Nat.div_mod_eq (n - 4) 3) as D.
    pose proof (Nat.mod_upper_bound (n - 4) 3 ltac:(lia)) as M.
    eexists _, _, _. split; [reflexivity|]. lia.
Qed.

(* The dollars a pending prefix is holding, when they turn out to be
   text. *)
Local Definition dollars (two : bool) : string :=
  if two then (one dollar ++ one dollar)%string else one dollar.

(* A candidate that failed is its own source: the `<`, what it ate, and
   whatever pended before it.  One string rather than a state, because
   the byte that killed it still has to be dispatched. *)
Local Definition auto_lit (src : string) (txt : Buf) : Buf :=
  tpush txt (String lt src).

(* A slice boundary in the ordinary reading of a candidate's region.
   djot.js re-feeds a failed region cut into slices at every special
   byte, so a matcher bounded by the slice cannot see past the byte it
   starts on: a run of `-` or `.` never reaches the length that would
   make it a dash or an ellipsis, a `{` never marks the delimiter after
   it, a `]` never finds its destination, an autolink's region never
   reaches its `>`, and a `\` escapes nothing.  (`IEscWs` cannot arise
   here: the escape it continues is settled at the boundary before it.)
   What crosses a boundary lives in the parser rather than in the slice:
   an open delimiter, a verbatim, a math prefix that peeks at the byte
   after it.  Hence no `IDelim`, `IOpen`, `IVerb`, `IDollar` or
   `IPercent` arm: a hole's prefix peeks as a math prefix does.
   `IBang` is not here either: `!` is not a special byte, so no slice
   ends on it. *)
Fixpoint islice_end (st : iscan) : iscan :=
  match st with
  | IText true txt _ o => IText false (tpush txt (one bslash)) (Some bslash) o
  | IBrace txt _ o => IText false (tpush txt (one lbrace)) (Some lbrace) o
  | IPeriod two txt _ o =>
      IText false (tpush txt (periods two)) (Some period) o
  | IDash n txt _ o =>
      IText false (tpush txt (typography_dashes n)) (Some hyphen) o
  | IClosed txt o => IText false (tpush txt (one rbrack)) (Some rbrack) o
  | IAuto src txt o =>
      IText false (auto_lit (tval src) txt) (blit_prev (String lt (tval src))) o
  | ISymbol _ _ sh _ => islice_end sh
  | _ => st
  end.

(* Where a finished spec goes: into the scope, as a marker, with the
   pending text flushed in front of it so that the run it will attach to
   is the item immediately below.  `oresolve` settles it (see
   `oattach_list`). *)
Definition iattr_mark `{PosPolicy} `{InlineCursor}
  (src : Buf) (a : attr) (txt : Buf) (o : ostate) : iscan :=
  let spec_start := spot_before cursor_start (String lbrace (tval src)) in
  let spec := pspan (SrcSpan spec_start cursor_stop) in
  IText false tnil (Some rbrace)
    (omark a spec (flush_text_to_at spec_start (tval txt) o)).

(* One byte of an inline attribute spec, read with the machine block
   attributes use.  `sh` has already consumed the same byte as ordinary
   inline input.  Failure selects it; success discards it; otherwise both
   readings remain live -- and the one kept is stored at a slice
   boundary, since the byte it has just read is where its slice ends. *)
Definition iattr_feed `{PosPolicy} `{InlineCursor}
  (c : ascii) (p : aparser) (src txt : Buf)
  (prev : option ascii) (sh : iscan_g) (o : ostate) : iscan :=
  let p' := astep p c in
  if ap_failed p'
  then sh
  else if ap_done p'
  then iattr_mark src (ap_attrs p') txt o
  else IAttr p' (tpush src (one c)) txt prev (islice_end sh) o.

(* A marked open with `S extra` characters of its token in hand.  Its
   role is not in doubt (a marked delimiter can open and cannot close),
   but its spelling when abandoned is, because a `}` right after it flips
   the row's decay side.  So the push waits for one byte whatever the
   width, in `istep` or `iresolve`.  `before` is `None` throughout: the
   branch that would read it is never reached. *)
Definition idelim_marked (k : dstyle) (extra : nat) (txt : Buf)
  (o : ostate) : iscan := IDelim k extra txt None true o.

(* The push itself, once the byte after a completed marked opener is
   known (or known not to exist). *)
Definition oopen_marked `{PosPolicy} `{InlineCursor}
  (k : dstyle) (cm : bool) (txt : Buf)
  (o : ostate) : ostate :=
  let open := dtoken_span k true in
  opush_at k true cm open (flush_text_to_at (span_start open) (tval txt) o).

Definition idelim_open_marked `{PosPolicy} `{InlineCursor}
  (k : dstyle) (cm : bool) (txt : Buf)
  (o : ostate) : iscan :=
  IText false tnil (Some (dchar k)) (oopen_marked k cm txt o).

(* What a token that never finished decays to: the row's characters
   received so far, with the `{` of a marked open back in front of
   them. *)
Local Definition idelim_run (k : dstyle) (extra : nat) (marked : bool) : string :=
  ((if marked then one lbrace else EmptyString)
     ++ chars (dchar k) (S extra))%string.

Local Lemma idelim_run_nonempty :
  forall k extra marked, nonempty_str (idelim_run k extra marked) = true.
Proof. intros k extra []; reflexivity. Qed.

(* Resolving a `{`: an open marker if a delimiter follows, an attribute
   candidate if that capability is enabled, and ordinary text otherwise. *)
Definition ibrace_step_at `{PosPolicy} `{InlineCursor}
  (attrs_enabled : bool) (c : ascii) (txt : Buf)
  (prev : option ascii) (o : ostate) : iscan :=
  match dstyle_of c with
  | Some k => idelim_marked k 0 txt o
  | None =>
      if attrs_enabled
      then iattr_feed c ap_init tnil txt prev
             (ilead c (tpush txt (one lbrace)) (Some lbrace) o) o
      (* The spec's own immediate-failure path, taken before the first
         byte is read: `{` goes back into the text and this byte is
         dispatched afresh. *)
      else let '(t, o') := battr_lit EmptyString txt o in
           ilead c t (blit_prev (one lbrace)) o'
  end.

Definition ibrace_step `{PosPolicy} `{InlineCursor}
  (c : ascii) (txt : Buf) (prev : option ascii)
  (o : ostate) : iscan :=
  ibrace_step_at inline_attrs_enabled c txt prev o.

(* A span ignores the image marker: `![x]{.a}` is a literal `!` followed
   by a span.  The `!` was never flushed -- the bracket frame records it
   and `fr_src` puts it back on the literal path -- so the span path
   has to emit it here, and it merges with any `Str` already at the tip
   the same way, since `flush_text` alone would leave two adjacent. *)
Definition ospan_bang `{PosPolicy} `{InlineCursor}
  (image : bool) (o : ostate) : ostate :=
  if image
  then let '(pre, o1) := opop_str o in
       flush_text_at (pre ++ one bang)%string o1
  else o.

(* One byte into an open span's spec.  `ADone` arrives on the `}`, so the
   node is built here with no byte left over.  On `AFail` the region up to
   but not including the failing byte becomes text and that byte is
   dispatched afresh, so `[s]{bad*x*y` is `[s]{bad`, a strong `x`, and
   `y`. *)
Definition ispan_feed `{PosPolicy} `{InlineCursor}
  (c : ascii) (kids : inlines) (image : bool) (open : span)
  (p : aparser) (src : Buf) (o : ostate) : iscan :=
  let p' := astep p c in
  if ap_failed p'
  then let '(txt, o') := bspan_lit kids image (tval src) o in
       ilead c txt (blit_prev (String lbrace (tval src))) o'
  else if ap_done p'
  then let spec_start := spot_before cursor_start (String lbrace (tval src)) in
       let spec := SrcSpan spec_start cursor_stop in
       IText false tnil (Some rbrace)
         (oemit
           (add_inline_role RAttrSpec spec
             (Node (mkpos (inline_prov (span_start open) spec_start))
               (ap_attrs p') (Span EmptyString kids)))
           (ospan_bang image o))
  else ISpan kids image open p' (tpush src (one c)) o.

(* One byte of a footnote label.  The `]` is the only byte with a role,
   and a backslash defers it once without being decoded, since the label
   is source: `[^a\]b]` keeps the backslash. *)
Definition inote_step `{PosPolicy} `{InlineCursor}
  (c : ascii) (esc image : bool) (label : Buf) (open : span)
  (o : ostate) : iscan :=
  if esc then INote false image (tpush label (one bslash ++ one c)) open o
  else if is_bslash c then INote true image label open o
  else if Ascii.eqb c rbrack
  then IText false tnil (Some rbrack)
         (oemit (imk (span_start open) cursor_stop
                    (FootnoteReference (normalize_label (tval label))))
            (ospan_bang image o))
  else INote false image (tpush label (one c)) open o.

(* One byte of an autolink candidate.  Three bytes end it: the `>` that
   may resolve it, and the whitespace or second `<` that the region may
   not contain.  Everything else is region, raw -- no escape is decoded
   and no construct is dispatched, which is what makes the region of a
   *successful* autolink literal.

   The `>` of a failed candidate is dispatched rather than appended, so
   that this arm has one exit for every byte that is not region.

   `auto_body_ok` asks more than the `>` has to: the three exclusions
   are invariants of the mode, since a byte that breaks one leaves it.
   It is spelled in full so that the test *is* `ci_ok`'s, which is what
   makes the scan inversion a rewrite rather than an argument. *)
Definition iauto_step `{PosPolicy} `{InlineCursor}
  (c : ascii) (src txt : Buf) (o : ostate) : iscan :=
  if (Ascii.eqb c gt && auto_body_ok (tval src) && auto_kind_ok (tval src))%bool
  then let start := spot_before cursor_start (String lt (tval src)) in
       IText false tnil (Some gt)
         (oemit (imk start cursor_stop (auto_node (tval src)))
           (flush_text_to_at start (tval txt) o))
  else if (Ascii.eqb c gt || is_ws c || Ascii.eqb c lt)%bool
  then ilead c (auto_lit (tval src) txt) (blit_prev (String lt (tval src))) o
  else IAuto (tpush src (one c)) txt o.

Definition isymbol_step `{PosPolicy} `{InlineCursor}
  (c : ascii) (alias txt : Buf)
  (o : ostate) (sh' : iscan) : iscan :=
  if symbol_char c then ISymbol (tpush alias (one c)) txt sh' o
  else if (Ascii.eqb c ":"%char && tnonempty alias)%bool
  then let start := spot_before cursor_start (one ":"%char ++ tval alias)%string in
       IText false tnil (Some c)
         (oemit (imk start cursor_stop (Symbol (tval alias)))
           (flush_text_to_at start (tval txt) o))
  (* the alias is a name, and the `[` opens its bracket *)
  else if (Ascii.eqb c lbrack && tnonempty alias && tags_enabled
           && tag_may_follow (tval txt))%bool
  then let start := spot_before cursor_start (one ":"%char ++ tval alias)%string in
       IText false tnil (Some c)
         (tag_push (tval alias) start (flush_text_to_at start (tval txt) o))
  else sh'.

(* One byte of a raw-format spec.  The `}` decides it; the pattern's
   excluded bytes end it; anything else is spec.

   A failed spec is put back with the verbatim it followed, and there the
   two cases differ.  With nothing read yet the `{` had no `=` after it,
   so it takes the ordinary attribute path.  With an `=` read the region
   cannot parse as attributes, so it is text. *)
Local Definition iraw_lit (spec : string) : string :=
  (String lbrace spec)%string.

Definition iraw_step_at `{PosPolicy} `{InlineCursor}
  (attrs_enabled : bool) (c : ascii) (spec : Buf) (txt : string)
  (o : ostate) : iscan :=
  if (Ascii.eqb c rbrace && raw_spec_ok (tval spec))%bool
  then if raw_inline_enabled
       then IText false tnil (Some rbrace)
              (oemit (imk (text_start o) cursor_stop
                        (RawInline (raw_format (tval spec)) txt)) o)
       else ilead c (tof (iraw_lit (tval spec))) (blit_prev (iraw_lit (tval spec)))
              (oemit (imk (text_start o)
                         (spot_before cursor_start (String lbrace (tval spec)))
                         (Verbatim txt)) o)
  else if (if tnonempty spec then (Ascii.eqb c rbrace || raw_stop c)%bool
           else negb (Ascii.eqb c eqchar))
  then let closed :=
         oemit (imk (text_start o)
                  (spot_before cursor_start (String lbrace (tval spec)))
                  (Verbatim txt)) o in
       if tnonempty spec
       then ilead c (tof (iraw_lit (tval spec))) (blit_prev (iraw_lit (tval spec))) closed
       else ibrace_step_at attrs_enabled c tnil (Some tick) closed
  else IRaw (tpush spec (one c)) txt o.

Local Definition iraw_step `{PosPolicy} `{InlineCursor}
  (c : ascii) (spec : Buf) (txt : string) (o : ostate) : iscan :=
  iraw_step_at inline_attrs_enabled c spec txt o.

(* A label that never closed is its own source: the bracket it took back,
   the marker, and what it had eaten.  `opop_str` reabsorbs the `Str`
   that the bracket's own `flush_text` emitted, so the reconstruction is
   one run and `no_adjacent_str` survives -- the move `bclosed_lit`
   makes, for the same reason. *)
Definition bnote_lit `{PosPolicy} `{InlineCursor}
  (esc image : bool) (label : string) (o : ostate)
  : string * ostate :=
  let '(pre, o1) := opop_str o in
  ((pre ++ bracket_open image ++ one hat ++ label
       ++ (if esc then one bslash else EmptyString))%string, o1).

(* A wikilink region split at its first unescaped `|`: the target, and
   the alias if there is a bar.  A backslash and the byte after it stay
   together and are never split. *)
Fixpoint wiki_split (s : string) : string * option string :=
  match s with
  | EmptyString => (EmptyString, None)
  | String c rest =>
      if is_bslash c then
        match rest with
        | EmptyString => (one c, None)
        | String c' rest' =>
            let '(t, al) := wiki_split rest' in (String c (String c' t), al)
        end
      else if Ascii.eqb c vbar then (EmptyString, Some rest)
      else let '(t, al) := wiki_split rest in (String c t, al)
  end.

(* A wikilink candidate's own source: both brackets, the region, and the
   pending `]` and backslash.  The literal fallback, with whatever text
   pended before the first bracket, as `bnote_lit` rebuilds a label. *)
Local Definition wiki_lit (esc rb image : bool) (region : string) : string :=
  (bracket_open image ++ one lbrack ++ region
     ++ (if rb then one rbrack else EmptyString)
     ++ (if esc then one bslash else EmptyString))%string.

Definition bwiki_lit (esc rb image : bool) (region : string) (o : ostate)
  : string * ostate :=
  let '(pre, o1) := opop_str o in ((pre ++ wiki_lit esc rb image region)%string, o1).

(* The `]]` has arrived.  An empty target is not a wikilink: the whole
   candidate is text, closer included, and pends as text so that no later
   `]` can close a scope with it. *)
Definition iwiki_close `{PosPolicy} `{InlineCursor}
  (image : bool) (region : Buf) (open : span) (o : ostate) : iscan :=
  match wiki_split (tval region) with
  | (EmptyString, _) =>
      let '(txt, o') := bwiki_lit false true image (tval region) o in
      IText false (tpush (tof txt) (one rbrack)) (Some rbrack) o'
  | (t, al) =>
      IText false tnil (Some rbrack)
        (oemit (imk (span_start open) cursor_stop (Ext_wikilink image t al)) o)
  end.

(* One byte of a wikilink region.  A pending `]` becomes content unless
   this byte completes the closer; a backslash protects the next byte
   without being decoded. *)
Definition iwiki_step `{PosPolicy} `{InlineCursor}
  (c : ascii) (esc rb image : bool) (region : Buf) (open : span)
  (o : ostate) : iscan :=
  if esc then IWiki false false image (tpush region (one bslash ++ one c)) open o
  else if (rb && Ascii.eqb c rbrack)%bool then iwiki_close image region open o
  else
    let region' := if rb then tpush region (one rbrack) else region in
    if is_bslash c then IWiki true false image region' open o
    else if Ascii.eqb c rbrack then IWiki false true image region' open o
    else IWiki false false image (tpush region' (one c)) open o.

(* Resolving a `!`: an image opener if a `[` follows, text otherwise.
   The `!` is not flushed with the text before it: it is the opener's own
   source, and `fr_src` puts it back if the bracket decays. *)
Definition ibang_step `{PosPolicy} `{InlineCursor}
  (c : ascii) (txt : Buf) (prev : option ascii)
  (o : ostate) : iscan :=
  if Ascii.eqb c lbrack
  then IText false tnil (Some lbrack)
         (bpush true
            (flush_text_to_at (previous_spot cursor_start) (tval txt) o))
  else ilead c (tpush txt (one bang)) (Some bang) o.

(* Resolving an unbraced delimiter, once the byte after it has arrived
   (or not, at the end of a line: `inone`).  Closing wins over opening,
   and a `}` immediately after forces the close. *)
Local Definition idelim_lit (k : dstyle) (txt : Buf) (marker : bool) : Buf :=
  (tpush txt (ddecay_str k false marker)).

(* And the source byte it ends on, which `ddecay_str` does not spell for a
   smart quote: `'` is written and `’` is what lands in the buffer. *)
Local Definition idelim_lit_prev (k : dstyle) (marker : bool) : option ascii :=
  Some (if marker then rbrace else dchar k).

Definition idelim_done `{PosPolicy} `{InlineCursor}
  (k : dstyle) (txt : Buf) (before : option ascii)
  (marker : bool) (next : option ascii) (o : ostate) : iscan :=
  if (dbare k before && negb marker && nonspace_at next)%bool
  then IText false tnil (Some (dchar k))
         (opush k false
            (flush_text_to_at (span_start (dtoken_span k false)) (tval txt) o))
  else IText false (idelim_lit k txt marker) (idelim_lit_prev k marker) o.

Definition idelim_resolve `{PosPolicy} `{InlineCursor}
  (k : dstyle) (txt : Buf) (before : option ascii)
  (marker : bool) (next : option ascii) (o : ostate) : iscan :=
  if (nonspace_at before || marker)%bool
  then match (if oclose_reaches k marker (os_stk o)
               then oclose k marker (if marker then cursor_stop else cursor_start)
                      (flush_text_to_at (span_start (dtoken_span k false))
                         (tval txt) o)
               else None) with
       | Some o' =>
           IText false tnil
             (Some (if marker then rbrace else dchar k)) o'
       (* a barred opener is the one failure that does not offer the
          token as an opener in its turn *)
       | None =>
           if oclose_barred k marker o
           then IText false (idelim_lit k txt marker) (idelim_lit_prev k marker) o
           else idelim_done k txt before marker next o
       end
  else idelim_done k txt before marker next o.

(* Resolving a `$`: another `$` widens the prefix to display math, a
   backtick run opens the span it prefixes, and anything else makes the
   dollars text.  A third `$` keeps the last two, so the extra one is
   flushed here.

   With math off the backtick takes the same exit as any other byte: the
   dollars join the pending text and `ilead` opens the verbatim they
   would have prefixed. *)
Definition idollar_step `{PosPolicy} `{InlineCursor}
  (c : ascii) (two : bool) (txt : Buf)
  (prev : option ascii) (o : ostate) : iscan :=
  if Ascii.eqb c dollar
  then (if two then IDollar true (tpush txt (one dollar)) (Some dollar) o
        else IDollar true txt prev o)
  else if (is_tick c && math_enabled)%bool
  then IOpen 1 (VMath (if two then DisplayMath else InlineMath))
         (flush_text_to_at (spot_before cursor_start (dollars two)) (tval txt) o)
  else if (is_tick c && dollar_math_enabled && negb two)%bool
  then IOpen 1 (VMaybeDollarMath (tval txt))
         (flush_text_to_at cursor_start (tval txt ++ one dollar) o)
  else if (dollar_math_enabled
           && (negb two ||
               negb (match prev with Some p => Ascii.eqb p dollar | None => false end))
           && (two || (negb (is_ws_nl c) && negb (is_tick c))))%bool
  then IDollarMath two (is_bslash c) (tof (one c)) txt (Some c)
         (ilead c (tpush txt (dollars two)) (Some dollar) o) o
  else ilead c (tpush txt (dollars two)) (Some dollar) o.

(* Three periods are one ellipsis and any other run is literal, so the
   state counts to two and the third byte decides.  A run of four is an
   ellipsis and a period, which falls out of resolving at the third and
   starting again. *)
Definition iperiod_step `{PosPolicy} `{InlineCursor}
  (c : ascii) (two : bool) (txt : Buf)
  (prev : option ascii) (o : ostate) : iscan :=
  if Ascii.eqb c period
  then (if two then
          IText false
            (tpush txt (typography_ellipsis))
            (Some c) o
        else IPeriod true txt prev o)
  else ilead c (tpush txt (periods two)) (Some period) o.

(* A run of hyphens ends at the first byte that is not one.  A `}` is the
   exception, and the only place the dash rule and the delete row meet:
   the run gives its last hyphen back to be a close marker, and what is
   left is cut into dashes.  When no row is spelled with a hyphen there
   is nothing to close and the two bytes are text. *)
Definition idash_step `{PosPolicy} `{InlineCursor}
  (c : ascii) (n : nat) (txt : Buf)
  (prev : option ascii) (o : ostate) : iscan :=
  if Ascii.eqb c hyphen then IDash (S n) txt prev o
  else if Ascii.eqb c rbrace
  then match dstyle_of hyphen with
       | Some k =>
           (* the row takes its whole token back, not one hyphen: djot's
              rows are all one character wide, but the table is a
              parameter and `iscan_marked_close_step` is stated for every
              row, so the arithmetic has to be the row's *)
           if Nat.leb (dwidth k) n
           then idelim_resolve k
                  (tpush txt (typography_dashes (n - dwidth k)))
                  None true (Some c) o
           else IText false (tpush txt (typography_dashes n ++ one rbrace))
                  (Some rbrace) o
       | None => IText false (tpush txt (typography_dashes n ++ one rbrace))
                   (Some rbrace) o
       end
  else ilead c (tpush txt (typography_dashes n)) (Some hyphen) o.

(* Resolving a `%`: a backtick run opens the hole it prefixes, which
   then reads exactly as a verbatim does; anything else makes the `%`
   text and is dispatched afresh. *)
Definition ipercent_step `{PosPolicy} `{InlineCursor}
  (c : ascii) (txt : Buf) (prev : option ascii) (o : ostate) : iscan :=
  if is_tick c
  then IOpen 1 VHole
         (flush_text_to_at (spot_before cursor_start (one percent)) (tval txt) o)
  else ilead c (tpush txt (one percent)) (Some percent) o.

(* No byte follows: the end of a line or of the paragraph.  Every state
   waiting on a next byte resolves here, so after it none remains, which
   is what lets `ibreak` and `ifinish` match on the rest. *)
Definition iresolve `{PosPolicy} `{InlineCursor} (st : iscan) : iscan :=
  match st with
  | IBrace txt _ o => IText false (tpush txt (one lbrace)) (Some lbrace) o
  | IDollar two txt _ o =>
      IText false (tpush txt (dollars two)) (Some dollar) o
  | IPeriod two txt _ o =>
      IText false (tpush txt (periods two)) (Some period) o
  | IDash n txt _ o =>
      IText false (tpush txt (typography_dashes n)) (Some hyphen) o
  | IBang txt _ o => IText false (tpush txt (one bang)) (Some bang) o
  | IPercent txt _ o => IText false (tpush txt (one percent)) (Some percent) o
  (* A token still being spelled is text: the run ended before the row's
     width was reached. *)
  | IDelim k extra txt before marked o =>
      if Nat.ltb (S extra) (dwidth k)
      then IText false (tpush txt (idelim_run k extra marked))
             (Some (dchar k)) o
      else if marked then idelim_open_marked k false txt o
      else idelim_resolve k txt before false None o
  (* The line end is none of the three bytes that make a construct, so
     `[a]` at the end of a line leaves the `]` as text and the scope
     open. *)
  | IClosed txt o => IText false (tpush txt (one rbrack)) (Some rbrack) o
  | _ => st
  end.

(* What a backslash and a whitespace run decay to when the line does not
   end after them.  Only a space after the backslash makes a
   non-breaking space; a tab leaves the backslash literal.  Either way
   the decision consumes only the first byte of the run, and the rest is
   ordinary text. *)
Definition iescws_resolve `{PosPolicy} `{InlineCursor}
  (ws txt : Buf) (prev : option ascii)
  (o : ostate) : Buf * option ascii * ostate :=
  match tval ws with
  | String c rest =>
      if Ascii.eqb c " "%char
      then (tof rest, str_last rest (Some c),
            oemit
              (imk (spot_before cursor_start (tval ws))
                 (spot_before cursor_start rest) NonBreakingSpace)
              (flush_text_to_at
                 (spot_before cursor_start (one bslash ++ tval ws)%string) (tval txt) o))
      else ((tpush txt (one bslash ++ tval ws)), str_last (tval ws) prev, o)
  (* unreachable: `IEscWs` is only ever built with a byte in hand.  Spelt
     as the bare backslash anyway, so the state's own source survives on
     every path out of it. *)
  | EmptyString => ((tpush txt (one bslash)), Some bslash, o)
  end.

(* The line ended after the backslash: a hard break.  The whitespace
   before the backslash is trimmed off the pending text. *)
Definition iesc_hard `{PosPolicy} `{InlineCursor}
  (ws txt : Buf) (o : ostate) : ostate :=
  let kept := strip_trailing_ws (tval txt) in
  (* the source between the text and the line end: the whitespace the
     trim dropped, the backslash, and the run after it.  Two lengths per
     hard break, which is per line at worst; no `String.length` runs per
     scanned byte. *)
  let over := S (String.length (tval ws)
                 + (String.length (tval txt) - String.length kept)) in
  oemit (imk_here HardBreak)
    (flush_text_to_at (spot_plus over cursor_start) kept o).

(* Recursive in exactly one place: a destination advances the ordinary
   reading of its own region, which is this same scanner one scope in. *)
Fixpoint istep_at `{PosPolicy} `{InlineCursor}
  (attrs_enabled : bool) (c : ascii) (st : iscan) : iscan :=
  match st with
  | IText true txt prev o =>
      if is_ws c then IEscWs (tof (one c)) txt prev o
      else IText false (tpush txt (if is_punct c then one c
                                   else String "\"%char (one c))) (Some c) o
  | IEscWs ws txt prev o =>
      if is_ws c then IEscWs (tpush ws (one c)) txt prev o
      else let '(txt', prev', o') := iescws_resolve ws txt prev o in
           ilead c txt' prev' o'
  | IText false txt prev o => ilead c txt prev o
  | IBrace txt prev o => ibrace_step_at attrs_enabled c txt prev o
  | IBang txt prev o => ibang_step c txt prev o
  | IDelim k extra txt before marked o =>
      if Nat.ltb (S extra) (dwidth k)
      then (* still spelling the token: another of the row's characters
              continues it -- and completes a marked one, which opens
              without waiting -- while anything else makes the partial
              run text *)
        (if Ascii.eqb c (dchar k)
         then (if marked then idelim_marked k (S extra) txt o
               else IDelim k (S extra) txt before false o)
         else ilead c (tpush txt (idelim_run k extra marked))
                (Some (dchar k)) o)
      else if marked
      then (* a completed marked opener: it opens whatever comes next, and
              this byte only chooses the side its decay takes, so it is
              still dispatched *)
        ilead c tnil (Some (dchar k))
          (oopen_marked k (Ascii.eqb c rbrace) txt o)
      else
      let marker := Ascii.eqb c rbrace in
      let st' := idelim_resolve k txt before marker (Some c) o in
      (* the `}` of a close marker is consumed with the delimiter; any
         other byte still has to be dispatched *)
      if marker then st'
      else match st' with
           | IText false txt' prev' o' => ilead c txt' prev' o'
           | other => other
           end
  | IDollar two txt prev o => idollar_step c two txt prev o
  | IDollarMath two escaped src txt last sh o =>
      let sh' := istep_at attrs_enabled c sh in
      if escaped
      then IDollarMath two false (tpush src (one c)) txt (Some c) sh' o
      else if Ascii.eqb c dollar
      then IDollarMathClose two src txt
             (if two then Some nl_char else last) sh' o
      else IDollarMath two (is_bslash c) (tpush src (one c)) txt
             (Some c) sh' o
  | IDollarMathClose two src txt last sh o =>
      let sh' := istep_at attrs_enabled c sh in
      if two
      then match last with
           | Some p =>
               if Ascii.eqb p nl_char
               then if Ascii.eqb c dollar
                    then IDollarMathClose true src txt None sh' o
                    else IDollarMath true (is_bslash c)
                           (tpush src (String dollar (one c))) txt (Some c) sh' o
               else if Ascii.eqb c dollar
                    then IDollarMathClose true (tpush src (one c)) txt
                           (Some dollar) sh' o
                    else IDollarMath true (is_bslash c)
                           (tpush src (one c)) txt (Some c) sh' o
           | None =>
               if Ascii.eqb c dollar
               then IDollarMathClose true (tpush src "$$$") txt
                      (Some dollar) sh' o
               else let start := spot_before cursor_start
                              (dollars true ++ tval src ++ dollars true) in
                    ilead c tnil (Some dollar)
                      (oemit (imk start cursor_start
                                 (Math DisplayMath (tval src)))
                        (flush_text_to_at start (tval txt) o))
           end
      else if (match last with Some p => negb (is_ws_nl p)
               | None => false end
               && negb ((Nat.leb 48 (nat_of_ascii c))
                        && (Nat.leb (nat_of_ascii c) 57)))%bool
           then let start := spot_before cursor_start
                     (one dollar ++ tval src ++ one dollar) in
                ilead c tnil (Some dollar)
                  (oemit (imk start cursor_start (Math InlineMath (tval src)))
                    (flush_text_to_at start (tval txt) o))
           else sh'
  | IPeriod two txt prev o => iperiod_step c two txt prev o
  | IDash n txt prev o => idash_step c n txt prev o
  | IOpen n vk o =>
      if is_tick c then IOpen (S n) vk o else IVerb n 0 (tof (one c)) vk o
  | IVerb n run txt vk o =>
      if is_tick c then IVerb n (S run) txt vk o
      else if Nat.eqb run n
      (* the byte after the closing run decides whether a raw spec
         follows, and only for a verbatim: math takes the ordinary
         path *)
      then (match vk with
            | VMaybeDollarMath prefix =>
                if Ascii.eqb c dollar
                then let '(_, o') := opop_str o in
                     let start := spot_before cursor_stop
                       (one dollar ++ ticks n ++ tval txt ++ ticks n ++ one dollar) in
                     IText false tnil (Some dollar)
                       (oemit (imk start cursor_stop
                                  (Math InlineMath (trim_verb (tval txt))))
                         (flush_text_to_at start prefix o'))
                else if Ascii.eqb c lbrace
                     then IRaw tnil (trim_verb (tval txt)) o
                     else ilead c tnil (Some tick)
                            (oemit (imk (text_start o) cursor_start
                                      (Verbatim (trim_verb (tval txt)))) o)
            | VMath InlineMath =>
                if (Ascii.eqb c dollar && dollar_math_enabled)%bool
                then IText false tnil (Some dollar)
                       (oemit (imk (text_start o) cursor_stop
                                  (Math InlineMath (trim_verb (tval txt)))) o)
                else ilead c tnil (Some tick)
                       (oemit (imk (text_start o) cursor_start
                                  (Math InlineMath (trim_verb (tval txt)))) o)
            | _ =>
                if (Ascii.eqb c lbrace && vkind_verb vk)%bool
                then IRaw tnil (trim_verb (tval txt)) o
                else ilead c tnil (Some tick)
                       (oemit (imk (text_start o) cursor_start
                                 (vnode vk (trim_verb (tval txt)))) o)
            end)
      else IVerb n 0 (tpush txt (ticks run ++ one c)) vk o
  (* The three bytes that make a construct of the bracket close it; every
     other one leaves the scope alone and the `]` in the buffer, which is
     why `bclose` runs here rather than at the `]`.  Its `None` is the
     same fall-through: no bracket was open, so the `]` was text. *)
  | IClosed txt o =>
      match (if (Ascii.eqb c lparen || Ascii.eqb c lbrack
                 || (Ascii.eqb c lbrace && attrs_enabled))%bool
             then bclose (flush_text_to_at (previous_spot cursor_start) (tval txt) o)
             else None) with
      | Some (kids, image, open, o') =>
          if Ascii.eqb c lparen
          then IDest kids image open false 0 tnil
                 (idest_open kids image open o') o'
          else if Ascii.eqb c lbrack
               then IReference kids image open false tnil o'
               else ISpan kids image open ap_init tnil o'
      | None => ilead c (tpush txt (one rbrack)) (Some rbrack) o
      end
  | ISpan kids image open p src o =>
      ispan_feed c kids image open p src o
  | IAttr p src txt prev sh o =>
      (* The failing byte is not part of the candidate's source, so it
         arrives in the ordinary reading after that source's last slice
         boundary -- which `iattr_feed` has already applied.  This is what
         keeps `{...` three literal periods rather than one ellipsis. *)
      if ap_failed (astep p c)
      then istep_at false c sh
      else iattr_feed c p src txt prev (istep_at false c sh) o
  | INote esc image label open o => inote_step c esc image label open o
  | IWiki esc rb image region open o => iwiki_step c esc rb image region open o
  | IAuto src txt o => iauto_step c src txt o
  | ISymbol alias txt sh o =>
      isymbol_step c alias txt o
        (istep_at attrs_enabled c sh)
  | IRaw spec txt o => iraw_step_at attrs_enabled c spec txt o
  | IReference kids image open true label o =>
      IReference kids image open false (tpush label (one bslash ++ one c)) o
  | IReference kids image open false label o =>
      if is_bslash c then IReference kids image open true label o
      else if Ascii.eqb c rbrack
      then let key := match tval label with
                      | EmptyString => reference_inlines_text kids
                      | _ => tval label
                      end in
           IText false tnil (Some rbrack)
             (oemit (imk (span_start open) cursor_stop
                       (bnode image kids (Reference (normalize_label key)))) o)
      else IReference kids image open false (tpush label (one c)) o
  | IDest kids image open true depth dst sh o =>
      IDest kids image open false depth
        (tpush dst (if is_punct c then one c
                 else String bslash (one c))) (istep_at attrs_enabled c sh) o
  | IDest kids image open false depth dst sh o =>
      if is_bslash c then IDest kids image open true depth dst
                             (istep_at attrs_enabled c sh) o
      else if Ascii.eqb c lparen
      then IDest kids image open false (S depth) (tpush dst (one lparen))
             (istep_at attrs_enabled c sh) o
      else if Ascii.eqb c rparen
      then match depth with
           | O =>
               (* the balanced close: the one byte that builds the node,
                  and the one that discards the ordinary reading *)
               IText false tnil (Some rparen)
                 (oemit (imk (span_start open) cursor_stop
                           (bnode image kids (Direct (drop_nl (tval dst))))) o)
           | S d => IDest kids image open false d (tpush dst (one rparen))
                      (istep_at attrs_enabled c sh) o
           end
      else IDest kids image open false depth (tpush dst (one c))
             (istep_at attrs_enabled c sh) o
  | IPercent txt prev o => ipercent_step c txt prev o
  end.

Definition istep `{PosPolicy} `{InlineCursor}
  (c : ascii) (st : iscan) : iscan :=
  istep_at inline_attrs_enabled c st.

(* End of the paragraph.  An unclosed verbatim closes here.  A pending
   backslash is a hard break; djoths keeps it as a literal backslash
   (`.project/djotjs-divergences.md`).  A canonical rendering cannot
   produce one, since `escape_str` emits a backslash only before
   punctuation. *)
Definition ifinish_ostate_flat `{PosPolicy} `{InlineCursor}
  (st : iscan) : ostate :=
  match st with
  | IText true txt _ o => iesc_hard tnil txt o
  | IEscWs ws txt _ o => iesc_hard ws txt o
  | IText false txt _ o => flush_text_at (tval txt) o
  | IOpen n vk o =>
      oemit (imk (text_start o) cursor_start (vnode vk EmptyString)) o
  | IVerb n run txt vk o =>
      oemit (imk (text_start o) cursor_start
               (vnode vk (trim_verb
                  (tval (if Nat.eqb run n then txt else tpush txt (ticks run)))))) o
  (* unreachable: `ifinish_ostate` takes a destination's shadow before it
     gets here, and `iresolve` builds no `IDest` *)
  | IDest _ _ _ _ _ _ _ o => o
  | INote esc image label _ o =>
      let '(txt, o') := bnote_lit esc image (tval label) o in flush_text_at txt o'
  (* a wikilink candidate the line ended inside is literal, brackets and
     all *)
  | IWiki esc rb image region _ o =>
      let '(txt, o') := bwiki_lit esc rb image (tval region) o in flush_text_at txt o'
  (* a candidate the line ended inside is literal: the region may not
     contain a break, so the `>` it wanted can never arrive *)
  | IAuto src txt o => flush_text_at (tval (auto_lit (tval src) txt)) o
  | ISymbol _ _ _ o => o
  (* a spec the line ended inside never closed: the verbatim stands and
     the spec source is text after it *)
  | IRaw spec txt o =>
      let spec_start := spot_before cursor_start (String lbrace (tval spec)) in
      flush_text_at (iraw_lit (tval spec))
        (oemit (imk (text_start o) spec_start (Verbatim txt)) o)
  | IReference kids image _ esc label o =>
      let '(txt, o') := bref_lit kids image
                          (tval label ++ (if esc then one bslash else EmptyString)) o in
      flush_text_at (tval txt) o'
  (* an unclosed span is literal too: there is no next line for its spec
     to close on, and the breaks it did cross are in the source *)
  | ISpan kids image _ _ src o =>
      let '(txt, o') := bspan_lit kids image (tval src) o in flush_text_at (tval txt) o'
  (* a spec the paragraph ended inside never closed, and its source is
     text: the brace, then what the machine has read since *)
  | IAttr _ src txt _ _ o =>
      let '(t, o') := battr_lit (tval src) txt o in flush_text_at (tval t) o'
  (* unreachable: `iresolve` leaves no `IBrace`, `IBang`, `IDollar`,
     `IPeriod`, `IDash`, `IDelim` or `IClosed` *)
  | IDollarMath _ _ _ _ _ _ o | IDollarMathClose _ _ _ _ _ o
  | IPercent _ _ o
  | IBrace _ _ o | IBang _ _ o | IDollar _ _ _ o
  | IPeriod _ _ _ o | IDash _ _ _ o
  | IDelim _ _ _ _ _ o | IClosed _ o => o
  end.

(* An unclosed destination is not literal: the region turns literal only
   at the close, so a region that never closes keeps its ordinary
   reading, and `oflatten` puts the `[` and `](` back when it abandons
   the `FKDest` frame. *)
Fixpoint ifinish_ostate `{PosPolicy} `{InlineCursor} (st : iscan) : ostate :=
  match st with
  | IDollarMath _ _ _ _ _ sh _ => ifinish_ostate sh
  | IDollarMathClose false src txt last sh o =>
      if match last with Some p => negb (is_ws_nl p) | None => false end
      then let start := spot_before cursor_start
                       (one dollar ++ tval src ++ one dollar) in
           oemit (imk start cursor_start (Math InlineMath (tval src)))
             (flush_text_to_at start (tval txt) o)
      else ifinish_ostate sh
  | IDollarMathClose true src txt None _ o =>
      let start := spot_before cursor_start
                     (dollars true ++ tval src ++ dollars true) in
      oemit (imk start cursor_start (Math DisplayMath (tval src)))
        (flush_text_to_at start (tval txt) o)
  | IDollarMathClose true _ _ _ sh _ => ifinish_ostate sh
  | IAttr _ _ _ _ sh _ => ifinish_ostate sh
  | IDest _ _ _ _ _ _ sh _ => ifinish_ostate sh
  | ISymbol _ _ sh _ => ifinish_ostate sh
  | _ => ifinish_ostate_flat (iresolve st)
  end.

Definition ifinish_items `{PosPolicy} `{InlineCursor} (st : iscan) : oitems :=
  oitems_of (ifinish_ostate st).

Definition ifinish_rev `{PosPolicy} `{InlineCursor} (st : iscan) : inlines :=
  ofinish (ifinish_ostate st).

Lemma ifinish_rev_items :
  forall st, ifinish_rev st = oresolve (ifinish_items st).
Proof. reflexivity. Qed.

Definition ifinish `{PosPolicy} `{InlineCursor} (st : iscan) : inlines :=
  List.rev (ifinish_rev st).

(* A line boundary inside a paragraph.  The newline is an ordinary byte
   of the paragraph, so a span may cross a break: `` `a `` / `` b` `` is
   one code span containing a newline.  A paragraph is therefore one scan
   with this between its lines.

   Inside a verbatim the newline is content.  A resolved closing run
   (`run = n`) is the one case where the span ends at the break and the
   newline is the soft break after it. *)
Fixpoint ibreak_flat `{PosPolicy} `{InlineCursor} (st : iscan) : iscan :=
  match st with
  (* A hard break replaces the soft one: it is the break, rendered. *)
  | IText true txt _ o =>
      IText false tnil None (oword_reset (iesc_hard tnil txt o))
  | IEscWs ws txt _ o =>
      IText false tnil None (oword_reset (iesc_hard ws txt o))
  | IText false txt _ o =>
      IText false tnil None
        (oword_reset
          (oemit (imk_here SoftBreak)
            (flush_text_at (tval txt) o)))
  | IOpen n vk o => IVerb n 0 (tof nl) vk o
  | IVerb n run txt vk o =>
      if Nat.eqb run n
      then IText false tnil None
             (oword_reset
                (oemit (imk_here SoftBreak)
                  (oemit (imk (text_start o) cursor_start
                            (vnode vk (trim_verb (tval txt)))) o)))
      else IVerb n 0 (tpush txt (ticks run ++ nl)) vk o
  (* unreachable, as in `ifinish_ostate_flat` *)
  | IDest _ _ _ _ _ _ _ _ as st' => st'
  (* A label crosses a break and the newline is whitespace to
     `normalize_label`, so `[^a` / `b]` is one reference to `a b`. *)
  | INote esc image label open o =>
      INote false image
        (tpush label ((if esc then one bslash else EmptyString) ++ nl)) open o
  | IReference kids image open esc label o =>
      IReference kids image open false
        (tpush label ((if esc then one bslash else EmptyString) ++ nl)) o
  (* A wikilink candidate does not cross a break: it decays here, as an
     autolink candidate does just below. *)
  | IWiki esc rb image region _ o =>
      let '(txt, o') := bwiki_lit esc rb image (tval region) o in
      IText false tnil None
        (oword_reset (oemit (imk_here SoftBreak) (flush_text_at (tval txt) o')))
  (* and the break itself is the soft one, exactly as it is for the text
     the candidate decays to *)
  | IAuto src txt o =>
      IText false tnil None
        (oword_reset
          (oemit (imk_here SoftBreak)
            (flush_text_at (tval (auto_lit (tval src) txt)) o)))
  | ISymbol _ _ sh _ => ibreak_flat sh
  (* nor does a raw spec: the pattern excludes whitespace, so a break
     ends the candidate exactly as `ifinish` does *)
  | IRaw spec txt o =>
      let spec_start := spot_before cursor_start (String lbrace (tval spec)) in
      IText false tnil None
        (oword_reset
          (oemit (imk_here SoftBreak)
             (flush_text_at (iraw_lit (tval spec))
               (oemit (imk (text_start o) spec_start (Verbatim txt)) o))))
  (* A span's spec crosses the break too, and the newline is whitespace to
     the machine: `[s]{.a` / `.b}` is one span whose classes merge.  It is
     fed rather than accumulated because the machine is what decides
     whether the break separates two tokens. *)
  | ISpan kids image open p src o =>
      ispan_feed nl_char kids image open p src o
  (* and so does a bare spec: `hi{#i .c` / `k="v"}` attaches to `hi`.  No
     `SoftBreak` is emitted, since the break is inside the spec's
     source. *)
  | IAttr p src txt prev sh o =>
      (* unreachable: `ibreak_at` advances the ordinary reading too *)
      iattr_feed nl_char p src txt prev sh o
  (* unreachable, as in `ifinish_ostate` *)
  | (IDollarMath _ _ _ _ _ _ _ | IDollarMathClose _ _ _ _ _ _
    | IPercent _ _ _
    | IBrace _ _ _ | IBang _ _ _ | IDollar _ _ _ _
    | IPeriod _ _ _ _ | IDash _ _ _ _
    | IDelim _ _ _ _ _ _ | IClosed _ _) as st' => st'
  end.

(* A destination crosses the break: the byte is accumulated and dropped
   at the close.  The ordinary reading takes the break as the soft one it
   is, so the shadow gets `ibreak` and not `istep nl`. *)
Fixpoint ibreak_at `{PosPolicy} `{InlineCursor}
  (attrs_enabled : bool) (st : iscan) : iscan :=
  match st with
  | IDollar two txt prev o =>
      if (two && dollar_math_enabled &&
          negb (match prev with Some p => Ascii.eqb p dollar
                | None => false end))%bool
      then IDollarMath true false (tof nl) txt (Some nl_char)
             (ibreak_flat
                (IText false (tpush txt (dollars true))
                   (Some dollar) o)) o
      else ibreak_flat (iresolve st)
  | IDollarMath two escaped src txt last sh o =>
      IDollarMath two false
        (tpush src nl)
        txt (Some nl_char) (ibreak_at attrs_enabled sh) o
  | IDollarMathClose two src txt last sh o =>
      if two then
        match last with
        | None =>
            let start := spot_before cursor_start
                           (dollars true ++ tval src ++ dollars true) in
            ibreak_flat
              (IText false tnil (Some dollar)
                (oemit (imk start cursor_start (Math DisplayMath (tval src)))
                  (flush_text_to_at start (tval txt) o)))
        | Some p =>
            IDollarMath true false
              (tpush src (if Ascii.eqb p nl_char then one dollar ++ nl else nl))
              txt (Some nl_char) (ibreak_at attrs_enabled sh) o
        end
      else if match last with Some p => negb (is_ws_nl p)
              | None => false end
           then let start := spot_before cursor_start
                       (one dollar ++ tval src ++ one dollar) in
                ibreak_flat
                  (IText false tnil (Some dollar)
                    (oemit (imk start cursor_start (Math InlineMath (tval src)))
                      (flush_text_to_at start (tval txt) o)))
           else ibreak_at attrs_enabled sh
  | IAttr p src txt prev sh o =>
      iattr_feed nl_char p src txt prev
        (ibreak_at false sh) o
  | IDest kids image open esc depth dst sh o =>
      IDest kids image open false depth
        (tpush dst ((if esc then one bslash else EmptyString) ++ nl))
        (ibreak_at attrs_enabled sh) o
  | ISymbol _ _ sh _ => ibreak_at attrs_enabled sh
  | _ => ibreak_flat (iresolve st)
  end.


Definition ibreak `{PosPolicy} `{InlineCursor} (st : iscan) : iscan :=
  ibreak_at inline_attrs_enabled st.

(* A state that owes nothing to the next line: every construct it has
   seen is resolved, so the boundary just ends the line and `ibreak`
   agrees with `ifinish` on what was emitted.  What fails it is a span
   still open across the break -- an unterminated backtick run, a
   verbatim whose closer has not arrived, or any open scope. *)
Definition iclosed_at (st : iscan) : bool :=
  match st with
  (* a pending backslash is not closed: it owes the *next* byte a hard
     break or a literal, so the line does not end with a soft one *)
  | IText esc _ _ o => (negb esc && null (os_stk o))%bool
  | IEscWs _ _ _ _ => false
  | IOpen _ _ _ => false
  | IVerb n run _ _ o => (Nat.eqb run n && null (os_stk o))%bool
  (* an open destination or an unclosed spec owes the next line;
     `IClosed` cannot appear, since `iresolve` has just turned it into
     text *)
  | IBrace _ _ _ | IAttr _ _ _ _ _ _ | IBang _ _ _ | IDollar _ _ _ _
  | IDollarMath _ _ _ _ _ _ _ | IDollarMathClose _ _ _ _ _ _
  | IPercent _ _ _
  | IPeriod _ _ _ _ | IDash _ _ _ _
  | IDelim _ _ _ _ _ _ | IClosed _ _ | ISpan _ _ _ _ _ _
  | INote _ _ _ _ _ | IReference _ _ _ _ _ _
  | IDest _ _ _ _ _ _ _ _ => false
  (* an autolink candidate owes the next line nothing: the region may not
     hold a break, so the candidate dies at the boundary and what it ate
     is text on this line *)
  | IAuto _ _ o | IRaw _ _ o
  | IWiki _ _ _ _ _ o => null (os_stk o)
  | ISymbol _ _ _ _ => false
  end.

Definition iscan_closed `{PosPolicy} `{InlineCursor} (st : iscan) : bool :=
  match st with
  | IDollar two _ prev _ =>
      if (two && dollar_math_enabled &&
          negb (match prev with Some p => Ascii.eqb p dollar
                | None => false end))%bool
      then false else iclosed_at (iresolve st)
  | _ => iclosed_at (iresolve st)
  end.

(* `iresolve` is the end-of-line disposition.  When a byte is known to
   follow, only `IDelim` answers differently, and only about opening:
   `idelim_done` consults that byte and `iresolve` passes `None`, so a
   run that cannot close settles as text at the end of a line and opens
   in the middle of one. *)
Local Definition iresolve_next `{PosPolicy} `{InlineCursor}
  (c : ascii) (st : iscan) : iscan :=
  match st with
  | IDelim k extra txt before marked o =>
      if Nat.ltb (S extra) (dwidth k)
      then IText false (tpush txt (idelim_run k extra marked))
             (Some (dchar k)) o
      else if marked then idelim_open_marked k (Ascii.eqb c rbrace) txt o
      else idelim_resolve k txt before false (Some c) o
  | _ => iresolve st
  end.

(* "Nothing is open, and nothing is waiting on what comes after `c`".
   Strictly stronger than `iscan_closed`, and the two differ exactly on
   a delimiter run that would open: `a*` is closed at a line's end and
   an opener before a colon, which is why the split test asks this one.
   See `.project/keyed-blocks.md` 9.1. *)
Definition iscan_settled `{PosPolicy} `{InlineCursor}
  (c : ascii) (st : iscan) : bool :=
  iclosed_at (iresolve_next c st).

(* The two recursive definitions above handle a state carrying an
   alternative scan themselves and send everything else through
   `iresolve`.  The lemmas below that reason by cases on the resolved
   state are about the second kind; `iclosed_at` and `iscan_wf` both
   exclude the first. *)
Definition is_compound (st : iscan) : bool :=
  match st with
  | IDollar two _ prev _ =>
      (two && dollar_math_enabled &&
       negb (match prev with Some p => Ascii.eqb p dollar
             | None => false end))%bool
  | IDollarMath _ _ _ _ _ _ _ | IDollarMathClose _ _ _ _ _ _ => true
  | IAttr _ _ _ _ _ _ | IDest _ _ _ _ _ _ _ _
  | ISymbol _ _ _ _ => true
  | _ => false
  end.

End Text.

(* The specification scanner's state. *)
Notation iscan := (iscan_g (Buf:=string)).

(* `blit_prev` on the fragment alone agrees with it on the whole text the
   fragment joins, cut or not: the fallbacks never read the pending text
   for it. *)
Lemma str_last_app : forall a b p, str_last (a ++ b) p = str_last b (str_last a p).
Proof. induction a as [|c a IH]; intros b p; [reflexivity|]. apply IH. Qed.

Lemma blit_prev_fragment : forall a c s,
  blit_prev (a ++ String c s) = blit_prev (String c s).
Proof. intros a c s. unfold blit_prev. rewrite str_last_app. reflexivity. Qed.

Lemma blit_prev_bsplit_nl : forall `{PosPolicy} `{InlineCursor} s t o,
  blit_prev (fst (bsplit_nl s t o)) = blit_prev (t ++ s).
Proof.
  intros P C s. induction s as [|c s IH]; intros t o.
  - cbn. rewrite append_empty_r. reflexivity.
  - cbn [bsplit_nl]. tred.
    destruct (Ascii.eqb c nl_char) eqn:E.
    + apply Ascii.eqb_eq in E. subst c. rewrite IH.
      unfold blit_prev. rewrite (str_last_app t). reflexivity.
    + rewrite IH, append_assoc. reflexivity.
Qed.

(* A buffer's scan state read as the specification's: every pending-text
   and source field through `tval`, and back through `tof`. `InlineBuffer.v`
   proves the scan commutes with `map_text`. *)
Section Read.
Context {Buf : Type} {X : TextOps Buf}.

Fixpoint map_text (st : iscan_g (Buf:=Buf)) : iscan :=
  match st with
  | IText esc t prev o => IText esc (tval t) prev o
  | IEscWs ws t prev o => IEscWs (tval ws) (tval t) prev o
  | IBrace t prev o => IBrace (tval t) prev o
  | IDelim k extra t before marked o => IDelim k extra (tval t) before marked o
  | IOpen n vk o => IOpen n vk o
  | IVerb n run v vk o => IVerb n run (tval v) vk o
  | IDollar two t prev o => IDollar two (tval t) prev o
  | IDollarMath two escaped src t last sh o =>
      IDollarMath two escaped (tval src) (tval t) last (map_text sh) o
  | IDollarMathClose two src t last sh o =>
      IDollarMathClose two (tval src) (tval t) last (map_text sh) o
  | IPeriod two t prev o => IPeriod two (tval t) prev o
  | IDash n t prev o => IDash n (tval t) prev o
  | IBang t prev o => IBang (tval t) prev o
  | IClosed t o => IClosed (tval t) o
  | ISpan kids image open p src o => ISpan kids image open p (tval src) o
  | IAttr p src t prev sh o => IAttr p (tval src) (tval t) prev (map_text sh) o
  | IReference kids image open esc label o => IReference kids image open esc (tval label) o
  | INote esc image label open o => INote esc image (tval label) open o
  | IWiki esc rb image region open o => IWiki esc rb image (tval region) open o
  | IDest kids image open esc depth dst sh o =>
      IDest kids image open esc depth (tval dst) (map_text sh) o
  | IAuto src t o => IAuto (tval src) (tval t) o
  | ISymbol alias t sh o => ISymbol (tval alias) (tval t) (map_text sh) o
  | IRaw spec v o => IRaw (tval spec) v o
  | IPercent t prev o => IPercent (tval t) prev o
  end.

Fixpoint lift (st : iscan) : iscan_g (Buf:=Buf) :=
  match st with
  | IText esc t prev o => IText esc (tof t) prev o
  | IEscWs ws t prev o => IEscWs (tof ws) (tof t) prev o
  | IBrace t prev o => IBrace (tof t) prev o
  | IDelim k extra t before marked o => IDelim k extra (tof t) before marked o
  | IOpen n vk o => IOpen n vk o
  | IVerb n run v vk o => IVerb n run (tof v) vk o
  | IDollar two t prev o => IDollar two (tof t) prev o
  | IDollarMath two escaped src t last sh o =>
      IDollarMath two escaped (tof src) (tof t) last (lift sh) o
  | IDollarMathClose two src t last sh o =>
      IDollarMathClose two (tof src) (tof t) last (lift sh) o
  | IPeriod two t prev o => IPeriod two (tof t) prev o
  | IDash n t prev o => IDash n (tof t) prev o
  | IBang t prev o => IBang (tof t) prev o
  | IClosed t o => IClosed (tof t) o
  | ISpan kids image open p src o => ISpan kids image open p (tof src) o
  | IAttr p src t prev sh o => IAttr p (tof src) (tof t) prev (lift sh) o
  | IReference kids image open esc label o => IReference kids image open esc (tof label) o
  | INote esc image label open o => INote esc image (tof label) open o
  | IWiki esc rb image region open o => IWiki esc rb image (tof region) open o
  | IDest kids image open esc depth dst sh o =>
      IDest kids image open esc depth (tof dst) (lift sh) o
  | IAuto src t o => IAuto (tof src) (tof t) o
  | ISymbol alias t sh o => ISymbol (tof alias) (tof t) (lift sh) o
  | IRaw spec v o => IRaw (tof spec) v o
  | IPercent t prev o => IPercent (tof t) prev o
  end.

End Read.

(*
The candidate stack
===================

The scanner the extraction runs.  It computes what the specification
scanner computes (`InlineStack.v`), and differs in one place: the open
link destinations.

In the specification each destination carries the ordinary reading of
its region, and that reading opens the next destination inside itself,
so k open destinations are a chain k deep that every byte walks.  Here
they are frames on a stack over one ordinary reading, `s_cur`.  Two
facts make that sound.  Destinations count the same bytes, `(` and `)`,
under the same escapes, so the later one closes first and one counter
serves all of them, each frame keeping the counter's value at its
opener.  And a close discards the ordinary reading it closes over,
which is where every later destination lived, so only the top frame
can close.

A frame's payload is not kept whole.  `cf_under` holds the source from
the opener of the frame below it to its own opener, and `s_seg` the
source since the top frame's opener, so a byte is pushed once whatever
the depth, and a close joins the top frame's payload to the segment
below it.

A destination the specification nests where the stack would not take
it stays nested in `s_cur`: one opened inside an attribute, symbol or
dollar math candidate's shadow, or one whose counter would not stay
above the frame below.  That costs what it costs today, and nothing
else depends on it.
*)
Section Stack.
Context {Buf : Type} {X : TextOps Buf}.

(* A destination's `dst` as a function of its source: an escaped byte is
   itself if it is punctuation and keeps its backslash otherwise, and a
   pending backslash at the end is not there yet. *)
Fixpoint ddecode_from (esc : bool) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if esc
      then ((if is_punct c then one c else String bslash (one c))
            ++ ddecode_from false rest)%string
      else if is_bslash c then ddecode_from true rest
      else String c (ddecode_from false rest)
  end.

Definition ddecode (s : string) : string := ddecode_from false s.

(* What a frame builds at its close, on the state from before its
   opener. *)
Inductive ckind : Type :=
  | CDest (kids : inlines) (image : bool) (open : span) (o : ostate).

(* `cf_level` is the counter just after the opener. *)
Record cframe : Type := CFrame {
  cf_kind : ckind;
  cf_level : nat;
  cf_under : Buf
}.

(* `s_frames` is top first, and only the top frame can close.  The
   counter and `s_esc` run over every byte; `s_seg` only while a frame is
   open. *)
Record sscan : Type := SScan {
  s_frames : list cframe;
  s_parens : nat;
  s_esc : bool;
  s_seg : Buf;
  s_cur : iscan_g (Buf:=Buf)
}.

Definition slift (st : iscan_g (Buf:=Buf)) : sscan :=
  SScan [] 0 false tnil st.

Definition stop_level (fs : list cframe) : option nat :=
  match fs with [] => None | f :: _ => Some (cf_level f) end.

Definition sabove (top : option nat) (n : nat) : bool :=
  match top with Some l => Nat.ltb l n | None => true end.

Definition scount (esc : bool) (c up down : ascii) (n : nat) : nat :=
  if esc then n
  else if Ascii.eqb c up then S n
  else if Ascii.eqb c down then pred n
  else n.

(* A destination the reading has just opened becomes a frame: nothing
   read into it yet, and its counter above the frame below. *)
Definition speel (fs : list cframe) (p : nat) (esc : bool) (seg : Buf)
  (cur : iscan_g (Buf:=Buf)) : sscan :=
  match cur with
  | IDest kids image open false O dst sh o =>
      if (negb (tnonempty dst) && negb esc && sabove (stop_level fs) p)%bool
      then SScan (CFrame (CDest kids image open o) p seg :: fs) p esc tnil sh
      else SScan fs p esc seg cur
  | _ => SScan fs p esc seg cur
  end.

Definition sframe_close `{PosPolicy} `{InlineCursor}
  (k : ckind) (pay : string) : iscan_g (Buf:=Buf) :=
  match k with
  | CDest kids image open o =>
      IText false tnil (Some rparen)
        (oemit (imk (span_start open) cursor_stop
                  (bnode image kids (Direct (drop_nl (ddecode pay))))) o)
  end.

Definition sstep_at `{PosPolicy} `{InlineCursor}
  (attrs_enabled : bool) (c : ascii) (s : sscan) : sscan :=
  let '(SScan fs p esc seg cur) := s in
  let p' := scount esc c lparen rparen p in
  let esc' := (negb esc && is_bslash c)%bool in
  match fs with
  | [] => speel [] p' esc' seg (istep_at attrs_enabled c cur)
  | f :: fs' =>
      if (negb esc && Ascii.eqb c rparen && Nat.eqb (cf_level f) p)%bool
      then SScan fs' p' false
             (if null fs' then tnil else tpush (cf_under f) (tval seg ++ one c))
             (sframe_close (cf_kind f) (tval seg))
      else speel fs p' esc' (tpush seg (one c)) (istep_at attrs_enabled c cur)
  end.

(* A break is a byte of every open payload, and escapes nothing. *)
Definition sbreak_at `{PosPolicy} `{InlineCursor}
  (attrs_enabled : bool) (s : sscan) : sscan :=
  let '(SScan fs p _ seg cur) := s in
  SScan fs p false (if null fs then seg else tpush seg nl)
    (ibreak_at attrs_enabled cur).

(* The paragraph ends with every frame open, and an open candidate keeps
   its ordinary reading. *)
Definition sfinish `{PosPolicy} `{InlineCursor} (s : sscan) : inlines :=
  ifinish (s_cur s).

End Stack.

Lemma ibreak_flat_state :
  forall `{PosPolicy} `{InlineCursor} st,
    is_compound st = false -> ibreak st = ibreak_flat (iresolve st).
Proof.
  intros P C st H. destruct st; try reflexivity; try discriminate H.
  cbn [is_compound ibreak ibreak_at] in H |- *.
  destruct (two && dollar_math_enabled &&
    negb (match prev with Some p => Ascii.eqb p dollar
          | None => false end))%bool; [discriminate H|reflexivity].
Qed.

Lemma ibreak_at_flat_state :
  forall `{PosPolicy} `{InlineCursor} attrs_enabled st,
    is_compound st = false -> ibreak_at attrs_enabled st = ibreak st.
Proof.
  intros P C attrs_enabled st H. destruct st; try reflexivity;
    try discriminate H.
Qed.

Lemma ifinish_ostate_flat_state :
  forall `{PosPolicy} `{InlineCursor} st,
    is_compound st = false ->
    ifinish_ostate st = ifinish_ostate_flat (iresolve st).
Proof. intros P C st H. destruct st; try reflexivity; discriminate H. Qed.

Lemma ibreak_closed :
  forall `{PosPolicy} `{InlineCursor} st,
    iscan_closed st = true ->
    ibreak st = IText false EmptyString None
                  (OState
                    (OIn (imk_here SoftBreak)
                       :: ifinish_items st) [] None).
Proof.
  intros P C st H.
  assert (Hd : is_compound st = false)
    by (destruct st; try reflexivity;
        try (cbn in H; discriminate H);
        cbn [is_compound iscan_closed] in H |- *;
        destruct (two && dollar_math_enabled &&
          negb (match prev with Some p => Ascii.eqb p dollar
                | None => false end))%bool;
        [discriminate H|reflexivity]).
  assert (Hclosed : iclosed_at (iresolve st) = true).
  { destruct st; cbn [iscan_closed] in H; try exact H.
    destruct (two && dollar_math_enabled &&
      negb (match prev with Some p => Ascii.eqb p dollar
            | None => false end))%bool; [discriminate H|exact H]. }
  clear H. rename Hclosed into H.
  rewrite (ibreak_flat_state st Hd).
  unfold ifinish_items. rewrite oitems_of_spec.
  rewrite (ifinish_ostate_flat_state st Hd).
  unfold iscan_closed, iclosed_at, ibreak_flat, ifinish_ostate_flat in *.
  cbn [tval tnonempty tpush tof tnil] in *.
  destruct (iresolve st) as [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|? ? ? ? ? ? ?|? ? ? ? ? ?|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|cltxt clob|kids img open sp ssrc sob|ap asrc atxt aprev ash aob|kids img open label ob|nesc nimg nlab open nob|wesc wrb wimg wreg wopen wob|kids img open esc depth dst sh ob|asrc atxt aob|salias stxt sh so|rspec rtxt rob|pctxt pcprev pcob];
    try discriminate.
  - destruct o as [out [|f stk] word]; [|discriminate].
    unfold flush_text_at, oemit; cbn [os_stk os_out oflatten oapp].
    destruct (nonempty_str txt); reflexivity.
  - apply andb_true_iff in H as [Hr Hs]. rewrite Hr.
    destruct o as [out [|f stk] word]; [|discriminate].
    unfold oemit; cbn [os_stk os_out oflatten oapp]. reflexivity.
  (* a wikilink candidate decays the same way, with its own literal; taking
     back the text before it leaves the stack as empty as it was *)
  - destruct wob as [out [|f stk] word]; [|discriminate].
    unfold bwiki_lit, opop_str; cbn [os_stk os_out].
    destruct out as [|[[p a v]|b sp w] out];
      try (destruct a as [|kv a]; [destruct v|]);
      unfold flush_text_at, oemit; cbn [os_stk os_out oflatten oapp];
      match goal with |- context [nonempty_str ?t] => destruct (nonempty_str t) end;
      reflexivity.
  (* the candidate decays to text and the boundary is the soft break
     after it, which is the text case with `auto_lit` in the buffer *)
  - destruct aob as [out [|f stk] word]; [|discriminate].
    unfold flush_text_at, oemit; cbn [os_stk os_out oflatten oapp].
    destruct (nonempty_str (auto_lit asrc atxt)); reflexivity.
  (* the same, with the verbatim the spec did not claim underneath *)
  - destruct rob as [out [|f stk] word]; [|discriminate].
    unfold flush_text_at, oemit; cbn [os_stk os_out oflatten oapp].
    destruct (nonempty_str (iraw_lit rspec)); reflexivity.
Qed.

Fixpoint iscan_str (s : string) (st : iscan) : iscan :=
  match s with
  | EmptyString => st
  | String c rest =>
      iscan_str rest (@istep _ _ semantic_pos semantic_inline_cursor c st)
  end.

(* An executable certificate for the outer scan's source dispatch: one
   unit of fuel dispatches one source byte, and state rewrites such as
   closing or abandoning a scope spend none and never feed a byte back.
   It says nothing about the cost of one dispatch (`oclose` may walk the
   opener stack), so it is not a linear-time theorem.  Where djot.js
   replays a failed candidate's source, this scanner advances an
   ordinary-reading shadow alongside the candidate (`IAttr`, `IDest`,
   `ISymbol`) and selects it (`.project/no-backtracking.md`). *)
Fixpoint iscan_str_fuel (fuel : nat) (s : string) (st : iscan)
  : option iscan :=
  match s with
  | EmptyString => Some st
  | String c rest =>
      match fuel with
      | O => None
      | S fuel' =>
          iscan_str_fuel fuel' rest
            (@istep _ _ semantic_pos semantic_inline_cursor c st)
      end
  end.

Lemma iscan_str_no_reread :
  forall s st,
    iscan_str_fuel (String.length s) s st = Some (iscan_str s st).
Proof.
  induction s as [|c rest IH]; intros st; cbn [String.length iscan_str_fuel
    iscan_str]; [reflexivity|apply IH].
Qed.

Local Lemma iscan_str_fuel_short :
  forall s fuel st,
    fuel < String.length s -> iscan_str_fuel fuel s st = None.
Proof.
  induction s as [|c rest IH]; intros fuel st Hlt.
  - cbn [String.length] in Hlt. lia.
  - destruct fuel as [|fuel']; [reflexivity|].
    cbn [String.length iscan_str_fuel] in Hlt |- *.
    apply IH. lia.
Qed.

(* A paragraph's lines, in order.  Trailing whitespace is stripped from
   the last line only, whatever state the scan is in, so `` `a  `` closes
   on the trimmed content.  Interior lines keep their trailing spaces,
   which is observable inside a verbatim. *)
Fixpoint iscan_lines (l : list string) (st : iscan) : iscan :=
  match l with
  | [] => st
  | [x] => iscan_str (strip_trailing_ws x) st
  | x :: rest =>
      iscan_lines rest
        (@ibreak _ _ semantic_pos semantic_inline_cursor (iscan_str x st))
  end.

(* The same scan with attribute recognition off.  A block attribute spec
   that fails hands its lines back to the paragraph, which reads them this
   way. *)
Fixpoint iscan_str_off (s : string) (st : iscan) : iscan :=
  match s with
  | EmptyString => st
  | String c rest =>
      iscan_str_off rest
        (@istep_at _ _ semantic_pos semantic_inline_cursor false c st)
  end.

(* `k` leading lines of a paragraph read with attributes off, the rest as
   usual.  The region is whole lines, so the in-line slice boundaries of
   `islice_end` have no counterpart here.  The break that ends each off
   line is off too.

   `k = 0` is `iscan_lines`, definitionally, which leaves every statement
   about a paragraph's scan unconditioned. *)
Fixpoint iscan_lines_off (k : nat) (l : list string) (st : iscan) : iscan :=
  match k with
  | O => iscan_lines l st
  | S k' =>
      match l with
      | [] => st
      | [x] => iscan_str_off (strip_trailing_ws x) st
      | x :: rest =>
          iscan_lines_off k' rest
            (@ibreak_at _ _ semantic_pos semantic_inline_cursor false
              (iscan_str_off x st))
      end
  end.

Definition istart : iscan := IText false EmptyString None ostart.

(* The paragraph drivers over the candidate stack, on a buffer.  They are
   `iscan_str` and its siblings with `sstep_at` and `sbreak_at` for the
   transitions, and the extraction runs them in place of those
   (`InlineStack.v` proves the two agree). *)
Section StackDrivers.
Context {Buf : Type} {X : TextOps Buf}.

Fixpoint sscan_str (s : string) (st : sscan (Buf:=Buf)) : sscan :=
  match s with
  | EmptyString => st
  | String c rest =>
      sscan_str rest
        (@sstep_at _ _ semantic_pos semantic_inline_cursor
           inline_attrs_enabled c st)
  end.

Fixpoint sscan_str_off (s : string) (st : sscan (Buf:=Buf)) : sscan :=
  match s with
  | EmptyString => st
  | String c rest =>
      sscan_str_off rest
        (@sstep_at _ _ semantic_pos semantic_inline_cursor false c st)
  end.

Fixpoint sscan_lines (l : list string) (st : sscan (Buf:=Buf)) : sscan :=
  match l with
  | [] => st
  | [x] => sscan_str (strip_trailing_ws x) st
  | x :: rest =>
      sscan_lines rest
        (@sbreak_at _ _ semantic_pos semantic_inline_cursor
           inline_attrs_enabled (sscan_str x st))
  end.

Fixpoint sscan_lines_off (k : nat) (l : list string) (st : sscan (Buf:=Buf))
  : sscan :=
  match k with
  | O => sscan_lines l st
  | S k' =>
      match l with
      | [] => st
      | [x] => sscan_str_off (strip_trailing_ws x) st
      | x :: rest =>
          sscan_lines_off k' rest
            (@sbreak_at _ _ semantic_pos semantic_inline_cursor false
              (sscan_str_off x st))
      end
  end.

Definition sstart : sscan (Buf:=Buf) := slift (lift istart).

End StackDrivers.

(* What the extraction runs for `parse_inline_line` and
   `para_inlines_off`: the same scans, on the stack and over `chunks`. *)
Definition parse_inline_line_stk (s : string) : inlines :=
  @sfinish chunks _ semantic_pos semantic_inline_cursor
    (sscan_str s sstart).

Definition para_inlines_off_stk (k : nat) (l : list string) : inlines :=
  @sfinish chunks _ semantic_pos semantic_inline_cursor
    (sscan_lines_off k l sstart).
(* Parse one line's inline content. *)
Definition parse_inline_line (s : string) : inlines := ifinish (iscan_str s istart).

Lemma iscan_str_app :
  forall a b st, iscan_str (a ++ b) st = iscan_str b (iscan_str a st).
Proof.
  induction a as [|c a IH]; intros b st; cbn [iscan_str]; [reflexivity|].
  apply IH.
Qed.

(* A paragraph's lines, in order, into inlines: one scan, with `ibreak`
   between lines.  A scan per line joined by `SoftBreak` agrees with it
   exactly when no line leaves the scan mid-span, which the canonical
   view guarantees (`para_inlines_cons2_closed`). *)
Definition para_inlines (l : list string) : inlines :=
  ifinish (iscan_lines l istart).

(* A paragraph whose first `k` lines came from a block attribute spec
   that failed: those lines are read with attributes off, and the rest as
   usual. *)
Definition para_inlines_off (k : nat) (l : list string) : inlines :=
  ifinish (iscan_lines_off k l istart).

Local Lemma para_inlines_off_0 :
  forall l, para_inlines_off 0 l = para_inlines l.
Proof. reflexivity. Qed.

(* Classification sees the source and nothing else: brackets produce
   unresolved `Reference` and `FootnoteReference` nodes without
   consulting either side table.  A later resolution pass may fill
   targets but may not change this tree. *)
Record inline_env : Type := InlineEnv {
  inline_notes : note_map;
  inline_references : reference_map;
  inline_auto_references : reference_map
}.

Definition classify_inlines (_ : inline_env) (l : list string) : inlines :=
  para_inlines l.

Theorem classify_inlines_locality :
  forall a b l, classify_inlines a l = classify_inlines b l.
Proof. reflexivity. Qed.

Lemma para_inlines_one :
  forall x, para_inlines [x] = parse_inline_line (strip_trailing_ws x).
Proof. reflexivity. Qed.

(*
Rules stated from text mode
===========================

Each takes the scan in text mode with nothing pending, `IText false`,
whatever came before, and says what the construct's bytes do to it.
*)

(** O2: a backslash and a punctuation byte add the byte to the text, and
    nothing else. *)
Theorem escape_in_text : forall c rest txt prev o,
  is_punct c = true ->
  iscan_str (String bslash (String c rest)) (IText false txt prev o)
  = iscan_str rest (IText false (txt ++ one c) (Some c) o).
Proof.
  intros c rest txt prev o Hc. cbn [iscan_str]. unfold istep. cbn [istep_at].
  unfold ilead. change (is_bslash bslash) with true. cbn [istep_at].
  rewrite Hc, (is_punct_not_ws c Hc). reflexivity.
Qed.

Local Lemma iscan_dash_run : forall n m txt prev o s,
  iscan_str (chars hyphen n ++ s) (IDash m txt prev o)
  = iscan_str s (IDash (n + m) txt prev o).
Proof.
  induction n as [|n IH]; intros m txt prev o s; [reflexivity|].
  cbn [chars append iscan_str]. unfold istep. cbn [istep_at]. unfold idash_step.
  rewrite Ascii.eqb_refl, IH. f_equal. f_equal. lia.
Qed.

(** Q5: a run of hyphens is cut whole.  The run ends at the first byte
    that is not a hyphen, the text gains `typography_dashes` of its
    length (`dashes`, when smart typography is on: `dashes_divide`), and
    that byte is read next.  A `}` is the exception: it takes the last
    hyphen back for a close marker (`idash_step`). *)
Theorem dash_run_in_text : forall n c rest txt prev o,
  Ascii.eqb c hyphen = false -> Ascii.eqb c rbrace = false ->
  iscan_str (chars hyphen (S n) ++ String c rest) (IText false txt prev o)
  = iscan_str (String c rest)
      (IText false (txt ++ typography_dashes (S n)) (Some hyphen) o).
Proof.
  intros n c rest txt prev o Hh Hr.
  change (iscan_str (chars hyphen (S n) ++ String c rest) (IText false txt prev o))
    with (iscan_str (chars hyphen n ++ String c rest) (IDash 1 txt prev o)).
  rewrite iscan_dash_run, Nat.add_1_r. cbn [iscan_str]. f_equal.
  unfold istep. cbn [istep_at]. unfold idash_step. rewrite Hh, Hr. reflexivity.
Qed.

(** Q5, for a run that ends its line. *)
Theorem dash_run_at_end : forall n txt prev o,
  iresolve (iscan_str (chars hyphen (S n)) (IText false txt prev o))
  = IText false (txt ++ typography_dashes (S n)) (Some hyphen) o.
Proof.
  intros n txt prev o.
  change (iscan_str (chars hyphen (S n)) (IText false txt prev o))
    with (iscan_str (chars hyphen n) (IDash 1 txt prev o)).
  rewrite <- (append_empty_r (chars hyphen n)), iscan_dash_run, Nat.add_1_r.
  reflexivity.
Qed.

Local Lemma iscan_open_run : forall k m vk o s,
  iscan_str (ticks k ++ s) (IOpen m vk o) = iscan_str s (IOpen (k + m) vk o).
Proof.
  induction k as [|k IH]; intros m vk o s; [reflexivity|].
  cbn [ticks append iscan_str]. unfold istep. cbn [istep_at].
  change (is_tick tick) with true. cbn iota. rewrite IH. do 2 f_equal. lia.
Qed.

Local Lemma iscan_verb_run : forall k n run txt vk o s,
  iscan_str (ticks k ++ s) (IVerb n run txt vk o)
  = iscan_str s (IVerb n (k + run) txt vk o).
Proof.
  induction k as [|k IH]; intros n run txt vk o s; [reflexivity|].
  cbn [ticks append iscan_str]. unfold istep. cbn [istep_at].
  change (is_tick tick) with true. cbn iota. rewrite IH. do 2 f_equal. lia.
Qed.

Local Lemma iscan_verb_body : forall body n run txt vk o,
  verb_safe_from n run body = true ->
  nonempty_str body = true -> ends_tick body = false ->
  iscan_str body (IVerb n run txt vk o)
  = IVerb n 0 (txt ++ ticks run ++ body) vk o.
Proof.
  induction body as [|c body IH]; intros n run txt vk o Hs Hne He; [discriminate|].
  cbn [iscan_str verb_safe_from] in *. unfold istep. cbn [istep_at].
  destruct (is_tick c) eqn:Ec.
  - destruct body as [|d body].
    { unfold ends_tick in He. cbn in He. congruence. }
    rewrite ends_tick_cons_nonempty in He.
    rewrite (IH n (S run) txt vk o Hs eq_refl He).
    unfold is_tick in Ec. apply Ascii.eqb_eq in Ec. subst c. rewrite ticks_succ_r.
    f_equal. rewrite !append_assoc. reflexivity.
  - apply andb_true_iff in Hs as [Hr Hs]. apply negb_true_iff in Hr. rewrite Hr.
    destruct body as [|d body]; [reflexivity|].
    rewrite ends_tick_cons_nonempty in He.
    rewrite (IH n 0 _ vk o Hs eq_refl He). cbn [ticks append]. f_equal.
    change (tpush txt (ticks run ++ one c)) with (txt ++ ticks run ++ one c).
    rewrite !append_assoc. reflexivity.
Qed.

(* An opening run and a body with no run of the same length: the scan is
   inside the verbatim, holding the body. *)
Local Lemma iscan_verb_span : forall n body s txt prev o,
  nonempty_str body = true -> starts_tick body = false ->
  ends_tick body = false -> verb_safe (S n) body = true ->
  iscan_str (ticks (S n) ++ body ++ s) (IText false txt prev o)
  = iscan_str s (IVerb (S n) 0 body VVerb (flush_text txt o)).
Proof.
  intros n body s txt prev o Hne Hs He Hsafe.
  change (iscan_str (ticks (S n) ++ body ++ s) (IText false txt prev o))
    with (iscan_str (ticks n ++ body ++ s) (IOpen 1 VVerb (flush_text txt o))).
  rewrite iscan_open_run, Nat.add_1_r.
  destruct body as [|d body]; [discriminate|]. cbn [starts_tick] in Hs.
  cbn [append iscan_str].
  replace (istep d (IOpen (S n) VVerb (flush_text txt o)))
    with (IVerb (S n) 0 (one d) VVerb (flush_text txt o))
    by (unfold istep; cbn [istep_at]; rewrite Hs; reflexivity).
  unfold verb_safe in Hsafe. cbn [verb_safe_from] in Hsafe. rewrite Hs in Hsafe.
  cbn [Nat.eqb negb andb] in Hsafe.
  destruct body as [|e body]; [reflexivity|].
  rewrite ends_tick_cons_nonempty in He.
  rewrite iscan_str_app, (iscan_verb_body _ _ _ _ _ _ Hsafe eq_refl He).
  reflexivity.
Qed.

(** V1: a run of backticks opens a verbatim, and the next run of the same
    length closes it.  `body` neither starts nor ends with a backtick, so
    the two runs are exactly the delimiters, and holds no run of their
    length (`verb_safe`).  The node's text is `trim_verb body` (V3).  The
    byte after the closer is read next; a `{` there may begin a raw
    format instead (R1). *)
Theorem verbatim_in_text : forall n body c rest txt prev o,
  nonempty_str body = true -> starts_tick body = false ->
  ends_tick body = false -> verb_safe (S n) body = true ->
  is_tick c = false -> Ascii.eqb c lbrace = false ->
  iscan_str (ticks (S n) ++ body ++ ticks (S n) ++ String c rest)
    (IText false txt prev o)
  = iscan_str (String c rest)
      (IText false "" (Some tick)
         (oemit (mk (Verbatim (trim_verb body))) (flush_text txt o))).
Proof.
  intros n body c rest txt prev o Hne Hs He Hsafe Hc Hb.
  rewrite (iscan_verb_span n body _ txt prev o Hne Hs He Hsafe).
  rewrite iscan_verb_run, Nat.add_0_r. cbn [iscan_str]. f_equal.
  unfold istep. cbn [istep_at]. rewrite Hc, Nat.eqb_refl, Hb. reflexivity.
Qed.

(** V1, for a verbatim that ends its paragraph. *)
Theorem verbatim_at_end : forall n body txt prev o,
  nonempty_str body = true -> starts_tick body = false ->
  ends_tick body = false -> verb_safe (S n) body = true ->
  ifinish_ostate
    (iscan_str (ticks (S n) ++ body ++ ticks (S n)) (IText false txt prev o))
  = oemit (mk (Verbatim (trim_verb body))) (flush_text txt o).
Proof.
  intros n body txt prev o Hne Hs He Hsafe.
  rewrite (iscan_verb_span n body _ txt prev o Hne Hs He Hsafe).
  rewrite <- (append_empty_r (ticks (S n))), iscan_verb_run, Nat.add_0_r.
  cbn [iscan_str ifinish_ostate iresolve]. unfold ifinish_ostate_flat.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

(*
The key connective
==================

Where a colon on a line pairs a label with what follows it, which is
`.project/keyed-blocks.md` sections 3.1 and 3.2.  The block layer asks
this of a line that would otherwise open a paragraph; both questions it
has to answer are inline ones -- what the scan still has open at a byte,
and how many nodes the text before that byte resolves to -- which is why
the test lives here and not beside the other line recognizers in
`Line.v`.
*)

(* The colon sits against its label: the byte before it is not
   whitespace, and a line-initial colon has no label at all. *)
Local Definition key_before (prev : option ascii) : bool :=
  match prev with None => false | Some c => negb (is_ws c) end.

(* And a space or the end of the line follows it.  A tab is neither, so
   this is spelled out rather than reusing `is_space`, which admits one. *)
Local Definition key_after (rest : string) : bool :=
  match rest with
  | EmptyString => true
  | String c _ => Ascii.eqb c " "%char
  end.

(* The line's split point: the label's source and the value's.  One
   left-to-right pass with the scan state carried alongside, so no byte
   is read twice and no candidate needs a lookahead.  `iscan_closed` is
   the "nothing open" test: a colon the scan is unsure about is not a
   split point and the pass goes on to the next, which is what sends
   `x{title="a: b"}y: z` to its second colon.

   An escaped colon is declined by that same test, a pending backslash
   being an open state, so `foo\: bar` needs no case of its own. *)
Local Fixpoint key_scan (s lbl : string) (prev : option ascii) (st : iscan)
  : option (string * string) :=
  match s with
  | EmptyString => None
  | String c rest =>
      if (Ascii.eqb c ":"%char && key_before prev && key_after rest
          && iscan_settled c st)%bool
      then Some (rev_string lbl, drop_leading_ws rest)
      else key_scan rest (String c lbl) (Some c) (istep c st)
  end.

(* The line is normalised first, which is what makes the answer
   independent of the indentation a container prefix leaves behind. *)
Definition key_point (l : string) : option (string * string) :=
  key_scan (drop_leading_ws l) EmptyString None istart.

(* Is the label one inline?  A fact about the *resolved* list, so it
   turns on the merge in `oresolve`: `it's` and `foo\: bar` are one run
   because of it, and ``x`y` `` is two because a verbatim span cannot
   merge with the text beside it. *)
Definition key_label_ok (lbl : string) : bool :=
  match para_inlines [lbl] with [_] => true | _ => false end.

(* The split, when the line is a key.  Only the first split point is
   tried: a label already two elements cannot come back to one, since
   collapsing two settled elements would take a construct opening before
   both, and that would have left the earlier point unsettled. *)
Definition key_split (l : string) : option (string * string) :=
  match key_point l with
  | Some (lbl, v) => if key_label_ok lbl then Some (lbl, v) else None
  | None => None
  end.

(* Leading whitespace is dropped before the scan, so a pad is invisible
   to the whole test.  `step_fuel_pad` is what needs it: a padded line
   and a shifted offset are the same descent, and a key opened by one
   has to be the key opened by the other. *)
Local Lemma key_point_ws_prefix :
  forall p l, is_blank p = true -> key_point (p ++ l) = key_point l.
Proof.
  intros p l Hp. unfold key_point.
  rewrite (drop_leading_ws_ws_prefix p l Hp). reflexivity.
Qed.

(* A label is never blank: the split rule asks the byte before the colon
   not to be whitespace, so the accumulator is headed by that byte.  The
   invariant is what the recursion has to carry, since the character is
   `prev` at the split and the head of the accumulator one step later. *)
Local Lemma key_scan_label_nonblank :
  forall s acc prev st r v,
    (forall c, prev = Some c -> is_ws c = false -> is_blank acc = false) ->
    key_scan s acc prev st = Some (r, v) -> nonblank r = true.
Proof.
  induction s as [|c rest IH]; intros acc prev st r v Hinv H; [discriminate|].
  cbn [key_scan] in H.
  destruct (Ascii.eqb c ":"%char && key_before prev && key_after rest
            && iscan_settled c st)%bool eqn:E; [|apply (IH (String c acc) (Some c)
      (istep c st) r v); [|exact H];
      intros c0 Hc0 Hws; injection Hc0 as <-;
      rewrite is_blank_cons, Hws; reflexivity].
  injection H as <- _.
  apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E _].
  apply andb_true_iff in E as [_ E].
  unfold key_before in E. destruct prev as [c0|]; [|discriminate].
  apply negb_true_iff in E.
  unfold nonblank. rewrite rev_blank, (Hinv c0 eq_refl E). reflexivity.
Qed.

Local Lemma key_point_label_nonblank :
  forall l lbl v, key_point l = Some (lbl, v) -> nonblank lbl = true.
Proof.
  intros l lbl v H. unfold key_point in H.
  refine (key_scan_label_nonblank _ _ _ _ _ _ _ H).
  intros c Hc. discriminate Hc.
Qed.

Local Lemma key_split_label_nonblank :
  forall l lbl v, key_split l = Some (lbl, v) -> nonblank lbl = true.
Proof.
  intros l lbl v H. unfold key_split in H.
  destruct (key_point l) as [[lbl0 v0]|] eqn:E; [|discriminate].
  destruct (key_label_ok lbl0); [|discriminate]. injection H as <- <-.
  exact (key_point_label_nonblank _ _ _ E).
Qed.

(* The state carried by [key_scan] is exactly the scan of the reversed
   accumulator it returns as the label.  This is the bridge between the
   test performed during the one-pass search and a statement about the
   returned label itself. *)
Local Lemma key_scan_label_settled :
  forall s acc prev st lbl v,
    st = iscan_str (rev_string acc) istart ->
    key_scan s acc prev st = Some (lbl, v) ->
    iscan_settled ":"%char (iscan_str lbl istart) = true.
Proof.
  induction s as [|c rest IH]; intros acc prev st lbl v Hst Hsplit.
  - discriminate.
  - cbn [key_scan] in Hsplit.
    destruct (Ascii.eqb c ":"%char && key_before prev && key_after rest
              && iscan_settled c st)%bool eqn:E.
    + apply andb_true_iff in E as [E Hsettled].
      apply andb_true_iff in E as [E _].
      apply andb_true_iff in E as [Ec _].
      apply Ascii.eqb_eq in Ec. subst c.
      injection Hsplit as <- _.
      rewrite <- Hst. exact Hsettled.
    + apply (IH (String c acc) (Some c) (istep c st) lbl v).
      * subst st. rewrite rev_string_cons, iscan_str_app.
        cbn [one iscan_str]. reflexivity.
      * exact Hsplit.
Qed.

Local Lemma key_point_label_settled :
  forall l lbl v,
    key_point l = Some (lbl, v) ->
    iscan_settled ":"%char (iscan_str lbl istart) = true.
Proof.
  intros l lbl v H. unfold key_point in H.
  eapply key_scan_label_settled; [reflexivity|exact H].
Qed.

Local Lemma key_split_label_settled :
  forall l lbl v,
    key_split l = Some (lbl, v) ->
    iscan_settled ":"%char (iscan_str lbl istart) = true.
Proof.
  intros l lbl v H. unfold key_split in H.
  destruct (key_point l) as [[lbl0 v0]|] eqn:E; [|discriminate].
  destruct (key_label_ok lbl0); [|discriminate].
  injection H as <- <-. eapply key_point_label_settled; exact E.
Qed.

Local Lemma key_split_label_one :
  forall l lbl v,
    key_split l = Some (lbl, v) ->
    exists x, para_inlines [lbl] = [x].
Proof.
  intros l lbl v H. unfold key_split in H.
  destruct (key_point l) as [[lbl0 v0]|] eqn:E; [|discriminate].
  destruct (key_label_ok lbl0) eqn:Hok; [|discriminate].
  injection H as <- <-. unfold key_label_ok in Hok.
  destruct (para_inlines [lbl0]) as [|x xs] eqn:Hils; [discriminate|].
  destruct xs as [|y ys]; [exists x; reflexivity|discriminate].
Qed.

(** A successful key split has one nonblank resolved label, and the scan
    of that label is settled with the connective colon known as the next
    byte.  Thus the block layer consumes only split points for which the
    inline layer has no open or undecided construct. *)
Theorem key_split_contract :
  forall l lbl v,
    key_split l = Some (lbl, v) ->
    nonblank lbl = true /\
    (exists x, para_inlines [lbl] = [x]) /\
    iscan_settled ":"%char (iscan_str lbl istart) = true.
Proof.
  intros l lbl v H. split.
  - exact (key_split_label_nonblank _ _ _ H).
  - split.
    + exact (key_split_label_one _ _ _ H).
    + exact (key_split_label_settled _ _ _ H).
Qed.

(* The same fact in the form the block layer wants: `open_kind` hands
   the arm the line already normalized. *)
Local Lemma key_point_drop_leading_ws :
  forall l, key_point (drop_leading_ws l) = key_point l.
Proof.
  intros l. unfold key_point. rewrite drop_leading_ws_idem. reflexivity.
Qed.

Lemma key_split_drop_leading_ws :
  forall l, key_split (drop_leading_ws l) = key_split l.
Proof.
  intros l. unfold key_split. rewrite key_point_drop_leading_ws. reflexivity.
Qed.

Lemma key_split_ws_prefix :
  forall p l, is_blank p = true -> key_split (p ++ l) = key_split l.
Proof.
  intros p l Hp. unfold key_split. rewrite (key_point_ws_prefix p l Hp).
  reflexivity.
Qed.

End WithTable.

(* Again, since closing the section dropped the one inside it. *)
Notation iscan := (iscan_g (Buf:=string)).
