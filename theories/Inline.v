(* ai-disclosure: ai-generated *)

(* The inline layer: the parser's within-line pass, and the canonical
   (renderable) view it inverts.

   The same two-sided shape as the block layer, one level down.  There,
   `Line.v` classifies a line and `Step.v` folds lines into blocks, while
   `Render.v`'s `cblock` describes the parser's image by the source data
   that determines it.  Here `parse_inline_line` is the pass, `cinline`
   is the image, and the two meet in `parse_inline_line_ci`.

   Nothing recognizes inline syntax yet: a line is one `Str`, which is
   what `Step.para_inlines` already did, and `para_inlines_one` /
   `para_inlines_cons2` still hold by `reflexivity`.  What this file adds
   is the shape the constructs in `.project/260811.inline-parser.md` need
   (escapes, verbatim, the delimiter table, brackets), fixed while it is
   still cheap to fix.

   Parser and renderer share the file because at this size a split would
   be three files of twenty lines.  It splits the way the block parser
   did once a side outgrows the other. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Strings Ast.
Import ListNotations.

Local Open Scope string_scope.

(*
Escapes
=======

A backslash escape is not a construct: `\*` and a bare `*` in a position
where nothing opens both parse to `Str "*"`, so the AST cannot tell them
apart and `cinline` gains no constructor.  What an escape is, is the
*spelling* a `CIStr` needs so that its text comes back unchanged, which
makes this a pair of string functions and one theorem relating them. *)

(* djot.js `pattPunctuation` (inline.ts:84): the ASCII punctuation
   blocks.  This is the set a backslash may escape, and it is deliberately
   wider than the set that ever *needs* escaping. *)
Definition is_punct (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((Nat.leb 33 n && Nat.leb n 47) || (Nat.leb 58 n && Nat.leb n 64)
   || (Nat.leb 91 n && Nat.leb n 96) || (Nat.leb 123 n && Nat.leb n 126))%bool.

(* The characters a `CIStr` must escape to survive reparsing.  Today only
   the backslash: nothing else has inline meaning yet.  Every construct
   that claims a delimiter character adds it here, and the two
   obligations below are what it has to keep true.

   The alternative, escaping every punctuation character unconditionally,
   would keep this constant and needs no obligation, at the cost of
   rendering `a, b` as `a\, b`.  djot.js escapes selectively (it renders
   `\,` back as a bare `,`), and matching that costs only the two lemmas. *)
Definition tick : ascii := "`"%char.
Definition is_tick (c : ascii) : bool := Ascii.eqb c tick.

(* The escape character itself, as opposed to the set of characters that
   need escaping.  The scanner must test *this* to detect a pending
   escape: `needs_escape` contains the backtick, and testing it here
   would make a bare backtick set the escape flag instead of opening a
   verbatim span. *)
Definition bslash : ascii := "\"%char.
Definition is_bslash (c : ascii) : bool := Ascii.eqb c bslash.

Definition needs_escape (c : ascii) : bool := (is_bslash c || is_tick c)%bool.

(* Obligation 1: an escaped character must be one the decoder accepts. *)
Lemma needs_escape_punct : forall c, needs_escape c = true -> is_punct c = true.
Proof.
  intros c H. unfold needs_escape, is_bslash, is_tick in H.
  apply orb_true_iff in H as [H|H]; apply Ascii.eqb_eq in H; subst; reflexivity.
Qed.

(* Obligation 2: the escape character escapes itself, or a text ending in
   a backslash would decode as an escape of whatever followed. *)
Lemma needs_escape_backslash : needs_escape "\"%char = true.
Proof. reflexivity. Qed.

(* Obligation 3: a backtick in a `Str` must not reach the scanner bare,
   or it would open a verbatim span instead of standing for itself.  This
   is the obligation every delimiter character will add. *)
Lemma needs_escape_tick : forall c, is_tick c = true -> needs_escape c = true.
Proof. intros c H. unfold needs_escape. rewrite H. apply orb_true_r. Qed.

Fixpoint escape_str (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if needs_escape c
      then String "\"%char (String c (escape_str rest))
      else String c (escape_str rest)
  end.

(*
Canonical inlines
=================
*)

(* One line's inline content, described by the source that determines it.
   One constructor per inline construct the roundtrip covers, exactly as
   `cblock` carries one per block construct. *)
Inductive cinline : Type :=
  | CIStr (s : string).

(* The last byte of `s`, or `prev` when `s` is empty. *)
Fixpoint str_last (s : string) (prev : option ascii) : option ascii :=
  match s with
  | EmptyString => prev
  | String c rest => str_last rest (Some c)
  end.

(* Source text, threading the byte to the left of what is being emitted
   (`None` at the start of a line).

   Not `concat (map ...)`: a delimiter's spelling depends on its
   neighbours, so `Emph [CIStr "b"]` renders `_b_` at a line start but
   `{_b_}` inside `a_b_c`, and a context-free per-element function
   cannot say which.  One byte on each side is the whole of the context
   any djot rule consults, since `can_open` and `can_close` each test a
   single neighbouring character (djot.js `inline.ts:110-112`); the byte
   to the right is available from the unconsumed tail. *)
Fixpoint ci_text (prev : option ascii) (cis : list cinline) : string :=
  match cis with
  | [] => EmptyString
  | CIStr s :: rest =>
      let e := escape_str s in e ++ ci_text (str_last e prev) rest
  end.

Definition ci_line (cis : list cinline) : string := ci_text None cis.

(* ...and the AST the parser builds from that text. *)
Definition ci_ast (ci : cinline) : node inline :=
  match ci with CIStr s => mk (Str s) end.

Definition ci_inlines (cis : list cinline) : inlines := map ci_ast cis.

Lemma ci_line_nil : ci_line [] = EmptyString.
Proof. reflexivity. Qed.

Lemma ci_line_str : forall s, ci_line [CIStr s] = escape_str s.
Proof. intros s. unfold ci_line. cbn [ci_text]. apply append_empty_r. Qed.

(*
Renderability
-------------
*)

(* A `Str` carrying no text would not have been emitted, and one carrying
   a newline is not within-line content. *)
Definition ci_ok (ci : cinline) : bool :=
  match ci with CIStr s => nonempty_str s && no_nl s end.

(* Two adjacent `CIStr` would have parsed as one, the `no_adjacent_str`
   of `Wf.v` moved to the canonical view.  With `CIStr` the only
   constructor this forces a line to be a single element; it stops being
   degenerate at the first construct that is not a `Str`. *)
Fixpoint no_adjacent_ci_str (cis : list cinline) : bool :=
  match cis with
  | CIStr _ :: ((CIStr _ :: _) as rest) => false && no_adjacent_ci_str rest
  | _ => true
  end.

Definition cis_ok (cis : list cinline) : bool :=
  forallb ci_ok cis && no_adjacent_ci_str cis.

(* Nonemptiness of a line's content is not a separate obligation: the
   block layer already asks that a paragraph's rendered lines are
   nonblank, and only `[]` renders blank. *)
Lemma cis_nonempty_of_line :
  forall cis, nonempty_str (ci_line cis) = true -> nonempty cis = true.
Proof.
  intros [|c rest] H; [rewrite ci_line_nil in H; discriminate | reflexivity].
Qed.

(* The form the block layer supplies it in: `para_ok` and `heading_ok`
   both carry `forallb line_ok` over the rendered lines. *)
Lemma cis_nonempty_of_lines :
  forall lss,
    forallb line_ok (map ci_line lss) = true ->
    forallb nonempty lss = true.
Proof.
  induction lss as [|cis rest IH]; [reflexivity|].
  cbn [map forallb]. intros H. apply andb_true_iff in H as [Hl Hr].
  rewrite (cis_nonempty_of_line cis
             (nonblank_nonempty _ (line_ok_nonblank _ Hl))).
  exact (IH Hr).
Qed.

(*
The inline pass
===============
*)

(* Verbatim content is trimmed of one padding space at each end, but only
   where it sits against a backtick (djot.js `trimVerbatim`, parse.ts:57).
   A space not adjacent to a backtick is content: `` ` a ` `` really is
   " a ".  Reversed, "ends with a backtick then a space" is "starts with a
   space then a backtick", so one function does both ends. *)

Definition starts_tick (s : string) : bool :=
  match s with String c _ => is_tick c | _ => false end.

Definition strip_pad (s : string) : string :=
  match s with
  | String c rest =>
      if (Ascii.eqb c " "%char && starts_tick rest)%bool then rest else s
  | EmptyString => s
  end.

Definition trim_verb (s : string) : string :=
  rev_string (strip_pad (rev_string (strip_pad s))).

Fixpoint ticks (n : nat) : string :=
  match n with 0 => EmptyString | S k => String tick (ticks k) end.

(*
The scanner
-----------

One character at a time, structurally recursive on the remaining input.
That is not an accident of style: it is what makes "the scanner never
revisits a position" definitional rather than a theorem, which is the
`no-backtracking` half of Phase 3 obtained for free (see
`.project/260811.inline-parser.md` §2.4).  It also matches djot.js's
`feed`, which is a position-at-a-time loop over a mode flag.

A verbatim closer is a run of *exactly* the opening width, so a run
cannot be resolved until the character after it arrives; that is why
`IVerb` carries a pending run count rather than closing eagerly.  A run
of the wrong width is content, which is how `` ` `` ` `` holds two
backticks inside a one-backtick fence. *)

Inductive iscan : Type :=
  (* accumulating literal text; `esc` is a pending backslash *)
  | IText (esc : bool) (txt : string) (out : inlines)
  (* counting an opening backtick run *)
  | IOpen (n : nat) (out : inlines)
  (* inside a width-`n` verbatim, with `run` unresolved trailing ticks *)
  | IVerb (n run : nat) (txt : string) (out : inlines).

Definition one (c : ascii) : string := String c EmptyString.

Definition flush_text (txt : string) (out : inlines) : inlines :=
  if nonempty_str txt then mk (Str txt) :: out else out.

Definition istep (c : ascii) (st : iscan) : iscan :=
  match st with
  | IText true txt out =>
      IText false (txt ++ (if is_punct c then one c
                           else String "\"%char (one c)))%string out
  | IText false txt out =>
      if is_bslash c then IText true txt out
      else if is_tick c then IOpen 1 (flush_text txt out)
      else IText false (txt ++ one c)%string out
  | IOpen n out =>
      if is_tick c then IOpen (S n) out else IVerb n 0 (one c) out
  | IVerb n run txt out =>
      if is_tick c then IVerb n (S run) txt out
      else if Nat.eqb run n
      then IText false (one c) (mk (Verbatim (trim_verb txt)) :: out)
      else IVerb n 0 (txt ++ ticks run ++ one c)%string out
  end.

(* End of line.  An unclosed verbatim closes here, as djot.js does in
   `getMatches`.  A pending backslash is a literal backslash, which is
   djoths's reading; djot.js makes it a hard break, an already-logged
   disagreement (`escapes.test:30`).  Neither can arise from a canonical
   rendering, since `escape_str` never emits a bare backslash. *)
Definition ifinish (st : iscan) : inlines :=
  List.rev
    match st with
    | IText true txt out =>
        flush_text (txt ++ String "\"%char EmptyString)%string out
    | IText false txt out => flush_text txt out
    | IOpen _ out => mk (Verbatim EmptyString) :: out
    | IVerb n run txt out =>
        if Nat.eqb run n
        then mk (Verbatim (trim_verb txt)) :: out
        else mk (Verbatim (trim_verb (txt ++ ticks run)%string)) :: out
    end.

Fixpoint iscan_str (s : string) (st : iscan) : iscan :=
  match s with
  | EmptyString => st
  | String c rest => iscan_str rest (istep c st)
  end.

(* Parse one line's inline content.  Every construct of
   `.project/260811.inline-parser.md` lands here. *)
Definition parse_inline_line (s : string) : inlines :=
  ifinish (iscan_str s (IText false EmptyString [])).

(* Canonical text never opens a verbatim: `needs_escape` claims the
   backtick, so `escape_str` emits none bare.  The scanner therefore
   stays in `IText` throughout, and this is the whole of what the
   roundtrip needs from it today. *)
Lemma iscan_escape :
  forall s txt out,
    iscan_str (escape_str s) (IText false txt out)
    = IText false (txt ++ s)%string out.
Proof.
  induction s as [|c rest IH]; intros txt out.
  - cbn [escape_str iscan_str]. rewrite append_empty_r. reflexivity.
  - cbn [escape_str]. destruct (needs_escape c) eqn:Hc.
    + simpl. rewrite (needs_escape_punct c Hc).
      rewrite IH, append_assoc. reflexivity.
    + cbn [iscan_str istep].
      replace (is_bslash c) with false
        by (destruct (is_bslash c) eqn:Hb; [|reflexivity];
            unfold needs_escape in Hc; rewrite Hb in Hc; discriminate).
      replace (is_tick c) with false
        by (destruct (is_tick c) eqn:Ht;
            [rewrite (needs_escape_tick c Ht) in Hc; discriminate | reflexivity]).
      rewrite IH, append_assoc. reflexivity.
Qed.

(*
The scan is productive
----------------------

`Wf.v` needs that a nonempty line yields at least one inline, which the
old one-`Str`-per-line parser had by construction and a scanner does not.
The initial state is deliberately *un*productive, since empty input must
give no inlines; one character suffices. *)

Definition iscan_productive (st : iscan) : bool :=
  match st with
  | IText false txt out => (nonempty_str txt || nonempty out)%bool
  | _ => true
  end.

Lemma nonempty_rev : forall (l : inlines), nonempty (List.rev l) = nonempty l.
Proof.
  intros [|n l]; [reflexivity|].
  cbn [List.rev nonempty]. destruct (List.rev l ++ [n])%list eqn:E; [|reflexivity].
  destruct (List.rev l); discriminate.
Qed.

Lemma iscan_productive_step :
  forall c st, iscan_productive st = true -> iscan_productive (istep c st) = true.
Proof.
  intros c [[] txt out|n out|n run txt out] H; cbn [istep iscan_productive].
  - destruct (is_punct c); cbn [iscan_productive];
      rewrite ?nonempty_str_append_r; try reflexivity;
      apply orb_true_iff; left;
      destruct txt; reflexivity.
  - destruct (is_bslash c); [reflexivity|].
    destruct (is_tick c); [reflexivity|].
    cbn [iscan_productive]. apply orb_true_iff. left.
    destruct txt; reflexivity.
  - destruct (is_tick c); reflexivity.
  - destruct (is_tick c); [reflexivity|].
    destruct (Nat.eqb run n); cbn [iscan_productive]; [|reflexivity].
    apply orb_true_iff. left. reflexivity.
Qed.

Lemma iscan_productive_str :
  forall s st, iscan_productive st = true ->
  iscan_productive (iscan_str s st) = true.
Proof.
  induction s as [|c rest IH]; intros st H; [exact H|].
  cbn [iscan_str]. apply IH, iscan_productive_step, H.
Qed.

Lemma iscan_productive_finish :
  forall st, iscan_productive st = true -> nonempty (ifinish st) = true.
Proof.
  intros [[] txt out|n out|n run txt out] H; unfold ifinish;
    rewrite nonempty_rev; unfold flush_text.
  - destruct (nonempty_str (txt ++ String "\"%char EmptyString)) eqn:E;
      [reflexivity|].
    destruct txt; discriminate.
  - cbn [iscan_productive] in H. apply orb_true_iff in H as [H|H].
    + rewrite H. reflexivity.
    + destruct (nonempty_str txt); [reflexivity | exact H].
  - reflexivity.
  - destruct (Nat.eqb run n); reflexivity.
Qed.

Lemma iscan_productive_first :
  forall c, iscan_productive (istep c (IText false EmptyString [])) = true.
Proof.
  intros c. cbn [istep].
  destruct (is_bslash c); [reflexivity|].
  destruct (is_tick c); reflexivity.
Qed.

Lemma parse_inline_line_nonempty :
  forall s, nonempty_str s = true -> nonempty (parse_inline_line s) = true.
Proof.
  intros [|c rest] H; [discriminate|].
  unfold parse_inline_line. cbn [iscan_str].
  apply iscan_productive_finish, iscan_productive_str, iscan_productive_first.
Qed.

Lemma parse_inline_line_escape :
  forall s, nonempty_str s = true ->
  parse_inline_line (escape_str s) = [mk (Str s)].
Proof.
  intros s H. unfold parse_inline_line. rewrite iscan_escape.
  change (EmptyString ++ s)%string with s.
  unfold ifinish, flush_text. rewrite H. reflexivity.
Qed.

(* A paragraph's lines, in order, into inlines: each line's content, with
   `SoftBreak` between.  Trailing whitespace is stripped at the end of a
   paragraph but kept on interior lines (observed djot.js/djoths
   behaviour on para.test, and djot.js's own trailing-softbreak trim in
   `inline.ts` getMatches). *)
Fixpoint para_inlines (l : list string) : inlines :=
  match l with
  | [] => []
  | [x] => parse_inline_line (strip_trailing_ws x)
  | x :: rest => (parse_inline_line x ++ mk SoftBreak :: para_inlines rest)%list
  end.

Lemma para_inlines_one :
  forall x, para_inlines [x] = parse_inline_line (strip_trailing_ws x).
Proof. reflexivity. Qed.

Lemma para_inlines_cons2 :
  forall x y rest,
    para_inlines (x :: y :: rest) =
    (parse_inline_line x ++ mk SoftBreak :: para_inlines (y :: rest))%list.
Proof. reflexivity. Qed.

(* The canonical view's paragraph, laid out the same way. *)
Fixpoint ci_para (lss : list (list cinline)) : inlines :=
  match lss with
  | [] => []
  | [cis] => ci_inlines cis
  | cis :: rest => (ci_inlines cis ++ mk SoftBreak :: ci_para rest)%list
  end.

Lemma ci_para_one : forall cis, ci_para [cis] = ci_inlines cis.
Proof. reflexivity. Qed.

Lemma ci_para_cons2 :
  forall cis cis2 rest,
    ci_para (cis :: cis2 :: rest)
    = (ci_inlines cis ++ mk SoftBreak :: ci_para (cis2 :: rest))%list.
Proof. reflexivity. Qed.

(*
The pass inverts the view
=========================
*)

(** Parsing a canonical line's text gives back its inlines. *)
Lemma parse_inline_line_ci :
  forall cis, cis_ok cis = true -> nonempty cis = true ->
  parse_inline_line (ci_line cis) = ci_inlines cis.
Proof.
  intros [|c rest] Hok Hne; [discriminate|].
  destruct c as [s]. destruct rest as [|c2 rest'].
  - unfold ci_inlines. cbn [map ci_ast].
    rewrite ci_line_str. apply parse_inline_line_escape.
    unfold cis_ok in Hok. cbn [forallb ci_ok] in Hok.
    apply andb_true_iff in Hok as [Hok _]. apply andb_true_iff in Hok as [Hok _].
    apply andb_true_iff in Hok as [Hok _]. exact Hok.
  - destruct c2 as [s2]. unfold cis_ok in Hok.
    cbn [no_adjacent_ci_str] in Hok. rewrite andb_false_r in Hok. discriminate.
Qed.

(** The same, a paragraph at a time.  The last hypothesis is `para_ok`'s
    trailing-whitespace conjunct: `para_inlines` strips the final line,
    so the two agree exactly when there is nothing to strip. *)
Lemma para_inlines_ci_para :
  forall lss,
    forallb cis_ok lss = true ->
    forallb nonempty lss = true ->
    strip_trailing_ws (last (map ci_line lss) EmptyString)
      = last (map ci_line lss) EmptyString ->
    para_inlines (map ci_line lss) = ci_para lss.
Proof.
  induction lss as [|cis rest IH]; intros Hok Hne Hlast; [reflexivity|].
  cbn [forallb] in Hok, Hne.
  apply andb_true_iff in Hok as [Hc Hr].
  apply andb_true_iff in Hne as [Hn Hnr].
  destruct rest as [|cis2 rest'].
  - cbn [map last] in Hlast |- *.
    rewrite para_inlines_one, Hlast.
    change (parse_inline_line (ci_line cis) = ci_para [cis]).
    rewrite ci_para_one. apply parse_inline_line_ci; assumption.
  - cbn [map] in *.
    rewrite para_inlines_cons2, ci_para_cons2.
    rewrite <- (parse_inline_line_ci cis Hc Hn).
    unfold parse_inline_line. cbn [app].
    f_equal. f_equal.
    apply IH; [exact Hr | exact Hnr |].
    rewrite last_cons_nonnil in Hlast by discriminate. exact Hlast.
Qed.

(*
The renderer
============
*)

(* Recover the lines of a paragraph from its inlines: `Str` extends the
   current line, `SoftBreak` ends it. *)
Fixpoint inline_lines (ils : inlines) (cur : string) : list string :=
  match ils with
  | [] => [cur]
  | Node _ _ (Str s) :: rest => inline_lines rest (cur ++ escape_str s)
  | Node _ _ SoftBreak :: rest => cur :: inline_lines rest EmptyString
  | _ :: rest => inline_lines rest cur
  end.

Lemma inline_lines_softbreak :
  forall rest cur,
    inline_lines (mk SoftBreak :: rest) cur = cur :: inline_lines rest EmptyString.
Proof. reflexivity. Qed.

(** Rendering a canonical line's inlines appends its text and consumes
    nothing else, which is what makes the paragraph case an induction. *)
Lemma inline_lines_ci_inlines :
  forall cis cur rest,
    cis_ok cis = true -> nonempty cis = true ->
    inline_lines (ci_inlines cis ++ rest)%list cur
    = inline_lines rest (cur ++ ci_line cis).
Proof.
  intros [|c cs] cur rest Hok Hne; [discriminate|].
  destruct c as [s]. destruct cs as [|c2 cs'].
  - unfold ci_inlines. cbn [map ci_ast app inline_lines].
    rewrite ci_line_str. reflexivity.
  - destruct c2 as [s2]. unfold cis_ok in Hok.
    cbn [no_adjacent_ci_str] in Hok. rewrite andb_false_r in Hok. discriminate.
Qed.

Lemma inline_lines_ci_para :
  forall rest cis cur,
    forallb cis_ok (cis :: rest) = true ->
    forallb nonempty (cis :: rest) = true ->
    inline_lines (ci_para (cis :: rest)) cur
    = (cur ++ ci_line cis) :: map ci_line rest.
Proof.
  induction rest as [|cis2 rest' IH]; intros cis cur Hok Hne;
    cbn [forallb] in Hok, Hne;
    apply andb_true_iff in Hok as [Hc Hr];
    apply andb_true_iff in Hne as [Hn Hnr].
  - rewrite ci_para_one. cbn [map].
    rewrite <- (app_nil_r (ci_inlines cis)).
    rewrite inline_lines_ci_inlines by assumption.
    reflexivity.
  - rewrite ci_para_cons2.
    rewrite inline_lines_ci_inlines by assumption.
    rewrite inline_lines_softbreak.
    rewrite IH by assumption.
    reflexivity.
Qed.

(** The renderer emits exactly the canonical lines. *)
Corollary inline_lines_ci :
  forall lss,
    forallb cis_ok lss = true -> forallb nonempty lss = true ->
    nonempty lss = true ->
    inline_lines (ci_para lss) EmptyString = map ci_line lss.
Proof.
  intros [|cis rest] Hok Hne Hlss; [discriminate|].
  rewrite inline_lines_ci_para by assumption. reflexivity.
Qed.

(*
Escapes, pinned
===============
*)

(* The scanner accepts any punctuation after a backslash... *)
Example escaped_punct_literal : parse_inline_line "\*" = [mk (Str "*")].
Proof. reflexivity. Qed.

(* ...and leaves a backslash before anything else alone. *)
Example escaped_nonpunct_literal : parse_inline_line "\a" = [mk (Str "\a")].
Proof. reflexivity. Qed.

(* A backtick in a `Str` is escaped, so it does not open a verbatim... *)
Example escaped_tick_literal : parse_inline_line "\`a\`" = [mk (Str "`a`")].
Proof. reflexivity. Qed.

(* ...while a bare one does, and a run of the wrong width is content. *)
Example verbatim_basic : parse_inline_line "`a`" = [mk (Verbatim "a")].
Proof. reflexivity. Qed.

Example verbatim_wrong_width_is_content :
  parse_inline_line "` `` `" = [mk (Verbatim "``")].
Proof. reflexivity. Qed.

Example verbatim_unclosed_closes_at_eol :
  parse_inline_line "`a" = [mk (Verbatim "a")].
Proof. reflexivity. Qed.

(* The encoder emits only what `needs_escape` names, which is why a
   comma renders bare where a backslash does not.  Matching djot.js,
   which renders `\,` back as `,`. *)
Example escape_backslash : escape_str "a\b" = "a\\b".
Proof. reflexivity. Qed.

Example escape_leaves_punct : escape_str "a,*b" = "a,*b".
Proof. reflexivity. Qed.
