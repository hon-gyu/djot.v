(* Byte-string utilities and their lemmas: whitespace, reversal, line
   splitting and joining, the source-line table that resolves spans to
   byte offsets, and small list helpers. *)

From Stdlib Require Import String Ascii List Bool Lia.
From Stdlib Require DecimalString.
From DjotV Require Import Ast.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope char_scope.

(*
Whitespace and blank lines
==========================
*)

(* Intra-line whitespace: space, tab, CR.  Not LF: newlines separate
   lines and are never content. *)
Definition is_ws (c : ascii) : bool :=
  Ascii.eqb c " " || Ascii.eqb c "009" || Ascii.eqb c "013".

(* A line is blank when it is empty or all whitespace. *)
Fixpoint is_blank (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => is_ws c && is_blank s'
  end.

Lemma is_blank_cons :
  forall c s, is_blank (String c s) = (is_ws c && is_blank s)%bool.
Proof. reflexivity. Qed.

(* About content, where `nonempty_str` is about length: a line of spaces
   is nonempty but blank. *)
Definition nonblank (l : string) : bool := negb (is_blank l).

(*
Shape helpers
=============
*)

(* Decidable "has at least one element", for lists and for strings. *)
Definition nonempty {A : Type} (l : list A) : bool :=
  match l with [] => false | _ => true end.

Definition nonempty_str (s : string) : bool :=
  match s with EmptyString => false | _ => true end.

Lemma nonempty_str_intro :
  forall s, s <> EmptyString -> nonempty_str s = true.
Proof. 
    destruct s.
    - congruence.
    - reflexivity.
Qed.

Lemma nonblank_nonempty :
  forall s, is_blank s = false -> nonempty_str s = true.
Proof. 
    destruct s.
    all: simpl.
    all: try congruence.
Qed.


Local Lemma nonempty_app_singleton :
  forall {A : Type} (l : list A) (x : A), nonempty (l ++ [x])%list = true.
Proof. intros A l x. destruct l. all: reflexivity. Qed.

(* Decimal rendering, for heading levels and identifier disambiguators. *)
Definition nat_str (n : nat) : string :=
  DecimalString.NilZero.string_of_uint (Nat.to_uint n).

Lemma forallb_rev :
  forall {A : Type} (f : A -> bool) (l : list A),
    forallb f (rev l) = forallb f l.
Proof.
  intros A f l.
  induction l as [|x l IH]; simpl.
  - reflexivity.
  - rewrite forallb_app, IH. simpl.
    destruct (f x), (forallb f l); reflexivity.
Qed.

(*
Append and reverse
==================
*)

Lemma append_empty_r : forall s, s ++ "" = s.
Proof.
  induction s as [|c s IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma append_assoc : forall a b c, (a ++ b) ++ c = a ++ (b ++ c).
Proof.
  induction a as [|x a IH]; intros; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

(* String reversal, accumulator-style so it is structurally recursive.
   It defines strip_trailing_ws by drop_leading_ws, and lets split_lines
   build lines front to back. *)
Fixpoint rev_string_aux (s acc : string) : string :=
  match s with
  | EmptyString => acc
  | String c s' => rev_string_aux s' (String c acc)
  end.

Definition rev_string (s : string) : string := rev_string_aux s EmptyString.

Local Lemma rev_aux_app :
  forall s acc, rev_string_aux s acc = rev_string s ++ acc.
Proof.
  induction s as [|c s IH]; intros acc; simpl.
  - reflexivity.
  - rewrite IH. unfold rev_string. simpl. rewrite (IH (String c "")).
    rewrite append_assoc. reflexivity.
Qed.

Lemma rev_string_cons :
  forall c s, rev_string (String c s) = rev_string s ++ String c "".
Proof.
  intros c s. unfold rev_string. simpl. apply rev_aux_app.
Qed.

Lemma rev_string_app :
  forall a b, rev_string (a ++ b) = rev_string b ++ rev_string a.
Proof.
  induction a as [|c a IH]; intros b; simpl.
  - rewrite append_empty_r. reflexivity.
  - rewrite !rev_string_cons, IH, append_assoc. reflexivity.
Qed.

Lemma rev_string_involutive : forall s, rev_string (rev_string s) = s.
Proof.
  induction s as [|c s IH].
  - reflexivity.
  - rewrite rev_string_cons, rev_string_app, IH. reflexivity.
Qed.

Local Lemma rev_aux_length :
  forall s acc,
    String.length (rev_string_aux s acc) =
    (String.length s + String.length acc)%nat.
Proof.
  induction s as [|c s IH]; intros acc; simpl.
  - reflexivity.
  - rewrite IH. simpl. lia.
Qed.

Local Lemma rev_length :
  forall s, String.length (rev_string s) = String.length s.
Proof.
  intros s. unfold rev_string. rewrite rev_aux_length. simpl. lia.
Qed.

Local Lemma rev_aux_blank :
  forall s acc, is_blank (rev_string_aux s acc) = (is_blank s && is_blank acc)%bool.
Proof.
  induction s as [|c s IH]; intros acc; simpl.
  - reflexivity.
  - rewrite IH. simpl.
    destruct (is_ws c), (is_blank s), (is_blank acc); reflexivity.
Qed.

Lemma rev_blank : forall s, is_blank (rev_string s) = is_blank s.
Proof.
  intros s. unfold rev_string. rewrite rev_aux_blank. simpl.
  apply andb_true_r.
Qed.

(*
Leading and trailing whitespace
===============================
*)

(* Drop a leading run of whitespace. *)
Fixpoint drop_leading_ws (s : string) : string :=
  match s with
  | String c s' => if is_ws c then drop_leading_ws s' else s
  | EmptyString => EmptyString
  end.

(* The column of a line's first non-whitespace character.  List-item
   continuation is stated against it. *)
Fixpoint indent_of (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => if is_ws c then S (indent_of s') else 0
  end.

(* Drop a trailing run of whitespace, by reversing.  The parser applies it
   to a paragraph's last line; `Render.para_ok` requires it to be the
   identity there. *)
Definition strip_trailing_ws (s : string) : string :=
  rev_string (drop_leading_ws (rev_string s)).

(* Drop a leading run of whitespace, but no more than `n` characters of
   it.  A container whose content is verbatim text removes its own column
   from every line: a line indented less keeps none of its indent, and a
   line indented more keeps the difference. *)
Fixpoint drop_ws_upto (n : nat) (s : string) : string :=
  match n, s with
  | S n', String c s' => if is_ws c then drop_ws_upto n' s' else s
  | _, _ => s
  end.

Local Lemma drop_ws_upto_0 : forall s, drop_ws_upto 0 s = s.
Proof. destruct s; reflexivity. Qed.

Lemma map_drop_ws_upto_0 : forall ls, map (drop_ws_upto 0) ls = ls.
Proof.
  induction ls as [|l ls IH]; [reflexivity|].
  cbn [map]. rewrite drop_ws_upto_0, IH. reflexivity.
Qed.

(* The two ways of reaching a nested line agree on it: `n` more columns
   of offset to strip and `n` more columns of blank prefix cancel. *)
Lemma drop_ws_upto_ws_prefix :
  forall p n s,
    is_blank p = true ->
    drop_ws_upto (String.length p + n) (p ++ s) = drop_ws_upto n s.
Proof.
  induction p as [|c p IH]; intros n s Hp; [reflexivity|].
  rewrite is_blank_cons in Hp. apply andb_true_iff in Hp as [Hc Hp].
  cbn [String.length append Nat.add drop_ws_upto]. rewrite Hc. apply IH; exact Hp.
Qed.

Lemma length_append :
  forall a b, String.length (a ++ b) = String.length a + String.length b.
Proof. induction a as [|c a IH]; intros b; cbn; [reflexivity|rewrite IH; reflexivity]. Qed.

(* Dropping whitespace never lengthens a string. *)
Lemma drop_leading_ws_length :
  forall s, String.length (drop_leading_ws s) <= String.length s.
Proof.
  induction s as [|c s IH]; simpl; [lia|].
  destruct (is_ws c); [lia | simpl; lia].
Qed.

Local Lemma drop_leading_ws_nonempty :
  forall s, is_blank s = false -> drop_leading_ws s <> EmptyString.
Proof.
  induction s as [|c s IH]; intros H.
  - discriminate.
  - rewrite is_blank_cons in H. cbn [drop_leading_ws].
    destruct (is_ws c) eqn:E.
    + apply IH. rewrite andb_true_l in H. exact H.
    + discriminate.
Qed.

(* Dropping leading whitespace preserves blankness. *)
Local Lemma is_blank_drop_leading_ws :
  forall s, is_blank (drop_leading_ws s) = is_blank s.
Proof.
  induction s as [|c s IH]; [reflexivity|].
  cbn [drop_leading_ws]. destruct (is_ws c) eqn:E.
  - rewrite IH, is_blank_cons, E. reflexivity.
  - reflexivity.
Qed.

Lemma drop_leading_ws_idem :
  forall s, drop_leading_ws (drop_leading_ws s) = drop_leading_ws s.
Proof.
  induction s as [|c s' IH]; [reflexivity|].
  cbn [drop_leading_ws]. destruct (is_ws c) eqn:E; [exact IH|].
  cbn [drop_leading_ws]. rewrite E. reflexivity.
Qed.

(* The converse: what drop_leading_ws dropped is an all-whitespace prefix. *)
Lemma drop_leading_ws_split :
  forall l, exists pre, is_blank pre = true /\ l = pre ++ drop_leading_ws l.
Proof.
  induction l as [|c l IH]; [exists EmptyString; split; reflexivity|].
  cbn [drop_leading_ws]. destruct (is_ws c) eqn:Ec.
  - destruct IH as (pre & Hpre & Hl). exists (String c pre).
    split; [rewrite is_blank_cons, Ec; exact Hpre|].
    cbn [append]. rewrite <- Hl. reflexivity.
  - exists EmptyString. split; reflexivity.
Qed.

(* Past the first non-whitespace character nothing more is dropped. *)
Lemma drop_leading_ws_app_nonblank : forall a b,
  drop_leading_ws a <> EmptyString -> drop_leading_ws (a ++ b) = drop_leading_ws a ++ b.
Proof.
  induction a as [|c a IH]; intros b H; [contradiction|].
  cbn [append drop_leading_ws] in *. destruct (is_ws c); [apply IH, H|reflexivity].
Qed.

(* An all-whitespace prefix is invisible to drop_leading_ws, is_blank and
   indent_of: they scan through it into `l`. *)
Lemma drop_leading_ws_ws_prefix :
  forall p l, is_blank p = true -> drop_leading_ws (p ++ l) = drop_leading_ws l.
Proof.
  induction p as [|c p IH]; intros l H; [reflexivity|].
  cbn [is_blank] in H. apply andb_true_iff in H as [Hc Hp].
  change (String c p ++ l) with (String c (p ++ l)).
  cbn [drop_leading_ws]. rewrite Hc. apply IH, Hp.
Qed.

Lemma is_blank_ws_prefix :
  forall p l, is_blank p = true -> is_blank (p ++ l) = is_blank l.
Proof.
  induction p as [|c p IH]; intros l H; [reflexivity|].
  cbn [is_blank] in H. apply andb_true_iff in H as [Hc Hp].
  change (String c p ++ l) with (String c (p ++ l)).
  rewrite is_blank_cons, Hc. cbn [andb]. apply IH, Hp.
Qed.

Lemma indent_of_ws_prefix :
  forall p l, is_blank p = true ->
  indent_of (p ++ l) = String.length p + indent_of l.
Proof.
  induction p as [|c p IH]; intros l H; [reflexivity|].
  cbn [is_blank] in H. apply andb_true_iff in H as [Hc Hp].
  change (String c p ++ l) with (String c (p ++ l)).
  cbn [indent_of]. rewrite Hc. cbn [String.length]. rewrite (IH l Hp).
  reflexivity.
Qed.

Local Lemma strip_trailing_ws_nonempty :
  forall s, is_blank s = false -> nonempty_str (strip_trailing_ws s) = true.
Proof.
  intros s H. unfold strip_trailing_ws.
  apply nonempty_str_intro.
  intros Hrev.
  assert (Hd : drop_leading_ws (rev_string s) <> EmptyString).
  { apply drop_leading_ws_nonempty. rewrite rev_blank. exact H. }
  apply Hd.
  apply (f_equal String.length) in Hrev.
  rewrite rev_length in Hrev. simpl in Hrev.
  destruct (drop_leading_ws (rev_string s)); [reflexivity | discriminate].
Qed.

(* A string drop_leading_ws leaves alone does not start with whitespace. *)
Lemma drop_leading_ws_fixed : forall h t,
  drop_leading_ws (String h t) = String h t -> is_ws h = false.
Proof.
  intros h t H. cbn [drop_leading_ws] in H. destruct (is_ws h) eqn:E; [|reflexivity].
  exfalso. pose proof (drop_leading_ws_length t) as Hl. rewrite H in Hl.
  cbn in Hl. lia.
Qed.

(* A string strip_trailing_ws leaves alone is empty or ends in a
   non-whitespace character. *)
Lemma strip_trailing_last : forall s,
  strip_trailing_ws s = s ->
  s = EmptyString \/ exists x z, s = x ++ String z EmptyString /\ is_ws z = false.
Proof.
  intros s H. unfold strip_trailing_ws in H.
  apply (f_equal rev_string) in H. rewrite rev_string_involutive in H.
  destruct (rev_string s) as [|z t] eqn:E.
  - left. rewrite <- (rev_string_involutive s), E. reflexivity.
  - right. exists (rev_string t), z. split.
    + rewrite <- (rev_string_involutive s), E, rev_string_cons. reflexivity.
    + exact (drop_leading_ws_fixed z t H).
Qed.

(* What strip_trailing_ws dropped is an all-whitespace suffix. *)
Lemma strip_trailing_split : forall s,
  exists w, is_blank w = true /\ s = strip_trailing_ws s ++ w.
Proof.
  intros s. destruct (drop_leading_ws_split (rev_string s)) as (p & Hp & E).
  exists (rev_string p). split; [rewrite rev_blank; exact Hp|].
  unfold strip_trailing_ws. rewrite <- rev_string_app, <- E, rev_string_involutive.
  reflexivity.
Qed.

Lemma strip_trailing_ws_app_blank : forall s w,
  is_blank w = true -> strip_trailing_ws (s ++ w) = strip_trailing_ws s.
Proof.
  intros s w Hw. unfold strip_trailing_ws. rewrite rev_string_app.
  rewrite (drop_leading_ws_ws_prefix (rev_string w) _ (eq_trans (rev_blank w) Hw)).
  reflexivity.
Qed.

(* Only a blank string drops to nothing. *)
Lemma drop_leading_ws_empty : forall r,
  drop_leading_ws r = EmptyString -> is_blank r = true.
Proof.
  intros r H. destruct (drop_leading_ws_split r) as (p & Hp & E).
  rewrite H, append_empty_r in E. subst r. exact Hp.
Qed.

(*
Lines: splitting and joining
============================
*)

(* The newline, as a one-character string. *)
Definition nl : string := String "010" EmptyString.

(* Split on LF.  A trailing newline does not yield a final empty line:
   "a\n" splits to ["a"], not ["a"; ""].  Hence the side condition, on
   lemmas about split_lines, that the last line is nonempty. *)
Local Fixpoint split_lines_aux (s : string) (cur : string) : list string :=
  match s with
  | EmptyString =>
      match cur with
      | EmptyString => []
      | _ => [rev_string cur]
      end
  | String c s' =>
      if Ascii.eqb c "010"
      then rev_string cur :: split_lines_aux s' EmptyString
      else split_lines_aux s' (String c cur)
  end.

Definition split_lines (s : string) : list string := split_lines_aux s EmptyString.

(* [split_lines], each line paired with its index. *)
Local Fixpoint index_lines_from (i : nat) (lines : list string)
  : list (nat * string) :=
  match lines with
  | [] => []
  | l :: rest => (i, l) :: index_lines_from (S i) rest
  end.

Definition split_lines_indexed (s : string) : list (nat * string) :=
  index_lines_from 0 (split_lines s).

Local Lemma map_snd_index_lines_from :
  forall i lines, map snd (index_lines_from i lines) = lines.
Proof.
  intros i lines. revert i.
  induction lines as [|l rest IH]; intros i; cbn; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma split_lines_indexed_values :
  forall s, map snd (split_lines_indexed s) = split_lines s.
Proof. intros s. apply map_snd_index_lines_from. Qed.

(* One entry per line produced by [split_lines].  Starts and lengths are
   byte counts.  [source_line_ending] is 1 precisely when LF terminated
   the line; CR remains part of [source_line_length], matching the parser's
   line model. *)
Record source_line : Type := SourceLine
  { source_line_start : nat
  ; source_line_length : nat
  ; source_line_ending : nat }.

Local Fixpoint line_table_aux (s : string) (start len : nat)
  : list source_line :=
  match s with
  | EmptyString =>
      match len with
      | 0 => []
      | _ => [SourceLine start len 0]
      end
  | String c rest =>
      if Ascii.eqb c "010"
      then SourceLine start len 1
           :: line_table_aux rest (S (start + len)) 0
      else line_table_aux rest start (S len)
  end.

Definition line_table (s : string) : list source_line :=
  line_table_aux s 0 0.

Local Definition source_line_at (lines : list source_line) (i : nat)
  : option source_line := nth_error lines i.

Record source_point : Type := SourcePoint
  { source_byte : nat
  ; source_line_index : nat
  ; source_column : nat }.

Record source_span : Type := SourceSpan
  { source_span_start : source_point
  ; source_span_stop : source_point }.

(* Resolve the end-anchored `spot` to a byte offset and column, once, at
   the API boundary.  A spot past its line's end is rejected rather than
   clamped. *)
Definition resolve_spot (lines : list source_line) (p : spot)
  : option source_point :=
  match source_line_at lines (spot_line p) with
  | Some l =>
      if Nat.leb (spot_rem p) (source_line_length l)
      then
        let col := source_line_length l - spot_rem p in
        Some (SourcePoint (source_line_start l + col) (spot_line p) col)
      else None
  | None => None
  end.

Definition resolve_span (lines : list source_line) (r : span)
  : option source_span :=
  match resolve_spot lines (span_start r), resolve_spot lines (span_stop r) with
  | Some a, Some b => Some (SourceSpan a b)
  | _, _ => None
  end.

(* No embedded newline: the precondition for a string to survive a
   split/join round trip as a single line. *)
Fixpoint no_nl (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => negb (Ascii.eqb c "010") && no_nl s'
  end.

(* One character absent. *)
Fixpoint no_char (c : ascii) (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c' s' => negb (Ascii.eqb c' c) && no_char c s'
  end.

(* Intra-line whitespace plus the line separator.  A token that must be
   written back onto one line has to exclude both. *)
Definition is_ws_nl (c : ascii) : bool := is_ws c || Ascii.eqb c "010".

(* No whitespace at all.  A reference definition's destination is one
   such run (Line.ref_value), and staying whitespace-free is what lets it
   be rendered back onto one line. *)
Fixpoint no_ws (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => negb (is_ws_nl c) && no_ws s'
  end.

Lemma no_ws_no_nl : forall s, no_ws s = true -> no_nl s = true.
Proof.
  induction s as [|c s IH]; [reflexivity|].
  cbn [no_ws no_nl]. intros H. apply andb_true_iff in H as [Hc Hs].
  rewrite (IH Hs), andb_true_r. apply negb_true_iff in Hc.
  unfold is_ws_nl in Hc. apply orb_false_iff in Hc as [_ Hc].
  rewrite Hc. reflexivity.
Qed.

(* A whitespace-free string has no leading whitespace to drop. *)
Lemma no_ws_drop_leading_ws :
  forall s, no_ws s = true -> drop_leading_ws s = s.
Proof.
  intros [|c s] H; [reflexivity|].
  cbn [no_ws] in H. apply andb_true_iff in H as [Hc _].
  apply negb_true_iff in Hc. unfold is_ws_nl in Hc.
  apply orb_false_iff in Hc as [Hws _].
  cbn [drop_leading_ws]. rewrite Hws. reflexivity.
Qed.

Lemma no_ws_append :
  forall s t, no_ws s = true -> no_ws t = true -> no_ws (s ++ t) = true.
Proof.
  induction s as [|c s IH]; intros t Hs Ht; [exact Ht|].
  cbn [no_ws append] in *. apply andb_true_iff in Hs as [Hc Hs].
  rewrite Hc. cbn. apply (IH t Hs Ht).
Qed.

(* A whitespace-free string is not blank unless it is empty. *)
Local Lemma no_ws_nonempty_nonblank :
  forall s, no_ws s = true -> nonempty_str s = true -> is_blank s = false.
Proof.
  intros [|c s] H He; [discriminate|].
  cbn [no_ws] in H. apply andb_true_iff in H as [Hc _].
  apply negb_true_iff in Hc. unfold is_ws_nl in Hc.
  apply orb_false_iff in Hc as [Hc _].
  rewrite is_blank_cons, Hc. reflexivity.
Qed.

(* A line as a renderer may produce it: nonblank, newline-free, and flush
   against its left margin.  The parser strips a text line's leading
   whitespace as it stores it (`Step.push_text`), so a line with leading
   whitespace cannot come back unchanged. *)
Definition line_ok (l : string) : bool :=
  nonblank l && no_nl l && String.eqb (drop_leading_ws l) l.

Lemma line_ok_no_nl : forall l, line_ok l = true -> no_nl l = true.
Proof.
  intros l H. unfold line_ok in H.
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H]. exact H.
Qed.

Lemma line_ok_nonblank : forall l, line_ok l = true -> is_blank l = false.
Proof.
  intros l H. unfold line_ok, nonblank in H.
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H _].
  apply negb_true_iff in H. exact H.
Qed.

Lemma line_ok_no_leading_ws : forall l, line_ok l = true -> drop_leading_ws l = l.
Proof.
  intros l H. unfold line_ok in H.
  apply andb_true_iff in H as [_ H]. apply String.eqb_eq in H. exact H.
Qed.

Local Lemma line_ok_nonempty : forall l, line_ok l = true -> l <> EmptyString.
Proof.
  intros l H E. subst. discriminate (line_ok_nonblank _ H).
Qed.

Local Lemma split_aux_no_nl :
  forall x cur, no_nl x = true ->
  split_lines_aux x cur =
  match rev_string_aux x cur with
  | EmptyString => []
  | String _ _ => [rev_string (rev_string_aux x cur)]
  end.
Proof.
  induction x as [|c x IH]; intros cur H; simpl.
  - reflexivity.
  - simpl in H. apply andb_true_iff in H as [Hc Hx].
    apply negb_true_iff in Hc. rewrite Hc.
    apply IH. exact Hx.
Qed.

Local Lemma split_lines_single :
  forall x, no_nl x = true -> x <> EmptyString -> split_lines x = [x].
Proof.
  intros x H Hne. unfold split_lines.
  rewrite (split_aux_no_nl x EmptyString H).
  rewrite rev_aux_app, append_empty_r.
  destruct (rev_string x) eqn:E.
  - exfalso. apply Hne.
    apply (f_equal String.length) in E. rewrite rev_length in E.
    destruct x; [reflexivity | discriminate].
  - rewrite <- E, rev_string_involutive. reflexivity.
Qed.

Local Lemma split_lines_line :
  forall x r, no_nl x = true ->
  split_lines (x ++ String "010" r) = x :: split_lines r.
Proof.
  intros x r H. unfold split_lines.
  (* aux with a general accumulator *)
  assert (Haux : forall x cur, no_nl x = true ->
    split_lines_aux (x ++ String "010" r) cur =
    rev_string (rev_string_aux x cur) :: split_lines_aux r EmptyString).
  { induction x0 as [|c x0 IH]; intros cur Hx; simpl.
    - reflexivity.
    - simpl in Hx. apply andb_true_iff in Hx as [Hc Hx].
      apply negb_true_iff in Hc. rewrite Hc.
      apply IH. exact Hx. }
  rewrite (Haux x EmptyString H).
  rewrite rev_aux_app, append_empty_r, rev_string_involutive.
  reflexivity.
Qed.

Local Lemma split_lines_cons_nl :
  forall r, split_lines (String "010" r) = EmptyString :: split_lines r.
Proof. reflexivity. Qed.

(*
Joined newline-free lines split back exactly
--------------------------------------------

Interior lines may be blank (code-block content); only the final line
must be nonempty, because split_lines drops a trailing empty line. *)

(* concat then split is the identity, when the last line is nonempty. *)
Lemma split_join_last :
  forall a ls,
    forallb no_nl (a :: ls) = true ->
    last (a :: ls) EmptyString <> EmptyString ->
    split_lines (String.concat nl (a :: ls)) = a :: ls.
Proof.
  intros a ls. revert a.
  induction ls as [|b ls IH]; intros a H Hlast; simpl in H;
    apply andb_true_iff in H as [Ha Hrest].
  - simpl. apply split_lines_single; [exact Ha | exact Hlast].
  - change (String.concat nl (a :: b :: ls))
      with (a ++ String "010" (String.concat nl (b :: ls))).
    rewrite split_lines_line by exact Ha.
    f_equal. apply IH; [exact Hrest | exact Hlast].
Qed.

(* ...and the same when more input follows the join: the joined lines
   come off the front and the remainder splits independently. *)
Local Lemma split_join_line :
  forall a ls r, forallb no_nl (a :: ls) = true ->
  split_lines (String.concat nl (a :: ls) ++ String "010" r) =
  ((a :: ls) ++ split_lines r)%list.
Proof.
  intros a ls. revert a.
  induction ls as [|b ls IH]; intros a r H; simpl in H;
    apply andb_true_iff in H as [Ha Hrest].
  - simpl. apply split_lines_line. exact Ha.
  - change (String.concat nl (a :: b :: ls))
      with (a ++ String "010" (String.concat nl (b :: ls))).
    rewrite append_assoc. simpl.
    rewrite split_lines_line by exact Ha.
    simpl. f_equal. apply IH. exact Hrest.
Qed.

(*
List helpers
------------
*)

Lemma no_nl_append :
  forall a b, no_nl (a ++ b) = (no_nl a && no_nl b)%bool.
Proof.
  induction a as [|c a IH]; intros b; simpl.
  - reflexivity.
  - rewrite IH. rewrite andb_assoc. reflexivity.
Qed.

Lemma forallb_last :
  forall (f : string -> bool) a ls,
    forallb f (a :: ls) = true -> f (last (a :: ls) EmptyString) = true.
Proof.
  intros f a ls. revert a.
  induction ls as [|b ls IH]; intros a H; simpl in H;
    apply andb_true_iff in H as [Ha Hrest].
  - exact Ha.
  - apply IH. exact Hrest.
Qed.

(* Join lines, each with a trailing newline (code-block content shape). *)
Fixpoint join_nl (ls : list string) : string :=
  match ls with
  | [] => EmptyString
  | l :: rest => l ++ nl ++ join_nl rest
  end.

Local Lemma concat_cons_ne :
  forall sep x l, l <> [] ->
  String.concat sep (x :: l) = x ++ sep ++ String.concat sep l.
Proof. intros sep x l H. destruct l; [congruence | reflexivity]. Qed.

(* Content lines followed by a final line: the newline-terminated join
   against the final line is the same as concat over all of them. *)
Local Lemma join_nl_last :
  forall content x,
    (join_nl content ++ x)%string = String.concat nl (content ++ [x])%list.
Proof.
  induction content as [|c cont IH]; intros x; simpl join_nl.
  - reflexivity.
  - rewrite !append_assoc.
    change ((c :: cont) ++ [x])%list with (c :: (cont ++ [x]))%list.
    rewrite concat_cons_ne by (destruct cont; discriminate).
    rewrite <- IH. reflexivity.
Qed.

Lemma last_app_singleton :
  forall {A : Type} (l : list A) (x d : A), last (l ++ [x])%list d = x.
Proof.
  induction l as [|a l IH]; intros x d; simpl.
  - reflexivity.
  - destruct (l ++ [x])%list eqn:E.
    + exfalso. destruct l; discriminate.
    + rewrite <- E. apply IH.
Qed.

Lemma last_cons_nonnil :
  forall {A : Type} (a : A) (l : list A) (d : A),
    l <> [] -> last (a :: l) d = last l d.
Proof. intros A a l d H. destruct l; [congruence | reflexivity]. Qed.

Lemma last_app_nonnil :
  forall {A : Type} (l1 l2 : list A) (d : A),
    l2 <> [] -> last (l1 ++ l2)%list d = last l2 d.
Proof.
  induction l1 as [|a l1 IH]; intros l2 d H; cbn [app]; [reflexivity|].
  rewrite last_cons_nonnil
    by (destruct l1; cbn [app]; [exact H | discriminate]).
  apply IH. exact H.
Qed.

(* The default only shows through on the empty list. *)
Lemma last_default :
  forall {A : Type} (l : list A) (d d' : A), l <> [] -> last l d = last l d'.
Proof.
  intros A l. induction l as [|a l IH]; intros d d' H; [congruence|].
  destruct l as [|b l']; [reflexivity|].
  change (last (a :: b :: l') d) with (last (b :: l') d).
  change (last (a :: b :: l') d') with (last (b :: l') d').
  apply IH. discriminate.
Qed.

Lemma last_map :
  forall {A B : Type} (f : A -> B) (l : list A) (d : A),
    l <> [] -> last (map f l) (f d) = f (last l d).
Proof.
  intros A B f l. induction l as [|a l IH]; intros d H; [congruence|].
  destruct l as [|b l']; [reflexivity|].
  change (last (map f (a :: b :: l')) (f d))
    with (last (map f (b :: l')) (f d)).
  change (last (a :: b :: l') d) with (last (b :: l') d).
  apply IH. discriminate.
Qed.

(* join_nl is inverted by split_lines outright: every line carries its
   own newline, so there is no "last line nonempty" side condition. *)
Lemma split_join_nl :
  forall ls, forallb no_nl ls = true -> split_lines (join_nl ls) = ls.
Proof.
  induction ls as [|l ls IH]; intros H; [reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hl Hls].
  cbn [join_nl].
  change (l ++ nl ++ join_nl ls)%string
    with (l ++ String "010" (join_nl ls))%string.
  rewrite split_lines_line by exact Hl.
  f_equal. apply IH. exact Hls.
Qed.
