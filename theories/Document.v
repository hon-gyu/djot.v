(* ai-disclosure: autonomous *)

(** * Whole-document resolution

   The part of parsing that is a function of the finished block list
   rather than of a single line.  It runs after `Parser.parse_blocks`,
   never inside the fold, so inline classification cannot depend on the
   reference and note maps.

   - Auto-identifiers and implicit heading references, assigned in
     document order because uniqueness suffixes depend on what came
     before.
   - Section nesting: a level-driven container stack over the top-level
     block list, moving each heading's id onto the section that wraps it.
   - Footnote and reference definitions: read into the note map and the
     reference map.  Both stay in the tree.

   Sectioning is top-level only: a section opens only where the enclosing
   container tracks a heading level, which the document does and a block
   quote does not, so `> # h` yields a bare `<h1 id="h">`.  Identifiers
   are assigned everywhere and share one counter. *)

From Stdlib Require Import String Ascii List Bool PeanoNat Lia.
From Stdlib Require MSetAVL FMapAVL OrdersEx OrderedTypeEx.
From DjotV Require Import Strings Ast Parser Reparse.
Import ListNotations.

(* Balanced trees over strings, for the identifier pass: the identifiers
   taken so far, the labels that already have an implicit reference, and
   each base's next candidate index.  Declared here because a module
   cannot be declared inside a section. *)
Module StrSet := MSetAVL.Make OrdersEx.String_as_OT.
Module StrMap := FMapAVL.Make OrderedTypeEx.String_as_OT.

Local Open Scope string_scope.

(* The delimiter table this file is read at.  Implicit, so nothing below
   mentions it: what it buys is that the statements quantify over the
   family rather than over djot's spelling. *)
Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(*
Heading text
============
*)

(* The string an element contributes to its heading's identifier:
   text-carrying leaves give their text, breaks give a newline,
   containers concatenate their children, and footnote references
   contribute nothing, so a heading's marker does not leak into its id.
   A symbol carries only its alias and contributes nothing, as in
   djot.js. *)
Fixpoint inline_text (il : inline) : string :=
  let go :=
    fix go (ns : list (node inline)) : string :=
      match ns with
      | [] => ""
      | Node _ _ x :: rest => inline_text x ++ go rest
      end in
  match il with
  | Str s => s
  | Verbatim s => s
  | Math _ s => s
  | RawInline _ s => s
  (* a hole contributes its expression, as math contributes its formula *)
  | Hole s => s
  | SoftBreak | HardBreak => nl
  | FootnoteReference _ => ""
  | Emph ils | Strong ils | Highlight ils | Insert ils | Delete ils
  | Superscript ils | Subscript ils | Span _ ils
  | Link ils _ | Image ils _ | Quoted _ ils => go ils
  (* an autolink contributes its region, so it reaches a heading id and
     an image `alt` *)
  | UrlLink s | EmailLink s => s
  (* the text a wikilink displays, as its desugared link would push it *)
  | Ext_wikilink _ t al => wiki_display t al
  | Symbol _ | NonBreakingSpace => ""
  end.

Definition inlines_text (ils : inlines) : string :=
  String.concat "" (map (fun n => inline_text (node_contents n)) ils).

(*
Auto-identifiers
================
*)

(* The characters an identifier drops.  Runs of them separate words,
   which are joined with "-": `words` over the class, where collapsing
   and trimming are what dropping empty tokens already does. *)
Local Definition is_id_sep (c : ascii) : bool :=
  (* JavaScript \s, ASCII part: HT VT FF CR LF and space *)
  ((Ascii.eqb c "009" || Ascii.eqb c "010" || Ascii.eqb c "011"
    || Ascii.eqb c "012" || Ascii.eqb c "013" || Ascii.eqb c " ")
   || (Ascii.eqb c "[" || Ascii.eqb c "]" || Ascii.eqb c "~"
       || Ascii.eqb c "!" || Ascii.eqb c "@" || Ascii.eqb c "#"
       || Ascii.eqb c "$" || Ascii.eqb c "%" || Ascii.eqb c "^"
       || Ascii.eqb c "&" || Ascii.eqb c "*" || Ascii.eqb c "("
       || Ascii.eqb c ")" || Ascii.eqb c "{" || Ascii.eqb c "}"
       || Ascii.eqb c "096" (* backquote *)
       || Ascii.eqb c "," || Ascii.eqb c "." || Ascii.eqb c "<"
       || Ascii.eqb c ">" || Ascii.eqb c "092" (* backslash *)
       || Ascii.eqb c "|" || Ascii.eqb c "=" || Ascii.eqb c "+"
       || Ascii.eqb c "/" || Ascii.eqb c "?"))%char%bool.

Definition id_base (s : string) : string :=
  String.concat "-" (words is_id_sep s).

(* The syntax reference on the identifier: the heading's text, "removing
   punctuation (other than `_` and `-`), replacing spaces with `-`".  The
   next two lemmas say which bytes `id_base` drops, over all 256.  It
   follows djot.js where that differs from the wording: both quote
   characters, `:` and `;` are kept too, and a punctuation byte separates
   words as a space does, so `a.b` gives `a-b`. *)
Lemma is_id_sep_punct : forall c, is_punct c = true ->
  is_id_sep c
  = negb (existsb (Ascii.eqb c) ["_"; "-"; """"; "'"; ":"; ";"]%char).
Proof.
  intros [[] [] [] [] [] [] [] []]; vm_compute; first [reflexivity | discriminate].
Qed.

Lemma is_id_sep_other : forall c, is_punct c = false ->
  is_id_sep c
  = existsb (Ascii.eqb c) ["009"; "010"; "011"; "012"; "013"; " "]%char.
Proof.
  intros [[] [] [] [] [] [] [] []]; vm_compute; first [reflexivity | discriminate].
Qed.

Local Lemma concat_dash_sep_free : forall ws,
  Forall (fun w => w <> "" /\ sep_free is_id_sep w = true) ws ->
  sep_free is_id_sep (String.concat "-" ws) = true.
Proof.
  assert (A : forall a b, sep_free is_id_sep a = true ->
    sep_free is_id_sep b = true -> sep_free is_id_sep (a ++ b) = true).
  { unfold sep_free. intros a b Ha Hb.
    induction a as [|c a IH]; cbn in *; [exact Hb|].
    apply andb_true_iff in Ha. destruct Ha as [Hc Ha].
    rewrite Hc, IH by exact Ha. reflexivity. }
  induction ws as [|w ws IH]; intros H; [reflexivity|].
  inversion H as [|? ? [_ Hw] Hws]; subst. cbn [String.concat].
  destruct ws as [|w' ws']; [exact Hw|].
  apply A; [exact Hw|]. apply (A "-"); [reflexivity|]. apply IH, Hws.
Qed.

(* No dropped byte reaches the identifier. *)
Theorem id_base_sep_free : forall s, sep_free is_id_sep (id_base s) = true.
Proof. intros s. apply concat_dash_sep_free, words_tokens. Qed.

(* `id_base` by cases on the text, as `words` is: a text with nothing to
   drop is its own identifier; dropped bytes at the start vanish; a word
   followed by a dropped byte is joined to the rest by one `-`, or stands
   alone when the rest has no word.  So runs collapse and neither end
   carries a `-` of its own. *)
Theorem id_base_word : forall w,
  sep_free is_id_sep w = true -> id_base w = w.
Proof.
  intros w H. unfold id_base. destruct w as [|c w]; [reflexivity|].
  rewrite words_last by (exact H || discriminate). reflexivity.
Qed.

Theorem id_base_sep : forall c s,
  is_id_sep c = true -> id_base (String c s) = id_base s.
Proof.
  intros c s H. unfold id_base. rewrite words_sep by exact H. reflexivity.
Qed.

Theorem id_base_word_sep : forall w c s,
  w <> "" -> sep_free is_id_sep w = true -> is_id_sep c = true ->
  id_base (w ++ String c s)
  = if nonempty_str (id_base s) then w ++ "-" ++ id_base s else w.
Proof.
  intros w c s Hne Hw Hc. unfold id_base.
  rewrite words_word by assumption. cbn [String.concat].
  pose proof (words_tokens is_id_sep s) as Tk.
  destruct (words is_id_sep s) as [|w' ws]; [reflexivity|].
  inversion Tk as [|? ? [Hw' _] _]; subst.
  destruct w' as [|x w']; [contradiction|].
  destruct ws; reflexivity.
Qed.

Local Definition id_taken (used : list string) (s : string) : bool :=
  existsb (String.eqb s) used.

(* Candidate i: the base itself at 0, then base-1, base-2, ...  An empty
   base is rejected at 0 and becomes "s-1", "s-2", ... *)
Local Definition id_candidate (base : string) (i : nat) : string :=
  if Nat.eqb i 0 then base
  else (match base with EmptyString => "s" | _ => base end)
       ++ "-" ++ nat_str i.

(* The specification: the first free candidate.  Fuel, fixed by
   `unique_id` below.  With n identifiers taken, candidates 1..n+1 are
   n+1 distinct nonempty strings, so one of them is free and the O branch
   is unreachable (`unique_id_first`). *)
Local Fixpoint unique_id_from (fuel i : nat) (used : list string) (base : string)
  : string :=
  let cand := id_candidate base i in
  match fuel with
  | O => cand
  | S f =>
      if nonempty_str cand && negb (id_taken used cand)
      then cand
      else unique_id_from f (S i) used base
  end.

Definition unique_id (used : list string) (base : string) : string :=
  unique_id_from (S (S (length used))) 0 used base.

(*
The identifier pass
-------------------
*)

(* Threaded through the block tree in document order.  The lists hold
   their entries newest-first; `doc_pass` reverses the two it keeps.

   Run as written, `unique_id` rescans every candidate from 0 against the
   whole list, which is cubic in the number of headings sharing a text.
   The pass keeps three more fields so that it need not: the taken set,
   the labels with an implicit reference, and per base the index below
   which every candidate is known to be taken.  `id_inv` says the fields
   agree with the lists, and `assign_heading_id_spec` says the pass then
   assigns `unique_id` exactly. *)
Record id_state : Type := IdSt
  { id_used : list string
  ; id_refs : reference_map
  ; id_count : nat
  ; id_used_set : StrSet.t
  ; id_ref_labels : StrSet.t
  ; id_next : StrMap.t nat
  (* The identifiers the pass derived, latest first. *)
  ; id_derived : list string }.

Definition id_state_init : id_state :=
  IdSt [] [] 0 StrSet.empty StrSet.empty (@StrMap.empty nat) [].

Local Definition take_id (ident : string) (st : id_state) : id_state :=
  IdSt (ident :: id_used st) (id_refs st) (S (id_count st))
       (StrSet.add ident (id_used_set st)) (id_ref_labels st) (id_next st)
       (id_derived st).

(* An implicit reference from the heading's text to its own id, unless
   that label already has an implicit one.  Explicit references are not
   consulted: `Html.doc_refs` appends the implicit map after the explicit
   one and lookup takes the first match, so an explicit definition wins
   at lookup. *)
Local Definition add_auto_ref (label ident : string) (st : id_state) : id_state :=
  if StrSet.mem label (id_ref_labels st)
  then st
  else IdSt (id_used st) ((label, ("#" ++ ident, [])) :: id_refs st)
            (id_count st) (id_used_set st)
            (StrSet.add label (id_ref_labels st)) (id_next st)
            (id_derived st).

(* An identifier a block attribute spec supplied is taken, and a later
   heading's auto-identifier steps around it.  Every id present in the
   tree at this point came from a spec, since this pass adds the
   others. *)
Definition register_id (a : attr) (st : id_state) : id_state :=
  match alist_lookup "id" a with
  | None => st
  | Some ident => take_id ident st
  end.

(* `unique_id_from` with the taken test on the set, returning the index. *)
Local Fixpoint fresh_index (taken : StrSet.t) (base : string) (fuel i : nat)
  : nat :=
  match fuel with
  | O => i
  | S f =>
      let cand := id_candidate base i in
      if nonempty_str cand && negb (StrSet.mem cand taken)
      then i
      else fresh_index taken base f (S i)
  end.

(* The index to search from, and the fuel that makes the search end where
   `unique_id`'s does. *)
Local Definition fresh_for (st : id_state) (base : string) : nat :=
  let start := match StrMap.find base (id_next st) with
               | Some n => n
               | None => 0
               end in
  fresh_index (id_used_set st) base (S (S (id_count st)) - start) start.

Definition assign_heading_id (p : pos) (a : attr) (lvl : nat) (ils : inlines)
  (st : id_state) : id_state * node block :=
  let text := inlines_text ils in
  match alist_lookup "id" a with
  (* An explicit id wins, and takes its slot.  The implicit reference is
     registered either way and points at that id, so `{#foo}` over
     `# Introduction` makes `[Introduction][]` a link to `#foo`. *)
  | Some ident =>
      (add_auto_ref (normalize_label text) ident (register_id a st),
       Node p a (Heading lvl ils))
  | None =>
      let base := id_base text in
      let i := fresh_for st base in
      let ident := id_candidate base i in
      let st1 := take_id ident st in
      let st' := IdSt (id_used st1) (id_refs st1) (id_count st1)
                      (id_used_set st1) (id_ref_labels st1)
                      (StrMap.add base (S i) (id_next st1))
                      (ident :: id_derived st1) in
      (add_auto_ref (normalize_label text) ident st',
       Node p (("id", ident) :: a) (Heading lvl ils))
  end.

(*
Agreement with the specification
---------------------------------
*)

Local Definition id_free (used : list string) (base : string) (j : nat) : bool :=
  nonempty_str (id_candidate base j)
  && negb (id_taken used (id_candidate base j)).

Definition id_inv (st : id_state) : Prop :=
  (forall s, StrSet.In s (id_used_set st) <-> In s (id_used st))
  /\ (forall l, StrSet.In l (id_ref_labels st) <-> In l (map fst (id_refs st)))
  /\ id_count st = length (id_used st)
  /\ (forall base n, StrMap.MapsTo base n (id_next st) ->
        n <= S (S (length (id_used st)))
        /\ forall j, j < n -> id_free (id_used st) base j = false).

Lemma id_inv_init : id_inv id_state_init.
Proof.
  split; [|split; [|split]]; cbn.
  - intros s. split; [intros H; apply StrSet.empty_spec in H; contradiction|
                      intros []].
  - intros l. split; [intros H; apply StrSet.empty_spec in H; contradiction|
                      intros []].
  - reflexivity.
  - intros base n H. apply StrMap.find_1 in H. discriminate H.
Qed.

Local Lemma id_taken_in : forall used s, id_taken used s = true <-> In s used.
Proof.
  intros used s. unfold id_taken. rewrite existsb_exists. split.
  - intros [x [Hx He]]. apply String.eqb_eq in He. subst x. exact Hx.
  - intros H. exists s. split; [exact H|apply String.eqb_refl].
Qed.

Local Lemma mem_taken : forall st s,
  (forall s, StrSet.In s (id_used_set st) <-> In s (id_used st)) ->
  StrSet.mem s (id_used_set st) = id_taken (id_used st) s.
Proof.
  intros st s H. destruct (StrSet.mem s (id_used_set st)) eqn:E;
    destruct (id_taken (id_used st) s) eqn:E'; try reflexivity.
  - apply StrSet.mem_spec, H, id_taken_in in E. congruence.
  - apply id_taken_in, H, StrSet.mem_spec in E'. congruence.
Qed.

(* Taking an identifier only makes more candidates taken. *)
Local Lemma id_free_cons : forall used x base j,
  id_free used base j = false -> id_free (x :: used) base j = false.
Proof.
  intros used x base j H. unfold id_free, id_taken in *. cbn [existsb].
  destruct (nonempty_str (id_candidate base j)); [|reflexivity].
  destruct (existsb (String.eqb (id_candidate base j)) used); [|discriminate H].
  rewrite orb_true_r. reflexivity.
Qed.

Local Lemma fresh_index_spec : forall st base f i,
  (forall s, StrSet.In s (id_used_set st) <-> In s (id_used st)) ->
  id_candidate base (fresh_index (id_used_set st) base f i)
  = unique_id_from f i (id_used st) base
  /\ i <= fresh_index (id_used_set st) base f i <= i + f
  /\ (forall j, i <= j < fresh_index (id_used_set st) base f i ->
        id_free (id_used st) base j = false).
Proof.
  intros st base f. induction f as [|f IH]; intros i Hset.
  - cbn. split; [reflexivity|split; [lia|intros j Hj; lia]].
  - cbn [fresh_index unique_id_from]. rewrite (mem_taken st _ Hset).
    destruct (nonempty_str (id_candidate base i)
              && negb (id_taken (id_used st) (id_candidate base i))) eqn:E.
    + split; [reflexivity|split; [lia|intros j Hj; lia]].
    + destruct (IH (S i) Hset) as [Hc [Hb Hf]].
      split; [exact Hc|split; [lia|]].
      intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne]; [exact E|].
      apply Hf. lia.
Qed.

(* Skipping candidates known to be taken does not change the answer. *)
Local Lemma unique_id_from_skip : forall used base k f i,
  (forall j, i <= j < i + k -> id_free used base j = false) ->
  unique_id_from (k + f) i used base = unique_id_from f (i + k) used base.
Proof.
  intros used base k. induction k as [|k IH]; intros f i H.
  - rewrite Nat.add_0_r. reflexivity.
  - cbn [Nat.add unique_id_from].
    pose proof (H i ltac:(lia)) as Hi. unfold id_free in Hi. rewrite Hi.
    rewrite IH by (intros j Hj; apply H; lia).
    f_equal. lia.
Qed.

Local Lemma pigeonhole : forall (f : nat -> string) (used : list string),
  (forall a b, f a = f b -> a = b) ->
  exists j, j <= length used /\ ~ In (f j) used.
Proof.
  intros f used Hinj.
  assert (D : forall n, (forall j, j < n -> In (f j) used) -> n <= length used).
  { intros n Hall.
    replace n with (length (map f (seq 0 n)))
      by (rewrite length_map, length_seq; reflexivity).
    apply NoDup_incl_length.
    - apply NoDup_map_NoDup_ForallPairs;
        [intros a b _ _; apply Hinj|apply seq_NoDup].
    - intros x Hx. apply in_map_iff in Hx. destruct Hx as [j [<- Hj]].
      apply in_seq in Hj. apply Hall. lia. }
  destruct (Exists_dec (fun j => ~ In (f j) used) (seq 0 (S (length used))))
    as [E|E].
  - intros j. destruct (in_dec string_dec (f j) used); [right|left]; tauto.
  - apply Exists_exists in E. destruct E as [j [Hj Hn]]. apply in_seq in Hj.
    exists j. split; [lia|exact Hn].
  - exfalso. specialize (D (S (length used))).
    assert (S (length used) <= length used); [|lia].
    apply D. intros j Hj.
    destruct (in_dec string_dec (f j) used) as [Hi|Hi]; [exact Hi|].
    exfalso. apply E, Exists_exists.
    exists j. split; [apply in_seq; lia|exact Hi].
Qed.

Local Lemma id_candidate_S : forall base i,
  id_candidate base (S i)
  = (match base with EmptyString => "s" | _ => base end)
    ++ "-" ++ nat_str (S i).
Proof. reflexivity. Qed.

(* Within the fuel `unique_id` runs on, some candidate is free. *)
Local Lemma id_free_within : forall used base,
  exists j, j < S (S (length used)) /\ id_free used base j = true.
Proof.
  intros used base.
  destruct (pigeonhole (fun j => id_candidate base (S j)) used)
    as [j [Hj Hn]].
  { intros a b H. rewrite !id_candidate_S in H.
    apply append_inj_l in H. apply (append_inj_l "-") in H.
    apply nat_str_inj in H. lia. }
  exists (S j). split; [lia|]. unfold id_free.
  replace (nonempty_str (id_candidate base (S j))) with true
    by (rewrite id_candidate_S; destruct base; reflexivity).
  cbn [andb].
  destruct (id_taken used (id_candidate base (S j))) eqn:E; [|reflexivity].
  apply id_taken_in in E. contradiction.
Qed.

Local Lemma unique_id_from_first : forall used base f i,
  (exists j, i <= j < i + f /\ id_free used base j = true) ->
  exists j, i <= j < i + f /\ id_free used base j = true
    /\ (forall k, i <= k < j -> id_free used base k = false)
    /\ unique_id_from f i used base = id_candidate base j.
Proof.
  intros used base f. induction f as [|f IH]; intros i [j [Hj Hf]]; [lia|].
  cbn [unique_id_from]. fold (id_free used base i).
  destruct (id_free used base i) eqn:E.
  - exists i. split; [lia|]. split; [exact E|].
    split; [intros k Hk; lia|reflexivity].
  - destruct (IH (S i)) as [j' [Hj' [Hf' [Hlow Heq]]]].
    { exists j. split; [|exact Hf].
      destruct (Nat.eq_dec j i); [congruence|lia]. }
    exists j'. split; [lia|]. split; [exact Hf'|]. split; [|exact Heq].
    intros k Hk. destruct (Nat.eq_dec k i) as [->|]; [exact E|apply Hlow; lia].
Qed.

(* The reference: "a numerical suffix to ensure uniqueness".  `unique_id`
   is the first candidate that is nonempty and not taken. *)
Theorem unique_id_first : forall used base,
  exists i, unique_id used base = id_candidate base i
    /\ id_free used base i = true
    /\ forall j, j < i -> id_free used base j = false.
Proof.
  intros used base. unfold unique_id.
  destruct (unique_id_from_first used base (S (S (length used))) 0)
    as [j [_ [Hf [Hlow Heq]]]].
  { destruct (id_free_within used base) as [j [Hj Hf]].
    exists j. split; [lia|exact Hf]. }
  exists j. split; [exact Heq|]. split; [exact Hf|].
  intros k Hk. apply Hlow. lia.
Qed.

Theorem unique_id_fresh : forall used base,
  unique_id used base <> "" /\ ~ In (unique_id used base) used.
Proof.
  intros used base. destruct (unique_id_first used base) as [i [-> [Hf _]]].
  unfold id_free in Hf. apply andb_true_iff in Hf. destruct Hf as [Hn Ht].
  split.
  - intros E. rewrite E in Hn. discriminate.
  - intros Hin. apply id_taken_in in Hin. rewrite Hin in Ht. discriminate.
Qed.

Local Lemma fresh_for_spec : forall st base,
  id_inv st ->
  id_candidate base (fresh_for st base) = unique_id (id_used st) base
  /\ fresh_for st base <= S (S (length (id_used st)))
  /\ forall j, j < fresh_for st base -> id_free (id_used st) base j = false.
Proof.
  intros st base [Hset [_ [Hcount Hnext]]]. unfold fresh_for, unique_id.
  rewrite Hcount.
  set (L := S (S (length (id_used st)))).
  destruct (StrMap.find base (id_next st)) as [n|] eqn:Ef.
  - apply StrMap.find_2 in Ef. destruct (Hnext base n Ef) as [Hn Hlow].
    destruct (fresh_index_spec st base (L - n) n Hset) as [Hc [Hb Hf]].
    assert (Hu : unique_id_from L 0 (id_used st) base
                 = unique_id_from (L - n) n (id_used st) base).
    { replace L with (n + (L - n)) at 1 by lia.
      rewrite (unique_id_from_skip _ _ n (L - n) 0)
        by (intros j Hj; apply Hlow; lia).
      reflexivity. }
    rewrite Hu. split; [exact Hc|split; [lia|]].
    intros j Hj. destruct (Nat.lt_ge_cases j n); [apply Hlow; lia|apply Hf; lia].
  - destruct (fresh_index_spec st base (L - 0) 0 Hset) as [Hc [Hb Hf]].
    rewrite Nat.sub_0_r in *.
    split; [exact Hc|split; [lia|intros j Hj; apply Hf; lia]].
Qed.

Local Lemma take_id_inv : forall ident st,
  id_inv st -> id_inv (take_id ident st).
Proof.
  intros ident st [Hset [Hlab [Hcount Hnext]]].
  unfold take_id. split; [|split; [|split]]; cbn [id_used id_refs id_count
    id_used_set id_ref_labels id_next length In].
  - intros s. rewrite StrSet.add_spec, Hset. split; intros [H|H]; auto.
  - exact Hlab.
  - rewrite Hcount. reflexivity.
  - intros base n H. destruct (Hnext base n H) as [Hn Hlow].
    split; [lia|intros j Hj; apply id_free_cons, Hlow, Hj].
Qed.

Local Lemma add_auto_ref_inv : forall label ident st,
  id_inv st -> id_inv (add_auto_ref label ident st).
Proof.
  intros label ident st Hinv. unfold add_auto_ref.
  destruct (StrSet.mem label (id_ref_labels st)); [exact Hinv|].
  destruct Hinv as [Hset [Hlab [Hcount Hnext]]].
  split; [|split; [|split]]; cbn [id_used id_refs id_count
    id_used_set id_ref_labels id_next map fst In]; try assumption.
  intros l. rewrite StrSet.add_spec, Hlab. split; intros [H|H]; auto.
Qed.

Lemma register_id_inv : forall a st, id_inv st -> id_inv (register_id a st).
Proof.
  intros a st H. unfold register_id.
  destruct (alist_lookup "id" a); [apply take_id_inv, H|exact H].
Qed.

(* The pass assigns what the specification assigns, and keeps `id_inv`. *)
Theorem assign_heading_id_spec : forall p a lvl ils st,
  id_inv st ->
  alist_lookup "id" a = None ->
  snd (assign_heading_id p a lvl ils st)
  = Node p (("id", unique_id (id_used st) (id_base (inlines_text ils))) :: a)
         (Heading lvl ils).
Proof.
  intros p a lvl ils st Hinv Ha. unfold assign_heading_id. rewrite Ha.
  cbn [snd]. destruct (fresh_for_spec st (id_base (inlines_text ils)) Hinv)
    as [Hc _]. rewrite Hc. reflexivity.
Qed.

Lemma assign_heading_id_inv : forall p a lvl ils st,
  id_inv st -> id_inv (fst (assign_heading_id p a lvl ils st)).
Proof.
  intros p a lvl ils st Hinv. unfold assign_heading_id.
  destruct (alist_lookup "id" a) as [ident|] eqn:Ha; cbn [fst].
  - apply add_auto_ref_inv, register_id_inv, Hinv.
  - apply add_auto_ref_inv.
    set (base := id_base (inlines_text ils)).
    destruct (fresh_for_spec st base Hinv) as [_ [Hb Hlow]].
    set (i := fresh_for st base) in *.
    pose proof (take_id_inv (id_candidate base i) st Hinv)
      as [Hset [Hlab [Hcount Hnext]]].
    unfold take_id in *.
    split; [|split; [|split]]; cbn [id_used id_refs id_count
      id_used_set id_ref_labels id_next] in *; try assumption.
    intros b n Hm.
    destruct (String.string_dec b base) as [->|Hne].
    + assert (n = S i) as ->.
      { apply StrMap.find_1 in Hm.
        assert (Hm' : StrMap.MapsTo base (S i)
                        (StrMap.add base (S i) (id_next st)))
          by (apply StrMap.add_1; reflexivity).
        apply StrMap.find_1 in Hm'. congruence. }
      split; [cbn [length]; lia|].
      intros j Hj. destruct (Nat.eq_dec j i) as [->|Hne].
      * unfold id_free, id_taken. cbn [existsb].
        rewrite String.eqb_refl, orb_true_l, andb_false_r. reflexivity.
      * apply id_free_cons, Hlow. lia.
    + apply StrMap.add_3 in Hm; [exact (Hnext b n Hm)|].
      intros He. apply Hne. symmetry. exact He.
Qed.

End WithTable.
(* The document pass treats a section and a heading each in its own way,
   and every other block as its children. *)
Definition plain_block (b : block) : bool :=
  match b with
  | Section _ | Heading _ _ => false
  | _ => true
  end.

Lemma plain_block_map_acc_children :
  forall (S : Type) (f : node block -> S -> S * node block) b st,
    plain_block (snd (map_acc_children f b st)) = plain_block b.
Proof.
  intros S f b st. destruct b; cbn [map_acc_children]; try reflexivity;
    match goal with |- context [let (_, _) := ?e in _] => destruct e end;
    reflexivity.
Qed.

Lemma plain_block_erase : forall b,
  plain_block (Erase.of_block b) = plain_block b.
Proof. intros b. destruct b as [| | | | | | | | | | | | | | | |? []|]; reflexivity. Qed.

Module Ids.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(* Pre-order, which is document order for headings: a heading closes
   before anything that starts after it, and headings do not nest.

   Recursion is on the payload, with the node's position and attributes
   passed alongside, because `block` recurses through `list (node
   block)`, two type constructors deep, which the guard checker will not
   follow from a `node block` principal argument.  `Html.render_block`
   has the same shape for the same reason.

   A section is not entered: the line fold builds none.  A table's cells
   and caption hold inlines, so there is no heading inside one to find. *)
Fixpoint of_block (b : block) (p : pos) (a : attr) (st : id_state)
  {struct b} : id_state * node block :=
  match b with
  | Heading lvl ils => assign_heading_id p a lvl ils st
  | Section _ => (register_id a st, Node p a b)
  | _ =>
      let (st', b') :=
        map_acc_children
          (fun n s => match n with Node p' a' x => of_block x p' a' s end)
          b (register_id a st) in
      (st', Node p a b')
  end.

Definition of_node (n : node block) (st : id_state)
  : id_state * node block :=
  match n with Node p a b => of_block b p a st end.

Definition of_list (ns : blocks) (st : id_state) : id_state * blocks :=
  map_acc of_node ns st.

Lemma of_block_plain :
  forall b p a st,
    plain_block b = true ->
    of_block b p a st
    = (fst (map_acc_children of_node b (register_id a st)),
       Node p a (snd (map_acc_children of_node b (register_id a st)))).
Proof.
  intros b p a st H.
  transitivity (let (st', b') := map_acc_children of_node b (register_id a st) in
                (st', Node p a b')).
  - destruct b; try discriminate; reflexivity.
  - destruct (map_acc_children of_node b (register_id a st)); reflexivity.
Qed.

(* The pass keeps `id_inv`, so by `assign_heading_id_spec` every heading
   without an explicit id gets `unique_id` of the identifiers before it. *)
Lemma of_block_inv :
  forall b p a st, id_inv st -> id_inv (fst (of_block b p a st)).
Proof.
  intros b. induction b as [b IH] using block_children_ind. intros p a st H.
  destruct (plain_block b) eqn:Hp.
  - rewrite of_block_plain by exact Hp. cbn [fst].
    rewrite map_acc_children_fst.
    pose proof (register_id_inv a st H) as Hs. revert Hs.
    generalize (register_id a st).
    induction IH as [|[q c x] rest Hx _ IHr]; intros s Hs; [exact Hs|].
    rewrite map_acc_cons. cbn [fst]. apply IHr, Hx, Hs.
  - destruct b; try discriminate; cbn [of_block fst].
    + apply register_id_inv, H.
    + apply assign_heading_id_inv, H.
Qed.

Lemma of_list_inv :
  forall bs st, id_inv st -> id_inv (fst (of_list bs st)).
Proof.
  unfold of_list. induction bs as [|[p a b] rest IH]; intros st H; [exact H|].
  rewrite map_acc_cons. cbn [fst]. apply IH, of_block_inv, H.
Qed.

(*
The pass in document order
--------------------------
*)

(* The pass at one block: a heading gets its identifier, and any other
   block's own identifier is taken. *)
Definition visit (n : node block) (st : id_state) : id_state * node block :=
  match n with
  | Node p a (Heading lvl ils) => assign_heading_id p a lvl ils st
  | Node _ a _ => (register_id a st, n)
  end.

Definition is_heading (n : node block) : bool :=
  match node_contents n with Heading _ _ => true | _ => false end.

(* No section at any depth.  The pass does not enter one, and the line
   fold builds none. *)
Definition no_sections (bs : blocks) : bool :=
  forallb (fun n => match node_contents n with Section _ => false | _ => true end)
    (preorder bs).

Lemma no_sections_cons : forall n bs,
  no_sections (n :: bs)
  = (match node_contents n with Section _ => false | _ => true end
     && no_sections (children (node_contents n)) && no_sections bs)%bool.
Proof.
  intros n bs. unfold no_sections. rewrite preorder_cons. cbn [forallb].
  rewrite forallb_app, below_children, andb_assoc. reflexivity.
Qed.

(* Two listings with the same attributes and the same headings. *)
Local Definition agrees (out spec : blocks) : Prop :=
  map (@node_attrs _) out = map (@node_attrs _) spec
  /\ filter is_heading out = filter is_heading spec.

Local Lemma agrees_app : forall o1 s1 o2 s2,
  agrees o1 s1 -> agrees o2 s2 -> agrees (o1 ++ o2)%list (s1 ++ s2)%list.
Proof.
  intros o1 s1 o2 s2 [A1 H1] [A2 H2]. split.
  - rewrite !map_app, A1, A2. reflexivity.
  - rewrite !filter_app, H1, H2. reflexivity.
Qed.

Local Definition in_order (n : node block) : Prop :=
  forall st, no_sections [n] = true ->
    fst (of_node n st) = fst (map_acc visit (preorder [n]) st)
    /\ agrees (preorder [snd (of_node n st)])
              (snd (map_acc visit (preorder [n]) st)).

Local Lemma of_nodes_in_order : forall l,
  Forall in_order l ->
  forall st, no_sections l = true ->
    fst (of_list l st) = fst (map_acc visit (preorder l) st)
    /\ agrees (preorder (snd (of_list l st)))
              (snd (map_acc visit (preorder l) st)).
Proof.
  assert (PA : forall l1 l2 : blocks,
            preorder (l1 ++ l2)%list = (preorder l1 ++ preorder l2)%list)
    by (intros; apply flat_map_app).
  unfold of_list.
  induction 1 as [|n l Hn _ IH]; intros st Hs; [split; [|split]; reflexivity|].
  rewrite no_sections_cons in Hs. apply andb_true_iff in Hs as [Hn' Hl].
  assert (Hn1 : no_sections [n] = true)
    by (rewrite no_sections_cons, Hn'; reflexivity).
  destruct (Hn st Hn1) as [F1 A1].
  destruct (IH (fst (of_node n st)) Hl) as [F2 A2].
  rewrite map_acc_cons. cbn [fst snd].
  change (n :: l) with ([n] ++ l)%list.
  change (snd (of_node n st) :: snd (map_acc of_node l (fst (of_node n st))))
    with ([snd (of_node n st)]
          ++ snd (map_acc of_node l (fst (of_node n st))))%list.
  rewrite !PA, map_acc_app. cbn [fst snd]. rewrite <- F1.
  split; [exact F2|]. apply agrees_app; assumption.
Qed.

Local Lemma of_node_in_order : forall b p a, in_order (Node p a b).
Proof.
  intros b. induction b as [b IH] using block_children_ind. intros p a st Hs.
  rewrite no_sections_cons in Hs. cbn [node_contents] in Hs.
  apply andb_true_iff in Hs as [Hs _]. apply andb_true_iff in Hs as [Hb Hc].
  unfold preorder. cbn [flat_map node_contents of_node]. rewrite !app_nil_r.
  destruct (plain_block b) eqn:Hp.
  - rewrite of_block_plain by exact Hp. cbn [fst snd node_contents].
    assert (V : visit (Node p a b) st = (register_id a st, Node p a b))
      by (destruct b; try discriminate; reflexivity).
    rewrite map_acc_cons, V. cbn [fst snd].
    rewrite map_acc_children_fst, !below_children, map_acc_children_snd.
    assert (NH : forall x, plain_block x = true -> is_heading (Node p a x) = false)
      by (intros x Hx; destruct x; try discriminate; reflexivity).
    assert (Hch : Forall in_order (children b)).
    { apply Forall_forall. intros [q c x] Hn. rewrite Forall_forall in IH.
      exact (IH _ Hn q c). }
    destruct (of_nodes_in_order (children b) Hch (register_id a st) Hc)
      as [F [A1 A2]].
    split; [exact F|]. split.
    + cbn [map node_attrs]. f_equal. exact A1.
    + cbn [filter].
      rewrite (NH b Hp),
        (NH _ (eq_trans (plain_block_map_acc_children _ _ _ _) Hp)).
      exact A2.
  - (* a heading: the pass is `visit` itself *)
    destruct b as [| |lvl ils| | | | | | | | | | | | | | |]; try discriminate.
    cbn [of_block below fold_children map_acc preorder flat_map visit].
    assert (E : node_contents (snd (assign_heading_id p a lvl ils st))
                = Heading lvl ils)
      by (unfold assign_heading_id; destruct (alist_lookup "id" a); reflexivity).
    rewrite E. destruct (assign_heading_id p a lvl ils st) as [s1 y].
    split; [reflexivity|split; reflexivity].
Qed.

(** The pass is `visit` applied to the document's blocks in document
    order, nested ones included: it ends in the same state, every block
    has the attributes `visit` gives it, and the headings are the ones
    `visit` gives. *)
Theorem of_list_document_order : forall bs st,
  no_sections bs = true ->
  fst (of_list bs st) = fst (map_acc visit (preorder bs) st)
  /\ map (@node_attrs _) (preorder (snd (of_list bs st)))
     = map (@node_attrs _) (snd (map_acc visit (preorder bs) st))
  /\ filter is_heading (preorder (snd (of_list bs st)))
     = filter is_heading (snd (map_acc visit (preorder bs) st)).
Proof.
  intros bs st H. apply of_nodes_in_order; [|exact H].
  apply Forall_forall. intros [p a b] _. apply of_node_in_order.
Qed.

(* `visit` keeps what the pass keeps. *)
Local Lemma visit_inv : forall n st, id_inv st -> id_inv (fst (visit n st)).
Proof.
  intros [p a b] st H.
  destruct b; cbn [visit fst];
    first [apply assign_heading_id_inv, H | apply register_id_inv, H].
Qed.

(* The derived identifiers are distinct and are among the taken ones. *)
Local Definition derived_ok (st : id_state) : Prop :=
  NoDup (id_derived st) /\ incl (id_derived st) (id_used st).

Local Lemma visit_derived_ok : forall n st,
  id_inv st -> derived_ok st -> derived_ok (fst (visit n st)).
Proof.
  assert (R : forall a st, derived_ok st -> derived_ok (register_id a st)).
  { intros a st [N I]. unfold register_id.
    destruct (alist_lookup "id" a); [|split; assumption].
    split; [exact N|]. intros x Hx. right. apply I, Hx. }
  assert (A : forall l i st, derived_ok st -> derived_ok (add_auto_ref l i st)).
  { intros l i st D. unfold add_auto_ref.
    destruct (StrSet.mem l (id_ref_labels st)); exact D. }
  intros [p a b] st Hinv D. destruct b; cbn [visit fst]; try (apply R, D).
  unfold assign_heading_id. destruct (alist_lookup "id" a) eqn:Ha; cbn [fst];
    apply A.
  - unfold register_id. rewrite Ha. destruct D as [N I].
    split; [exact N|]. intros x Hx. right. apply I, Hx.
  - destruct D as [N I].
    destruct (fresh_for_spec st (id_base (inlines_text ils)) Hinv) as [Hc _].
    rewrite Hc.
    destruct (unique_id_fresh (id_used st) (id_base (inlines_text ils)))
      as [_ Hf].
    split; cbn [id_derived id_used take_id].
    + constructor; [|exact N]. intros Hin. apply Hf, I, Hin.
    + intros x [<-|Hx]; [left; reflexivity|right; apply I, Hx].
Qed.

(** Every heading the pass leaves carries an identifier, at any depth. *)
Theorem headings_identified : forall bs st,
  no_sections bs = true ->
  Forall (fun n => is_heading n = true -> alist_lookup "id" (node_attrs n) <> None)
    (preorder (snd (of_list bs st))).
Proof.
  intros bs st H. destruct (of_list_document_order bs st H) as (_ & _ & Hh).
  assert (Q : forall l s,
            Forall (fun n => is_heading n = true ->
                             alist_lookup "id" (node_attrs n) <> None)
              (snd (map_acc visit l s))).
  { induction l as [|[p a b] l IH]; intros s; [constructor|].
    rewrite map_acc_cons. cbn [snd]. constructor; [|apply IH].
    destruct b; cbn [visit snd]; try (intros X; discriminate X).
    unfold assign_heading_id. destruct (alist_lookup "id" a) eqn:E;
      cbn [snd node_attrs]; intros _; [rewrite E|cbn]; discriminate. }
  apply Forall_forall. intros o Ho Hhd.
  assert (Hin : In o (filter is_heading (snd (map_acc visit (preorder bs) st))))
    by (rewrite <- Hh; apply filter_In; split; assumption).
  apply filter_In in Hin as [Hin _].
  exact (proj1 (Forall_forall _ _) (Q _ _) o Hin Hhd).
Qed.

(** The identifiers the pass derives are pairwise distinct.  An
    identifier written on a later block can still repeat one. *)
Theorem derived_ids_distinct : forall bs,
  no_sections bs = true ->
  NoDup (id_derived (fst (of_list bs id_state_init))).
Proof.
  intros bs H. destruct (of_list_document_order bs id_state_init H) as [-> _].
  assert (L : forall l st, id_inv st -> derived_ok st ->
                derived_ok (fst (map_acc visit l st))).
  { induction l as [|n l IH]; intros st Hi Hd; [exact Hd|].
    rewrite map_acc_cons. cbn [fst].
    apply IH; [apply visit_inv, Hi|apply visit_derived_ok; assumption]. }
  apply L; [apply id_inv_init|].
  split; [constructor|intros x []].
Qed.

End WithTable.
End Ids.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(*
Section nesting
===============
*)

(* A stack of open sections, innermost first.  Each entry carries the
   heading level that opened it, the attributes moved off that heading,
   and the blocks collected so far in reverse.  The bottom entry is the
   document, at level 0: no heading level is <= 0, so it is never closed
   and the stack is never empty. *)
(* The section builder and the pass are the only parts of this file that
   build a node of their own, so they are the only ones the position
   policy reaches.  Closing the section before the lemmas below leaves
   every one of them at the semantic instance. *)
Section WithPolicy.
Context {P : PosPolicy}.

Definition sect_state : Type := list (nat * attr * blocks).

Local Definition sect_init : sect_state := [(0, [], [])].

(* Close every section a level-`lvl` heading interrupts, carrying the
   already-closed nodes inward-out in `pending` so each lands inside the
   section that encloses it.  Recursion is on the stack, so this is
   structural: `pending` is what lets the current section nest into its
   parent before the parent is tested. *)
(* A section covers its heading and everything under it, which is
   exactly the children it is built from. *)
Definition section_node (a : attr) (bs : blocks) : node block :=
  Node (hull_pos_with bs) a (Section bs).

Fixpoint close_ge (lvl : nat) (pending : blocks) (stk : sect_state)
  : sect_state :=
  match stk with
  | [] => []
  | [(l, a, acc)] => [(l, a, (pending ++ acc)%list)]
  | (l, a, acc) :: outer =>
      if Nat.leb lvl l
      then close_ge lvl [section_node a (rev (pending ++ acc))] outer
      else ((l, a, (pending ++ acc)%list) :: outer)
  end.

(* Equation lemmas, as everywhere else in this development: `cbn` on
   close_ge reduces the *recursive* call as well, and an induction
   hypothesis about it then no longer matches. *)
Local Lemma close_ge_singleton :
  forall lvl pending l a acc,
    close_ge lvl pending [(l, a, acc)] = [(l, a, (pending ++ acc)%list)].
Proof. reflexivity. Qed.

Local Lemma close_ge_cons :
  forall lvl pending l a acc outer,
    outer <> [] ->
    close_ge lvl pending ((l, a, acc) :: outer)
    = if Nat.leb lvl l
      then close_ge lvl [section_node a (rev (pending ++ acc))] outer
      else ((l, a, (pending ++ acc)%list) :: outer).
Proof. intros lvl pending l a acc [|e outer] H; [contradiction|reflexivity]. Qed.

(* End of input closes every open section, whatever its level.  Testing
   levels here would be wrong as well as unnecessary: a level-0 heading
   would leave its entry open, and sect_bottom would then drop it and
   everything it had collected. *)
Fixpoint close_all (pending : blocks) (stk : sect_state) : sect_state :=
  match stk with
  | [] => []
  | [(l, a, acc)] => [(l, a, (pending ++ acc)%list)]
  | (l, a, acc) :: outer =>
      close_all [section_node a (rev (pending ++ acc))] outer
  end.

Lemma close_all_cons :
  forall pending l a acc outer,
    outer <> [] ->
    close_all pending ((l, a, acc) :: outer)
    = close_all [section_node a (rev (pending ++ acc))] outer.
Proof. intros pending l a acc [|e outer] H; [contradiction|reflexivity]. Qed.

Definition sect_push (b : node block) (stk : sect_state) : sect_state :=
  match stk with
  | [] => []
  | (l, a, acc) :: rest => (l, a, b :: acc) :: rest
  end.

(* A heading closes the sections it interrupts, then opens its own with
   the heading as its first child.  The id moves from the heading to the
   section. *)
Definition sect_step (stk : sect_state) (n : node block) : sect_state :=
  match n with
  | Node p a (Heading lvl ils) =>
      (lvl, a, [Node p [] (Heading lvl ils)]) :: close_ge lvl [] stk
  | _ => sect_push n stk
  end.

(* The document's own accumulator, once every section above it is closed. *)
Fixpoint sect_bottom (stk : sect_state) : blocks :=
  match stk with
  | [] => []
  | [(_, _, acc)] => rev acc
  | _ :: outer => sect_bottom outer
  end.

Definition sectionize (bs : blocks) : blocks :=
  sect_bottom (close_all [] (fold_left sect_step bs sect_init)).

(*
The pass
========
*)

(*
Reference definitions
=====================

A definition contributes no HTML and no structure, only an entry in the
document's map, which is why it is collected here rather than in the
line fold, and why `Undo.pass` below needs no arm for it: the pass reads
the block tree and does not touch it.

Nesting is not a barrier: a definition inside a quote or a list item
registers with the document all the same, so the traversal descends
into every container the fold can build.
*)

(* Keyed by normalized label, assigned the way a JS object is: a repeated
   label keeps the first definition's position and takes the last one's
   value.  An empty label is dropped before normalization, so `[ ]: u`,
   whose normalized label is empty, is still recorded. *)
Local Definition add_ref (p : pos) (a : attr) (b : block) (m : reference_map)
  : reference_map :=
  match b with
  | RefDef label dest =>
      if nonempty_str label
      then alist_set (normalize_label label) (dest, a) m
      else m
  | _ => m
  end.

End WithPolicy.
End WithTable.
Module Refs.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.
Section WithPolicy.
Context {P : PosPolicy}.

(* Pre-order, which is document order. *)
Local Fixpoint of_block (b : block) (p : pos) (a : attr) (m : reference_map)
  {struct b} : reference_map :=
  fold_children (fun acc n => match n with Node p' a' x => of_block x p' a' acc end)
    b (add_ref p a b m).

Local Fixpoint of_list (ns : blocks) (m : reference_map) : reference_map :=
  match ns with
  | [] => m
  | Node p a b :: rest => of_list rest (of_block b p a m)
  end.

Local Lemma of_block_children : forall b p a m,
  of_block b p a m = of_list (children b) (add_ref p a b m).
Proof.
  intros b p a m.
  assert (L : forall ns acc,
            fold_left (fun acc n => match n with Node p' a' x => of_block x p' a' acc end) ns acc
            = of_list ns acc)
    by (induction ns as [|[p' a' x] rest IH]; intros acc; [reflexivity|apply IH]).
  rewrite <- L, <- fold_children_spec. destruct b; reflexivity.
Qed.

End WithPolicy.
End WithTable.
End Refs.

(*
Footnote definitions
====================

Collected the way reference definitions are: the pass reads the tree and
leaves it as it is.  An entry is the definition's body as it stands in
the tree, so a definition written inside another stays in its parent's
body and has an entry of its own as well.
*)

Module Notes.

(* Keyed by normalized label and assigned like `add_ref`.  A definition
   is assigned after its body, the order in which nested containers
   close.  `Section` has an arm so that the map can be read back off
   `doc_blocks` (`doc_footnotes_of_blocks`). *)
Definition add_note (b : block) (m : note_map) : note_map :=
  match b with
  | FootnoteDef label bs => alist_set (normalize_label label) bs m
  | _ => m
  end.

Fixpoint of_block (b : block) (m : note_map) {struct b} : note_map :=
  add_note b (fold_children (fun acc n => match n with Node _ _ x => of_block x acc end) b m).

Fixpoint of_list (ns : blocks) (m : note_map) : note_map :=
  match ns with
  | [] => m
  | Node _ _ b :: rest => of_list rest (of_block b m)
  end.

Lemma of_list_app : forall l1 l2 m,
  of_list (l1 ++ l2)%list m = of_list l2 (of_list l1 m).
Proof.
  induction l1 as [|[p a b] rest IH]; intros l2 m; [reflexivity|].
  cbn [app of_list]. apply IH.
Qed.

Lemma of_block_children : forall b m,
  of_block b m = add_note b (of_list (children b) m).
Proof.
  intros b m.
  assert (L : forall ns acc,
            fold_left (fun acc n => match n with Node _ _ x => of_block x acc end) ns acc
            = of_list ns acc)
    by (induction ns as [|[p' a' x] rest IH]; intros acc; [reflexivity|apply IH]).
  rewrite <- L, <- fold_children_spec. destruct b; reflexivity.
Qed.

End Notes.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.
Section WithPolicy.
Context {P : PosPolicy}.

Definition doc_pass (bs : blocks) : doc :=
  let (st, bs') := Ids.of_list bs id_state_init in
  {| doc_blocks := sectionize bs'
   ; doc_footnotes := Notes.of_list bs' []
   ; doc_references := Refs.of_list bs' []
   ; doc_auto_references := rev (id_refs st)
   ; doc_auto_identifiers := rev (id_derived st) |}.

(** Parse a Djot document: first run the line fold, then perform
    whole-document resolution. *)
Definition parse_doc (s : string) : doc := doc_pass (parse_blocks s).

End WithPolicy.

(* Outside the policy section every mention means the semantic instance,
   where a section is the node it always was. *)
Lemma section_node_nopos :
  forall a bs, @section_node semantic_pos a bs = Node NoPos a (Section bs).
Proof. reflexivity. Qed.

Local Ltac nosect := rewrite ?section_node_nopos.

(* The located document: the same pass over the located block parse. *)
Definition parse_doc_located (s : string) : doc :=
  @doc_pass located_pos (parse_blocks_located s).

(*
Erasure
=======

The pass only adds, and what it adds is recoverable: a section is
exactly its heading plus the blocks that followed it, and an
auto-identifier is exactly an "id" attribute on a heading that carried
none.  `Undo.pass` takes both back out in one traversal, and
`pass_erase` says it takes out precisely what the pass put in.  That is
what keeps Roundtrip.v's theorem meaningful above the block layer:
render, parse, erase is the identity.
*)

(* Oriented like alist_lookup, so the two compose without an eqb flip. *)
Local Definition strip_id (a : attr) : attr :=
  filter (fun kv => negb (String.eqb "id" (fst kv))) a.

Local Lemma strip_id_absent :
  forall a, alist_lookup "id" a = None -> strip_id a = a.
Proof.
  induction a as [|[k v] rest IH]; intros H; [reflexivity|].
  cbn [alist_lookup] in H. cbn [strip_id filter fst].
  destruct (String.eqb "id" k); [discriminate|].
  cbn [negb]. f_equal. apply IH. exact H.
Qed.

Local Lemma strip_id_cons :
  forall v a, alist_lookup "id" a = None -> strip_id (("id", v) :: a) = a.
Proof.
  intros v a H. cbn [strip_id filter fst].
  rewrite String.eqb_refl. cbn [negb].
  apply strip_id_absent. exact H.
Qed.

(* A section's attributes came off the heading that opened it, which
   sectionize left as its first child. *)
Local Definition set_first (a : attr) (bs : blocks) : blocks :=
  match bs with
  | [] => []
  | Node p _ x :: rest => Node p a x :: rest
  end.

End WithTable.
Module Undo.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(* Stripping the id *before* handing the attributes back is what makes
   one traversal enough: the identifier the pass added rides on the
   section, so it has to come off there.

   `Section` is the one block whose undo is not a single node, and
   `sectionize` builds none below the top level, so under a key the
   `hd` default is unreachable and the payload comes back as itself. *)
Local Fixpoint pass_block (b : block) (p : pos) (a : attr) {struct b}
  : blocks :=
  let node (n : node block) : blocks :=
    match n with Node p' a' x => pass_block x p' a' end in
  match b with
  | Section inner => set_first (strip_id a) (flat_map node inner)
  | Heading _ _ => [Node p (strip_id a) b]
  | _ => [Node p a (map_children (flat_map node) (fun n => hd n (node n)) b)]
  end.

Local Definition pass_node (n : node block) : blocks :=
  match n with Node p a b => pass_block b p a end.

Fixpoint pass (bs : blocks) : blocks :=
  match bs with
  | [] => []
  | Node p a b :: rest => (pass_block b p a ++ pass rest)%list
  end.

Local Lemma pass_flat_map : forall bs, pass bs = flat_map pass_node bs.
Proof.
  induction bs as [|[p a b] rest IH]; [reflexivity|].
  cbn [pass flat_map pass_node]. rewrite IH. reflexivity.
Qed.

Local Lemma pass_section :
  forall inner p a,
    pass_block (Section inner) p a
    = set_first (strip_id a) (pass inner).
Proof. intros inner p a. rewrite pass_flat_map. reflexivity. Qed.

Local Lemma pass_block_plain :
  forall b p a,
    plain_block b = true ->
    pass_block b p a
    = [Node p a (map_children (flat_map pass_node) (fun n => hd n (pass_node n)) b)].
Proof. intros b p a H. destruct b; try discriminate; reflexivity. Qed.

Local Lemma pass_cons :
  forall n rest, pass (n :: rest) = (pass_node n ++ pass rest)%list.
Proof. intros [p a b] rest. reflexivity. Qed.

Local Lemma pass_single : forall n, pass [n] = pass_node n.
Proof. intros [p a b]. cbn [pass pass_node]. apply app_nil_r. Qed.

Local Lemma pass_app :
  forall l1 l2, pass (l1 ++ l2)%list = (pass l1 ++ pass l2)%list.
Proof.
  induction l1 as [|[p a b] rest IH]; intros l2; [reflexivity|].
  cbn [app pass]. rewrite IH, app_assoc. reflexivity.
Qed.

End WithTable.
End Undo.

(* The tree without its attribute blocks, for a consumer that wants
   block attributes only where they attach.  One stays: an attribute
   block that is the one block of a key, which a key cannot be without.
   Nothing else changes, a list's spacing included, and the HTML is the
   same (`Html.html_tree_drop_attr_blocks`). *)
Module DropAttrBlocks.

Definition is_attr_block (b : block) : bool :=
  match b with AttrBlock => true | _ => false end.

Fixpoint of_block (b : block) {struct b} : block :=
  let node (n : node block) : node block :=
    match n with Node p a x => Node p a (of_block x) end in
  map_children
    (flat_map (fun n => if is_attr_block (node_contents n) then [] else [node n]))
    node b.

Definition of_node (n : node block) : node block :=
  match n with Node p a x => Node p a (of_block x) end.

Definition of_list (bs : blocks) : blocks :=
  flat_map (fun n => if is_attr_block (node_contents n) then [] else [of_node n]) bs.

Lemma of_block_children : forall b,
  of_block b = map_children of_list of_node b.
Proof. intros b. destruct b; reflexivity. Qed.

Definition of_doc (d : doc) : doc :=
  Doc (of_list (doc_blocks d))
      (map (fun note => (fst note, of_list (snd note))) (doc_footnotes d))
      (doc_references d) (doc_auto_references d) (doc_auto_identifiers d).

End DropAttrBlocks.

(* The sections taken back off, ids kept: a section is its blocks, and
   its attributes go back to the heading it opens with.  A section that
   opens with anything else loses them.  Top level only, which is where
   `sectionize` builds sections. *)
Fixpoint unsection_block (b : block) (p : pos) (a : attr) {struct b}
  : blocks :=
  match b with
  | Section inner =>
      match (fix go (ns : blocks) : blocks :=
               match ns with
               | [] => []
               | Node p' a' x :: rest =>
                   (unsection_block x p' a' ++ go rest)%list
               end) inner with
      | Node hp _ (Heading lvl ils) :: rest =>
          Node hp a (Heading lvl ils) :: rest
      | bs => bs
      end
  | _ => [Node p a b]
  end.

Definition unsection (bs : blocks) : blocks :=
  flat_map (fun n => match n with Node p a b => unsection_block b p a end) bs.

Module Pristine.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(* Input the pass has not already run on: no sections, and no heading
   carrying an explicit id.  Checked in every container `Ids.of_block`
   descends into. *)
Local Fixpoint of_block (b : block) (a : attr) {struct b} : bool :=
  match b with
  | Section _ => false
  | Heading _ _ =>
      match alist_lookup "id" a with Some _ => false | None => true end
  | _ =>
      fold_children
        (fun acc n => match n with Node _ a' x => (acc && of_block x a')%bool end)
        b true
  end.

Local Definition of_node (n : node block) : bool :=
  match n with Node _ a b => of_block b a end.

Fixpoint of_list (bs : blocks) : bool :=
  match bs with
  | [] => true
  | Node _ a b :: rest => (of_block b a && of_list rest)%bool
  end.

Local Lemma cons :
  forall p a b rest,
    of_list (Node p a b :: rest) = (of_block b a && of_list rest)%bool.
Proof. reflexivity. Qed.

Local Lemma cons_node :
  forall n rest, of_list (n :: rest) = (of_node n && of_list rest)%bool.
Proof. intros [p a b] rest. reflexivity. Qed.

Local Lemma of_block_plain :
  forall b a, plain_block b = true -> of_block b a = of_list (children b).
Proof.
  assert (F : forall l c,
            fold_left (fun acc n => match n with Node _ a' x => (acc && of_block x a')%bool end)
              l c = (c && of_list l)%bool).
  { induction l as [|[p a x] rest IH]; intros c; cbn [fold_left of_list].
    - symmetry. apply andb_true_r.
    - rewrite IH. symmetry. apply andb_assoc. }
  intros b a H.
  transitivity (fold_children
    (fun acc n => match n with Node _ a' x => (acc && of_block x a')%bool end) b true).
  - destruct b; try discriminate; reflexivity.
  - rewrite fold_children_spec. apply F.
Qed.

Local Lemma of_list_forall : forall bs n,
  of_list bs = true -> In n bs -> of_node n = true.
Proof.
  induction bs as [|x rest IH]; intros n H Hn; [destruct Hn|].
  rewrite cons_node in H. apply andb_true_iff in H as [H1 H2].
  destruct Hn as [<-|Hn]; [exact H1|exact (IH n H2 Hn)].
Qed.

End WithTable.
End Pristine.

Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.
Local Ltac nosect := rewrite ?section_node_nopos.

(*
Undoing the identifiers
-----------------------
*)

(* A list comes back when each of its nodes does. *)
Local Lemma undo_assign_ids_nodes :
  forall l st,
    Forall (fun n => forall s, Undo.pass_node (snd (Ids.of_node n s)) = [n]) l ->
    Undo.pass (snd (Ids.of_list l st)) = l.
Proof.
  unfold Ids.of_list. induction l as [|n l IH]; intros st H; [reflexivity|].
  inversion H as [|? ? Hn Hl]; subst.
  rewrite map_acc_cons. cbn [snd]. rewrite Undo.pass_cons, Hn, IH by exact Hl.
  reflexivity.
Qed.

Local Lemma undo_assign_ids :
  forall b p a st,
    Pristine.of_block b a = true ->
    Undo.pass_node (snd (Ids.of_block b p a st)) = [Node p a b].
Proof.
  intros b. induction b as [b IH] using block_children_ind. intros p a st H.
  destruct (plain_block b) eqn:Hp.
  - rewrite Pristine.of_block_plain in H by exact Hp.
    assert (C : forall n, In n (children b) ->
                forall s, Undo.pass_node (snd (Ids.of_node n s)) = [n]).
    { intros [q c x] Hn s. rewrite Forall_forall in IH. cbn [Ids.of_node].
      apply (IH _ Hn). exact (Pristine.of_list_forall _ _ H Hn). }
    rewrite Ids.of_block_plain by exact Hp. cbn [snd Undo.pass_node].
    rewrite Undo.pass_block_plain
      by (rewrite plain_block_map_acc_children; exact Hp).
    do 2 f_equal. apply map_children_map_acc_children.
    + intros l s Hl. rewrite <- Undo.pass_flat_map.
      apply undo_assign_ids_nodes. revert Hl. apply Forall_impl. exact C.
    + intros n s Hn. rewrite C by exact Hn. reflexivity.
  - destruct b; try discriminate.
    (* Heading; a section is excluded by `Pristine.of_block` *)
    cbn [Pristine.of_block] in H.
    unfold Ids.of_block, assign_heading_id.
    destruct (alist_lookup "id" a) as [v|] eqn:Eid; [discriminate|].
    cbn [snd Undo.pass_node Undo.pass_block].
    rewrite strip_id_cons by exact Eid. reflexivity.
Qed.

Local Lemma undo_assign_ids_list :
  forall bs st,
    Pristine.of_list bs = true -> Undo.pass (snd (Ids.of_list bs st)) = bs.
Proof.
  intros bs st H. apply undo_assign_ids_nodes, Forall_forall.
  intros [p a b] Hn s. apply undo_assign_ids.
  exact (Pristine.of_list_forall _ _ H Hn).
Qed.

(*
Undoing the sections
--------------------

Unconditional: sectionize only ever wraps, and Undo.pass unwraps.  A
`Section` already present in the input is flattened the same way on both
sides, so it needs no hypothesis; only the identifier half cares what
the input looked like.
*)

Local Lemma set_first_app :
  forall z X Y,
    nonempty X = true -> set_first z (X ++ Y)%list = (set_first z X ++ Y)%list.
Proof. intros z [|[p a b] X'] Y H; [discriminate|reflexivity]. Qed.

(* The blocks the stack has consumed so far, recovered.  Entries hold
   their accumulators reversed, and every entry above the document's
   carries the attributes that came off its heading, hence the
   set_first, which is why those entries have to erase to something
   nonempty.  That, plus "only the document sits at level 0", is the
   whole invariant. *)
Local Fixpoint stack_erase (stk : sect_state) : blocks :=
  match stk with
  | [] => []
  | [(_, _, acc)] => Undo.pass (rev acc)
  | (_, a, acc) :: outer =>
      (stack_erase outer ++ set_first (strip_id a) (Undo.pass (rev acc)))%list
  end.

(* The only thing erasure needs of the stack: every entry above the
   document's erases to something nonempty, so that set_first has a node
   to put the section's attributes back on.  True by construction: such
   an entry always starts with the heading that opened it. *)
Local Fixpoint sect_ok (stk : sect_state) : bool :=
  match stk with
  | [] => false
  | [_] => true
  | (_, _, acc) :: outer => (nonempty (Undo.pass (rev acc)) && sect_ok outer)%bool
  end.

Local Lemma stack_erase_cons :
  forall l a acc outer,
    outer <> [] ->
    stack_erase ((l, a, acc) :: outer)
    = (stack_erase outer ++ set_first (strip_id a) (Undo.pass (rev acc)))%list.
Proof. intros l a acc [|e outer] H; [contradiction|reflexivity]. Qed.

Local Lemma sect_ok_cons :
  forall l a acc outer,
    outer <> [] ->
    sect_ok ((l, a, acc) :: outer)
    = (nonempty (Undo.pass (rev acc)) && sect_ok outer)%bool.
Proof. intros l a acc [|e outer] H; [contradiction|reflexivity]. Qed.

Local Lemma sect_ok_nonnil : forall stk, sect_ok stk = true -> stk <> [].
Proof. intros [|e stk] H; [discriminate|congruence]. Qed.

Local Lemma close_ge_ok :
  forall stk lvl pending,
    sect_ok stk = true -> sect_ok (close_ge lvl pending stk) = true.
Proof.
  induction stk as [|[[l a] acc] outer IH]; intros lvl pending Hs;
    [discriminate|].
  destruct outer as [|e outer']; [exact Hs|].
  rewrite sect_ok_cons in Hs by discriminate.
  apply andb_true_iff in Hs as [Hne Houter].
  rewrite close_ge_cons by discriminate. destruct (Nat.leb lvl l).
  - apply IH. exact Houter.
  - rewrite sect_ok_cons by discriminate.
    rewrite Houter, andb_true_r.
    rewrite rev_app_distr, Undo.pass_app.
    destruct (Undo.pass (rev acc)) as [|x r]; [discriminate|reflexivity].
Qed.

Local Lemma close_ge_erase :
  forall stk lvl pending,
    sect_ok stk = true ->
    stack_erase (close_ge lvl pending stk)
    = (stack_erase stk ++ Undo.pass (rev pending))%list.
Proof.
  induction stk as [|[[l a] acc] outer IH]; intros lvl pending Hs;
    [discriminate|].
  destruct outer as [|e outer'].
  - rewrite close_ge_singleton. cbn [stack_erase].
    rewrite rev_app_distr, Undo.pass_app. reflexivity.
  - rewrite sect_ok_cons in Hs by discriminate.
    apply andb_true_iff in Hs as [Hne Houter].
    rewrite stack_erase_cons by discriminate.
    rewrite close_ge_cons by discriminate. destruct (Nat.leb lvl l).
    + rewrite (IH _ _ Houter).
      nosect. cbn [Undo.pass rev app]. rewrite app_nil_r.
      rewrite Undo.pass_section, rev_app_distr, Undo.pass_app.
      rewrite set_first_app by exact Hne.
      rewrite app_assoc. reflexivity.
    + rewrite stack_erase_cons by discriminate.
      rewrite rev_app_distr, Undo.pass_app.
      rewrite set_first_app by exact Hne.
      rewrite app_assoc. reflexivity.
Qed.

(* close_all always lands on the document entry alone, which is what
   lets sect_bottom read the answer off. *)
Local Lemma close_all_singleton :
  forall stk pending,
    stk <> [] -> exists l a acc, close_all pending stk = [(l, a, acc)].
Proof.
  induction stk as [|[[l a] acc] outer IH]; intros pending H; [contradiction|].
  destruct outer as [|e outer'].
  - exists l, a, (pending ++ acc)%list. reflexivity.
  - rewrite close_all_cons by discriminate. apply IH. discriminate.
Qed.

Local Lemma close_all_erase :
  forall stk pending,
    sect_ok stk = true ->
    stack_erase (close_all pending stk)
    = (stack_erase stk ++ Undo.pass (rev pending))%list.
Proof.
  induction stk as [|[[l a] acc] outer IH]; intros pending Hs; [discriminate|].
  destruct outer as [|e outer'].
  - cbn [close_all stack_erase].
    rewrite rev_app_distr, Undo.pass_app. reflexivity.
  - rewrite sect_ok_cons in Hs by discriminate.
    apply andb_true_iff in Hs as [Hne Houter].
    rewrite stack_erase_cons by discriminate.
    rewrite close_all_cons by discriminate.
    rewrite (IH _ Houter).
    nosect. cbn [Undo.pass rev app]. rewrite app_nil_r.
    rewrite Undo.pass_section, rev_app_distr, Undo.pass_app.
    rewrite set_first_app by exact Hne.
    rewrite app_assoc. reflexivity.
Qed.

Local Lemma sect_push_ok :
  forall stk n, sect_ok stk = true -> sect_ok (sect_push n stk) = true.
Proof.
  intros [|[[l a] acc] outer] n Hs; [discriminate|].
  cbn [sect_push]. destruct outer as [|e outer']; [exact Hs|].
  rewrite sect_ok_cons in Hs |- * by discriminate.
  apply andb_true_iff in Hs as [Hne Houter].
  rewrite Houter, andb_true_r.
  cbn [rev]. rewrite Undo.pass_app.
  destruct (Undo.pass (rev acc)) as [|x r]; [discriminate|reflexivity].
Qed.

Local Lemma sect_push_erase :
  forall stk n,
    sect_ok stk = true ->
    stack_erase (sect_push n stk) = (stack_erase stk ++ Undo.pass_node n)%list.
Proof.
  intros [|[[l a] acc] outer] n Hs; [discriminate|].
  cbn [sect_push]. destruct outer as [|e outer'].
  - cbn [stack_erase rev]. rewrite Undo.pass_app, Undo.pass_single.
    reflexivity.
  - rewrite sect_ok_cons in Hs by discriminate.
    apply andb_true_iff in Hs as [Hne _].
    rewrite !stack_erase_cons by discriminate.
    cbn [rev]. rewrite Undo.pass_app, Undo.pass_single.
    rewrite set_first_app by exact Hne.
    rewrite app_assoc. reflexivity.
Qed.

Local Lemma sect_step_ok :
  forall stk n, sect_ok stk = true -> sect_ok (sect_step stk n) = true.
Proof.
  intros stk [p a b] Hs. destruct b; try (apply sect_push_ok; exact Hs).
  cbn [sect_step].
  pose proof (close_ge_ok stk level [] Hs) as Hc.
  destruct (close_ge level [] stk) as [|e rest] eqn:E; [discriminate|].
  rewrite sect_ok_cons by discriminate.
  rewrite Hc, andb_true_r.
  (* a heading erases to exactly one block, so the entry is nonempty *)
  cbn [rev Undo.pass Undo.pass_block app nonempty]. reflexivity.
Qed.

Local Lemma sect_step_erase :
  forall stk n,
    sect_ok stk = true ->
    stack_erase (sect_step stk n) = (stack_erase stk ++ Undo.pass_node n)%list.
Proof.
  intros stk [p a b] Hs. destruct b; try (apply sect_push_erase; exact Hs).
  cbn [sect_step].
  pose proof (close_ge_ok stk level [] Hs) as Hc.
  pose proof (close_ge_erase stk level [] Hs) as He.
  destruct (close_ge level [] stk) as [|e rest] eqn:E; [discriminate|].
  rewrite stack_erase_cons by discriminate.
  rewrite He. cbn [rev Undo.pass]. rewrite app_nil_r.
  cbn [rev Undo.pass Undo.pass_node Undo.pass_block strip_id filter
       set_first app].
  reflexivity.
Qed.

Local Lemma fold_sect_step_ok :
  forall bs stk,
    sect_ok stk = true -> sect_ok (fold_left sect_step bs stk) = true.
Proof.
  induction bs as [|n rest IH]; intros stk Hs; [exact Hs|].
  cbn [fold_left]. apply IH. apply sect_step_ok. exact Hs.
Qed.

Local Lemma fold_sect_step_erase :
  forall bs stk,
    sect_ok stk = true ->
    stack_erase (fold_left sect_step bs stk)
    = (stack_erase stk ++ Undo.pass bs)%list.
Proof.
  induction bs as [|n rest IH]; intros stk Hs.
  - cbn [fold_left Undo.pass]. rewrite app_nil_r. reflexivity.
  - cbn [fold_left]. rewrite IH by (apply sect_step_ok; exact Hs).
    rewrite sect_step_erase by exact Hs.
    rewrite Undo.pass_cons, app_assoc. reflexivity.
Qed.

(** Sectioning is invisible to erasure: it only wraps, and Undo.pass
    unwraps exactly what it wrapped. *)
Lemma undo_sectionize :
  forall bs, Undo.pass (sectionize bs) = Undo.pass bs.
Proof.
  intros bs. unfold sectionize.
  pose proof (fold_sect_step_ok bs sect_init eq_refl) as Hok.
  pose proof (fold_sect_step_erase bs sect_init eq_refl) as Her.
  cbn [stack_erase rev Undo.pass] in Her.
  destruct (close_all_singleton _ [] (sect_ok_nonnil _ Hok)) as [l [a [acc E]]].
  pose proof (close_all_erase _ [] Hok) as Hc.
  rewrite E in Hc. cbn [stack_erase rev Undo.pass] in Hc.
  rewrite app_nil_r in Hc.
  rewrite E. cbn [sect_bottom].
  rewrite Hc, Her. reflexivity.
Qed.

(*
Sections and the note map
-------------------------

`sectionize` only wraps, and the notes pass reads through a `Section`, so
the map is the same collected before sectioning or after.  Stated at any
position policy, since a section's position is not read.
*)

Section WithPolicy.
Context {P : PosPolicy}.

(* The map collected from the blocks the stack holds, outermost entry
   first, which is document order. *)
Local Fixpoint stack_notes (stk : sect_state) (m : note_map) : note_map :=
  match stk with
  | [] => m
  | (_, _, acc) :: outer => Notes.of_list (rev acc) (stack_notes outer m)
  end.

Local Lemma section_node_notes :
  forall a bs m, Notes.of_list [section_node a bs] m = Notes.of_list bs m.
Proof.
  intros a bs m. unfold section_node. cbn [Notes.of_list].
  rewrite Notes.of_block_children. reflexivity.
Qed.

Local Lemma close_ge_notes :
  forall stk lvl pending m,
    stk <> [] ->
    stack_notes (close_ge lvl pending stk) m
    = Notes.of_list (rev pending) (stack_notes stk m).
Proof.
  induction stk as [|[[l a] acc] outer IH]; intros lvl pending m H;
    [contradiction|].
  destruct outer as [|e outer'].
  - rewrite close_ge_singleton. cbn [stack_notes].
    rewrite rev_app_distr, Notes.of_list_app. reflexivity.
  - rewrite close_ge_cons by discriminate. destruct (Nat.leb lvl l).
    + rewrite IH by discriminate. cbn [rev app].
      rewrite section_node_notes, rev_app_distr, Notes.of_list_app.
      reflexivity.
    + cbn [stack_notes]. rewrite rev_app_distr, Notes.of_list_app.
      reflexivity.
Qed.

Local Lemma close_all_notes :
  forall stk pending m,
    stk <> [] ->
    Notes.of_list (sect_bottom (close_all pending stk)) m
    = Notes.of_list (rev pending) (stack_notes stk m).
Proof.
  induction stk as [|[[l a] acc] outer IH]; intros pending m H;
    [contradiction|].
  destruct outer as [|e outer'].
  - cbn [close_all sect_bottom stack_notes].
    rewrite rev_app_distr, Notes.of_list_app. reflexivity.
  - rewrite close_all_cons by discriminate.
    rewrite IH by discriminate. cbn [rev app].
    rewrite section_node_notes, rev_app_distr, Notes.of_list_app.
    reflexivity.
Qed.

Local Lemma sect_step_notes :
  forall stk n m,
    stk <> [] ->
    sect_step stk n <> []
    /\ stack_notes (sect_step stk n) m
       = Notes.of_list [n] (stack_notes stk m).
Proof.
  intros stk [p a b] m H.
  destruct b;
    try (destruct stk as [|[[l a'] acc] outer]; [contradiction|];
         cbn [sect_step sect_push stack_notes rev];
         rewrite Notes.of_list_app; split; [discriminate|reflexivity]).
  (* a heading holds no definition, and neither does what it closes *)
  cbn [sect_step stack_notes rev app]. split; [discriminate|].
  rewrite close_ge_notes by exact H. reflexivity.
Qed.

Local Lemma fold_sect_step_notes :
  forall bs stk m,
    stk <> [] ->
    fold_left sect_step bs stk <> []
    /\ stack_notes (fold_left sect_step bs stk) m
       = Notes.of_list bs (stack_notes stk m).
Proof.
  induction bs as [|n rest IH]; intros stk m H; [split; [exact H|reflexivity]|].
  destruct (sect_step_notes stk n m H) as [Hne Hn].
  destruct (IH (sect_step stk n) m Hne) as [Hne' Hrest].
  cbn [fold_left]. split; [exact Hne'|].
  rewrite Hrest, Hn. destruct n as [p a b]. reflexivity.
Qed.

Lemma sectionize_notes :
  forall bs m, Notes.of_list (sectionize bs) m = Notes.of_list bs m.
Proof.
  intros bs m. unfold sectionize.
  destruct (fold_sect_step_notes bs sect_init m ltac:(discriminate))
    as [Hne Hn].
  rewrite close_all_notes by exact Hne. rewrite Hn. reflexivity.
Qed.

(** The note map is a function of the document's blocks. *)
Theorem doc_footnotes_of_blocks :
  forall bs,
    doc_footnotes (doc_pass bs) = Notes.of_list (doc_blocks (doc_pass bs)) [].
Proof.
  intros bs. unfold doc_pass.
  destruct (Ids.of_list bs id_state_init) as [st bs'].
  cbn [doc_footnotes doc_blocks]. symmetry. apply sectionize_notes.
Qed.

End WithPolicy.

(*
The theorem
-----------
*)

(** The whole-document pass adds only structure that erasure recovers:
    on input the pass has not already run on, undoing it is exact. *)
Theorem pass_erase :
  forall bs, Pristine.of_list bs = true -> Undo.pass (doc_blocks (doc_pass bs)) = bs.
Proof.
  intros bs H. unfold doc_pass.
  destruct (Ids.of_list bs id_state_init) as [st bs'] eqn:E.
  cbn [doc_blocks]. rewrite undo_sectionize.
  replace bs' with (snd (Ids.of_list bs id_state_init))
    by (rewrite E; reflexivity).
  apply undo_assign_ids_list. exact H.
Qed.

(*
Erasure of the side tables
==========================

The document pass reads the tree and writes two side tables; erasing a
located tree's positions has to give the document the pass produces on
the erased tree.  The traversals below are the pos-blind half of that:
none of `Ids.of_block`, `Notes.of_block` or `Refs.of_block` reads a
position, so each commutes with `Erase.of_blocks` structurally.  The
sectionizer is the other half and is not here.

`erase_note_map` and `erase_doc` are the erasure of the two maps and of
the record; `doc_references`, `doc_auto_references` and
`doc_auto_identifiers` hold no nodes, so they are carried through.
*)

Local Lemma inlines_text_cons : forall (n : node inline) (rest : inlines),
  inlines_text (n :: rest)%list
  = (inline_text (node_contents n) ++ inlines_text rest)%string.
Proof.
  intros n rest. unfold inlines_text. cbn [map].
  destruct rest as [|y rest].
  - cbn [String.concat]. symmetry. apply append_empty_r.
  - reflexivity.
Qed.

Local Lemma inline_text_go : forall ns,
  (fix go (ns : list (node inline)) : string :=
     match ns with
     | [] => ""
     | Node _ _ x :: rest => (inline_text x ++ go rest)%string
     end) ns = inlines_text ns.
Proof.
  induction ns as [|[p a x] rest IH]; [reflexivity|].
  rewrite inlines_text_cons. cbn [inline_text]. rewrite IH. reflexivity.
Qed.

Local Lemma inline_text_erase : forall il,
  inline_text (Erase.of_inline il) = inline_text il.
Proof.
  induction il using inline_ind2 with
    (Q := fun ils =>
       (fix go (ns : list (node inline)) : string :=
          match ns with
          | [] => ""
          | Node _ _ x :: rest => (inline_text x ++ go rest)%string
          end) (Erase.of_inlines ils)
       = (fix go (ns : list (node inline)) : string :=
          match ns with
          | [] => ""
          | Node _ _ x :: rest => (inline_text x ++ go rest)%string
          end) ils);
    cbn [Erase.of_inline inline_text].
  all: try reflexivity.
  all: try (rewrite Erase.inline_children; assumption).
  - (* hcons *)
    rewrite Erase.inlines_cons. cbn [Erase.inode inline_text].
    congruence.
Qed.

Local Lemma inlines_text_erase : forall ils,
  inlines_text (Erase.of_inlines ils) = inlines_text ils.
Proof.
  induction ils as [|[p a x] rest IH]; [reflexivity|].
  rewrite Erase.inlines_cons. cbn [Erase.inode node_contents].
  rewrite inlines_text_cons. cbn [node_contents].
  rewrite inlines_text_cons. cbn [node_contents].
  rewrite IH, inline_text_erase. reflexivity.
Qed.

Local Definition erase_note_map (m : note_map) : note_map :=
  map (fun kv => (fst kv, Erase.of_blocks (snd kv))) m.

Definition erase_doc (d : doc) : doc :=
  {| doc_blocks := Erase.of_blocks (doc_blocks d)
   ; doc_footnotes := erase_note_map (doc_footnotes d)
   ; doc_references := doc_references d
   ; doc_auto_references := doc_auto_references d
   ; doc_auto_identifiers := doc_auto_identifiers d |}.

Local Lemma erase_note_map_alist_set : forall k v m,
  erase_note_map (alist_set k v m)
  = alist_set k (Erase.of_blocks v) (erase_note_map m).
Proof.
  intros k v m. induction m as [|[k' v'] rest IH];
    cbn [alist_set fst snd]; [reflexivity|].
  destruct (String.eqb k k') eqn:E.
  - cbn [erase_note_map map alist_set fst snd]. rewrite E. reflexivity.
  - cbn [erase_note_map map alist_set fst snd]. rewrite E.
    change ((k', Erase.of_blocks v') :: erase_note_map (alist_set k v rest)
            = (k', Erase.of_blocks v') :: alist_set k (Erase.of_blocks v)
                (erase_note_map rest)).
    rewrite IH. reflexivity.
Qed.

(* The item erasures as `Erase.of_block` spells them internally, bridged to
   the map form the statements below use. *)
Local Lemma erase_items_fix : forall its,
  (fix goitems (its : list (node blocks)) : list (node blocks) :=
     match its with
     | [] => []
     | Node _ a item :: rest => Node NoPos a (Erase.of_blocks item) :: goitems rest
     end) its = map Erase.item its.
Proof.
  induction its as [|[ip ia it] rest IH]; [reflexivity|].
  cbn [map Erase.item Erase.task_item Erase.def_entry Erase.inlines_node]. rewrite IH. reflexivity.
Qed.

Local Lemma erase_def_items_fix : forall its,
  (fix godefs (its : list (node (node inlines * node blocks)))
      : list (node (node inlines * node blocks)) :=
     match its with
     | [] => []
     | Node _ a (term, Node _ b item) :: rest =>
         Node NoPos a (Erase.inlines_node term, Node NoPos b (Erase.of_blocks item))
         :: godefs rest
     end) its
  = map Erase.def_entry its.
Proof.
  induction its as [|[ip ia [term [dp da it]]] rest IH]; [reflexivity|].
  cbn [map Erase.item Erase.task_item Erase.def_entry Erase.inlines_node]. rewrite IH. reflexivity.
Qed.

Local Lemma erase_task_items_fix : forall its,
  (fix gotasks (its : list (node (task_status * blocks)))
      : list (node (task_status * blocks)) :=
     match its with
     | [] => []
     | Node _ a (status, item) :: rest =>
         Node NoPos a (status, Erase.of_blocks item) :: gotasks rest
     end) its
  = map Erase.task_item its.
Proof.
  induction its as [|[ip ia [status it]] rest IH]; [reflexivity|].
  cbn [map Erase.item Erase.task_item Erase.def_entry Erase.inlines_node]. rewrite IH. reflexivity.
Qed.

(* Erasure keeps a block's children. *)
Local Lemma erase_children : forall b,
  children (Erase.of_block b) = Erase.of_blocks (children b).
Proof.
  assert (F : forall (A : Type) (g : A -> blocks) (e : A -> A),
            (forall x, g (e x) = Erase.of_blocks (g x)) ->
            forall its, flat_map g (map e its) = Erase.of_blocks (flat_map g its)).
  { intros A g e H. induction its as [|x its IH]; [reflexivity|].
    cbn [map flat_map]. rewrite Erase.blocks_app, H, IH. reflexivity. }
  intros b. destruct b as [| | | | | | | | | | | | | | | |? []|];
    cbn [Erase.of_block Ast.children]; fold Erase.of_blocks; try reflexivity.
  - rewrite erase_items_fix. apply F. intros []; reflexivity.
  - rewrite erase_items_fix. apply F. intros []; reflexivity.
  - rewrite erase_task_items_fix. apply F. intros [? ? []]; reflexivity.
  - rewrite erase_def_items_fix. apply F. intros [? ? [? []]]; reflexivity.
Qed.

(*
Ids.of_block
*)

Local Definition erase_node (n : node block) : node block :=
  match n with Node _ a b => Node NoPos a (Erase.of_block b) end.

Local Lemma erase_blocks_map : forall bs, Erase.of_blocks bs = map erase_node bs.
Proof.
  induction bs as [|[p a b] rest IH]; [reflexivity|].
  cbn [Erase.of_blocks map erase_node]. rewrite IH. reflexivity.
Qed.

(* A stateful map that commutes with `e` at each element commutes with
   it over the list. *)
Local Lemma map_acc_commute :
  forall (S A : Type) (k k' : A -> S -> S * A) (e : A -> A) (l : list A),
    (forall x, In x l -> forall s, k' (e x) s = (fst (k x s), e (snd (k x s)))) ->
    forall s, map_acc k' (map e l) s
              = (fst (map_acc k l s), map e (snd (map_acc k l s))).
Proof.
  intros S A k k' e. induction l as [|x l IH]; intros H s; [reflexivity|].
  cbn [map]. rewrite !map_acc_cons, H by (left; reflexivity). cbn [fst snd map].
  rewrite IH by (intros y Hy; apply H; right; exact Hy). reflexivity.
Qed.

(* The same for a rebuild: erasure keeps a block's children, so a
   rebuild that commutes with it at each child commutes with it. *)
Local Lemma map_acc_children_erase :
  forall (S : Type) (f f' : node block -> S -> S * node block) b st,
    (forall n, In n (children b) ->
       forall s, f' (erase_node n) s = (fst (f n s), erase_node (snd (f n s)))) ->
    map_acc_children f' (Erase.of_block b) st
    = (fst (map_acc_children f b st),
       Erase.of_block (snd (map_acc_children f b st))).
Proof.
  intros S f f' b st H.
  assert (I : forall (l : blocks) s,
            (forall n, In n l -> In n (children b)) ->
            map_acc f' (Erase.of_blocks l) s
            = (fst (map_acc f l s), Erase.of_blocks (snd (map_acc f l s)))).
  { intros l s Hl. rewrite !erase_blocks_map. apply map_acc_commute.
    intros n Hn. apply H, Hl, Hn. }
  (* An item's blocks are among the list's children. *)
  Local Ltac item_blocks I Hit :=
    unfold map_acc_node, map_acc_snd, Erase.item, Erase.task_item, Erase.def_entry;
    cbn [fst snd];
    rewrite I by (intros n Hn; apply in_flat_map; eexists; split; [exact Hit|exact Hn]);
    match goal with |- context [map_acc ?f ?x ?s] => destruct (map_acc f x s) end;
    reflexivity.
  Local Ltac items_done st :=
    match goal with |- context [map_acc ?k ?items st] =>
      destruct (map_acc k items st) as [s1 l1] end;
    cbn [fst snd Erase.of_block]; fold Erase.of_blocks;
    rewrite ?erase_items_fix, ?erase_def_items_fix, ?erase_task_items_fix;
    reflexivity.
  destruct b as [| | | | | | | | | | | | | | | |? []|];
    cbn [Erase.of_block map_acc_children Ast.children] in *; fold Erase.of_blocks;
    rewrite ?erase_items_fix, ?erase_def_items_fix, ?erase_task_items_fix;
    try reflexivity.
  all: try (rewrite I by (intros; assumption);
            destruct (map_acc f _ st) as [s1 l1]; reflexivity).
  - rewrite (map_acc_commute S _ (map_acc_node (map_acc f))
               (map_acc_node (map_acc f')) Erase.item items); [items_done st|].
    intros [q c x] Hit s. item_blocks I Hit.
  - rewrite (map_acc_commute S _ (map_acc_node (map_acc f))
               (map_acc_node (map_acc f')) Erase.item items); [items_done st|].
    intros [q c x] Hit s. item_blocks I Hit.
  - rewrite (map_acc_commute S _ (map_acc_node (map_acc_snd (map_acc f)))
               (map_acc_node (map_acc_snd (map_acc f'))) Erase.task_item items);
      [items_done st|].
    intros [q c [t x]] Hit s. item_blocks I Hit.
  - rewrite (map_acc_commute S _
               (map_acc_node (map_acc_snd (map_acc_node (map_acc f))))
               (map_acc_node (map_acc_snd (map_acc_node (map_acc f'))))
               Erase.def_entry items); [items_done st|].
    intros [q c [t [r d x]]] Hit s. item_blocks I Hit.
  - change (Node NoPos a (Erase.of_block x)) with (erase_node (Node p a x)).
    rewrite H by (left; reflexivity).
    destruct (f (Node p a x) st) as [s1 [q c y]]. reflexivity.
Qed.

Local Lemma assign_ids_erase :
  forall b p a st,
    Ids.of_block (Erase.of_block b) NoPos a st
    = (fst (Ids.of_block b p a st), erase_node (snd (Ids.of_block b p a st))).
Proof.
  intros b. induction b as [b IH] using block_children_ind. intros p a st.
  destruct (plain_block b) eqn:Hp.
  - rewrite !Ids.of_block_plain by (rewrite ?plain_block_erase; exact Hp).
    cbn [fst snd erase_node].
    rewrite (map_acc_children_erase _ Ids.of_node Ids.of_node b).
    + reflexivity.
    + intros [q c x] Hn s. rewrite Forall_forall in IH. exact (IH _ Hn q c s).
  - destruct b; try discriminate.
    + reflexivity.
    + cbn [Erase.of_block Ids.of_block]. unfold assign_heading_id.
      rewrite inlines_text_erase.
      destruct (alist_lookup "id" a); reflexivity.
Qed.

Local Lemma assign_ids_list_erase : forall bs st,
  fst (Ids.of_list (Erase.of_blocks bs) st) = fst (Ids.of_list bs st)
  /\ Erase.of_blocks (snd (Ids.of_list bs st))
     = snd (Ids.of_list (Erase.of_blocks bs) st).
Proof.
  intros bs st. unfold Ids.of_list. rewrite !erase_blocks_map.
  rewrite (map_acc_commute _ _ Ids.of_node Ids.of_node erase_node).
  - split; reflexivity.
  - intros [p a b] _ s. apply assign_ids_erase.
Qed.

(*
Notes.of_block
*)

Local Lemma collect_notes_erase : forall b m,
  Notes.of_block (Erase.of_block b) (erase_note_map m)
  = erase_note_map (Notes.of_block b m).
Proof.
  intros b. induction b as [b IH] using block_children_ind. intros m.
  rewrite !Notes.of_block_children, erase_children.
  assert (L : Notes.of_list (Erase.of_blocks (children b)) (erase_note_map m)
              = erase_note_map (Notes.of_list (children b) m)).
  { revert m. induction IH as [|[q c x] rest Hx _ IHr]; intros m; [reflexivity|].
    cbn [Erase.of_blocks Notes.of_list node_contents] in *. rewrite Hx. apply IHr. }
  rewrite L. destruct b as [| | | | | | | | | | | | | | | |? []|]; try reflexivity.
  (* FootnoteDef: the body is erased both in the tree and in its entry *)
  cbn [Erase.of_block Notes.add_note]. fold Erase.of_blocks.
  rewrite erase_note_map_alist_set. reflexivity.
Qed.

Local Lemma collect_notes_list_erase : forall ns m,
  Notes.of_list (Erase.of_blocks ns) (erase_note_map m)
  = erase_note_map (Notes.of_list ns m).
Proof.
  induction ns as [|[p a b] rest IH]; intros m; [reflexivity|].
  cbn [Erase.of_blocks Notes.of_list].
  rewrite (collect_notes_erase b m), IH. reflexivity.
Qed.

(*
Refs.of_block
*)

Local Lemma collect_refs_erase : forall b p a m,
  Refs.of_block (Erase.of_block b) NoPos a m = Refs.of_block b p a m.
Proof.
  intros b. induction b as [b IH] using block_children_ind. intros p a m.
  rewrite !Refs.of_block_children, erase_children.
  replace (add_ref NoPos a (Erase.of_block b) m) with (add_ref p a b m)
    by (destruct b as [| | | | | | | | | | | | | | | |? []|]; reflexivity).
  generalize (add_ref p a b m). induction IH as [|[q c x] rest Hx _ IHr]; intros m'; [reflexivity|].
  cbn [Erase.of_blocks Refs.of_list node_contents] in *. rewrite (Hx q c m'). apply IHr.
Qed.

Local Lemma collect_refs_list_erase : forall ns m,
  Refs.of_list (Erase.of_blocks ns) m = Refs.of_list ns m.
Proof.
  induction ns as [|[p a b] rest IH]; intros m; [reflexivity|].
  cbn [Erase.of_blocks Refs.of_list].
  rewrite (collect_refs_erase b p a m), IH. reflexivity.
Qed.
(* The sectionizer is the one part of the pass that reads a position:
   `section_node` takes the hull of the children it wraps.  Erasure of
   the stack is erasure of each entry's accumulator. *)
Local Fixpoint erase_sect (stk : sect_state) : sect_state :=
  match stk with
  | [] => []
  | (l, a, acc) :: rest => (l, a, Erase.of_blocks acc) :: erase_sect rest
  end.

Local Lemma section_node_pos : forall a bs,
  Erase.of_blocks [@section_node located_pos a bs]
  = [@section_node semantic_pos a (Erase.of_blocks bs)].
Proof.
  intros a bs. cbn [Erase.of_blocks Erase.of_block section_node]. fold Erase.of_blocks.
  rewrite section_node_nopos. reflexivity.
Qed.

Local Lemma close_ge_pos : forall lvl pending stk,
  erase_sect (@close_ge located_pos lvl pending stk) =
  @close_ge semantic_pos lvl (Erase.of_blocks pending) (erase_sect stk).
Proof.
  intros lvl pending stk. revert lvl pending.
  induction stk as [|[[l a] acc] outer IH]; intros lvl pending.
  - reflexivity.
  - destruct outer as [|e outer'].
    + rewrite (@close_ge_singleton located_pos). cbn [erase_sect].
      rewrite (@close_ge_singleton semantic_pos), Erase.blocks_app.
      reflexivity.
    + destruct e as [[l1 a1] acc1].
      rewrite (@close_ge_cons located_pos) by discriminate.
      cbn [erase_sect].
      rewrite (@close_ge_cons semantic_pos) by discriminate.
      destruct (Nat.leb lvl l).
      * rewrite IH, section_node_pos, Erase.blocks_rev, Erase.blocks_app.
        cbn [erase_sect]. reflexivity.
      * cbn [erase_sect]. rewrite Erase.blocks_app. reflexivity.
Qed.

Local Lemma close_all_pos : forall pending stk,
  erase_sect (@close_all located_pos pending stk) =
  @close_all semantic_pos (Erase.of_blocks pending) (erase_sect stk).
Proof.
  intros pending stk. revert pending.
  induction stk as [|[[l a] acc] outer IH]; intros pending.
  - reflexivity.
  - destruct outer as [|[[l1 a1] acc1] outer'].
    + cbn [close_all erase_sect]. rewrite Erase.blocks_app. reflexivity.
    + rewrite (@close_all_cons located_pos) by discriminate.
      cbn [erase_sect].
      rewrite (@close_all_cons semantic_pos) by discriminate.
      rewrite IH, section_node_pos.
      rewrite Erase.blocks_rev, Erase.blocks_app. reflexivity.
Qed.

Local Lemma sect_push_pos : forall p a b stk,
  erase_sect (sect_push (Node p a b) stk) =
  sect_push (Node NoPos a (Erase.of_block b)) (erase_sect stk).
Proof. intros p a b [|[[l a'] acc] outer]; reflexivity. Qed.

Local Lemma sect_step_pos : forall stk p a b,
  erase_sect (@sect_step located_pos stk (Node p a b)) =
  @sect_step semantic_pos (erase_sect stk) (Node NoPos a (Erase.of_block b)).
Proof.
  intros stk p a b. destruct b;
    try (cbn [sect_step]; apply sect_push_pos).
  (* a key's node has to be destructured before `Erase.of_block` reduces *)
  2: (destruct b; cbn [sect_step Erase.of_block]; apply sect_push_pos).
  cbn [sect_step erase_sect Erase.of_blocks Erase.of_block].
  rewrite close_ge_pos. reflexivity.
Qed.

Local Lemma fold_sect_step_pos : forall bs stk,
  erase_sect (fold_left (@sect_step located_pos) bs stk) =
  fold_left (@sect_step semantic_pos) (Erase.of_blocks bs) (erase_sect stk).
Proof.
  induction bs as [|[p a b] rest IH]; intros stk; [reflexivity|].
  cbn [fold_left Erase.of_blocks]. rewrite IH, sect_step_pos. reflexivity.
Qed.

Local Lemma sect_bottom_pos : forall stk,
  Erase.of_blocks (sect_bottom stk) = sect_bottom (erase_sect stk).
Proof.
  induction stk as [|[[l a] acc] outer IH]; [reflexivity|].
  destruct outer as [|[[l1 a1] acc1] outer'].
  - cbn [sect_bottom erase_sect]. apply Erase.blocks_rev.
  - cbn [erase_sect]. cbn [sect_bottom]. cbn [erase_sect] in IH. exact IH.
Qed.

Local Lemma sectionize_erase : forall bs,
  Erase.of_blocks (@sectionize located_pos bs) =
  @sectionize semantic_pos (Erase.of_blocks bs).
Proof.
  intros bs. unfold sectionize.
  rewrite sect_bottom_pos, close_all_pos, fold_sect_step_pos.
  reflexivity.
Qed.

(* The pass as a whole.  Three of its four components never read a
   position, so erasing the blocks they are given commutes with each;
   the fourth is the sectionizer above. *)
Local Lemma doc_pass_erase : forall bs,
  erase_doc (@doc_pass located_pos bs) =
  @doc_pass semantic_pos (Erase.of_blocks bs).
Proof.
  intros bs. unfold doc_pass.
  destruct (Ids.of_list bs id_state_init) as [st tagged] eqn:E.
  destruct (Ids.of_list (Erase.of_blocks bs) id_state_init)
    as [st' tagged'] eqn:E'.
  destruct (assign_ids_list_erase bs id_state_init) as [Hst Htagged].
  rewrite E, E' in Hst, Htagged. cbn [fst snd] in Hst, Htagged.
  subst st' tagged'.
  unfold erase_doc.
  cbn [doc_blocks doc_footnotes doc_references doc_auto_references
    doc_auto_identifiers].
  rewrite sectionize_erase, collect_refs_list_erase.
  rewrite <- (collect_notes_list_erase tagged []). reflexivity.
Qed.

(* The located document is the semantic one with positions on it. *)
Theorem parse_doc_located_erase : forall s,
  erase_doc (parse_doc_located s) = @parse_doc T K semantic_pos s.
Proof.
  intros s. unfold parse_doc_located, parse_doc.
  rewrite doc_pass_erase, parse_blocks_located_erase. reflexivity.
Qed.

(*
Replacing lines
===============

The document pass runs over the whole spliced block list.  The examples
at the end of this file show what it changes outside an edit.
*)

Theorem parse_doc_pieces :
  forall s, @parse_doc T K semantic_pos s
            = doc_pass (pieces_tree (sem_pieces (split_lines s))).
Proof.
  intros s. unfold parse_doc, parse_blocks. rewrite pieces_parse. reflexivity.
Qed.

Corollary parse_doc_splice :
  forall ls i j new s,
    let cs := sem_pieces ls in
    i <= j -> j <= length cs ->
    split_lines s
      = (pieces_text (firstn i cs) ++ new ++ pieces_text (skipn j cs))%list ->
    @parse_doc T K semantic_pos s
    = doc_pass (pieces_tree (splice sem_step finish cs i j new)).
Proof.
  intros ls i j new s cs Hij Hj Hs. unfold parse_doc, parse_blocks.
  rewrite Hs. f_equal. apply splice_parse; assumption.
Qed.

Corollary parse_doc_located_splice :
  forall ls i j new s,
    let cs := loc_pieces ls in
    i <= j -> j <= length cs ->
    split_lines s
      = (pieces_text (firstn i cs) ++ new ++ pieces_text (skipn j cs))%list ->
    parse_doc_located s
    = @doc_pass located_pos
        (assemble 0 (splice loc_step (@finish T K located_pos) cs i j new)).
Proof.
  intros ls i j new s cs Hij Hj Hs. unfold parse_doc_located.
  rewrite (splice_located ls i j new s Hij Hj Hs). reflexivity.
Qed.

(*
Examples
========

Each is a case from djot.js/test/headings.test, checked at the AST level.
*)

End WithTable.

Example section_simple :
  doc_blocks (parse_doc "## Heading")
  = [Node NoPos [("id", "Heading")]
       (Section [mk (Heading 2 [mk (Str "Heading")])])].
Proof. reflexivity. Qed.

Example section_nested :
  doc_blocks (parse_doc "## Heading
### Next level")
  = [Node NoPos [("id", "Heading")]
       (Section [ mk (Heading 2 [mk (Str "Heading")])
                ; Node NoPos [("id", "Next-level")]
                    (Section [mk (Heading 3 [mk (Str "Next level")])]) ])].
Proof. reflexivity. Qed.

Example section_siblings :
  doc_blocks (parse_doc "# Heading

# another")
  = [ Node NoPos [("id", "Heading")]
        (Section [mk (Heading 1 [mk (Str "Heading")])])
    ; Node NoPos [("id", "another")]
        (Section [mk (Heading 1 [mk (Str "another")])]) ].
Proof. reflexivity. Qed.

(* A multi-line heading's id joins its lines: the SoftBreak contributes a
   newline, which is an id separator. *)
Example section_multiline_id :
  doc_auto_identifiers (parse_doc "# Heading
continued") = ["Heading-continued"].
Proof. reflexivity. Qed.

(* An empty heading has an empty base, so the disambiguator starts at 1. *)
Example section_empty_id :
  doc_auto_identifiers (parse_doc "##") = ["s-1"].
Proof. reflexivity. Qed.

Example section_duplicate_ids :
  doc_auto_identifiers (parse_doc "# Foo bar

## Foo  bar") = ["Foo-bar"; "Foo-bar-1"].
Proof. reflexivity. Qed.

(* Explicit ids occupy the same rendered fragment namespace as automatic
   heading ids.  They remain distinct for editing: only the former came
   from stable source identity. *)
Example explicit_id_displaces_auto_id :
  doc_auto_identifiers (parse_doc "{#x}
a

# x") = ["x-1"].
Proof. reflexivity. Qed.

(* A written id that repeats a derived one comes after it, since a
   derived id steps around every id before its heading.  So the first
   heading with a listed id is the one it was derived for. *)
Example written_id_repeats_derived :
  let d := parse_doc "# x

{#x}
# y" in
  doc_auto_identifiers d = ["x"]
  /\ map node_attrs (doc_blocks d) = [[("id", "x")]; [("id", "x")]].
Proof. split; reflexivity. Qed.

(* Sections are top-level only: inside a quote the heading keeps its id. *)
Example quote_heading_unsectioned :
  doc_blocks (parse_doc "> # Heading")
  = [mk (BlockQuote
           [Node NoPos [("id", "Heading")]
              (Heading 1 [mk (Str "Heading")])])].
Proof. reflexivity. Qed.

(* The map keys by normalized label, and a repeated label keeps the first
   definition's position with the last one's value. *)
Example reference_map_last_wins :
  doc_references (parse_doc "[a]: u

[b]: w

[a]: v")
  = [("a", ("v", [])); ("b", ("w", []))].
Proof. reflexivity. Qed.

(* A definition inside a container still registers with the document. *)
Example reference_map_nested :
  doc_references (parse_doc "> [q]: u

- [l]: v")
  = [("q", ("u", [])); ("l", ("v", []))].
Proof. reflexivity. Qed.

(* Block attributes on the definition ride into the map, where the HTML
   renderer puts them on the link. *)
Example reference_map_attributes :
  doc_references (parse_doc "{#x}
[a]: u")
  = [("a", ("u", [("id", "x")]))].
Proof. reflexivity. Qed.

(* An empty raw label is dropped before normalization, so `[]: u` defines
   nothing while `[ ]: u`, whose normalized label is also empty, does. *)
Example reference_map_empty_label_dropped :
  doc_references (parse_doc "[]: u") = [].
Proof. reflexivity. Qed.

Example reference_map_blank_label_kept :
  doc_references (parse_doc "[ ]: u") = [("", ("u", []))].
Proof. reflexivity. Qed.

Example footnote_map_last_wins :
  doc_footnotes (parse_doc "[^a]: one

[^a]: two")
  = [("a", [mk (Para [mk (Str "two")])])].
Proof. reflexivity. Qed.

Example footnote_map_normalized_label :
  doc_footnotes (parse_doc "[^A  B]: one

[^A B]: two")
  = [("A B", [mk (Para [mk (Str "two")])])].
Proof. reflexivity. Qed.

(* The inner definition has its own entry and stays in the outer one's
   body, which is the body as the tree has it. *)
Example footnote_map_nested_close_order :
  doc_footnotes (parse_doc "[^a]: outer

  [^b]: inner")
  = [ ("b", [mk (Para [mk (Str "inner")])])
    ; ("a", [ mk (Para [mk (Str "outer")])
            ; mk (FootnoteDef "b" [mk (Para [mk (Str "inner")])]) ]) ].
Proof. reflexivity. Qed.

Example footnote_stays_inside_quote :
  doc_blocks (parse_doc "> [^a]: note")
  = [mk (BlockQuote [mk (FootnoteDef "a" [mk (Para [mk (Str "note")])])])].
Proof. reflexivity. Qed.

(* A definition under a heading is in that heading's section. *)
Example footnote_inside_section :
  doc_blocks (parse_doc "# h

[^a]: note")
  = [Node NoPos [("id", "h")]
       (Section [ mk (Heading 1 [mk (Str "h")])
                ; mk (FootnoteDef "a" [mk (Para [mk (Str "note")])]) ])].
Proof. reflexivity. Qed.

Example footnote_heading_shares_identifier_pass :
  doc_auto_identifiers (parse_doc "[^a]: # Heading

# After") = ["Heading"; "After"].
Proof. reflexivity. Qed.

Example implicit_heading_reference :
  doc_auto_references (parse_doc "# Introduction")
  = [("Introduction", ("#Introduction", []))].
Proof. reflexivity. Qed.

(* An explicit id suppresses the auto-*identifier*, not the reference:
   the label is still the heading's text, and it points at the spec's
   id. *)
Example implicit_heading_reference_explicit_id :
  doc_auto_references (parse_doc "{#foo}
# Introduction")
  = [("Introduction", ("#foo", []))].
Proof. reflexivity. Qed.

(* Blocks before the first heading stay at the document level. *)
Example section_preamble :
  doc_blocks (parse_doc "intro

# h")
  = [ mk (Para [mk (Str "intro")])
    ; Node NoPos [("id", "h")] (Section [mk (Heading 1 [mk (Str "h")])]) ].
Proof. reflexivity. Qed.

(* Closing two levels at once: the h3's section nests inside the h2's,
   and both close when the h1 arrives. *)
Example section_close_multiple :
  doc_blocks (parse_doc "## a

### b

# c")
  = [ Node NoPos [("id", "a")]
        (Section [ mk (Heading 2 [mk (Str "a")])
                 ; Node NoPos [("id", "b")]
                     (Section [mk (Heading 3 [mk (Str "b")])]) ])
    ; Node NoPos [("id", "c")]
        (Section [mk (Heading 1 [mk (Str "c")])]) ].
Proof. reflexivity. Qed.

(*
What the pass changes outside an edit
-------------------------------------

Each pair below differs only in its first block.
*)

(* An id taken before a heading renumbers that heading's auto id. *)
Example pass_renumbers_id :
  nth_error (doc_blocks (parse_doc "x

# a")) 1
  = Some (Node NoPos [("id", "a")]
            (Section [Node NoPos [] (Heading 1 [Node NoPos [] (Str "a")])]))
  /\ nth_error (doc_blocks (parse_doc "{#a}
x

# a")) 1
  = Some (Node NoPos [("id", "a-1")]
            (Section [Node NoPos [] (Heading 1 [Node NoPos [] (Str "a")])])).
Proof. split; vm_compute; reflexivity. Qed.

(* A heading moves the blocks after it into its section. *)
Example pass_moves_sections :
  length (doc_blocks (parse_doc "# a

x

y")) = 1
  /\ length (doc_blocks (parse_doc "# a

# b

y")) = 2.
Proof. split; vm_compute; reflexivity. Qed.

(* A reference definition changes the table a link elsewhere resolves
   against, not the link. *)
Example pass_reference_table :
  hd_error (doc_blocks (parse_doc "[t][r]

x"))
  = hd_error (doc_blocks (parse_doc "[t][r]

[r]: u"))
  /\ doc_references (parse_doc "[t][r]

x") = []
  /\ doc_references (parse_doc "[t][r]

[r]: u") = [("r", ("u", []))].
Proof. repeat split; vm_compute; reflexivity. Qed.

(* Likewise a footnote definition and the note map. *)
Example pass_note_map :
  hd_error (doc_blocks (parse_doc "a[^n]

x"))
  = hd_error (doc_blocks (parse_doc "a[^n]

[^n]: x"))
  /\ doc_footnotes (parse_doc "a[^n]

x") = []
  /\ doc_footnotes (parse_doc "a[^n]

[^n]: x")
     = [("n", [Node NoPos [] (Para [Node NoPos [] (Str "x")])])].
Proof. repeat split; vm_compute; reflexivity. Qed.

(* Sections come back off with every id on its heading, derived or
   written. *)
Example unsection_then_pass :
  let d := parse_doc "# a

{#x}
## b

c

# a" in
  unsection (doc_blocks d)
  = [ Node NoPos [("id", "a")] (Heading 1 [mk (Str "a")])
    ; Node NoPos [("id", "x")] (Heading 2 [mk (Str "b")])
    ; mk (Para [mk (Str "c")])
    ; Node NoPos [("id", "a-1")] (Heading 1 [mk (Str "a")]) ].
Proof. reflexivity. Qed.
