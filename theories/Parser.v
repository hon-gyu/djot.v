(* Block parsing: a fold over classified lines with an explicit state.

   The state is a *container stack*, growing inward: an open paragraph
   accumulator (empty = idle), an open code fence collecting verbatim
   lines, or a block quote holding the blocks it has closed so far plus
   the state of its contents.  Per line:
   - inside a fence, only the close test applies — no classification;
   - otherwise KBlank ends any open paragraph, KThematic/KFence start
     blocks only when no paragraph is open (paragraphs can never be
     interrupted — spec), and KText extends or opens a paragraph;
   - KQuote strips its prefix and re-enters `step` on the enclosed line,
     which is where nesting and uniformity both come from: a quote's
     contents run the same transition as the top level.

   `step` is the whole per-line transition (Phase 2's `continue`/`close`/
   `finalize` rolled into one function) and `finish` closes the stack at
   end of input.  `parse_lines` is then a plain fold.

   The equation lemmas at the bottom are the interface the wf and
   roundtrip proofs use; keep them in sync with the definition. *)

From Stdlib Require Import String Ascii List Bool PeanoNat Lia.
From DjotV Require Import Strings Line Ast.
Import ListNotations.

Local Open Scope string_scope.

(*
Paragraph assembly
==================
*)

(* Trailing whitespace is stripped at the end of a paragraph (but kept on
   interior lines) — observed djot.js/djoths behavior on para.test. *)

(* Turn a paragraph's source lines (in order) into inlines: one Str per
   line, SoftBreak between.  Render.inline_lines is the inverse. *)
Fixpoint para_inlines (l : list string) : inlines :=
  match l with
  | [] => []
  | [x] => [mk (Str (strip_trailing_ws x))]
  | x :: rest => mk (Str x) :: mk SoftBreak :: para_inlines rest
  end.

(*
Fenced block assembly
=====================
*)

(* Content is the lines rejoined, each with its newline.  An info string
   starting with '=' makes a raw block (=FORMAT); otherwise it is the
   language of a code block. *)

Definition fence_block (f : fence) (content : list string) : node block :=
  let text := join_nl content in
  match f_info f with
  | String "="%char fmt => mk (RawBlock fmt text)
  | info => mk (CodeBlock info text)
  end.

(*
The line fold
=============
*)

(* The fold's state: a container stack.  Every accumulator holds its
   items in *reverse* order, hence the `rev` at each use site. *)
Inductive pstate : Type :=
  | PPara (cur : list string)              (* [] = no open block *)
  | PFence (f : fence) (acc : list string)
  | PQuote (done : blocks) (inner : pstate).

(* End of input (or of an enclosing container): close everything still
   open, outermost result first. *)
Fixpoint finish (st : pstate) : blocks :=
  match st with
  | PPara [] => []
  | PPara cur => [mk (Para (para_inlines (rev cur)))]
  | PFence f acc => [fence_block f (rev acc)]
  | PQuote done inner => [mk (BlockQuote (rev done ++ finish inner)%list)]
  end.

(* Lazy continuation (djot.js: `isLazy`).  A nonblank, otherwise
   featureless line that is missing its container prefixes still
   continues the innermost open *paragraph* — but nothing else, which is
   why fence content is excluded. *)
Fixpoint lazy_ok (st : pstate) : bool :=
  match st with
  | PPara [] => false
  | PPara (_ :: _) => true
  | PFence _ _ => false
  | PQuote _ inner => lazy_ok inner
  end.

Definition is_lazy (k : line_kind) (inner : pstate) : bool :=
  match k with KText => lazy_ok inner | _ => false end.

(* Append a lazy line to the innermost paragraph, prefixes and all. *)
Fixpoint feed_lazy (l : string) (st : pstate) : pstate :=
  match st with
  | PPara cur => PPara (l :: cur)
  | PFence f acc => PFence f acc      (* excluded by lazy_ok *)
  | PQuote done inner => PQuote done (feed_lazy l inner)
  end.

(* What a line does at an idle state, for every kind but KQuote — which
   needs `step`'s recursive descent and is handled there.  Factored out
   because both "idle at top level" and "a quote just closed, now
   reprocess the line outside it" need exactly this. *)
Definition open_kind (l : string) (k : line_kind) : blocks * pstate :=
  match k with
  | KBlank => ([], PPara [])
  | KThematic => ([mk ThematicBreak], PPara [])
  | KFence f => ([], PFence f [])
  | KText => ([], PPara [l])
  | KQuote _ => ([], PPara [])        (* unreachable: see step *)
  end.

(* The per-line transition, on fuel.  The only recursion is into a
   stripped quote prefix, and `classify_quote_length` says that line is
   strictly shorter — so the line's own length is always enough fuel.
   `step` below fixes it there, and `step_fuel_enough` retires it, so no
   downstream statement mentions fuel. *)
Fixpoint step_fuel (n : nat) (l : string) (st : pstate) : blocks * pstate :=
  match n with
  | O => ([], st)                     (* unreachable from step *)
  | S n' =>
      match st with
      | PFence f acc =>
          if fence_close f l
          then ([fence_block f (rev acc)], PPara [])
          else ([], PFence f (l :: acc))
      | PPara [] =>
          match classify l with
          | KQuote rest =>
              let (bs, inner) := step_fuel n' rest (PPara []) in
              ([], PQuote (rev bs) inner)
          | k => open_kind l k
          end
      | PPara (c :: cur') =>
          match classify l with
          | KBlank => ([mk (Para (para_inlines (rev (c :: cur'))))], PPara [])
          | _ => ([], PPara (l :: c :: cur'))   (* paragraphs never interrupt *)
          end
      | PQuote done inner =>
          match classify l with
          | KQuote rest =>
              let (bs, inner') := step_fuel n' rest inner in
              ([], PQuote (rev bs ++ done)%list inner')
          | k =>
              if is_lazy k inner
              then ([], PQuote done (feed_lazy l inner))
              else
                let (bs, st') := open_kind l k in
                (mk (BlockQuote (rev done ++ finish inner)%list) :: bs, st')
          end
      end
  end.

(* The transition proper: fuel is the line's length, always sufficient. *)
Definition step (l : string) (st : pstate) : blocks * pstate :=
  step_fuel (S (String.length l)) l st.

(* The parser: fold the transition over the lines, then close the stack.
   Structurally recursive on `lines`, so it always terminates and proofs
   can step it one line at a time. *)
Fixpoint parse_lines (lines : list string) (st : pstate) : blocks :=
  match lines with
  | [] => finish st
  | l :: rest =>
      let (bs, st') := step l st in
      (bs ++ parse_lines rest st')%list
  end.

(* Entry point: split the source into lines and fold from the idle state.
   The side tables stay empty until there is an inline pass. *)
Definition parse_doc (s : string) : doc :=
  {| doc_blocks := parse_lines (split_lines s) (PPara [])
   ; doc_footnotes := []
   ; doc_references := []
   ; doc_auto_references := []
   ; doc_auto_identifiers := [] |}.

(*
Equation lemmas
===============

One lemma per branch of `step`, each proved by `cbn` + `rewrite` on the
classification, then lifted to `parse_lines`.  Downstream proofs rewrite
with these instead of calling `simpl` on the parser, which otherwise
unfolds into an unusable match tower. *)

(*
Retiring the fuel
-----------------

Fuel is an implementation detail of `step_fuel`: any amount past the
line's length gives the same answer, so `step` can fix it and no
downstream statement ever mentions it. *)

Lemma step_fuel_stable :
  forall bound n l st,
    n <= bound -> S (String.length l) <= n ->
    step_fuel n l st = step_fuel (S (String.length l)) l st.
Proof.
  induction bound as [|bound IH]; intros n l st Hb Hn; [lia|].
  destruct n as [|n']; [lia|].
  cbn [step_fuel].
  destruct st as [cur|f acc|done inner].
  - destruct cur as [|c cur'].
    + destruct (classify l) as [| |f|rest|] eqn:E; try reflexivity.
      pose proof (classify_quote_length _ _ E) as Hlt.
      rewrite (IH n' rest (PPara [])) by lia.
      rewrite (IH (String.length l) rest (PPara [])) by lia.
      reflexivity.
    + destruct (classify l); reflexivity.
  - destruct (fence_close f l); reflexivity.
  - destruct (classify l) as [| |f|rest|] eqn:E; try reflexivity.
    pose proof (classify_quote_length _ _ E) as Hlt.
    rewrite (IH n' rest inner) by lia.
    rewrite (IH (String.length l) rest inner) by lia.
    reflexivity.
Qed.

Lemma step_fuel_enough :
  forall n l st, S (String.length l) <= n -> step_fuel n l st = step l st.
Proof. intros n l st H. apply (step_fuel_stable n); lia. Qed.

(*
The transition, branch by branch
--------------------------------
*)

(* Kinds `open_kind` handles, i.e. everything but the recursive one. *)
Definition not_quote (k : line_kind) : bool :=
  match k with KQuote _ => false | _ => true end.

Lemma step_fence_close :
  forall l f acc, fence_close f l = true ->
  step l (PFence f acc) = ([fence_block f (rev acc)], PPara []).
Proof. intros l f acc H. unfold step. cbn [step_fuel]. rewrite H. reflexivity. Qed.

Lemma step_fence_content :
  forall l f acc, fence_close f l = false ->
  step l (PFence f acc) = ([], PFence f (l :: acc)).
Proof. intros l f acc H. unfold step. cbn [step_fuel]. rewrite H. reflexivity. Qed.

(* At an idle state every non-quote kind opens its block. *)
Lemma step_idle :
  forall l k, classify l = k -> not_quote k = true ->
  step l (PPara []) = open_kind l k.
Proof.
  intros l k H Hk. unfold step. cbn [step_fuel]. rewrite H.
  destruct k; (reflexivity || discriminate).
Qed.

(* An open paragraph is flushed by a blank line and by nothing else. *)
Lemma step_para_flush :
  forall l c cur', classify l = KBlank ->
  step l (PPara (c :: cur')) =
  ([mk (Para (para_inlines (rev (c :: cur'))))], PPara []).
Proof. intros l c cur' H. unfold step. cbn [step_fuel]. rewrite H. reflexivity. Qed.

Lemma step_para_cont :
  forall l c cur', classify l <> KBlank ->
  step l (PPara (c :: cur')) = ([], PPara (l :: c :: cur')).
Proof.
  intros l c cur' H. unfold step. cbn [step_fuel].
  destruct (classify l); (congruence || reflexivity).
Qed.

(*
Quote transitions
-----------------

Opening and continuing both recurse on the enclosed line; the fuel bound
discharges via classify_quote_length. *)

Lemma step_quote_open :
  forall l rest bs inner,
    classify l = KQuote rest ->
    step rest (PPara []) = (bs, inner) ->
    step l (PPara []) = ([], PQuote (rev bs) inner).
Proof.
  intros l rest bs inner H Hr. unfold step at 1. cbn [step_fuel]. rewrite H.
  rewrite step_fuel_enough by (pose proof (classify_quote_length _ _ H); lia).
  rewrite Hr. reflexivity.
Qed.

Lemma step_quote_cont :
  forall l rest done inner bs inner',
    classify l = KQuote rest ->
    step rest inner = (bs, inner') ->
    step l (PQuote done inner) = ([], PQuote (rev bs ++ done)%list inner').
Proof.
  intros l rest done inner bs inner' H Hr. unfold step at 1.
  cbn [step_fuel]. rewrite H.
  rewrite step_fuel_enough by (pose proof (classify_quote_length _ _ H); lia).
  rewrite Hr. reflexivity.
Qed.

(* A prefix-less text line still continues the innermost paragraph. *)
Lemma step_quote_lazy :
  forall l done inner,
    classify l = KText -> lazy_ok inner = true ->
    step l (PQuote done inner) = ([], PQuote done (feed_lazy l inner)).
Proof.
  intros l done inner H Hl. unfold step. cbn [step_fuel]. rewrite H.
  cbn [is_lazy]. rewrite Hl. reflexivity.
Qed.

(* Anything else closes the quote, and the line is then reprocessed
   outside it — the same `open_kind` the idle state uses. *)
Lemma step_quote_close :
  forall l k done inner bs st',
    classify l = k -> not_quote k = true -> is_lazy k inner = false ->
    open_kind l k = (bs, st') ->
    step l (PQuote done inner) =
    (mk (BlockQuote (rev done ++ finish inner)%list) :: bs, st').
Proof.
  intros l k done inner bs st' H Hk Hlz Ho. unfold step. cbn [step_fuel].
  rewrite H.
  destruct k; try discriminate; rewrite Hlz; rewrite Ho; reflexivity.
Qed.

(*
Lifting to the fold
-------------------
*)

Lemma parse_lines_nil : forall st, parse_lines [] st = finish st.
Proof. reflexivity. Qed.

(* The workhorse: one transition, one prefix of emitted blocks. *)
Lemma parse_lines_step :
  forall l rest st bs st',
    step l st = (bs, st') ->
    parse_lines (l :: rest) st = (bs ++ parse_lines rest st')%list.
Proof. intros l rest st bs st' H. cbn [parse_lines]. rewrite H. reflexivity. Qed.

Lemma para_inlines_one :
  forall x, para_inlines [x] = [mk (Str (strip_trailing_ws x))].
Proof. reflexivity. Qed.

Lemma para_inlines_cons2 :
  forall x y rest,
    para_inlines (x :: y :: rest) =
    mk (Str x) :: mk SoftBreak :: para_inlines (y :: rest).
Proof. reflexivity. Qed.

Lemma parse_lines_nil_cons :
  forall c cur',
    parse_lines [] (PPara (c :: cur')) =
    [mk (Para (para_inlines (rev (c :: cur'))))].
Proof. reflexivity. Qed.

Lemma parse_lines_blank_nil :
  forall l rest, classify l = KBlank ->
  parse_lines (l :: rest) (PPara []) = parse_lines rest (PPara []).
Proof.
  intros l rest H.
  rewrite (parse_lines_step _ _ _ _ _ (step_idle _ _ H eq_refl)). reflexivity.
Qed.

Lemma parse_lines_blank_cons :
  forall l rest c cur', classify l = KBlank ->
  parse_lines (l :: rest) (PPara (c :: cur')) =
  mk (Para (para_inlines (rev (c :: cur')))) :: parse_lines rest (PPara []).
Proof.
  intros l rest c cur' H.
  rewrite (parse_lines_step _ _ _ _ _ (step_para_flush _ _ _ H)). reflexivity.
Qed.

Lemma parse_lines_thematic_nil :
  forall l rest, classify l = KThematic ->
  parse_lines (l :: rest) (PPara []) =
  mk ThematicBreak :: parse_lines rest (PPara []).
Proof.
  intros l rest H.
  rewrite (parse_lines_step _ _ _ _ _ (step_idle _ _ H eq_refl)). reflexivity.
Qed.

Lemma parse_lines_fence_open :
  forall l rest f, classify l = KFence f ->
  parse_lines (l :: rest) (PPara []) = parse_lines rest (PFence f []).
Proof.
  intros l rest f H.
  rewrite (parse_lines_step _ _ _ _ _ (step_idle _ _ H eq_refl)). reflexivity.
Qed.

Lemma parse_lines_text :
  forall l rest cur, classify l = KText ->
  parse_lines (l :: rest) (PPara cur) = parse_lines rest (PPara (l :: cur)).
Proof.
  intros l rest cur H. destruct cur as [|c cur'].
  - rewrite (parse_lines_step _ _ _ _ _ (step_idle _ _ H eq_refl)). reflexivity.
  - rewrite (parse_lines_step _ _ _ _ _
               (step_para_cont _ _ _ (fun E => ltac:(rewrite H in E; discriminate)))).
    reflexivity.
Qed.

(* Any nonblank line continues an open paragraph. *)
Lemma parse_lines_cont :
  forall l rest c cur', classify l <> KBlank ->
  parse_lines (l :: rest) (PPara (c :: cur')) =
  parse_lines rest (PPara (l :: c :: cur')).
Proof.
  intros l rest c cur' H.
  rewrite (parse_lines_step _ _ _ _ _ (step_para_cont _ _ _ H)). reflexivity.
Qed.

(*
Fence equations
---------------
*)

Lemma parse_lines_fence_eof :
  forall f acc, parse_lines [] (PFence f acc) = [fence_block f (rev acc)].
Proof. reflexivity. Qed.

Lemma parse_lines_fence_close :
  forall l rest f acc, fence_close f l = true ->
  parse_lines (l :: rest) (PFence f acc) =
  fence_block f (rev acc) :: parse_lines rest (PPara []).
Proof.
  intros l rest f acc H.
  rewrite (parse_lines_step _ _ _ _ _ (step_fence_close _ _ _ H)). reflexivity.
Qed.

Lemma parse_lines_fence_content :
  forall l rest f acc, fence_close f l = false ->
  parse_lines (l :: rest) (PFence f acc) =
  parse_lines rest (PFence f (l :: acc)).
Proof.
  intros l rest f acc H.
  rewrite (parse_lines_step _ _ _ _ _ (step_fence_content _ _ _ H)). reflexivity.
Qed.

(*
Seed lemmas: feeding runs of lines
----------------------------------
*)

(* A run of nonblank lines accumulates (reversed) onto an open paragraph. *)
Lemma parse_lines_cont_seed :
  forall ls tail c cur',
    forallb nonblank ls = true ->
    parse_lines (ls ++ tail)%list (PPara (c :: cur')) =
    parse_lines tail (PPara (rev ls ++ (c :: cur'))%list).
Proof.
  induction ls as [|l ls IH]; intros tail c cur' H.
  - reflexivity.
  - simpl in H. apply andb_true_iff in H as [Hl Hls].
    unfold nonblank in Hl. apply negb_true_iff in Hl.
    change ((l :: ls) ++ tail)%list with (l :: (ls ++ tail))%list.
    rewrite parse_lines_cont
      by (intros E; rewrite (classify_kblank_blank _ E) in Hl; discriminate).
    rewrite IH by exact Hls.
    simpl rev. rewrite <- app_assoc. reflexivity.
Qed.

(* Opening a paragraph with a text line, then feeding its remaining lines. *)
Lemma parse_lines_para_seed :
  forall a ls tail,
    classify a = KText ->
    forallb nonblank ls = true ->
    parse_lines ((a :: ls) ++ tail)%list (PPara []) =
    parse_lines tail (PPara (rev (a :: ls))).
Proof.
  intros a ls tail Ha Hls.
  change ((a :: ls) ++ tail)%list with (a :: (ls ++ tail))%list.
  rewrite parse_lines_text by exact Ha.
  rewrite parse_lines_cont_seed by exact Hls.
  reflexivity.
Qed.

(* A run of non-closing lines accumulates (reversed) into an open fence. *)
Lemma parse_lines_fence_seed :
  forall ls tail f acc,
    forallb (fun l => negb (fence_close f l)) ls = true ->
    parse_lines (ls ++ tail)%list (PFence f acc) =
    parse_lines tail (PFence f (rev ls ++ acc)%list).
Proof.
  induction ls as [|l ls IH]; intros tail f acc H.
  - reflexivity.
  - simpl in H. apply andb_true_iff in H as [Hl Hls].
    apply negb_true_iff in Hl.
    change ((l :: ls) ++ tail)%list with (l :: (ls ++ tail))%list.
    rewrite parse_lines_fence_content by exact Hl.
    rewrite IH by exact Hls.
    simpl rev. rewrite <- app_assoc. reflexivity.
Qed.

(*
Uniformity of block quotes
--------------------------

The payoff of routing a quote's contents back through `step`: prefixing
every line of a document with "> " parses to exactly that document,
wrapped in a quote.  Nothing about the contents is assumed — this holds
for every construct the parser knows, including future ones and nested
quotes. *)

(* Inside an open quote, the prefixed lines drive the inner state and
   the blank line that follows closes the quote. *)
Lemma parse_lines_quote_cont :
  forall lines tail done inner,
    parse_lines (map (fun l => ("> " ++ l)%string) lines ++ EmptyString :: tail)%list
                (PQuote done inner)
    = mk (BlockQuote (rev done ++ parse_lines lines inner)%list)
      :: parse_lines tail (PPara []).
Proof.
  induction lines as [|l lines IH]; intros tail done inner.
  - cbn [map app].
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_close _ KBlank _ _ _ _
                  (classify_blank EmptyString eq_refl) eq_refl eq_refl eq_refl)).
    reflexivity.
  - cbn [map app].
    destruct (step l inner) as [bs inner'] eqn:Es.
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_cont _ _ _ _ _ _ (classify_canonical_quote l) Es)).
    cbn [app]. rewrite IH.
    rewrite (parse_lines_step _ _ _ _ _ Es).
    rewrite rev_app_distr, rev_involutive, <- app_assoc.
    reflexivity.
Qed.

(* ...and the same when the input simply ends. *)
Lemma parse_lines_quote_cont_eof :
  forall lines done inner,
    parse_lines (map (fun l => ("> " ++ l)%string) lines) (PQuote done inner)
    = [mk (BlockQuote (rev done ++ parse_lines lines inner)%list)].
Proof.
  induction lines as [|l lines IH]; intros done inner.
  - reflexivity.
  - cbn [map].
    destruct (step l inner) as [bs inner'] eqn:Es.
    rewrite (parse_lines_step _ _ _ _ _
               (step_quote_cont _ _ _ _ _ _ (classify_canonical_quote l) Es)).
    cbn [app]. rewrite IH.
    rewrite (parse_lines_step _ _ _ _ _ Es).
    rewrite rev_app_distr, rev_involutive, <- app_assoc.
    reflexivity.
Qed.

Lemma parse_lines_quote :
  forall l lines tail,
    parse_lines
      (map (fun x => ("> " ++ x)%string) (l :: lines) ++ EmptyString :: tail)%list
      (PPara [])
    = mk (BlockQuote (parse_lines (l :: lines) (PPara [])))
      :: parse_lines tail (PPara []).
Proof.
  intros l lines tail. cbn [map app].
  destruct (step l (PPara [])) as [bs inner] eqn:Es.
  rewrite (parse_lines_step _ _ _ _ _
             (step_quote_open _ _ _ _ (classify_canonical_quote l) Es)).
  cbn [app]. rewrite parse_lines_quote_cont, rev_involutive.
  rewrite (parse_lines_step _ _ _ _ _ Es).
  reflexivity.
Qed.

(** Uniformity for block quotes: a quote's contents parse exactly as
    they would at top level.  One proof, every construct. *)
Theorem quote_uniformity :
  forall l lines,
    parse_lines (map (fun x => ("> " ++ x)%string) (l :: lines)) (PPara [])
    = [mk (BlockQuote (parse_lines (l :: lines) (PPara [])))].
Proof.
  intros l lines. cbn [map].
  destruct (step l (PPara [])) as [bs inner] eqn:Es.
  rewrite (parse_lines_step _ _ _ _ _
             (step_quote_open _ _ _ _ (classify_canonical_quote l) Es)).
  cbn [app]. rewrite parse_lines_quote_cont_eof, rev_involutive.
  rewrite (parse_lines_step _ _ _ _ _ Es).
  reflexivity.
Qed.

(*
Sanity checks
=============
*)

Example parse_two_paras :
  doc_blocks (parse_doc "hi
there

bye") =
  [ mk (Para [mk (Str "hi"); mk SoftBreak; mk (Str "there")])
  ; mk (Para [mk (Str "bye")]) ].
Proof. reflexivity. Qed.

Example parse_thematic :
  doc_blocks (parse_doc "one

  * * * *

two") =
  [ mk (Para [mk (Str "one")])
  ; mk ThematicBreak
  ; mk (Para [mk (Str "two")]) ].
Proof. reflexivity. Qed.

(* Paragraphs are never interrupted: thematic-break- or fence-shaped
   lines inside a paragraph are text. *)
Example parse_no_interrupt :
  doc_blocks (parse_doc "one
---") =
  [ mk (Para [mk (Str "one"); mk SoftBreak; mk (Str "---")]) ].
Proof. reflexivity. Qed.

Example parse_code_block :
  doc_blocks (parse_doc "``` ruby
x = 5
```") =
  [ mk (CodeBlock "ruby" ("x = 5" ++ nl)) ].
Proof. reflexivity. Qed.

Example parse_raw_block :
  doc_blocks (parse_doc "``` =html
<hr>
```") =
  [ mk (RawBlock "html" ("<hr>" ++ nl)) ].
Proof. reflexivity. Qed.

(* Unclosed fences extend to end of input; content is never classified. *)
Example parse_unclosed_fence :
  doc_blocks (parse_doc "~~~
* * *
para") =
  [ mk (CodeBlock "" ("* * *" ++ nl ++ "para" ++ nl)) ].
Proof. reflexivity. Qed.

Example parse_blank_only : doc_blocks (parse_doc "  ") = [].
Proof. reflexivity. Qed.

(*
Block quotes
------------

Each example is a case from djot.js/test/block_quote.test or a probe
against djot.js; the comment gives the behaviour being pinned. *)

Example parse_quote_basic :
  doc_blocks (parse_doc "> Basic
> quote.") =
  [ mk (BlockQuote [mk (Para [mk (Str "Basic"); mk SoftBreak; mk (Str "quote.")])]) ].
Proof. reflexivity. Qed.

(* A bare ">" is a quote with no content — the reason wf_block lets
   BlockQuote be empty. *)
Example parse_quote_empty :
  doc_blocks (parse_doc ">") = [mk (BlockQuote [])].
Proof. reflexivity. Qed.

(* ">" without following whitespace is not a prefix at all. *)
Example parse_quote_needs_ws :
  doc_blocks (parse_doc ">not a quote") =
  [ mk (Para [mk (Str ">not a quote")]) ].
Proof. reflexivity. Qed.

(* A blank prefixed line ends the inner paragraph without ending the
   quote; a truly blank line ends the quote. *)
Example parse_quote_two_paras :
  doc_blocks (parse_doc "> a
>
> b") =
  [ mk (BlockQuote [ mk (Para [mk (Str "a")]); mk (Para [mk (Str "b")]) ]) ].
Proof. reflexivity. Qed.

Example parse_quote_split :
  doc_blocks (parse_doc "> a

> b") =
  [ mk (BlockQuote [mk (Para [mk (Str "a")])])
  ; mk (BlockQuote [mk (Para [mk (Str "b")])]) ].
Proof. reflexivity. Qed.

(* Nesting comes from re-entering the classifier on the stripped line. *)
Example parse_quote_nested :
  doc_blocks (parse_doc "> > > deep") =
  [ mk (BlockQuote [mk (BlockQuote [mk (BlockQuote
      [mk (Para [mk (Str "deep")])])])]) ].
Proof. reflexivity. Qed.

(* Lazy continuation: a prefix-less text line still joins the innermost
   open paragraph, at any depth. *)
Example parse_quote_lazy :
  doc_blocks (parse_doc "> > deep
lazy") =
  [ mk (BlockQuote [mk (BlockQuote
      [mk (Para [mk (Str "deep"); mk SoftBreak; mk (Str "lazy")])])]) ].
Proof. reflexivity. Qed.

(* ...but only into a paragraph.  Verbatim content is not lazily
   continued, so the quote closes and a new paragraph starts. *)
Example parse_quote_no_lazy_fence :
  doc_blocks (parse_doc "> ```
> x
y") =
  [ mk (BlockQuote [mk (CodeBlock "" ("x" ++ nl))])
  ; mk (Para [mk (Str "y")]) ].
Proof. reflexivity. Qed.

(* Nor is a line that starts a block of its own: the quote closes. *)
Example parse_quote_closed_by_thematic :
  doc_blocks (parse_doc "> a
* * * *") =
  [ mk (BlockQuote [mk (Para [mk (Str "a")])]); mk ThematicBreak ].
Proof. reflexivity. Qed.

(* Paragraphs are never interrupted, quotes included. *)
Example parse_quote_no_interrupt :
  doc_blocks (parse_doc "a
> b") =
  [ mk (Para [mk (Str "a"); mk SoftBreak; mk (Str "> b")]) ].
Proof. reflexivity. Qed.
