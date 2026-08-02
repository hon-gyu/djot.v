(* Block parsing: a fold over classified lines with an explicit state.

   The state is a sum: an open paragraph accumulator (possibly empty =
   idle), or an open code fence collecting verbatim lines.  Per line:
   - inside a fence, only the close test applies — no classification;
   - otherwise KBlank ends any open paragraph, KThematic/KFence start
     blocks only when no paragraph is open (paragraphs can never be
     interrupted — spec), and KText extends or opens a paragraph.

   The equation lemmas at the bottom are the interface the wf and
   roundtrip proofs use; keep them in sync with the definition. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Strings Line Ast.
Import ListNotations.

Local Open Scope string_scope.

(*
Paragraph assembly
==================
*)

(* Trailing whitespace is stripped at the end of a paragraph (but kept on
   interior lines) — observed djot.js/djoths behavior on para.test. *)

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

Inductive pstate : Type :=
  | PPara (cur : list string)             (* [] = no open block *)
  | PFence (f : fence) (acc : list string).

Fixpoint parse_lines (lines : list string) (st : pstate) : blocks :=
  match lines with
  | [] =>
      match st with
      | PPara [] => []
      | PPara cur => [mk (Para (para_inlines (rev cur)))]
      | PFence f acc => [fence_block f (rev acc)]  (* EOF closes the fence *)
      end
  | l :: rest =>
      match st with
      | PFence f acc =>
          if fence_close f l
          then fence_block f (rev acc) :: parse_lines rest (PPara [])
          else parse_lines rest (PFence f (l :: acc))
      | PPara cur =>
          let flush := fun (k : blocks) =>
            match cur with
            | [] => k
            | _ => mk (Para (para_inlines (rev cur))) :: k
            end in
          match classify l, cur with
          | KBlank, _ => flush (parse_lines rest (PPara []))
          | KThematic, [] => mk ThematicBreak :: parse_lines rest (PPara [])
          | KFence f, [] => parse_lines rest (PFence f [])
          | KThematic, _ | KFence _, _ =>
              parse_lines rest (PPara (l :: cur))  (* paragraph continuation *)
          | KText, _ => parse_lines rest (PPara (l :: cur))
          end
      end
  end.

Definition parse_doc (s : string) : doc :=
  {| doc_blocks := parse_lines (split_lines s) (PPara [])
   ; doc_footnotes := []
   ; doc_references := []
   ; doc_auto_references := []
   ; doc_auto_identifiers := [] |}.

(*
Equation lemmas
===============
*)

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
Proof. intros l rest H. cbn [parse_lines]. rewrite H. reflexivity. Qed.

Lemma parse_lines_blank_cons :
  forall l rest c cur', classify l = KBlank ->
  parse_lines (l :: rest) (PPara (c :: cur')) =
  mk (Para (para_inlines (rev (c :: cur')))) :: parse_lines rest (PPara []).
Proof. intros l rest c cur' H. cbn [parse_lines]. rewrite H. reflexivity. Qed.

Lemma parse_lines_thematic_nil :
  forall l rest, classify l = KThematic ->
  parse_lines (l :: rest) (PPara []) =
  mk ThematicBreak :: parse_lines rest (PPara []).
Proof. intros l rest H. cbn [parse_lines]. rewrite H. reflexivity. Qed.

Lemma parse_lines_fence_open :
  forall l rest f, classify l = KFence f ->
  parse_lines (l :: rest) (PPara []) = parse_lines rest (PFence f []).
Proof. intros l rest f H. cbn [parse_lines]. rewrite H. reflexivity. Qed.

Lemma parse_lines_text :
  forall l rest cur, classify l = KText ->
  parse_lines (l :: rest) (PPara cur) = parse_lines rest (PPara (l :: cur)).
Proof.
  intros l rest cur H. cbn [parse_lines]. rewrite H.
  destruct cur; reflexivity.
Qed.

(* Any nonblank line continues an open paragraph. *)
Lemma parse_lines_cont :
  forall l rest c cur', classify l <> KBlank ->
  parse_lines (l :: rest) (PPara (c :: cur')) =
  parse_lines rest (PPara (l :: c :: cur')).
Proof.
  intros l rest c cur' H. cbn [parse_lines].
  destruct (classify l) eqn:E; [congruence | reflexivity | reflexivity | reflexivity].
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
Proof. intros l rest f acc H. cbn [parse_lines]. rewrite H. reflexivity. Qed.

Lemma parse_lines_fence_content :
  forall l rest f acc, fence_close f l = false ->
  parse_lines (l :: rest) (PFence f acc) =
  parse_lines rest (PFence f (l :: acc)).
Proof. intros l rest f acc H. cbn [parse_lines]. rewrite H. reflexivity. Qed.

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
