(* Probe for "attach at the end": is the resolution pass's
   well-formedness lemma cheap?  Nothing here is meant to be kept. *)
From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Strings Ast Attributes Inline Wf.
Import ListNotations.
Open Scope string_scope.
Existing Instance djot_table.

(* The scanner's output element: a finished node, or an attribute spec
   whose target is not yet known.  `src` is what the spec ate, kept for
   the case where nothing takes it. *)
Inductive oitem : Type :=
  | OIn (n : node inline)
  | OMark (a : attr) (src : string).

(* Resolving one marker against what has already been rebuilt.  The
   accumulator's current scope holds the nodes in reverse, so its head is
   the thing immediately before the spec. *)
Definition oattach_now (a : attr) (src : string) (o : ostate) : ostate :=
  match ocur o with
  | Node p [] (Str s) :: rest =>
      let '(pre, w) := last_ws_split s in
      if nonempty_str w
      then match a with
           | [] => o
           | _ =>
               let o1 := oset_cur rest o in
               let o2 := if nonempty_str pre
                         then oemit_merge (mk (Str pre)) o1 else o1 in
               oemit_merge (Node NoPos a (Str w)) o2
           end
      else o
  | Node p a' v :: rest => oset_cur (Node p (attr_merge a a') v :: rest) o
  | [] => oemit_merge (mk (Str src)) o
  end.

Fixpoint oresolve (l : list oitem) (o : ostate) : ostate :=
  match l with
  | [] => o
  | OIn n :: rest => oresolve rest (oemit_merge n o)
  | OMark a src :: rest => oresolve rest (oattach_now a src o)
  end.

Definition oitem_ok (i : oitem) : bool :=
  match i with
  | OIn n => wf_inline (node_contents n)
  | OMark _ src => nonempty_str src
  end.

(* The load-bearing lemma. *)
Lemma oattach_now_ok :
  forall a src o,
    oscope_ok o = true -> nonempty_str src = true ->
    oscope_ok (oattach_now a src o) = true.
Proof.
  intros a src o Ho Hsrc.
  pose proof (ilist_ok_ocur o Ho) as Hl.
  unfold oattach_now.
  destruct (ocur o) as [|[p a' v] rest] eqn:Ec.
  - apply oscope_ok_emit_merge; [exact Ho | exact Hsrc].
  - assert (Hre : plain_str (Node p a' v) = false ->
                  oscope_ok (oset_cur (Node p (attr_merge a a') v :: rest) o)
                  = true).
    { intros Hp. apply oscope_ok_set_cur; [exact Ho|].
      eapply ilist_ok_reattr;
        [exact Hl | reflexivity | apply plain_str_reattr, Hp | exact Hp]. }
    destruct a' as [|kv a'']; [|apply Hre; reflexivity].
    destruct v; try (apply Hre; reflexivity).
    destruct (last_ws_split s) as [pre w] eqn:Es.
    destruct (nonempty_str w) eqn:Ew; [|exact Ho].
    destruct a as [|ka a2]; [exact Ho|].
    assert (Hrest : oscope_ok (oset_cur rest o) = true)
      by (apply oscope_ok_set_cur; [exact Ho | exact (ilist_ok_tail _ _ Hl)]).
    apply oscope_ok_emit_merge; [|exact Ew].
    destruct (nonempty_str pre) eqn:Ep; [|exact Hrest].
    apply oscope_ok_emit_merge; [exact Hrest | exact Ep].
Qed.

Lemma oresolve_ok :
  forall l o,
    oscope_ok o = true ->
    forallb oitem_ok l = true ->
    oscope_ok (oresolve l o) = true.
Proof.
  induction l as [|i l IH]; intros o Ho Hl; [exact Ho|].
  cbn [oresolve forallb] in Hl |- *.
  apply andb_true_iff in Hl as [Hi Hl].
  destruct i as [n|a src].
  - apply IH; [apply oscope_ok_emit_merge; assumption | exact Hl].
  - apply IH; [apply oattach_now_ok; assumption | exact Hl].
Qed.
Print Assumptions oresolve_ok.
