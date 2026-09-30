(* ai-disclosure: autonomous *)

(* The inline scanner builds the tree the precedence rules describe
   (`Precedence.v`): on a line of bare delimiters and plain bytes,
   `parse_inline_line` is `tree_of` of the unique valid matching. *)

From Stdlib Require Import String Ascii List Bool Lia Arith Sorted.
From DjotV Require Import Strings Ast InlineTable InlineView InlineScan
  InlineInvert Precedence.
Import ListNotations.

Local Open Scope string_scope.

Section WithTable.
Context {T : dtable}.

(*
The prefix view
===============

What the scanner holds after a prefix of the tokens: the live openers,
innermost first, each with what has been read since it, above what was
read before the outermost one.  An opener dies with the pair that
closes over it, and at the end every opener still live is text.

`tree_of` instead knows the whole matching and opens a frame only for
an opener that will be closed.  The two agree because a frame of the
view whose opener is never closed reads, once it is text, as its
opener's spelling followed by its content (`collapse`).

Contents are kept as `inline` values rather than nodes: every node here
is built with `mk`, and merging text is then associative on the nose. *)

(* Push onto a reversed list, merging two `Str`s at the seam. *)
Definition xsnoc (x : inline) (out : list inline) : list inline :=
  match out, x with
  | Str t :: rest, Str s => Str (t ++ s) :: rest
  | _, _ => x :: out
  end.

(* `cur`, reversed, in front of `out`, reversed. *)
Fixpoint xapp (cur out : list inline) : list inline :=
  match cur with
  | [] => out
  | [x] => xsnoc x out
  | x :: rest => x :: xapp rest out
  end.

Definition lit (k : dstyle) : inline := Str (dtoken k).

Definition pframe : Type := (nat * dstyle * list inline)%type.

Record pview : Type := PView {
  pv_stk : list pframe;
  pv_out : list inline
}.

Definition pv0 : pview := PView [] [].

Definition pkey (f : pframe) : nat * dstyle := (fst (fst f), snd (fst f)).

(* The live openers, as `rstep` keeps them. *)
Definition pv_live (v : pview) : list (nat * dstyle) := map pkey (pv_stk v).

Definition pv_add (x : inline) (v : pview) : pview :=
  match pv_stk v with
  | [] => PView [] (xsnoc x (pv_out v))
  | (p, k, c) :: rest => PView ((p, k, xsnoc x c) :: rest) (pv_out v)
  end.

(* Close the innermost frame of style `k`, turning the frames above it
   into text in its content. *)
Fixpoint pclose_go (k : dstyle) (pend : list inline) (stk : list pframe)
  : option (list inline * list pframe) :=
  match stk with
  | [] => None
  | (p, k', c) :: rest =>
      let content := xapp pend c in
      if dstyle_eq k k' then Some (content, rest)
      else pclose_go k (xapp content [lit k']) rest
  end.

Definition popen (i : nat) (k : dstyle) (op : bool) (v : pview) : pview :=
  if op then PView ((i, k, []) :: pv_stk v) (pv_out v)
  else pv_add (lit k) v.

(* `rstep`, keeping the content. *)
Definition pstep (i : nat) (t : token) (v : pview) : pview :=
  match t with
  | TText c => pv_add (Str (one c)) v
  | TDelim k op cl =>
      match (if cl then pick k (pv_live v) else None) with
      | Some (p, _) =>
          if Nat.ltb (S p) i
          then match pclose_go k [] (pv_stk v) with
               | Some (content, rest) =>
                   pv_add (dnode k (map mk (List.rev content)))
                     (PView rest (pv_out v))
               | None => v
               end
          else popen i k op v
      | None => popen i k op v
      end
  end.

Fixpoint prun (i : nat) (ts : list token) (v : pview) : pview :=
  match ts with
  | [] => v
  | t :: rest => prun (S i) rest (pstep i t v)
  end.

(* Every open frame read as text, as at the end of the line. *)
Fixpoint pflatten_go (pend : list inline) (stk : list pframe)
  (bottom : list inline) : list inline :=
  match stk with
  | [] => xapp pend bottom
  | (_, k, c) :: rest => pflatten_go (xapp (xapp pend c) [lit k]) rest bottom
  end.

Definition pflatten (v : pview) : list inline :=
  pflatten_go [] (pv_stk v) (pv_out v).

(* The frames of `tree_go` that a view stands for, given which openers
   the whole line closes: a frame whose opener is closed stays a frame,
   and any other is its opener's text and its content, in the frame
   below it. *)
Definition xinner (g : list inline -> list inline)
  (st : list (dstyle * list inline) * list inline)
  : list (dstyle * list inline) * list inline :=
  match st with
  | ([], top) => ([], g top)
  | ((k, c) :: fs, top) => ((k, g c) :: fs, top)
  end.

Fixpoint collapse (real : nat -> bool) (stk : list pframe) (out : list inline)
  : list (dstyle * list inline) * list inline :=
  match stk with
  | [] => ([], out)
  | (p, k, c) :: rest =>
      if real p then ((k, c) :: fst (collapse real rest out),
                      snd (collapse real rest out))
      else xinner (fun acc => xapp c (xsnoc (lit k) acc))
             (collapse real rest out)
  end.

Definition tembed (st : list (dstyle * list inline) * list inline)
  : tframes * inlines :=
  (map (fun f => (fst f, map mk (snd f))) (fst st), map mk (snd st)).

(*
Merging text
------------
*)

Local Lemma xsnoc_nonstr : forall x l, (forall s, x <> Str s) -> xsnoc x l = x :: l.
Proof.
  intros x l H. destruct x; [destruct (H s eq_refl)|..];
    (destruct l as [|[] l]; reflexivity).
Qed.

Local Lemma str_view : forall x, {s | x = Str s} + {forall s, x <> Str s}.
Proof.
  intros x. destruct x; [left; eexists; reflexivity|..];
    right; intros s' E; discriminate E.
Defined.

Local Lemma xsnoc_str_nonstr : forall t w b,
  (forall u, w <> Str u) -> xsnoc (Str t) (w :: b) = Str t :: w :: b.
Proof. intros t w b H. destruct w; [destruct (H s eq_refl)|..]; reflexivity. Qed.

Local Lemma xapp_xsnoc : forall x a b, xapp (xsnoc x a) b = xsnoc x (xapp a b).
Proof.
  intros x a b. destruct (str_view x) as [[s ->]|Hx].
  - destruct a as [|y r]; [reflexivity|].
    destruct (str_view y) as [[t ->]|Hy].
    + destruct r as [|z r]; cbn [xsnoc xapp]; [|reflexivity].
      destruct b as [|w b]; [reflexivity|].
      destruct (str_view w) as [[u ->]|Hw].
      * cbn. rewrite append_assoc. reflexivity.
      * rewrite (xsnoc_str_nonstr t w b Hw). cbn.
        destruct w; [destruct (Hw _ eq_refl)|..]; reflexivity.
    + rewrite (xsnoc_str_nonstr s y r Hy). destruct r as [|z r]; cbn [xapp].
      * rewrite (xsnoc_nonstr y b Hy), (xsnoc_str_nonstr s y b Hy).
        reflexivity.
      * rewrite (xsnoc_str_nonstr s y _ Hy). reflexivity.
  - rewrite (xsnoc_nonstr x a Hx). destruct a as [|y r]; cbn [xapp];
      [reflexivity|].
    destruct r as [|z r]; rewrite (xsnoc_nonstr x _ Hx); reflexivity.
Qed.

Local Lemma xapp_nonempty : forall a b, a <> [] -> xapp a b <> [].
Proof.
  intros a b H. destruct a as [|x [|y r]]; [contradiction|..|discriminate].
  cbn [xapp]. unfold xsnoc.
  destruct b as [|y b]; [discriminate|].
  destruct y; try discriminate. destruct x; discriminate.
Qed.

Local Lemma xapp_assoc : forall a b c, xapp (xapp a b) c = xapp a (xapp b c).
Proof.
  induction a as [|x a IH]; intros b c; [reflexivity|].
  destruct a as [|y r]; [apply xapp_xsnoc|].
  change (xapp (x :: y :: r) b) with (x :: xapp (y :: r) b).
  change (xapp (x :: y :: r) (xapp b c)) with (x :: xapp (y :: r) (xapp b c)).
  rewrite <- IH.
  assert (xapp (y :: r) b <> []) as Hn by (apply xapp_nonempty; discriminate).
  destruct (xapp (y :: r) b) as [|z w]; [contradiction|reflexivity].
Qed.

Local Lemma str_snoc_mk : forall s l, str_snoc s (map mk l) = map mk (xsnoc (Str s) l).
Proof.
  intros s l. destruct l as [|y l]; [reflexivity|].
  destruct (str_view y) as [[t ->]|Hy]; [reflexivity|].
  rewrite (xsnoc_str_nonstr s y l Hy).
  destruct y; [destruct (Hy _ eq_refl)|..]; reflexivity.
Qed.

(*
Collapsing the view
-------------------
*)

Local Lemma collapse_add : forall real x v,
  collapse real (pv_stk (pv_add x v)) (pv_out (pv_add x v))
  = xinner (xsnoc x) (collapse real (pv_stk v) (pv_out v)).
Proof.
  intros real x [stk out]. unfold pv_add; cbn [pv_stk pv_out].
  destruct stk as [|[[p k] c] rest]; [reflexivity|].
  cbn [pv_stk pv_out collapse].
  destruct (real p); [reflexivity|].
  destruct (collapse real rest out) as [[|[k' c'] fs] top]; cbn;
    rewrite xapp_xsnoc; reflexivity.
Qed.

Local Lemma pick_split : forall k stk p below,
  pick k (map pkey stk) = Some (p, below) ->
  exists above c rest,
    stk = (above ++ (p, k, c) :: rest)%list
    /\ Forall (fun f => dstyle_eq k (snd (fst f)) = false) above
    /\ map pkey rest = below.
Proof.
  intros k stk. induction stk as [|[[q k'] c] stk IH]; intros p below H;
    [discriminate|].
  cbn [map pkey fst snd pick] in H.
  destruct (dstyle_eq k k') eqn:E.
  - injection H as <- <-. apply dstyle_eq_iff in E. subst k'.
    exists [], c, stk. split; [reflexivity|]. split; [constructor|reflexivity].
  - destruct (IH p below H) as (above & c' & rest & -> & F & Hb).
    exists ((q, k', c) :: above)%list, c', rest. split; [reflexivity|].
    split; [constructor; [exact E|exact F]|exact Hb].
Qed.

Local Lemma close_collapse : forall real k above p c rest out pend,
  Forall (fun f => dstyle_eq k (snd (fst f)) = false
                   /\ real (fst (fst f)) = false) above ->
  real p = true ->
  exists content,
    pclose_go k pend (above ++ (p, k, c) :: rest)
    = Some (xapp pend content, rest)
    /\ collapse real (above ++ (p, k, c) :: rest) out
       = ((k, content) :: fst (collapse real rest out),
          snd (collapse real rest out)).
Proof.
  intros real k above.
  induction above as [|[[q k1] c1] above IH];
    intros p c rest out pend F Hp; cbn [app pclose_go collapse].
  - assert (dstyle_eq k k = true) as E by (apply dstyle_eq_iff; reflexivity).
    rewrite E, Hp. exists c. split; reflexivity.
  - apply Forall_cons_iff in F as [[E Hq] F]. cbn [fst snd] in E, Hq.
    rewrite E, Hq.
    destruct (IH p c rest out (xapp (xapp pend c1) [lit k1]) F Hp)
      as (content & Hc & Hl).
    exists (xapp c1 (xsnoc (lit k1) content)). rewrite Hc, Hl.
    split; [|reflexivity]. rewrite !xapp_assoc. reflexivity.
Qed.

Local Lemma flatten_collapse : forall real stk out pend,
  Forall (fun f => real (fst (fst f)) = false) stk ->
  collapse real stk out = ([], snd (collapse real stk out))
  /\ pflatten_go pend stk out = xapp pend (snd (collapse real stk out)).
Proof.
  intros real stk out.
  induction stk as [|[[q k] c] stk IH]; intros pend F;
    cbn [collapse pflatten_go]; [split; reflexivity|].
  apply Forall_cons_iff in F as [Hq F]. cbn [fst] in Hq. rewrite Hq.
  destruct (IH (xapp (xapp pend c) [lit k]) F) as [E1 E2].
  rewrite E1 in *. cbn [xinner fst snd]. rewrite E2. split; [reflexivity|].
  rewrite !xapp_assoc. reflexivity.
Qed.

(*
One token
---------

The view and `tree_go` move together, given what the whole line's
matching says about the token: whether it closes, whether it will be
closed as an opener, and that the openers a closer passes over are
never closed. *)

Definition step_facts (m : matching) (n : nat) (t : token)
  (lv : list (nat * dstyle)) : Prop :=
  match t with
  | TText _ => True
  | TDelim k op cl =>
      match (if cl then pick k lv else None) with
      | Some (p, _) =>
          if Nat.ltb (S p) n
          then is_opener m n = false /\ is_closer m n = true
               /\ is_opener m p = true
               /\ (forall q k', In (q, k') lv -> p < q -> is_opener m q = false)
          else is_closer m n = false /\ (op = false -> is_opener m n = false)
      | None => is_closer m n = false /\ (op = false -> is_opener m n = false)
      end
  end.

Local Lemma pv_live_add : forall x v, pv_live (pv_add x v) = pv_live v.
Proof.
  intros x [[|[[p k] c] rest] out]; reflexivity.
Qed.

Local Lemma temit_str_embed : forall s st,
  temit_str s (fst (tembed st)) (snd (tembed st))
  = tembed (xinner (xsnoc (Str s)) st).
Proof.
  intros s [[|[k c] fs] top]; cbn; rewrite str_snoc_mk; reflexivity.
Qed.

Local Lemma temit_embed : forall x st,
  temit (mk x) (fst (tembed st)) (snd (tembed st))
  = tembed (xinner (cons x) st).
Proof.
  intros x [[|[k c] fs] top]; reflexivity.
Qed.

Local Lemma desc_above : forall above f rest,
  desc (map pkey (above ++ f :: rest)) ->
  forall g, In g above -> fst (fst f) < fst (fst g).
Proof.
  induction above as [|h above IH]; intros f rest D g Hg; [destruct Hg|].
  cbn [app map] in D. apply StronglySorted_inv in D as [D F].
  destruct Hg as [<-|Hg]; [|exact (IH f rest D g Hg)].
  rewrite Forall_forall in F. apply (F (pkey f)).
  apply in_map. apply in_or_app. right. left. reflexivity.
Qed.

Local Lemma pv_live_pkey : forall v, pv_live v = map pkey (pv_stk v).
Proof. reflexivity. Qed.

Local Lemma popen_live : forall n k op v,
  pv_live (popen n k op v) = ropen n k op (pv_live v).
Proof. intros n k [|] v; [reflexivity|apply pv_live_add]. Qed.

Local Lemma pclose_split : forall k above p c rest pend,
  Forall (fun f => dstyle_eq k (snd (fst f)) = false) above ->
  exists content,
    pclose_go k pend (above ++ (p, k, c) :: rest) = Some (content, rest).
Proof.
  intros k above. induction above as [|[[q k1] c1] above IH];
    intros p c rest pend F; cbn [app pclose_go].
  - assert (dstyle_eq k k = true) as E by (apply dstyle_eq_iff; reflexivity).
    rewrite E. eexists. reflexivity.
  - apply Forall_cons_iff in F as [E F]. cbn [fst snd] in E. rewrite E.
    apply IH, F.
Qed.

Local Lemma pstep_live : forall n t v s,
  pv_live v = rs_live s -> pv_live (pstep n t v) = rs_live (rstep n t s).
Proof.
  intros n t v s H. destruct t as [c|k op cl]; cbn [pstep rstep].
  - rewrite pv_live_add. exact H.
  - rewrite <- H. destruct cl; [|apply popen_live].
    destruct (pick k (pv_live v)) as [[p below]|] eqn:P; [|apply popen_live].
    destruct (Nat.ltb (S p) n); [|apply popen_live].
    rewrite pv_live_pkey in P.
    destruct (pick_split k (pv_stk v) p below P)
      as (above & c & rest & E & F & Hb).
    rewrite E. destruct (pclose_split k above p c rest [] F) as [content Hc].
    rewrite Hc, pv_live_add. exact Hb.
Qed.

Local Lemma xinner_ext : forall g h st,
  (forall l, g l = h l) -> xinner g st = xinner h st.
Proof. intros g h [[|[k c] fs] top] H; cbn; rewrite H; reflexivity. Qed.

Local Lemma dnode_nonstr : forall k l s, dnode k l <> Str s.
Proof. intros [] l s E; discriminate E. Qed.

Local Lemma tstep_text : forall m n c st,
  tstep m n (TText c) st = temit_str (one c) (fst st) (snd st).
Proof. intros m n c [fs top]. reflexivity. Qed.

Local Lemma tstep_delim : forall m n k op cl st,
  tstep m n (TDelim k op cl) st
  = if is_opener m n then ((k, []) :: fst st, snd st)
    else match is_closer m n, fst st with
         | true, (k', acc) :: fs0 =>
             temit (mk (dnode k' (List.rev acc))) fs0 (snd st)
         | _, _ => temit_str (dtoken k) (fst st) (snd st)
         end.
Proof. intros m n k op cl [fs top]. reflexivity. Qed.

(* The token opens or is text, in both. *)
Local Lemma popen_tstep : forall m n k op cl v,
  is_closer m n = false -> (op = false -> is_opener m n = false) ->
  tstep m n (TDelim k op cl)
    (tembed (collapse (is_opener m) (pv_stk v) (pv_out v)))
  = tembed (collapse (is_opener m) (pv_stk (popen n k op v))
              (pv_out (popen n k op v))).
Proof.
  intros m n k op cl v Hc Ho. rewrite tstep_delim. destruct op.
  - unfold popen; cbn [pv_stk pv_out collapse].
    destruct (is_opener m n); [reflexivity|].
    rewrite Hc, temit_str_embed. reflexivity.
  - rewrite (Ho eq_refl), Hc. unfold popen.
    rewrite collapse_add, temit_str_embed. reflexivity.
Qed.

Local Lemma pstep_tstep : forall m n t v,
  desc (pv_live v) -> step_facts m n t (pv_live v) ->
  tstep m n t (tembed (collapse (is_opener m) (pv_stk v) (pv_out v)))
  = tembed (collapse (is_opener m) (pv_stk (pstep n t v))
              (pv_out (pstep n t v))).
Proof.
  intros m n t v D Hf. destruct t as [c|k op cl].
  - cbn [pstep]. rewrite tstep_text, collapse_add, <- temit_str_embed.
    reflexivity.
  - unfold step_facts in Hf. cbn [pstep].
    destruct (if cl then pick k (pv_live v) else None) as [[p below]|] eqn:P;
      [|destruct Hf as [Hc Ho]; apply popen_tstep; assumption].
    destruct (Nat.ltb (S p) n);
      [|destruct Hf as [Hc Ho]; apply popen_tstep; assumption].
    destruct Hf as (Hon & Hcn & Hop & Habove).
    destruct cl; [|discriminate].
    rewrite pv_live_pkey in P, D, Habove.
    destruct (pick_split k (pv_stk v) p below P)
      as (above & c & rest & E & F & Hb).
    rewrite E in D, Habove |- *.
    assert (Fr : Forall (fun f => dstyle_eq k (snd (fst f)) = false
                                  /\ is_opener m (fst (fst f)) = false) above).
    { rewrite Forall_forall in F |- *. intros g Hg.
      split; [exact (F g Hg)|].
      apply (Habove (fst (fst g)) (snd (fst g))).
      - apply in_map_iff. exists g. split; [reflexivity|].
        apply in_or_app. left. exact Hg.
      - exact (desc_above above (p, k, c) rest D g Hg). }
    destruct (close_collapse (is_opener m) k above p c rest (pv_out v) [] Fr Hop)
      as (content & Hpc & Hcol).
    rewrite Hpc, Hcol, tstep_delim, Hon, Hcn. cbn [xapp fst snd tembed map].
    rewrite collapse_add. cbn [pv_stk pv_out].
    rewrite (xinner_ext (xsnoc _) (cons (dnode k (map mk (List.rev content)))))
      by (intros l; apply xsnoc_nonstr, dnode_nonstr).
    rewrite <- temit_embed, map_rev. reflexivity.
Qed.

(*
The whole line
--------------

The facts `step_facts` asks for hold of the matching `ref_match`
computes, at every token, because it is valid and it grows by closers:
the pairs that close before `n` are the ones the first `n` steps made. *)

Local Lemma is_opener_iff : forall m i, is_opener m i = true <-> exists j, In (i, j) m.
Proof.
  intros m i. unfold is_opener. rewrite existsb_exists. split.
  - intros ([a b] & Hin & E). apply Nat.eqb_eq in E. cbn in E. subst a.
    exists b. exact Hin.
  - intros [j Hin]. exists (i, j). split; [exact Hin|apply Nat.eqb_refl].
Qed.

Local Lemma is_closer_iff : forall m j, is_closer m j = true <-> exists i, In (i, j) m.
Proof.
  intros m j. unfold is_closer. rewrite existsb_exists. split.
  - intros ([a b] & Hin & E). apply Nat.eqb_eq in E. cbn in E. subst b.
    exists a. exact Hin.
  - intros [i Hin]. exists (i, j). split; [exact Hin|apply Nat.eqb_refl].
Qed.

Local Lemma rrun_pairs : forall ts i s,
  exists new, rs_pairs (rrun i ts s) = (new ++ rs_pairs s)%list
              /\ forall a b, In (a, b) new -> i <= b.
Proof.
  induction ts as [|t ts IH]; intros i s; cbn [rrun].
  - exists []. split; [reflexivity|intros a b []].
  - destruct (IH (S i) (rstep i t s)) as (new & E & B).
    assert (B' : forall a b, In (a, b) new -> i <= b)
      by (intros a b H; specialize (B a b H); lia).
    destruct t as [c|k op cl]; cbn [rstep] in E |- *;
      [exists new; split; [exact E|exact B']|].
    destruct (if cl then pick k (rs_live s) else None) as [[p below]|];
      [destruct (Nat.ltb (S p) i)|];
      [|exists new; split; [exact E|exact B']..].
    exists (new ++ [(p, i)])%list. rewrite E, <- app_assoc.
    split; [reflexivity|].
    intros a b H. apply in_app_or in H as [H|[H|[]]]; [exact (B' a b H)|].
    injection H as _ <-. lia.
Qed.

Local Lemma facts_hold : forall ts n t s,
  nth_error ts n = Some t -> rinv ts n s ->
  (forall i j, j < S n ->
     In (i, j) (ref_match ts) <-> In (i, j) (rs_pairs (rstep n t s))) ->
  step_facts (ref_match ts) n t (rs_live s).
Proof.
  intros ts n t s Hn I Hpre. pose proof (ref_match_valid ts) as [V1 _].
  set (m := ref_match ts) in *.
  destruct I as [Bd Lv Ds Pr Un]. cbn [rs_live rs_pairs] in *.
  destruct t as [c|k op cl]; [exact Logic.I|].
  assert (Open : (forall i j, j < S n -> In (i, j) m <-> In (i, j) (rs_pairs s))
                 -> is_closer m n = false
                    /\ (op = false -> is_opener m n = false)).
  { intros Hs. split.
    - destruct (is_closer m n) eqn:C; [|reflexivity].
      apply is_closer_iff in C as [i Hi].
      apply (Hs i n (Nat.lt_succ_diag_r n)) in Hi.
      specialize (Bd i n Hi). lia.
    - intros ->. destruct (is_opener m n) eqn:O; [|reflexivity].
      apply is_opener_iff in O as [j Hj].
      destruct (V1 n j Hj) as (k' & _ & [(_ & [cl' Ho] & _) _] & _).
      rewrite Hn in Ho. discriminate. }
  unfold step_facts. revert Hpre. cbn [rstep].
  destruct (if cl then pick k (rs_live s) else None) as [[p below]|] eqn:P;
    [|exact Open].
  destruct (Nat.ltb (S p) n) eqn:L; [|exact Open].
  intros Hpre. cbn [rs_pairs] in Hpre. apply Nat.ltb_lt in L.
  assert (Hpn : In (p, n) m) by (apply Hpre; [lia|left; reflexivity]).
  split.
  { destruct (is_opener m n) eqn:O; [|reflexivity]. exfalso.
    apply is_opener_iff in O as [j Hj].
    destruct (V1 n j Hj) as (_ & _ & [(_ & _ & Hc & _) _] & _).
    apply Hc. exists p. exact Hpn. }
  split; [apply is_closer_iff; exists p; exact Hpn|].
  split; [apply is_opener_iff; exists n; exact Hpn|].
  (* an opener the closer passed over is inside the pair, so it is never
     closed: not before `n`, since it is live there, not at `n`, whose
     opener is `p`, and not after, since it is enclosed *)
  intros q k' Hq Hpq. destruct (is_opener m q) eqn:O; [|reflexivity]. exfalso.
  apply is_opener_iff in O as [j Hj].
  destruct (V1 q j Hj) as (kq & Hkq & Cq & _).
  pose proof Cq as [(Hqj & _ & _ & Hu & He) _].
  apply Lv in Hq. pose proof Hq as [Hqn _].
  destruct (lt_eq_lt_dec j n) as [[Hjn| Ejn]|Hjn].
  - destruct Hq as (_ & _ & _ & Hu' & _). apply Hu'. exists j.
    split; [exact Hjn|].
    apply Hpre in Hj; [|lia].
    destruct Hj as [E|Hj]; [injection E as _ E; lia|exact Hj].
  - subst j. destruct (V1 p n Hpn) as (kp & Hkp & Cp & _).
    rewrite <- (may_close_fun ts n kq kp Hkq Hkp) in Cp.
    pose proof (closest_live_fun ts m n kq q p Cq Cp). lia.
  - apply He. exists p, n. split; [exact Hjn|]. split; [exact Hpn|lia].
Qed.

Local Lemma prun_tree : forall ts suf pre s v,
  ts = (pre ++ suf)%list -> rinv ts (length pre) s ->
  ref_match ts = rs_pairs (rrun (length pre) suf s) ->
  pv_live v = rs_live s ->
  tree_go (ref_match ts) (length pre) suf
    (tembed (collapse (is_opener (ref_match ts)) (pv_stk v) (pv_out v)))
  = tembed (collapse (is_opener (ref_match ts))
              (pv_stk (prun (length pre) suf v))
              (pv_out (prun (length pre) suf v))).
Proof.
  intros ts suf. induction suf as [|t rest IH]; intros pre s v E I Hm Hl;
    cbn [tree_go prun]; [reflexivity|].
  assert (Hn : nth_error ts (length pre) = Some t).
  { rewrite E, nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
  assert (Hpairs : forall i j, j < S (length pre) ->
            In (i, j) (ref_match ts)
            <-> In (i, j) (rs_pairs (rstep (length pre) t s))).
  { intros i j Hj. rewrite Hm. cbn [rrun].
    destruct (rrun_pairs rest (S (length pre)) (rstep (length pre) t s))
      as (new & En & Bn).
    rewrite En. split; [|intros H; apply in_or_app; right; exact H].
    intros H. apply in_app_or in H as [H|H]; [specialize (Bn i j H); lia|].
    exact H. }
  pose proof (facts_hold ts (length pre) t s Hn I Hpairs) as Hf.
  rewrite pstep_tstep;
    [|rewrite Hl; exact (ri_desc _ _ _ I)|rewrite Hl; exact Hf].
  specialize (IH (pre ++ [t])%list (rstep (length pre) t s)
                (pstep (length pre) t v)).
  rewrite length_app in IH. cbn [length] in IH. rewrite Nat.add_1_r in IH.
  apply IH.
  - rewrite E, <- app_assoc. reflexivity.
  - apply rinv_step; assumption.
  - rewrite Hm. reflexivity.
  - apply pstep_live, Hl.
Qed.

Theorem tree_of_prun : forall ts,
  tree_of ts (ref_match ts) = map mk (List.rev (pflatten (prun 0 ts pv0))).
Proof.
  intros ts.
  assert (Live : forall ts' i v s, pv_live v = rs_live s ->
            pv_live (prun i ts' v) = rs_live (rrun i ts' s)).
  { induction ts' as [|t ts' IH]; intros i v s H; [exact H|].
    cbn [prun rrun]. apply IH, pstep_live, H. }
  set (m := ref_match ts).
  pose proof (prun_tree ts ts [] (RState [] []) pv0 eq_refl (rinv_start ts)
                eq_refl eq_refl) as E.
  cbn [length] in E. fold m in E.
  unfold tree_of.
  change (([], []) : tframes * inlines)
    with (tembed (collapse (is_opener m) (pv_stk pv0) (pv_out pv0))).
  rewrite E. set (V := prun 0 ts pv0).
  (* an opener still live at the end is never closed *)
  assert (F : Forall (fun f => is_opener m (fst (fst f)) = false) (pv_stk V)).
  { apply Forall_forall. intros f Hf.
    assert (Hin : In (pkey f) (rs_live (rrun 0 ts (RState [] [])))).
    { rewrite <- (Live ts 0 pv0 (RState [] []) eq_refl), pv_live_pkey.
      apply in_map, Hf. }
    pose proof (rinv_run ts [] ts _ eq_refl (rinv_start ts)) as [_ Lv _ _ _].
    apply Lv in Hin. destruct Hin as (_ & _ & _ & Hu & _).
    destruct (is_opener m (fst (fst f))) eqn:O; [|reflexivity]. exfalso.
    apply is_opener_iff in O as [j Hj].
    destruct (ref_match_valid ts) as [V1 _].
    destruct (V1 _ _ Hj) as (k & [op Hk] & _).
    apply Hu. exists j.
    split; [apply nth_error_Some; rewrite Hk; discriminate|exact Hj]. }
  destruct (flatten_collapse (is_opener m) (pv_stk V) (pv_out V) [] F)
    as [_ E2].
  unfold pflatten. rewrite E2. cbn [xapp tembed snd]. rewrite map_rev.
  reflexivity.
Qed.

(*
The scanner
===========

On the alphabet the scanner is in text mode between tokens, and its
scope stack is the view: a frame per live opener, holding what the view
holds.  The one difference is text not yet flushed, which the view has
already added to its innermost content; the scanner's innermost content
never ends in text, so the two meet by consing it back.

A delimiter token is resolved by the byte after it, which is also what
the token's may-open flag reads. *)

Definition oframe (f : pframe) : frame :=
  Frame (FKDelim (snd (fst f)) false) false null_span
    (map OIn (map mk (snd f))).

Definition oview (v : pview) : ostate :=
  OState (map OIn (map mk (pv_out v))) (map oframe (pv_stk v)) None.

Definition top_of (v : pview) : list inline :=
  match pv_stk v with [] => pv_out v | (_, _, c) :: _ => c end.

Definition starts_text (l : list inline) : bool :=
  match l with Str _ :: _ => true | _ => false end.

Definition add_text (txt : string) (v : pview) : pview :=
  if nonempty_str txt then pv_add (Str txt) v else v.

Definition sim (v : pview) (txt : string) (o : ostate) : Prop :=
  exists v0, o = oview v0 /\ starts_text (top_of v0) = false
             /\ v = add_text txt v0.

Definition bare_frames (stk : list pframe) : Prop :=
  Forall (fun f => bare_row (snd (fst f)) = true) stk.

(* What the view keeps between tokens: live openers innermost first and
   all before `n`, and the innermost one's content is empty exactly when
   it is the last token read. *)
Definition pv_ok (n : nat) (v : pview) : Prop :=
  desc (pv_live v) /\ (forall p k, In (p, k) (pv_live v) -> p < n)
  /\ bare_frames (pv_stk v)
  /\ match pv_stk v with
     | (p, _, c) :: _ => c = [] <-> S p = n
     | [] => True
     end.

Definition prev_ok (prev : option ascii) : bool :=
  match prev with Some c => in_alphabet c | None => true end.

(*
The view, embedded
------------------
*)

Local Lemma osnoc_embed : forall x b,
  osnoc (OIn (mk x)) (map OIn (map mk b)) = map OIn (map mk (xsnoc x b)).
Proof.
  intros x b. destruct b as [|y b]; [reflexivity|].
  destruct (str_view y) as [[t ->]|Hy].
  - destruct (str_view x) as [[s ->]|Hx]; [reflexivity|].
    rewrite (xsnoc_nonstr x _ Hx).
    destruct x; [destruct (Hx _ eq_refl)|..]; reflexivity.
  - destruct (str_view x) as [[s ->]|Hx].
    + rewrite (xsnoc_str_nonstr s y b Hy).
      destruct y; [destruct (Hy _ eq_refl)|..]; reflexivity.
    + rewrite (xsnoc_nonstr x _ Hx).
      destruct y; [destruct (Hy _ eq_refl)|..]; reflexivity.
Qed.

Local Lemma oapp_embed : forall a b,
  oapp (map OIn (map mk a)) (map OIn (map mk b)) = map OIn (map mk (xapp a b)).
Proof.
  induction a as [|x a IH]; intros b; [reflexivity|].
  destruct a as [|y r]; [apply osnoc_embed|].
  change (map OIn (map mk (x :: y :: r)))
    with (OIn (mk x) :: OIn (mk y) :: map OIn (map mk r)).
  rewrite oapp_cons2.
  change (OIn (mk y) :: map OIn (map mk r)) with (map OIn (map mk (y :: r))).
  rewrite IH. reflexivity.
Qed.

Local Lemma bare_decay : forall k,
  bare_row k = true -> ddecay_str k false false = dtoken k.
Proof.
  intros k H. unfold bare_row in H. unfold ddecay_str.
  destruct (dsyntax_of k); try discriminate.
  destruct (dc_decay cfg k); [|discriminate].
  cbn. apply append_empty_r.
Qed.

Local Lemma fr_lit_oframe : forall f,
  bare_row (snd (fst f)) = true -> fr_lit (oframe f) = mk (lit (snd (fst f))).
Proof.
  intros [[p k] c] H. cbn [fst snd] in *.
  unfold fr_lit, oframe, fr_src; cbn [fr_kind fr_marked fst snd].
  rewrite (bare_decay k H). reflexivity.
Qed.

Local Lemma oflatten_embed : forall stk pend out,
  bare_frames stk ->
  oflatten (map OIn (map mk pend)) (map oframe stk) (map OIn (map mk out))
  = map OIn (map mk (pflatten_go pend stk out)).
Proof.
  induction stk as [|[[p k] c] stk IH]; intros pend out B;
    cbn [map oflatten pflatten_go]; [apply oapp_embed|].
  apply Forall_cons_iff in B as [Bk B].
  rewrite (fr_lit_oframe (p, k, c) Bk).
  unfold oframe at 1; cbn [fst snd fr_out].
  rewrite oapp_embed.
  change [OIn (mk (lit k))] with (map OIn (map mk [lit k])).
  rewrite oapp_embed. apply IH, B.
Qed.

Local Lemma oclose_go_embed : forall k pend stk,
  bare_frames stk ->
  oclose_go k false (map OIn (map mk pend)) (map oframe stk)
  = match pclose_go k pend stk with
    | Some (content, rest) =>
        if nonempty content
        then Some (map OIn (map mk content), null_span, map oframe rest)
        else None
    | None => None
    end.
Proof.
  intros k pend stk. revert pend.
  induction stk as [|[[p k'] c] stk IH]; intros pend B; [reflexivity|].
  apply Forall_cons_iff in B as [Bk B].
  cbn [map oclose_go pclose_go]. unfold dmatch at 1.
  rewrite (fr_lit_oframe (p, k', c) Bk).
  cbn [oframe fr_kind fr_marked fr_out fr_open fr_barrier fst snd].
  rewrite oapp_embed. cbn [Bool.eqb andb]. rewrite andb_true_r.
  destruct (dstyle_eq k k'); [destruct (xapp pend c); reflexivity|].
  change [OIn (mk (lit k'))] with (map OIn (map mk [lit k'])).
  rewrite oapp_embed. apply IH, B.
Qed.

Local Lemma flush_view : forall txt v0,
  starts_text (top_of v0) = false ->
  flush_text txt (oview v0) = oview (add_text txt v0).
Proof.
  intros txt [stk out] H. unfold flush_text, flush_text_at, add_text.
  destruct (nonempty_str txt); [|reflexivity].
  assert (X : forall l, starts_text l = false -> xsnoc (Str txt) l = Str txt :: l)
    by (intros [|[] l] Hl; try reflexivity; discriminate).
  unfold pv_add, oview, oemit.
  cbn [pv_stk pv_out os_stk os_out os_word_start] in *.
  destruct stk as [|[[p k] c] rest]; cbn [top_of pv_stk pv_out] in H;
    rewrite (X _ H); reflexivity.
Qed.

Local Lemma bare_frames_add : forall x v,
  bare_frames (pv_stk v) -> bare_frames (pv_stk (pv_add x v)).
Proof.
  intros x [[|[[p k] c] rest] out] B; [exact B|].
  apply Forall_cons_iff in B as [Bk B]. constructor; [exact Bk|exact B].
Qed.

Local Lemma ifinish_view : forall txt prev v0,
  bare_frames (pv_stk v0) -> starts_text (top_of v0) = false ->
  ifinish (IText false txt prev (oview v0))
  = map mk (List.rev (pflatten (add_text txt v0))).
Proof.
  intros txt prev v0 B H.
  unfold ifinish, ifinish_rev, ofinish. rewrite oitems_of_spec.
  cbn [ifinish_ostate ifinish_ostate_flat iresolve].
  change (tval txt) with txt.
  change (@flush_text_at semantic_pos semantic_inline_cursor txt (oview v0))
    with (flush_text txt (oview v0)).
  rewrite (flush_view txt v0 H).
  assert (B' : bare_frames (pv_stk (add_text txt v0))).
  { unfold add_text. destruct (nonempty_str txt); [apply bare_frames_add|];
      exact B. }
  unfold oview at 1 2. cbn [os_stk os_out].
  change ([] : oitems) with (map OIn (map mk ([] : list inline))).
  rewrite (oflatten_embed _ _ _ B'), oresolve_map, map_rev. reflexivity.
Qed.

(*
The view's invariant
--------------------
*)

Local Lemma xsnoc_nonempty : forall x l, xsnoc x l <> [].
Proof.
  intros x [|[] l]; unfold xsnoc; try discriminate; destruct x; discriminate.
Qed.

Local Lemma xapp_nonempty_r : forall a b, b <> [] -> xapp a b <> [].
Proof.
  intros [|x [|y r]] b H; [exact H|apply xsnoc_nonempty|discriminate].
Qed.

Local Lemma pclose_none : forall k stk pend,
  pick k (map pkey stk) = None -> pclose_go k pend stk = None.
Proof.
  intros k stk. induction stk as [|[[p k'] c] stk IH]; intros pend H;
    [reflexivity|].
  cbn [map pkey fst snd pick] in H. cbn [pclose_go].
  destruct (dstyle_eq k k'); [discriminate|]. apply IH, H.
Qed.

Local Lemma pclose_grows : forall k stk pend content rest,
  pclose_go k pend stk = Some (content, rest) -> pend <> [] -> content <> [].
Proof.
  intros k stk. induction stk as [|[[p k'] c] stk IH];
    intros pend content rest H Hp; [discriminate|].
  cbn [pclose_go] in H. destruct (dstyle_eq k k').
  - injection H as <- _. apply xapp_nonempty, Hp.
  - apply (IH _ _ _ H). apply xapp_nonempty_r. discriminate.
Qed.

(* A closer finds its opener's content empty exactly when the opener is
   the token right before it. *)
Local Lemma close_empty : forall n v above p k c rest content rest',
  pv_ok n v -> pv_stk v = (above ++ (p, k, c) :: rest)%list ->
  Forall (fun f => dstyle_eq k (snd (fst f)) = false) above ->
  pclose_go k [] (pv_stk v) = Some (content, rest') ->
  (content = [] <-> S p = n).
Proof.
  intros n v above p k c rest content rest' (D & Bd & _ & Inn) E F H.
  rewrite pv_live_pkey in D, Bd. rewrite E in D, Bd, H, Inn.
  destruct above as [|[[q k1] c1] above'].
  - cbn [app pclose_go] in H.
    assert (dstyle_eq k k = true) as Ek by (apply dstyle_eq_iff; reflexivity).
    rewrite Ek in H. injection H as <- _. exact Inn.
  - (* a frame above the opener: the content holds its spelling, and the
       opener is at least two tokens back *)
    apply Forall_cons_iff in F as [Fk F]. cbn [fst snd] in Fk.
    cbn [app pclose_go] in H. rewrite Fk in H.
    apply pclose_grows in H; [|apply xapp_nonempty_r; discriminate].
    assert (Hpq : p < q).
    { apply (desc_above ((q, k1, c1) :: above') (p, k, c) rest D (q, k1, c1)).
      left. reflexivity. }
    assert (Hq : q < n) by (apply (Bd q k1); left; reflexivity).
    split; [intros; contradiction|lia].
Qed.

Local Lemma pv_ok_add : forall n x v,
  desc (pv_live v) -> (forall p k, In (p, k) (pv_live v) -> p < n) ->
  bare_frames (pv_stk v) -> pv_ok (S n) (pv_add x v).
Proof.
  intros n x v D Bd B. split; [rewrite pv_live_add; exact D|].
  split; [intros p k H; rewrite pv_live_add in H; specialize (Bd p k H); lia|].
  split; [apply bare_frames_add, B|].
  unfold pv_add. destruct (pv_stk v) as [|[[p k] c] rest] eqn:E; [exact I|].
  cbn [pv_stk]. assert (p < n).
  { apply (Bd p k). rewrite pv_live_pkey, E. left. reflexivity. }
  split; [intros Hc; destruct (xsnoc_nonempty x c Hc)|lia].
Qed.

Local Lemma desc_below : forall above f rest,
  desc (map pkey (above ++ f :: rest)) -> desc (map pkey rest).
Proof.
  induction above as [|g above IH]; intros f rest D.
  - apply StronglySorted_inv in D as [D _]. exact D.
  - apply StronglySorted_inv in D as [D _]. exact (IH f rest D).
Qed.

Local Lemma pv_ok_step : forall n t v,
  pv_ok n v ->
  (forall k op cl, t = TDelim k op cl -> bare_row k = true) ->
  pv_ok (S n) (pstep n t v).
Proof.
  intros n t v Ok Hb. pose proof Ok as (D & Bd & B & _).
  assert (Open : forall k op, bare_row k = true -> pv_ok (S n) (popen n k op v)).
  { intros k [|] Hk; [|apply pv_ok_add; assumption].
    unfold popen. split; [|split; [|split]].
    - rewrite pv_live_pkey. cbn [pv_stk map]. rewrite <- pv_live_pkey.
      constructor; [exact D|]. apply Forall_forall. intros [q k'] H.
      cbn. exact (Bd q k' H).
    - rewrite pv_live_pkey. cbn [pv_stk map].
      intros q k' [E|H]; [injection E as <- _; lia|].
      rewrite <- pv_live_pkey in H. specialize (Bd q k' H). lia.
    - constructor; [exact Hk|exact B].
    - cbn [pv_stk]. split; reflexivity. }
  destruct t as [c|k op cl]; cbn [pstep]; [apply pv_ok_add; assumption|].
  specialize (Hb k op cl eq_refl).
  destruct (if cl then pick k (pv_live v) else None) as [[p below]|] eqn:P;
    [|apply Open, Hb].
  destruct (Nat.ltb (S p) n); [|apply Open, Hb].
  destruct cl; [|discriminate].
  rewrite pv_live_pkey in P.
  destruct (pick_split k (pv_stk v) p below P)
    as (above & c & rest & E & F & Hbl).
  rewrite E. destruct (pclose_split k above p c rest [] F) as [content Hc].
  rewrite Hc. apply pv_ok_add; try rewrite pv_live_pkey; cbn [pv_stk].
  - rewrite pv_live_pkey, E in D. exact (desc_below above _ rest D).
  - intros q k' H. apply (Bd q k'). rewrite pv_live_pkey, E, map_app.
    apply in_or_app. right. right. exact H.
  - rewrite E in B. unfold bare_frames in B. apply Forall_app in B as [_ B].
    apply Forall_cons_iff in B as [_ B]. exact B.
Qed.

(*
Text and tokens, scanned
------------------------
*)

Local Lemma sim_text : forall v txt o s,
  sim v txt o -> nonempty_str s = true ->
  sim (pv_add (Str s) v) (txt ++ s) o.
Proof.
  intros v txt o s (v0 & -> & Ht & ->) Hs. exists v0.
  split; [reflexivity|]. split; [exact Ht|].
  assert (X : forall l, starts_text l = false ->
            xsnoc (Str s) (xsnoc (Str txt) l) = xsnoc (Str (txt ++ s)) l)
    by (intros [|[] l] Hl; try reflexivity; discriminate).
  unfold add_text. destruct txt as [|a t'].
  - cbn [append]. rewrite Hs. reflexivity.
  - cbn [nonempty_str append]. unfold pv_add.
    destruct v0 as [[|[[p k] c] rest] out]; cbn [top_of pv_stk pv_out] in Ht |- *;
      rewrite (X _ Ht); reflexivity.
Qed.

Local Lemma ilead_text : forall c txt prev o,
  in_alphabet c = true -> dstyle_of c = None -> prev_ok prev = true ->
  ilead c txt prev o = IText false (txt ++ one c) (Some c) o.
Proof.
  intros c txt prev o Ha Hd Hp.
  unfold in_alphabet in Ha. rewrite Hd in Ha.
  apply andb_true_iff in Ha as [Ha _]. apply andb_true_iff in Ha as [Ha Hhy].
  apply andb_true_iff in Ha as [_ Hres]. apply negb_true_iff in Hres, Hhy.
  pose proof (dreserved_false c Hres)
    as (Hbs & Htk & Hlb & Hrb & Hlk & Hrk & Hbg & Hdol & Hpd & Hlt).
  assert (Hcolon : Ascii.eqb c ":"%char = false).
  { unfold dreserved in Hres.
    repeat (apply orb_false_iff in Hres as [Hres ?]). assumption. }
  (* the byte before is not a bracket, so a `^` is not a footnote marker *)
  assert (Hnote : note_pos txt prev = false).
  { unfold note_pos. destruct prev as [p|]; [|apply andb_false_r].
    cbn [prev_ok] in Hp. destruct (Ascii.eqb p lbrack) eqn:E;
      [|apply andb_false_r].
    apply Ascii.eqb_eq in E. subst p. vm_compute in Hp. discriminate. }
  unfold ilead.
  rewrite Hbs, Htk, Hdol, Hpd, Hhy, Hlb, Hbg, Hlt, Hcolon, Hlk, Hrk, Hnote.
  rewrite andb_false_r. cbn [andb]. rewrite Hd. reflexivity.
Qed.

Local Lemma bunpush_view : forall v, bunpush (oview v) = None.
Proof.
  intros [[|[[p k] c] rest] out]; reflexivity.
Qed.

Local Lemma oclose_barred_view : forall k v, oclose_barred k false (oview v) = false.
Proof.
  intros k v. unfold oclose_barred, oview; cbn [os_stk].
  induction (pv_stk v) as [|f stk IH]; [reflexivity|].
  cbn [map oclose_barred_go].
  destruct (dmatch k false (oframe f)); [reflexivity|exact IH].
Qed.

Local Lemma bare_hyphen : forall k,
  bare_row k = true -> Ascii.eqb (dchar k) hyphen = false.
Proof.
  intros k Hb. apply dchar_bare_free. unfold bare_row in Hb.
  destruct (dsyntax_of k); try discriminate. reflexivity.
Qed.

(* The byte after a token decides it, and is then read as usual. *)
Local Lemma scan_token : forall k rest txt prev o txt' prev' o',
  bare_row k = true -> denabled_of k = true ->
  (forall d r, rest = String d r -> Ascii.eqb d rbrace = false) ->
  idelim_resolve k txt prev false (get 0 rest) o = IText false txt' prev' o' ->
  bunpush o = None ->
  ifinish (iscan_str (dtoken k ++ rest) (IText false txt prev o))
  = ifinish (iscan_str rest (IText false txt' prev' o')).
Proof.
  intros k rest txt prev o txt' prev' o' Hb Hen Hr Hres Hup.
  rewrite iscan_str_app, (iscan_dtoken k txt prev o Hen (bare_hyphen k Hb) Hup).
  assert (Hw : Nat.ltb (S (pred (dwidth k))) (dwidth k) = false).
  { pose proof (dwidth_nonzero k). apply Nat.ltb_ge. lia. }
  destruct rest as [|d r]; cbn [get] in Hres.
  - unfold ifinish, ifinish_rev. cbn [iscan_str ifinish_ostate iresolve].
    rewrite Hw, Hres. reflexivity.
  - cbn [iscan_str]. f_equal. f_equal.
    unfold istep. cbn [istep_at]. rewrite Hw, (Hr d r eq_refl), Hres.
    reflexivity.
Qed.

(* A run of a row's character too short to be a token is text. *)
Local Lemma scan_partial : forall k j rest txt prev o,
  denabled_of k = true -> bare_row k = true ->
  0 < j < dwidth k ->
  (forall d r, rest = String d r -> d <> dchar k) ->
  bunpush o = None ->
  ifinish (iscan_str (chars (dchar k) j ++ rest) (IText false txt prev o))
  = ifinish (iscan_str rest
      (IText false (txt ++ chars (dchar k) j) (Some (dchar k)) o)).
Proof.
  intros k j rest txt prev o Hen Hb [Hj0 Hjw] Hr Hup.
  destruct j as [|j]; [lia|].
  rewrite iscan_str_app. cbn [chars iscan_str].
  unfold istep at 1. cbn [istep_at].
  rewrite (ilead_dchar k txt prev o Hen (bare_hyphen k Hb) Hup).
  rewrite (iscan_chars_delim j k 0 txt prev o) by lia. cbn [plus].
  assert (Hw : Nat.ltb (S j) (dwidth k) = true) by (apply Nat.ltb_lt; lia).
  destruct rest as [|d r].
  - unfold ifinish, ifinish_rev. cbn [iscan_str ifinish_ostate iresolve].
    rewrite Hw. reflexivity.
  - cbn [iscan_str]. f_equal. f_equal.
    unfold istep. cbn [istep_at]. rewrite Hw.
    assert (Ascii.eqb d (dchar k) = false) as Hd
      by (apply Ascii.eqb_neq, (Hr d r eq_refl)).
    rewrite Hd. reflexivity.
Qed.

Local Lemma resolve_sim : forall n k txt prev next v o,
  bare_row k = true -> pv_ok n v -> sim v txt o ->
  exists txt' o',
    idelim_resolve k txt prev false next o = IText false txt' (Some (dchar k)) o'
    /\ sim (pstep n (TDelim k (nonspace_at next) (nonspace_at prev)) v) txt' o'.
Proof.
  intros n k txt prev next v o Hb Ok (v0 & -> & Ht & ->).
  pose proof Ok as (_ & Bd & B & _).
  set (v := add_text txt v0) in *.
  assert (Hv : flush_text txt (oview v0) = oview v) by (apply flush_view, Ht).
  (* the token does not close: it opens if it may, or it is text *)
  assert (Done : exists txt' o',
            idelim_done k txt prev false next (oview v0)
            = IText false txt' (Some (dchar k)) o'
            /\ sim (popen n k (nonspace_at next) v) txt' o').
  { unfold idelim_done.
    assert (dbare k prev = true) as Hd
      by (unfold dbare, bare_row in *; destruct (dsyntax_of k);
          try discriminate; reflexivity).
    rewrite Hd. cbn [negb andb]. destruct (nonspace_at next).
    - change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s
                (tval txt) (oview v0))
        with (flush_text txt (oview v0)).
      rewrite Hv. eexists "", _. split; [reflexivity|].
      exists (PView ((n, k, []) :: pv_stk v) (pv_out v)).
      split; [reflexivity|]. split; reflexivity.
    - eexists (txt ++ dtoken k), (oview v0). split.
      + unfold InlineScan.idelim_lit, InlineScan.idelim_lit_prev.
        cbn [tpush]. rewrite (bare_decay k Hb). reflexivity.
      + apply sim_text; [|apply dtoken_nonempty].
        exists v0. split; [reflexivity|]. split; [exact Ht|reflexivity]. }
  unfold idelim_resolve. rewrite orb_false_r. cbn [pstep].
  destruct (nonspace_at prev) eqn:Hp; [|exact Done].
  rewrite oclose_guard.
  change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s
            (tval txt) (oview v0))
    with (flush_text txt (oview v0)).
  rewrite Hv. unfold oclose. unfold oview at 1.
  cbn [os_stk os_out os_word_start].
  change (@nil oitem) with (map OIn (map mk (@nil inline))).
  rewrite (oclose_go_embed k [] (pv_stk v) B), oclose_barred_view.
  destruct (pick k (pv_live v)) as [[p below]|] eqn:P.
  2: { rewrite pv_live_pkey in P. rewrite (pclose_none k (pv_stk v) [] P).
       exact Done. }
  rewrite pv_live_pkey in P.
  destruct (pick_split k (pv_stk v) p below P)
    as (above & c & rest & E & F & Hbl).
  destruct (pclose_split k above p c rest [] F) as [content Hc].
  rewrite <- E in Hc. rewrite Hc.
  pose proof (close_empty n v above p k c rest content rest Ok E F Hc) as Hce.
  assert (Hpn : p < n).
  { apply (Bd p k). rewrite pv_live_pkey, E, map_app.
    apply in_or_app. right. left. reflexivity. }
  destruct (Nat.ltb (S p) n) eqn:L.
  - apply Nat.ltb_lt in L.
    assert (content <> []) as Hne by (intros H0; apply Hce in H0; lia).
    destruct content as [|x0 content']; [contradiction|]. cbn [nonempty].
    set (content := x0 :: content').
    eexists "", _. split; [reflexivity|].
    exists (pv_add (dnode k (map mk (List.rev content))) (PView rest (pv_out v))).
    split; [|split; [|reflexivity]].
    + rewrite oresolve_map. unfold oemit, oview, pv_add.
      destruct rest as [|[[q k'] c'] rest'];
        cbn [map oframe fst snd pv_out pv_stk os_stk os_out os_word_start
             fr_kind fr_marked fr_open fr_out];
        rewrite (xsnoc_nonstr _ _ (dnode_nonstr k _)); cbn [map];
        rewrite <- map_rev; reflexivity.
    + unfold pv_add.
      destruct rest as [|[[q k'] c'] rest']; cbn [pv_stk pv_out top_of];
        rewrite (xsnoc_nonstr _ _ (dnode_nonstr k _)); unfold starts_text;
        destruct k; reflexivity.
  - apply Nat.ltb_ge in L.
    assert (content = []) as -> by (apply Hce; lia). exact Done.
Qed.

(*
Tokens, lexed
-------------
*)

Local Lemma lex_skip : forall j c rest,
  lex (Some c) j (chars c j ++ rest) = lex (Some c) 0 rest.
Proof.
  induction j as [|j IH]; intros c rest; [reflexivity|]. apply IH.
Qed.

Local Lemma prefix_chars : forall c w j rest,
  w <= j -> prefix (chars c w) (chars c j ++ rest) = true.
Proof.
  intros c w. induction w as [|w IH]; intros j rest Hj;
    [destruct (chars c j ++ rest)%string; reflexivity|].
  destruct j as [|j]; [lia|]. cbn [chars append prefix].
  destruct (ascii_dec c c) as [_|Hn]; [apply IH; lia|contradiction].
Qed.

Local Lemma prefix_chars_short : forall c w j rest,
  j < w -> (forall d r, rest = String d r -> d <> c) ->
  prefix (chars c w) (chars c j ++ rest) = false.
Proof.
  intros c w j. revert w. induction j as [|j IH]; intros w rest Hj Hr.
  - destruct w as [|w]; [lia|]. cbn [chars append].
    destruct rest as [|d r]; [reflexivity|]. cbn [prefix].
    destruct (ascii_dec c d) as [E|_]; [|reflexivity].
    subst d. destruct (Hr c r eq_refl). reflexivity.
  - destruct w as [|w]; [lia|]. cbn [chars append prefix].
    destruct (ascii_dec c c) as [_|Hn]; [apply IH; [lia|exact Hr]|contradiction].
Qed.

Local Lemma run_split : forall c s,
  exists j rest, s = (chars c j ++ rest)%string
                 /\ forall d r, rest = String d r -> d <> c.
Proof.
  intros c s. induction s as [|d s IH].
  - exists 0, EmptyString. split; [reflexivity|]. intros d r E. discriminate.
  - destruct (ascii_dec d c) as [->|Hn].
    + destruct IH as (j & rest & -> & Hr). exists (S j), rest.
      split; [reflexivity|exact Hr].
    + exists 0, (String d s). split; [reflexivity|].
      intros d' r E. injection E as <- _. exact Hn.
Qed.

Local Lemma lex_token : forall k prev rest,
  dstyle_of (dchar k) = Some k ->
  lex prev 0 (dtoken k ++ rest)
  = TDelim k (nonspace_at (get 0 rest)) (nonspace_at prev)
      :: lex (Some (dchar k)) 0 rest.
Proof.
  intros k prev rest Hk.
  assert (Hg : forall c n r, get n (chars c n ++ r) = get 0 r)
    by (intros c n r; induction n as [|n IH]; [reflexivity|exact IH]).
  assert (Hpre : prefix (dtoken k) (dtoken k ++ rest) = true)
    by (apply prefix_chars; lia).
  destruct (dwidth k) as [|w] eqn:Ew; [destruct (dwidth_nonzero k Ew)|].
  assert (Ed : dtoken k = String (dchar k) (chars (dchar k) w))
    by (unfold dtoken; rewrite Ew; reflexivity).
  rewrite Ed at 1. cbn [append lex]. rewrite Hk.
  replace (String (dchar k) (chars (dchar k) w ++ rest))
    with (dtoken k ++ rest)%string by (rewrite Ed; reflexivity).
  rewrite Hpre. unfold dtoken. rewrite Ew, Hg. cbn [pred].
  rewrite lex_skip. reflexivity.
Qed.

Local Lemma lex_partial : forall k j prev rest,
  dstyle_of (dchar k) = Some k -> j < dwidth k ->
  (forall d r, rest = String d r -> d <> dchar k) ->
  lex prev 0 (chars (dchar k) j ++ rest)
  = (repeat (TText (dchar k)) j
     ++ lex (if Nat.eqb j 0 then prev else Some (dchar k)) 0 rest)%list.
Proof.
  intros k j. induction j as [|j IH]; intros prev rest Hk Hj Hr; [reflexivity|].
  cbn [chars append lex]. rewrite Hk.
  replace (prefix (dtoken k) (String (dchar k) (chars (dchar k) j ++ rest)))
    with false
    by (symmetry;
        exact (prefix_chars_short (dchar k) (dwidth k) (S j) rest Hj Hr)).
  rewrite (IH (Some (dchar k)) rest Hk ltac:(lia) Hr).
  cbn [repeat app Nat.eqb]. destruct j; reflexivity.
Qed.

(*
The line
--------
*)

Local Lemma over_alphabet_cons : forall c s,
  over_alphabet (String c s) <-> in_alphabet c = true /\ over_alphabet s.
Proof.
  intros c s. unfold over_alphabet. cbn [list_ascii_of_string In]. split.
  - intros H. split; [apply H; left; reflexivity|].
    intros d Hd. apply H. right. exact Hd.
  - intros [Hc H] d [<-|Hd]; [exact Hc|exact (H d Hd)].
Qed.

Local Lemma over_alphabet_app : forall a b,
  over_alphabet (a ++ b) <-> over_alphabet a /\ over_alphabet b.
Proof.
  induction a as [|c a IH]; intros b; cbn [append].
  - split; [intros H; split; [intros d []|exact H]|intros [_ H]; exact H].
  - rewrite !over_alphabet_cons, IH. tauto.
Qed.

Local Lemma chars_add : forall c a b,
  chars c (a + b) = (chars c a ++ chars c b)%string.
Proof.
  intros c a b. induction a as [|a IH]; [reflexivity|]. cbn. rewrite IH.
  reflexivity.
Qed.

Local Lemma length_chars : forall c m, String.length (chars c m) = m.
Proof.
  intros c m. induction m as [|m IH]; [reflexivity|]. cbn. rewrite IH.
  reflexivity.
Qed.

Local Lemma prun_app : forall a b i v,
  prun i (a ++ b) v = prun (i + length a) b (prun i a v).
Proof.
  induction a as [|t a IH]; intros b i v; cbn [app prun length];
    [rewrite Nat.add_0_r; reflexivity|].
  rewrite IH. f_equal. lia.
Qed.

Local Lemma prun_texts : forall c j n v txt o,
  sim v txt o -> pv_ok n v ->
  sim (prun n (repeat (TText c) j) v) (txt ++ chars c j) o
  /\ pv_ok (n + j) (prun n (repeat (TText c) j) v).
Proof.
  intros c j. induction j as [|j IH]; intros n v txt o Hs Ok; cbn [repeat prun].
  - rewrite append_empty_r, Nat.add_0_r. split; assumption.
  - destruct (IH (S n) (pstep n (TText c) v) (txt ++ one c) o) as [Hs' Ok'].
    + apply sim_text; [exact Hs|reflexivity].
    + apply pv_ok_step; [exact Ok|intros k op cl E; discriminate].
    + change (chars c (S j)) with (one c ++ chars c j)%string.
      rewrite <- append_assoc, <- Nat.add_succ_comm. split; assumption.
Qed.

Local Lemma bare_frames_add_inv : forall x v,
  bare_frames (pv_stk (pv_add x v)) -> bare_frames (pv_stk v).
Proof.
  intros x [[|[[p k] c] rest] out] B; [exact B|].
  apply Forall_cons_iff in B as [Bk B]. constructor; [exact Bk|exact B].
Qed.

Local Lemma scan_sim : forall len s prev txt o n v,
  String.length s <= len -> over_alphabet s -> prev_ok prev = true ->
  pv_ok n v -> sim v txt o ->
  ifinish (iscan_str s (IText false txt prev o))
  = map mk (List.rev (pflatten (prun n (lex prev 0 s) v))).
Proof.
  induction len as [|len IH]; intros s prev txt o n v Hl Ha Hp Ok Hs;
    destruct s as [|c s'].
  1,3: destruct Hs as (v0 & -> & Ht & ->); cbn [iscan_str lex prun];
       apply ifinish_view; [|exact Ht];
       destruct Ok as (_ & _ & B & _); unfold add_text in B;
       destruct (nonempty_str txt); [exact (bare_frames_add_inv _ _ B)|exact B].
  1: cbn [String.length] in Hl; lia.
  change (String.length (String c s') <= S len) in Hl.
  pose proof Ha as Ha'. apply over_alphabet_cons in Ha' as [Hc Hs'].
  pose proof Hs as (v0 & Ho & _ & _).
  assert (Hup : bunpush o = None) by (rewrite Ho; apply bunpush_view).
  destruct (dstyle_of c) as [k|] eqn:Hd.
  2: { (* a plain byte *)
       cbn [iscan_str]. unfold istep. cbn [istep_at].
       rewrite (ilead_text c txt prev o Hc Hd Hp).
       cbn [lex]. rewrite Hd. cbn [prun pstep].
       apply IH; [cbn [String.length] in Hl; lia|exact Hs'|exact Hc| |].
       - apply (pv_ok_step n (TText c) v Ok). intros ? ? ? E; discriminate.
       - apply sim_text; [exact Hs|reflexivity]. }
  assert (Hk : bare_row k = true).
  { unfold in_alphabet in Hc. rewrite Hd in Hc.
    apply andb_true_iff in Hc as [_ Hc]. exact Hc. }
  pose proof (dstyle_of_enabled c k Hd) as Hen.
  pose proof (dstyle_of_char c k Hd) as Ec. subst c.
  destruct (run_split (dchar k) (String (dchar k) s')) as (j & rest0 & E & Hr).
  destruct j as [|j'].
  { cbn [chars append] in E. destruct (Hr (dchar k) s' (eq_sym E) eq_refl). }
  set (j := S j') in *.
  destruct (Nat.le_gt_cases (dwidth k) j) as [Hw|Hw].
  - (* a whole token, then what follows the token *)
    set (rest := (chars (dchar k) (j - dwidth k) ++ rest0)%string).
    assert (Es : String (dchar k) s' = (dtoken k ++ rest)%string).
    { rewrite E. unfold rest, dtoken. rewrite <- append_assoc, <- chars_add.
      f_equal. f_equal. lia. }
    rewrite Es in Ha, Hl |- *.
    apply over_alphabet_app in Ha as [_ Hrest].
    assert (Hfirst : forall d r, rest = String d r -> Ascii.eqb d rbrace = false).
    { intros d r Er. rewrite Er in Hrest.
      apply over_alphabet_cons in Hrest as [Hdd _].
      unfold in_alphabet in Hdd. apply andb_true_iff in Hdd as [Hdd _].
      apply andb_true_iff in Hdd as [Hdd _].
      apply andb_true_iff in Hdd as [_ Hres].
      apply negb_true_iff in Hres. apply (dreserved_false d Hres). }
    destruct (resolve_sim n k txt prev (get 0 rest) v o Hk Ok Hs)
      as (txt' & o' & Hres & Hsim).
    rewrite (scan_token k rest txt prev o txt' (Some (dchar k)) o'
               Hk Hen Hfirst Hres Hup).
    rewrite (lex_token k prev rest Hd). cbn [prun].
    rewrite length_append in Hl. pose proof (dtoken_nonempty k) as Hne.
    apply IH; [|exact Hrest|exact Hc| |exact Hsim].
    + destruct (dtoken k); [discriminate|]. cbn [String.length] in Hl. lia.
    + apply pv_ok_step; [exact Ok|].
      intros k' op cl Et. injection Et as <- _ _. exact Hk.
  - (* a run too short to be a token *)
    rewrite E in Ha, Hl |- *.
    apply over_alphabet_app in Ha as [_ Hrest].
    rewrite (scan_partial k j rest0 txt prev o Hen Hk ltac:(lia) Hr Hup).
    rewrite (lex_partial k j prev rest0 Hd Hw Hr). cbn [Nat.eqb j].
    rewrite prun_app, repeat_length.
    destruct (prun_texts (dchar k) j n v txt o Hs Ok) as [Hs2 Ok2].
    rewrite length_append, length_chars in Hl.
    apply IH; [lia|exact Hrest|exact Hc|exact Ok2|exact Hs2].
Qed.

(*
The theorem
===========

On a line over the alphabet, the scanner builds the tree of the unique
matching the precedence rules allow. *)

Theorem parse_inline_line_matching : forall s,
  over_alphabet s ->
  parse_inline_line s = tree_of (tokens s) (ref_match (tokens s)).
Proof.
  intros s Ha. unfold parse_inline_line, istart. rewrite tree_of_prun.
  apply (scan_sim (String.length s) s None "" ostart 0 pv0); auto.
  - split; [constructor|]. split; [intros p k []|]. split; [constructor|exact I].
  - exists pv0. split; [reflexivity|]. split; reflexivity.
Qed.

(* A paragraph's last line is read with its trailing whitespace
   stripped. *)
Corollary para_inlines_matching : forall s,
  over_alphabet s ->
  para_inlines [s]
  = tree_of (tokens (strip_trailing_ws s))
      (ref_match (tokens (strip_trailing_ws s))).
Proof.
  intros s Ha. apply parse_inline_line_matching.
  destruct (strip_trailing_split s) as (w & _ & E).
  rewrite E in Ha. apply over_alphabet_app in Ha as [Ha _]. exact Ha.
Qed.

(* The same in the reference's terms: the paragraph is the tree of any
   matching the precedence rules allow (P1, P5), since there is one. *)

Local Lemma tree_of_members : forall ts m1 m2,
  (forall i j, In (i, j) m1 <-> In (i, j) m2) -> tree_of ts m1 = tree_of ts m2.
Proof.
  intros ts m1 m2 E.
  assert (Eo : forall i, is_opener m1 i = is_opener m2 i).
  { intros i. apply Bool.eq_true_iff_eq. rewrite !is_opener_iff.
    split; intros [j H]; exists j; apply E; exact H. }
  assert (Ec : forall i, is_closer m1 i = is_closer m2 i).
  { intros i. apply Bool.eq_true_iff_eq. rewrite !is_closer_iff.
    split; intros [j H]; exists j; apply E; exact H. }
  unfold tree_of. f_equal. f_equal.
  generalize 0 as i. generalize (([], []) : tframes * inlines) as st.
  induction ts as [|t ts IH]; intros st i; cbn [tree_go]; [reflexivity|].
  replace (tstep m1 i t st) with (tstep m2 i t st); [apply IH|].
  destruct t; [rewrite !tstep_text|rewrite !tstep_delim, Eo, Ec]; reflexivity.
Qed.

Corollary para_inlines_valid : forall s m,
  over_alphabet s -> valid (tokens (strip_trailing_ws s)) m ->
  para_inlines [s] = tree_of (tokens (strip_trailing_ws s)) m.
Proof.
  intros s m Ha Hv. rewrite (para_inlines_matching s Ha).
  apply tree_of_members.
  exact (valid_unique _ _ m (ref_match_valid _) Hv).
Qed.

End WithTable.
