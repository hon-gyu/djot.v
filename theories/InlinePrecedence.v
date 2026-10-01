(* ai-disclosure: autonomous *)

(* The inline scanner builds the tree the precedence rules describe
   (`Precedence.v`): on a paragraph of delimiters, bare or marked with
   braces, brackets with their destinations and labels, and plain bytes,
   `para_inlines` is `tree_of` of the unique valid reading. *)

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

What the scanner holds after a prefix of the tokens: the openers still
open, innermost first, each with what has been read since it, a frame
for each destination that does not close, above what was read before
the outermost one; and, after a bracket's closer, the region being read.
An opener dies with the pair that closes over it, and at the end every
frame still open is text.

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

(* An opener's spelling, which it reads as once it is text. *)
Definition lit (k : key) : inline :=
  Str (match k with
       | KDelim k' mr => tok_text (TDelim k' mr true false)
       | KBracket => one lbrack
       end).

(* An opener's frame, or a destination's: its region is read inside the
   bracket's scope, which reads as `[`, the link text and `](` first. *)
Inductive pframe : Type :=
  | PF (p : nat) (k : key) (c : list inline)
  | PB (d : nat) (c : list inline).

Definition fcontent (f : pframe) : list inline :=
  match f with PF _ _ c | PB _ c => c end.

Definition flit (f : pframe) : inline :=
  match f with PF _ k _ => lit k | PB _ _ => Str (one lbrack) end.

Definition fitem (f : pframe) : litem :=
  match f with PF p k _ => LOpen p k | PB d _ => LBar d end.

Definition fset (f : pframe) (c : list inline) : pframe :=
  match f with PF p k _ => PF p k c | PB d _ => PB d c end.

(* As `rmode`, with what a region has gathered: its link text and its
   text so far. *)
Inductive pmode : Type :=
  | PMNormal
  | PMRegion (dest : bool) (kids : list inline) (d : nat) (e : option nat) (txt : string).

Record pview : Type := PView {
  pv_stk : list pframe;
  pv_out : list inline;
  pv_mode : pmode
}.

Definition pv0 : pview := PView [] [] PMNormal.

(* The stack, as `rstep` keeps it. *)
Definition pv_live (v : pview) : list litem := map fitem (pv_stk v).

Definition pv_add (x : inline) (v : pview) : pview :=
  match pv_stk v with
  | [] => PView [] (xsnoc x (pv_out v)) (pv_mode v)
  | f :: rest => PView (fset f (xsnoc x (fcontent f)) :: rest) (pv_out v) (pv_mode v)
  end.

Definition pv_setmode (md : pmode) (v : pview) : pview :=
  PView (pv_stk v) (pv_out v) md.

(* Close the innermost frame of key `k`, turning the frames above it
   into text in its content.  A destination's frame stops the search. *)
Fixpoint pclose_go (k : key) (pend : list inline) (stk : list pframe)
  : option (list inline * list pframe) :=
  match stk with
  | [] => None
  | PB _ _ :: _ => None
  | PF p k' c :: rest =>
      let content := xapp pend c in
      if key_eq k k' then Some (content, rest)
      else pclose_go k (xapp content [lit k']) rest
  end.

(* A token that does not close opens if it may, or is its own text. *)
Definition popen (i : nat) (k : key) (op : bool) (txt : string) (v : pview)
  : pview :=
  if op then PView (PF i k [] :: pv_stk v) (pv_out v) (pv_mode v)
  else pv_add (Str txt) v.

(* `rstep`, keeping the content. *)
Definition pstep (ts : list token) (i : nat) (t : token) (v : pview) : pview :=
  match pv_mode v with
  | PMRegion b kids d e txt =>
      if match e with Some e' => Nat.eqb i e' | None => false end
      then pv_add (region_node b (map mk kids) txt) (pv_setmode PMNormal v)
      else pv_setmode (PMRegion b kids d e
                         (if Nat.eqb i (S d) then txt else (txt ++ tok_text t)%string)) v
  | PMNormal =>
      match t with
      | TText c => pv_add (Str (one c)) v
      | TBreak => pv_add SoftBreak v
      | TOpen => popen i KBracket true (tok_text t) v
      | TDelim k mr op cl =>
          match (if cl then pick (KDelim k mr) (pv_live v) else PNone) with
          | PFound p _ =>
              if Nat.ltb (S p) i
              then match pclose_go (KDelim k mr) [] (pv_stk v) with
                   | Some (content, rest) =>
                       pv_add (dnode k (map mk (List.rev content)))
                         (PView rest (pv_out v) PMNormal)
                   | None => v
                   end
              else popen i (KDelim k mr) op (tok_text t) v
          | PBarred => pv_add (Str (tok_text t)) v
          | PNone => popen i (KDelim k mr) op (tok_text t) v
          end
      | TClose b =>
          match pick KBracket (pv_live v), pclose_go KBracket [] (pv_stk v) with
          | PFound _ _, Some (content, rest) =>
              match region_end ts i b with
              | Some e => PView rest (pv_out v) (PMRegion b (List.rev content) i (Some e) "")
              | None =>
                  if b
                  then PView (PB i (xsnoc (Str (one rbrack)) content) :: rest)
                         (pv_out v) PMNormal
                  else PView rest (pv_out v) (PMRegion false (List.rev content) i None "")
              end
          | _, _ => pv_add (Str (tok_text t)) v
          end
      end
  end.

Fixpoint prun (ts : list token) (i : nat) (rest : list token) (v : pview) : pview :=
  match rest with
  | [] => v
  | t :: more => prun ts (S i) more (pstep ts i t v)
  end.

Fixpoint pv_add_all (xs : list inline) (v : pview) : pview :=
  match xs with [] => v | x :: rest => pv_add_all rest (pv_add x v) end.

(* Every open frame read as text, as at the end of the paragraph, after a
   reference label that never ended has been put back as text. *)
Fixpoint pflatten_go (pend : list inline) (stk : list pframe)
  (bottom : list inline) : list inline :=
  match stk with
  | [] => xapp pend bottom
  | f :: rest => pflatten_go (xapp (xapp pend (fcontent f)) [flit f]) rest bottom
  end.

Definition pfinish (v : pview) : pview :=
  match pv_mode v with
  | PMRegion _ kids _ None txt =>
      pv_add_all (Str (one lbrack) :: kids
                  ++ [Str (one rbrack ++ one lbrack ++ txt)])%list v
  | _ => v
  end.

Definition pflatten (v : pview) : list inline :=
  let v' := pfinish v in pflatten_go [] (pv_stk v') (pv_out v').

(* The frames of `tree_go` that a view stands for, given which openers
   the whole line closes: a frame whose opener is closed stays a frame,
   and any other is its opener's text and its content, in the frame
   below it. *)
Definition xinner (g : list inline -> list inline)
  (st : list (tkind * list inline) * list inline)
  : list (tkind * list inline) * list inline :=
  match st with
  | ([], top) => ([], g top)
  | ((k, c) :: fs, top) => ((k, g c) :: fs, top)
  end.

Definition tkind_of (k : key) : tkind :=
  match k with KDelim k' _ => TKDelim k' | KBracket => TKBracket end.

Fixpoint collapse (real : nat -> bool) (stk : list pframe) (out : list inline)
  : list (tkind * list inline) * list inline :=
  match stk with
  | [] => ([], out)
  | PF p k c :: rest =>
      if real p then ((tkind_of k, c) :: fst (collapse real rest out),
                      snd (collapse real rest out))
      else xinner (fun acc => xapp c (xsnoc (lit k) acc)) (collapse real rest out)
  | PB _ c :: rest =>
      xinner (fun acc => xapp c (xsnoc (Str (one lbrack)) acc)) (collapse real rest out)
  end.

Definition membed (md : pmode) : tmode :=
  match md with
  | PMNormal => TMNormal
  | PMRegion b kids d e txt => TMRegion b (map mk kids) d e txt
  end.

Definition tembed (st : list (tkind * list inline) * list inline) (md : pmode)
  : tstate :=
  (map (fun f => (fst f, map mk (snd f))) (fst st), map mk (snd st), membed md).

Definition vembed (real : nat -> bool) (v : pview) : tstate :=
  tembed (collapse real (pv_stk v) (pv_out v)) (pv_mode v).

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
Normal contents
---------------

A content never has two `Str`s side by side.  Emitting nodes one at a
time, as `temit_all` does, then agrees with `xapp`.
*)

Definition is_str (x : inline) : bool := match x with Str _ => true | _ => false end.

Fixpoint normal (l : list inline) : Prop :=
  match l with
  | [] => True
  | x :: rest =>
      match rest with
      | [] => True
      | y :: _ => (is_str x = false \/ is_str y = false) /\ normal rest
      end
  end.

Local Lemma normal_tail : forall x l, normal (x :: l) -> normal l.
Proof. intros x [|y l] H; [exact Logic.I|exact (proj2 H)]. Qed.

Local Lemma normal_xsnoc : forall x l, normal l -> normal (xsnoc x l).
Proof.
  intros x [|y l] H; [destruct x; exact Logic.I|].
  destruct (str_view x) as [[s ->]|Hx].
  - destruct (str_view y) as [[t ->]|Hy].
    + cbn. destruct l as [|z l]; [exact Logic.I|]. split; [|exact (proj2 H)].
      destruct H as [[H|H] _]; [discriminate|right; exact H].
    + rewrite (xsnoc_str_nonstr s y l Hy). split; [|exact H].
      right. destruct y; [destruct (Hy _ eq_refl)|..]; reflexivity.
  - rewrite (xsnoc_nonstr x _ Hx). split; [|exact H].
    left. destruct x; [destruct (Hx _ eq_refl)|..]; reflexivity.
Qed.

Local Lemma normal_xapp : forall a b, normal a -> normal b -> normal (xapp a b).
Proof.
  induction a as [|x a IH]; intros b Ha Hb; [exact Hb|].
  destruct a as [|y r]; [apply normal_xsnoc, Hb|].
  change (xapp (x :: y :: r) b) with (x :: xapp (y :: r) b).
  pose proof (IH b (normal_tail _ _ Ha) Hb) as H.
  assert (Hne : xapp (y :: r) b <> []) by (apply xapp_nonempty; discriminate).
  destruct (xapp (y :: r) b) as [|z w] eqn:E; [contradiction|].
  split; [|exact H].
  destruct Ha as [[Hx|Hy] _]; [left; exact Hx|right].
  (* the head of `xapp (y :: r) b` is `y`, or a `Str` merged from it *)
  destruct r as [|r0 r].
  - cbn [xapp] in E. destruct (str_view y) as [[t ->]|Hy'].
    + discriminate Hy.
    + rewrite (xsnoc_nonstr y b Hy') in E. injection E as <- _. exact Hy.
  - cbn [xapp] in E. injection E as <- _. exact Hy.
Qed.

(* Pushing the nodes of a normal content in order is `xapp`. *)
Local Lemma fold_xsnoc : forall c acc,
  normal c -> fold_left (fun a x => xsnoc x a) (List.rev c) acc = xapp c acc.
Proof.
  induction c as [|x c IH]; intros acc H; [reflexivity|].
  cbn [List.rev]. rewrite fold_left_app. cbn [fold_left].
  rewrite (IH acc (normal_tail _ _ H)).
  destruct c as [|y c]; [reflexivity|].
  change (xapp (x :: y :: c) acc) with (x :: xapp (y :: c) acc).
  assert (Hne : xapp (y :: c) acc <> []) by (apply xapp_nonempty; discriminate).
  destruct H as [[Hx|Hy] _].
  - apply xsnoc_nonstr. intros s E. rewrite E in Hx. discriminate.
  - destruct (str_view x) as [[s ->]|Hx]; [|apply xsnoc_nonstr, Hx].
    destruct c as [|z c].
    + cbn [xapp]. destruct (str_view y) as [[t ->]|Hy']; [discriminate Hy|].
      rewrite (xsnoc_nonstr y acc Hy'). apply xsnoc_str_nonstr, Hy'.
    + cbn [xapp]. apply xsnoc_str_nonstr.
      intros u E. rewrite E in Hy. discriminate.
Qed.

(*
Collapsing the view
-------------------
*)

Local Lemma collapse_add : forall real x v,
  collapse real (pv_stk (pv_add x v)) (pv_out (pv_add x v))
  = xinner (xsnoc x) (collapse real (pv_stk v) (pv_out v)).
Proof.
  intros real x [stk out md]. unfold pv_add; cbn [pv_stk pv_out].
  destruct stk as [|[p k c|d c] rest]; [reflexivity| |];
    cbn [pv_stk pv_out pv_mode fset fcontent collapse].
  - destruct (real p); [reflexivity|].
    destruct (collapse real rest out) as [[|[k' c'] fs] top]; cbn [xinner];
      rewrite xapp_xsnoc; reflexivity.
  - destruct (collapse real rest out) as [[|[k' c'] fs] top]; cbn [xinner];
      rewrite xapp_xsnoc; reflexivity.
Qed.

(* The frames a closer passes over are openers of other keys: a
   destination's frame would have stopped `pick`. *)
Definition passes (k : key) (f : pframe) : Prop :=
  match f with PF _ k' _ => key_eq k k' = false | PB _ _ => False end.

Local Lemma pick_split : forall k stk p below,
  pick k (map fitem stk) = PFound p below ->
  exists above c rest,
    stk = (above ++ PF p k c :: rest)%list
    /\ Forall (passes k) above
    /\ map fitem rest = below.
Proof.
  intros k stk. induction stk as [|[q k' c|d c] stk IH]; intros p below H;
    [discriminate| |].
  - cbn [map fitem pick] in H. destruct (key_eq k k') eqn:E.
    + injection H as <- <-. apply key_eq_iff in E. subst k'.
      exists [], c, stk. split; [reflexivity|]. split; [constructor|reflexivity].
    + destruct (IH p below H) as (above & c' & rest & -> & F & Hb).
      exists (PF q k' c :: above)%list, c', rest. split; [reflexivity|].
      split; [constructor; [exact E|exact F]|exact Hb].
  - cbn [map fitem pick] in H. destruct (has_key k (map fitem stk)); discriminate.
Qed.

Local Lemma pclose_split : forall k above p c rest pend,
  Forall (passes k) above ->
  exists content,
    pclose_go k pend (above ++ PF p k c :: rest) = Some (content, rest).
Proof.
  intros k above. induction above as [|f above IH]; intros p c rest pend F;
    cbn [app pclose_go].
  - rewrite key_eq_refl. eexists. reflexivity.
  - apply Forall_cons_iff in F as [E F].
    destruct f as [q k1 c1|d c1]; [|destruct E]. cbn [passes] in E. rewrite E.
    apply IH, F.
Qed.

Local Lemma close_collapse : forall real k above p c rest out pend,
  Forall (fun f => passes k f /\ match f with PF q _ _ => real q = false | PB _ _ => True end)
    above ->
  real p = true ->
  exists content,
    pclose_go k pend (above ++ PF p k c :: rest) = Some (xapp pend content, rest)
    /\ collapse real (above ++ PF p k c :: rest) out
       = ((tkind_of k, content) :: fst (collapse real rest out),
          snd (collapse real rest out)).
Proof.
  intros real k above.
  induction above as [|f above IH]; intros p c rest out pend F Hp; cbn [app pclose_go collapse].
  - rewrite key_eq_refl, Hp. exists c. split; reflexivity.
  - apply Forall_cons_iff in F as [[E Hq] F].
    destruct f as [q k1 c1|d c1]; [|destruct E]. cbn [passes] in E.
    rewrite E, Hq.
    destruct (IH p c rest out (xapp (xapp pend c1) [lit k1]) F Hp)
      as (content & Hc & Hl).
    exists (xapp c1 (xsnoc (lit k1) content)). rewrite Hc, Hl.
    split; [|reflexivity]. rewrite !xapp_assoc. reflexivity.
Qed.

Local Lemma flatten_collapse : forall real stk out pend,
  Forall (fun f => match f with PF q _ _ => real q = false | PB _ _ => True end) stk ->
  collapse real stk out = ([], snd (collapse real stk out))
  /\ pflatten_go pend stk out = xapp pend (snd (collapse real stk out)).
Proof.
  intros real stk out.
  induction stk as [|f stk IH]; intros pend F;
    cbn [collapse pflatten_go]; [split; reflexivity|].
  apply Forall_cons_iff in F as [Hq F].
  destruct f as [q k c|d c]; cbn [fcontent flit] in *; [rewrite Hq|].
  - destruct (IH (xapp (xapp pend c) [lit k]) F) as [E1 E2].
    rewrite E1 in *; cbn [xinner fst snd]; rewrite E2; split; [reflexivity|].
    rewrite !xapp_assoc; reflexivity.
  - destruct (IH (xapp (xapp pend c) [Str (one lbrack)]) F) as [E1 E2].
    rewrite E1 in *; cbn [xinner fst snd]; rewrite E2; split; [reflexivity|].
    rewrite !xapp_assoc; reflexivity.
Qed.

(*
The tree, embedded
------------------
*)

Definition tfr (st : list (tkind * list inline) * list inline) : tframes * inlines :=
  (map (fun f => (fst f, map mk (snd f))) (fst st), map mk (snd st)).

Local Lemma temit_str_embed : forall s st,
  temit_str s (fst (tfr st)) (snd (tfr st)) = tfr (xinner (xsnoc (Str s)) st).
Proof.
  intros s [[|[k c] fs] top]; cbn; rewrite str_snoc_mk; reflexivity.
Qed.

Local Lemma temit_embed : forall x st,
  temit (mk x) (fst (tfr st)) (snd (tfr st)) = tfr (xinner (cons x) st).
Proof. intros x [[|[k c] fs] top]; reflexivity. Qed.

Local Lemma xinner_ext : forall g h st,
  (forall l, g l = h l) -> xinner g st = xinner h st.
Proof. intros g h [[|[k c] fs] top] H; cbn; rewrite H; reflexivity. Qed.

Local Lemma xinner_comp : forall g h st, xinner g (xinner h st) = xinner (fun l => g (h l)) st.
Proof. intros g h [[|[k c] fs] top]; reflexivity. Qed.

Local Lemma temit_all_embed : forall l st,
  temit_all (map mk l) (fst (tfr st)) (snd (tfr st))
  = tfr (xinner (fun acc => fold_left (fun a x => xsnoc x a) l acc) st).
Proof.
  induction l as [|x l IH]; intros st.
  - destruct st as [[|[k c] fs] top]; reflexivity.
  - cbn [map fold_left]. destruct (str_view x) as [[s ->]|Hx].
    + cbn [temit_all mk]. rewrite temit_str_embed.
      change (let '(fs', top') := tfr (xinner (xsnoc (Str s)) st) in
              temit_all (map mk l) fs' top')
        with (temit_all (map mk l) (fst (tfr (xinner (xsnoc (Str s)) st)))
                (snd (tfr (xinner (xsnoc (Str s)) st)))).
      rewrite IH, xinner_comp. reflexivity.
    + assert (E : temit_all (mk x :: map mk l) (fst (tfr st)) (snd (tfr st))
                  = temit_all (map mk l) (fst (tfr (xinner (cons x) st)))
                      (snd (tfr (xinner (cons x) st)))).
      { rewrite <- temit_embed.
        destruct x; [destruct (Hx _ eq_refl)|..]; cbn [temit_all mk];
          destruct (temit _ _ _); reflexivity. }
      rewrite E, IH, xinner_comp. apply f_equal, xinner_ext. intros acc.
      rewrite (xsnoc_nonstr x acc Hx). reflexivity.
Qed.

(*
The view and the computed reading
---------------------------------
*)

Definition rmode_of (md : pmode) : rmode :=
  match md with PMNormal => RNormal | PMRegion _ _ _ e _ => RInert e end.

Local Lemma pv_add_live : forall x v,
  pv_live (pv_add x v) = pv_live v /\ pv_mode (pv_add x v) = pv_mode v.
Proof. intros x [[|[p k c|d c] rest] out md]; split; reflexivity. Qed.

Local Lemma pclose_found : forall k stk p below,
  pick k (map fitem stk) = PFound p below ->
  exists content rest, pclose_go k [] stk = Some (content, rest) /\ map fitem rest = below.
Proof.
  intros k stk p below P.
  destruct (pick_split k stk p below P) as (above & c & rest & -> & F & Hb).
  destruct (pclose_split k above p c rest [] F) as [content Hc].
  exists content, rest. split; [exact Hc|exact Hb].
Qed.

Local Lemma pstep_live : forall ts n t v s,
  pv_live v = rs_live s -> rmode_of (pv_mode v) = rs_mode s ->
  pv_live (pstep ts n t v) = rs_live (rstep ts n t s)
  /\ rmode_of (pv_mode (pstep ts n t v)) = rs_mode (rstep ts n t s).
Proof.
  intros ts n t v [lv m os md] Hl Hm. cbn [rs_live rs_mode] in *.
  unfold pstep, rstep. cbn [rs_live rs_pairs rs_os rs_mode].
  destruct (pv_mode v) as [|b kids d e txt] eqn:Ev; cbn [rmode_of] in Hm; subst md.
  2: { destruct e as [e|].
       - destruct (Nat.eqb n e).
         + destruct (pv_add_live (region_node b (map mk kids) txt) (pv_setmode PMNormal v))
             as [E1 E2].
           rewrite E1, E2. split; [exact Hl|reflexivity].
         + cbn. split; [exact Hl|reflexivity].
       - cbn. split; [exact Hl|reflexivity]. }
  assert (Add : forall x, pv_live (pv_add x v) = lv /\ rmode_of (pv_mode (pv_add x v)) = RNormal).
  { intros x. destruct (pv_add_live x v) as [E1 E2]. rewrite E1, E2, Ev. split; [exact Hl|reflexivity]. }
  assert (Open : forall i k op txt,
            pv_live (popen i k op txt v) = rs_live (ropen i k op (RState lv m os RNormal))
            /\ rmode_of (pv_mode (popen i k op txt v))
               = rs_mode (ropen i k op (RState lv m os RNormal))).
  { intros i k [|] txt; unfold popen, ropen; cbn [pv_live pv_stk pv_mode rs_live rs_mode map fitem].
    - unfold pv_live in Hl. rewrite Hl, Ev. split; reflexivity.
    - apply Add. }
  destruct t as [c| |k mr op cl| |b]; try apply Add; [| |].
  - rewrite Hl. destruct (if cl then pick (KDelim k mr) lv else PNone) as [p below| |] eqn:P;
      [|apply Add|apply Open].
    destruct (Nat.ltb (S p) n); [|apply Open].
    destruct cl; [|discriminate].
    unfold pv_live in Hl. rewrite <- Hl in P.
    destruct (pclose_found _ _ _ _ P) as (content & rest & Hc & Hb).
    rewrite Hc. destruct (pv_add_live (dnode k (map mk (List.rev content)))
                            (PView rest (pv_out v) PMNormal)) as [E1 E2].
    rewrite E1, E2. split; [exact Hb|reflexivity].
  - apply Open.
  - rewrite Hl. destruct (pick KBracket lv) as [p below| |] eqn:P;
      [|apply Add|apply Add].
    unfold pv_live in Hl. rewrite <- Hl in P.
    destruct (pclose_found _ _ _ _ P) as (content & rest & Hc & Hb).
    rewrite Hc. destruct (region_end ts n b) as [e|]; [|destruct b];
      cbn [pv_live pv_stk pv_mode rmode_of map fitem]; split; try reflexivity;
      rewrite ?Hb; reflexivity.
Qed.

(*
One token
---------

The view and `tree_go` move together, given what the whole line's
matching says about the token: whether it closes, whether it will be
closed as an opener, and that the openers a closer passes over are
never closed. *)

Definition closes_here (m : matching) (n p : nat) (lv : list litem) : Prop :=
  is_closer m n = true /\ is_opener m p = true
  /\ (forall q k', In (LOpen q k') lv -> p < q -> is_opener m q = false).

Definition step_facts (m : matching) (n : nat) (t : token) (lv : list litem)
  (md : pmode) : Prop :=
  match md with
  | PMRegion _ _ _ _ _ => True
  | PMNormal =>
      match t with
      | TDelim k mr op cl =>
          match (if cl then pick (KDelim k mr) lv else PNone) with
          | PFound p _ =>
              if Nat.ltb (S p) n then is_opener m n = false /\ closes_here m n p lv
              else is_closer m n = false /\ (op = false -> is_opener m n = false)
          | PBarred => is_closer m n = false /\ is_opener m n = false
          | PNone => is_closer m n = false /\ (op = false -> is_opener m n = false)
          end
      | TClose _ =>
          match pick KBracket lv with
          | PFound p _ => closes_here m n p lv
          | _ => is_closer m n = false
          end
      | _ => True
      end
  end.

Definition frames_normal (v : pview) : Prop :=
  Forall (fun f => normal (fcontent f)) (pv_stk v).

Local Lemma dnode_nonstr : forall k l s, dnode k l <> Str s.
Proof. intros [] l s E; discriminate E. Qed.

Local Lemma region_node_nonstr : forall b l t s, region_node b l t <> Str s.
Proof. intros [] l t s E; discriminate E. Qed.

Local Lemma vembed_add : forall real x v,
  vembed real (pv_add x v)
  = (fst (tfr (xinner (xsnoc x) (collapse real (pv_stk v) (pv_out v)))),
     snd (tfr (xinner (xsnoc x) (collapse real (pv_stk v) (pv_out v)))),
     membed (pv_mode v)).
Proof.
  intros real x v. unfold vembed, tembed. rewrite collapse_add.
  rewrite (proj2 (pv_add_live x v)). reflexivity.
Qed.

Local Lemma ldesc_above : forall above f rest,
  ldesc (map fitem (above ++ f :: rest)) ->
  forall g, In g above -> lpos (fitem f) < lpos (fitem g).
Proof.
  induction above as [|h above IH]; intros f rest D g Hg; [destruct Hg|].
  cbn [app map] in D. apply StronglySorted_inv in D as [D F].
  destruct Hg as [<-|Hg]; [|exact (IH f rest D g Hg)].
  rewrite Forall_forall in F. apply (F (fitem f)).
  apply in_map. apply in_or_app. right. left. reflexivity.
Qed.

(* The frames a found closer passes over are never closed. *)
Local Lemma passed_unreal : forall m k p c rest above v,
  pv_stk v = (above ++ PF p k c :: rest)%list ->
  ldesc (pv_live v) -> Forall (passes k) above ->
  (forall q k', In (LOpen q k') (pv_live v) -> p < q -> is_opener m q = false) ->
  Forall (fun f => passes k f
                   /\ match f with PF q _ _ => is_opener m q = false | PB _ _ => True end)
    above.
Proof.
  intros m k p c rest above v E D F Habove.
  unfold pv_live in D, Habove. rewrite E in D, Habove.
  rewrite Forall_forall in F |- *. intros g Hg. split; [exact (F g Hg)|].
  destruct g as [q k' c'|d c']; [|exact Logic.I].
  apply (Habove q k').
  - apply in_map_iff. exists (PF q k' c'). split; [reflexivity|].
    apply in_or_app. left. exact Hg.
  - exact (ldesc_above above (PF p k c) rest D _ Hg).
Qed.

Local Lemma lit_normal : forall k, normal [lit k].
Proof. intros k. exact Logic.I. Qed.

Local Lemma pclose_go_normal : forall k stk pend content rest,
  Forall (fun f => normal (fcontent f)) stk -> normal pend ->
  pclose_go k pend stk = Some (content, rest) ->
  normal content /\ Forall (fun f => normal (fcontent f)) rest.
Proof.
  intros k stk. induction stk as [|[q k' c|d c] stk IH]; intros pend content rest N Hp H;
    [discriminate|cbn [pclose_go] in H|discriminate].
  apply Forall_cons_iff in N as [Nc N]. cbn [fcontent] in Nc.
  destruct (key_eq k k').
  - injection H as <- <-. split; [apply normal_xapp; assumption|exact N].
  - apply (IH (xapp (xapp pend c) [lit k']) _ _ N); [|exact H].
    apply normal_xapp; [apply normal_xapp; assumption|apply lit_normal].
Qed.

Local Lemma pstep_tstep : forall ts m n t v,
  ldesc (pv_live v) -> frames_normal v ->
  step_facts m n t (pv_live v) (pv_mode v) ->
  tstep ts m n t (vembed (is_opener m) v) = vembed (is_opener m) (pstep ts n t v).
Proof.
  intros ts m n t [stk out md] D N Hf. set (real := is_opener m).
  unfold pv_live in D, Hf. cbn [pv_stk pv_out pv_mode] in D, N, Hf.
  unfold vembed at 1, tembed. cbn [pv_stk pv_out pv_mode].
  destruct (collapse real stk out) as [fs0 top0] eqn:Ec. cbn [fst snd].
  destruct md as [|b kids d e txt].
  2: { cbn [membed tstep pstep pv_mode].
       destruct (match e with Some e' => Nat.eqb n e' | None => false end).
       - rewrite vembed_add. cbn [pv_stk pv_out pv_setmode pv_mode membed]. rewrite Ec.
         rewrite (xinner_ext (xsnoc _) (cons (region_node b (map mk kids) txt)))
           by (intros l; apply xsnoc_nonstr, region_node_nonstr).
         destruct fs0 as [|[k c] fs]; reflexivity.
       - unfold vembed, tembed. cbn [pv_stk pv_out pv_setmode pv_mode membed]. rewrite Ec.
         reflexivity. }
  cbn [membed] in *.
  set (v := {| pv_stk := stk; pv_out := out; pv_mode := PMNormal |}).
  assert (Emb : forall x, vembed real (pv_add x v)
                = (fst (tfr (xinner (xsnoc x) (fs0, top0))),
                   snd (tfr (xinner (xsnoc x) (fs0, top0))), TMNormal)).
  { intros x. rewrite vembed_add. unfold v. cbn [pv_stk pv_out pv_mode membed].
    fold real. rewrite Ec. reflexivity. }
  assert (Str_ : forall s',
            tnormal (temit_str s' (map (fun f => (fst f, map mk (snd f))) fs0) (map mk top0))
            = vembed real (pv_add (Str s') v)).
  { intros s'. rewrite Emb. unfold tnormal.
    change (map (fun f : tkind * list inline => (fst f, map mk (snd f))) fs0)
      with (fst (tfr (fs0, top0))).
    change (map mk top0) with (snd (tfr (fs0, top0))).
    rewrite temit_str_embed. reflexivity. }
  (* a closer that pairs with `p`, and the frame it closes *)
  assert (Close : forall K p below,
            pick K (map fitem stk) = PFound p below ->
            closes_here m n p (map fitem stk) ->
            exists content rest,
              pclose_go K [] stk = Some (content, rest)
              /\ fs0 = (tkind_of K, content) :: fst (collapse real rest out)
              /\ top0 = snd (collapse real rest out)
              /\ normal content).
  { intros K p below P (Hcn & Hop & Habove).
    destruct (pick_split K stk p below P) as (above & c & rest & E & F & Hb).
    pose proof (passed_unreal m K p c rest above v E D F Habove) as Fr.
    rewrite E in Ec.
    destruct (close_collapse real K above p c rest out [] Fr Hop) as (content & Hpc & Hcol).
    rewrite Hcol in Ec. injection Ec as <- <-.
    exists content, rest. rewrite E. split; [exact Hpc|]. split; [reflexivity|].
    split; [reflexivity|].
    unfold frames_normal in N. cbn [pv_stk] in N. rewrite E in N.
    exact (proj1 (pclose_go_normal K _ [] content rest N Logic.I Hpc)). }
  destruct t as [c| |k mr op cl| |b].
  - unfold v. cbn [tstep pstep pv_mode]. fold v. apply Str_.
  - unfold v. cbn [tstep pstep pv_mode]. fold v. rewrite Emb.
    rewrite (xinner_ext (xsnoc _) (cons SoftBreak))
      by (intros l; apply xsnoc_nonstr; discriminate).
    destruct fs0 as [|[k c] fs]; reflexivity.
  - (* a delimiter *)
    set (K := KDelim k mr).
    assert (Popen : (op = false -> is_opener m n = false) -> is_closer m n = false ->
              tstep ts m n (TDelim k mr op cl)
                (map (fun f => (fst f, map mk (snd f))) fs0, map mk top0, TMNormal)
              = vembed real (popen n K op (tok_text (TDelim k mr op cl)) v)).
    { intros Ho Hc. cbn [tstep]. unfold popen. destruct op.
      - unfold vembed, tembed, v. cbn [pv_stk pv_out pv_mode membed collapse].
        fold real. rewrite Ec. destruct (real n) eqn:Hr; [reflexivity|].
        cbn [xapp]. rewrite Hc.
        change (map (fun f : tkind * list inline => (fst f, map mk (snd f))) fs0)
          with (fst (tfr (fs0, top0))).
        change (map mk top0) with (snd (tfr (fs0, top0))).
        rewrite temit_str_embed.
        assert (E : tok_text (TDelim k mr true cl) = tok_text (TDelim k mr true false))
          by (destruct mr; reflexivity).
        unfold lit, K. rewrite E. reflexivity.
      - rewrite (Ho eq_refl), Hc. apply Str_. }
    cbn [step_facts] in Hf. unfold v. cbn [pstep pv_mode]. fold v. unfold pv_live. cbn [pv_stk pv_out].
    fold K in Hf |- *. change (pv_stk v) with stk. change (pv_out v) with out.
    destruct (if cl then pick K (map fitem stk) else PNone) as [p below| |] eqn:P.
    3: { destruct Hf as [Hc Ho]. apply Popen; assumption. }
    2: { destruct Hf as [Hc Ho]. cbn [tstep]. rewrite Ho, Hc. apply Str_. }
    destruct (Nat.ltb (S p) n); [|destruct Hf as [Hc Ho]; apply Popen; assumption].
    destruct Hf as (Hon & Hcl).
    destruct cl; [|discriminate].
    destruct (Close K p below P Hcl) as (content & rest & Hpc & -> & -> & _).
    pose proof Hcl as (Hcn & _).
    rewrite Hpc. cbn [tstep]. rewrite Hon, Hcn. cbn [map fst snd tkind_of K].
    rewrite vembed_add. cbn [pv_stk pv_out pv_mode membed].
    rewrite (xinner_ext (xsnoc _) (cons (dnode k (map mk (List.rev content)))))
      by (intros l; apply xsnoc_nonstr, dnode_nonstr).
    unfold tnormal. rewrite map_rev.
    destruct (collapse real rest out) as [[|[k1 c1] fs1] top1]; reflexivity.
  - (* a `[` *)
    unfold v. cbn [tstep pstep pv_mode]. unfold popen, vembed, tembed.
    cbn [pv_stk pv_out pv_mode membed collapse]. fold real. rewrite Ec.
    cbn [xapp]. destruct (real n); [reflexivity|].
    change (map (fun f : tkind * list inline => (fst f, map mk (snd f))) fs0)
      with (fst (tfr (fs0, top0))).
    change (map mk top0) with (snd (tfr (fs0, top0))).
    rewrite temit_str_embed. reflexivity.
  - (* a `]` *)
    cbn [step_facts] in Hf. unfold v. cbn [pstep pv_mode]. fold v. unfold pv_live. cbn [pv_stk pv_out].
    change (pv_stk v) with stk. change (pv_out v) with out.
    destruct (pick KBracket (map fitem stk)) as [p below| |] eqn:P.
    2,3: cbn [tstep]; rewrite Hf; apply Str_.
    destruct (Close KBracket p below P Hf) as (content & rest & Hpc & -> & -> & Hn).
    pose proof Hf as (Hcn & _).
    rewrite Hpc. cbn [tstep]. rewrite Hcn. cbn [map fst snd tkind_of].
    destruct (region_end ts n b) as [e|].
    + unfold vembed, tembed. cbn [pv_stk pv_out pv_mode membed]. rewrite map_rev. reflexivity.
    + destruct b.
      * unfold vembed, tembed. cbn [pv_stk pv_out pv_mode membed collapse].
        unfold tnormal.
        change (map (fun f : tkind * list inline => (fst f, map mk (snd f)))
                  (fst (collapse real rest out)))
          with (fst (tfr (collapse real rest out))).
        change (map mk (snd (collapse real rest out)))
          with (snd (tfr (collapse real rest out))).
        rewrite <- map_rev.
        replace (mk (Str (one lbrack)) :: map mk (List.rev content) ++ [mk (Str (one rbrack))])%list
          with (map mk (Str (one lbrack) :: List.rev content ++ [Str (one rbrack)]))%list
          by (cbn [map]; rewrite map_app; reflexivity).
        rewrite temit_all_embed.
        assert (X : forall acc,
                  fold_left (fun a x => xsnoc x a)
                    (Str (one lbrack) :: List.rev content ++ [Str (one rbrack)])%list acc
                  = xapp (xsnoc (Str (one rbrack)) content) (xsnoc (Str (one lbrack)) acc)).
        { intros acc. cbn [fold_left]. rewrite fold_left_app. cbn [fold_left].
          rewrite (fold_xsnoc content _ Hn), xapp_xsnoc. reflexivity. }
        rewrite (xinner_ext _ _ _ X). reflexivity.
      * unfold vembed, tembed. cbn [pv_stk pv_out pv_mode membed]. rewrite map_rev.
        reflexivity.
Qed.

Local Lemma pv_add_normal : forall x v, frames_normal v -> frames_normal (pv_add x v).
Proof.
  intros x [[|f rest] out md] N; [constructor|].
  unfold frames_normal in *. cbn [pv_add pv_stk] in *.
  apply Forall_cons_iff in N as [Nf N]. constructor; [|exact N].
  destruct f; cbn [fset fcontent] in *; apply normal_xsnoc, Nf.
Qed.

Local Lemma pstep_normal : forall ts n t v, frames_normal v -> frames_normal (pstep ts n t v).
Proof.
  intros ts n t [stk out md] N. unfold pstep. cbn [pv_mode].
  destruct md as [|b kids d e txt].
  2: { destruct (match e with Some e' => Nat.eqb n e' | None => false end);
       [apply pv_add_normal; exact N|exact N]. }
  assert (Open : forall i k op txt, frames_normal (popen i k op txt {| pv_stk := stk; pv_out := out; pv_mode := PMNormal |})).
  { intros i k [|] txt; [constructor; [exact Logic.I|exact N]|apply pv_add_normal, N]. }
  destruct t as [c| |k mr op cl| |b]; try (apply pv_add_normal; exact N); [| |].
  - unfold pv_live. cbn [pv_stk pv_out].
    destruct (if cl then pick (KDelim k mr) (map fitem stk) else PNone) as [p below| |];
      [|apply pv_add_normal, N|apply Open].
    destruct (Nat.ltb (S p) n); [|apply Open].
    destruct (pclose_go (KDelim k mr) [] stk) as [[content rest]|] eqn:Hc; [|exact N].
    apply pv_add_normal. exact (proj2 (pclose_go_normal _ stk [] content rest N Logic.I Hc)).
  - apply Open.
  - unfold pv_live. cbn [pv_stk pv_out].
    destruct (pick KBracket (map fitem stk));
      destruct (pclose_go KBracket [] stk) as [[content rest]|] eqn:Hc;
      try (apply pv_add_normal; exact N).
    destruct (pclose_go_normal _ stk [] content rest N Logic.I Hc) as [Nc Nr].
    destruct (region_end ts n b); [exact Nr|].
    destruct b; [|exact Nr]. constructor; [apply normal_xsnoc, Nc|exact Nr].
Qed.

(* Nor an empty `Str`: every text the view adds is a token's, and a
   token is never empty. *)
Definition clean (l : list inline) : Prop := Forall (fun x => x <> Str "") l.

Definition frames_clean (v : pview) : Prop :=
  Forall (fun f => clean (fcontent f)) (pv_stk v).

Local Lemma clean_xsnoc : forall x l, x <> Str "" -> clean l -> clean (xsnoc x l).
Proof.
  intros x l Hx Hl. destruct l as [|y l]; [constructor; [exact Hx|constructor]|].
  destruct (str_view x) as [[s' ->]|Hx'].
  - destruct (str_view y) as [[t ->]|Hy].
    + cbn. apply Forall_cons_iff in Hl as [Ht Hl]. constructor; [|exact Hl].
      intros E. injection E as E. destruct t; [contradiction|discriminate].
    + rewrite (xsnoc_str_nonstr s' y l Hy). constructor; [exact Hx|exact Hl].
  - rewrite (xsnoc_nonstr x _ Hx'). constructor; [exact Hx|exact Hl].
Qed.

Local Lemma clean_xapp : forall a b, clean a -> clean b -> clean (xapp a b).
Proof.
  induction a as [|x a IH]; intros b Ha Hb; [exact Hb|].
  apply Forall_cons_iff in Ha as [Hx Ha].
  destruct a as [|y r]; [apply clean_xsnoc; assumption|].
  change (xapp (x :: y :: r) b) with (x :: xapp (y :: r) b).
  constructor; [exact Hx|exact (IH b Ha Hb)].
Qed.

Local Lemma lit_clean : forall k, clean [lit k].
Proof.
  intros [k mr|]; constructor; [|constructor| |constructor];
    [destruct mr; cbn; unfold tok_text; pose proof (dtoken_nonempty k) as H;
     intros E; injection E as E; rewrite ?E in H;
     [destruct (dtoken k); discriminate|]; destruct (dtoken k); discriminate|discriminate].
Qed.

Local Lemma pclose_go_clean : forall k stk pend content rest,
  Forall (fun f => clean (fcontent f)) stk -> clean pend ->
  pclose_go k pend stk = Some (content, rest) ->
  clean content /\ Forall (fun f => clean (fcontent f)) rest.
Proof.
  intros k stk. induction stk as [|[q k' c|d c] stk IH]; intros pend content rest N Hp H;
    [discriminate|cbn [pclose_go] in H|discriminate].
  apply Forall_cons_iff in N as [Nc N]. cbn [fcontent] in Nc.
  destruct (key_eq k k').
  - injection H as <- <-. split; [apply clean_xapp; assumption|exact N].
  - apply (IH (xapp (xapp pend c) [lit k']) _ _ N); [|exact H].
    apply clean_xapp; [apply clean_xapp; assumption|apply lit_clean].
Qed.

Local Lemma pv_add_clean : forall x v, x <> Str "" -> frames_clean v -> frames_clean (pv_add x v).
Proof.
  intros x [[|f rest] out md] Hx N; [constructor|].
  unfold frames_clean in *. cbn [pv_add pv_stk] in *.
  apply Forall_cons_iff in N as [Nf N]. constructor; [|exact N].
  destruct f; cbn [fset fcontent] in *; apply clean_xsnoc; assumption.
Qed.

Local Lemma tok_text_ne : forall t, tok_text t <> "".
Proof.
  intros [c| |k [|] [|] cl| |b]; cbn; try discriminate;
    pose proof (dtoken_nonempty k) as H; destruct (dtoken k); discriminate.
Qed.

Local Lemma pstep_clean : forall ts n t v, frames_clean v -> frames_clean (pstep ts n t v).
Proof.
  intros ts n t [stk out md] N.
  assert (Str_ : forall s', s' <> "" -> Str s' <> Str "") by (intros s' H E; injection E as E; contradiction).
  unfold pstep. cbn [pv_mode].
  destruct md as [|b kids d e txt].
  2: { destruct (match e with Some e' => Nat.eqb n e' | None => false end);
       [apply pv_add_clean; [destruct b; discriminate|exact N]|exact N]. }
  assert (Open : forall i k op txt, txt <> "" ->
                 frames_clean (popen i k op txt {| pv_stk := stk; pv_out := out; pv_mode := PMNormal |})).
  { intros i k [|] txt Ht; [constructor; [constructor|exact N]|apply pv_add_clean; [apply Str_, Ht|exact N]]. }
  destruct t as [c| |k mr op cl| |b].
  - apply pv_add_clean; [discriminate|exact N].
  - apply pv_add_clean; [discriminate|exact N].
  - unfold pv_live. cbn [pv_stk pv_out].
    destruct (if cl then pick (KDelim k mr) (map fitem stk) else PNone) as [p below| |];
      [|apply pv_add_clean; [apply Str_, tok_text_ne|exact N]|apply Open, tok_text_ne].
    destruct (Nat.ltb (S p) n); [|apply Open, tok_text_ne].
    destruct (pclose_go (KDelim k mr) [] stk) as [[content rest]|] eqn:Hc; [|exact N].
    apply pv_add_clean; [apply dnode_nonstr|].
    exact (proj2 (pclose_go_clean _ stk [] content rest N (Forall_nil _) Hc)).
  - apply Open. discriminate.
  - unfold pv_live. cbn [pv_stk pv_out].
    destruct (pick KBracket (map fitem stk));
      destruct (pclose_go KBracket [] stk) as [[content rest]|] eqn:Hc;
      try (apply pv_add_clean; [apply Str_, tok_text_ne|exact N]).
    destruct (pclose_go_clean _ stk [] content rest N (Forall_nil _) Hc) as [Nc Nr].
    destruct (region_end ts n b); [exact Nr|].
    destruct b; [|exact Nr]. constructor; [apply clean_xsnoc; [discriminate|exact Nc]|exact Nr].
Qed.

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

(* A step adds at most a pair closing at the token and the token as an
   opener. *)
Local Lemma rstep_grows : forall ts i t s,
  (rs_pairs (rstep ts i t s) = rs_pairs s
   \/ exists p, rs_pairs (rstep ts i t s) = (p, i) :: rs_pairs s)
  /\ (rs_os (rstep ts i t s) = rs_os s \/ rs_os (rstep ts i t s) = i :: rs_os s).
Proof.
  intros ts i t [lv m os md]. unfold rstep. cbn [rs_mode rs_live rs_pairs rs_os].
  assert (Ro : forall k op s',
            rs_pairs s' = m -> rs_os s' = os ->
            (rs_pairs (ropen i k op s') = m \/ exists p, rs_pairs (ropen i k op s') = (p, i) :: m)
            /\ (rs_os (ropen i k op s') = os \/ rs_os (ropen i k op s') = i :: os)).
  { intros k [|] s' E1 E2; unfold ropen; cbn [rs_pairs rs_os]; rewrite E1, E2;
      split; [left|right|left|left]; reflexivity. }
  destruct md as [|[e|]].
  - destruct t as [c| |k mr op cl| |b]; try (split; left; reflexivity).
    + destruct (if cl then pick (KDelim k mr) lv else PNone) as [p below| |];
        [destruct (Nat.ltb (S p) i)| |];
        try (apply Ro; reflexivity); try (split; left; reflexivity).
      cbn. split; [right; exists p; reflexivity|left; reflexivity].
    + apply Ro; reflexivity.
    + destruct (pick KBracket lv) as [p below| |]; try (split; left; reflexivity).
      destruct (region_end ts i b); [|destruct b]; cbn;
        (split; [right; exists p; reflexivity|left; reflexivity]).
  - destruct (Nat.eqb i e); split; left; reflexivity.
  - split; left; reflexivity.
Qed.

Local Lemma rrun_grows : forall ts i rest s,
  (forall a b, In (a, b) (rs_pairs (rrun ts i rest s)) -> b < i -> In (a, b) (rs_pairs s))
  /\ (forall a b, In (a, b) (rs_pairs s) -> In (a, b) (rs_pairs (rrun ts i rest s)))
  /\ (forall q, In q (rs_os (rrun ts i rest s)) -> q < i -> In q (rs_os s))
  /\ (forall q, In q (rs_os s) -> In q (rs_os (rrun ts i rest s))).
Proof.
  intros ts i rest. revert i. induction rest as [|t rest IH]; intros i s; cbn [rrun].
  - split; [auto|]. split; [auto|]. split; auto.
  - destruct (IH (S i) (rstep ts i t s)) as (A1 & A2 & A3 & A4).
    destruct (rstep_grows ts i t s) as [Gp Go].
    split; [|split; [|split]].
    + intros a b H Hb. specialize (A1 a b H ltac:(lia)).
      destruct Gp as [Ep|[p Ep]]; rewrite Ep in A1; [exact A1|].
      destruct A1 as [E|A1]; [injection E as _ ->; lia|exact A1].
    + intros a b H. apply A2.
      destruct Gp as [Ep|[p Ep]]; rewrite Ep; [exact H|right; exact H].
    + intros q H Hq. specialize (A3 q H ltac:(lia)).
      destruct Go as [Eo|Eo]; rewrite Eo in A3; [exact A3|].
      destruct A3 as [->|A3]; [lia|exact A3].
    + intros q H. apply A4.
      destruct Go as [Eo|Eo]; rewrite Eo; [exact H|right; exact H].
Qed.

(*
The whole paragraph
-------------------

The facts `step_facts` asks for hold of the reading `ref_read` computes,
at every token, because it is valid and it grows one token at a time:
the pairs that close by `n` and the openers by `n` are the ones the
first steps made. *)

Local Lemma facts_hold : forall ts n t s,
  nth_error ts n = Some t -> rinv ts n s -> rs_mode s = RNormal ->
  (forall a b, b <= n -> In (a, b) (fst (ref_read ts)) <-> In (a, b) (rs_pairs (rstep ts n t s))) ->
  (forall q, q <= n -> In q (snd (ref_read ts)) <-> In q (rs_os (rstep ts n t s))) ->
  step_facts (fst (ref_read ts)) n t (rs_live s) PMNormal.
Proof.
  intros ts n t s Hn I Hmd Hp Ho.
  destruct (ref_read ts) as [m os] eqn:Er. cbn [fst snd] in *.
  pose proof (ref_read_valid ts) as V. rewrite Er in V. destruct V as (P & U & O).
  destruct (rstep_grows ts n t s) as [Gp Go].
  (* a token never in `os` opens nothing *)
  assert (NoOpen : forall q, ~ In q os -> is_opener m q = false).
  { intros q Hq. destruct (is_opener m q) eqn:E; [|reflexivity]. exfalso.
    apply is_opener_iff in E as [j Hj]. destruct (P q j Hj) as (_ & _ & _ & [((Hin & _) & _) _] & _).
    exact (Hq Hin). }
  assert (NoClose : rs_pairs (rstep ts n t s) = rs_pairs s -> is_closer m n = false).
  { intros E. destruct (is_closer m n) eqn:C; [|reflexivity]. exfalso.
    apply is_closer_iff in C as [i Hi]. apply (Hp i n (le_n n)) in Hi. rewrite E in Hi.
    specialize (ri_bound_pairs ts n s I i n Hi). lia. }
  assert (NotOs : rs_os (rstep ts n t s) = rs_os s -> ~ In n os).
  { intros E H. apply (Ho n (le_n n)) in H. rewrite E in H.
    specialize (ri_bound_os ts n s I n H). lia. }
  assert (Above : forall p, In (p, n) m ->
            forall q k', In (LOpen q k') (rs_live s) -> p < q -> is_opener m q = false).
  { intros p Hpn q k' Hq Hpq. destruct (is_opener m q) eqn:E; [|reflexivity]. exfalso.
    apply is_opener_iff in E as [j Hj].
    apply (ri_cand ts n s I) in Hq as (_ & Hqn & _ & _ & Hd).
    destruct (P q j Hj) as (kq & Hkq & _ & Cq & _).
    pose proof Cq as [((_ & _ & _ & _ & Hdq) & _) _].
    destruct (lt_eq_lt_dec j n) as [[Hjn| ->]|Hjn].
    - apply Hd. left. exists j. split; [exact Hjn|].
      apply (Hp q j ltac:(lia)) in Hj.
      destruct Gp as [Ep|[p' Ep]]; rewrite Ep in Hj; [exact Hj|].
      destruct Hj as [E'|Hj]; [injection E' as _ E'; lia|exact Hj].
    - destruct (P p n Hpn) as (kp & Hkp & _ & Cp & _).
      rewrite (close_key_fun ts n kq kp Hkq Hkp) in Cq.
      pose proof (closest_live_fun ts m os n kp q p Cq Cp). lia.
    - apply Hdq. right. exists p, n. split; [exact Hjn|]. split; [exact Hpn|lia]. }
  (* `n` closes in `m` exactly when the step paired it *)
  assert (Pair : forall p, rs_pairs (rstep ts n t s) = (p, n) :: rs_pairs s ->
            is_closer m n = true /\ is_opener m p = true /\ In (p, n) m
            /\ is_opener m n = false).
  { intros p E. assert (Hpn : In (p, n) m) by (apply (Hp p n (le_n n)); rewrite E; left; reflexivity).
    split; [apply is_closer_iff; exists p; exact Hpn|].
    split; [apply is_opener_iff; exists n; exact Hpn|]. split; [exact Hpn|].
    apply NoOpen. intros Hin. apply O in Hin as (_ & _ & Hc & _). apply Hc. exists p. exact Hpn. }
  assert (Paired : forall p, (forall a b, b <= n -> In (a, b) m <-> In (a, b) ((p, n) :: rs_pairs s)) ->
            closes_here m n p (rs_live s) /\ is_opener m n = false).
  { intros p H. assert (Hpn : In (p, n) m) by (apply (H p n (le_n n)); left; reflexivity).
    split; [split; [apply is_closer_iff; exists p; exact Hpn|]; split|].
    - apply is_opener_iff. exists n. exact Hpn.
    - exact (Above p Hpn).
    - apply NoOpen. intros Hin. apply O in Hin as (_ & _ & Hc & _). apply Hc.
      exists p. exact Hpn. }
  assert (Unpaired : (forall a b, b <= n -> In (a, b) m <-> In (a, b) (rs_pairs s)) ->
            is_closer m n = false).
  { intros H. destruct (is_closer m n) eqn:C; [|reflexivity]. exfalso.
    apply is_closer_iff in C as [i Hi]. apply (H i n (le_n n)) in Hi.
    specialize (ri_bound_pairs ts n s I i n Hi). lia. }
  assert (Unopened : (forall q, q <= n -> In q os <-> In q (rs_os s)) -> is_opener m n = false).
  { intros H. apply NoOpen. intros Hin. apply (H n (le_n n)) in Hin.
    specialize (ri_bound_os ts n s I n Hin). lia. }
  unfold rstep in Hp, Ho. rewrite Hmd in Hp, Ho. unfold step_facts.
  destruct s as [lv pairs os' md']. cbn [rs_live rs_pairs rs_os rs_mode] in *.
  destruct t as [c| |k mr op cl| |b]; try exact Logic.I.
  - remember (if cl then pick (KDelim k mr) lv else PNone) as r eqn:P'.
    destruct r as [p below| |].
    + remember (Nat.ltb (S p) n) as l eqn:L. destruct l.
      * destruct (Paired p Hp) as [A B]. split; assumption.
      * unfold ropen in Hp, Ho. split; [apply Unpaired; destruct op; exact Hp|].
        intros ->. apply Unopened. exact Ho.
    + split; [exact (Unpaired Hp)|exact (Unopened Ho)].
    + unfold ropen in Hp, Ho. split; [apply Unpaired; destruct op; exact Hp|].
      intros ->. apply Unopened. exact Ho.
  - remember (pick KBracket lv) as r eqn:P'. destruct r as [p below| |].
    2,3: exact (Unpaired Hp).
    remember (region_end ts n b) as r' eqn:R. destruct r' as [e|]; [|destruct b];
      exact (proj1 (Paired p Hp)).
Qed.

Local Lemma prun_tree : forall ts suf pre s v,
  ts = (pre ++ suf)%list -> rinv ts (length pre) s ->
  ref_read ts = (rs_pairs (rrun ts (length pre) suf s), rs_os (rrun ts (length pre) suf s)) ->
  pv_live v = rs_live s -> rmode_of (pv_mode v) = rs_mode s -> frames_normal v ->
  tree_go ts (fst (ref_read ts)) (length pre) suf
    (vembed (is_opener (fst (ref_read ts))) v)
  = vembed (is_opener (fst (ref_read ts))) (prun ts (length pre) suf v).
Proof.
  intros ts suf. induction suf as [|t rest IH]; intros pre s v E I Hr Hl Hm N;
    cbn [tree_go prun]; [reflexivity|].
  set (n := length pre) in *.
  assert (Hn : nth_error ts n = Some t).
  { rewrite E, nth_error_app2 by lia. unfold n. rewrite Nat.sub_diag. reflexivity. }
  cbn [rrun] in Hr.
  destruct (rrun_grows ts (S n) rest (rstep ts n t s)) as (A1 & A2 & A3 & A4).
  assert (Hf : step_facts (fst (ref_read ts)) n t (pv_live v) (pv_mode v)).
  { destruct (pv_mode v) as [|b kids d e txt] eqn:Ev; [|exact Logic.I].
    cbn [rmode_of] in Hm. rewrite Hl.
    apply (facts_hold ts n t s Hn I (eq_sym Hm)).
    - intros a b Hb. rewrite Hr. cbn [fst]. split; [intros H; apply A1; [exact H|lia]|apply A2].
    - intros q Hq. rewrite Hr. cbn [snd]. split; [intros H; apply A3; [exact H|lia]|apply A4]. }
  rewrite (pstep_tstep ts _ n t v); [|rewrite Hl; exact (ri_desc ts n s I)|exact N|exact Hf].
  specialize (IH (pre ++ [t])%list (rstep ts n t s) (pstep ts n t v)).
  rewrite length_app in IH. cbn [length] in IH. rewrite Nat.add_1_r in IH.
  apply IH.
  - rewrite E, <- app_assoc. reflexivity.
  - apply rinv_step; [exact Hn|exact I].
  - exact Hr.
  - exact (proj1 (pstep_live ts n t v s Hl Hm)).
  - exact (proj2 (pstep_live ts n t v s Hl Hm)).
  - apply pstep_normal, N.
Qed.

Local Lemma pv_add_all_collapse : forall real l v,
  collapse real (pv_stk (pv_add_all l v)) (pv_out (pv_add_all l v))
  = xinner (fun acc => fold_left (fun a x => xsnoc x a) l acc)
      (collapse real (pv_stk v) (pv_out v))
  /\ map fitem (pv_stk (pv_add_all l v)) = map fitem (pv_stk v).
Proof.
  intros real l. induction l as [|x l IH]; intros v.
  - cbn [pv_add_all fold_left]. split; [|reflexivity].
    destruct (collapse real (pv_stk v) (pv_out v)) as [[|[k c] fs] top]; reflexivity.
  - cbn [pv_add_all fold_left]. destruct (IH (pv_add x v)) as [E1 E2].
    rewrite E1, collapse_add, xinner_comp, E2. split; [reflexivity|].
    exact (proj1 (pv_add_live x v)).
Qed.

Theorem tree_of_prun : forall ts,
  tree_of ts (fst (ref_read ts)) = map mk (List.rev (pflatten (prun ts 0 ts pv0))).
Proof.
  intros ts. set (m := fst (ref_read ts)). set (real := is_opener m).
  assert (Hr : ref_read ts = (rs_pairs (rrun ts 0 ts rstart), rs_os (rrun ts 0 ts rstart)))
    by reflexivity.
  pose proof (prun_tree ts ts [] rstart pv0 eq_refl (rinv_start ts) Hr eq_refl eq_refl
                (Forall_nil _)) as E.
  cbn [length] in E. fold m real in E.
  unfold tree_of.
  change (([], [], TMNormal) : tstate) with (vembed real pv0).
  rewrite E. set (V := prun ts 0 ts pv0).
  pose proof (rinv_run ts [] ts _ eq_refl (rinv_start ts)) as I.
  assert (Live : pv_live V = rs_live (rrun ts 0 ts rstart)).
  { assert (G : forall rest i v s, pv_live v = rs_live s -> rmode_of (pv_mode v) = rs_mode s ->
              pv_live (prun ts i rest v) = rs_live (rrun ts i rest s)).
    { induction rest as [|t rest IH']; intros i v s H1 H2; [exact H1|].
      cbn [prun rrun]. destruct (pstep_live ts i t v s H1 H2) as [E1 E2]. apply IH'; assumption. }
    apply G; reflexivity. }
  (* no frame left at the end is closed *)
  assert (F : Forall (fun f => match f with PF q _ _ => real q = false | PB _ _ => True end)
                (pv_stk V)).
  { apply Forall_forall. intros [q k c|d c] Hf; [|exact Logic.I].
    assert (Hin : In (LOpen q k) (rs_live (rrun ts 0 ts rstart))).
    { rewrite <- Live. unfold pv_live. apply in_map_iff. exists (PF q k c). auto. }
    apply (ri_cand ts _ _ I) in Hin as (_ & _ & _ & _ & Hd).
    destruct (real q) eqn:O; [|reflexivity]. exfalso. unfold real in O.
    apply is_opener_iff in O as [j Hj]. unfold m in Hj. rewrite Hr in Hj. cbn [fst] in Hj.
    apply Hd. left. exists j. split; [exact (ri_bound_pairs ts _ _ I q j Hj)|exact Hj]. }
  unfold pflatten, pfinish, vembed, tembed, tree_end.
  destruct (pv_mode V) as [|b kids d [e|] txt] eqn:Em; cbn [membed].
  1,2: destruct (flatten_collapse real (pv_stk V) (pv_out V) [] F) as [E1 E2];
       rewrite E1, E2; cbn [xapp fst snd map]; rewrite map_rev; reflexivity.
  set (l := (Str (one lbrack) :: kids ++ [Str (one rbrack ++ one lbrack ++ txt)])%list).
  destruct (pv_add_all_collapse real l V) as [C1 C2].
  assert (F' : Forall (fun f => match f with PF q _ _ => real q = false | PB _ _ => True end)
                 (pv_stk (pv_add_all l V))).
  { assert (G : forall stk,
              Forall (fun f => match f with PF q _ _ => real q = false | PB _ _ => True end) stk
              <-> Forall (fun x => match x with LOpen q _ => real q = false | LBar _ => True end)
                    (map fitem stk)).
    { intros stk. rewrite Forall_map. split; apply Forall_impl; intros [] H; exact H. }
    apply G. rewrite C2. apply G. exact F. }
  destruct (flatten_collapse real (pv_stk (pv_add_all l V)) (pv_out (pv_add_all l V)) [] F')
    as [_ E2].
  destruct (flatten_collapse real (pv_stk V) (pv_out V) [] F) as [E1 _].
  rewrite E2, C1, E1. cbn [xinner xapp fst snd map].
  set (X := snd (collapse real (pv_stk V) (pv_out V))).
  replace (mk (Str (one lbrack)) :: map mk kids ++ [mk (Str (one rbrack ++ one lbrack ++ txt))])%list
    with (map mk l) by (unfold l; cbn [map]; rewrite map_app; reflexivity).
  change ([] : tframes) with (fst (tfr ([], X))).
  change (map mk X) with (snd (tfr ([], X))).
  rewrite temit_all_embed. cbn [xinner tfr snd]. rewrite map_rev. reflexivity.
Qed.

(*
The scanner
===========

Between tokens the scanner's state is a text-mode state or a region's,
inside one destination reading per destination that does not close.  In
text mode its scope stack is the view: a frame per open opener and per
such destination, holding what the view holds.  The one difference is
text not yet flushed, which the view has already added to its innermost
content; the scanner's innermost content never ends in text, so the two
meet by consing it back.

A marked frame also records whether a `}` came right after its opener,
which chooses the side a quote decays to and changes nothing for the
rows here.  The view does not keep it: `cm` gives it for each opener's
position. *)

Definition oframe (cm : nat -> bool) (f : pframe) : frame :=
  match f with
  | PF p (KDelim k mr) c =>
      Frame (FKDelim k (mr && cm p)) mr null_span (map OIn (map mk c))
  | PF _ KBracket c => Frame (FKBracket false) false null_span (map OIn (map mk c))
  | PB _ c => Frame (FKDest false) false null_span (map OIn (map mk c))
  end.

Definition oview (cm : nat -> bool) (v : pview) : ostate :=
  OState (map OIn (map mk (pv_out v))) (map (oframe cm) (pv_stk v)) None.

Definition top_of (v : pview) : list inline :=
  match pv_stk v with [] => pv_out v | f :: _ => fcontent f end.

Definition starts_text (l : list inline) : bool :=
  match l with Str _ :: _ => true | _ => false end.

Definition add_text (txt : string) (v : pview) : pview :=
  if nonempty_str txt then pv_add (Str txt) v else v.

Definition sim (v : pview) (txt : string) (o : ostate) : Prop :=
  exists v0 cm, o = oview cm v0 /\ starts_text (top_of v0) = false
                /\ v = add_text txt v0.

(* The delimiter frames are of rows whose unmatched token is its own
   text. *)
Definition self_frames (stk : list pframe) : Prop :=
  Forall (fun f => match f with PF _ (KDelim k _) _ => self_row k = true | _ => True end) stk.

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

(* What a token of these rows decays to is its own text. *)
Local Lemma self_decay : forall k mr b,
  self_row k = true ->
  ddecay_str k mr (mr && b) = tok_text (TDelim k mr true false).
Proof.
  intros k mr b H. unfold self_row in H. unfold ddecay_str.
  destruct (dsyntax_of k); try discriminate;
    (destruct (dc_decay cfg k); [|discriminate]);
    (destruct mr, b; cbn; rewrite ?append_empty_r; reflexivity).
Qed.

Local Lemma self_decay_close : forall k mr,
  self_row k = true ->
  ddecay_str k false mr = tok_text (TDelim k mr false true).
Proof.
  intros k mr H. unfold self_row in H. unfold ddecay_str.
  destruct (dsyntax_of k); try discriminate;
    (destruct (dc_decay cfg k); [|discriminate]);
    (destruct mr; cbn; rewrite ?append_empty_r; reflexivity).
Qed.

Local Lemma fr_lit_oframe : forall cm f,
  self_frames [f] -> fr_lit (oframe cm f) = mk (flit f).
Proof.
  intros cm [p [k mr|] c|d c] H; apply Forall_cons_iff in H as [H _];
    unfold fr_lit, oframe, fr_src; cbn [fr_kind fr_marked flit lit]; [|reflexivity..].
  rewrite (self_decay k mr (cm p) H). reflexivity.
Qed.

Local Lemma oflatten_embed : forall cm stk pend out,
  self_frames stk ->
  oflatten (map OIn (map mk pend)) (map (oframe cm) stk) (map OIn (map mk out))
  = map OIn (map mk (pflatten_go pend stk out)).
Proof.
  intros cm. induction stk as [|f stk IH]; intros pend out B;
    cbn [map oflatten pflatten_go]; [apply oapp_embed|].
  apply Forall_cons_iff in B as [Bf B].
  rewrite (fr_lit_oframe cm f (Forall_cons _ Bf (Forall_nil _))).
  replace (fr_out (oframe cm f)) with (map OIn (map mk (fcontent f)))
    by (destruct f as [p [k mr|] c|d c]; reflexivity).
  rewrite oapp_embed.
  change [OIn (mk (flit f))] with (map OIn (map mk [flit f])).
  rewrite oapp_embed. apply IH, B.
Qed.

Local Lemma fr_out_oframe : forall cm f, fr_out (oframe cm f) = map OIn (map mk (fcontent f)).
Proof. intros cm [p [k mr|] c|d c]; reflexivity. Qed.

Local Lemma oclose_go_embed : forall cm k mr pend stk,
  self_frames stk ->
  oclose_go k mr (map OIn (map mk pend)) (map (oframe cm) stk)
  = match pclose_go (KDelim k mr) pend stk with
    | Some (content, rest) =>
        if nonempty content
        then Some (map OIn (map mk content), null_span, map (oframe cm) rest)
        else None
    | None => None
    end.
Proof.
  intros cm k mr pend stk. revert pend.
  induction stk as [|f stk IH]; intros pend B; [reflexivity|].
  apply Forall_cons_iff in B as [Bf B].
  cbn [map oclose_go]. rewrite fr_out_oframe, oapp_embed.
  rewrite (fr_lit_oframe cm f (Forall_cons _ Bf (Forall_nil _))).
  change [OIn (mk (flit f))] with (map OIn (map mk [flit f])).
  destruct f as [p [k' m'|] c|d c]; cbn [pclose_go key_eq fcontent flit].
  - unfold dmatch. cbn [oframe fr_kind fr_marked fr_open fr_barrier].
    destruct (dstyle_eq k k' && Bool.eqb mr m')%bool;
      [destruct (xapp pend c); reflexivity|].
    rewrite oapp_embed. apply IH, B.
  - unfold dmatch. cbn [oframe fr_kind fr_barrier].
    rewrite oapp_embed. apply IH, B.
  - reflexivity.
Qed.

(* A closer is barred when the first matching opener down the stack is
   below a destination. *)
Local Lemma oclose_barred_embed : forall cm k mr stk past,
  oclose_barred_go k mr past (map (oframe cm) stk)
  = if past then has_key (KDelim k mr) (map fitem stk)
    else match pick (KDelim k mr) (map fitem stk) with PBarred => true | _ => false end.
Proof.
  intros cm k mr stk. induction stk as [|f stk IH]; intros past;
    [destruct past; reflexivity|].
  destruct f as [p [k' m'|] c|d c]; cbn [map oclose_barred_go fitem has_key pick key_eq].
  - unfold dmatch. cbn [oframe fr_kind fr_marked fr_barrier].
    destruct (dstyle_eq k k' && Bool.eqb mr m')%bool; [destruct past; reflexivity|].
    rewrite orb_false_r. rewrite IH. destruct past; reflexivity.
  - unfold dmatch. cbn [oframe fr_kind fr_barrier]. rewrite orb_false_r, IH.
    destruct past; reflexivity.
  - unfold dmatch. cbn [oframe fr_kind fr_barrier]. rewrite orb_true_r, IH.
    destruct past; [reflexivity|]. destruct (has_key (KDelim k mr) (map fitem stk)); reflexivity.
Qed.

Local Lemma bclose_embed : forall cm out stk,
  self_frames stk ->
  bclose (OState (map OIn (map mk out)) (map (oframe cm) stk) None)
  = match pclose_go KBracket [] stk with
    | Some (content, rest) =>
        Some (map mk (List.rev content), false, null_span,
              OState (map OIn (map mk out)) (map (oframe cm) rest) None)
    | None => None
    end.
Proof.
  intros cm out stk Bs. unfold bclose. cbn [os_stk os_out os_word_start].
  change (@nil oitem) with (map OIn (map mk (@nil inline))).
  assert (G : forall pend, self_frames stk ->
            bclose_go (map OIn (map mk pend)) (map (oframe cm) stk)
            = match pclose_go KBracket pend stk with
              | Some (content, rest) =>
                  Some (map OIn (map mk content), false, null_span, map (oframe cm) rest)
              | None => None
              end).
  { induction stk as [|f stk IH]; intros pend B; [reflexivity|].
    apply Forall_cons_iff in B as [Bf B].
    cbn [map bclose_go]. rewrite fr_out_oframe, oapp_embed.
    rewrite (fr_lit_oframe cm f (Forall_cons _ Bf (Forall_nil _))).
    change [OIn (mk (flit f))] with (map OIn (map mk [flit f])).
    destruct f as [p [k' m'|] c|d c]; cbn [pclose_go key_eq fcontent flit oframe fr_kind fr_open].
    - rewrite oapp_embed. apply IH; exact B.
    - reflexivity.
    - reflexivity. }
  rewrite (G [] Bs). destruct (pclose_go KBracket [] stk) as [[content rest]|]; [|reflexivity].
  rewrite oresolve_map, map_rev. reflexivity.
Qed.

Local Lemma flush_view : forall cm txt v0,
  starts_text (top_of v0) = false ->
  flush_text txt (oview cm v0) = oview cm (add_text txt v0).
Proof.
  intros cm txt [stk out md] H. unfold flush_text, flush_text_at, add_text.
  destruct (nonempty_str txt); [|reflexivity].
  assert (X : forall l, starts_text l = false -> xsnoc (Str txt) l = Str txt :: l)
    by (intros [|[] l] Hl; try reflexivity; discriminate).
  unfold pv_add, oview, oemit.
  cbn [pv_stk pv_out os_stk os_out os_word_start] in *.
  destruct stk as [|f rest]; cbn [top_of pv_stk pv_out] in H;
    [rewrite (X _ H); reflexivity|].
  cbn [map]. rewrite (X _ H).
  destruct f as [p [k mr|] c|d c]; reflexivity.
Qed.

Local Lemma self_frames_add : forall x v,
  self_frames (pv_stk v) -> self_frames (pv_stk (pv_add x v)).
Proof.
  intros x [[|f rest] out md] B; [exact B|].
  apply Forall_cons_iff in B as [Bk B]. constructor; [|exact B].
  destruct f as [p [k mr|] c|d c]; exact Bk.
Qed.

Local Lemma self_frames_add_inv : forall x v,
  self_frames (pv_stk (pv_add x v)) -> self_frames (pv_stk v).
Proof.
  intros x [[|f rest] out md] B; [exact B|].
  apply Forall_cons_iff in B as [Bk B]. constructor; [|exact B].
  destruct f as [p [k mr|] c|d c]; exact Bk.
Qed.

Local Lemma ifinish_view : forall cm txt prev v0,
  self_frames (pv_stk v0) -> starts_text (top_of v0) = false ->
  ifinish (IText false txt prev (oview cm v0))
  = map mk (List.rev (pflatten_go [] (pv_stk (add_text txt v0)) (pv_out (add_text txt v0)))).
Proof.
  intros cm txt prev v0 B H.
  unfold ifinish, ifinish_rev, ofinish. rewrite oitems_of_spec.
  cbn [ifinish_ostate ifinish_ostate_flat iresolve].
  change (tval txt) with txt.
  change (@flush_text_at semantic_pos semantic_inline_cursor txt (oview cm v0))
    with (flush_text txt (oview cm v0)).
  rewrite (flush_view cm txt v0 H).
  assert (B' : self_frames (pv_stk (add_text txt v0))).
  { unfold add_text. destruct (nonempty_str txt); [apply self_frames_add|];
      exact B. }
  unfold oview at 1 2. cbn [os_stk os_out].
  change (@nil oitem) with (map OIn (map mk (@nil inline))).
  rewrite (oflatten_embed _ _ _ _ B'), oresolve_map, map_rev. reflexivity.
Qed.

(* Only the frames' own positions are read. *)
Local Lemma oview_ext : forall cm1 cm2 v,
  (forall f, In f (pv_stk v) -> cm1 (lpos (fitem f)) = cm2 (lpos (fitem f))) ->
  oview cm1 v = oview cm2 v.
Proof.
  intros cm1 cm2 v H. unfold oview.
  rewrite (map_ext_in (oframe cm1) (oframe cm2) (pv_stk v)); [reflexivity|].
  intros [p [k mr|] c|d c] Hf; [|reflexivity..].
  unfold oframe. specialize (H _ Hf). cbn [fitem lpos] in H. rewrite H. reflexivity.
Qed.

(*
The view's invariant
--------------------

The stack is ordered, its positions are before `n`, and its delimiter
frames are of the rows here; and outside a region the innermost frame
is empty exactly when its opener is the last token read. *)

Definition pv_ok (n : nat) (v : pview) : Prop :=
  ldesc (pv_live v) /\ (forall x, In x (pv_live v) -> lpos x < n)
  /\ self_frames (pv_stk v)
  /\ match pv_mode v, pv_stk v with
     | PMNormal, PF p _ c :: _ => c = [] <-> S p = n
     | _, _ => True
     end.

Local Lemma xsnoc_nonempty : forall x l, xsnoc x l <> [].
Proof.
  intros x [|[] l]; unfold xsnoc; try discriminate; destruct x; discriminate.
Qed.

Local Lemma xapp_nonempty_r : forall a b, b <> [] -> xapp a b <> [].
Proof.
  intros [|x [|y r]] b H; [exact H|apply xsnoc_nonempty|discriminate].
Qed.

Local Lemma pv_ok_add : forall n x v,
  ldesc (pv_live v) -> (forall y, In y (pv_live v) -> lpos y < n) ->
  self_frames (pv_stk v) -> pv_ok (S n) (pv_add x v).
Proof.
  intros n x v D Bd B. destruct (pv_add_live x v) as [E1 E2].
  split; [rewrite E1; exact D|].
  split; [intros y H; rewrite E1 in H; specialize (Bd y H); lia|].
  split; [apply self_frames_add, B|].
  rewrite E2. unfold pv_add. destruct (pv_stk v) as [|f rest] eqn:E; [destruct (pv_mode v); exact Logic.I|].
  cbn [pv_stk pv_mode]. destruct (pv_mode v); [|exact Logic.I].
  destruct f as [p k c|d c]; cbn [fset fcontent]; [|exact Logic.I].
  assert (p < n) by (apply (Bd (LOpen p k)); unfold pv_live; rewrite E; left; reflexivity).
  split; [intros Hc; destruct (xsnoc_nonempty x c Hc)|lia].
Qed.

Local Lemma ldesc_below : forall above f rest,
  ldesc (map fitem (above ++ f :: rest)) -> ldesc (map fitem rest).
Proof.
  induction above as [|g above IH]; intros f rest D.
  - apply StronglySorted_inv in D as [D _]. exact D.
  - apply StronglySorted_inv in D as [D _]. exact (IH f rest D).
Qed.

(* What closing a pair leaves of the stack. *)
Local Lemma pv_ok_close : forall n v K p below content rest,
  pv_ok n v -> pick K (pv_live v) = PFound p below ->
  pclose_go K [] (pv_stk v) = Some (content, rest) ->
  ldesc (map fitem rest) /\ (forall y, In y (map fitem rest) -> lpos y < p)
  /\ self_frames rest /\ p < n.
Proof.
  intros n v K p below content rest (D & Bd & B & _) P Hc.
  unfold pv_live in P, D, Bd.
  destruct (pick_split K _ p below P) as (above & c & rest' & E & F & Hb).
  rewrite E in Hc, D, Bd, B.
  destruct (pclose_split K above p c rest' [] F) as [content' Hc'].
  rewrite Hc in Hc'. injection Hc' as <- <-.
  assert (Hpn : p < n).
  { apply (Bd (LOpen p K)). rewrite map_app. apply in_or_app. right. left. reflexivity. }
  split; [exact (ldesc_below above _ rest D)|].
  split; [|split; [|exact Hpn]].
  - intros y Hy. rewrite map_app in D. cbn [map] in D.
    clear -D Hy. induction above as [|g above IH]; cbn [app] in D.
    + apply StronglySorted_inv in D as [_ F]. rewrite Forall_forall in F. exact (F y Hy).
    + apply StronglySorted_inv in D as [D _]. exact (IH D).
  - unfold self_frames in B. apply Forall_app in B as [_ B].
    apply Forall_cons_iff in B as [_ B]. exact B.
Qed.

Local Lemma pv_ok_step : forall ts n t v,
  pv_ok n v ->
  (forall k mr op cl, t = TDelim k mr op cl -> self_row k = true) ->
  pv_ok (S n) (pstep ts n t v).
Proof.
  intros ts n t v Ok Hb. pose proof Ok as (D & Bd & B & _).
  unfold pstep. destruct (pv_mode v) as [|b kids d e txt] eqn:Em.
  2: { destruct (match e with Some e' => Nat.eqb n e' | None => false end).
       - apply pv_ok_add; exact D || exact Bd || exact B.
       - split; [exact D|]. split; [intros y H; specialize (Bd y H); lia|].
         split; [exact B|]. cbn [pv_setmode pv_mode]. exact Logic.I. }
  assert (Open : forall k op txt, (forall k' mr, k = KDelim k' mr -> self_row k' = true) ->
                   pv_ok (S n) (popen n k op txt v)).
  { intros k [|] txt Hk; [|apply pv_ok_add; assumption].
    unfold popen. split; [|split; [|split]].
    - unfold pv_live. cbn [pv_stk map]. constructor; [exact D|].
      apply Forall_forall. intros y H. exact (Bd y H).
    - unfold pv_live. cbn [pv_stk map fitem lpos].
      intros y [<-|H]; [cbn; lia|]. specialize (Bd y H). lia.
    - constructor; [|exact B]. destruct k as [k' mr|]; [exact (Hk k' mr eq_refl)|exact Logic.I].
    - cbn [pv_stk pv_mode]. rewrite Em. split; reflexivity. }
  destruct t as [c| |k mr op cl| |b]; try (apply pv_ok_add; assumption).
  - specialize (Hb k mr op cl eq_refl).
    destruct (if cl then pick (KDelim k mr) (pv_live v) else PNone) as [p below| |] eqn:P;
      [|apply pv_ok_add; assumption|apply Open; intros k' mr' E; injection E as <- _; exact Hb].
    destruct (Nat.ltb (S p) n); [|apply Open; intros k' mr' E; injection E as <- _; exact Hb].
    destruct cl; [|discriminate].
    destruct (pclose_go (KDelim k mr) [] (pv_stk v)) as [[content rest]|] eqn:Hc;
      [|destruct (pclose_found _ _ _ _ P) as (? & ? & E & _); congruence].
    destruct (pv_ok_close n v _ p below content rest Ok P Hc) as (D' & Bd' & B' & Hpn).
    apply (pv_ok_add n _ (PView rest (pv_out v) PMNormal)); unfold pv_live; cbn [pv_stk].
    + exact D'.
    + intros y H. specialize (Bd' y H). lia.
    + exact B'.
  - apply Open. intros k' mr E. discriminate.
  - destruct (pick KBracket (pv_live v)) as [p below| |] eqn:P;
      destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|] eqn:Hc;
      try (apply pv_ok_add; assumption).
    destruct (pv_ok_close n v _ p below content rest Ok P Hc) as (D' & Bd' & B' & Hpn).
    destruct (region_end ts n b) as [e|]; [|destruct b].
    + split; [exact D'|]. split; [intros y H; specialize (Bd' y H); cbn; lia|].
      split; [exact B'|exact Logic.I].
    + split; [|split; [|split]]; unfold pv_live; cbn [pv_stk pv_mode map fitem].
      * constructor; [exact D'|]. apply Forall_forall. intros y H. specialize (Bd' y H). cbn. lia.
      * intros y [<-|H]; [cbn; lia|]. specialize (Bd' y H). lia.
      * constructor; [exact Logic.I|exact B'].
      * exact Logic.I.
    + split; [exact D'|]. split; [intros y H; specialize (Bd' y H); cbn; lia|].
      split; [exact B'|exact Logic.I].
Qed.

(*
Text and tokens, scanned
------------------------
*)

Local Lemma sim_text : forall v txt o s,
  sim v txt o -> nonempty_str s = true ->
  sim (pv_add (Str s) v) (txt ++ s) o.
Proof.
  intros v txt o s (v0 & cm & -> & Ht & ->) Hs. exists v0, cm.
  split; [reflexivity|]. split; [exact Ht|].
  assert (X : forall l, starts_text l = false ->
            xsnoc (Str s) (xsnoc (Str txt) l) = xsnoc (Str (txt ++ s)) l)
    by (intros [|[] l] Hl; try reflexivity; discriminate).
  unfold add_text. destruct txt as [|a t'].
  - cbn [append]. rewrite Hs. reflexivity.
  - cbn [nonempty_str append]. unfold pv_add.
    destruct v0 as [[|f rest] out md]; cbn [top_of pv_stk pv_out pv_mode] in Ht |- *;
      [rewrite (X _ Ht); reflexivity|].
    destruct f as [p k c|d c]; cbn [fset fcontent] in *; rewrite (X _ Ht); reflexivity.
Qed.

(* What `ilead` asks of a byte that is not a footnote's `^`. *)
Definition no_note (c : ascii) (txt : string) (prev : option ascii) : bool :=
  negb (Ascii.eqb c hat && note_pos txt prev).

(* A plain byte, a paren, and `}` where no token is before it, are text. *)
Local Lemma ilead_text : forall c txt prev o,
  in_alphabet c = true -> Ascii.eqb c lbrace = false ->
  Ascii.eqb c lbrack = false -> Ascii.eqb c rbrack = false ->
  dstyle_of c = None -> no_note c txt prev = true ->
  ilead c txt prev o = IText false (txt ++ one c) (Some c) o.
Proof.
  intros c txt prev o Ha Hlb Hlk Hrk Hd Hn.
  unfold no_note in Hn. apply negb_true_iff in Hn.
  destruct (Ascii.eqb c rbrace) eqn:Erb.
  { apply Ascii.eqb_eq in Erb. subst c. unfold ilead.
    change (is_bslash rbrace) with false. change (is_tick rbrace) with false.
    change (Ascii.eqb rbrace dollar) with false.
    change (Ascii.eqb rbrace period) with false.
    change (Ascii.eqb rbrace hyphen) with false.
    change (Ascii.eqb rbrace lbrace) with false.
    change (Ascii.eqb rbrace bang) with false.
    change (Ascii.eqb rbrace lt) with false.
    change (Ascii.eqb rbrace ":"%char) with false.
    change (Ascii.eqb rbrace lbrack) with false.
    change (Ascii.eqb rbrace rbrack) with false.
    change (Ascii.eqb rbrace hat) with false. cbn [andb].
    rewrite Hd. reflexivity. }
  unfold in_alphabet in Ha. rewrite Hd in Ha.
  apply andb_true_iff in Ha as [Ha _]. apply andb_true_iff in Ha as [Ha Hhy].
  apply andb_true_iff in Ha as [_ Hres]. rewrite Hlb, Erb, Hlk, Hrk in Hres.
  cbn [orb] in Hres. apply negb_true_iff in Hres, Hhy.
  pose proof (dreserved_false c Hres)
    as (Hbs & Htk & _ & _ & _ & _ & Hbg & Hdol & Hpd & Hlt).
  assert (Hcolon : Ascii.eqb c ":"%char = false).
  { unfold dreserved in Hres.
    repeat (apply orb_false_iff in Hres as [Hres ?]). assumption. }
  unfold ilead.
  rewrite Hbs, Htk, Hdol, Hpd, Hhy, Hlb, Hbg, Hlt, Hcolon, Hlk, Hrk, Hn.
  cbn [andb]. rewrite Hd. reflexivity.
Qed.

Local Lemma alphabet_hyphen : forall c,
  in_alphabet c = true -> Ascii.eqb c hyphen = false.
Proof.
  intros c H. unfold in_alphabet in H.
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
  apply negb_true_iff in H. exact H.
Qed.

Local Lemma alphabet_self : forall c k,
  in_alphabet c = true -> dstyle_of c = Some k -> self_row k = true.
Proof.
  intros c k H Hd. unfold in_alphabet in H. rewrite Hd in H.
  apply andb_true_iff in H as [_ H]. apply andb_true_iff in H as [H _]. exact H.
Qed.

Local Lemma alphabet_paren : forall c k,
  in_alphabet c = true -> dstyle_of c = Some k ->
  Ascii.eqb c lparen = false /\ Ascii.eqb c rparen = false.
Proof.
  intros c k H Hd. unfold in_alphabet in H. rewrite Hd in H.
  apply andb_true_iff in H as [_ H]. apply andb_true_iff in H as [_ H].
  apply negb_true_iff, orb_false_iff in H. exact H.
Qed.

Local Lemma self_dbare : forall k prev,
  self_row k = true -> dbare k prev = bare_opens k.
Proof.
  intros k prev H. unfold self_row in H. unfold dbare, bare_opens.
  destruct (dsyntax_of k); try discriminate; reflexivity.
Qed.

(* `ilead_dchar`, with the guard on the footnote marker in place of an
   empty stack top: a bracket may have just opened. *)
Local Lemma ilead_dchar_note : forall k txt prev o,
  denabled_of k = true -> Ascii.eqb (dchar k) hyphen = false ->
  no_note (dchar k) txt prev = true ->
  ilead (dchar k) txt prev o = IDelim k 0 txt prev false o.
Proof.
  intros k txt prev o Hen Hhy Hn. unfold no_note in Hn. apply negb_true_iff in Hn.
  destruct (dreserved_false (dchar k) (dchar_free k))
    as [Hb [Ht [Hlb [Hrb [Hlk [Hrk [Hbg [Hdol [Hpd Hlt]]]]]]]]].
  unfold ilead.
  rewrite Hb, Ht, Hdol, Hpd, Hhy, Hlb, Hlt, Hlk, Hrk, Hbg, Hn.
  assert (Hcolon : Ascii.eqb (dchar k) ":"%char = false).
  { destruct (Ascii.eqb (dchar k) ":"%char) eqn:E; [|reflexivity].
    apply Ascii.eqb_eq in E. pose proof (dchar_free k) as Hfree.
    rewrite E in Hfree. discriminate. }
  rewrite Hcolon. cbn [andb]. rewrite (dstyle_of_dchar k Hen). reflexivity.
Qed.

Local Lemma iscan_dtoken_note : forall k txt prev o,
  denabled_of k = true -> Ascii.eqb (dchar k) hyphen = false ->
  no_note (dchar k) txt prev = true ->
  iscan_str (dtoken k) (IText false txt prev o) = IDelim k (pred (dwidth k)) txt prev false o.
Proof.
  intros k txt prev o Hen Hhy Hn. unfold dtoken.
  destruct (dwidth k) as [|w] eqn:Ew; [destruct (dwidth_nonzero k Ew)|].
  cbn [chars iscan_str istep istep_at]. rewrite (ilead_dchar_note k _ _ _ Hen Hhy Hn).
  rewrite (iscan_chars_delim w k 0 txt _ o) by lia.
  cbn [pred]. reflexivity.
Qed.

Local Lemma oemit_view : forall cm x v,
  (forall s, x <> Str s) -> oemit (mk x) (oview cm v) = oview cm (pv_add x v).
Proof.
  intros cm x [[|f rest] out md] Hx; unfold oemit, oview, pv_add;
    cbn [pv_stk pv_out os_stk os_out os_word_start map];
    rewrite (xsnoc_nonstr x _ Hx); [reflexivity|].
  destruct f as [p [k mr|] c|d c]; reflexivity.
Qed.

Local Lemma top_add_nonstr : forall x v,
  (forall s, x <> Str s) -> starts_text (top_of (pv_add x v)) = false.
Proof.
  intros x [[|f rest] out md] Hx; unfold pv_add, top_of; cbn [pv_stk pv_out];
    [|destruct f; cbn [fset fcontent]];
    rewrite (xsnoc_nonstr x _ Hx); destruct x; try reflexivity; destruct (Hx _ eq_refl).
Qed.

Local Lemma pclose_none : forall k stk pend,
  (forall p below, pick k (map fitem stk) <> PFound p below) ->
  pclose_go k pend stk = None.
Proof.
  intros k stk. induction stk as [|[q k' c|d c] stk IH]; intros pend H; [reflexivity| |reflexivity].
  cbn [pclose_go]. cbn [map fitem pick] in H.
  destruct (key_eq k k'); [destruct (H q (map fitem stk) eq_refl)|]. apply IH, H.
Qed.

Local Lemma pclose_grows : forall k stk pend content rest,
  pclose_go k pend stk = Some (content, rest) -> pend <> [] -> content <> [].
Proof.
  intros k stk. induction stk as [|[q k' c|d c] stk IH];
    intros pend content rest H Hp; [discriminate| |discriminate].
  cbn [pclose_go] in H. destruct (key_eq k k').
  - injection H as <- _. apply xapp_nonempty, Hp.
  - apply (IH _ _ _ H). apply xapp_nonempty_r. discriminate.
Qed.

(* Outside a region, a closer finds its opener's content empty exactly
   when the opener is the token right before it. *)
Local Lemma close_empty : forall n v above p k c rest content rest',
  pv_ok n v -> pv_mode v = PMNormal ->
  pv_stk v = (above ++ PF p k c :: rest)%list ->
  Forall (passes k) above ->
  pclose_go k [] (pv_stk v) = Some (content, rest') ->
  (content = [] <-> S p = n).
Proof.
  intros n v above p k c rest content rest' (D & Bd & _ & Inn) Em E F H.
  unfold pv_live in D, Bd. rewrite E in D, Bd, H, Inn. rewrite Em in Inn.
  destruct above as [|g above'].
  - cbn [app pclose_go] in H. rewrite key_eq_refl in H. injection H as <- _. exact Inn.
  - apply Forall_cons_iff in F as [Fk F].
    destruct g as [q k1 c1|d c1]; [|destruct Fk]. cbn [passes] in Fk.
    cbn [app pclose_go] in H. rewrite Fk in H.
    apply pclose_grows in H; [|apply xapp_nonempty_r; discriminate].
    assert (Hpq : p < q).
    { apply (ldesc_above (PF q k1 c1 :: above') (PF p k c) rest D (PF q k1 c1)).
      left. reflexivity. }
    assert (Hq : q < n) by (apply (Bd (LOpen q k1)); left; reflexivity).
    split; [intros; contradiction|lia].
Qed.

(* A completed token, bare or with `}` after it (`mr`), resolved. *)
Local Lemma resolve_sim : forall ts n k mr txt prev next v o,
  self_row k = true -> pv_ok n v -> pv_mode v = PMNormal -> sim v txt o ->
  exists txt' o',
    idelim_resolve k txt prev mr next o
    = IText false txt' (Some (if mr then rbrace else dchar k)) o'
    /\ sim (pstep ts n (TDelim k mr (negb mr && bare_opens k && nonspace_at next)
                          (mr || nonspace_at prev)) v) txt' o'.
Proof.
  intros ts n k mr txt prev next v o Hb Ok Em (v0 & cm & -> & Ht & ->).
  pose proof Ok as (_ & Bd & B & _).
  set (v := add_text txt v0) in *.
  set (t := TDelim k mr (negb mr && bare_opens k && nonspace_at next)
              (mr || nonspace_at prev)).
  set (K := KDelim k mr).
  assert (Hv : flush_text txt (oview cm v0) = oview cm v)
    by (apply flush_view, Ht).
  assert (Lv : pv_live v = pv_live v0).
  { unfold v, add_text. destruct (nonempty_str txt); [apply pv_add_live|reflexivity]. }
  (* the token does not close: it opens if it may, or it is text *)
  assert (Done : exists txt' o',
            idelim_done k txt prev mr next (oview cm v0)
            = IText false txt' (Some (if mr then rbrace else dchar k)) o'
            /\ sim (popen n K (negb mr && bare_opens k && nonspace_at next)
                      (tok_text t) v) txt' o').
  { unfold idelim_done. rewrite (self_dbare k prev Hb).
    replace (bare_opens k && negb mr && nonspace_at next)%bool
      with (negb mr && bare_opens k && nonspace_at next)%bool
      by (destruct mr, (bare_opens k); reflexivity).
    destruct (negb mr && bare_opens k && nonspace_at next)%bool eqn:Op.
    - assert (mr = false) as -> by (destruct mr; [discriminate|reflexivity]).
      change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s
                (tval txt) (oview cm v0))
        with (flush_text txt (oview cm v0)).
      rewrite Hv. eexists "", _. split; [reflexivity|].
      exists (PView (PF n (KDelim k false) [] :: pv_stk v) (pv_out v) (pv_mode v)), cm.
      split; [reflexivity|]. split; reflexivity.
    - assert (Et : tok_text t = tok_text (TDelim k mr false true))
        by (unfold t; try rewrite Op; destruct mr; reflexivity).
      exists (txt ++ tok_text t), (oview cm v0). split.
      + unfold InlineScan.idelim_lit, InlineScan.idelim_lit_prev.
        cbn [tpush]. rewrite Et, (self_decay_close k mr Hb).
        destruct mr; reflexivity.
      + unfold popen. apply sim_text.
        * exists v0, cm. split; [reflexivity|]. split; [exact Ht|reflexivity].
        * rewrite Et. destruct mr; cbn [tok_text];
            [destruct (dtoken k); reflexivity|apply dtoken_nonempty]. }
  unfold idelim_resolve.
  destruct (nonspace_at prev || mr)%bool eqn:Hc.
  2: { apply orb_false_iff in Hc as [Hp ->]. unfold t in *. rewrite Hp in *.
       unfold pstep. rewrite Em. cbn. fold K. exact Done. }
  assert (Et : tok_text t
               = tok_text (TDelim k mr (negb mr && bare_opens k && nonspace_at next)
                             true))
    by (destruct mr; reflexivity).
  rewrite Et in Done. unfold t. rewrite orb_comm, Hc. unfold pstep. rewrite Em.
  fold K.
  rewrite oclose_guard.
  change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s
            (tval txt) (oview cm v0))
    with (flush_text txt (oview cm v0)).
  rewrite Hv. unfold oclose. unfold oview at 1.
  cbn [os_stk os_out os_word_start].
  change (@nil oitem) with (map OIn (map mk (@nil inline))).
  rewrite (oclose_go_embed cm k mr [] (pv_stk v) B).
  unfold oclose_barred.
  change (os_stk (oview cm v0)) with (map (oframe cm) (pv_stk v0)).
  rewrite oclose_barred_embed.
  assert (Lv' : map fitem (pv_stk v0) = pv_live v) by (rewrite Lv; reflexivity).
  rewrite Lv'. fold K.
  destruct (pick K (pv_live v)) as [p below| |] eqn:P.
  2: { rewrite (pclose_none K (pv_stk v) []) by (intros p' b'; unfold pv_live in P; rewrite P; discriminate).
       eexists (txt ++ tok_text (TDelim k mr (negb mr && bare_opens k && nonspace_at next) true)), (oview cm v0).
       split.
       - unfold InlineScan.idelim_lit, InlineScan.idelim_lit_prev. cbn [tpush].
         rewrite (self_decay_close k mr Hb). destruct mr; reflexivity.
       - apply sim_text.
         + exists v0, cm. split; [reflexivity|]. split; [exact Ht|reflexivity].
         + destruct mr; cbn [tok_text];
             [destruct (dtoken k); reflexivity|apply dtoken_nonempty]. }
  2: { rewrite (pclose_none K (pv_stk v) []) by (intros p' b'; unfold pv_live in P; rewrite P; discriminate).
       exact Done. }
  unfold pv_live in P.
  destruct (pick_split K (pv_stk v) p below P)
    as (above & c & rest & E & F & Hbl).
  destruct (pclose_split K above p c rest [] F) as [content Hc'].
  rewrite <- E in Hc'. rewrite Hc'.
  pose proof (close_empty n v above p K c rest content rest Ok Em E F Hc')
    as Hce.
  assert (Hpn : p < n).
  { apply (Bd (LOpen p K)). unfold pv_live. rewrite E, map_app.
    apply in_or_app. right. left. reflexivity. }
  destruct (Nat.ltb (S p) n) eqn:L.
  - apply Nat.ltb_lt in L.
    assert (content <> []) as Hne by (intros H0; apply Hce in H0; lia).
    destruct content as [|x0 content']; [contradiction|]. cbn [nonempty].
    set (content := x0 :: content').
    eexists "", _. split; [destruct mr; reflexivity|].
    exists (pv_add (dnode k (map mk (List.rev content))) (PView rest (pv_out v) PMNormal)),
      cm.
    split; [|split; [apply top_add_nonstr, dnode_nonstr|reflexivity]].
    rewrite oresolve_map, <- map_rev.
    destruct mr;
      change ({| os_out := os_out (oview cm v); os_stk := map (oframe cm) rest;
                 os_word_start := os_word_start (oview cm v) |})
        with (oview cm (PView rest (pv_out v) PMNormal));
      apply oemit_view, dnode_nonstr.
  - apply Nat.ltb_ge in L.
    assert (content = []) as -> by (apply Hce; lia). exact Done.
Qed.

(*
Destination readings
--------------------

A destination that does not close is read twice: as a destination,
which the balanced `)` would end and never does, and as ordinary text
inside the bracket's scope, which is what the paragraph keeps.  The
scanner's state is the second reading inside one `IDest` per such
destination.  A byte passes through each of them, counting parens, as
long as it is not a backslash and not the `)` that would end one. *)

Record wlayer : Type := WL {
  wl_kids : inlines; wl_open : span; wl_depth : nat; wl_dst : string; wl_o : ostate
}.

Fixpoint wrap (ws : list wlayer) (core : iscan) : iscan :=
  match ws with
  | [] => core
  | w :: rest =>
      IDest (wl_kids w) false (wl_open w) false (wl_depth w) (wl_dst w) (wrap rest core) (wl_o w)
  end.

(* The paren depth after a byte, or `None` if the byte ends the
   destination. *)
Definition pstep_byte (c : ascii) (depth : nat) : option nat :=
  if Ascii.eqb c lparen then Some (S depth)
  else if Ascii.eqb c rparen then match depth with O => None | S d => Some d end
  else Some depth.

Fixpoint pdepth (depth : nat) (s : string) : option nat :=
  match s with
  | EmptyString => Some depth
  | String c rest =>
      match pstep_byte c depth with Some d => pdepth d rest | None => None end
  end.

Definition wl_step (c : ascii) (w : wlayer) : wlayer :=
  WL (wl_kids w) (wl_open w)
     (match pstep_byte c (wl_depth w) with Some d => d | None => 0 end)
     (wl_dst w ++ one c) (wl_o w).

Definition wl_after (s : string) (w : wlayer) : wlayer :=
  WL (wl_kids w) (wl_open w)
     (match pdepth (wl_depth w) s with Some d => d | None => 0 end)
     (wl_dst w ++ s) (wl_o w).

Fixpoint no_bslash (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c rest => negb (is_bslash c) && no_bslash rest
  end.

Local Lemma istep_idest : forall c kids op depth dst sh o d',
  is_bslash c = false -> pstep_byte c depth = Some d' ->
  istep c (IDest kids false op false depth dst sh o)
  = IDest kids false op false d' (dst ++ one c) (istep c sh) o.
Proof.
  intros c kids op depth dst sh o d' Hb Hp. unfold pstep_byte in Hp.
  unfold istep. cbn [istep_at]. rewrite Hb.
  destruct (Ascii.eqb c lparen) eqn:El.
  - injection Hp as <-. apply Ascii.eqb_eq in El. subst c. reflexivity.
  - destruct (Ascii.eqb c rparen) eqn:Er.
    + apply Ascii.eqb_eq in Er. subst c.
      destruct depth as [|d]; [discriminate|injection Hp as <-]. reflexivity.
    + injection Hp as <-. reflexivity.
Qed.

Local Lemma istep_wrap : forall c ws core,
  is_bslash c = false ->
  Forall (fun w => pstep_byte c (wl_depth w) <> None) ws ->
  istep c (wrap ws core) = wrap (map (wl_step c) ws) (istep c core).
Proof.
  intros c ws core Hb. induction ws as [|w ws IH]; intros F; [reflexivity|].
  apply Forall_cons_iff in F as [Fw F]. cbn [wrap map].
  destruct (pstep_byte c (wl_depth w)) as [d'|] eqn:Hp; [|contradiction].
  rewrite (istep_idest c _ _ _ _ _ _ d' Hb Hp), IH by exact F.
  unfold wl_step. rewrite Hp. reflexivity.
Qed.

Local Lemma iscan_wrap : forall s ws core,
  no_bslash s = true ->
  Forall (fun w => pdepth (wl_depth w) s <> None) ws ->
  iscan_str s (wrap ws core) = wrap (map (wl_after s) ws) (iscan_str s core).
Proof.
  induction s as [|c s IH]; intros ws core Hb F.
  - cbn [iscan_str]. f_equal. rewrite <- (map_id ws) at 1. apply map_ext.
    intros [k o d dst o']. unfold wl_after. cbn. rewrite append_empty_r. reflexivity.
  - cbn [no_bslash] in Hb. apply andb_true_iff in Hb as [Hc Hb]. apply negb_true_iff in Hc.
    cbn [iscan_str].
    rewrite (istep_wrap c ws core Hc).
    2: { rewrite Forall_forall in F |- *. intros w Hw E. apply (F w Hw).
         cbn [pdepth]. rewrite E. reflexivity. }
    rewrite IH; [|exact Hb|].
    + f_equal. rewrite map_map. apply map_ext_in. intros [k o d dst o'] Hw.
      rewrite Forall_forall in F. specialize (F _ Hw). cbn [wl_depth pdepth] in F.
      unfold wl_step, wl_after. cbn [wl_depth wl_dst wl_kids wl_open wl_o pdepth].
      destruct (pstep_byte c d); [|contradiction]. rewrite append_assoc. reflexivity.
    + rewrite Forall_map. rewrite Forall_forall in F |- *. intros w Hw E.
      apply (F w Hw). unfold wl_step in E. cbn [wl_depth pdepth] in *.
      destruct (pstep_byte c (wl_depth w)); [exact E|reflexivity].
Qed.

(* A state resolved as at the end of a line, through the destination
   readings. *)
Fixpoint rres (st : iscan) : iscan :=
  match st with
  | IDest k i o e d dst sh o' => IDest k i o e d dst (rres sh) o'
  | _ => iresolve st
  end.

Local Lemma rres_wrap : forall ws core, rres (wrap ws core) = wrap ws (rres core).
Proof. induction ws as [|w ws IH]; intros core; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

(* What a token leaves behind agrees with a settled state on the byte
   after it, or at the end of the line. *)
Definition settles (X st : iscan) (next : option ascii) : Prop :=
  match next with
  | Some c => istep c X = istep c st
  | None => rres X = rres st
  end.

Local Lemma pdepth_app : forall d a b,
  pdepth d (a ++ b) = match pdepth d a with Some d' => pdepth d' b | None => None end.
Proof.
  intros d a. revert d. induction a as [|c a IH]; intros d b; [reflexivity|].
  cbn [append pdepth]. destruct (pstep_byte c d); [apply IH|reflexivity].
Qed.

Local Lemma no_bslash_app : forall a b, no_bslash (a ++ b) = (no_bslash a && no_bslash b)%bool.
Proof.
  induction a as [|c a IH]; intros b; [reflexivity|]. cbn. rewrite IH. apply andb_assoc.
Qed.

Local Lemma step_through : forall bytes rest ws core X st,
  no_bslash (bytes ++ rest) = true ->
  Forall (fun w => pdepth (wl_depth w) (bytes ++ rest) <> None) ws ->
  iscan_str bytes core = X -> settles X st (get 0 rest) ->
  rres (iscan_str (bytes ++ rest) (wrap ws core))
  = rres (iscan_str rest (wrap (map (wl_after bytes) ws) st)).
Proof.
  intros bytes rest ws core X st Hb F HX Hs.
  rewrite no_bslash_app in Hb. apply andb_true_iff in Hb as [Hb1 Hb2].
  rewrite iscan_str_app, iscan_wrap, HX.
  2: exact Hb1.
  2: { rewrite Forall_forall in F |- *. intros w Hw E. apply (F w Hw).
       rewrite pdepth_app, E. reflexivity. }
  destruct rest as [|c r].
  - cbn [iscan_str]. rewrite !rres_wrap. cbn [get settles] in Hs. rewrite Hs. reflexivity.
  - cbn [iscan_str no_bslash] in *. apply andb_true_iff in Hb2 as [Hc _].
    apply negb_true_iff in Hc.
    assert (Fc : Forall (fun w => pstep_byte c (wl_depth w) <> None) (map (wl_after bytes) ws)).
    { rewrite Forall_map. rewrite Forall_forall in F |- *. intros w Hw E. apply (F w Hw).
      rewrite pdepth_app. unfold wl_after in E. cbn [wl_depth] in E.
      destruct (pdepth (wl_depth w) bytes) as [d'|]; [|reflexivity].
      cbn [pdepth]. rewrite E. reflexivity. }
    rewrite !(istep_wrap c _ _ Hc Fc). cbn [get settles] in Hs. rewrite Hs. reflexivity.
Qed.

(*
Tokens, in text mode
--------------------
*)

Local Lemma settles_refl : forall X next, settles X X next.
Proof. intros X [c|]; reflexivity. Qed.

(* A bare token: the byte after it resolves it. *)
Local Lemma tok_bare : forall k txt prev o next txt' o',
  denabled_of k = true -> Ascii.eqb (dchar k) hyphen = false ->
  no_note (dchar k) txt prev = true ->
  (forall c, next = Some c -> Ascii.eqb c rbrace = false) ->
  idelim_resolve k txt prev false next o = IText false txt' (Some (dchar k)) o' ->
  settles (iscan_str (dtoken k) (IText false txt prev o))
          (IText false txt' (Some (dchar k)) o') next.
Proof.
  intros k txt prev o next txt' o' Hen Hhy Hn Hr Hres.
  rewrite (iscan_dtoken_note k txt prev o Hen Hhy Hn).
  assert (Hw : Nat.ltb (S (pred (dwidth k))) (dwidth k) = false).
  { pose proof (dwidth_nonzero k). apply Nat.ltb_ge. lia. }
  destruct next as [c|]; cbn [settles].
  - unfold istep at 1. cbn [istep_at]. rewrite Hw, (Hr c eq_refl), Hres. reflexivity.
  - cbn [rres iresolve]. rewrite Hw, Hres. reflexivity.
Qed.

(* A token with `}` after it: a marked closer, the `}` with it. *)
Local Lemma tok_marked_close : forall k txt prev o,
  denabled_of k = true -> Ascii.eqb (dchar k) hyphen = false ->
  no_note (dchar k) txt prev = true ->
  iscan_str (dtoken k ++ one rbrace) (IText false txt prev o)
  = idelim_resolve k txt prev true (Some rbrace) o.
Proof.
  intros k txt prev o Hen Hhy Hn.
  rewrite iscan_str_app, (iscan_dtoken_note k txt prev o Hen Hhy Hn).
  assert (Hw : Nat.ltb (S (pred (dwidth k))) (dwidth k) = false).
  { pose proof (dwidth_nonzero k). apply Nat.ltb_ge. lia. }
  cbn [iscan_str one]. unfold istep. cbn [istep_at].
  rewrite Hw, Ascii.eqb_refl. reflexivity.
Qed.

(* `{` and a token: a marked opener, pushed when the byte after it is
   known. *)
Local Lemma tok_marked_open : forall k txt prev o next,
  denabled_of k = true ->
  settles (iscan_str (marked_open k) (IText false txt prev o))
          (IText false "" (Some (dchar k)) (oopen_marked k (at_rbrace next) txt o)) next.
Proof.
  intros k txt prev o next Hen.
  rewrite (iscan_marked_open k txt prev o Hen).
  assert (Hw : Nat.ltb (S (pred (dwidth k))) (dwidth k) = false).
  { pose proof (dwidth_nonzero k). apply Nat.ltb_ge. lia. }
  unfold idelim_marked. destruct next as [c|]; cbn [settles at_rbrace].
  - unfold istep at 1. cbn [istep_at]. rewrite Hw. reflexivity.
  - cbn [rres iresolve]. rewrite Hw. reflexivity.
Qed.

(* A run of a row's character too short to be a token is text. *)
Local Lemma tok_partial : forall k j txt prev o next,
  denabled_of k = true -> Ascii.eqb (dchar k) hyphen = false ->
  no_note (dchar k) txt prev = true -> 0 < j < dwidth k ->
  (forall c, next = Some c -> c <> dchar k) ->
  settles (iscan_str (chars (dchar k) j) (IText false txt prev o))
          (IText false (txt ++ chars (dchar k) j) (Some (dchar k)) o) next.
Proof.
  intros k j txt prev o next Hen Hhy Hn [Hj0 Hjw] Hr.
  destruct j as [|j]; [lia|].
  cbn [chars iscan_str]. unfold istep at 1. cbn [istep_at].
  rewrite (ilead_dchar_note k txt prev o Hen Hhy Hn).
  rewrite (iscan_chars_delim j k 0 txt prev o) by lia. cbn [plus].
  assert (Hw : Nat.ltb (S j) (dwidth k) = true) by (apply Nat.ltb_lt; lia).
  destruct next as [c|]; cbn [settles].
  - unfold istep at 1. cbn [istep_at]. rewrite Hw.
    assert (Ascii.eqb c (dchar k) = false) as Hd
      by (apply Ascii.eqb_neq, (Hr c eq_refl)).
    rewrite Hd. reflexivity.
  - cbn [rres iresolve]. rewrite Hw. reflexivity.
Qed.

Local Lemma tok_marked_partial : forall k j txt prev o next,
  denabled_of k = true -> 0 < j < dwidth k ->
  (forall c, next = Some c -> c <> dchar k) ->
  settles (iscan_str (String lbrace (chars (dchar k) j)) (IText false txt prev o))
          (IText false (txt ++ String lbrace (chars (dchar k) j)) (Some (dchar k)) o) next.
Proof.
  intros k j txt prev o next Hen [Hj0 Hjw] Hr.
  destruct j as [|j]; [lia|].
  change (String lbrace (chars (dchar k) (S j)))
    with (String lbrace (String (dchar k) (chars (dchar k) j))).
  cbn [iscan_str]. unfold istep at 2. cbn [istep_at].
  change (ilead lbrace txt prev o) with (IBrace txt prev o).
  unfold istep at 1. cbn [istep_at]. unfold ibrace_step_at.
  rewrite (dstyle_of_dchar k Hen).
  rewrite (iscan_chars_marked j k 0 txt o) by lia.
  cbn [plus]. unfold idelim_marked.
  assert (Hw : Nat.ltb (S j) (dwidth k) = true) by (apply Nat.ltb_lt; lia).
  destruct next as [c|]; cbn [settles].
  - unfold istep. cbn [istep_at]. rewrite Hw.
    assert (Ascii.eqb c (dchar k) = false) as Hd
      by (apply Ascii.eqb_neq, (Hr c eq_refl)).
    rewrite Hd. reflexivity.
  - cbn [rres iresolve]. rewrite Hw. reflexivity.
Qed.

(* `]` that closes nothing: the byte after it is read as usual. *)
Local Lemma tok_rbrack_text : forall txt prev o next,
  (forall c, next = Some c ->
     (Ascii.eqb c lparen || Ascii.eqb c lbrack || (Ascii.eqb c lbrace && inline_attrs_enabled))%bool
     = true -> bclose (flush_text txt o) = None) ->
  settles (iscan_str (one rbrack) (IText false txt prev o))
          (IText false (txt ++ one rbrack) (Some rbrack) o) next.
Proof.
  intros txt prev o next H. cbn [iscan_str one]. unfold istep at 1. cbn [istep_at].
  change (ilead rbrack txt prev o) with (IClosed txt o).
  destruct next as [c|]; cbn [settles].
  - unfold istep at 1. cbn [istep_at].
    destruct (Ascii.eqb c lparen || Ascii.eqb c lbrack || (Ascii.eqb c lbrace && inline_attrs_enabled))%bool eqn:E.
    + change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s (tval txt) o)
        with (flush_text txt o).
      rewrite (H c eq_refl E). reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

(*
The tokens' text
----------------

A line's tokens spell the line, and parens are counted the same over
either.
*)

Fixpoint sdrop (n : nat) (s : string) : string :=
  match n, s with
  | S m, String _ r => sdrop m r
  | _, _ => s
  end.

Fixpoint toks_text (ts : list token) : string :=
  match ts with [] => "" | t :: r => tok_text t ++ toks_text r end.

Local Lemma prefix_sdrop : forall a s,
  prefix a s = true -> s = a ++ sdrop (String.length a) s.
Proof.
  induction a as [|x a IH]; intros s H; [reflexivity|].
  destruct s as [|y s]; [discriminate|]. cbn [prefix] in H.
  destruct (ascii_dec x y) as [->|]; [|discriminate].
  cbn. rewrite <- (IH s H). reflexivity.
Qed.

Local Lemma length_chars : forall c m, String.length (chars c m) = m.
Proof.
  intros c m. induction m as [|m IH]; [reflexivity|]. cbn. rewrite IH.
  reflexivity.
Qed.

Local Lemma lex_text : forall s prev skip, toks_text (lex prev skip s) = sdrop skip s.
Proof.
  induction s as [|c rest IH]; intros prev skip; [destruct skip; reflexivity|].
  cbn [lex]. destruct skip as [|skip]; [|apply IH]. cbn [sdrop].
  assert (One : forall t p, tok_text t = one c ->
            toks_text (t :: lex p 0 rest) = String c rest).
  { intros t p E. cbn [toks_text]. rewrite E, IH. reflexivity. }
  destruct (Ascii.eqb c lbrack) eqn:Elk.
  { apply Ascii.eqb_eq in Elk. subst c. apply One. reflexivity. }
  destruct (Ascii.eqb c rbrack) eqn:Erk.
  { apply Ascii.eqb_eq in Erk. subst c.
    destruct (starts_with lparen rest); [|destruct (starts_with lbrack rest)];
      apply One; reflexivity. }
  destruct (Ascii.eqb c lbrace) eqn:Elb.
  { apply Ascii.eqb_eq in Elb. subst c.
    destruct rest as [|d r]; [apply One; reflexivity|].
    destruct (dstyle_of d) as [k|]; [|apply One; reflexivity].
    destruct (prefix (dtoken k) (String d r)) eqn:P; [|apply One; reflexivity].
    cbn [toks_text tok_text]. rewrite IH.
    rewrite (prefix_sdrop _ _ P) at 2. unfold dtoken at 3. rewrite length_chars.
    reflexivity. }
  destruct (dstyle_of c) as [k|]; [|apply One; reflexivity].
  destruct (prefix (dtoken k) (String c rest)) eqn:P; [|apply One; reflexivity].
  pose proof (prefix_sdrop _ _ P) as E. unfold dtoken at 2 in E. rewrite length_chars in E.
  destruct (dwidth k) as [|w] eqn:Ew; [destruct (dwidth_nonzero k Ew)|].
  cbn [sdrop pred] in *.
  destruct (at_rbrace (get (S w) (String c rest))) eqn:Ar.
  - cbn [toks_text tok_text]. rewrite IH. rewrite E, append_assoc. f_equal.
    cbn [get] in Ar. clear -Ar. revert rest Ar. induction w as [|w IHw]; intros rest Ar.
    + destruct rest as [|d r]; [discriminate|]. cbn in Ar. apply Ascii.eqb_eq in Ar.
      subst d. reflexivity.
    + destruct rest as [|d r]; [discriminate|]. cbn [get sdrop] in *. apply IHw, Ar.
  - cbn [toks_text tok_text]. rewrite IH. exact (eq_sym E).
Qed.

(* A delimiter token of the rows here, whose character is not a paren. *)
Definition tok_plain (t : token) : Prop :=
  match t with
  | TDelim k _ _ _ =>
      self_row k = true /\ Ascii.eqb (dchar k) lparen = false
      /\ Ascii.eqb (dchar k) rparen = false
  | _ => True
  end.

Local Lemma over_alphabet_cons : forall c s,
  over_alphabet (String c s) = true ->
  in_alphabet c = true /\ follow_ok c s = true /\ over_alphabet s = true.
Proof.
  intros c s H. cbn [over_alphabet] in H. apply andb_true_iff in H as [H H3].
  apply andb_true_iff in H as [H1 H2]. auto.
Qed.

Local Lemma alphabet_plain : forall c k b1 b2 b3,
  in_alphabet c = true -> dstyle_of c = Some k -> tok_plain (TDelim k b1 b2 b3).
Proof.
  intros c k b1 b2 b3 Hc Hd. pose proof (dstyle_of_char c k Hd) as E. subst c.
  split; [exact (alphabet_self _ k Hc Hd)|exact (alphabet_paren _ k Hc Hd)].
Qed.

Local Lemma lex_plain : forall s prev skip,
  over_alphabet s = true -> Forall tok_plain (lex prev skip s).
Proof.
  induction s as [|c rest IH]; intros prev skip Ha; [constructor|].
  apply over_alphabet_cons in Ha as (Hc & _ & Hr).
  cbn [lex]. destruct skip as [|skip]; [|apply IH, Hr].
  destruct (Ascii.eqb c lbrack); [constructor; [exact Logic.I|apply IH, Hr]|].
  destruct (Ascii.eqb c rbrack).
  { constructor; [|apply IH, Hr].
    destruct (starts_with lparen rest); [|destruct (starts_with lbrack rest)]; exact Logic.I. }
  destruct (Ascii.eqb c lbrace).
  { destruct rest as [|d r]; [constructor; [exact Logic.I|apply IH, Hr]|].
    destruct (dstyle_of d) as [k|] eqn:Hd; [|constructor; [exact Logic.I|apply IH, Hr]].
    destruct (prefix (dtoken k) (String d r)); constructor;
      try exact Logic.I; try (apply IH, Hr).
    apply over_alphabet_cons in Hr as (Hdc & _). exact (alphabet_plain d k _ _ _ Hdc Hd). }
  destruct (dstyle_of c) as [k|] eqn:Hd; [|constructor; [exact Logic.I|apply IH, Hr]].
  destruct (prefix (dtoken k) (String c rest)); [|constructor; [exact Logic.I|apply IH, Hr]].
  destruct (at_rbrace _); (constructor; [exact (alphabet_plain c k _ _ _ Hc Hd)|apply IH, Hr]).
Qed.

Local Lemma pdepth_chars : forall c n d,
  Ascii.eqb c lparen = false -> Ascii.eqb c rparen = false ->
  pdepth d (chars c n) = Some d.
Proof.
  intros c n d H1 H2. induction n as [|n IH]; [reflexivity|].
  cbn [chars pdepth]. unfold pstep_byte. rewrite H1, H2. exact IH.
Qed.

Local Lemma delim_pdepth : forall k mr op cl depth,
  tok_plain (TDelim k mr op cl) ->
  pdepth depth (tok_text (TDelim k mr op cl)) = Some depth.
Proof.
  intros k mr op cl depth (_ & H1 & H2).
  destruct mr; [destruct op|]; cbn [tok_text]; unfold dtoken;
    rewrite ?pdepth_app; cbn [one append pdepth];
    rewrite ?(pdepth_chars _ _ _ H1 H2); try reflexivity.
  change (pstep_byte lbrace depth) with (Some depth). cbn.
  apply pdepth_chars; assumption.
Qed.

Local Lemma paren_close_cons : forall t depth i rest,
  tok_plain t ->
  paren_close depth i (t :: rest)
  = match pdepth depth (tok_text t) with
    | Some d' => paren_close d' (S i) rest
    | None => Some i
    end.
Proof.
  intros t depth i rest Hp. destruct t as [c| |k mr op cl| |b]; try reflexivity.
  - cbn [paren_close tok_text pdepth one]. unfold pstep_byte.
    destruct (Ascii.eqb c lparen); [reflexivity|].
    destruct (Ascii.eqb c rparen); [destruct depth; reflexivity|reflexivity].
  - rewrite (delim_pdepth k mr op cl depth Hp). reflexivity.
Qed.

(* Only the `)` that balances ends a destination. *)
Local Lemma pdepth_none : forall t depth,
  tok_plain t -> pdepth depth (tok_text t) = None ->
  tok_text t = one rparen /\ depth = 0.
Proof.
  intros t depth Hp H. destruct t as [c| |k mr op cl| |b]; try discriminate H.
  - cbn [tok_text one pdepth] in H. unfold pstep_byte in H.
    destruct (Ascii.eqb c lparen); [discriminate|].
    destruct (Ascii.eqb c rparen) eqn:E; [|discriminate].
    apply Ascii.eqb_eq in E. subst c. destruct depth; [split; reflexivity|discriminate].
  - rewrite (delim_pdepth k mr op cl depth Hp) in H. discriminate.
Qed.

(* Tokens that leave a paren open: so do their bytes. *)
Local Lemma paren_close_app : forall toks depth i rest,
  Forall tok_plain toks -> paren_close depth i (toks ++ rest) = None ->
  exists d', pdepth depth (toks_text toks) = Some d'
             /\ paren_close d' (i + length toks) rest = None.
Proof.
  induction toks as [|t toks IH]; intros depth i rest F H.
  - exists depth. rewrite Nat.add_0_r. split; [reflexivity|exact H].
  - apply Forall_cons_iff in F as [Ft F]. cbn [app] in H.
    rewrite (paren_close_cons t depth i _ Ft) in H.
    cbn [toks_text length]. rewrite pdepth_app.
    destruct (pdepth depth (tok_text t)) as [d1|]; [|discriminate].
    destruct (IH d1 (S i) rest F H) as (d' & E1 & E2). exists d'.
    rewrite <- Nat.add_succ_comm. split; assumption.
Qed.

(*
Line ends
---------

A break or the paragraph's end reads a state as resolved, through the
destination readings.
*)

Local Lemma iresolve_shape : forall st : iscan,
  (exists txt prev o, iresolve st = IText false txt prev o) \/ iresolve st = st.
Proof.
  intros st. destruct st; try (right; reflexivity); try (left; cbn [iresolve]; eauto; fail).
  left. cbn [iresolve]. destruct (Nat.ltb (S extra) (dwidth k)); [eauto|].
  destruct marked; [unfold idelim_open_marked; eauto|].
  unfold idelim_resolve, idelim_done.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    repeat match goal with |- context [match ?b with Some _ => _ | None => _ end] => destruct b end;
    eauto.
Qed.

Local Lemma ifinish_ostate_rres : forall st : iscan,
  ifinish_ostate (rres st) = ifinish_ostate st.
Proof.
  induction st; try reflexivity.
  - destruct (iresolve_shape (IDelim k extra txt before marked o)) as [(t & p & o' & E)|E];
      cbn [rres ifinish_ostate]; rewrite !E; cbn [ifinish_ostate]; rewrite ?E; reflexivity.
  - cbn [rres ifinish_ostate]. exact IHst.
Qed.

Local Lemma ifinish_rres : forall st : iscan, ifinish (rres st) = ifinish st.
Proof. intros st. unfold ifinish, ifinish_rev. rewrite ifinish_ostate_rres. reflexivity. Qed.

Local Lemma ibreak_rres : forall a (st : iscan), ibreak_at a (rres st) = ibreak_at a st.
Proof.
  intros a st. revert a. induction st; intros a; try reflexivity.
  - destruct (iresolve_shape (IDelim k extra txt before marked o)) as [(t & p & o' & E)|E];
      cbn [rres ibreak_at]; rewrite !E; cbn [ibreak_at]; rewrite ?E; reflexivity.
  - cbn [rres ibreak_at]. rewrite IHst. reflexivity.
Qed.

Local Lemma ifinish_wrap : forall ws core, ifinish (wrap ws core) = ifinish core.
Proof.
  intros ws core. unfold ifinish, ifinish_rev.
  induction ws as [|w ws IH]; [reflexivity|]. cbn [wrap ifinish_ostate]. exact IH.
Qed.

Local Lemma ibreak_wrap : forall ws core,
  ibreak (wrap ws core) = wrap (map (wl_after nl) ws) (ibreak core).
Proof.
  intros ws core. unfold ibreak. induction ws as [|w ws IH]; [reflexivity|].
  cbn [wrap map ibreak_at]. rewrite IH. destruct w as [k o d dst o'].
  unfold wl_after. cbn. reflexivity.
Qed.

(*
Brackets put back as text
-------------------------
*)

Local Lemma bflat_sim : forall l txt o v,
  clean l -> sim v txt o ->
  exists txt' o', bflat (map mk l) txt o = (txt', o') /\ sim (pv_add_all l v) txt' o'.
Proof.
  induction l as [|x l IH]; intros txt o v Hl Hs; [exists txt, o; split; [reflexivity|exact Hs]|].
  apply Forall_cons_iff in Hl as [Hx Hl].
  destruct (str_view x) as [[s ->]|Hn].
  - cbn [map mk bflat pv_add_all]. apply IH; [exact Hl|]. apply sim_text; [exact Hs|].
    destruct s; [contradiction|reflexivity].
  - assert (E : bflat (map mk (x :: l)) txt o
                = bflat (map mk l) "" (oemit (mk x) (flush_text txt o)))
      by (destruct x; [destruct (Hn _ eq_refl)|..]; reflexivity).
    rewrite E. cbn [pv_add_all]. apply IH; [exact Hl|].
    destruct Hs as (v0 & cm & -> & Ht & ->).
    rewrite (flush_view cm txt v0 Ht), (oemit_view cm x _ Hn).
    exists (pv_add x (add_text txt v0)), cm.
    split; [reflexivity|]. split; [apply top_add_nonstr, Hn|reflexivity].
Qed.

(* Taking back the text before a bracket. *)
Local Lemma opop_sim : forall cm v,
  normal (top_of v) -> clean (top_of v) ->
  exists pre o1, opop_str (oview cm v) = (pre, o1) /\ sim v pre o1.
Proof.
  intros cm [stk out md] Hn Hc.
  assert (Tail : forall s l, normal (Str s :: l) -> starts_text l = false).
  { intros s [|y l] H; [reflexivity|]. destruct H as [[H|H] _]; [discriminate|].
    destruct y; [discriminate|..]; reflexivity. }
  assert (Head : forall s l, clean (Str s :: l) -> nonempty_str s = true).
  { intros s l H. apply Forall_cons_iff in H as [H _]. destruct s; [contradiction|reflexivity]. }
  assert (Cons : forall s l, starts_text l = false -> xsnoc (Str s) l = Str s :: l)
    by (intros s [|[] l] Hl; try reflexivity; discriminate).
  destruct stk as [|f rest]; cbn [top_of pv_stk pv_out fcontent] in Hn, Hc.
  - destruct out as [|x l].
    + exists "", (oview cm (PView [] [] md)). split; [reflexivity|].
      exists (PView [] [] md), cm. split; [reflexivity|]. split; reflexivity.
    + destruct (str_view x) as [[s ->]|Hx].
      * exists s, (oview cm (PView [] l md)). split; [reflexivity|].
        exists (PView [] l md), cm. split; [reflexivity|].
        split; [exact (Tail s l Hn)|].
        unfold add_text. rewrite (Head s l Hc). unfold pv_add. cbn [pv_stk pv_out pv_mode].
        rewrite (Cons s l (Tail s l Hn)). reflexivity.
      * exists "", (oview cm (PView [] (x :: l) md)).
        split; [destruct x; [destruct (Hx _ eq_refl)|..]; reflexivity|].
        exists (PView [] (x :: l) md), cm. split; [reflexivity|].
        split; [destruct x; [destruct (Hx _ eq_refl)|..]; reflexivity|reflexivity].
  - destruct (fcontent f) as [|x l] eqn:Ef.
    + exists "", (oview cm (PView (f :: rest) out md)).
      split; [unfold opop_str, oview; cbn [os_stk map pv_stk]; rewrite fr_out_oframe, Ef; reflexivity|].
      exists (PView (f :: rest) out md), cm. split; [reflexivity|].
      split; [cbn [top_of pv_stk]; rewrite Ef; reflexivity|reflexivity].
    + destruct (str_view x) as [[s ->]|Hx].
      * exists s, (oview cm (PView (fset f l :: rest) out md)).
        split; [destruct f as [p [k mr|] c|d c]; cbn [fcontent] in Ef; subst c; reflexivity|].
        exists (PView (fset f l :: rest) out md), cm. split; [reflexivity|].
        assert (El : fcontent (fset f l) = l) by (destruct f; reflexivity).
        split; [cbn [top_of pv_stk]; rewrite El; exact (Tail s l Hn)|].
        unfold add_text. rewrite (Head s l Hc). unfold pv_add. cbn [pv_stk pv_out pv_mode].
        rewrite El, (Cons s l (Tail s l Hn)).
        destruct f; cbn [fset fcontent] in *; subst; reflexivity.
      * exists "", (oview cm (PView (f :: rest) out md)).
        split; [unfold opop_str, oview; cbn [os_stk map pv_stk]; rewrite fr_out_oframe, Ef;
                destruct x; [destruct (Hx _ eq_refl)|..]; reflexivity|].
        exists (PView (f :: rest) out md), cm. split; [reflexivity|].
        split; [cbn [top_of pv_stk]; rewrite Ef;
                destruct x; [destruct (Hx _ eq_refl)|..]; reflexivity|reflexivity].
Qed.

Local Lemma pv_add_all_app : forall a b v,
  pv_add_all (a ++ b) v = pv_add_all b (pv_add_all a v).
Proof. induction a as [|x a IH]; intros b v; [reflexivity|]. cbn [app pv_add_all]. apply IH. Qed.

Local Lemma self_frames_add_all : forall l v,
  self_frames (pv_stk v) -> self_frames (pv_stk (pv_add_all l v)).
Proof.
  induction l as [|x l IH]; intros v B; [exact B|]. cbn [pv_add_all].
  apply IH, self_frames_add, B.
Qed.

Local Lemma sim_finish : forall v txt prev o,
  sim v txt o -> self_frames (pv_stk v) ->
  ifinish (IText false txt prev o) = map mk (List.rev (pflatten_go [] (pv_stk v) (pv_out v))).
Proof.
  intros v txt prev o (v0 & cm & -> & Ht & ->) B. apply ifinish_view; [|exact Ht].
  unfold add_text in B. destruct (nonempty_str txt); [exact (self_frames_add_inv _ _ B)|exact B].
Qed.

(* A reference label the paragraph ends in. *)
Local Lemma ref_finish : forall cm v b kids d open label,
  pv_mode v = PMRegion b kids d None label -> self_frames (pv_stk v) ->
  normal (top_of v) -> clean (top_of v) -> clean kids ->
  ifinish (IReference (map mk kids) false open label (oview cm v))
  = map mk (List.rev (pflatten v)).
Proof.
  intros cm v b kids d open label Em B Hn Hc Hk.
  destruct (opop_sim cm v Hn Hc) as (pre & o1 & Ep & S1).
  pose proof (sim_text _ _ _ (one lbrack) S1 eq_refl) as S2.
  destruct (bflat_sim kids _ _ _ Hk S2) as (txt & o2 & Eb & S3).
  pose proof (sim_text _ _ _ (one rbrack ++ one lbrack ++ label) S3 eq_refl) as S4.
  unfold pflatten, pfinish. rewrite Em.
  change (Str (one lbrack) :: kids ++ [Str (one rbrack ++ one lbrack ++ label)])%list
    with ([Str (one lbrack)] ++ kids ++ [Str (one rbrack ++ one lbrack ++ label)])%list.
  rewrite !pv_add_all_app. cbn [pv_add_all].
  rewrite <- (sim_finish _ _ None _ S4).
  2: { apply self_frames_add, self_frames_add_all, self_frames_add, B. }
  unfold ifinish, ifinish_rev. cbn [ifinish_ostate iresolve ifinish_ostate_flat].
  unfold bref_lit, bclosed_lit. rewrite Ep.
  change (tof (pre ++ bracket_open false)) with (pre ++ one lbrack).
  rewrite Eb. cbn [tval tpush]. rewrite append_assoc. reflexivity.
Qed.

(*
Tidy contents
-------------

Every content of the view, the outermost too, is normal and clean.
*)

Definition tidy (v : pview) : Prop :=
  normal (pv_out v) /\ clean (pv_out v) /\ frames_normal v /\ frames_clean v.

Local Lemma pv_add_out : forall x v,
  pv_out (pv_add x v) = pv_out v \/ pv_out (pv_add x v) = xsnoc x (pv_out v).
Proof. intros x [[|f rest] out md]; [right|left]; reflexivity. Qed.

Local Lemma pstep_out : forall ts n t v,
  pv_out (pstep ts n t v) = pv_out v
  \/ exists x, x <> Str "" /\ pv_out (pstep ts n t v) = xsnoc x (pv_out v).
Proof.
  intros ts n t v.
  assert (Add : forall x v', x <> Str "" -> pv_out v' = pv_out v ->
            pv_out (pv_add x v') = pv_out v
            \/ exists y, y <> Str "" /\ pv_out (pv_add x v') = xsnoc y (pv_out v)).
  { intros x v' Hx E. destruct (pv_add_out x v') as [H|H]; rewrite H, E;
      [left; reflexivity|right; exists x; split; [exact Hx|reflexivity]]. }
  assert (Txt : forall t', Str (tok_text t') <> Str "")
    by (intros t' E; injection E as E; exact (tok_text_ne t' E)).
  assert (Open : forall i k op t',
            pv_out (popen i k op (tok_text t') v) = pv_out v
            \/ exists y, y <> Str "" /\ pv_out (popen i k op (tok_text t') v) = xsnoc y (pv_out v)).
  { intros i k [|] t'; [left; reflexivity|apply Add; [apply Txt|reflexivity]]. }
  unfold pstep. destruct (pv_mode v) as [|b kids d e txt].
  2: { destruct (match e with Some e' => Nat.eqb n e' | None => false end);
         [apply Add; [apply region_node_nonstr|reflexivity]|left; reflexivity]. }
  destruct t as [c| |k mr op cl| |b].
  - apply Add; [discriminate|reflexivity].
  - apply Add; [discriminate|reflexivity].
  - destruct (if cl then pick (KDelim k mr) (pv_live v) else PNone) as [p below| |];
      [|apply Add; [apply Txt|reflexivity]|apply Open].
    destruct (Nat.ltb (S p) n); [|apply Open].
    destruct (pclose_go (KDelim k mr) [] (pv_stk v)) as [[content rest]|]; [|left; reflexivity].
    apply Add; [apply dnode_nonstr|reflexivity].
  - apply Open.
  - destruct (pick KBracket (pv_live v));
      destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|];
      try (apply Add; [apply Txt|reflexivity]).
    destruct (region_end ts n b); [left; reflexivity|]. destruct b; left; reflexivity.
Qed.

Local Lemma pstep_tidy : forall ts n t v, tidy v -> tidy (pstep ts n t v).
Proof.
  intros ts n t v (Hn & Hc & Fn & Fc).
  split; [|split; [|split; [apply pstep_normal, Fn|apply pstep_clean, Fc]]];
    destruct (pstep_out ts n t v) as [E|(x & Hx & E)]; rewrite E; try assumption.
  - apply normal_xsnoc, Hn.
  - apply clean_xsnoc; assumption.
Qed.

Local Lemma tidy_top : forall v, tidy v -> normal (top_of v) /\ clean (top_of v).
Proof.
  intros [[|f rest] out md] (Hn & Hc & Fn & Fc); [split; assumption|].
  apply Forall_cons_iff in Fn as [Fn _]. apply Forall_cons_iff in Fc as [Fc _].
  split; assumption.
Qed.

(*
Lexing a line
-------------
*)

Local Lemma lex_skip : forall j x c rest,
  lex x j (chars c j ++ rest)
  = match j with O => lex x 0 rest | S _ => lex (Some c) 0 rest end.
Proof.
  induction j as [|j IH]; intros x c rest; [reflexivity|].
  cbn [chars append lex]. rewrite IH. destruct j; reflexivity.
Qed.

(* Skipping a token and the byte after it. *)
Local Lemma lex_skip_last : forall j x c d r,
  lex x (S j) (chars c j ++ String d r) = lex (Some d) 0 r.
Proof.
  induction j as [|j IH]; intros x c d r; [reflexivity|].
  cbn [chars append lex]. apply IH.
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

Local Lemma get_chars : forall c n r, get n (chars c n ++ r) = get 0 r.
Proof. intros c n r; induction n as [|n IH]; [reflexivity|exact IH]. Qed.

Local Lemma dtoken_cons : forall k,
  exists w, dwidth k = S w /\ dtoken k = String (dchar k) (chars (dchar k) w).
Proof.
  intros k. destruct (dwidth k) as [|w] eqn:Ew; [destruct (dwidth_nonzero k Ew)|].
  exists w. split; [reflexivity|]. unfold dtoken. rewrite Ew. reflexivity.
Qed.

(* A row's character is no brace and no bracket. *)
Local Lemma dchar_plain : forall k,
  Ascii.eqb (dchar k) lbrace = false /\ Ascii.eqb (dchar k) rbrace = false
  /\ Ascii.eqb (dchar k) lbrack = false /\ Ascii.eqb (dchar k) rbrack = false.
Proof.
  intros k. destruct (dreserved_false (dchar k) (dchar_free k))
    as (_ & _ & H1 & H2 & H3 & H4 & _). auto.
Qed.

(* A token with no `}` after it. *)
Local Lemma lex_token : forall k prev rest,
  dstyle_of (dchar k) = Some k -> at_rbrace (get 0 rest) = false ->
  lex prev 0 (dtoken k ++ rest)
  = TDelim k false (bare_opens k && nonspace_at (get 0 rest)) (nonspace_at prev)
      :: lex (Some (dchar k)) 0 rest.
Proof.
  intros k prev rest Hk Hr. destruct (dchar_plain k) as (Hlb & _ & Hlk & Hrk).
  assert (Hpre : prefix (dtoken k) (dtoken k ++ rest) = true)
    by (apply prefix_chars; lia).
  destruct (dtoken_cons k) as (w & Ew & Ed).
  rewrite Ed at 1. cbn [append lex]. rewrite Hlk, Hrk, Hlb, Hk.
  replace (String (dchar k) (chars (dchar k) w ++ rest))
    with (dtoken k ++ rest)%string by (rewrite Ed; reflexivity).
  rewrite Hpre. unfold dtoken. rewrite Ew, get_chars, Hr. cbn [pred].
  rewrite lex_skip. destruct w; reflexivity.
Qed.

Local Lemma lex_marked_close : forall k prev r,
  dstyle_of (dchar k) = Some k ->
  lex prev 0 (dtoken k ++ String rbrace r)
  = TDelim k true false true :: lex (Some rbrace) 0 r.
Proof.
  intros k prev r Hk. destruct (dchar_plain k) as (Hlb & _ & Hlk & Hrk).
  assert (Hpre : prefix (dtoken k) (dtoken k ++ String rbrace r) = true)
    by (apply prefix_chars; lia).
  destruct (dtoken_cons k) as (w & Ew & Ed).
  rewrite Ed at 1. cbn [append lex]. rewrite Hlk, Hrk, Hlb, Hk.
  replace (String (dchar k) (chars (dchar k) w ++ String rbrace r))
    with (dtoken k ++ String rbrace r)%string by (rewrite Ed; reflexivity).
  rewrite Hpre. unfold dtoken. rewrite Ew, get_chars. cbn [get at_rbrace].
  rewrite Ascii.eqb_refl, lex_skip_last. reflexivity.
Qed.

Local Lemma lex_marked_open : forall k prev rest,
  dstyle_of (dchar k) = Some k ->
  lex prev 0 (String lbrace (dtoken k ++ rest))
  = TDelim k true true false :: lex (Some (dchar k)) 0 rest.
Proof.
  intros k prev rest Hk.
  assert (Hpre : prefix (dtoken k) (dtoken k ++ rest) = true)
    by (apply prefix_chars; lia).
  destruct (dtoken_cons k) as (w & Ew & Ed).
  cbn [lex]. change (Ascii.eqb lbrace lbrack) with false.
  change (Ascii.eqb lbrace rbrack) with false. rewrite Ascii.eqb_refl.
  rewrite Ed at 1. cbn [append]. rewrite Hk.
  replace (String (dchar k) (chars (dchar k) w ++ rest))
    with (dtoken k ++ rest)%string by (rewrite Ed; reflexivity).
  rewrite Hpre, Ew. rewrite Ed. cbn [append lex].
  rewrite lex_skip. destruct w; reflexivity.
Qed.

(* A row's character short of a token is text. *)
Local Lemma lex_short : forall k j prev rest,
  dstyle_of (dchar k) = Some k -> S j < dwidth k ->
  (forall d r, rest = String d r -> d <> dchar k) ->
  lex prev 0 (String (dchar k) (chars (dchar k) j ++ rest))
  = TText (dchar k) :: lex (Some (dchar k)) 0 (chars (dchar k) j ++ rest).
Proof.
  intros k j prev rest Hk Hj Hr. destruct (dchar_plain k) as (Hlb & _ & Hlk & Hrk).
  cbn [lex]. rewrite Hlk, Hrk, Hlb, Hk.
  change (String (dchar k) (chars (dchar k) j ++ rest))
    with (chars (dchar k) (S j) ++ rest)%string.
  unfold dtoken. rewrite (prefix_chars_short (dchar k) (dwidth k) (S j) rest Hj Hr).
  reflexivity.
Qed.

Local Lemma lex_partial : forall k j prev rest,
  dstyle_of (dchar k) = Some k -> j < dwidth k ->
  (forall d r, rest = String d r -> d <> dchar k) ->
  lex prev 0 (chars (dchar k) j ++ rest)
  = (repeat (TText (dchar k)) j
     ++ lex (if Nat.eqb j 0 then prev else Some (dchar k)) 0 rest)%list.
Proof.
  intros k j. induction j as [|j IH]; intros prev rest Hk Hj Hr;
    [reflexivity|].
  cbn [chars append]. rewrite (lex_short k j prev rest Hk Hj Hr).
  rewrite (IH (Some (dchar k)) rest Hk ltac:(lia) Hr).
  cbn [repeat app Nat.eqb]. destruct j; reflexivity.
Qed.

(* `{` before a run too short to be a token is text. *)
Local Lemma lex_lbrace_short : forall k j prev rest,
  dstyle_of (dchar k) = Some k -> S j < dwidth k ->
  (forall d r, rest = String d r -> d <> dchar k) ->
  lex prev 0 (String lbrace (chars (dchar k) (S j) ++ rest))
  = TText lbrace :: lex (Some lbrace) 0 (chars (dchar k) (S j) ++ rest).
Proof.
  intros k j prev rest Hk Hj Hr.
  cbn [lex]. change (Ascii.eqb lbrace lbrack) with false.
  change (Ascii.eqb lbrace rbrack) with false. rewrite Ascii.eqb_refl.
  cbn [chars append]. rewrite Hk.
  change (String (dchar k) (chars (dchar k) j ++ rest))
    with (chars (dchar k) (S j) ++ rest)%string.
  unfold dtoken. rewrite (prefix_chars_short (dchar k) (dwidth k) (S j) rest Hj Hr).
  reflexivity.
Qed.

(* A byte that is no row's character, no `{` and no bracket. *)
Local Lemma lex_byte : forall c prev rest,
  Ascii.eqb c lbrack = false -> Ascii.eqb c rbrack = false ->
  Ascii.eqb c lbrace = false -> dstyle_of c = None ->
  lex prev 0 (String c rest) = TText c :: lex (Some c) 0 rest.
Proof. intros c prev rest H1 H2 H3 H4. cbn [lex]. rewrite H1, H2, H3, H4. reflexivity. Qed.

(* A paren is no row's character on a line over the alphabet. *)
Local Lemma alphabet_paren_none : forall c,
  in_alphabet c = true -> (Ascii.eqb c lparen || Ascii.eqb c rparen)%bool = true ->
  dstyle_of c = None.
Proof.
  intros c H Hp. unfold in_alphabet in H. destruct (dstyle_of c); [|reflexivity].
  rewrite Hp in H. cbn in H. rewrite !andb_false_r in H. discriminate.
Qed.

Definition prev_ok (prev : option ascii) (s : string) : bool :=
  match prev with Some p => follow_ok p s | None => true end.

Local Lemma follow_ok_plain : forall p s,
  Ascii.eqb p lbrace = false -> Ascii.eqb p lbrack = false -> Ascii.eqb p rbrack = false ->
  follow_ok p s = true.
Proof. intros p s H1 H2 H3. unfold follow_ok. rewrite H1, H2, H3. reflexivity. Qed.

Local Lemma over_alphabet_app_r : forall a b,
  over_alphabet (a ++ b) = true -> over_alphabet b = true.
Proof.
  induction a as [|c a IH]; intros b H; [exact H|].
  apply over_alphabet_cons in H as (_ & _ & H). exact (IH b H).
Qed.

Local Lemma chars_add : forall c a b,
  chars c (a + b) = (chars c a ++ chars c b)%string.
Proof.
  intros c a b. induction a as [|a IH]; [reflexivity|]. cbn. rewrite IH.
  reflexivity.
Qed.

(* The first token of a line, its bytes, and the line after it. *)
Local Lemma lex_cons : forall s prev,
  over_alphabet s = true -> s <> "" ->
  exists t r prev1,
    s = (tok_text t ++ r)%string /\ lex prev 0 s = t :: lex prev1 0 r
    /\ prev_ok prev1 r = true /\ String.length r < String.length s
    /\ (forall c0, tok_text t = one c0 -> prev1 = Some c0).
Proof.
  intros s prev Ha Hne. destruct s as [|c s']; [contradiction|].
  pose proof Ha as Ha'. apply over_alphabet_cons in Ha' as (Hc & Hf & Hs').
  assert (One : forall t, tok_text t = one c ->
            lex prev 0 (String c s') = t :: lex (Some c) 0 s' ->
            exists t r prev1,
              String c s' = (tok_text t ++ r)%string
              /\ lex prev 0 (String c s') = t :: lex prev1 0 r
              /\ prev_ok prev1 r = true /\ String.length r < String.length (String c s')
              /\ (forall c0, tok_text t = one c0 -> prev1 = Some c0)).
  { intros t Et El. exists t, s', (Some c). rewrite Et. split; [reflexivity|].
    split; [exact El|]. split; [exact Hf|]. split; [cbn; lia|].
    intros c0 E0. injection E0 as <-. reflexivity. }
  destruct (Ascii.eqb c lbrack) eqn:Elk.
  { apply (One TOpen); [apply Ascii.eqb_eq in Elk; subst c; reflexivity|].
    cbn [lex]. rewrite Elk. reflexivity. }
  destruct (Ascii.eqb c rbrack) eqn:Erk.
  { assert (Ec : c = rbrack) by (apply Ascii.eqb_eq, Erk).
    cbn [lex] in One |- *. rewrite Elk, Erk in One |- *.
    destruct (starts_with lparen s'); [|destruct (starts_with lbrack s')];
      eapply One; try reflexivity; subst c; reflexivity. }
  destruct (Ascii.eqb c lbrace) eqn:Elb.
  { apply Ascii.eqb_eq in Elb. subst c.
    pose proof Hf as Hf'.
    unfold follow_ok in Hf. rewrite Ascii.eqb_refl in Hf. cbn in Hf.
    rewrite !andb_true_r in Hf.
    destruct s' as [|d s'']; [discriminate|].
    cbn [starts_row] in Hf. unfold is_delim in Hf.
    destruct (dstyle_of d) as [k|] eqn:Hd; [|discriminate].
    pose proof (dstyle_of_char d k Hd) as Ec. subst d.
    destruct (dchar_plain k) as (Hlb & Hrb & Hlk & Hrk).
    destruct (run_split (dchar k) (String (dchar k) s'')) as (j & rest0 & E & Hr).
    destruct j as [|j]; [cbn [chars append] in E; destruct (Hr _ _ (eq_sym E) eq_refl)|].
    destruct (Nat.le_gt_cases (dwidth k) (S j)) as [Hw|Hw].
    - assert (Es : String (dchar k) s'' = (dtoken k ++ (chars (dchar k) (S j - dwidth k) ++ rest0))%string).
      { rewrite E. unfold dtoken. rewrite <- append_assoc, <- chars_add.
        f_equal. f_equal. lia. }
      rewrite Es. exists (TDelim k true true false), (chars (dchar k) (S j - dwidth k) ++ rest0)%string,
        (Some (dchar k)).
      split; [reflexivity|]. split; [apply lex_marked_open, Hd|].
      split; [apply follow_ok_plain; assumption|].
      split; [cbn [String.length]; rewrite !length_append; lia|].
      intros c0 E0. cbn in E0. injection E0 as _ E0.
      pose proof (dtoken_nonempty k) as H. rewrite E0 in H. discriminate.
    - rewrite E. exists (TText lbrace), (chars (dchar k) (S j) ++ rest0)%string, (Some lbrace).
      split; [reflexivity|]. split; [apply lex_lbrace_short; assumption|].
      split; [cbn [prev_ok]; rewrite <- E; exact Hf'|]. split; [cbn; lia|].
      intros c0 E0. injection E0 as <-. reflexivity. }
  destruct (dstyle_of c) as [k|] eqn:Hd.
  2: { apply (One (TText c)); [reflexivity|]. apply lex_byte; assumption. }
  pose proof (dstyle_of_char c k Hd) as Ec. subst c.
  destruct (dtoken_cons k) as (w & Ew & Ed).
  destruct (run_split (dchar k) (String (dchar k) s')) as (j & rest0 & E & Hr).
  destruct j as [|j]; [cbn [chars append] in E; destruct (Hr _ _ (eq_sym E) eq_refl)|].
  destruct (Nat.le_gt_cases (dwidth k) (S j)) as [Hw|Hw].
  - set (rest := (chars (dchar k) (S j - dwidth k) ++ rest0)%string).
    assert (Es : String (dchar k) s' = (dtoken k ++ rest)%string).
    { rewrite E. unfold rest, dtoken. rewrite <- append_assoc, <- chars_add.
      f_equal. f_equal. lia. }
    rewrite Es. clearbody rest.
    assert (Hlen : String.length rest < String.length (dtoken k ++ rest)).
    { rewrite length_append, Ed. cbn [String.length]. lia. }
    destruct (at_rbrace (get 0 rest)) eqn:Hat.
    + destruct rest as [|e r]; [discriminate|]. cbn [get at_rbrace] in Hat.
      apply Ascii.eqb_eq in Hat. subst e.
      exists (TDelim k true false true), r, (Some rbrace).
      split; [cbn [tok_text]; rewrite append_assoc; reflexivity|].
      split; [apply lex_marked_close, Hd|]. split; [reflexivity|].
      split; [rewrite length_append in *; cbn [String.length] in *; lia|].
      intros c0 E0. cbn [tok_text] in E0. rewrite Ed in E0. cbn in E0.
      injection E0 as _ E0. destruct w; discriminate.
    + exists (TDelim k false (bare_opens k && nonspace_at (get 0 rest)) (nonspace_at prev)),
        rest, (Some (dchar k)).
      split; [reflexivity|]. split; [apply lex_token; assumption|].
      split; [apply follow_ok_plain; assumption|]. split; [exact Hlen|].
      intros c0 E0. cbn [tok_text] in E0. rewrite Ed in E0. injection E0 as <- _. reflexivity.
  - rewrite E. cbn [chars append]. exists (TText (dchar k)), (chars (dchar k) j ++ rest0)%string,
      (Some (dchar k)).
    split; [reflexivity|]. split; [apply lex_short; assumption|].
    split; [apply follow_ok_plain; assumption|]. split; [cbn; lia|].
    intros c0 E0. injection E0 as <-. reflexivity.
Qed.

(*
The simulation
==============

After `n` tokens the scanner is in the view of those tokens: in text
mode, in a reference label, or in a destination that the tokens ahead
close; inside one reading per destination that they do not close.
*)

Definition never (ts : list token) (n : nat) (w : wlayer) : Prop :=
  paren_close (wl_depth w) n (skipn n ts) = None.

Definition vinv (n : nat) (v : pview) : Prop := pv_ok n v /\ tidy v.

Definition linked (ts : list token) (n : nat) (v : pview) (prev : option ascii)
  (core : iscan) : Prop :=
  match pv_mode v with
  | PMNormal => exists txt o, core = IText false txt prev o /\ sim v txt o
  | PMRegion false kids d e label =>
      S d < n /\ e = rbrack_at n (skipn n ts) /\ clean kids
      /\ exists open cm, core = IReference (map mk kids) false open label (oview cm v)
  | PMRegion true kids d e dst =>
      S d < n /\ exists open depth sh cm,
        e = paren_close depth n (skipn n ts) /\ e <> None
        /\ core = IDest (map mk kids) false open false depth dst sh (oview cm v)
  end.

(* A line's bytes, scanned from a linked state, end in one. *)
Definition scanned (ts : list token) (n : nat) (v : pview) (ws : list wlayer)
  (core : iscan) (prev : option ascii) (s : string) : Prop :=
  exists ws' core' prev',
    rres (iscan_str s (wrap ws core)) = wrap ws' core'
    /\ vinv (n + length (lex prev 0 s)) (prun ts n (lex prev 0 s) v)
    /\ Forall (never ts (n + length (lex prev 0 s))) ws'
    /\ linked ts (n + length (lex prev 0 s)) (prun ts n (lex prev 0 s) v) prev' core'.

Definition scan_ih (ts after : list token) (len : nat) : Prop :=
  forall s prev n v ws core,
    String.length s <= len -> over_alphabet s = true -> prev_ok prev s = true ->
    skipn n ts = (lex prev 0 s ++ after)%list ->
    vinv n v -> Forall (never ts n) ws -> linked ts n v prev core ->
    scanned ts n v ws core prev s.

Local Lemma prun_app : forall ts a b i v,
  prun ts i (a ++ b) v = prun ts (i + length a) b (prun ts i a v).
Proof.
  intros ts. induction a as [|t a IH]; intros b i v; cbn [app prun length];
    [rewrite Nat.add_0_r; reflexivity|].
  rewrite IH. f_equal. lia.
Qed.

Local Lemma vinv_step : forall ts n t v,
  vinv n v -> tok_plain t -> vinv (S n) (pstep ts n t v).
Proof.
  intros ts n t v [Ok Ti] Hp. split; [|apply pstep_tidy, Ti].
  apply pv_ok_step; [exact Ok|]. intros k mr op cl ->. exact (proj1 Hp).
Qed.

Local Lemma vinv_prun : forall ts toks n v,
  vinv n v -> Forall tok_plain toks -> vinv (n + length toks) (prun ts n toks v).
Proof.
  intros ts. induction toks as [|t toks IH]; intros n v V F; cbn [prun length];
    [rewrite Nat.add_0_r; exact V|].
  apply Forall_cons_iff in F as [Ft F]. rewrite <- Nat.add_succ_comm.
  apply IH; [apply vinv_step; assumption|exact F].
Qed.

Local Lemma skipn_app_tail : forall (ts a b : list token) n,
  skipn n ts = (a ++ b)%list -> skipn (n + length a) ts = b.
Proof.
  intros ts a b n H. rewrite Nat.add_comm, <- skipn_skipn, H.
  rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Local Lemma layers_step : forall ts n ws toks rest,
  Forall (never ts n) ws -> skipn n ts = (toks ++ rest)%list -> Forall tok_plain toks ->
  Forall (fun w => pdepth (wl_depth w) (toks_text toks) <> None) ws
  /\ Forall (never ts (n + length toks)) (map (wl_after (toks_text toks)) ws).
Proof.
  intros ts n ws toks rest F Hs Fp. rewrite Forall_map.
  split; (eapply Forall_impl; [|exact F]); intros w Hw; unfold never in *;
    rewrite Hs in Hw;
    destruct (paren_close_app toks _ n rest Fp Hw) as (d' & E1 & E2).
  - rewrite E1. discriminate.
  - rewrite (skipn_app_tail ts toks rest n Hs). unfold wl_after. cbn [wl_depth].
    rewrite E1. exact E2.
Qed.

Local Lemma wrap_app : forall a b core, wrap (a ++ b) core = wrap a (wrap b core).
Proof. induction a as [|w a IH]; intros b core; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Local Lemma alphabet_no_bslash : forall s, over_alphabet s = true -> no_bslash s = true.
Proof.
  induction s as [|c s IH]; intros H; [reflexivity|].
  apply over_alphabet_cons in H as (Hc & _ & Hs). cbn [no_bslash]. rewrite (IH Hs), andb_true_r.
  unfold in_alphabet in Hc. apply andb_true_iff in Hc as [Hc _].
  apply andb_true_iff in Hc as [Hc _]. apply andb_true_iff in Hc as [_ Hc].
  destruct (Ascii.eqb c lbrace) eqn:E1; [apply Ascii.eqb_eq in E1; subst c; reflexivity|].
  destruct (Ascii.eqb c rbrace) eqn:E2; [apply Ascii.eqb_eq in E2; subst c; reflexivity|].
  destruct (Ascii.eqb c lbrack) eqn:E3; [apply Ascii.eqb_eq in E3; subst c; reflexivity|].
  destruct (Ascii.eqb c rbrack) eqn:E4; [apply Ascii.eqb_eq in E4; subst c; reflexivity|].
  cbn [orb] in Hc. apply negb_true_iff in Hc.
  rewrite (proj1 (dreserved_false c Hc)). reflexivity.
Qed.

(* One step of the simulation: a chunk of bytes and its tokens, then the
   rest of the line. *)
Local Lemma scan_advance : forall ts after len,
  scan_ih ts after len ->
  forall s prev n v ws core bytes rest toks prev1 extra core1,
    String.length s <= S len -> over_alphabet s = true ->
    skipn n ts = (lex prev 0 s ++ after)%list ->
    vinv n v -> Forall (never ts n) ws ->
    s = (bytes ++ rest)%string -> bytes <> "" ->
    lex prev 0 s = (toks ++ lex prev1 0 rest)%list -> toks_text toks = bytes ->
    prev_ok prev1 rest = true ->
    settles (iscan_str bytes core) (wrap extra core1) (get 0 rest) ->
    Forall (never ts (n + length toks)) extra ->
    linked ts (n + length toks) (prun ts n toks v) prev1 core1 ->
    scanned ts n v ws core prev s.
Proof.
  intros ts after len IH s prev n v ws core bytes rest toks prev1 extra core1
    Hl Ha Hsk V Fn Es Hne El Et Hp Hset Fe L.
  pose proof (lex_plain s prev 0 Ha) as Fp.
  destruct (layers_step ts n ws _ after Fn Hsk Fp) as [Hopen _].
  rewrite lex_text in Hopen. cbn [sdrop] in Hopen.
  rewrite El in Fp, Hsk. apply Forall_app in Fp as [Fp _].
  rewrite <- app_assoc in Hsk.
  destruct (layers_step ts n ws toks _ Fn Hsk Fp) as [_ Fn'].
  pose proof (skipn_app_tail ts toks _ n Hsk) as Hsk'.
  assert (Hlen : String.length rest <= len).
  { rewrite Es, length_append in Hl. destruct bytes; [contradiction|]. cbn in Hl. lia. }
  assert (Ha' : over_alphabet rest = true) by (rewrite Es in Ha; exact (over_alphabet_app_r _ _ Ha)).
  destruct (IH rest prev1 (n + length toks) (prun ts n toks v)
              (map (wl_after bytes) ws ++ extra)%list core1 Hlen Ha' Hp Hsk'
              (vinv_prun ts toks n v V Fp))
    as (ws' & core' & prev' & E & V' & Fn'' & L').
  { apply Forall_app. split; [rewrite <- Et; exact Fn'|exact Fe]. }
  { exact L. }
  exists ws', core', prev'.
  rewrite El, length_app, prun_app, Nat.add_assoc.
  split; [|split; [exact V'|split; [exact Fn''|exact L']]].
  rewrite <- E, wrap_app. rewrite Es at 1.
  apply (step_through bytes rest ws core (iscan_str bytes core) (wrap extra core1));
    [| |reflexivity|exact Hset].
  - rewrite <- Es. apply alphabet_no_bslash, Ha.
  - rewrite <- Es. exact Hopen.
Qed.

(*
The view's steps
----------------
*)

Local Lemma pstep_mode : forall ts n t v,
  pv_mode v = PMNormal -> (forall b, t <> TClose b) ->
  pv_mode (pstep ts n t v) = PMNormal.
Proof.
  intros ts n t v Em Ht. unfold pstep. rewrite Em.
  assert (Add : forall x, pv_mode (pv_add x v) = PMNormal)
    by (intros x; rewrite (proj2 (pv_add_live x v)); exact Em).
  assert (Open : forall i k op txt, pv_mode (popen i k op txt v) = PMNormal)
    by (intros i k [|] txt; [exact Em|apply Add]).
  destruct t as [c| |k mr op cl| |b]; try apply Add; try apply Open.
  - destruct (if cl then pick (KDelim k mr) (pv_live v) else PNone); try apply Add; try apply Open.
    destruct (Nat.ltb (S p) n); [|apply Open].
    destruct (pclose_go (KDelim k mr) [] (pv_stk v)) as [[content rest]|]; [|exact Em].
    rewrite (proj2 (pv_add_live _ _)). reflexivity.
  - destruct (Ht b eq_refl).
Qed.

Local Lemma prun_texts : forall ts c j n v txt o,
  pv_mode v = PMNormal -> sim v txt o ->
  sim (prun ts n (repeat (TText c) j) v) (txt ++ chars c j) o
  /\ pv_mode (prun ts n (repeat (TText c) j) v) = PMNormal.
Proof.
  intros ts c j. induction j as [|j IH]; intros n v txt o Em Hs; cbn [repeat prun].
  - rewrite append_empty_r. split; assumption.
  - destruct (IH (S n) (pstep ts n (TText c) v) (txt ++ one c) o) as [Hs' Em'].
    + apply pstep_mode; [exact Em|discriminate].
    + unfold pstep. rewrite Em. apply sim_text; [exact Hs|reflexivity].
    + change (chars c (S j)) with (one c ++ chars c j)%string.
      rewrite <- append_assoc. split; assumption.
Qed.

Local Lemma toks_text_repeat : forall c j, toks_text (repeat (TText c) j) = chars c j.
Proof. intros c j. induction j as [|j IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Local Lemma linked_normal : forall ts n v prev txt o,
  pv_mode v = PMNormal -> sim v txt o -> linked ts n v prev (IText false txt prev o).
Proof. intros ts n v prev txt o Em Hs. unfold linked. rewrite Em. exists txt, o. auto. Qed.

(* A `[` pushes the view's frame. *)
Local Lemma open_bracket_sim : forall n v txt o,
  sim v txt o -> sim (popen n KBracket true (one lbrack) v) "" (bpush false (flush_text txt o)).
Proof.
  intros n v txt o (v0 & cm & -> & Ht & ->).
  rewrite (flush_view cm txt v0 Ht). set (v := add_text txt v0).
  exists (popen n KBracket true (one lbrack) v), cm. split; [|split; reflexivity].
  reflexivity.
Qed.

(* A marked opener pushes the view's frame, with the bit the scanner
   records at its position. *)
Local Lemma open_marked_sim : forall n k b txt v o,
  pv_ok n v -> sim v txt o ->
  sim (popen n (KDelim k true) true (tok_text (TDelim k true true false)) v) ""
    (oopen_marked k b txt o).
Proof.
  intros n k b txt v o Ok (v0 & cm & -> & Ht & ->).
  pose proof Ok as (_ & Bd & _ & _).
  unfold oopen_marked.
  change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s
            (tval txt) (oview cm v0))
    with (flush_text txt (oview cm v0)).
  rewrite (flush_view cm txt v0 Ht).
  set (v := add_text txt v0) in *.
  set (cm' := fun p => if Nat.eqb p n then b else cm p).
  exists (popen n (KDelim k true) true (tok_text (TDelim k true true false)) v), cm'.
  split; [|split; reflexivity].
  rewrite (oview_ext cm cm' v).
  2: { intros f Hf. unfold cm'.
       assert (Hp : lpos (fitem f) < n) by (apply Bd, in_map, Hf).
       destruct (Nat.eqb (lpos (fitem f)) n) eqn:E; [apply Nat.eqb_eq in E; lia|reflexivity]. }
  unfold popen, oview, opush_at; cbn [pv_stk pv_out os_out os_stk os_word_start map oframe].
  unfold cm'. rewrite Nat.eqb_refl. reflexivity.
Qed.

Local Lemma pstep_close_found : forall ts n b v content rest,
  pv_mode v = PMNormal -> pclose_go KBracket [] (pv_stk v) = Some (content, rest) ->
  pstep ts n (TClose b) v
  = match region_end ts n b with
    | Some e => PView rest (pv_out v) (PMRegion b (List.rev content) n (Some e) "")
    | None =>
        if b then PView (PB n (xsnoc (Str (one rbrack)) content) :: rest) (pv_out v) PMNormal
        else PView rest (pv_out v) (PMRegion false (List.rev content) n None "")
    end.
Proof.
  intros ts n b v content rest Em Hc. unfold pstep. rewrite Em, Hc.
  destruct (pick KBracket (pv_live v)) eqn:P; [reflexivity| |];
    rewrite (pclose_none KBracket (pv_stk v) []) in Hc
      by (intros p' b'; unfold pv_live in P; rewrite P; discriminate);
    discriminate.
Qed.

Local Lemma pstep_close_none : forall ts n b v,
  pv_mode v = PMNormal -> pclose_go KBracket [] (pv_stk v) = None ->
  pstep ts n (TClose b) v = pv_add (Str (one rbrack)) v.
Proof.
  intros ts n b v Em Hc. unfold pstep. rewrite Em, Hc.
  destruct (pick KBracket (pv_live v)); reflexivity.
Qed.

(* A token inside a region joins its text. *)
Local Lemma region_stay : forall ts n t v b kids d e txt,
  pv_mode v = PMRegion b kids d e txt -> S d < n ->
  (forall e', e = Some e' -> n < e') ->
  pstep ts n t v = pv_setmode (PMRegion b kids d e (txt ++ tok_text t)) v.
Proof.
  intros ts n t v b kids d e txt Em Hd He. unfold pstep. rewrite Em.
  replace (match e with Some e' => Nat.eqb n e' | None => false end) with false.
  2: { destruct e as [e'|]; [|reflexivity]. symmetry. apply Nat.eqb_neq.
       specialize (He e' eq_refl). lia. }
  replace (Nat.eqb n (S d)) with false by (symmetry; apply Nat.eqb_neq; lia).
  reflexivity.
Qed.

(* The token after a bracket's closer opens the region and is not part
   of it. *)
Local Lemma region_first : forall ts n t rest out b kids e,
  (forall e', e = Some e' -> S n < e') ->
  pstep ts (S n) t (PView rest out (PMRegion b kids n e ""))
  = PView rest out (PMRegion b kids n e "").
Proof.
  intros ts n t rest out b kids e He. unfold pstep. cbn [pv_mode].
  replace (match e with Some e' => Nat.eqb (S n) e' | None => false end) with false.
  2: { destruct e as [e'|]; [|reflexivity]. symmetry. apply Nat.eqb_neq.
       specialize (He e' eq_refl). lia. }
  rewrite Nat.eqb_refl. reflexivity.
Qed.

Local Lemma region_close : forall ts n t v b kids d txt,
  pv_mode v = PMRegion b kids d (Some n) txt ->
  pstep ts n t v = pv_add (region_node b (map mk kids) txt) (pv_setmode PMNormal v).
Proof. intros ts n t v b kids d txt Em. unfold pstep. rewrite Em, Nat.eqb_refl. reflexivity. Qed.

Local Lemma region_close_linked : forall ts n v cm x prev,
  (forall s, x <> Str s) ->
  linked ts n (pv_add x (pv_setmode PMNormal v)) prev
    (IText false "" prev (oemit (mk x) (oview cm v))).
Proof.
  intros ts n v cm x prev Hx. apply linked_normal.
  - rewrite (proj2 (pv_add_live _ _)). reflexivity.
  - exists (pv_add x (pv_setmode PMNormal v)), cm.
    split; [exact (oemit_view cm x (pv_setmode PMNormal v) Hx)|].
    split; [apply top_add_nonstr, Hx|reflexivity].
Qed.

(*
The scanner's steps
-------------------
*)

(* A `]` before `(` or `[`, with a bracket open. *)
Local Lemma closed_step : forall cm v0 txt c2 content rest,
  starts_text (top_of v0) = false -> self_frames (pv_stk (add_text txt v0)) ->
  pclose_go KBracket [] (pv_stk (add_text txt v0)) = Some (content, rest) ->
  c2 = lparen \/ c2 = lbrack ->
  istep c2 (IClosed txt (oview cm v0))
  = let kids := map mk (List.rev content) in
    let o' := oview cm (PView rest (pv_out (add_text txt v0)) PMNormal) in
    if Ascii.eqb c2 lparen
    then IDest kids false null_span false 0 "" (idest_open kids false null_span o') o'
    else IReference kids false null_span "" o'.
Proof.
  intros cm v0 txt c2 content rest Ht B Hc Hc2.
  unfold istep. cbn [istep_at].
  change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s (tval txt) (oview cm v0))
    with (flush_text txt (oview cm v0)).
  rewrite (flush_view cm txt v0 Ht). unfold oview at 1.
  rewrite (bclose_embed cm _ _ B), Hc.
  destruct Hc2 as [-> | ->]; reflexivity.
Qed.

Local Lemma xapp_nil : forall c, xapp c [] = c.
Proof.
  induction c as [|x c IH]; [reflexivity|]. destruct c as [|y r]; [destruct x; reflexivity|].
  change (xapp (x :: y :: r) []) with (x :: xapp (y :: r) []). rewrite IH. reflexivity.
Qed.

Local Lemma pv_add_all_frame : forall l d c rest out md,
  pv_add_all l (PView (PB d c :: rest) out md)
  = PView (PB d (fold_left (fun a x => xsnoc x a) l c) :: rest) out md.
Proof. induction l as [|x l IH]; intros d c rest out md; [reflexivity|]. cbn [pv_add_all fold_left]. apply IH. Qed.

(* A destination that does not close: its ordinary reading, with the
   link text and `](` put back. *)
Local Lemma dest_open_sim : forall cm d content rest out,
  normal content -> clean content ->
  exists txt' o'',
    idest_open (map mk (List.rev content)) false null_span (oview cm (PView rest out PMNormal))
    = IText false (txt' ++ one rbrack ++ one lparen) (Some lparen) o''
    /\ sim (pv_add (Str (one lparen))
              (PView (PB d (xsnoc (Str (one rbrack)) content) :: rest) out PMNormal))
         (txt' ++ one rbrack ++ one lparen) o''.
Proof.
  intros cm d content rest out Hn Hc.
  set (vB := PView (PB d [] :: rest) out PMNormal).
  assert (S0 : sim vB "" (dpush false null_span (oview cm (PView rest out PMNormal)))).
  { exists vB, cm. split; [reflexivity|]. split; reflexivity. }
  assert (Hc' : clean (List.rev content)) by (apply Forall_rev, Hc).
  destruct (bflat_sim _ _ _ _ Hc' S0) as (txt' & o'' & Eb & S1).
  unfold vB in S1. rewrite pv_add_all_frame, (fold_xsnoc content [] Hn), xapp_nil in S1.
  exists txt', o''. split; [unfold idest_open; cbn [tnil]; rewrite Eb; reflexivity|].
  rewrite <- append_assoc.
  apply sim_text; [|reflexivity].
  exact (sim_text _ _ _ (one rbrack) S1 eq_refl).
Qed.

Fixpoint no_rbrack (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c rest => negb (Ascii.eqb c rbrack) && no_rbrack rest
  end.

Local Lemma iscan_ref : forall bytes kids im open label o,
  no_rbrack bytes = true ->
  iscan_str bytes (IReference kids im open label o)
  = IReference kids im open (label ++ bytes) o.
Proof.
  induction bytes as [|c bytes IH]; intros kids im open label o H;
    [rewrite append_empty_r; reflexivity|].
  cbn [no_rbrack] in H. apply andb_true_iff in H as [Hc H]. apply negb_true_iff in Hc.
  cbn [iscan_str]. unfold istep. cbn [istep_at]. rewrite Hc, IH by exact H.
  cbn [tpush]. rewrite append_assoc. reflexivity.
Qed.

Definition is_rb (t : token) : bool :=
  match t with TText c => Ascii.eqb c rbrack | TClose _ => true | _ => false end.

Local Lemma rbrack_at_cons : forall t i rest,
  rbrack_at i (t :: rest) = if is_rb t then Some i else rbrack_at (S i) rest.
Proof. intros [c| |k mr op cl| |b] i rest; reflexivity. Qed.

Local Lemma no_rbrack_chars : forall c n, Ascii.eqb c rbrack = false -> no_rbrack (chars c n) = true.
Proof. intros c n H. induction n as [|n IH]; [reflexivity|]. cbn. rewrite H, IH. reflexivity. Qed.

Local Lemma no_rbrack_app : forall a b, no_rbrack (a ++ b) = (no_rbrack a && no_rbrack b)%bool.
Proof. induction a as [|c a IH]; intros b; [reflexivity|]. cbn. rewrite IH. apply andb_assoc. Qed.

Local Lemma tok_rb : forall t,
  if is_rb t then tok_text t = one rbrack else no_rbrack (tok_text t) = true.
Proof.
  intros [c| |k mr op cl| |b]; try reflexivity.
  - cbn. destruct (Ascii.eqb c rbrack) eqn:E; [apply Ascii.eqb_eq in E; subst c; reflexivity|].
    reflexivity.
  - destruct (dchar_plain k) as (_ & _ & _ & Hrk).
    cbn [is_rb]. destruct mr; [destruct op|]; cbn [tok_text]; unfold dtoken;
      rewrite ?no_rbrack_app; cbn [one append no_rbrack];
      rewrite ?(no_rbrack_chars _ _ Hrk); reflexivity.
Qed.

Local Lemma iscan_dest : forall bytes kids open depth dst sh o d',
  no_bslash bytes = true -> pdepth depth bytes = Some d' ->
  iscan_str bytes (IDest kids false open false depth dst sh o)
  = IDest kids false open false d' (dst ++ bytes) (iscan_str bytes sh) o.
Proof.
  intros bytes kids open depth dst sh o d' Hb Hp.
  pose proof (iscan_wrap bytes [WL kids open depth dst o] sh Hb) as E.
  cbn [wrap map wl_after wl_kids wl_open wl_depth wl_dst wl_o] in E.
  rewrite Hp in E. apply E. constructor; [|constructor].
  cbn [wl_depth]. rewrite Hp. discriminate.
Qed.

Local Lemma no_nl_drop : forall s, no_nl s = drop_nl s.
Proof. induction s as [|c s IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Local Lemma skipn_cons_tail : forall (ts : list token) n t rest,
  skipn n ts = t :: rest -> skipn (S n) ts = rest.
Proof.
  intros ts n t rest H. pose proof (skipn_app_tail ts [t] rest n H) as E.
  cbn [length] in E. rewrite Nat.add_1_r in E. exact E.
Qed.

(*
A line
------
*)

Local Lemma linked_rres : forall ts n v prev core,
  linked ts n v prev core -> linked ts n v prev (rres core).
Proof.
  intros ts n v prev core L. unfold linked in *.
  destruct (pv_mode v) as [|[|] kids d e txt].
  - destruct L as (t & o & -> & Hs). exists t, o. split; [reflexivity|exact Hs].
  - destruct L as (Hd & open & depth & sh & cm & He & Hne & ->).
    split; [exact Hd|]. exists open, depth, (rres sh), cm. auto.
  - destruct L as (Hd & He & Hk & open & cm & ->). split; [exact Hd|].
    split; [exact He|]. split; [exact Hk|]. exists open, cm. reflexivity.
Qed.

Local Lemma scanned_nil : forall ts n v ws core prev,
  vinv n v -> Forall (never ts n) ws -> linked ts n v prev core ->
  scanned ts n v ws core prev "".
Proof.
  intros ts n v ws core prev V Fn L. exists ws, (rres core), prev.
  cbn [lex length prun iscan_str]. rewrite Nat.add_0_r, rres_wrap.
  split; [reflexivity|]. split; [exact V|]. split; [exact Fn|apply linked_rres, L].
Qed.

(* Right after a `[`, a `^` would mark a footnote and a `[` a wikilink;
   the alphabet has neither there. *)
Local Lemma note_free : forall prev c s' txt,
  prev_ok prev (String c s') = true -> c = lbrack \/ c = hat ->
  note_pos txt prev = false.
Proof.
  intros prev c s' txt H Hc. unfold note_pos.
  destruct prev as [p|]; [|apply andb_false_r].
  destruct (Ascii.eqb p lbrack) eqn:E; [|apply andb_false_r]. exfalso.
  cbn [prev_ok] in H. unfold follow_ok in H.
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
  rewrite E in H. destruct Hc as [-> | ->]; discriminate H.
Qed.

Local Lemma no_note_ok : forall prev c s' txt,
  prev_ok prev (String c s') = true -> no_note c txt prev = true.
Proof.
  intros prev c s' txt H. unfold no_note.
  destruct (Ascii.eqb c hat) eqn:E; [|reflexivity].
  apply Ascii.eqb_eq in E. subst c.
  rewrite (note_free prev hat s' txt H (or_intror eq_refl)). reflexivity.
Qed.

Local Lemma ilead_lbrack : forall txt prev o,
  note_pos txt prev = false ->
  ilead lbrack txt prev o = IText false "" (Some lbrack) (bpush false (flush_text txt o)).
Proof. intros txt prev o H. unfold ilead. cbn. rewrite H. reflexivity. Qed.

Local Lemma lex_rbrack : forall prev s',
  lex prev 0 (String rbrack s')
  = (if starts_with lparen s' then TClose true
     else if starts_with lbrack s' then TClose false else TText rbrack)
    :: lex (Some rbrack) 0 s'.
Proof. reflexivity. Qed.

Local Lemma scan_sim : forall ts after len, scan_ih ts after len.
Proof.
  intros ts after. induction len as [|len IH]; intros s prev n v ws core Hl Ha Hp Hsk V Fn L;
    destruct s as [|c s']; try (apply scanned_nil; assumption).
  { cbn [String.length] in Hl. lia. }
  pose proof (fun bytes rest toks prev1 extra core1 =>
                scan_advance ts after len IH (String c s') prev n v ws core
                  bytes rest toks prev1 extra core1 Hl Ha Hsk V Fn) as A.
  pose proof V as [Ok Ti]. pose proof Ok as (_ & _ & B & _).
  unfold linked in L. destruct (pv_mode v) as [|b kids d e txt] eqn:Em.
  2: { (* in a region *)
    destruct (lex_cons (String c s') prev Ha ltac:(discriminate))
      as (t & r & prev1 & Es & El & Hp1 & _ & Hlast).
    pose proof (lex_plain _ prev 0 Ha) as Fp. rewrite El in Fp.
    apply Forall_cons_iff in Fp as [Ft _].
    rewrite El in Hsk. cbn [app] in Hsk.
    pose proof (skipn_cons_tail ts n t _ Hsk) as Hsk1.
    assert (Hb : no_bslash (tok_text t) = true).
    { pose proof (alphabet_no_bslash _ Ha) as H. rewrite Es, no_bslash_app in H.
      apply andb_true_iff in H as [H _]. exact H. }
    assert (Step : forall core1,
              settles (iscan_str (tok_text t) core) core1 (get 0 r) ->
              linked ts (S n) (pstep ts n t v) prev1 core1 ->
              scanned ts n v ws core prev (String c s')).
    { intros core1 Hset L1.
      apply (A (tok_text t) r [t] prev1 [] core1);
        [exact Es|apply tok_text_ne|exact El|cbn; apply append_empty_r|exact Hp1|exact Hset
        |constructor|]. cbn [length prun]. rewrite Nat.add_1_r. exact L1. }
    destruct b.
    - destruct L as (Hd & open & depth & sh & cm & He & Hne & ->).
      rewrite Hsk, (paren_close_cons t depth n _ Ft) in He.
      destruct (pdepth depth (tok_text t)) as [d'|] eqn:Pd.
      + apply (Step (IDest (map mk kids) false open false d' (txt ++ tok_text t)
                      (iscan_str (tok_text t) sh) (oview cm v))).
        * rewrite (iscan_dest _ _ _ _ _ _ _ d' Hb Pd). apply settles_refl.
        * rewrite (region_stay ts n t v true kids d e txt Em Hd).
          2: { intros e' E'. rewrite E' in He. symmetry in He.
               apply Precedence.paren_close_ge in He. lia. }
          unfold linked. cbn [pv_setmode pv_mode]. split; [lia|].
          exists open, d', (iscan_str (tok_text t) sh), cm.
          rewrite Hsk1. split; [exact He|]. split; [exact Hne|reflexivity].
      + destruct (pdepth_none t depth Ft Pd) as [Et ->]. subst e.
        pose proof (Hlast _ Et) as ->.
        apply (Step (IText false "" (Some rparen)
                       (oemit (mk (region_node true (map mk kids) txt)) (oview cm v)))).
        * rewrite Et. unfold region_node. rewrite no_nl_drop. apply settles_refl.
        * rewrite (region_close ts n t v true kids d txt Em).
          apply region_close_linked, region_node_nonstr.
    - destruct L as (Hd & He & Hk & open & cm & ->).
      rewrite Hsk, rbrack_at_cons in He. pose proof (tok_rb t) as Hrb.
      destruct (is_rb t).
      + subst e. pose proof (Hlast _ Hrb) as ->.
        apply (Step (IText false "" (Some rbrack)
                       (oemit (mk (region_node false (map mk kids) txt)) (oview cm v)))).
        * rewrite Hrb. apply settles_refl.
        * rewrite (region_close ts n t v false kids d txt Em).
          apply region_close_linked, region_node_nonstr.
      + apply (Step (IReference (map mk kids) false open (txt ++ tok_text t) (oview cm v))).
        * rewrite (iscan_ref _ _ _ _ _ _ Hrb). apply settles_refl.
        * rewrite (region_stay ts n t v false kids d e txt Em Hd).
          2: { intros e' E'. rewrite E' in He. symmetry in He.
               apply Precedence.rbrack_at_ge in He. lia. }
          unfold linked. cbn [pv_setmode pv_mode]. split; [lia|].
          rewrite Hsk1. split; [exact He|]. split; [exact Hk|].
          exists open, cm. reflexivity. }
  (* in text mode *)
  destruct L as (txt & o & -> & Hs).
  pose proof Hs as (v0 & cm & Eo & Ht & Ev).
  pose proof Ha as Ha'. apply over_alphabet_cons in Ha' as (Hc & Hf & Hs').
  assert (Hn : no_note c txt prev = true) by exact (no_note_ok prev c s' txt Hp).
  assert (Nrm : forall bytes rest toks prev1 txt' o',
            String c s' = (bytes ++ rest)%string -> bytes <> "" ->
            lex prev 0 (String c s') = (toks ++ lex prev1 0 rest)%list ->
            toks_text toks = bytes -> prev_ok prev1 rest = true ->
            settles (iscan_str bytes (IText false txt prev o)) (IText false txt' prev1 o')
              (get 0 rest) ->
            pv_mode (prun ts n toks v) = PMNormal -> sim (prun ts n toks v) txt' o' ->
            scanned ts n v ws (IText false txt prev o) prev (String c s')).
  { intros bytes rest toks prev1 txt' o' H1 H2 H3 H4 H5 H6 H7 H8.
    apply (A bytes rest toks prev1 [] (IText false txt' prev1 o')); try assumption;
      [constructor|apply linked_normal; assumption]. }
  destruct (Ascii.eqb c lbrack) eqn:Elk.
  { apply Ascii.eqb_eq in Elk. subst c.
    apply (Nrm (one lbrack) s' [TOpen] (Some lbrack) "" (bpush false (flush_text txt o)));
      [reflexivity|discriminate|reflexivity|reflexivity|exact Hf| | |].
    - cbn [iscan_str one]. unfold istep. cbn [istep_at].
      rewrite (ilead_lbrack txt prev o (note_free prev lbrack s' txt Hp (or_introl eq_refl))).
      apply settles_refl.
    - cbn [prun]. apply pstep_mode; [exact Em|discriminate].
    - cbn [prun]. unfold pstep. rewrite Em. apply open_bracket_sim, Hs. }
  destruct (Ascii.eqb c rbrack) eqn:Erk.
  { apply Ascii.eqb_eq in Erk. subst c.
    assert (Txt : forall t, tok_text t = one rbrack ->
              lex prev 0 (String rbrack s') = t :: lex (Some rbrack) 0 s' ->
              pstep ts n t v = pv_add (Str (one rbrack)) v ->
              (forall c0, get 0 s' = Some c0 ->
                 (Ascii.eqb c0 lparen || Ascii.eqb c0 lbrack
                  || (Ascii.eqb c0 lbrace && inline_attrs_enabled))%bool = true ->
                 bclose (flush_text txt o) = None) ->
              scanned ts n v ws (IText false txt prev o) prev (String rbrack s')).
    { intros t Et El Ep Hb.
      apply (Nrm (one rbrack) s' [t] (Some rbrack) (txt ++ one rbrack) o);
        [reflexivity|discriminate|exact El|cbn; rewrite Et; reflexivity|exact Hf| | |].
      - apply tok_rbrack_text, Hb.
      - cbn [prun]. rewrite Ep, (proj2 (pv_add_live _ _)). exact Em.
      - cbn [prun]. rewrite Ep. apply sim_text; [exact Hs|reflexivity]. }
    assert (Hfl : flush_text txt o = oview cm v) by (rewrite Eo, Ev; apply flush_view, Ht).
    destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest']|] eqn:Hpc.
    2: { (* no bracket to close *)
      assert (Hb : bclose (flush_text txt o) = None).
      { rewrite Hfl. unfold oview. rewrite (bclose_embed cm _ _ B), Hpc. reflexivity. }
      destruct (starts_with lparen s') eqn:S1; [|destruct (starts_with lbrack s') eqn:S2].
      - apply (Txt (TClose true)); [reflexivity|rewrite lex_rbrack, S1; reflexivity
                                   |exact (pstep_close_none ts n true v Em Hpc)|intros; exact Hb].
      - apply (Txt (TClose false)); [reflexivity|rewrite lex_rbrack, S1, S2; reflexivity
                                    |exact (pstep_close_none ts n false v Em Hpc)|intros; exact Hb].
      - apply (Txt (TText rbrack)); [reflexivity|rewrite lex_rbrack, S1, S2; reflexivity
                                    |unfold pstep; rewrite Em; reflexivity|intros; exact Hb]. }
    destruct Ti as (_ & _ & Fnm & Fcl).
    destruct (pclose_go_normal KBracket (pv_stk v) [] content rest' Fnm Logic.I Hpc) as [Nc _].
    destruct (pclose_go_clean KBracket (pv_stk v) [] content rest' Fcl (Forall_nil _) Hpc)
      as [Cc _].
    set (kids := map mk (List.rev content)).
    set (o1 := oview cm (PView rest' (pv_out v) PMNormal)).
    assert (Hcl : forall c2, c2 = lparen \/ c2 = lbrack ->
              iscan_str (String rbrack (one c2)) (IText false txt prev o)
              = if Ascii.eqb c2 lparen
                then IDest kids false null_span false 0 "" (idest_open kids false null_span o1) o1
                else IReference kids false null_span "" o1).
    { intros c2 H2. cbn [iscan_str one]. unfold istep at 2. cbn [istep_at].
      change (ilead rbrack txt prev o) with (IClosed txt o). rewrite Eo.
      pose proof (closed_step cm v0 txt c2 content rest' Ht) as Hcs.
      rewrite <- Ev in Hcs. exact (Hcs B Hpc H2). }
    destruct (starts_with lparen s') eqn:S1.
    { (* a destination *)
      destruct s' as [|c2 r]; [discriminate|]. cbn [starts_with] in S1.
      apply Ascii.eqb_eq in S1. subst c2.
      apply over_alphabet_cons in Hs' as (Hc2 & _ & Hr').
      assert (El : lex prev 0 (String rbrack (String lparen r))
                   = ([TClose true; TText lparen] ++ lex (Some lparen) 0 r)%list).
      { rewrite lex_rbrack. cbn [starts_with app].
        rewrite (lex_byte lparen (Some rbrack) r eq_refl eq_refl eq_refl
                   (alphabet_paren_none lparen Hc2 eq_refl)). reflexivity. }
      assert (Hcp : iscan_str (String rbrack (one lparen)) (IText false txt prev o)
                    = IDest kids false null_span false 0 ""
                        (idest_open kids false null_span o1) o1)
        by exact (Hcl lparen (or_introl eq_refl)).
      clear Hcl. rename Hcp into Hcl.
      destruct (region_end ts n true) as [e|] eqn:R.
      - apply (A (String rbrack (one lparen)) r [TClose true; TText lparen] (Some lparen) []
                 (IDest kids false null_span false 0 "" (idest_open kids false null_span o1) o1));
          [reflexivity|discriminate|exact El|reflexivity|reflexivity
          |rewrite Hcl; apply settles_refl|constructor|].
        cbn [length prun]. rewrite (pstep_close_found ts n true v content rest' Em Hpc), R.
        rewrite region_first.
        2: { intros e' E'. injection E' as <-.
             pose proof (Precedence.region_end_ge ts n true e R). lia. }
        unfold linked. cbn [pv_mode]. split; [lia|].
        exists null_span, 0, (idest_open kids false null_span o1), cm.
        replace (n + 2) with (S (S n)) by lia.
        split; [symmetry; exact R|]. split; [discriminate|reflexivity].
      - destruct (dest_open_sim cm n content rest' (pv_out v) Nc Cc) as (txt' & o2 & Eo' & S').
        apply (A (String rbrack (one lparen)) r [TClose true; TText lparen] (Some lparen)
                 [WL kids null_span 0 "" o1]
                 (IText false (txt' ++ one rbrack ++ one lparen) (Some lparen) o2));
          [reflexivity|discriminate|exact El|reflexivity|reflexivity| | |].
        + rewrite Hcl. cbn [wrap wl_kids wl_open wl_depth wl_dst wl_o].
          fold kids o1 in Eo'. rewrite Eo'. apply settles_refl.
        + constructor; [|constructor]. unfold never. cbn [wl_depth length].
          replace (n + 2) with (S (S n)) by lia. exact R.
        + cbn [length prun]. rewrite (pstep_close_found ts n true v content rest' Em Hpc), R.
          apply linked_normal; [|exact S'].
          unfold pstep. cbn [pv_mode]. rewrite (proj2 (pv_add_live _ _)). reflexivity. }
    destruct (starts_with lbrack s') eqn:S2.
    { (* a reference label *)
      destruct s' as [|c2 r]; [discriminate|]. cbn [starts_with] in S2.
      apply Ascii.eqb_eq in S2. subst c2.
      apply over_alphabet_cons in Hs' as (_ & Hf2 & _).
      assert (Hcp : iscan_str (String rbrack (one lbrack)) (IText false txt prev o)
                    = IReference kids false null_span "" o1)
        by exact (Hcl lbrack (or_intror eq_refl)).
      clear Hcl. rename Hcp into Hcl.
      set (e := region_end ts n false).
      assert (Ev1 : pstep ts n (TClose false) v
                    = PView rest' (pv_out v) (PMRegion false (List.rev content) n e "")).
      { rewrite (pstep_close_found ts n false v content rest' Em Hpc). unfold e.
        destruct (region_end ts n false); reflexivity. }
      apply (A (String rbrack (one lbrack)) r [TClose false; TOpen] (Some lbrack) []
               (IReference kids false null_span "" o1));
        [reflexivity|discriminate|reflexivity|reflexivity|exact Hf2
        |rewrite Hcl; apply settles_refl|constructor|].
      cbn [length prun]. rewrite Ev1, region_first.
      2: { intros e' E'. pose proof (Precedence.region_end_ge ts n false e' E'). lia. }
      unfold linked. cbn [pv_mode]. split; [lia|].
      replace (n + 2) with (S (S n)) by lia.
      split; [reflexivity|]. split; [apply Forall_rev, Cc|].
      exists null_span, cm. reflexivity. }
    (* a `]` before anything else *)
    apply (Txt (TText rbrack)); [reflexivity|rewrite lex_rbrack, S1, S2; reflexivity
                                |unfold pstep; rewrite Em; reflexivity|].
    intros c0 E0 Hor. exfalso. destruct s' as [|c1 r]; [discriminate|].
    injection E0 as ->. cbn [starts_with] in S1, S2. rewrite S1, S2 in Hor. cbn [orb] in Hor.
    unfold follow_ok in Hf. apply andb_true_iff in Hf as [_ Hf]. cbn in Hf.
    apply negb_true_iff in Hf. rewrite Hf in Hor. discriminate. }
  destruct (Ascii.eqb c lbrace) eqn:Elb.
  { (* `{`, which a row's character follows *)
    apply Ascii.eqb_eq in Elb. subst c.
    assert (Hrow : starts_row s' = true).
    { unfold follow_ok in Hf. rewrite Ascii.eqb_refl in Hf. cbn in Hf.
      rewrite !andb_true_r in Hf. exact Hf. }
    destruct s' as [|d s'']; [discriminate|].
    cbn [starts_row] in Hrow. unfold is_delim in Hrow.
    destruct (dstyle_of d) as [k|] eqn:Hd; [|discriminate].
    pose proof Hs' as Hd'. apply over_alphabet_cons in Hd' as (Hdc & _ & _).
    pose proof (dstyle_of_enabled d k Hd) as Hen.
    pose proof (dstyle_of_char d k Hd) as Ec. subst d.
    destruct (dchar_plain k) as (Hlbk & Hrbk & Hlkk & Hrkk).
    destruct (run_split (dchar k) s'') as (j' & rest0 & -> & Hr).
    assert (Hnext : forall c0, get 0 rest0 = Some c0 -> c0 <> dchar k).
    { intros c0 E0. destruct rest0 as [|d r]; [discriminate|]. injection E0 as <-.
      exact (Hr d r eq_refl). }
    destruct (Nat.le_gt_cases (dwidth k) (S j')) as [Hw|Hw].
    - (* a marked opener *)
      set (rest := (chars (dchar k) (S j' - dwidth k) ++ rest0)%string).
      assert (Es : String (dchar k) (chars (dchar k) j' ++ rest0) = (dtoken k ++ rest)%string).
      { unfold rest, dtoken. rewrite <- append_assoc, <- chars_add.
        replace (dwidth k + (S j' - dwidth k)) with (S j') by lia. reflexivity. }
      clearbody rest.
      apply (Nrm (marked_open k) rest [TDelim k true true false] (Some (dchar k)) ""
               (oopen_marked k (at_rbrace (get 0 rest)) txt o)).
      + rewrite Es. reflexivity.
      + unfold marked_open. discriminate.
      + rewrite Es. exact (lex_marked_open k prev rest Hd).
      + cbn [toks_text]. rewrite append_empty_r. reflexivity.
      + apply follow_ok_plain; assumption.
      + apply tok_marked_open, Hen.
      + cbn [prun]. apply pstep_mode; [exact Em|discriminate].
      + cbn [prun]. unfold pstep. rewrite Em.
        exact (open_marked_sim n k _ txt v o Ok Hs).
    - (* `{` and a run too short to be a token: text *)
      destruct (prun_texts ts (dchar k) (S j') (S n) (pstep ts n (TText lbrace) v)
                  (txt ++ one lbrace) o) as [S2 M2].
      { apply pstep_mode; [exact Em|discriminate]. }
      { unfold pstep. rewrite Em. apply sim_text; [exact Hs|reflexivity]. }
      rewrite append_assoc in S2.
      apply (Nrm (String lbrace (chars (dchar k) (S j'))) rest0
               (TText lbrace :: repeat (TText (dchar k)) (S j')) (Some (dchar k))
               (txt ++ String lbrace (chars (dchar k) (S j'))) o).
      + reflexivity.
      + discriminate.
      + change (String lbrace (String (dchar k) (chars (dchar k) j' ++ rest0)))
          with (String lbrace (chars (dchar k) (S j') ++ rest0)).
        rewrite (lex_lbrace_short k j' prev rest0 Hd Hw Hr),
          (lex_partial k (S j') (Some lbrace) rest0 Hd Hw Hr). reflexivity.
      + cbn [toks_text tok_text]. rewrite toks_text_repeat. reflexivity.
      + apply follow_ok_plain; assumption.
      + apply tok_marked_partial; [exact Hen|lia|exact Hnext].
      + exact M2.
      + exact S2. }
  destruct (dstyle_of c) as [k|] eqn:Hd.
  2: { (* a plain byte *)
    apply (Nrm (one c) s' [TText c] (Some c) (txt ++ one c) o);
      [reflexivity|discriminate|exact (lex_byte c prev s' Elk Erk Elb Hd)|reflexivity|exact Hf| | |].
    - cbn [iscan_str one]. unfold istep. cbn [istep_at].
      rewrite (ilead_text c txt prev o Hc Elb Elk Erk Hd Hn). apply settles_refl.
    - cbn [prun]. apply pstep_mode; [exact Em|discriminate].
    - cbn [prun]. unfold pstep. rewrite Em. apply sim_text; [exact Hs|reflexivity]. }
  pose proof (alphabet_self c k Hc Hd) as Hk.
  pose proof (alphabet_hyphen c Hc) as Hhy.
  pose proof (dstyle_of_enabled c k Hd) as Hen.
  pose proof (dstyle_of_char c k Hd) as Ec. subst c.
  destruct (dchar_plain k) as (Hlbk & Hrbk & Hlkk & Hrkk).
  destruct (run_split (dchar k) s') as (j' & rest0 & -> & Hr).
  assert (Hnext : forall c0, get 0 rest0 = Some c0 -> c0 <> dchar k).
  { intros c0 E0. destruct rest0 as [|d0 r]; [discriminate|]. injection E0 as <-.
    exact (Hr d0 r eq_refl). }
  assert (Htok : dtoken k <> "").
  { destruct (dtoken_cons k) as (w & _ & Ed). rewrite Ed. discriminate. }
  destruct (Nat.le_gt_cases (dwidth k) (S j')) as [Hw|Hw].
  - (* a whole token *)
    set (rest := (chars (dchar k) (S j' - dwidth k) ++ rest0)%string).
    assert (Es : String (dchar k) (chars (dchar k) j' ++ rest0) = (dtoken k ++ rest)%string).
    { unfold rest, dtoken. rewrite <- append_assoc, <- chars_add.
      replace (dwidth k + (S j' - dwidth k)) with (S j') by lia. reflexivity. }
    clearbody rest.
    destruct (at_rbrace (get 0 rest)) eqn:Hat.
    + (* a marked closer *)
      destruct rest as [|e0 r]; [discriminate|]. cbn [get at_rbrace] in Hat.
      apply Ascii.eqb_eq in Hat. subst e0.
      destruct (resolve_sim ts n k true txt prev (Some rbrace) v o Hk Ok Em Hs)
        as (txt' & o' & Hres & Hsim).
      apply (Nrm (dtoken k ++ one rbrace) r [TDelim k true false true] (Some rbrace) txt' o').
      * rewrite Es, append_assoc. reflexivity.
      * intros E0. destruct (dtoken k); [exact (Htok eq_refl)|discriminate].
      * rewrite Es. exact (lex_marked_close k prev r Hd).
      * cbn [toks_text tok_text]. apply append_empty_r.
      * reflexivity.
      * rewrite (tok_marked_close k txt prev o Hen Hhy Hn), Hres. apply settles_refl.
      * cbn [prun]. apply pstep_mode; [exact Em|discriminate].
      * cbn [prun]. exact Hsim.
    + (* a bare token *)
      destruct (resolve_sim ts n k false txt prev (get 0 rest) v o Hk Ok Em Hs)
        as (txt' & o' & Hres & Hsim).
      apply (Nrm (dtoken k) rest
               [TDelim k false (bare_opens k && nonspace_at (get 0 rest)) (nonspace_at prev)]
               (Some (dchar k)) txt' o').
      * exact Es.
      * exact Htok.
      * rewrite Es. exact (lex_token k prev rest Hd Hat).
      * cbn [toks_text tok_text]. apply append_empty_r.
      * apply follow_ok_plain; assumption.
      * apply (tok_bare k txt prev o (get 0 rest) txt' o' Hen Hhy Hn); [|exact Hres].
        intros c0 E0. rewrite E0 in Hat. exact Hat.
      * cbn [prun]. apply pstep_mode; [exact Em|discriminate].
      * cbn [prun]. exact Hsim.
  - (* a run too short to be a token *)
    destruct (prun_texts ts (dchar k) (S j') n v txt o Em Hs) as [S2 M2].
    apply (Nrm (chars (dchar k) (S j')) rest0 (repeat (TText (dchar k)) (S j'))
             (Some (dchar k)) (txt ++ chars (dchar k) (S j')) o).
    + reflexivity.
    + discriminate.
    + exact (lex_partial k (S j') prev rest0 Hd Hw Hr).
    + apply toks_text_repeat.
    + apply follow_ok_plain; assumption.
    + apply tok_partial; [exact Hen|exact Hhy|exact Hn|lia|exact Hnext].
    + exact M2.
    + exact S2.
Qed.

(*
Lines
-----

Between two lines the scanner resolves what is pending as at the end of
a line and takes the break: a soft break in text mode, a byte of the
region in a label or a destination.  That is the view of a break token.
*)

Local Lemma break_linked : forall ts n v prev core rest,
  skipn n ts = TBreak :: rest -> linked ts n v prev core ->
  linked ts (S n) (pstep ts n TBreak v) None (ibreak core).
Proof.
  intros ts n v prev core rest Hsk L. pose proof (skipn_cons_tail ts n _ _ Hsk) as Hsk1.
  unfold linked in L. destruct (pv_mode v) as [|[|] kids d e txt] eqn:Em.
  - destruct L as (txt & o & -> & Hs). destruct Hs as (v0 & cm & -> & Ht & Ev).
    assert (E : ibreak (IText false txt prev (oview cm v0))
                = IText false "" None (oview cm (pv_add SoftBreak v))).
    { unfold ibreak, ibreak_at, ibreak_flat. cbn [iresolve].
      change (@flush_text_at semantic_pos semantic_inline_cursor (tval txt) (oview cm v0))
        with (flush_text txt (oview cm v0)).
      rewrite (flush_view cm txt v0 Ht), <- Ev.
      change (imk_here SoftBreak) with (mk SoftBreak).
      rewrite (oemit_view cm SoftBreak v) by discriminate. reflexivity. }
    rewrite E. apply linked_normal; [apply pstep_mode; [exact Em|discriminate]|].
    unfold pstep. rewrite Em. exists (pv_add SoftBreak v), cm.
    split; [reflexivity|]. split; [apply top_add_nonstr; discriminate|reflexivity].
  - destruct L as (Hd & open & depth & sh & cm & He & Hne & ->).
    rewrite Hsk in He. cbn [paren_close] in He.
    rewrite (region_stay ts n TBreak v true kids d e txt Em Hd).
    2: { intros e' E'. rewrite E' in He. symmetry in He.
         apply Precedence.paren_close_ge in He. lia. }
    unfold linked. cbn [pv_setmode pv_mode]. split; [lia|].
    exists open, depth, (ibreak sh), cm. rewrite Hsk1.
    split; [exact He|]. split; [exact Hne|reflexivity].
  - destruct L as (Hd & He & Hk & open & cm & ->).
    rewrite Hsk in He. cbn [rbrack_at] in He.
    rewrite (region_stay ts n TBreak v false kids d e txt Em Hd).
    2: { intros e' E'. rewrite E' in He. symmetry in He.
         apply Precedence.rbrack_at_ge in He. lia. }
    unfold linked. cbn [pv_setmode pv_mode]. split; [lia|].
    rewrite Hsk1. split; [exact He|]. split; [exact Hk|].
    exists open, cm. reflexivity.
Qed.

(* The paragraph's end, in a linked state. *)
Local Lemma linked_finish : forall ts n v ws prev core,
  vinv n v -> linked ts n v prev core -> skipn n ts = [] ->
  ifinish (wrap ws core) = map mk (List.rev (pflatten v)).
Proof.
  intros ts n v ws prev core [Ok Ti] L Hsk. pose proof Ok as (_ & _ & B & _).
  rewrite ifinish_wrap. unfold linked in L.
  destruct (pv_mode v) as [|[|] kids d e txt] eqn:Em.
  - destruct L as (txt & o & -> & Hs). rewrite (sim_finish v txt prev o Hs B).
    unfold pflatten, pfinish. rewrite Em. reflexivity.
  - destruct L as (_ & open & depth & sh & cm & He & Hne & _).
    rewrite Hsk in He. destruct (Hne He).
  - destruct L as (_ & He & Hk & open & cm & ->). rewrite Hsk in He. cbn in He. subst e.
    destruct (tidy_top v Ti) as [Hn Hc].
    exact (ref_finish cm v false kids d open txt Em B Hn Hc Hk).
Qed.

Local Lemma blank_not_row : forall w, is_blank w = true -> starts_row w = false.
Proof.
  intros [|c w] H; [reflexivity|]. cbn [is_blank] in H.
  apply andb_true_iff in H as [Hc _]. cbn [starts_row]. unfold is_delim.
  destruct (dstyle_of c) as [k|] eqn:Hd; [|reflexivity].
  apply dstyle_of_char in Hd. subst c.
  rewrite (is_punct_not_ws _ (dchar_punct k)) in Hc. discriminate.
Qed.

Local Lemma over_alphabet_app_l : forall a b,
  over_alphabet (a ++ b) = true -> starts_row b = false ->
  over_alphabet a = true.
Proof.
  induction a as [|c a IH]; intros b H Hb; [reflexivity|].
  apply over_alphabet_cons in H as (Hc & Hf & H).
  cbn [over_alphabet]. rewrite Hc, (IH b H Hb), andb_true_r. cbn [andb].
  destruct a as [|d a]; [|exact Hf].
  cbn [append] in Hf. unfold follow_ok in *. rewrite Hb in Hf.
  apply andb_true_iff in Hf as [Hf _]. apply andb_true_iff in Hf as [Hf _].
  cbn. rewrite Hf, !andb_false_r. reflexivity.
Qed.

Local Lemma over_alphabet_strip : forall x,
  over_alphabet x = true -> over_alphabet (strip_trailing_ws x) = true.
Proof.
  intros x Ha. destruct (strip_trailing_split x) as (w & Hw & E).
  rewrite E in Ha. exact (over_alphabet_app_l _ w Ha (blank_not_row w Hw)).
Qed.

Local Lemma scan_lines_sim : forall ts ls n v ws core,
  Forall (fun x => over_alphabet x = true) ls ->
  skipn n ts = para_tokens ls ->
  vinv n v -> Forall (never ts n) ws -> linked ts n v None core ->
  ifinish (iscan_lines ls (wrap ws core))
  = map mk (List.rev (pflatten (prun ts n (para_tokens ls) v))).
Proof.
  intros ts. induction ls as [|x rest IH]; intros n v ws core Ha Hsk V Fn L.
  - cbn [iscan_lines para_tokens prun]. exact (linked_finish ts n v ws None core V L Hsk).
  - apply Forall_cons_iff in Ha as [Hx Ha].
    destruct rest as [|y rest'].
    + cbn [iscan_lines para_tokens] in *. unfold tokens in *.
      rewrite <- (app_nil_r (lex None 0 (strip_trailing_ws x))) in Hsk.
      destruct (scan_sim ts [] _ (strip_trailing_ws x) None n v ws core (le_n _)
                  (over_alphabet_strip x Hx) eq_refl Hsk V Fn L)
        as (ws' & core' & prev' & E & V' & Fn' & L').
      rewrite <- ifinish_rres, E.
      exact (linked_finish ts _ _ ws' prev' core' V' L' (skipn_app_tail ts _ [] n Hsk)).
    + change (iscan_lines (x :: y :: rest') (wrap ws core))
        with (iscan_lines (y :: rest') (ibreak (iscan_str x (wrap ws core)))).
      change (para_tokens (x :: y :: rest'))
        with (lex None 0 x ++ TBreak :: para_tokens (y :: rest'))%list in *.
      destruct (scan_sim ts _ _ x None n v ws core (le_n _) Hx eq_refl Hsk V Fn L)
        as (ws' & core' & prev' & E & V' & Fn' & L').
      pose proof (skipn_app_tail ts _ _ n Hsk) as Hsk'.
      unfold ibreak at 1. rewrite <- ibreak_rres, E. fold (ibreak (wrap ws' core')).
      rewrite ibreak_wrap, prun_app. cbn [prun].
      apply IH; [exact Ha|exact (skipn_cons_tail ts _ _ _ Hsk')
                |apply vinv_step; [exact V'|exact Logic.I]| |exact (break_linked ts _ _ _ _ _ Hsk' L')].
      destruct (layers_step ts _ ws' [TBreak] _ Fn' Hsk' (Forall_cons TBreak (Logic.I : tok_plain TBreak) (Forall_nil _)))
        as [_ F]. rewrite Nat.add_1_r in F. exact F.
Qed.

(*
The theorem
===========

On a paragraph over the alphabet, the scanner builds the tree of the
unique reading the precedence rules allow. *)

Local Lemma vinv_start : vinv 0 pv0.
Proof.
  split; [split; [constructor|]; split; [intros x []|]; split; [constructor|exact Logic.I]|].
  split; [exact Logic.I|]. split; [constructor|]. split; constructor.
Qed.

Local Lemma linked_start : forall ts, linked ts 0 pv0 None istart.
Proof.
  intros ts. exists "", ostart. split; [reflexivity|].
  exists pv0, (fun _ => false). split; [reflexivity|]. split; reflexivity.
Qed.

Theorem parse_inline_line_matching : forall s,
  over_alphabet s = true ->
  parse_inline_line s = tree_of (tokens s) (fst (ref_read (tokens s))).
Proof.
  intros s Ha. unfold parse_inline_line. rewrite tree_of_prun.
  assert (Hsk : skipn 0 (tokens s) = (lex None 0 s ++ [])%list) by (rewrite app_nil_r; reflexivity).
  destruct (scan_sim (tokens s) [] _ s None 0 pv0 [] istart (le_n _) Ha eq_refl Hsk
              vinv_start (Forall_nil _) (linked_start _))
    as (ws' & core' & prev' & E & V' & Fn' & L').
  cbn [wrap] in E. rewrite <- ifinish_rres, E.
  exact (linked_finish (tokens s) _ _ ws' prev' core' V' L' (skipn_app_tail _ _ [] 0 Hsk)).
Qed.

(* A paragraph: its lines, each over the alphabet, with a break between
   two of them and the last read without its trailing whitespace. *)
Theorem para_inlines_matching : forall ls,
  Forall (fun x => over_alphabet x = true) ls ->
  para_inlines ls = tree_of (para_tokens ls) (fst (ref_read (para_tokens ls))).
Proof.
  intros ls Ha. unfold para_inlines. rewrite tree_of_prun.
  exact (scan_lines_sim (para_tokens ls) ls 0 pv0 [] istart Ha eq_refl vinv_start
           (Forall_nil _) (linked_start _)).
Qed.

(* The same in the reference's terms: the paragraph is the tree of any
   reading the precedence rules allow (P1, P3, P4, P5), since there is
   one. *)

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
  unfold tree_of. f_equal.
  generalize 0 as i. generalize (([], [], TMNormal) : tstate) as st.
  generalize ts at 2 4 as rest.
  induction rest as [|t rest IH]; intros st i; cbn [tree_go]; [reflexivity|].
  replace (tstep ts m1 i t st) with (tstep ts m2 i t st); [apply IH|].
  destruct st as [[fs top] md]. unfold tstep.
  destruct md; [destruct t|]; rewrite ?Eo, ?Ec; reflexivity.
Qed.

Corollary para_inlines_valid : forall ls m os,
  Forall (fun x => over_alphabet x = true) ls -> valid (para_tokens ls) (m, os) ->
  para_inlines ls = tree_of (para_tokens ls) m.
Proof.
  intros ls m os Ha Hv. rewrite (para_inlines_matching ls Ha).
  apply tree_of_members.
  pose proof (ref_read_valid (para_tokens ls)) as Hr.
  destruct (ref_read (para_tokens ls)) as [m0 os0].
  exact (proj1 (valid_unique _ _ _ _ _ Hr Hv)).
Qed.

End WithTable.
