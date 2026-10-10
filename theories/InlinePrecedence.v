(* ai-disclosure: autonomous *)

(* The inline scanner builds the tree the precedence rules describe
   (`Precedence.v`): on a paragraph of delimiters, bare or marked with
   braces, brackets with their destinations and labels, and plain bytes,
   `para_inlines` is `tree_of` of the unique valid reading. *)

From Stdlib Require Import String Ascii List Bool Lia Arith Sorted.
From DjotV Require Import Strings Ast Attributes InlineTable InlineView InlineScan
  InlineInvert Precedence.
Import ListNotations.

Local Open Scope string_scope.

Section WithTable.
Context {T : dtable}.

(*
The prefix view
===============

What the scanner holds after a prefix of the paragraph: the openers
still open, innermost first, each with what has been read since it, a
frame for each destination that does not close, above what was read
before the outermost one; and, after a bracket's closer, the region
being read.  The view reads the units the scanner does: a token of the
chain, or a byte of a region.
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

(* As the chain's jump past a region, with what a region has gathered:
   its link text and its bytes so far, its `(` or `[` aside; or inside a
   token of several bytes whose node `x` is added at its last byte `e`. *)
Inductive pmode : Type :=
  | PMNormal
  | PMRegion (dest : bool) (kids : list inline) (d : nat) (e : option nat) (txt : string)
  | PMAtom (x : inline) (e : nat).

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

(* What a hard break trims: the text it ends, as `str_trim`. *)
Definition xtrim (l : list inline) : list inline :=
  match l with
  | Str t :: rest =>
      match strip_trailing_ws t with
      | EmptyString => rest
      | t' => Str t' :: rest
      end
  | _ => l
  end.

Definition pv_trim (v : pview) : pview :=
  match pv_stk v with
  | [] => PView [] (xtrim (pv_out v)) (pv_mode v)
  | f :: rest => PView (fset f (xtrim (fcontent f)) :: rest) (pv_out v) (pv_mode v)
  end.

(* A token that does not close opens if it may, or is its own text. *)
Definition popen (i : nat) (k : key) (op : bool) (txt : string) (v : pview)
  : pview :=
  if op then PView (PF i k [] :: pv_stk v) (pv_out v) (pv_mode v)
  else pv_add (Str txt) v.

Definition add_text (txt : string) (v : pview) : pview :=
  if nonempty_str txt then pv_add (Str txt) v else v.

(* A token of the chain: `rstep`, keeping the content.  `hard` says the
   token before was a hard break. *)
Definition pstep (s : string) (i : nat) (hard : bool) (t : token) (v : pview) : pview :=
  match t with
  | TText c => pv_add (Str (one c)) v
  | TEsc c => pv_add (Str (esc_text c)) v
  | TEscWs ws =>
      match nbsp_rest ws with
      | Some rest =>
          let w := pv_add NonBreakingSpace v in
          if nonempty_str rest then pv_add (Str rest) w else w
      | None => pv_add (Str (tok_text t)) v
      end
  | THard _ => pv_add HardBreak (pv_trim v)
  | TBreak => if hard then v else pv_add SoftBreak v
  | TVerb pre _ body _ raw =>
      let v1 := add_text (chars dollar (pre - 2)) v in
      if Nat.ltb (S i) (tok_end s i)
      then pv_setmode (PMAtom (verb_node pre raw body) (pred (tok_end s i))) v1
      else pv_add (verb_node pre raw body) v1
  | TDollars _ => pv_add (Str (tok_text t)) v
  | TOpen => popen i KBracket true (tok_text t) v
  | TDelim k mr op cl =>
      match (if cl then pick (KDelim k mr) (pv_live v) else PNone) with
      | PFound p _ =>
          if Nat.ltb (tok_end s p) i
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
          match region_end s i b with
          | Some e => PView rest (pv_out v) (PMRegion b (List.rev content) i (Some e) "")
          | None =>
              if b
              then PView (PB i (xsnoc (Str (one rbrack)) content) :: rest)
                     (pv_out v) PMNormal
              else PView rest (pv_out v) (PMRegion false (List.rev content) i None "")
          end
      | _, _ => pv_add (Str (tok_text t)) v
      end
  end.

(* A byte of a region: the `(` or `[` that opens it is skipped, and the
   byte that ends it makes the link.  A byte of a token: the last one
   adds its node. *)
Definition pbyte (i : nat) (c : ascii) (v : pview) : pview :=
  match pv_mode v with
  | PMAtom x e => if Nat.eqb i e then pv_add x (pv_setmode PMNormal v) else v
  | PMRegion b kids d e txt =>
      if match e with Some e' => Nat.eqb i e' | None => false end
      then pv_add (region_node b (map mk kids) (if b then dest_text false txt else txt))
             (pv_setmode PMNormal v)
      else pv_setmode (PMRegion b kids d e
                         (if Nat.eqb i (S d) then txt else (txt ++ one c)%string)) v
  | PMNormal => v
  end.

(* One unit from byte `i`: where the next one is, whether this one was a
   hard break, and the view after it.  A token that leaves the view in a
   region or inside itself is followed by its next byte. *)
Definition punit (s : string) (i : nat) (hard : bool) (v : pview)
  : option (nat * bool * pview) :=
  match pv_mode v with
  | PMNormal =>
      match tok_at s i with
      | Some (t, l) =>
          let v' := pstep s i hard t v in
          Some (match pv_mode v' with PMNormal => i + l | _ => S i end, is_hard t, v')
      | None => None
      end
  | PMRegion _ _ _ _ _ | PMAtom _ _ =>
      match get i s with
      | Some c => Some (S i, false, pbyte i c v)
      | None => None
      end
  end.

Inductive pruns (s : string) : nat -> bool -> pview -> nat -> bool -> pview -> Prop :=
  | pruns_refl : forall i h v, pruns s i h v i h v
  | pruns_step : forall i h v j h1 v1 k h2 v2,
      punit s i h v = Some (j, h1, v1) -> pruns s j h1 v1 k h2 v2 -> pruns s i h v k h2 v2.

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

(* The frames of `tgo` that a view stands for, given which openers the
   whole paragraph closes: a frame whose opener is closed stays a frame,
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

Definition tfr (st : list (tkind * list inline) * list inline) : tframes * inlines :=
  (map (fun f => (fst f, map mk (snd f))) (fst st), map mk (snd st)).

Definition vembed (real : nat -> bool) (v : pview) : tframes * inlines :=
  tfr (collapse real (pv_stk v) (pv_out v)).

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

Local Lemma pv_add_live : forall x v,
  pv_live (pv_add x v) = pv_live v /\ pv_mode (pv_add x v) = pv_mode v.
Proof. intros x [[|[p k c|d c] rest] out md]; split; reflexivity. Qed.

Local Lemma add_text_live : forall t v,
  pv_live (add_text t v) = pv_live v /\ pv_mode (add_text t v) = pv_mode v.
Proof. intros t v. unfold add_text. destruct (nonempty_str t); [apply pv_add_live|split; reflexivity]. Qed.

Local Lemma verb_node_nonstr : forall d r b s, verb_node d r b <> Str s.
Proof. intros [|[|d]] [f|] b s; discriminate. Qed.

Local Lemma pv_trim_live : forall v,
  pv_live (pv_trim v) = pv_live v /\ pv_mode (pv_trim v) = pv_mode v.
Proof. intros [[|[p k c|d c] rest] out md]; split; reflexivity. Qed.

Local Lemma pclose_found : forall k stk p below,
  pick k (map fitem stk) = PFound p below ->
  exists content rest, pclose_go k [] stk = Some (content, rest) /\ map fitem rest = below.
Proof.
  intros k stk p below P.
  destruct (pick_split k stk p below P) as (above & c & rest & -> & F & Hb).
  destruct (pclose_split k above p c rest [] F) as [content Hc].
  exists content, rest. split; [exact Hc|exact Hb].
Qed.

Local Lemma pstep_live : forall s n h t v st,
  pv_live v = rs_live st -> pv_live (pstep s n h t v) = rs_live (rstep s n t st).
Proof.
  intros s n h t v [lv m os] Hl. cbn [rs_live] in *.
  unfold pstep, rstep. cbn [rs_live rs_pairs rs_os].
  assert (Add : forall x, pv_live (pv_add x v) = lv)
    by (intros x; rewrite (proj1 (pv_add_live x v)); exact Hl).
  assert (Open : forall i k op txt,
            pv_live (popen i k op txt v) = rs_live (ropen i k op (RState lv m os))).
  { intros i k [|] txt; unfold popen, ropen; cbn [pv_live pv_stk rs_live map fitem].
    - unfold pv_live in Hl. rewrite Hl. reflexivity.
    - apply Add. }
  destruct t as [c| |k mr op cl| |b|c|ws|ws|vp vn vb vc vr|dk]; try apply Add.
  - destruct h; [exact Hl|apply Add].
  - rewrite Hl. destruct (if cl then pick (KDelim k mr) lv else PNone) as [p below| |] eqn:P;
      [|apply Add|apply Open].
    destruct (Nat.ltb (tok_end s p) n); [|apply Open].
    destruct cl; [|discriminate].
    unfold pv_live in Hl. rewrite <- Hl in P.
    destruct (pclose_found _ _ _ _ P) as (content & rest & Hc & Hb).
    rewrite Hc. rewrite (proj1 (pv_add_live _ _)). exact Hb.
  - apply Open.
  - rewrite Hl. destruct (pick KBracket lv) as [p below| |] eqn:P; [|apply Add|apply Add].
    unfold pv_live in Hl. rewrite <- Hl in P.
    destruct (pclose_found _ _ _ _ P) as (content & rest & Hc & Hb).
    rewrite Hc. destruct (region_end s n b) as [e|]; [|destruct b];
      cbn [pv_live pv_stk map fitem]; rewrite ?Hb; reflexivity.
  - destruct (nbsp_rest ws) as [r|]; [|apply Add].
    destruct (nonempty_str r); [|apply Add].
    rewrite (proj1 (pv_add_live _ _)). apply Add.
  - rewrite (proj1 (pv_add_live _ _)), (proj1 (pv_trim_live v)). exact Hl.
  - assert (At : pv_live (add_text (chars dollar (vp - 2)) v) = lv)
      by (unfold add_text; destruct (nonempty_str _); [apply Add|exact Hl]).
    destruct (Nat.ltb _ _); [exact At|rewrite (proj1 (pv_add_live _ _)); exact At].
Qed.

Local Lemma pstep_mode : forall s n h t v,
  pv_mode v = PMNormal -> (forall b, t <> TClose b) -> (forall d m b c r, t <> TVerb d m b c r) ->
  pv_mode (pstep s n h t v) = PMNormal.
Proof.
  intros s n h t v Em Ht Hv. unfold pstep.
  assert (Add : forall x, pv_mode (pv_add x v) = PMNormal)
    by (intros x; rewrite (proj2 (pv_add_live x v)); exact Em).
  assert (Open : forall i k op txt, pv_mode (popen i k op txt v) = PMNormal)
    by (intros i k [|] txt; [exact Em|apply Add]).
  destruct t as [c| |k mr op cl| |b|c|ws|ws|vp vn vb vc vr|dk]; try apply Add; try apply Open.
  - destruct h; [exact Em|apply Add].
  - destruct (if cl then pick (KDelim k mr) (pv_live v) else PNone); try apply Add; try apply Open.
    destruct (Nat.ltb (tok_end s p) n); [|apply Open].
    destruct (pclose_go (KDelim k mr) [] (pv_stk v)) as [[content rest]|]; [|exact Em].
    rewrite (proj2 (pv_add_live _ _)). reflexivity.
  - destruct (Ht b eq_refl).
  - destruct (nbsp_rest ws); [|apply Add].
    destruct (nonempty_str s0); [rewrite (proj2 (pv_add_live _ _))|]; apply Add.
  - rewrite (proj2 (pv_add_live _ _)), (proj2 (pv_trim_live _)). exact Em.
  - destruct (Hv vp vn vb vc vr eq_refl).
Qed.

Local Lemma pclose_none : forall k stk pend,
  (forall p below, pick k (map fitem stk) <> PFound p below) ->
  pclose_go k pend stk = None.
Proof.
  intros k stk. induction stk as [|[q k' c|d c] stk IH]; intros pend H; [reflexivity| |reflexivity].
  cbn [pclose_go]. cbn [map fitem pick] in H.
  destruct (key_eq k k'); [destruct (H q (map fitem stk) eq_refl)|]. apply IH, H.
Qed.

Local Lemma pstep_close_found : forall s n h b v content rest,
  pclose_go KBracket [] (pv_stk v) = Some (content, rest) ->
  pstep s n h (TClose b) v
  = match region_end s n b with
    | Some e => PView rest (pv_out v) (PMRegion b (List.rev content) n (Some e) "")
    | None =>
        if b then PView (PB n (xsnoc (Str (one rbrack)) content) :: rest) (pv_out v) PMNormal
        else PView rest (pv_out v) (PMRegion false (List.rev content) n None "")
    end.
Proof.
  intros s n h b v content rest Hc. unfold pstep. rewrite Hc.
  destruct (pick KBracket (pv_live v)) eqn:P; [reflexivity| |];
    rewrite (pclose_none KBracket (pv_stk v) []) in Hc
      by (intros p' b'; unfold pv_live in P; rewrite P; discriminate);
    discriminate.
Qed.

Local Lemma pstep_close_none : forall s n h b v,
  pclose_go KBracket [] (pv_stk v) = None ->
  pstep s n h (TClose b) v = pv_add (Str (one rbrack)) v.
Proof.
  intros s n h b v Hc. unfold pstep. rewrite Hc.
  destruct (pick KBracket (pv_live v)); reflexivity.
Qed.

(*
One token
---------

The view and `tstep` move together, given what the whole paragraph's
matching says about the token: whether it closes, whether it will be
closed as an opener, and that the openers a closer passes over are
never closed. *)

Definition closes_here (m : matching) (n p : nat) (lv : list litem) : Prop :=
  is_closer m n = true /\ is_opener m p = true
  /\ (forall q k', In (LOpen q k') lv -> p < q -> is_opener m q = false).

Definition step_facts (s : string) (m : matching) (n : nat) (t : token)
  (lv : list litem) : Prop :=
  match t with
  | TDelim k mr op cl =>
      match (if cl then pick (KDelim k mr) lv else PNone) with
      | PFound p _ =>
          if Nat.ltb (tok_end s p) n then is_opener m n = false /\ closes_here m n p lv
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
  end.

Definition frames_normal (v : pview) : Prop :=
  Forall (fun f => normal (fcontent f)) (pv_stk v).

Local Lemma dnode_nonstr : forall k l s, dnode k l <> Str s.
Proof. intros [] l s E; discriminate E. Qed.

Local Lemma region_node_nonstr : forall b l t s, region_node b l t <> Str s.
Proof. intros [] l t s E; discriminate E. Qed.

(*
Trimming before a hard break
----------------------------

A hard break trims the text right before it, in the innermost content.
A frame that `collapse` turns into text puts its opener's spelling
before its content, and that spelling ends in a byte that is not
whitespace, so trimming the collapsed content trims the frame's own.
*)

Local Lemma strip_app_nonempty : forall w t,
  strip_trailing_ws t <> EmptyString ->
  strip_trailing_ws (w ++ t) = (w ++ strip_trailing_ws t)%string.
Proof.
  intros w t H. unfold strip_trailing_ws in *. rewrite rev_string_app.
  rewrite drop_leading_ws_app_nonblank.
  - rewrite rev_string_app, rev_string_involutive. reflexivity.
  - intros E. apply H. rewrite E. reflexivity.
Qed.

Local Lemma strip_app_empty : forall w t,
  strip_trailing_ws t = EmptyString -> strip_trailing_ws (w ++ t) = strip_trailing_ws w.
Proof.
  intros w t H. destruct (strip_trailing_split t) as (p & Hp & E).
  rewrite H in E. cbn [append] in E. subst p.
  apply strip_trailing_ws_app_blank, Hp.
Qed.

(* Nonempty, and left alone by `strip_trailing_ws`. *)
Definition solid (s : string) : Prop := strip_trailing_ws s = s /\ s <> EmptyString.

Local Lemma xtrim_solid : forall w r, solid w -> xtrim (Str w :: r) = Str w :: r.
Proof.
  intros w r [H Hne]. cbn [xtrim]. rewrite H.
  destruct w; [contradiction|reflexivity].
Qed.

Local Lemma solid_app : forall u w, solid w -> solid (u ++ w).
Proof.
  intros u w [H Hne]. split.
  - rewrite strip_app_nonempty by (rewrite H; exact Hne). rewrite H. reflexivity.
  - destruct u; [exact Hne|discriminate].
Qed.

Local Lemma xsnoc_solid : forall s acc, solid s ->
  exists w r, xsnoc (Str s) acc = Str w :: r /\ solid w.
Proof.
  intros s [|y acc] Hs; [exists s, []; split; [reflexivity|exact Hs]|].
  destruct (str_view y) as [[u ->]|Hy].
  - exists (u ++ s)%string, acc. split; [reflexivity|apply solid_app, Hs].
  - exists s, (y :: acc). split; [apply xsnoc_str_nonstr, Hy|exact Hs].
Qed.

Local Lemma xtrim_xapp_solid : forall c w r, solid w ->
  xtrim (xapp c (Str w :: r)) = xapp (xtrim c) (Str w :: r).
Proof.
  intros c w r Hw. destruct c as [|y [|z c]].
  - apply xtrim_solid, Hw.
  - cbn [xapp]. destruct (str_view y) as [[t ->]|Hy].
    + cbn [xsnoc xtrim].
      destruct (strip_trailing_ws t) as [|a t'] eqn:Et.
      * rewrite (strip_app_empty w t Et), (proj1 Hw).
        destruct w; [destruct Hw as [_ []]; reflexivity|reflexivity].
      * rewrite (strip_app_nonempty w t) by (rewrite Et; discriminate).
        rewrite Et. destruct w; [destruct Hw as [_ []]; reflexivity|reflexivity].
    + rewrite (xsnoc_nonstr y _ Hy).
      destruct y; [destruct (Hy _ eq_refl)|..]; reflexivity.
  - change (xapp (y :: z :: c) (Str w :: r)) with (y :: xapp (z :: c) (Str w :: r)).
    destruct (str_view y) as [[t ->]|Hy].
    + cbn [xtrim]. destruct (strip_trailing_ws t); reflexivity.
    + destruct y; [destruct (Hy _ eq_refl)|..]; reflexivity.
Qed.

Local Lemma ws_punct : forall c, is_punct c = true -> is_ws c = false.
Proof. intros c. destruct c as [[] [] [] [] [] [] [] []]; vm_compute; congruence. Qed.

Local Lemma solid_last : forall x z, is_ws z = false -> solid (x ++ String z EmptyString).
Proof.
  intros x z Hz. apply solid_app. split; [|discriminate].
  unfold strip_trailing_ws. cbn. rewrite Hz. reflexivity.
Qed.

Local Lemma chars_last : forall c n, chars c (S n) = (chars c n ++ String c EmptyString)%string.
Proof.
  intros c n. induction n as [|n IH]; [reflexivity|].
  cbn [chars append]. f_equal. exact IH.
Qed.

Local Lemma lit_solid : forall k, exists s, lit k = Str s /\ solid s.
Proof.
  intros [k mr|]; [|exists (one lbrack); split; [reflexivity|split; [reflexivity|discriminate]]].
  pose proof (ws_punct _ (dchar_punct k)) as Hw.
  destruct (dwidth k) as [|n] eqn:En; [destruct (dwidth_nonzero k En)|].
  assert (Ht : solid (dtoken k))
    by (unfold dtoken; rewrite En, chars_last; apply solid_last, Hw).
  destruct mr; cbn [lit tok_text]; eexists; split; try reflexivity;
    [apply solid_app|]; exact Ht.
Qed.

Local Lemma xtrim_collapsed : forall c x acc, (exists s, x = Str s /\ solid s) ->
  xtrim (xapp c (xsnoc x acc)) = xapp (xtrim c) (xsnoc x acc).
Proof.
  intros c x acc (s & -> & Hs).
  destruct (xsnoc_solid s acc Hs) as (w & r & E & Hw). rewrite E.
  apply xtrim_xapp_solid, Hw.
Qed.

Local Lemma collapse_trim : forall real v,
  collapse real (pv_stk (pv_trim v)) (pv_out (pv_trim v))
  = xinner xtrim (collapse real (pv_stk v) (pv_out v)).
Proof.
  intros real [[|[p k c|d c] rest] out md]; cbn [pv_trim pv_stk pv_out fset fcontent collapse].
  - reflexivity.
  - destruct (real p); [reflexivity|].
    rewrite xinner_comp. apply xinner_ext. intros acc.
    symmetry. apply xtrim_collapsed, lit_solid.
  - rewrite xinner_comp. apply xinner_ext. intros acc.
    symmetry. apply xtrim_collapsed.
    exists (one lbrack). split; [reflexivity|split; [reflexivity|discriminate]].
Qed.

Local Lemma str_trim_embed : forall l, str_trim (map mk l) = map mk (xtrim l).
Proof.
  intros [|x l]; [reflexivity|]. destruct (str_view x) as [[t ->]|Hx].
  - cbn [map mk str_trim xtrim]. destruct (strip_trailing_ws t); reflexivity.
  - destruct x; [destruct (Hx _ eq_refl)|..]; reflexivity.
Qed.

Local Lemma ttrim_embed : forall st,
  ttrim (fst (tfr st)) (snd (tfr st)) = tfr (xinner xtrim st).
Proof.
  intros [[|[k c] fs] top]; cbn [tfr ttrim xinner fst snd map]; rewrite str_trim_embed;
    reflexivity.
Qed.

Local Lemma pv_trim_add : forall v, pv_mode (pv_trim v) = pv_mode v.
Proof. intros [[|[p k c|d c] rest] out md]; reflexivity. Qed.

Local Lemma vembed_add : forall real x v,
  vembed real (pv_add x v) = tfr (xinner (xsnoc x) (collapse real (pv_stk v) (pv_out v))).
Proof. intros real x v. unfold vembed. rewrite collapse_add. reflexivity. Qed.

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

(* What `tstep` does with a view, region and all: a region that ends is
   its link, a label that never does is text to the paragraph's end, and
   a token of several bytes is its node. *)
Definition vafter (s : string) (n : nat) (real : nat -> bool) (v : pview)
  : tframes * inlines :=
  let '(fs, top) := vembed real v in
  match pv_mode v with
  | PMNormal => (fs, top)
  | PMRegion b kids _ (Some e) _ =>
      temit (mk (region_node b (map mk kids) (region_text s n e b))) fs top
  | PMRegion b kids _ None _ =>
      temit_all (mk (Str (one lbrack)) :: map mk kids
                 ++ [mk (Str (one rbrack ++ sdrop (S n) s))])%list fs top
  | PMAtom x _ => temit (mk x) fs top
  end.

Local Lemma pstep_tstep : forall s m n h t v,
  pv_mode v = PMNormal -> ldesc (pv_live v) -> frames_normal v ->
  step_facts s m n t (pv_live v) ->
  tstep s m n t h (fst (vembed (is_opener m) v)) (snd (vembed (is_opener m) v))
  = vafter s n (is_opener m) (pstep s n h t v).
Proof.
  intros s m n h t [stk out md] Em D N Hf. set (real := is_opener m).
  cbn [pv_mode] in Em. subst md.
  unfold pv_live in D, Hf. cbn [pv_stk pv_out pv_mode] in D, N, Hf.
  unfold vembed at 1. cbn [pv_stk pv_out].
  destruct (collapse real stk out) as [fs0 top0] eqn:Ec. cbn [tfr fst snd].
  set (v := {| pv_stk := stk; pv_out := out; pv_mode := PMNormal |}).
  assert (Norm : forall v', pv_mode v' = PMNormal -> vafter s n real v' = vembed real v')
    by (intros v' E; unfold vafter; rewrite E; destruct (vembed real v'); reflexivity).
  assert (Emb : forall x, vembed real (pv_add x v) = tfr (xinner (xsnoc x) (fs0, top0))).
  { intros x. rewrite vembed_add. unfold v. cbn [pv_stk pv_out]. fold real. rewrite Ec.
    reflexivity. }
  assert (AddN : forall x, vafter s n real (pv_add x v) = tfr (xinner (xsnoc x) (fs0, top0))).
  { intros x. rewrite Norm; [apply Emb|]. rewrite (proj2 (pv_add_live _ _)). reflexivity. }
  assert (Str_ : forall s',
            temit_str s' (map (fun f => (fst f, map mk (snd f))) fs0) (map mk top0)
            = vafter s n real (pv_add (Str s') v)).
  { intros s'. rewrite AddN.
    change (map (fun f : tkind * list inline => (fst f, map mk (snd f))) fs0)
      with (fst (tfr (fs0, top0))).
    change (map mk top0) with (snd (tfr (fs0, top0))).
    apply temit_str_embed. }
  replace (snd (vembed real v)) with (map mk top0)
    by (unfold vembed, v; cbn [pv_stk pv_out]; fold real; rewrite Ec; reflexivity).
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
  destruct t as [c| |k mr op cl| |b|c|ws|ws|vp vn vb vc vr|dk].
  - cbn [tstep pstep]. apply Str_.
  - cbn [tstep pstep]. destruct h.
    + rewrite Norm by reflexivity. unfold vembed, v. cbn [pv_stk pv_out]. fold real.
      rewrite Ec. reflexivity.
    + rewrite AddN.
      rewrite (xinner_ext (xsnoc _) (cons SoftBreak))
        by (intros l; apply xsnoc_nonstr; discriminate).
      destruct fs0 as [|[k c] fs]; reflexivity.
  - (* a delimiter *)
    set (K := KDelim k mr).
    assert (Popen : (op = false -> is_opener m n = false) -> is_closer m n = false ->
              tstep s m n (TDelim k mr op cl) h
                (map (fun f => (fst f, map mk (snd f))) fs0) (map mk top0)
              = vafter s n real (popen n K op (tok_text (TDelim k mr op cl)) v)).
    { intros Ho Hc. cbn [tstep]. unfold popen. destruct op.
      - rewrite Norm by reflexivity. unfold vembed, v. cbn [pv_stk pv_out collapse].
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
    cbn [step_facts] in Hf. unfold v. cbn [pstep]. fold v. unfold pv_live. cbn [pv_stk pv_out].
    fold K in Hf |- *. change (pv_stk v) with stk. change (pv_out v) with out.
    destruct (if cl then pick K (map fitem stk) else PNone) as [p below| |] eqn:P.
    3: { destruct Hf as [Hc Ho]. apply Popen; assumption. }
    2: { destruct Hf as [Hc Ho]. cbn [tstep]. rewrite Ho, Hc. apply Str_. }
    destruct (Nat.ltb (tok_end s p) n); [|destruct Hf as [Hc Ho]; apply Popen; assumption].
    destruct Hf as (Hon & Hcl).
    destruct cl; [|discriminate].
    destruct (Close K p below P Hcl) as (content & rest & Hpc & -> & -> & _).
    pose proof Hcl as (Hcn & _).
    rewrite Hpc. cbn [tstep]. rewrite Hon, Hcn. cbn [map fst snd tkind_of K].
    rewrite Norm by (rewrite (proj2 (pv_add_live _ _)); reflexivity).
    rewrite vembed_add. cbn [pv_stk pv_out].
    rewrite (xinner_ext (xsnoc _) (cons (dnode k (map mk (List.rev content)))))
      by (intros l; apply xsnoc_nonstr, dnode_nonstr).
    rewrite map_rev.
    destruct (collapse real rest out) as [[|[k1 c1] fs1] top1]; reflexivity.
  - (* a `[` *)
    cbn [tstep pstep]. unfold popen. rewrite Norm by reflexivity. unfold vembed.
    cbn [pv_stk pv_out collapse v]. fold real. rewrite Ec.
    cbn [xapp]. destruct (real n); [reflexivity|].
    change (map (fun f : tkind * list inline => (fst f, map mk (snd f))) fs0)
      with (fst (tfr (fs0, top0))).
    change (map mk top0) with (snd (tfr (fs0, top0))).
    rewrite temit_str_embed. reflexivity.
  - (* a `]` *)
    cbn [step_facts] in Hf. unfold v. cbn [pstep]. fold v. unfold pv_live. cbn [pv_stk pv_out].
    change (pv_stk v) with stk. change (pv_out v) with out.
    destruct (pick KBracket (map fitem stk)) as [p below| |] eqn:P.
    2,3: cbn [tstep]; rewrite Hf; apply Str_.
    destruct (Close KBracket p below P Hf) as (content & rest & Hpc & -> & -> & Hn).
    pose proof Hf as (Hcn & _).
    rewrite Hpc. cbn [tstep]. rewrite Hcn. cbn [map fst snd tkind_of].
    destruct (region_end s n b) as [e|] eqn:R.
    + unfold vafter, vembed. cbn [pv_stk pv_out pv_mode tfr]. rewrite map_rev. reflexivity.
    + destruct b.
      * rewrite Norm by reflexivity. unfold vembed. cbn [pv_stk pv_out collapse].
        change (map (fun f : tkind * list inline => (fst f, map mk (snd f)))
                  (fst (collapse real rest out)))
          with (fst (tfr (collapse real rest out))).
        change (map mk (snd (collapse real rest out)))
          with (snd (tfr (collapse real rest out))).
        rewrite <- map_rev, append_empty_r.
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
      * unfold vafter, vembed. cbn [pv_stk pv_out pv_mode tfr]. rewrite map_rev. reflexivity.
  - (* an escape is text *)
    cbn [tstep pstep]. apply Str_.
  - (* an escaped whitespace run: a non-breaking space and the rest of
       the run, or text *)
    cbn [tstep pstep].
    destruct (nbsp_rest ws) as [r|]; [|apply Str_].
    change (map (fun f : tkind * list inline => (fst f, map mk (snd f))) fs0)
      with (fst (tfr (fs0, top0))).
    change (map mk top0) with (snd (tfr (fs0, top0))).
    rewrite temit_embed.
    destruct (nonempty_str r).
    + rewrite Norm by (rewrite !(proj2 (pv_add_live _ _)); reflexivity).
      rewrite vembed_add, collapse_add. unfold v. cbn [pv_add pv_stk pv_out pv_mode].
      fold real. rewrite Ec.
      rewrite (xinner_ext (xsnoc NonBreakingSpace) (cons NonBreakingSpace))
        by (intros l; apply xsnoc_nonstr; discriminate).
      destruct (xinner (cons NonBreakingSpace) (fs0, top0)) as [fs1 top1] eqn:E1.
      cbn [tfr fst snd].
      change (map (fun f : tkind * list inline => (fst f, map mk (snd f))) fs1)
        with (fst (tfr (fs1, top1))).
      change (map mk top1) with (snd (tfr (fs1, top1))).
      rewrite temit_str_embed. reflexivity.
    + rewrite AddN. rewrite (xinner_ext (xsnoc _) (cons NonBreakingSpace))
        by (intros l; apply xsnoc_nonstr; discriminate). reflexivity.
  - (* a hard break, after the text before it is trimmed *)
    cbn [tstep pstep].
    change (map (fun f : tkind * list inline => (fst f, map mk (snd f))) fs0)
      with (fst (tfr (fs0, top0))).
    change (map mk top0) with (snd (tfr (fs0, top0))).
    rewrite ttrim_embed.
    destruct (tfr (xinner xtrim (fs0, top0))) as [fs1 top1] eqn:E1.
    rewrite Norm by (rewrite (proj2 (pv_add_live _ _)), (proj2 (pv_trim_live _)); reflexivity).
    rewrite vembed_add, collapse_trim. unfold v. cbn [pv_stk pv_out].
    fold real. rewrite Ec.
    rewrite (xinner_ext (xsnoc _) (cons HardBreak))
      by (intros l; apply xsnoc_nonstr; discriminate).
    replace fs1 with (fst (tfr (xinner xtrim (fs0, top0)))) by (rewrite E1; reflexivity).
    replace top1 with (snd (tfr (xinner xtrim (fs0, top0)))) by (rewrite E1; reflexivity).
    rewrite temit_embed. reflexivity.
  - (* a verbatim: the dollars before it, then its node, now or at its last byte *)
    cbn [tstep pstep].
    set (X := chars dollar (vp - 2)). set (w := add_text X v).
    assert (Hw : (if Nat.ltb 2 vp
                  then temit_str X (map (fun f : tkind * list inline => (fst f, map mk (snd f))) fs0)
                         (map mk top0)
                  else (map (fun f : tkind * list inline => (fst f, map mk (snd f))) fs0, map mk top0))
                 = tfr (collapse real (pv_stk w) (pv_out w))).
    { unfold w, add_text. destruct (Nat.ltb 2 vp) eqn:E.
      - replace (nonempty_str X) with true
          by (unfold X; destruct vp as [|[|[|vp]]]; try discriminate; reflexivity).
        change (map (fun f : tkind * list inline => (fst f, map mk (snd f))) fs0)
          with (fst (tfr (fs0, top0))).
        change (map mk top0) with (snd (tfr (fs0, top0))).
        rewrite temit_str_embed, collapse_add. unfold v. cbn [pv_stk pv_out]. fold real.
        rewrite Ec. reflexivity.
      - replace X with "" by (unfold X; apply Nat.ltb_ge in E; replace (vp - 2) with 0 by lia;
                              reflexivity).
        cbn [nonempty_str]. unfold v. cbn [pv_stk pv_out]. fold real. rewrite Ec. reflexivity. }
    match goal with |- (let '(_, _) := ?A in _) = _ =>
      replace A with (tfr (collapse real (pv_stk w) (pv_out w))) by (symmetry; exact Hw) end.
    destruct (collapse real (pv_stk w) (pv_out w)) as [fs1 top1] eqn:Ec1. cbn [tfr].
    assert (Ew : pv_mode w = PMNormal)
      by (unfold w, add_text; destruct (nonempty_str X); [rewrite (proj2 (pv_add_live _ _))|];
          reflexivity).
    destruct (Nat.ltb (S n) (tok_end s n)).
    + unfold vafter, vembed. cbn [pv_setmode pv_stk pv_out pv_mode]. rewrite Ec1. reflexivity.
    + rewrite Norm by (rewrite (proj2 (pv_add_live _ _)); exact Ew).
      rewrite vembed_add, Ec1.
      change (map (fun f : tkind * list inline => (fst f, map mk (snd f))) fs1)
        with (fst (tfr (fs1, top1))).
      change (map mk top1) with (snd (tfr (fs1, top1))).
      change (temit (mk (verb_node vp vr vb)) (fst (tfr (fs1, top1))) (snd (tfr (fs1, top1)))
              = tfr (xinner (xsnoc (verb_node vp vr vb)) (fs1, top1))).
      rewrite temit_embed. rewrite (xinner_ext (xsnoc _) (cons (verb_node vp vr vb)))
        by (intros l; apply xsnoc_nonstr; intros ?; apply verb_node_nonstr). reflexivity.
  - (* a run of dollars: text *)
    cbn [tstep pstep]. apply Str_.
Qed.

Local Lemma pv_add_normal : forall x v, frames_normal v -> frames_normal (pv_add x v).
Proof.
  intros x [[|f rest] out md] N; [constructor|].
  unfold frames_normal in *. cbn [pv_add pv_stk] in *.
  apply Forall_cons_iff in N as [Nf N]. constructor; [|exact N].
  destruct f; cbn [fset fcontent] in *; apply normal_xsnoc, Nf.
Qed.

Local Lemma normal_xtrim : forall l, normal l -> normal (xtrim l).
Proof.
  intros [|x l] N; [exact Logic.I|]. destruct (str_view x) as [[t ->]|Hx].
  - cbn [xtrim]. destruct (strip_trailing_ws t) as [|a t'];
      [exact (normal_tail _ _ N)|].
    destruct l as [|y l]; [exact Logic.I|]. exact N.
  - destruct x; [destruct (Hx _ eq_refl)|..]; exact N.
Qed.

Local Lemma pv_trim_normal : forall v, frames_normal v -> frames_normal (pv_trim v).
Proof.
  intros [[|f rest] out md] N; [constructor|].
  unfold frames_normal in *. cbn [pv_trim pv_stk] in *.
  apply Forall_cons_iff in N as [Nf N]. constructor; [|exact N].
  destruct f; cbn [fset fcontent] in *; apply normal_xtrim, Nf.
Qed.

Local Lemma pstep_normal : forall s n h t v,
  frames_normal v -> frames_normal (pstep s n h t v).
Proof.
  intros s n h t [stk out md] N. unfold pstep.
  assert (Open : forall i k op txt, frames_normal (popen i k op txt {| pv_stk := stk; pv_out := out; pv_mode := md |})).
  { intros i k [|] txt; [constructor; [exact Logic.I|exact N]|apply pv_add_normal, N]. }
  destruct t as [c| |k mr op cl| |b|c|ws|ws|vp vn vb vc vr|dk]; try (apply pv_add_normal; exact N);
    [| | | | | |].
  - destruct h; [exact N|apply pv_add_normal, N].
  - unfold pv_live. cbn [pv_stk pv_out].
    destruct (if cl then pick (KDelim k mr) (map fitem stk) else PNone) as [p below| |];
      [|apply pv_add_normal, N|apply Open].
    destruct (Nat.ltb (tok_end s p) n); [|apply Open].
    destruct (pclose_go (KDelim k mr) [] stk) as [[content rest]|] eqn:Hc; [|exact N].
    apply pv_add_normal. exact (proj2 (pclose_go_normal _ stk [] content rest N Logic.I Hc)).
  - apply Open.
  - unfold pv_live. cbn [pv_stk pv_out].
    destruct (pick KBracket (map fitem stk));
      destruct (pclose_go KBracket [] stk) as [[content rest]|] eqn:Hc;
      try (apply pv_add_normal; exact N).
    destruct (pclose_go_normal _ stk [] content rest N Logic.I Hc) as [Nc Nr].
    destruct (region_end s n b); [exact Nr|].
    destruct b; [|exact Nr]. constructor; [apply normal_xsnoc, Nc|exact Nr].
  - destruct (nbsp_rest ws) as [r|]; [|apply pv_add_normal, N].
    destruct (nonempty_str r); repeat apply pv_add_normal; exact N.
  - apply pv_add_normal, pv_trim_normal, N.
  - assert (N' : frames_normal (add_text (chars dollar (vp - 2)) (PView stk out md)))
      by (unfold add_text; destruct (nonempty_str _); [apply pv_add_normal|]; exact N).
    destruct (Nat.ltb _ _); [exact N'|apply pv_add_normal, N'].
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

Local Lemma tok_text_ne : forall t,
  (forall d m b c r, t <> TVerb d m b c r) -> t <> TDollars 0 -> tok_text t <> "".
Proof.
  intros [c| |k [|] [|] cl| |b|c|ws|ws|d m b c r|[|dk]] Hv H0; cbn; try discriminate;
    try (pose proof (dtoken_nonempty k) as H; destruct (dtoken k); discriminate).
  - destruct (Hv d m b c r eq_refl).
  - destruct (H0 eq_refl).
Qed.

Local Lemma clean_xtrim : forall l, clean l -> clean (xtrim l).
Proof.
  intros [|x l] N; [constructor|]. destruct (str_view x) as [[t ->]|Hx].
  - apply Forall_cons_iff in N as [_ N]. cbn [xtrim].
    destruct (strip_trailing_ws t) as [|a t']; [exact N|].
    constructor; [discriminate|exact N].
  - destruct x; [destruct (Hx _ eq_refl)|..]; exact N.
Qed.

Local Lemma pv_trim_clean : forall v, frames_clean v -> frames_clean (pv_trim v).
Proof.
  intros [[|f rest] out md] N; [constructor|].
  unfold frames_clean in *. cbn [pv_trim pv_stk] in *.
  apply Forall_cons_iff in N as [Nf N]. constructor; [|exact N].
  destruct f; cbn [fset fcontent] in *; apply clean_xtrim, Nf.
Qed.

Local Lemma pstep_clean : forall s n h t v,
  t <> TDollars 0 -> frames_clean v -> frames_clean (pstep s n h t v).
Proof.
  intros s n h t [stk out md] H0 N.
  assert (Str_ : forall s', s' <> "" -> Str s' <> Str "") by (intros s' H E; injection E as E; contradiction).
  unfold pstep.
  assert (Open : forall i k op txt, txt <> "" ->
                 frames_clean (popen i k op txt {| pv_stk := stk; pv_out := out; pv_mode := md |})).
  { intros i k [|] txt Ht; [constructor; [constructor|exact N]|apply pv_add_clean; [apply Str_, Ht|exact N]]. }
  destruct t as [c| |k mr op cl| |b|c|ws|ws|vp vn vb vc vr|dk].
  - apply pv_add_clean; [discriminate|exact N].
  - destruct h; [exact N|apply pv_add_clean; [discriminate|exact N]].
  - unfold pv_live. cbn [pv_stk pv_out].
    destruct (if cl then pick (KDelim k mr) (map fitem stk) else PNone) as [p below| |];
      [|apply pv_add_clean; [apply Str_, tok_text_ne; discriminate|exact N]|apply Open, tok_text_ne; discriminate].
    destruct (Nat.ltb (tok_end s p) n); [|apply Open, tok_text_ne; discriminate].
    destruct (pclose_go (KDelim k mr) [] stk) as [[content rest]|] eqn:Hc; [|exact N].
    apply pv_add_clean; [apply dnode_nonstr|].
    exact (proj2 (pclose_go_clean _ stk [] content rest N (Forall_nil _) Hc)).
  - apply Open. discriminate.
  - unfold pv_live. cbn [pv_stk pv_out].
    destruct (pick KBracket (map fitem stk));
      destruct (pclose_go KBracket [] stk) as [[content rest]|] eqn:Hc;
      try (apply pv_add_clean; [apply Str_, tok_text_ne; discriminate|exact N]).
    destruct (pclose_go_clean _ stk [] content rest N (Forall_nil _) Hc) as [Nc Nr].
    destruct (region_end s n b); [exact Nr|].
    destruct b; [|exact Nr]. constructor; [apply clean_xsnoc; [discriminate|exact Nc]|exact Nr].
  - apply pv_add_clean; [apply Str_|exact N].
    unfold esc_text. destruct (is_punct c); discriminate.
  - destruct (nbsp_rest ws) as [r|];
      [|apply pv_add_clean; [apply Str_, (tok_text_ne (TEscWs ws)); discriminate|exact N]].
    destruct (nonempty_str r) eqn:Er.
    + apply pv_add_clean; [|apply pv_add_clean; [discriminate|exact N]].
      apply Str_. intros ->. discriminate Er.
    + apply pv_add_clean; [discriminate|exact N].
  - apply pv_add_clean; [discriminate|apply pv_trim_clean, N].
  - assert (N' : frames_clean (add_text (chars dollar (vp - 2)) (PView stk out md))).
    { unfold add_text. destruct (nonempty_str _) eqn:Ene; [|exact N].
      apply pv_add_clean; [|exact N]. apply Str_. intros E. rewrite E in Ene. discriminate. }
    destruct (Nat.ltb _ _); [exact N'|apply pv_add_clean; [apply verb_node_nonstr|exact N']].
  - apply pv_add_clean; [apply Str_, tok_text_ne; [discriminate|exact H0]|exact N].
Qed.

Local Lemma pbyte_normal : forall i c v, frames_normal v -> frames_normal (pbyte i c v).
Proof.
  intros i c [stk out md] N. unfold pbyte. cbn [pv_mode].
  destruct md as [|b kids d e txt|x e]; [exact N| |].
  - destruct (match e with Some e' => Nat.eqb i e' | None => false end);
      [apply pv_add_normal; exact N|exact N].
  - destruct (Nat.eqb i e); [apply pv_add_normal; exact N|exact N].
Qed.

(* The node a token of several bytes adds is no text. *)
Definition atom_ok (v : pview) : Prop :=
  match pv_mode v with PMAtom x _ => forall s, x <> Str s | _ => True end.

Local Lemma pbyte_clean : forall i c v,
  atom_ok v -> frames_clean v -> frames_clean (pbyte i c v).
Proof.
  intros i c [stk out md] A N. unfold atom_ok in A. unfold pbyte. cbn [pv_mode] in *.
  destruct md as [|b kids d e txt|x e]; [exact N| |].
  - destruct (match e with Some e' => Nat.eqb i e' | None => false end);
      [apply pv_add_clean; [destruct b; discriminate|exact N]|exact N].
  - destruct (Nat.eqb i e); [apply pv_add_clean; [apply A|exact N]|exact N].
Qed.

(*
What the reading says at a token
--------------------------------

The facts `step_facts` asks for hold of the reading `ref_read` computes,
at every token of its chain, because it is valid and it grows one token
at a time: the pairs that close by `n` and the openers by `n` are the
ones the first steps made. *)

Local Lemma rgo_grows : forall s f n st,
  (forall a b, In (a, b) (rs_pairs (rgo s f n st)) -> b < n -> In (a, b) (rs_pairs st))
  /\ (forall a b, In (a, b) (rs_pairs st) -> In (a, b) (rs_pairs (rgo s f n st)))
  /\ (forall q, In q (rs_os (rgo s f n st)) -> q < n -> In q (rs_os st))
  /\ (forall q, In q (rs_os st) -> In q (rs_os (rgo s f n st))).
Proof.
  intros s f. induction f as [|f IH]; intros n st; cbn [rgo].
  { split; [auto|]. split; [auto|]. split; auto. }
  destruct (tok_of s n) as [t|]; [|split; [auto|]; split; [auto|]; split; auto].
  destruct (rstep_grows s n t st) as [Gp Go].
  assert (B : forall q, chain_next s (rs_pairs (rstep s n t st)) n = Some q -> n < q)
    by (intros q Hq; apply chain_next_bound in Hq; lia).
  set (st' := rstep s n t st) in *.
  assert (G : (forall a b, In (a, b) (rs_pairs st') -> b < n -> In (a, b) (rs_pairs st))
              /\ (forall a b, In (a, b) (rs_pairs st) -> In (a, b) (rs_pairs st'))
              /\ (forall q, In q (rs_os st') -> q < n -> In q (rs_os st))
              /\ (forall q, In q (rs_os st) -> In q (rs_os st'))).
  { split; [|split; [|split]].
    - intros a b H Hb. destruct Gp as [Ep|[p Ep]]; rewrite Ep in H; [exact H|].
      destruct H as [E|H]; [injection E as _ ->; lia|exact H].
    - intros a b H. destruct Gp as [Ep|[p Ep]]; rewrite Ep; [exact H|right; exact H].
    - intros q H Hq. destruct Go as [Eo|Eo]; rewrite Eo in H; [exact H|].
      destruct H as [->|H]; [lia|exact H].
    - intros q H. destruct Go as [Eo|Eo]; rewrite Eo; [exact H|right; exact H]. }
  destruct (chain_next s (rs_pairs st') n) as [q|] eqn:Hq; [|exact G].
  specialize (B q eq_refl). destruct (IH q st') as (A1 & A2 & A3 & A4).
  destruct G as (G1 & G2 & G3 & G4).
  split; [|split; [|split]].
  - intros a b H Hb. apply G1; [apply A1; [exact H|lia]|exact Hb].
  - intros a b H. apply A2, G2, H.
  - intros q' H Hq'. apply G3; [apply A3; [exact H|lia]|exact Hq'].
  - intros q' H. apply A4, G4, H.
Qed.

Local Lemma facts_hold : forall s n t st,
  rinv s n st ->
  (forall a b, b <= n -> In (a, b) (fst (ref_read s)) <-> In (a, b) (rs_pairs (rstep s n t st))) ->
  (forall q, q <= n -> In q (snd (ref_read s)) <-> In q (rs_os (rstep s n t st))) ->
  step_facts s (fst (ref_read s)) n t (rs_live st).
Proof.
  intros s n t st I Hp Ho.
  destruct (ref_read s) as [m os] eqn:Er. cbn [fst snd] in *.
  pose proof (ref_read_valid s) as V. rewrite Er in V. destruct V as (P & U & O).
  destruct (rstep_grows s n t st) as [Gp Go].
  (* a token never in `os` opens nothing *)
  assert (NoOpen : forall q, ~ In q os -> is_opener m q = false).
  { intros q Hq. destruct (is_opener m q) eqn:E; [|reflexivity]. exfalso.
    apply is_opener_iff in E as [j Hj]. destruct (P q j Hj) as (_ & _ & _ & [((Hin & _) & _) _] & _).
    exact (Hq Hin). }
  assert (NoClose : rs_pairs (rstep s n t st) = rs_pairs st -> is_closer m n = false).
  { intros E. destruct (is_closer m n) eqn:C; [|reflexivity]. exfalso.
    apply is_closer_iff in C as [i Hi]. apply (Hp i n (le_n n)) in Hi. rewrite E in Hi.
    specialize (ri_bound_pairs s n st I i n Hi). lia. }
  assert (NotOs : rs_os (rstep s n t st) = rs_os st -> ~ In n os).
  { intros E H. apply (Ho n (le_n n)) in H. rewrite E in H.
    specialize (ri_bound_os s n st I n H). lia. }
  assert (Above : forall p, In (p, n) m ->
            forall q k', In (LOpen q k') (rs_live st) -> p < q -> is_opener m q = false).
  { intros p Hpn q k' Hq Hpq. destruct (is_opener m q) eqn:E; [|reflexivity]. exfalso.
    apply is_opener_iff in E as [j Hj].
    apply (ri_cand s n st I) in Hq as (_ & Hqn & _ & _ & Hd).
    destruct (P q j Hj) as (kq & Hkq & _ & Cq & _).
    pose proof Cq as [((_ & _ & _ & _ & Hdq) & _) _].
    destruct (lt_eq_lt_dec j n) as [[Hjn| ->]|Hjn].
    - apply Hd. left. exists j. split; [exact Hjn|].
      apply (Hp q j ltac:(lia)) in Hj.
      destruct Gp as [Ep|[p' Ep]]; rewrite Ep in Hj; [exact Hj|].
      destruct Hj as [E'|Hj]; [injection E' as _ E'; lia|exact Hj].
    - destruct (P p n Hpn) as (kp & Hkp & _ & Cp & _).
      rewrite (close_key_fun s n kq kp Hkq Hkp) in Cq.
      pose proof (closest_live_fun s m os n kp q p Cq Cp). lia.
    - apply Hdq. right. exists p, n. split; [exact Hjn|]. split; [exact Hpn|lia]. }
  (* `n` closes in `m` exactly when the step paired it *)
  assert (Pair : forall p, rs_pairs (rstep s n t st) = (p, n) :: rs_pairs st ->
            is_closer m n = true /\ is_opener m p = true /\ In (p, n) m
            /\ is_opener m n = false).
  { intros p E. assert (Hpn : In (p, n) m) by (apply (Hp p n (le_n n)); rewrite E; left; reflexivity).
    split; [apply is_closer_iff; exists p; exact Hpn|].
    split; [apply is_opener_iff; exists n; exact Hpn|]. split; [exact Hpn|].
    apply NoOpen. intros Hin. apply O in Hin as (_ & _ & Hc & _). apply Hc. exists p. exact Hpn. }
  assert (Paired : forall p, (forall a b, b <= n -> In (a, b) m <-> In (a, b) ((p, n) :: rs_pairs st)) ->
            closes_here m n p (rs_live st) /\ is_opener m n = false).
  { intros p H. assert (Hpn : In (p, n) m) by (apply (H p n (le_n n)); left; reflexivity).
    split; [split; [apply is_closer_iff; exists p; exact Hpn|]; split|].
    - apply is_opener_iff. exists n. exact Hpn.
    - exact (Above p Hpn).
    - apply NoOpen. intros Hin. apply O in Hin as (_ & _ & Hc & _). apply Hc.
      exists p. exact Hpn. }
  assert (Unpaired : (forall a b, b <= n -> In (a, b) m <-> In (a, b) (rs_pairs st)) ->
            is_closer m n = false).
  { intros H. destruct (is_closer m n) eqn:C; [|reflexivity]. exfalso.
    apply is_closer_iff in C as [i Hi]. apply (H i n (le_n n)) in Hi.
    specialize (ri_bound_pairs s n st I i n Hi). lia. }
  assert (Unopened : (forall q, q <= n -> In q os <-> In q (rs_os st)) -> is_opener m n = false).
  { intros H. apply NoOpen. intros Hin. apply (H n (le_n n)) in Hin.
    specialize (ri_bound_os s n st I n Hin). lia. }
  unfold rstep in Hp, Ho. unfold step_facts.
  destruct st as [lv pairs os']. cbn [rs_live rs_pairs rs_os] in *.
  destruct t as [c| |k mr op cl| |b|c|ws|ws|vp vn vb vc vr|dk]; try exact Logic.I.
  - remember (if cl then pick (KDelim k mr) lv else PNone) as r eqn:P'.
    destruct r as [p below| |].
    + remember (Nat.ltb (tok_end s p) n) as l eqn:L. destruct l.
      * destruct (Paired p Hp) as [A B]. split; assumption.
      * unfold ropen in Hp, Ho. split; [apply Unpaired; destruct op; exact Hp|].
        intros ->. apply Unopened. exact Ho.
    + split; [exact (Unpaired Hp)|exact (Unopened Ho)].
    + unfold ropen in Hp, Ho. split; [apply Unpaired; destruct op; exact Hp|].
      intros ->. apply Unopened. exact Ho.
  - remember (pick KBracket lv) as r eqn:P'. destruct r as [p below| |].
    2,3: exact (Unpaired Hp).
    remember (region_end s n b) as r' eqn:R. destruct r' as [e|], b;
      exact (proj1 (Paired p Hp)).
Qed.

(*
The walk
--------
*)

Local Lemma tok_of_at : forall s n, tok_of s n = None <-> tok_at s n = None.
Proof. intros s n. unfold tok_of. destruct (tok_at s n); split; easy. Qed.

Local Lemma punit_lt : forall s i h v j h1 v1,
  punit s i h v = Some (j, h1, v1) -> i < j <= String.length s.
Proof.
  intros s i h v j h1 v1 H. unfold punit in H.
  destruct (pv_mode v).
  - destruct (tok_at s i) as [[t l]|] eqn:E; [|discriminate]. injection H as <- _ _.
    pose proof (tok_at_len s i t l E). destruct (pv_mode (pstep s i h t v)); lia.
  - destruct (get i s) eqn:E; [|discriminate]. injection H as <- _ _.
    apply get_lt in E. lia.
  - destruct (get i s) eqn:E; [|discriminate]. injection H as <- _ _.
    apply get_lt in E. lia.
Qed.

Local Lemma pruns_none : forall s i h v k h2 v2,
  punit s i h v = None -> pruns s i h v k h2 v2 -> k = i /\ h2 = h /\ v2 = v.
Proof.
  intros s i h v k h2 v2 Hu H. inversion H as [|i' h' v' j h1 v1 k' h2' v2' Hu' _];
    [auto|congruence].
Qed.

Local Lemma pruns_some : forall s i h v j h1 v1 k h2 v2,
  punit s i h v = Some (j, h1, v1) -> pruns s i h v k h2 v2 ->
  String.length s <= k -> pruns s j h1 v1 k h2 v2.
Proof.
  intros s i h v j h1 v1 k h2 v2 Hu H Hk.
  inversion H as [i' h' v' E1 E2 E3 E4|i' h' v' j' h1' v1' k' h2' v2' Hu' Hr]; subst.
  - apply punit_lt in Hu. lia.
  - rewrite Hu in Hu'. injection Hu' as <- <- <-. exact Hr.
Qed.

Local Lemma substring_snoc : forall s a k c,
  get (a + k) s = Some c -> substring a (S k) s = (substring a k s ++ one c)%string.
Proof.
  intros s a. revert s. induction a as [|a IHa]; intros s k c H.
  - revert s H. induction k as [|k IHk]; intros [|x s'] H; try discriminate.
    + cbn in H. injection H as ->. destruct s'; reflexivity.
    + cbn [substring]. cbn [Nat.add get] in H. rewrite (IHk s' H). reflexivity.
  - destruct s as [|x s']; [discriminate|]. cbn [substring]. apply IHa. exact H.
Qed.

Local Lemma substring_rest : forall s a,
  substring a (String.length s - a) s = sdrop a s.
Proof.
  induction s as [|x s IH]; intros a; [destruct a; reflexivity|].
  destruct a as [|a].
  - cbn [String.length Nat.sub substring sdrop]. f_equal.
    specialize (IH 0). rewrite Nat.sub_0_r in IH. exact IH.
  - cbn [String.length Nat.sub substring sdrop]. apply IH.
Qed.

Local Lemma get_some : forall s i, i < String.length s -> exists c, get i s = Some c.
Proof.
  induction s as [|x s IH]; intros [|i] H; cbn in *; try lia; [eexists; reflexivity|].
  apply IH. lia.
Qed.

Local Lemma get_end : forall s, get (String.length s) s = None.
Proof. induction s as [|x s IH]; [reflexivity|exact IH]. Qed.

(* Through a region that ends at `e`. *)
Local Lemma region_walk : forall s b kids d e rest out i h2 v2,
  region_end s d b = Some e -> S d <= i <= e ->
  pruns s i false
    (PView rest out (PMRegion b kids d (Some e) (substring (S (S d)) (i - S (S d)) s)))
    (String.length s) h2 v2 ->
  pruns s (S e) false
    (pv_add (region_node b (map mk kids) (region_text s d e b)) (PView rest out PMNormal))
    (String.length s) h2 v2.
Proof.
  intros s b kids d e rest out i h2 v2 R Hi.
  pose proof (region_end_bound s d b e R) as Hb.
  remember (e - i) as k eqn:Hk. revert i Hi Hk.
  induction k as [|k IH]; intros i Hi Hk H.
  - assert (i = e) as -> by lia.
    destruct (get_some s e ltac:(lia)) as [c G].
    eapply pruns_some in H; [|unfold punit; cbn [pv_mode]; rewrite G; reflexivity|lia].
    unfold pbyte in H. cbn [pv_mode] in H. rewrite Nat.eqb_refl in H. exact H.
  - destruct (get_some s i ltac:(lia)) as [c G].
    eapply pruns_some in H; [|unfold punit; cbn [pv_mode]; rewrite G; reflexivity|lia].
    unfold pbyte in H. cbn [pv_mode pv_setmode pv_stk pv_out] in H.
    replace (Nat.eqb i e) with false in H by (symmetry; apply Nat.eqb_neq; lia).
    apply (IH (S i)); [lia|lia|].
    destruct (Nat.eqb i (S d)) eqn:Ed.
    + apply Nat.eqb_eq in Ed. subst i. replace (S (S d) - S (S d)) with 0 by lia.
      replace (S d - S (S d)) with 0 in H by lia. exact H.
    + apply Nat.eqb_neq in Ed. replace (S i - S (S d)) with (S (i - S (S d))) by lia.
      rewrite (substring_snoc s (S (S d)) (i - S (S d)) c); [exact H|].
      replace (S (S d) + (i - S (S d))) with i by lia. exact G.
Qed.

(* A label that never ends reads to the paragraph's end. *)
Local Lemma label_walk : forall s kids d rest out i h2 v2,
  S d <= i <= String.length s ->
  pruns s i false
    (PView rest out (PMRegion false kids d None (substring (S (S d)) (i - S (S d)) s)))
    (String.length s) h2 v2 ->
  v2 = PView rest out (PMRegion false kids d None (sdrop (S (S d)) s)).
Proof.
  intros s kids d rest out i h2 v2 Hi.
  remember (String.length s - i) as k eqn:Hk. revert i Hi Hk.
  induction k as [|k IH]; intros i Hi Hk H.
  - assert (i = String.length s) as -> by lia.
    apply pruns_none in H as (_ & _ & ->); [|unfold punit; cbn [pv_mode]; rewrite get_end; reflexivity].
    rewrite substring_rest. reflexivity.
  - destruct (get_some s i ltac:(lia)) as [c G].
    eapply pruns_some in H; [|unfold punit; cbn [pv_mode]; rewrite G; reflexivity|lia].
    unfold pbyte in H. cbn [pv_mode pv_setmode pv_stk pv_out] in H.
    apply (IH (S i)); [lia|lia|].
    destruct (Nat.eqb i (S d)) eqn:Ed.
    + apply Nat.eqb_eq in Ed. subst i. replace (S (S d) - S (S d)) with 0 by lia.
      replace (S d - S (S d)) with 0 in H by lia. exact H.
    + apply Nat.eqb_neq in Ed. replace (S i - S (S d)) with (S (i - S (S d))) by lia.
      rewrite (substring_snoc s (S (S d)) (i - S (S d)) c); [exact H|].
      replace (S (S d) + (i - S (S d))) with i by lia. exact G.
Qed.

Local Lemma substring_nil : forall s a, substring a 0 s = "".
Proof. induction s as [|x s IH]; intros [|a]; cbn; try reflexivity; apply IH. Qed.

(* A `]` before `[`. *)
Local Lemma tok_at_label : forall s n,
  tok_at s n = Some (TClose false, 1) -> sdrop (S n) s = String lbrack (sdrop (S (S n)) s).
Proof.
  intros s n Hat. replace (S (S n)) with (n + 2) by lia. replace (S n) with (n + 1) by lia.
  rewrite <- !sdrop_sdrop.
  unfold tok_at, next_tok, dollar_tok in Hat. destruct (sdrop n s) as [|c r]; [discriminate|].
  injection Hat as Hat.
  repeat match type of Hat with
  | context [verb_tok ?a ?b] =>
      let E := fresh in destruct (verb_tok_shape a b) as (? & ? & ? & ? & ? & E); rewrite E in Hat;
      cbn iota beta in Hat
  | (if ?b then _ else _) = _ => destruct b eqn:?
  | (match ?x with _ => _ end) = _ => destruct x eqn:?
  end; try discriminate Hat.
  destruct r as [|c2 r]; [discriminate|]. cbn [starts_with] in *.
  destruct (Ascii.eqb c2 lparen); [discriminate|].
  destruct (Ascii.eqb c2 lbrack) eqn:E2; [|discriminate].
  apply Ascii.eqb_eq in E2. subst c2. reflexivity.
Qed.

(* The view enters a region exactly where the chain jumps. *)
Local Lemma pstep_chain : forall s n h t l v st,
  rinv s n st -> tok_at s n = Some (t, l) -> pv_live v = rs_live st -> pv_mode v = PMNormal ->
  chain_next s (rs_pairs (rstep s n t st)) n
  = match pv_mode (pstep s n h t v) with
    | PMNormal => Some (n + l)
    | PMRegion _ _ _ (Some e) _ => Some (S e)
    | PMRegion _ _ _ None _ => None
    | PMAtom _ _ => Some (n + l)
    end.
Proof.
  intros s n h t l v st I Ht Hl Em. unfold chain_next. rewrite Ht.
  destruct t as [c| |k mr op cl| |b|c|ws|ws|vp vn vb vc vr|dk];
    try (rewrite pstep_mode by (assumption || discriminate); reflexivity).
  2: { unfold pstep. destruct (Nat.ltb (S n) (tok_end s n)); [reflexivity|].
       rewrite (proj2 (pv_add_live _ _)), (proj2 (add_text_live _ _)), Em. reflexivity. }
  pose proof (tok_at_close s n b l Ht) as ->.
  assert (Nc : is_closer (rs_pairs st) n = false).
  { destruct (is_closer (rs_pairs st) n) eqn:C; [|reflexivity].
    apply is_closer_iff in C as [i Hi]. specialize (ri_bound_pairs s n st I i n Hi). lia. }
  destruct st as [lv m os]. cbn [rs_live rs_pairs] in *. unfold rstep. cbn [rs_live rs_pairs].
  destruct (pick KBracket lv) as [p below| |] eqn:P.
  2,3: cbn [rs_pairs]; rewrite Nc, pstep_close_none;
       [rewrite (proj2 (pv_add_live _ _)), Em; reflexivity|];
       apply pclose_none; intros p' b'; unfold pv_live in Hl; rewrite Hl, P; discriminate.
  unfold pv_live in Hl. rewrite <- Hl in P.
  destruct (pclose_found _ _ _ _ P) as (content & rest & Hc & _).
  rewrite (pstep_close_found s n h b v content rest Hc).
  assert (C : is_closer ((p, n) :: m) n = true) by (cbn; rewrite Nat.eqb_refl; reflexivity).
  unfold resume. destruct (region_end s n b) as [e|] eqn:R, b; cbn [pv_mode rs_pairs];
    rewrite C; rewrite ?R; try reflexivity.
  rewrite Nat.add_1_r. reflexivity.
Qed.

(* Openers of the stack at the end of the reading are never closed. *)
Local Lemma final_unreal : forall s n st q k,
  rinv s n st -> In (LOpen q k) (rs_live st) -> is_opener (rs_pairs st) q = false.
Proof.
  intros s n st q k I H. apply (ri_cand s n st I) in H as (_ & _ & _ & _ & Hd).
  destruct (is_opener (rs_pairs st) q) eqn:O; [|reflexivity]. exfalso.
  apply is_opener_iff in O as [j Hj]. apply Hd. left. exists j.
  split; [exact (ri_bound_pairs s n st I q j Hj)|exact Hj].
Qed.

Local Lemma frames_unreal : forall real v,
  (forall q k, In (LOpen q k) (pv_live v) -> real q = false) ->
  Forall (fun f => match f with PF q _ _ => real q = false | PB _ _ => True end) (pv_stk v).
Proof.
  intros real v H. apply Forall_forall. intros [q k c|d c] Hf; [|exact Logic.I].
  apply (H q k). unfold pv_live. apply in_map_iff. exists (PF q k c). auto.
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

(* A view with no frame that will be closed reads as its flattening. *)
Local Lemma flatten_tree : forall real v,
  Forall (fun f => match f with PF q _ _ => real q = false | PB _ _ => True end) (pv_stk v) ->
  List.rev (snd (vembed real v)) = map mk (List.rev (pflatten_go [] (pv_stk v) (pv_out v))).
Proof.
  intros real v F. destruct (flatten_collapse real (pv_stk v) (pv_out v) [] F) as [_ E2].
  rewrite E2. unfold vembed, tfr. cbn [xapp snd]. rewrite map_rev. reflexivity.
Qed.

(* Through a token of several bytes. *)
Local Lemma atom_walk : forall s x e v i h2 v2,
  pv_mode v = PMAtom x e -> i <= e -> e < String.length s ->
  pruns s i false v (String.length s) h2 v2 ->
  pruns s (S e) false (pv_add x (pv_setmode PMNormal v)) (String.length s) h2 v2.
Proof.
  intros s x e v i h2 v2 Em Hi He. remember (e - i) as k eqn:Hk. revert i Hi Hk.
  induction k as [|k IH]; intros i Hi Hk H.
  - assert (i = e) as -> by lia. destruct (get_some s e He) as [c G].
    eapply pruns_some in H; [|unfold punit; rewrite Em, G; reflexivity|lia].
    unfold pbyte in H. rewrite Em, Nat.eqb_refl in H. exact H.
  - destruct (get_some s i ltac:(lia)) as [c G].
    eapply pruns_some in H; [|unfold punit; rewrite Em, G; reflexivity|lia].
    unfold pbyte in H. rewrite Em in H.
    replace (i =? e)%nat with false in H by (symmetry; apply Nat.eqb_neq; lia).
    apply (IH (S i)); [lia|lia|exact H].
Qed.

(*
The whole paragraph
-------------------

Along the chain of `ref_read`, the view and `tgo` move together; a
region is one step of `tgo` and a byte at a time for the view. *)

Local Lemma walk_tree : forall s m f n st h v h2 v2,
  m = fst (ref_read s) ->
  rinv s n st -> chain s (rs_pairs st) n -> String.length s - n < f ->
  ref_read s = (rs_pairs (rgo s f n st), rs_os (rgo s f n st)) ->
  pv_mode v = PMNormal -> pv_live v = rs_live st -> frames_normal v ->
  pruns s n h v (String.length s) h2 v2 ->
  List.rev (snd (tgo s m f n h (fst (vembed (is_opener m) v)) (snd (vembed (is_opener m) v))))
  = map mk (List.rev (pflatten v2)).
Proof.
  intros s m f. induction f as [|f IH]; intros n st h v h2 v2 Hm I Hch Hf Hr Em Hl N H; [lia|].
  set (real := is_opener m).
  cbn [tgo]. cbn [rgo] in Hr.
  destruct (tok_of s n) as [t|] eqn:Ht.
  2: { (* the end of the paragraph *)
       apply tok_of_at in Ht.
       apply pruns_none in H as (_ & _ & ->); [|unfold punit; rewrite Em, Ht; reflexivity].
       destruct (vembed real v) as [fs top] eqn:Ev. cbn [fst snd].
       assert (F := frames_unreal real v).
       unfold pflatten, pfinish. rewrite Em.
       rewrite <- (flatten_tree real v); [rewrite Ev; reflexivity|].
       apply F. intros q k Hq. unfold real. rewrite Hm, Hr. cbn [fst].
       rewrite Hl in Hq. exact (final_unreal s n st q k I Hq). }
  pose proof Ht as Ht'. unfold tok_of in Ht'.
  destruct (tok_at s n) as [[t' l]|] eqn:Hat; [|discriminate]. injection Ht' as ->.
  set (st' := rstep s n t st) in *.
  (* what the whole reading says up to `n` is what the step made *)
  assert (G : (forall a b, b <= n -> In (a, b) m <-> In (a, b) (rs_pairs st'))
              /\ (forall q, q <= n -> In q (snd (ref_read s)) <-> In q (rs_os st'))).
  { rewrite Hm, Hr. cbn [fst snd].
    destruct (chain_next s (rs_pairs st') n) as [q|] eqn:Hq; [|split; intros; reflexivity].
    pose proof (chain_next_bound s _ n q Hq) as Hb.
    destruct (rgo_grows s f q st') as (A1 & A2 & A3 & A4). split.
    - intros a b Hb'. split; [intros H0; apply A1; [exact H0|lia]|apply A2].
    - intros q' Hq'. split; [intros H0; apply A3; [exact H0|lia]|apply A4]. }
  destruct G as [Gp Go].
  assert (Hcn : chain_next s m n = chain_next s (rs_pairs st') n).
  { unfold chain_next. replace (is_closer m n) with (is_closer (rs_pairs st') n); [reflexivity|].
    apply Bool.eq_true_iff_eq. rewrite !is_closer_iff.
    split; intros [i Hi]; exists i; apply (Gp i n (le_n n)); exact Hi. }
  assert (Hfacts : step_facts s m n t (pv_live v)).
  { rewrite Hl, Hm. apply facts_hold; [exact I| |].
    - intros a b Hb. rewrite <- Hm. apply Gp, Hb.
    - exact Go. }
  pose proof (pstep_tstep s m n h t v Em ltac:(rewrite Hl; exact (ri_desc s n st I)) N Hfacts) as E.
  fold real in E. rewrite E. clear E.
  pose proof (pstep_chain s n h t l v st I Hat Hl Em) as PC. fold st' in PC.
  rewrite Hcn, PC.
  apply (pruns_some s n h v (match pv_mode (pstep s n h t v) with PMNormal => n + l | _ => S n end)
           (is_hard t) (pstep s n h t v)) in H; [|unfold punit; rewrite Em, Hat; reflexivity|lia].
  destruct (rinv_next s n st t I Hch Ht) as [Hch' Nx].
  fold st' in Nx, Hch'. rewrite PC in Nx, Hr.
  pose proof (pstep_live s n h t v st Hl) as Hl'.
  pose proof (pstep_normal s n h t v N) as N'.
  fold st' in Hl'.
  pose proof (tok_at_len s n t l Hat) as Hlen.
  unfold vafter.
  destruct (pv_mode (pstep s n h t v)) as [|b kids d [e|] txt|x e] eqn:Em'.
  - (* the next token *)
    destruct Nx as [I' Hq'].
    destruct (vembed real (pstep s n h t v)) as [fs top] eqn:Ev.
    replace fs with (fst (vembed real (pstep s n h t v))) by (rewrite Ev; reflexivity).
    replace top with (snd (vembed real (pstep s n h t v))) by (rewrite Ev; reflexivity).
    apply (IH (n + l) st' (is_hard t) (pstep s n h t v) h2 v2 Hm I' Hq' ltac:(lia) Hr Em' Hl' N' H).
  - (* a region that ends: its bytes, then the token after it *)
    assert (Rg : exists rest, t = TClose b /\ d = n /\ txt = "" /\ region_end s n b = Some e
              /\ pstep s n h t v = PView rest (pv_out v) (PMRegion b kids n (Some e) "")).
    { destruct t as [c| |k mr op cl| |b0|c|ws|ws|vp vn vb vc vr|dk];
        try (rewrite pstep_mode in Em' by (assumption || discriminate); discriminate);
        try (unfold pstep in Em'; destruct (Nat.ltb _ _); cbn [pv_mode pv_setmode] in Em';
             [discriminate
             |rewrite (proj2 (pv_add_live _ _)), (proj2 (add_text_live _ _)), Em in Em';
              discriminate]).
      destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|] eqn:Hc.
      2: { rewrite pstep_close_none in Em' by exact Hc.
           rewrite (proj2 (pv_add_live _ _)), Em in Em'. discriminate. }
      rewrite (pstep_close_found s n h b0 v content rest Hc) in Em' |- *.
      destruct (region_end s n b0) as [e'|] eqn:R, b0; cbn [pv_mode] in Em'; try discriminate;
        inversion Em'; subst; exists rest; auto. }
    destruct Rg as (rest & -> & -> & -> & R & Ep).
    pose proof (tok_at_close s n b l Hat) as ->.
    pose proof (region_end_bound s n b e R) as Hb.
    rewrite Ep in H, Hl', N' |- *. cbn [is_hard] in *.
    rewrite <- (substring_nil s (S (S n))), <- (Nat.sub_diag (S (S n))) in H.
    replace (S (S n) - S (S n)) with (S n - S (S n)) in H by lia.
    apply (region_walk s b kids n e rest (pv_out v) (S n) h2 v2 R ltac:(lia)) in H.
    destruct Nx as [I' Hq'].
    set (ve := pv_add (region_node b (map mk kids) (region_text s n e b))
                 (PView rest (pv_out v) PMNormal)) in H.
    assert (Eve : vembed real ve
                  = temit (mk (region_node b (map mk kids) (region_text s n e b)))
                      (fst (vembed real (PView rest (pv_out v) (PMRegion b kids n (Some e) ""))))
                      (snd (vembed real (PView rest (pv_out v) (PMRegion b kids n (Some e) ""))))).
    { unfold ve. rewrite vembed_add. unfold vembed. cbn [pv_stk pv_out].
      rewrite temit_embed. f_equal. apply xinner_ext. intros acc.
      apply xsnoc_nonstr, region_node_nonstr. }
    destruct (vembed real (PView rest (pv_out v) (PMRegion b kids n (Some e) ""))) as [fs top].
    cbn [fst snd] in Eve.
    destruct (temit (mk (region_node b (map mk kids) (region_text s n e b))) fs top) as [fs' top'].
    replace fs' with (fst (vembed real ve)) by (rewrite Eve; reflexivity).
    replace top' with (snd (vembed real ve)) by (rewrite Eve; reflexivity).
    apply (IH (S e) st' false ve h2 v2 Hm I' Hq' ltac:(lia) Hr).
    + unfold ve. rewrite (proj2 (pv_add_live _ _)). reflexivity.
    + unfold ve. rewrite (proj1 (pv_add_live _ _)). exact Hl'.
    + unfold ve. apply pv_add_normal. exact N'.
    + exact H.
  - (* a label that never ends: the rest of the paragraph is text *)
    assert (Rg : exists rest, t = TClose false /\ b = false /\ d = n /\ txt = ""
              /\ pstep s n h t v = PView rest (pv_out v) (PMRegion false kids n None "")).
    { destruct t as [c| |k mr op cl| |b0|c|ws|ws|vp vn vb vc vr|dk];
        try (rewrite pstep_mode in Em' by (assumption || discriminate); discriminate);
        try (unfold pstep in Em'; destruct (Nat.ltb _ _); cbn [pv_mode pv_setmode] in Em';
             [discriminate
             |rewrite (proj2 (pv_add_live _ _)), (proj2 (add_text_live _ _)), Em in Em';
              discriminate]).
      destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|] eqn:Hc.
      2: { rewrite pstep_close_none in Em' by exact Hc.
           rewrite (proj2 (pv_add_live _ _)), Em in Em'. discriminate. }
      rewrite (pstep_close_found s n h b0 v content rest Hc) in Em' |- *.
      destruct (region_end s n b0) as [e'|] eqn:R, b0; cbn [pv_mode] in Em'; try discriminate;
        inversion Em'; subst; exists rest; auto. }
    destruct Rg as (rest & -> & -> & -> & -> & Ep).
    pose proof (tok_at_close s n false l Hat) as ->.
    rewrite Ep in H, Hl', N' |- *.
    rewrite <- (substring_nil s (S (S n))), <- (Nat.sub_diag (S (S n))) in H.
    replace (S (S n) - S (S n)) with (S n - S (S n)) in H by lia.
    apply (label_walk s kids n rest (pv_out v) (S n) h2 v2 ltac:(lia)) in H. subst v2.
    rewrite (tok_at_label s n Hat). clear Nx.
    pose proof (rinv_step s n st (TClose false) Ht I Hch) as I'. fold st' in I'.
    assert (F : Forall (fun f => match f with PF q _ _ => real q = false | PB _ _ => True end) rest).
    { change rest with (pv_stk (PView rest (pv_out v) PMNormal)).
      apply frames_unreal. intros q k Hq. unfold real. rewrite Hm, Hr. cbn [fst].
      apply (final_unreal s (S n) st' q k I'). rewrite <- Hl'. exact Hq. }
    set (V := PView rest (pv_out v) (PMRegion false kids n None (sdrop (S (S n)) s))).
    set (L := (Str (one lbrack) :: kids
               ++ [Str (one rbrack ++ one lbrack ++ sdrop (S (S n)) s)])%list).
    unfold pflatten, pfinish. cbn [pv_mode V]. fold L.
    destruct (pv_add_all_collapse real L V) as [C1 C2].
    assert (F' : Forall (fun f => match f with PF q _ _ => real q = false | PB _ _ => True end)
                   (pv_stk (pv_add_all L V))).
    { assert (G : forall stk,
                Forall (fun f => match f with PF q _ _ => real q = false | PB _ _ => True end) stk
                <-> Forall (fun x => match x with LOpen q _ => real q = false | LBar _ => True end)
                      (map fitem stk)).
      { intros stk. rewrite Forall_map. split; apply Forall_impl; intros [] H0; exact H0. }
      apply G. rewrite C2. apply G. exact F. }
    destruct (flatten_collapse real (pv_stk (pv_add_all L V)) (pv_out (pv_add_all L V)) [] F')
      as [_ E2].
    destruct (flatten_collapse real (pv_stk V) (pv_out V) [] F) as [E1 _].
    rewrite E2, C1, E1. cbn [xinner xapp fst snd].
    unfold vembed. cbn [pv_stk pv_out V] in E1 |- *. rewrite E1. cbn [tfr fst snd map].
    set (X := snd (collapse real rest (pv_out v))).
    replace (mk (Str (one lbrack)) :: map mk kids
             ++ [mk (Str (one rbrack ++ String lbrack (sdrop (S (S n)) s)))])%list
      with (map mk L) by (unfold L; cbn [map]; rewrite map_app; reflexivity).
    change ([] : tframes) with (fst (tfr ([], X))).
    change (map mk X) with (snd (tfr ([], X))).
    rewrite temit_all_embed. cbn [xinner tfr snd]. rewrite map_rev. reflexivity.
  - (* a token of several bytes: its bytes, then the token after it *)
    assert (Ra : exists vp vn vb vc vr, t = TVerb vp vn vb vc vr /\ x = verb_node vp vr vb
                 /\ e = pred (tok_end s n) /\ S n < tok_end s n
                 /\ pstep s n h t v = pv_setmode (PMAtom x e) (add_text (chars dollar (vp - 2)) v)).
    { destruct t as [c| |k mr op cl| |b0|c|ws|ws|vp vn vb vc vr|dk];
        try (rewrite pstep_mode in Em' by (assumption || discriminate); discriminate).
      - destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|] eqn:Hc.
        2: { rewrite pstep_close_none in Em' by exact Hc.
             rewrite (proj2 (pv_add_live _ _)), Em in Em'. discriminate. }
        rewrite (pstep_close_found s n h b0 v content rest Hc) in Em'.
        destruct (region_end s n b0), b0; discriminate Em'.
      - unfold pstep in Em' |- *. destruct (Nat.ltb (S n) (tok_end s n)) eqn:L.
        + cbn [pv_setmode pv_mode] in Em'. injection Em' as <- <-.
          apply Nat.ltb_lt in L. exists vp, vn, vb, vc, vr. auto.
        + rewrite (proj2 (pv_add_live _ _)), (proj2 (add_text_live _ _)), Em in Em'. discriminate. }
    destruct Ra as (vp & vn & vb & vc & vr & -> & -> & -> & Hlt & Ep).
    set (w := add_text (chars dollar (vp - 2)) v) in *.
    assert (Hend : tok_end s n = n + l) by (unfold tok_end; rewrite Hat; reflexivity).
    rewrite Hend in Hlt, Ep. rewrite Ep in H, Hl', N' |- *.
    apply (atom_walk s _ (pred (n + l))
             (pv_setmode (PMAtom (verb_node vp vr vb) (pred (n + l))) w) (S n) h2 v2 eq_refl
             ltac:(lia) ltac:(lia)) in H.
    replace (S (pred (n + l))) with (n + l) in H by lia.
    destruct Nx as [I' Hq'].
    set (ve := pv_add (verb_node vp vr vb) (pv_setmode PMNormal
                 (pv_setmode (PMAtom (verb_node vp vr vb) (pred (n + l))) w))) in H.
    assert (Eve : vembed real ve
                  = temit (mk (verb_node vp vr vb))
                      (fst (vembed real (pv_setmode (PMAtom (verb_node vp vr vb) (pred (n + l))) w)))
                      (snd (vembed real (pv_setmode (PMAtom (verb_node vp vr vb) (pred (n + l))) w)))).
    { unfold ve. rewrite vembed_add. unfold vembed. cbn [pv_stk pv_out pv_setmode].
      rewrite temit_embed. f_equal. apply xinner_ext. intros acc.
      apply xsnoc_nonstr. intros ?; apply verb_node_nonstr. }
    unfold vafter. cbn [pv_mode pv_setmode].
    destruct (vembed real (pv_setmode (PMAtom (verb_node vp vr vb) (pred (n + l))) w)) as [fs top].
    cbn [fst snd] in Eve.
    destruct (temit (mk (verb_node vp vr vb)) fs top) as [fs' top'].
    replace fs' with (fst (vembed real ve)) by (rewrite Eve; reflexivity).
    replace top' with (snd (vembed real ve)) by (rewrite Eve; reflexivity).
    apply (IH (n + l) st' false ve h2 v2 Hm I' Hq' ltac:(lia) Hr).
    + unfold ve. rewrite (proj2 (pv_add_live _ _)). reflexivity.
    + unfold ve. rewrite (proj1 (pv_add_live _ _)). exact Hl'.
    + unfold ve. apply pv_add_normal. exact N'.
    + exact H.
Qed.

Theorem tree_of_pruns : forall s h2 v2,
  pruns s 0 false pv0 (String.length s) h2 v2 ->
  tree_of s (fst (ref_read s)) = map mk (List.rev (pflatten v2)).
Proof.
  intros s h2 v2 H. unfold tree_of.
  pose proof (walk_tree s _ (S (String.length s)) 0 rstart false pv0 h2 v2 eq_refl
                (rinv_start s) (chain_start _ _) ltac:(lia) eq_refl eq_refl eq_refl
                (Forall_nil _) H) as W.
  exact W.
Qed.

(*
The scanner
===========

Between units the scanner's state is a text-mode state or a region's,
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

(* The view has no named bracket: `:` is outside the alphabet. *)
Lemma tag_close_oview : forall cm v, tag_close (oview cm v) = None.
Proof.
  intros cm v. unfold tag_close, oview. cbn [os_stk].
  assert (H : forall stk pend, tag_close_go pend (map (oframe cm) stk) = None).
  { induction stk as [|f stk IH]; intros pend; [reflexivity|].
    destruct f as [p [k mr|] c|d c]; cbn [map oframe tag_close_go fr_kind];
      [apply IH|reflexivity|reflexivity]. }
  rewrite H. reflexivity.
Qed.

Definition top_of (v : pview) : list inline :=
  match pv_stk v with [] => pv_out v | f :: _ => fcontent f end.

Definition starts_text (l : list inline) : bool :=
  match l with Str _ :: _ => true | _ => false end.

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

The stack is ordered, its positions are before `n` and its openers'
tokens end by `n`, and its delimiter frames are of the rows here; and
outside a region the innermost frame is empty exactly when its opener's
token ends at `n`. *)

Definition fend (ps : string) (f : pframe) : nat :=
  match f with PF p _ _ => tok_end ps p | PB d _ => S d end.

(* A frame's token ends before any frame above it opens. *)
Definition stk_order (ps : string) (stk : list pframe) : Prop :=
  StronglySorted (fun a b => fend ps b <= lpos (fitem a)) stk.

Definition pv_ok (ps : string) (n : nat) (v : pview) : Prop :=
  ldesc (pv_live v) /\ (forall x, In x (pv_live v) -> lpos x < n)
  /\ (forall p k c, In (PF p k c) (pv_stk v) -> tok_end ps p <= n)
  /\ self_frames (pv_stk v) /\ stk_order ps (pv_stk v)
  /\ (forall p k c, In (PF p k c) (pv_stk v) -> p < tok_end ps p)
  /\ match pv_mode v, pv_stk v with
     | PMNormal, PF p _ c :: _ => c = [] <-> tok_end ps p = n
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

Local Lemma in_stk_add : forall x v p k c,
  In (PF p k c) (pv_stk (pv_add x v)) -> exists c', In (PF p k c') (pv_stk v).
Proof.
  intros x [[|f rest] out md] p k c H; [destruct H|].
  cbn [pv_add pv_stk] in H. destruct H as [E|H]; [|exists c; right; exact H].
  destruct f as [q k' c'|d c']; cbn [fset] in E; [|discriminate].
  injection E as -> -> _. exists c'. left. reflexivity.
Qed.

Local Lemma stk_order_set : forall ps f c rest,
  stk_order ps (f :: rest) -> stk_order ps (fset f c :: rest).
Proof.
  intros ps f c rest H. apply StronglySorted_inv in H as [H F]. constructor; [exact H|].
  rewrite Forall_forall in F |- *. intros y Hy. specialize (F y Hy).
  destruct f; exact F.
Qed.

Local Lemma stk_order_add : forall ps x v,
  stk_order ps (pv_stk v) -> stk_order ps (pv_stk (pv_add x v)).
Proof. intros ps x [[|f rest] out md] H; [exact H|apply stk_order_set, H]. Qed.

Local Lemma stk_order_trim : forall ps v,
  stk_order ps (pv_stk v) -> stk_order ps (pv_stk (pv_trim v)).
Proof. intros ps [[|f rest] out md] H; [exact H|apply stk_order_set, H]. Qed.

Local Lemma pv_ok_add : forall ps n n' x v,
  ldesc (pv_live v) -> (forall y, In y (pv_live v) -> lpos y < n) ->
  (forall p k c, In (PF p k c) (pv_stk v) -> tok_end ps p <= n) ->
  self_frames (pv_stk v) -> stk_order ps (pv_stk v) ->
  (forall p k c, In (PF p k c) (pv_stk v) -> p < tok_end ps p) ->
  n < n' -> pv_ok ps n' (pv_add x v).
Proof.
  intros ps n n' x v D Bd Be B So Bt Hn. destruct (pv_add_live x v) as [E1 E2].
  split; [rewrite E1; exact D|].
  split; [intros y H; rewrite E1 in H; specialize (Bd y H); lia|].
  split; [intros p k c H; destruct (in_stk_add x v p k c H) as [c' H']; specialize (Be p k c' H'); lia|].
  split; [apply self_frames_add, B|]. split; [apply stk_order_add, So|].
  split; [intros p k c H; destruct (in_stk_add x v p k c H) as [c' H']; exact (Bt p k c' H')|].
  rewrite E2. unfold pv_add. destruct (pv_stk v) as [|f rest] eqn:E; [destruct (pv_mode v); exact Logic.I|].
  cbn [pv_stk pv_mode]. destruct (pv_mode v); try exact Logic.I.
  destruct f as [p k c|d c]; cbn [fset fcontent]; [|exact Logic.I].
  assert (tok_end ps p <= n) by (apply (Be p k c); left; reflexivity).
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
Local Lemma pv_ok_close : forall ps n v K p below content rest,
  pv_ok ps n v -> pick K (pv_live v) = PFound p below ->
  pclose_go K [] (pv_stk v) = Some (content, rest) ->
  ldesc (map fitem rest) /\ (forall y, In y (map fitem rest) -> lpos y < p)
  /\ (forall q k c, In (PF q k c) rest -> tok_end ps q <= n)
  /\ self_frames rest /\ stk_order ps rest
  /\ (forall q k c, In (PF q k c) rest -> q < tok_end ps q) /\ p < n.
Proof.
  intros ps n v K p below content rest (D & Bd & Be & B & So & Bt & _) P Hc.
  unfold pv_live in P, D, Bd.
  destruct (pick_split K _ p below P) as (above & c & rest' & E & F & Hb).
  rewrite E in Hc, D, Bd, Be, B, So, Bt.
  destruct (pclose_split K above p c rest' [] F) as [content' Hc'].
  rewrite Hc in Hc'. injection Hc' as <- <-.
  assert (Hpn : p < n).
  { apply (Bd (LOpen p K)). rewrite map_app. apply in_or_app. right. left. reflexivity. }
  split; [exact (ldesc_below above _ rest D)|].
  split; [|split; [|split; [|split; [|split; [|exact Hpn]]]]].
  - intros y Hy. rewrite map_app in D. cbn [map] in D.
    clear -D Hy. induction above as [|g above IH]; cbn [app] in D.
    + apply StronglySorted_inv in D as [_ F]. rewrite Forall_forall in F. exact (F y Hy).
    + apply StronglySorted_inv in D as [D _]. exact (IH D).
  - intros q k c' H. apply (Be q k c'). apply in_or_app. right. right. exact H.
  - unfold self_frames in B. apply Forall_app in B as [_ B].
    apply Forall_cons_iff in B as [_ B]. exact B.
  - clear -So. induction above as [|g above IH]; cbn [app] in So.
    + apply StronglySorted_inv in So as [So _]. exact So.
    + apply StronglySorted_inv in So as [So _]. exact (IH So).
  - intros q k c' H. apply (Bt q k c'). apply in_or_app. right. right. exact H.
Qed.

Local Lemma self_frames_trim : forall v,
  self_frames (pv_stk v) -> self_frames (pv_stk (pv_trim v)).
Proof.
  intros [[|f rest] out md] B; [exact B|].
  apply Forall_cons_iff in B as [Bk B]. constructor; [|exact B].
  destruct f as [p [k mr|] c|d c]; exact Bk.
Qed.

(* The innermost frame holds something: true right after a hard break,
   which the break that follows it does not add to. *)
Definition top_filled (v : pview) : Prop :=
  match pv_mode v, pv_stk v with
  | PMNormal, PF _ _ c :: _ => c <> []
  | _, _ => True
  end.

Local Lemma in_stk_trim : forall v p k c,
  In (PF p k c) (pv_stk (pv_trim v)) -> exists c', In (PF p k c') (pv_stk v).
Proof.
  intros [[|f rest] out md] p k c H; [destruct H|].
  cbn [pv_trim pv_stk] in H. destruct H as [E|H]; [|exists c; right; exact H].
  destruct f as [q k' c'|d c']; cbn [fset] in E; [|discriminate].
  injection E as -> -> _. exists c'. left. reflexivity.
Qed.

(* Everything on the stack ends by `n`. *)
Local Lemma fend_le : forall ps n v f,
  (forall x, In x (pv_live v) -> lpos x < n) ->
  (forall p k c, In (PF p k c) (pv_stk v) -> tok_end ps p <= n) ->
  In f (pv_stk v) -> fend ps f <= n.
Proof.
  intros ps n v [p k c|d c] Bd Be H; cbn [fend].
  - exact (Be p k c H).
  - assert (lpos (LBar d) < n) by (apply Bd; unfold pv_live; apply in_map_iff;
                                   exists (PB d c); auto).
    cbn in H0. lia.
Qed.

Local Lemma pv_ok_step : forall ps n h t l v,
  pv_ok ps n v -> pv_mode v = PMNormal -> tok_at ps n = Some (t, l) ->
  (forall k mr op cl, t = TDelim k mr op cl -> self_row k = true) ->
  (t = TBreak -> h = true -> top_filled v) ->
  pv_ok ps (n + l) (pstep ps n h t v).
Proof.
  intros ps n h t l v Ok Em Ht Hb Hh. pose proof Ok as (D & Bd & Be & B & So & Bt & Inn).
  pose proof (tok_at_len ps n t l Ht) as Hl.
  assert (Hend : tok_end ps n = n + l) by (unfold tok_end; rewrite Ht; reflexivity).
  assert (Add : forall x, pv_ok ps (n + l) (pv_add x v))
    by (intros x; apply (pv_ok_add ps n); [exact D|exact Bd|exact Be|exact B|exact So|exact Bt|lia]).
  assert (Open : forall k op txt, (forall k' mr, k = KDelim k' mr -> self_row k' = true) ->
                   pv_ok ps (n + l) (popen n k op txt v)).
  { intros k [|] txt Hk; [|apply Add].
    unfold popen. split; [|split; [|split; [|split; [|split; [|split]]]]].
    - unfold pv_live. cbn [pv_stk map]. constructor; [exact D|].
      apply Forall_forall. intros y H. exact (Bd y H).
    - unfold pv_live. cbn [pv_stk map fitem lpos].
      intros y [<-|H]; [cbn; lia|]. specialize (Bd y H). lia.
    - cbn [pv_stk]. intros p k' c [E|H]; [injection E as <- _ _; lia|].
      specialize (Be p k' c H). lia.
    - constructor; [|exact B]. destruct k as [k' mr|]; [exact (Hk k' mr eq_refl)|exact Logic.I].
    - constructor; [exact So|]. apply Forall_forall. intros f Hf. cbn [fitem lpos].
      exact (fend_le ps n v f Bd Be Hf).
    - cbn [pv_stk]. intros p k' c [E|H]; [injection E as <- _ _; lia|exact (Bt p k' c H)].
    - cbn [pv_stk pv_mode]. rewrite Em. split; [intros _; exact Hend|reflexivity]. }
  unfold pstep.
  destruct t as [c| |k mr op cl| |b|c|ws|ws|vp vn vb vc vr|dk]; try apply Add.
  - (* a break after a hard break adds nothing, to a frame already filled *)
    destruct h; [|apply Add].
    specialize (Hh eq_refl eq_refl). unfold top_filled in Hh. rewrite Em in Hh.
    split; [exact D|]. split; [intros y H; specialize (Bd y H); lia|].
    split; [intros p k c H; specialize (Be p k c H); lia|].
    split; [exact B|]. split; [exact So|]. split; [exact Bt|]. rewrite Em.
    destruct (pv_stk v) as [|[p k c|d c] rest] eqn:Es; try exact Logic.I.
    assert (Hp : tok_end ps p <= n) by (apply (Be p k c); left; reflexivity).
    split; [intros Hc; contradiction|lia].
  - specialize (Hb k mr op cl eq_refl).
    destruct (if cl then pick (KDelim k mr) (pv_live v) else PNone) as [p below| |] eqn:P;
      [|apply Add|apply Open; intros k' mr' E; injection E as <- _; exact Hb].
    destruct (Nat.ltb (tok_end ps p) n); [|apply Open; intros k' mr' E; injection E as <- _; exact Hb].
    destruct cl; [|discriminate].
    destruct (pclose_go (KDelim k mr) [] (pv_stk v)) as [[content rest]|] eqn:Hc;
      [|destruct (pclose_found _ _ _ _ P) as (? & ? & E & _); congruence].
    destruct (pv_ok_close ps n v _ p below content rest Ok P Hc) as (D' & Bd' & Be' & B' & So' & Bt' & Hpn).
    apply (pv_ok_add ps n _ _ (PView rest (pv_out v) PMNormal)); unfold pv_live; cbn [pv_stk].
    + exact D'.
    + intros y H. specialize (Bd' y H). lia.
    + exact Be'.
    + exact B'.
    + exact So'.
    + exact Bt'.
    + lia.
  - apply Open. intros k' mr E. discriminate.
  - destruct (pick KBracket (pv_live v)) as [p below| |] eqn:P;
      destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|] eqn:Hc;
      try apply Add.
    destruct (pv_ok_close ps n v _ p below content rest Ok P Hc) as (D' & Bd' & Be' & B' & So' & Bt' & Hpn).
    destruct (region_end ps n b) as [e|]; [|destruct b].
    + split; [exact D'|]. split; [intros y H; specialize (Bd' y H); cbn; lia|].
      split; [intros q k c H; specialize (Be' q k c H); lia|].
      split; [exact B'|]. split; [exact So'|]. split; [exact Bt'|exact Logic.I].
    + split; [|split; [|split; [|split; [|split; [|split]]]]]; unfold pv_live; cbn [pv_stk pv_mode map fitem].
      * constructor; [exact D'|]. apply Forall_forall. intros y H. specialize (Bd' y H). cbn. lia.
      * intros y [<-|H]; [cbn; lia|]. specialize (Bd' y H). lia.
      * intros q k c [E|H]; [discriminate|]. specialize (Be' q k c H). lia.
      * constructor; [exact Logic.I|exact B'].
      * constructor; [exact So'|]. apply Forall_forall. intros f Hf. cbn [fitem lpos].
        destruct f as [q k c|d c]; cbn [fend].
        -- exact (Be' q k c Hf).
        -- assert (lpos (LBar d) < p) by (apply Bd'; apply in_map_iff; exists (PB d c); auto).
           cbn in H. lia.
      * intros q k c [E|H]; [discriminate|exact (Bt' q k c H)].
      * exact Logic.I.
    + split; [exact D'|]. split; [intros y H; specialize (Bd' y H); cbn; lia|].
      split; [intros q k c H; specialize (Be' q k c H); lia|].
      split; [exact B'|]. split; [exact So'|]. split; [exact Bt'|exact Logic.I].
  - destruct (nbsp_rest ws) as [r|]; [|apply Add].
    destruct (nonempty_str r); [|apply Add].
    destruct (pv_add_live NonBreakingSpace v) as [E1 _].
    apply (pv_ok_add ps n); [rewrite E1; exact D|rewrite E1; exact Bd| |apply self_frames_add, B
                            |apply stk_order_add, So| |lia];
      intros p k c H; destruct (in_stk_add _ _ p k c H) as [c' H'];
      first [exact (Be p k c' H')|exact (Bt p k c' H')].
  - destruct (pv_trim_live v) as [E1 _].
    apply (pv_ok_add ps n); [rewrite E1; exact D|rewrite E1; exact Bd| |apply self_frames_trim, B
                            |apply stk_order_trim, So| |lia];
      intros p k c H; destruct (in_stk_trim _ p k c H) as [c' H'];
      first [exact (Be p k c' H')|exact (Bt p k c' H')].
  - set (w := add_text (chars dollar (vp - 2)) v).
    assert (Fw : ldesc (pv_live w) /\ (forall y, In y (pv_live w) -> lpos y < n)
                 /\ (forall p k c, In (PF p k c) (pv_stk w) -> tok_end ps p <= n)
                 /\ self_frames (pv_stk w) /\ stk_order ps (pv_stk w)
                 /\ (forall p k c, In (PF p k c) (pv_stk w) -> p < tok_end ps p)).
    { unfold w, add_text.
      destruct (nonempty_str _); [|exact (conj D (conj Bd (conj Be (conj B (conj So Bt)))))].
      destruct (pv_add_live (Str (chars dollar (vp - 2))) v) as [E1 _]. rewrite E1.
      split; [exact D|]. split; [exact Bd|].
      split; [intros p k c H; destruct (in_stk_add _ _ p k c H) as [c' H']; exact (Be p k c' H')|].
      split; [apply self_frames_add, B|]. split; [apply stk_order_add, So|].
      intros p k c H; destruct (in_stk_add _ _ p k c H) as [c' H']; exact (Bt p k c' H'). }
    destruct Fw as (Dw & Bdw & Bew & Bw & Sow & Btw).
    destruct (Nat.ltb _ _).
    + split; [exact Dw|]. split; [intros y H; specialize (Bdw y H); lia|].
      split; [intros p k c H; specialize (Bew p k c H); lia|].
      split; [exact Bw|]. split; [exact Sow|]. split; [exact Btw|exact Logic.I].
    + apply (pv_ok_add ps n); [exact Dw|exact Bdw|exact Bew|exact Bw|exact Sow|exact Btw|lia].
Qed.

Local Lemma pv_ok_byte : forall ps n c v,
  pv_ok ps n v -> pv_mode v <> PMNormal -> pv_ok ps (S n) (pbyte n c v).
Proof.
  intros ps n c v Ok Em. pose proof Ok as (D & Bd & Be & B & So & Bt & _).
  assert (Keep : pv_mode v <> PMNormal -> pv_ok ps (S n) v).
  { intros E. unfold pv_ok. split; [exact D|]. split; [intros y H; specialize (Bd y H); lia|].
    split; [intros p k c' H; specialize (Be p k c' H); lia|].
    split; [exact B|]. split; [exact So|]. split; [exact Bt|].
    destruct (pv_mode v); [contradiction| |]; destruct (pv_stk v) as [|[] ?]; exact Logic.I. }
  unfold pbyte. destruct (pv_mode v) as [|b kids d e txt|x e] eqn:Ev; [contradiction| |].
  - destruct (match e with Some e' => Nat.eqb n e' | None => false end).
    + apply (pv_ok_add ps n); [exact D|exact Bd|exact Be|exact B|exact So|exact Bt|lia].
    + split; [exact D|]. split; [intros y H; specialize (Bd y H); lia|].
      split; [intros p k c' H; specialize (Be p k c' H); lia|].
      split; [exact B|]. split; [exact So|]. split; [exact Bt|exact Logic.I].
  - destruct (Nat.eqb n e).
    + apply (pv_ok_add ps n); [exact D|exact Bd|exact Be|exact B|exact So|exact Bt|lia].
    + apply Keep. discriminate.
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
  Ascii.eqb c lbrack = false -> Ascii.eqb c rbrack = false -> is_tick c = false ->
  Ascii.eqb c dollar = false -> dstyle_of c = None -> no_note c txt prev = true ->
  ilead c txt prev o = IText false (txt ++ one c) (Some c) o.
Proof.
  intros c txt prev o Ha Hlb Hlk Hrk Htk Hdl Hd Hn.
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
    rewrite Hd. change (Ascii.eqb rbrace percent) with false.
    rewrite andb_false_r. reflexivity. }
  unfold in_alphabet in Ha. rewrite Hd in Ha.
  apply andb_true_iff in Ha as [Ha _]. apply andb_true_iff in Ha as [Ha Hhy].
  apply andb_true_iff in Ha as [_ Hres]. rewrite Hlb, Erb, Hlk, Hrk, Htk, Hdl in Hres.
  cbn [orb] in Hres. apply andb_true_iff in Hres as [Hres Hpct].
  apply negb_true_iff in Hres, Hhy, Hpct.
  pose proof (dreserved_false c Hres)
    as (Hbs & _ & _ & _ & _ & _ & Hbg & Hdol & Hpd & Hlt).
  assert (Hcolon : Ascii.eqb c ":"%char = false).
  { unfold dreserved in Hres.
    repeat (apply orb_false_iff in Hres as [Hres ?]). assumption. }
  unfold ilead.
  rewrite Hbs, Htk, Hdol, Hpd, Hhy, Hlb, Hbg, Hlt, Hcolon, Hlk, Hrk, Hn.
  cbn [andb]. rewrite Hd, Hpct. reflexivity.
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
Local Lemma close_empty : forall ps n v above p k c rest content rest',
  pv_ok ps n v -> pv_mode v = PMNormal ->
  pv_stk v = (above ++ PF p k c :: rest)%list ->
  Forall (passes k) above ->
  pclose_go k [] (pv_stk v) = Some (content, rest') ->
  (content = [] <-> tok_end ps p = n).
Proof.
  intros ps n v above p k c rest content rest' (D & Bd & Be & _ & So & Bt & Inn) Em E F H.
  unfold pv_live in D, Bd. rewrite E in D, Bd, Be, H, Inn, So, Bt. rewrite Em in Inn.
  destruct above as [|g above'].
  - cbn [app pclose_go] in H. rewrite key_eq_refl in H. injection H as <- _. exact Inn.
  - apply Forall_cons_iff in F as [Fk F].
    destruct g as [q k1 c1|d c1]; [|destruct Fk]. cbn [passes] in Fk.
    cbn [app pclose_go] in H. rewrite Fk in H.
    apply pclose_grows in H; [|apply xapp_nonempty_r; discriminate].
    assert (Hq : tok_end ps q <= n) by (apply (Be q k1 c1); left; reflexivity).
    (* the opener below ends where the one above at the latest starts *)
    assert (Hpq : tok_end ps p <= q).
    { apply StronglySorted_inv in So as [_ G]. rewrite Forall_forall in G.
      apply (G (PF p k c)). apply in_or_app. right. left. reflexivity. }
    assert (Hqe : q < tok_end ps q) by (apply (Bt q k1 c1); left; reflexivity).
    split; [intros; contradiction|lia].
Qed.

(* A completed token, bare or with `}` after it (`mr`), resolved. *)
Local Lemma resolve_sim : forall ps n h k mr txt prev next v o,
  self_row k = true -> pv_ok ps n v -> pv_mode v = PMNormal -> sim v txt o ->
  exists txt' o',
    idelim_resolve k txt prev mr next o
    = IText false txt' (Some (if mr then rbrace else dchar k)) o'
    /\ sim (pstep ps n h (TDelim k mr (negb mr && bare_opens k && nonspace_at next)
                          (mr || nonspace_at prev)) v) txt' o'.
Proof.
  intros ps n h k mr txt prev next v o Hb Ok Em (v0 & cm & -> & Ht & ->).
  pose proof Ok as (_ & Bd & Be & B & _).
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
       unfold pstep. cbn. fold K. exact Done. }
  assert (Et : tok_text t
               = tok_text (TDelim k mr (negb mr && bare_opens k && nonspace_at next)
                             true))
    by (destruct mr; reflexivity).
  rewrite Et in Done. unfold t. rewrite orb_comm, Hc. unfold pstep.
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
  pose proof (close_empty ps n v above p K c rest content rest Ok Em E F Hc')
    as Hce.
  assert (Hpn : p < n).
  { apply (Bd (LOpen p K)). unfold pv_live. rewrite E, map_app.
    apply in_or_app. right. left. reflexivity. }
  assert (Hpe : tok_end ps p <= n).
  { apply (Be p K c). rewrite E. apply in_or_app. right. left. reflexivity. }
  destruct (Nat.ltb (tok_end ps p) n) eqn:L.
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
destination.  A byte passes through each of them, counting parens and
decoding escapes, as long as it is not the `)` that would end one.

What a destination keeps besides the reading inside it is a small
machine of its own (`dstep`): a pending backslash, the paren depth and
the text so far. *)

Record dstate : Type := DS { ds_esc : bool; ds_depth : nat; ds_dst : string }.

(* The paren depth after a byte, or `None` if the byte ends the
   destination. *)
Definition pstep_byte (c : ascii) (depth : nat) : option nat :=
  if Ascii.eqb c lparen then Some (S depth)
  else if Ascii.eqb c rparen then match depth with O => None | S d => Some d end
  else Some depth.

(* One byte, as `IDest` reads it: an escaped byte is decoded and counts
   no paren. *)
Definition dstep (c : ascii) (s : dstate) : option dstate :=
  if ds_esc s then Some (DS false (ds_depth s) (ds_dst s ++ esc_text c))
  else if is_bslash c then Some (DS true (ds_depth s) (ds_dst s))
  else match pstep_byte c (ds_depth s) with
       | Some d => Some (DS false d (ds_dst s ++ one c))
       | None => None
       end.

Fixpoint dfeed (s : string) (st : dstate) : option dstate :=
  match s with
  | EmptyString => Some st
  | String c rest => match dstep c st with Some st' => dfeed rest st' | None => None end
  end.

Local Lemma dfeed_app : forall a b st,
  dfeed (a ++ b) st = match dfeed a st with Some st' => dfeed b st' | None => None end.
Proof.
  induction a as [|c a IH]; intros b st; [reflexivity|].
  cbn [append dfeed]. destruct (dstep c st); [apply IH|reflexivity].
Qed.

Record wlayer : Type := WL {
  wl_kids : inlines; wl_open : span; wl_ds : dstate; wl_o : ostate
}.

Definition wl_depth (w : wlayer) : nat := ds_depth (wl_ds w).

Fixpoint wrap (ws : list wlayer) (core : iscan) : iscan :=
  match ws with
  | [] => core
  | w :: rest =>
      IDest (wl_kids w) false (wl_open w) (ds_esc (wl_ds w)) (ds_depth (wl_ds w))
        (ds_dst (wl_ds w)) (wrap rest core) (wl_o w)
  end.

Definition wl_after (s : string) (w : wlayer) : wlayer :=
  WL (wl_kids w) (wl_open w)
     (match dfeed s (wl_ds w) with Some d => d | None => wl_ds w end) (wl_o w).

Fixpoint no_bslash (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c rest => negb (is_bslash c) && no_bslash rest
  end.

Local Lemma istep_idest : forall c kids op e depth dst sh o d,
  dstep c (DS e depth dst) = Some d ->
  istep c (IDest kids false op e depth dst sh o)
  = IDest kids false op (ds_esc d) (ds_depth d) (ds_dst d) (istep c sh) o.
Proof.
  intros c kids op e depth dst sh o d H. unfold dstep in H. cbn [ds_esc ds_depth ds_dst] in H.
  unfold istep. destruct e; cbn [istep_at].
  - injection H as <-. reflexivity.
  - destruct (is_bslash c) eqn:Hb; [injection H as <-; reflexivity|].
    unfold pstep_byte in H.
    destruct (Ascii.eqb c lparen) eqn:El.
    + injection H as <-. apply Ascii.eqb_eq in El. subst c. reflexivity.
    + destruct (Ascii.eqb c rparen) eqn:Er.
      * apply Ascii.eqb_eq in Er. subst c.
        destruct depth as [|dp]; [discriminate|injection H as <-]. reflexivity.
      * injection H as <-. reflexivity.
Qed.

Definition wl_step (c : ascii) (w : wlayer) : wlayer :=
  WL (wl_kids w) (wl_open w)
     (match dstep c (wl_ds w) with Some d => d | None => wl_ds w end) (wl_o w).

Local Lemma istep_wrap : forall c ws core,
  Forall (fun w => dstep c (wl_ds w) <> None) ws ->
  istep c (wrap ws core) = wrap (map (wl_step c) ws) (istep c core).
Proof.
  intros c ws core. induction ws as [|w ws IHw]; intros G; [reflexivity|].
  apply Forall_cons_iff in G as [Gw G]. cbn [wrap map].
  destruct (dstep c (wl_ds w)) as [d|] eqn:Hd; [|contradiction].
  destruct w as [k o [e dp dst] o']. cbn [wl_ds wl_kids wl_open wl_o] in *.
  rewrite (istep_idest c _ _ _ _ _ _ _ d Hd), IHw by exact G.
  unfold wl_step. cbn [wl_ds wl_kids wl_open wl_o]. rewrite Hd. reflexivity.
Qed.

Local Lemma iscan_wrap : forall s ws core,
  Forall (fun w => dfeed s (wl_ds w) <> None) ws ->
  iscan_str s (wrap ws core) = wrap (map (wl_after s) ws) (iscan_str s core).
Proof.
  induction s as [|c s IH]; intros ws core F.
  - cbn [iscan_str]. f_equal. rewrite <- (map_id ws) at 1. apply map_ext.
    intros [k o d o']. reflexivity.
  - cbn [iscan_str].
    assert (Step : forall ws', Forall (fun w => dstep c (wl_ds w) <> None) ws' ->
              istep c (wrap ws' core)
              = wrap (map (fun w => WL (wl_kids w) (wl_open w)
                                      (match dstep c (wl_ds w) with Some d => d | None => wl_ds w end)
                                      (wl_o w)) ws') (istep c core)).
    { induction ws' as [|w ws' IHw]; intros G; [reflexivity|].
      apply Forall_cons_iff in G as [Gw G]. cbn [wrap map].
      destruct (dstep c (wl_ds w)) as [d|] eqn:Hd; [|contradiction].
      destruct w as [k o [e dp dst] o']. cbn [wl_ds wl_kids wl_open wl_o] in *.
      rewrite (istep_idest c _ _ _ _ _ _ _ d Hd), IHw by exact G. reflexivity. }
    rewrite Step.
    2: { rewrite Forall_forall in F |- *. intros w Hw E. apply (F w Hw).
         cbn [dfeed]. rewrite E. reflexivity. }
    rewrite IH.
    + f_equal. rewrite map_map. apply map_ext_in. intros [k o d o'] Hw.
      rewrite Forall_forall in F. specialize (F _ Hw). cbn [wl_ds dfeed] in F.
      unfold wl_after. cbn [wl_ds wl_kids wl_open wl_o dfeed].
      destruct (dstep c d) as [d0|]; [|contradiction].
      destruct (dfeed s d0); [reflexivity|contradiction].
    + rewrite Forall_map. rewrite Forall_forall in F |- *. intros w Hw E.
      apply (F w Hw). cbn [dfeed wl_ds] in *.
      destruct (dstep c (wl_ds w)); [exact E|reflexivity].
Qed.

(* A state resolved as at the end of a line, through the destination
   readings.  A pending `$` is kept while dollar math is on: a break may
   open display math from it, which its resolved text cannot. *)
Fixpoint rres (st : iscan) : iscan :=
  match st with
  | IDest k i o e d dst sh o' => IDest k i o e d dst (rres sh) o'
  | IDollar _ _ _ _ => if dollar_math_enabled then st else iresolve st
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

Local Lemma no_bslash_app : forall a b, no_bslash (a ++ b) = (no_bslash a && no_bslash b)%bool.
Proof.
  induction a as [|c a IH]; intros b; [reflexivity|]. cbn. rewrite IH. apply andb_assoc.
Qed.

Local Lemma step_through : forall bytes rest ws core X st,
  Forall (fun w => dfeed (bytes ++ rest) (wl_ds w) <> None) ws ->
  iscan_str bytes core = X -> settles X st (get 0 rest) ->
  rres (iscan_str (bytes ++ rest) (wrap ws core))
  = rres (iscan_str rest (wrap (map (wl_after bytes) ws) st)).
Proof.
  intros bytes rest ws core X st F HX Hs.
  rewrite iscan_str_app, iscan_wrap, HX.
  2: { rewrite Forall_forall in F |- *. intros w Hw E. apply (F w Hw).
       rewrite dfeed_app, E. reflexivity. }
  destruct rest as [|c r].
  - cbn [iscan_str]. rewrite !rres_wrap. cbn [get settles] in Hs. rewrite Hs. reflexivity.
  - cbn [iscan_str]. cbn [get settles] in Hs.
    assert (Fc : Forall (fun w => dstep c (wl_ds w) <> None) (map (wl_after bytes) ws)).
    { rewrite Forall_map. rewrite Forall_forall in F |- *. intros w Hw E. apply (F w Hw).
      rewrite dfeed_app. unfold wl_after in E. cbn [wl_ds] in E.
      destruct (dfeed bytes (wl_ds w)) as [d'|]; [|reflexivity].
      cbn [dfeed]. rewrite E. reflexivity. }
    rewrite !(istep_wrap c _ _ Fc), Hs. reflexivity.
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
(* A `]` that closes no named bracket waits for the next byte. *)
Local Lemma ilead_rbrack_closed : forall txt prev o,
  tag_close (flush_text txt o) = None -> ilead rbrack txt prev o = IClosed txt o.
Proof.
  intros txt prev o Ht. unfold ilead. cbn [is_bslash is_tick Ascii.eqb Ascii.ascii_dec].
  change (@flush_text_at semantic_pos semantic_inline_cursor (@tval string _ txt) o)
    with (flush_text txt o).
  rewrite Ht. destruct tags_enabled; reflexivity.
Qed.

Local Lemma tok_rbrack_text : forall txt prev o next,
  tag_close (flush_text txt o) = None ->
  (forall c, next = Some c ->
     (Ascii.eqb c lparen || Ascii.eqb c lbrack || (Ascii.eqb c lbrace && inline_attrs_enabled))%bool
     = true -> bclose (flush_text txt o) = None) ->
  settles (iscan_str (one rbrack) (IText false txt prev o))
          (IText false (txt ++ one rbrack) (Some rbrack) o) next.
Proof.
  intros txt prev o next Ht H. cbn [iscan_str one]. unfold istep at 1. cbn [istep_at].
  rewrite (ilead_rbrack_closed txt prev o Ht).
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
A line inside the paragraph
---------------------------

A token of a line is read the same from the line alone: nothing of the
newline after it, nor of the newline before it, changes it.
*)

Definition line_end (after : string) : Prop :=
  after = EmptyString \/ exists r, after = String nl_char r.

Local Lemma dstyle_of_nl : dstyle_of nl_char = None.
Proof.
  destruct (dstyle_of nl_char) as [k|] eqn:E; [|reflexivity].
  pose proof (dstyle_of_char _ k E) as H. pose proof (dchar_punct k) as P.
  rewrite H in P. discriminate P.
Qed.

Local Lemma no_char_app : forall c a b,
  no_char c (a ++ b) = (no_char c a && no_char c b)%bool.
Proof. intros c a. induction a as [|x a IH]; intros b; [reflexivity|]. cbn. rewrite IH. apply andb_assoc. Qed.

Local Lemma line_rest_app : forall r after,
  no_char nl_char r = true -> line_end after -> line_rest (r ++ after) = r.
Proof.
  induction r as [|x r IH]; intros after H He.
  - destruct He as [->|[r' ->]]; reflexivity.
  - cbn [no_char] in H. apply andb_true_iff in H as [Hx H]. apply negb_true_iff in Hx.
    cbn [append line_rest]. rewrite Hx. rewrite IH by assumption. reflexivity.
Qed.

Local Lemma line_rest_line : forall r, no_char nl_char r = true -> line_rest r = r.
Proof.
  intros r H. rewrite <- (append_empty_r r) at 1. apply line_rest_app; [exact H|left; reflexivity].
Qed.

Local Lemma ws_run_app : forall r a, is_blank r = false -> ws_run (r ++ a) = ws_run r.
Proof.
  induction r as [|x r IH]; intros a H; [discriminate|]. cbn [is_blank] in H.
  cbn [append ws_run]. destruct (is_ws x); [|reflexivity]. cbn in H. rewrite IH by exact H.
  reflexivity.
Qed.

Local Lemma prefix_chars_app : forall c n r a,
  c <> nl_char -> line_end a -> prefix (chars c n) (r ++ a) = prefix (chars c n) r.
Proof.
  intros c n. induction n as [|n IH]; intros r a Hc Ha.
  - cbn [chars]. destruct (r ++ a)%string, r; reflexivity.
  - destruct r as [|x r].
    + destruct Ha as [->|[r' ->]]; [reflexivity|]. cbn [chars append prefix].
      destruct (ascii_dec c nl_char); [contradiction|reflexivity].
    + cbn [chars append prefix]. destruct (ascii_dec c x); [apply IH; assumption|reflexivity].
Qed.

Local Lemma get_app_end : forall s a i,
  i <= String.length s -> line_end a ->
  at_rbrace (get i (s ++ a)) = at_rbrace (get i s)
  /\ nonspace_at (get i (s ++ a)) = nonspace_at (get i s).
Proof.
  induction s as [|x s IH]; intros a i Hi Ha.
  - assert (i = 0) as -> by (cbn in Hi; lia).
    destruct Ha as [->|[r ->]]; split; reflexivity.
  - destruct i as [|i]; [split; reflexivity|]. cbn [append get]. apply IH; [cbn in Hi; lia|exact Ha].
Qed.

Local Lemma dchar_not_nl : forall k, dchar k <> nl_char.
Proof. intros k E. pose proof (dchar_punct k) as P. rewrite E in P. discriminate P. Qed.

Local Lemma next_tok_prev : forall p1 p2 s,
  nonspace_at p1 = nonspace_at p2 -> next_tok p1 s = next_tok p2 s.
Proof. intros p1 p2 [|c r] H; [reflexivity|]. unfold next_tok. rewrite H. reflexivity. Qed.

Local Lemma next_tok_after : forall prev s after,
  no_char nl_char s = true -> line_end after -> s <> EmptyString -> starts_tick s = false ->
  starts_with dollar s = false ->
  next_tok prev (s ++ after) = next_tok prev s.
Proof.
  intros prev s after Hn Ha Hne Htk Hdl. destruct s as [|c rest]; [contradiction|].
  cbn [starts_tick starts_with] in Htk, Hdl.
  cbn [no_char] in Hn. apply andb_true_iff in Hn as [Hc Hn]. apply negb_true_iff in Hc.
  assert (SW : forall x, x <> nl_char -> starts_with x (rest ++ after) = starts_with x rest).
  { intros x Hx. destruct rest as [|y r]; [|reflexivity].
    destruct Ha as [->|[r ->]]; [reflexivity|]. cbn [append starts_with].
    apply Ascii.eqb_neq. intros E. apply Hx. symmetry. exact E. }
  assert (Pf : forall k s', prefix (dtoken k) (s' ++ after) = prefix (dtoken k) s')
    by (intros k s'; unfold dtoken; apply prefix_chars_app; [apply dchar_not_nl|exact Ha]).
  cbn [append]. unfold next_tok. f_equal.
  rewrite (line_rest_app rest after Hn Ha).
  destruct (Ascii.eqb c nl_char); [reflexivity|].
  destruct (is_bslash c).
  { rewrite (line_rest_line rest Hn).
    destruct (is_blank rest) eqn:B; [reflexivity|].
    destruct rest as [|d r]; [discriminate|]. cbn [append].
    destruct (is_ws d); [|reflexivity].
    change (String d (r ++ after)) with (String d r ++ after)%string.
    rewrite (ws_run_app (String d r) after B). reflexivity. }
  rewrite Htk, Hdl.
  destruct (Ascii.eqb c lbrack); [reflexivity|].
  destruct (Ascii.eqb c rbrack).
  { rewrite !SW by (intros E; discriminate E). reflexivity. }
  destruct (Ascii.eqb c lbrace).
  { destruct rest as [|d r].
    - destruct Ha as [->|[r ->]]; [reflexivity|]. cbn [append]. rewrite dstyle_of_nl. reflexivity.
    - cbn [append]. destruct (dstyle_of d) as [k|]; [|reflexivity].
      change (String d (r ++ after)) with (String d r ++ after)%string. rewrite Pf. reflexivity. }
  destruct (dstyle_of c) as [k|]; [|reflexivity].
  change (String c (rest ++ after)) with (String c rest ++ after)%string. rewrite Pf.
  destruct (prefix (dtoken k) (String c rest)) eqn:P; [|reflexivity].
  apply prefix_length in P. unfold dtoken in P. rewrite length_chars in P.
  destruct (get_app_end (String c rest) after (dwidth k) P Ha) as [E1 E2].
  rewrite E1, E2. reflexivity.
Qed.

(*
Bytes, escapes and brackets
---------------------------
*)

(* A backslash and whitespace the line ended after, which the scanner
   holds until the line's end. *)
Definition esc_pending (ws0 txt : string) (p : option ascii) (o : ostate) : iscan :=
  match ws0 with
  | EmptyString => IText true txt p o
  | _ => IEscWs ws0 txt p o
  end.

Local Lemma prefix_sdrop : forall a s,
  prefix a s = true -> s = a ++ sdrop (String.length a) s.
Proof.
  induction a as [|x a IH]; intros s H; [reflexivity|].
  destruct s as [|y s]; [discriminate|]. cbn [prefix] in H.
  destruct (ascii_dec x y) as [->|]; [|discriminate].
  cbn. rewrite <- (IH s H). reflexivity.
Qed.

Local Lemma ws_run_sdrop : forall s, (ws_run s ++ sdrop (String.length (ws_run s)) s)%string = s.
Proof.
  induction s as [|c s IH]; [reflexivity|]. cbn [ws_run].
  destruct (is_ws c); [|reflexivity]. cbn [String.length sdrop append]. rewrite IH. reflexivity.
Qed.

Local Lemma ws_run_blank : forall s, is_blank (ws_run s) = true.
Proof.
  induction s as [|c s IH]; [reflexivity|]. cbn [ws_run].
  destruct (is_ws c) eqn:E; [|reflexivity]. cbn [is_blank]. rewrite E. exact IH.
Qed.

Local Lemma over_alphabet_cons : forall c s,
  is_bslash c = false -> over_alphabet (String c s) = true ->
  in_alphabet c = true /\ follow_ok c s = true /\ over_alphabet s = true.
Proof.
  intros c s Hb H. cbn [over_alphabet] in H. rewrite Hb in H.
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2]. auto.
Qed.

Local Lemma delim_not_bslash : forall d k, dstyle_of d = Some k -> is_bslash d = false.
Proof.
  intros d k Hd. pose proof (dstyle_of_char d k Hd) as E. subst d.
  exact (proj1 (dreserved_false _ (dchar_free k))).
Qed.

(* Past a run of whitespace, a string of the alphabet still is one. *)
Local Lemma over_alphabet_ws_run : forall s,
  over_alphabet s = true -> over_alphabet (sdrop (String.length (ws_run s)) s) = true.
Proof.
  induction s as [|c s IH]; intros H; [exact H|]. cbn [ws_run].
  destruct (is_ws c) eqn:Ew; [|exact H].
  assert (Hb : is_bslash c = false)
    by (destruct c as [[] [] [] [] [] [] [] []]; try discriminate Ew; reflexivity).
  apply (over_alphabet_cons c s Hb) in H as (_ & _ & H). exact (IH H).
Qed.

Local Lemma over_alphabet_chars : forall c n r,
  is_bslash c = false -> over_alphabet (chars c n ++ r) = true -> over_alphabet r = true.
Proof.
  intros c n r Hb. induction n as [|n IHn]; intros H; [exact H|].
  cbn [chars append] in H. apply (over_alphabet_cons c _ Hb) in H as (_ & _ & H). exact (IHn H).
Qed.

Local Lemma blank_byte : forall c, is_ws c = true ->
  is_bslash c = false /\ Ascii.eqb c lparen = false /\ Ascii.eqb c rparen = false
  /\ is_punct c = false.
Proof. intros c. destruct c as [[] [] [] [] [] [] [] []]; intros H; try discriminate H; auto. Qed.

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
  induction st; try reflexivity; try (cbn [rres]; destruct dollar_math_enabled; reflexivity).
  - destruct (iresolve_shape (IDelim k extra txt before marked o)) as [(t & p & o' & E)|E];
      cbn [rres ifinish_ostate]; rewrite !E; cbn [ifinish_ostate]; rewrite ?E; reflexivity.
  - cbn [rres ifinish_ostate]. exact IHst.
Qed.

Local Lemma ifinish_rres : forall st : iscan, ifinish (rres st) = ifinish st.
Proof. intros st. unfold ifinish, ifinish_rev. rewrite ifinish_ostate_rres. reflexivity. Qed.

Local Lemma ibreak_rres : forall a (st : iscan), ibreak_at a (rres st) = ibreak_at a st.
Proof.
  intros a st. revert a. induction st; intros a; try reflexivity;
    try (cbn [rres]; destruct dollar_math_enabled eqn:Edm; [reflexivity|];
         cbn [ibreak_at iresolve]; rewrite Edm, !andb_false_r; reflexivity).
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
  cbn [wrap map ibreak_at]. rewrite IH. destruct w as [k o [e dp dst] o'].
  unfold wl_after. destruct e; reflexivity.
Qed.

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
  ifinish (IReference (map mk kids) false open false label (oview cm v))
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
  rewrite Eb. cbn [tval tpush]. rewrite append_empty_r, append_assoc. reflexivity.
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

Local Lemma dchar_nb : forall k, is_bslash (dchar k) = false.
Proof. intros k. exact (proj1 (dreserved_false _ (dchar_free k))). Qed.

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
  is_tick p = false -> follow_ok p s = true.
Proof. intros p s H1 H2 H3 H4. unfold follow_ok. rewrite H1, H2, H3, H4. reflexivity. Qed.

Local Lemma over_alphabet_app_r : forall a b,
  no_bslash a = true -> over_alphabet (a ++ b) = true -> over_alphabet b = true.
Proof.
  induction a as [|c a IH]; intros b Hb H; [exact H|].
  cbn [no_bslash] in Hb. apply andb_true_iff in Hb as [Hc Hb]. apply negb_true_iff in Hc.
  apply (over_alphabet_cons c _ Hc) in H as (_ & _ & H). exact (IH b Hb H).
Qed.

Local Lemma chars_add : forall c a b,
  chars c (a + b) = (chars c a ++ chars c b)%string.
Proof.
  intros c a b. induction a as [|a IH]; [reflexivity|]. cbn. rewrite IH.
  reflexivity.
Qed.

Local Lemma no_bslash_chars : forall c n, is_bslash c = false -> no_bslash (chars c n) = true.
Proof. intros c n H. induction n as [|n IH]; [reflexivity|]. cbn [chars no_bslash]. rewrite H, IH. reflexivity. Qed.

Local Lemma no_bslash_dtoken : forall k, no_bslash (dtoken k) = true.
Proof. intros k. apply no_bslash_chars, dchar_nb. Qed.

Local Lemma esc_text_ne : forall d, esc_text d <> EmptyString.
Proof. intros d. unfold esc_text. destruct (is_punct d); discriminate. Qed.

Local Lemma istep_bslash_text : forall txt p o,
  istep bslash (IText false txt p o) = IText true txt (Some bslash) o.
Proof. intros txt p o. reflexivity. Qed.

Local Lemma istep_esc_byte : forall d txt p o, is_ws d = false ->
  istep d (IText true txt p o) = IText false (txt ++ esc_text d) (Some d) o.
Proof.
  intros d txt p o Hw. unfold istep. cbn [istep_at]. rewrite Hw. tred.
  unfold esc_text. destruct (is_punct d); reflexivity.
Qed.

Local Lemma iescws_cons : forall d w1 txt p o,
  iescws_resolve (String d w1) txt p o
  = if Ascii.eqb d " "%char
    then (w1, str_last w1 (Some d), oemit (mk NonBreakingSpace) (flush_text txt o))
    else ((txt ++ String bslash (String d w1))%string, str_last w1 (Some d), o).
Proof. reflexivity. Qed.

Local Lemma iscan_escws_acc : forall ws acc txt p o, is_blank ws = true ->
  iscan_str ws (IEscWs acc txt p o) = IEscWs (acc ++ ws) txt p o.
Proof.
  induction ws as [|c ws IH]; intros acc txt p o H; [cbn; rewrite append_empty_r; reflexivity|].
  cbn [is_blank] in H. apply andb_true_iff in H as [Hc H]. cbn [iscan_str].
  unfold istep. cbn [istep_at]. rewrite Hc. tred. rewrite IH by exact H.
  rewrite append_assoc. reflexivity.
Qed.

Local Lemma iscan_bs_blank : forall w txt p o, is_blank w = true ->
  iscan_str (String bslash w) (IText false txt p o) = esc_pending w txt (Some bslash) o.
Proof.
  intros [|c w] txt p o H; [reflexivity|]. cbn [is_blank] in H. apply andb_true_iff in H as [Hc H].
  cbn [iscan_str]. rewrite istep_bslash_text. unfold istep. cbn [istep_at]. rewrite Hc. tred.
  rewrite iscan_escws_acc by exact H. reflexivity.
Qed.

Local Lemma ws_follow : forall x s, is_ws x = true -> follow_ok x s = true.
Proof. intros x s H. destruct x as [[] [] [] [] [] [] [] []]; try discriminate H; reflexivity. Qed.

Local Lemma str_last_blank : forall w c, is_blank (String c w) = true ->
  exists x, str_last w (Some c) = Some x /\ is_ws x = true.
Proof.
  induction w as [|c' w IH]; intros c H; cbn [is_blank] in H; apply andb_true_iff in H as [Hc H].
  - exists c. split; [reflexivity|exact Hc].
  - exact (IH c' H).
Qed.

Local Lemma ws_run_next : forall s c, get 0 (sdrop (String.length (ws_run s)) s) = Some c ->
  is_ws c = false.
Proof.
  induction s as [|d s IH]; intros c H; [discriminate|]. cbn [ws_run] in H.
  destruct (is_ws d) eqn:E.
  - cbn [String.length sdrop] in H. exact (IH c H).
  - cbn in H. injection H as <-. exact E.
Qed.

Local Lemma no_nl_drop : forall s, no_nl s = drop_nl s.
Proof. induction s as [|c s IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

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
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [_ H].
  rewrite E in H. destruct Hc as [-> | ->]; discriminate H.
Qed.

(* The same from `note_ok`, in text mode. *)
(* A `[` with nothing yet read after it would make a `^` a footnote's: the
   byte before the line, or the text the scanner holds, rules that out. *)
Definition note_ok (prev : option ascii) (core : iscan) (s : string) : Prop :=
  prev_ok prev s = true
  \/ (forall txt p o, core = IText false txt p o -> nonempty_str txt = true).

Local Lemma note_free' : forall prev c s' txt p o,
  note_ok prev (IText false txt p o) (String c s') -> c = lbrack \/ c = hat ->
  note_pos txt prev = false.
Proof.
  intros prev c s' txt p o [H|H] Hc; [exact (note_free prev c s' txt H Hc)|].
  unfold note_pos. tred. rewrite (H txt p o eq_refl). reflexivity.
Qed.

Local Lemma no_note_ok' : forall prev c s' txt p o,
  note_ok prev (IText false txt p o) (String c s') -> no_note c txt prev = true.
Proof.
  intros prev c s' txt p o H. unfold no_note.
  destruct (Ascii.eqb c hat) eqn:E; [|reflexivity].
  apply Ascii.eqb_eq in E. subst c.
  rewrite (note_free' prev hat s' txt p o H (or_intror eq_refl)). reflexivity.
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

(*
Tidy contents
-------------

Every content of the view, the outermost too, is normal and clean, and
a token the view is inside adds no text.
*)

Definition tidy (v : pview) : Prop :=
  normal (pv_out v) /\ clean (pv_out v) /\ frames_normal v /\ frames_clean v /\ atom_ok v.

Local Lemma pv_add_out : forall x v,
  pv_out (pv_add x v) = pv_out v \/ pv_out (pv_add x v) = xsnoc x (pv_out v).
Proof. intros x [[|f rest] out md]; [right|left]; reflexivity. Qed.

Local Lemma pv_trim_out : forall v,
  pv_out (pv_trim v) = pv_out v \/ pv_out (pv_trim v) = xtrim (pv_out v).
Proof. intros [[|f rest] out md]; [right|left]; reflexivity. Qed.

(* The outermost content stays normal and clean. *)
Local Lemma pstep_out : forall ps n h t v,
  t <> TDollars 0 -> normal (pv_out v) -> clean (pv_out v) ->
  normal (pv_out (pstep ps n h t v)) /\ clean (pv_out (pstep ps n h t v)).
Proof.
  intros ps n h t v H0 N0 C0.
  assert (Add : forall x v', x <> Str "" -> normal (pv_out v') -> clean (pv_out v') ->
            normal (pv_out (pv_add x v')) /\ clean (pv_out (pv_add x v'))).
  { intros x v' Hx N C. destruct (pv_add_out x v') as [H|H]; rewrite H;
      [split; assumption|split; [apply normal_xsnoc, N|apply clean_xsnoc; assumption]]. }
  assert (Txt : forall t', (forall d m b c r, t' <> TVerb d m b c r) -> t' <> TDollars 0 ->
                 Str (tok_text t') <> Str "")
    by (intros t' Hv Hd E; injection E as E; exact (tok_text_ne t' Hv Hd E)).
  assert (Open : forall i k op t', (forall d m b c r, t' <> TVerb d m b c r) -> t' <> TDollars 0 ->
            normal (pv_out (popen i k op (tok_text t') v)) /\ clean (pv_out (popen i k op (tok_text t') v))).
  { intros i k [|] t' Hv Hd; [split; assumption|apply Add; [apply Txt; [exact Hv|exact Hd]|exact N0|exact C0]]. }
  unfold pstep.
  destruct t as [c| |k mr op cl| |b|c|ws|ws|vp vn vb vc vr|dk].
  - apply Add; [discriminate|exact N0|exact C0].
  - destruct h; [split; assumption|apply Add; [discriminate|exact N0|exact C0]].
  - destruct (if cl then pick (KDelim k mr) (pv_live v) else PNone) as [p below| |];
      [|apply Add; [apply Txt; discriminate|exact N0|exact C0]|apply Open; discriminate].
    destruct (Nat.ltb (tok_end ps p) n); [|apply Open; discriminate].
    destruct (pclose_go (KDelim k mr) [] (pv_stk v)) as [[content rest]|]; [|split; assumption].
    apply Add; [apply dnode_nonstr|exact N0|exact C0].
  - apply Open; discriminate.
  - destruct (pick KBracket (pv_live v));
      destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|];
      try (apply Add; [apply Txt; discriminate|exact N0|exact C0]).
    destruct (region_end ps n b); [split; assumption|]. destruct b; split; assumption.
  - apply Add; [|exact N0|exact C0]. intros E. injection E as E.
    unfold esc_text in E. destruct (is_punct c); discriminate.
  - destruct (nbsp_rest ws) as [r|]; [|apply Add; [apply (Txt (TEscWs ws)); discriminate|exact N0|exact C0]].
    destruct (Add NonBreakingSpace v ltac:(discriminate) N0 C0) as [N1 C1].
    destruct (nonempty_str r) eqn:Er; [|split; assumption].
    apply Add; [|exact N1|exact C1]. intros E. injection E as ->. discriminate Er.
  - assert (Tr : normal (pv_out (pv_trim v)) /\ clean (pv_out (pv_trim v))).
    { destruct (pv_trim_out v) as [H|H]; rewrite H;
        [split; assumption|split; [apply normal_xtrim, N0|apply clean_xtrim, C0]]. }
    apply Add; [discriminate|exact (proj1 Tr)|exact (proj2 Tr)].
  - assert (A1 : normal (pv_out (add_text (chars dollar (vp - 2)) v))
                 /\ clean (pv_out (add_text (chars dollar (vp - 2)) v))).
    { unfold add_text. destruct (nonempty_str _) eqn:Ene; [|split; assumption].
      apply Add; [|exact N0|exact C0]. intros E. injection E as E. rewrite E in Ene. discriminate. }
    destruct (Nat.ltb _ _); [exact A1|].
    apply Add; [apply verb_node_nonstr|exact (proj1 A1)|exact (proj2 A1)].
  - apply Add; [apply Txt; [discriminate|exact H0]|exact N0|exact C0].
Qed.

Local Lemma pstep_atom : forall ps n h t v,
  pv_mode v = PMNormal -> atom_ok (pstep ps n h t v).
Proof.
  intros ps n h t v Em. unfold atom_ok.
  destruct t as [c| |k mr op cl| |b|c|ws|ws|vp vn vb vc vr|dk];
    try (rewrite pstep_mode by (assumption || discriminate); exact Logic.I).
  - destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|] eqn:Hc.
    + rewrite (pstep_close_found ps n h b v content rest Hc).
      destruct (region_end ps n b), b; exact Logic.I.
    + rewrite pstep_close_none by exact Hc. rewrite (proj2 (pv_add_live _ _)), Em. exact Logic.I.
  - unfold pstep. destruct (Nat.ltb _ _); cbn [pv_mode pv_setmode];
      [intros s E; exact (verb_node_nonstr _ _ _ _ E)
      |rewrite (proj2 (pv_add_live _ _)), (proj2 (add_text_live _ _)), Em; exact Logic.I].
Qed.

Local Lemma pstep_tidy : forall ps n h t v,
  t <> TDollars 0 -> pv_mode v = PMNormal -> tidy v -> tidy (pstep ps n h t v).
Proof.
  intros ps n h t v H0 Em (Hn & Hc & Fn & Fc & _).
  destruct (pstep_out ps n h t v H0 Hn Hc) as [N C].
  split; [exact N|split; [exact C|split; [apply pstep_normal, Fn|]]].
  split; [apply pstep_clean; [exact H0|exact Fc]|apply pstep_atom, Em].
Qed.

Local Lemma tidy_top : forall v, tidy v -> normal (top_of v) /\ clean (top_of v).
Proof.
  intros [[|f rest] out md] (Hn & Hc & Fn & Fc & _); [split; assumption|].
  apply Forall_cons_iff in Fn as [Fn _]. apply Forall_cons_iff in Fc as [Fc _].
  split; assumption.
Qed.

Local Lemma pbyte_tidy : forall i c v, tidy v -> tidy (pbyte i c v).
Proof.
  intros i c v (Hn & Hc & Fn & Fc & A).
  assert (Ao : atom_ok (pbyte i c v)).
  { unfold atom_ok, pbyte in *. destruct (pv_mode v) as [|b kids d e txt|x e] eqn:Em.
    - rewrite Em. exact Logic.I.
    - destruct (match e with Some e' => Nat.eqb i e' | None => false end).
      + rewrite (proj2 (pv_add_live _ _)). exact Logic.I.
      + exact Logic.I.
    - destruct (Nat.eqb i e); [rewrite (proj2 (pv_add_live _ _)); exact Logic.I|rewrite Em; exact A]. }
  split; [|split; [|split; [apply pbyte_normal, Fn|split; [apply pbyte_clean; assumption|exact Ao]]]];
    unfold atom_ok, pbyte in *; destruct (pv_mode v) as [|b kids d e txt|x e]; try assumption.
  - destruct (match e with Some e' => Nat.eqb i e' | None => false end); [|assumption].
    destruct (pv_add_out (region_node b (map mk kids) (if b then dest_text false txt else txt))
                (pv_setmode PMNormal v)) as [H|H]; rewrite H; [assumption|apply normal_xsnoc, Hn].
  - destruct (Nat.eqb i e); [|assumption].
    destruct (pv_add_out x (pv_setmode PMNormal v)) as [H|H]; rewrite H; [assumption|apply normal_xsnoc, Hn].
  - destruct (match e with Some e' => Nat.eqb i e' | None => false end); [|assumption].
    destruct (pv_add_out (region_node b (map mk kids) (if b then dest_text false txt else txt))
                (pv_setmode PMNormal v)) as [H|H]; rewrite H;
      [assumption|apply clean_xsnoc; [destruct b; discriminate|exact Hc]].
  - destruct (Nat.eqb i e); [|assumption].
    destruct (pv_add_out x (pv_setmode PMNormal v)) as [H|H]; rewrite H;
      [assumption|apply clean_xsnoc; [apply A|exact Hc]].
Qed.

(*
Tokens of a line
----------------
*)

Local Lemma dchar_nl : forall k, Ascii.eqb (dchar k) nl_char = false.
Proof. intros k. apply Ascii.eqb_neq, dchar_not_nl. Qed.

Local Lemma dchar_tick : forall k, is_tick (dchar k) = false.
Proof. intros k. exact (proj1 (proj2 (dreserved_false _ (dchar_free k)))). Qed.

Local Lemma dchar_dollar : forall k, Ascii.eqb (dchar k) dollar = false.
Proof.
  intros k. pose proof (dreserved_false _ (dchar_free k)) as (_ & _ & _ & _ & _ & _ & _ & H & _).
  exact H.
Qed.

(* A token with no `}` after it. *)
Local Lemma nt_token : forall k prev rest,
  dstyle_of (dchar k) = Some k -> at_rbrace (get 0 rest) = false ->
  next_tok prev (dtoken k ++ rest)
  = Some (TDelim k false (bare_opens k && nonspace_at (get 0 rest)) (nonspace_at prev), dwidth k).
Proof.
  intros k prev rest Hk Hr. destruct (dchar_plain k) as (Hlb & _ & Hlk & Hrk).
  assert (Hpre : prefix (dtoken k) (dtoken k ++ rest) = true) by (apply prefix_chars; lia).
  destruct (dtoken_cons k) as (w & Ew & Ed).
  rewrite Ed at 1. cbn [append next_tok]. rewrite dchar_nl, dchar_nb, dchar_tick, dchar_dollar, Hlk, Hrk, Hlb, Hk.
  replace (String (dchar k) (chars (dchar k) w ++ rest))
    with (dtoken k ++ rest)%string by (rewrite Ed; reflexivity).
  rewrite Hpre. unfold dtoken. rewrite Ew, get_chars, Hr. reflexivity.
Qed.

Local Lemma nt_marked_close : forall k prev r,
  dstyle_of (dchar k) = Some k ->
  next_tok prev (dtoken k ++ String rbrace r) = Some (TDelim k true false true, S (dwidth k)).
Proof.
  intros k prev r Hk. destruct (dchar_plain k) as (Hlb & _ & Hlk & Hrk).
  assert (Hpre : prefix (dtoken k) (dtoken k ++ String rbrace r) = true)
    by (apply prefix_chars; lia).
  destruct (dtoken_cons k) as (w & Ew & Ed).
  rewrite Ed at 1. cbn [append next_tok]. rewrite dchar_nl, dchar_nb, dchar_tick, dchar_dollar, Hlk, Hrk, Hlb, Hk.
  replace (String (dchar k) (chars (dchar k) w ++ String rbrace r))
    with (dtoken k ++ String rbrace r)%string by (rewrite Ed; reflexivity).
  rewrite Hpre. unfold dtoken. rewrite Ew, get_chars. cbn [get at_rbrace].
  rewrite Ascii.eqb_refl. reflexivity.
Qed.

Local Lemma nt_marked_open : forall k prev rest,
  dstyle_of (dchar k) = Some k ->
  next_tok prev (String lbrace (dtoken k ++ rest)) = Some (TDelim k true true false, S (dwidth k)).
Proof.
  intros k prev rest Hk.
  assert (Hpre : prefix (dtoken k) (dtoken k ++ rest) = true) by (apply prefix_chars; lia).
  destruct (dtoken_cons k) as (w & Ew & Ed).
  cbn [next_tok]. change (Ascii.eqb lbrace nl_char) with false.
  change (is_bslash lbrace) with false. change (is_tick lbrace) with false. try change (Ascii.eqb lbrace dollar) with false.
  change (Ascii.eqb lbrace lbrack) with false.
  change (Ascii.eqb lbrace rbrack) with false. rewrite Ascii.eqb_refl.
  rewrite Ed at 1. cbn [append]. rewrite Hk.
  replace (String (dchar k) (chars (dchar k) w ++ rest))
    with (dtoken k ++ rest)%string by (rewrite Ed; reflexivity).
  rewrite Hpre. reflexivity.
Qed.

(* A row's character short of a token is text. *)
Local Lemma nt_short : forall k j prev rest,
  dstyle_of (dchar k) = Some k -> S j < dwidth k ->
  (forall d r, rest = String d r -> d <> dchar k) ->
  next_tok prev (String (dchar k) (chars (dchar k) j ++ rest)) = Some (TText (dchar k), 1).
Proof.
  intros k j prev rest Hk Hj Hr. destruct (dchar_plain k) as (Hlb & _ & Hlk & Hrk).
  cbn [next_tok]. rewrite dchar_nl, dchar_nb, dchar_tick, dchar_dollar, Hlk, Hrk, Hlb, Hk.
  change (String (dchar k) (chars (dchar k) j ++ rest))
    with (chars (dchar k) (S j) ++ rest)%string.
  unfold dtoken. rewrite (prefix_chars_short (dchar k) (dwidth k) (S j) rest Hj Hr).
  reflexivity.
Qed.

(* `{` before a run too short to be a token is text. *)
Local Lemma nt_lbrace_short : forall k j prev rest,
  dstyle_of (dchar k) = Some k -> S j < dwidth k ->
  (forall d r, rest = String d r -> d <> dchar k) ->
  next_tok prev (String lbrace (chars (dchar k) (S j) ++ rest)) = Some (TText lbrace, 1).
Proof.
  intros k j prev rest Hk Hj Hr.
  cbn [next_tok]. change (Ascii.eqb lbrace nl_char) with false.
  change (is_bslash lbrace) with false. change (is_tick lbrace) with false. try change (Ascii.eqb lbrace dollar) with false.
  change (Ascii.eqb lbrace lbrack) with false.
  change (Ascii.eqb lbrace rbrack) with false. rewrite Ascii.eqb_refl.
  cbn [chars append]. rewrite Hk.
  change (String (dchar k) (chars (dchar k) j ++ rest))
    with (chars (dchar k) (S j) ++ rest)%string.
  unfold dtoken. rewrite (prefix_chars_short (dchar k) (dwidth k) (S j) rest Hj Hr).
  reflexivity.
Qed.

(* A byte that is no row's character, no `{`, no bracket and no
   newline. *)
Local Lemma nt_byte : forall c prev rest,
  Ascii.eqb c nl_char = false -> is_bslash c = false -> is_tick c = false ->
  Ascii.eqb c dollar = false ->
  Ascii.eqb c lbrack = false -> Ascii.eqb c rbrack = false ->
  Ascii.eqb c lbrace = false -> dstyle_of c = None ->
  next_tok prev (String c rest) = Some (TText c, 1).
Proof.
  intros c prev rest H H0 Ht Hdl H1 H2 H3 H4. cbn [next_tok]. rewrite H, H0, Ht, Hdl, H1, H2, H3, H4.
  reflexivity.
Qed.

Local Lemma nt_rbrack : forall prev s',
  next_tok prev (String rbrack s')
  = Some (if starts_with lparen s' then TClose true
          else if starts_with lbrack s' then TClose false else TText rbrack, 1).
Proof. reflexivity. Qed.

(* A backslash on a line. *)
Local Lemma nt_bs : forall p s, no_char nl_char s = true ->
  next_tok p (String bslash s)
  = Some (if is_blank s then (THard s, S (String.length s))
          else match s with
               | String d _ =>
                   if is_ws d then (TEscWs (ws_run s), S (String.length (ws_run s)))
                   else (TEsc d, 2)
               | EmptyString => (THard EmptyString, 1)
               end).
Proof.
  intros p s H. cbn [next_tok]. change (Ascii.eqb bslash nl_char) with false.
  change (is_bslash bslash) with true. cbn iota. rewrite (line_rest_line s H). reflexivity.
Qed.

Local Lemma alphabet_nl : forall c, in_alphabet c = true -> Ascii.eqb c nl_char = false.
Proof.
  intros c H. unfold in_alphabet in H. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H _].
  apply negb_true_iff in H. exact H.
Qed.

(* A line over the alphabet holds no newline. *)
Local Lemma alphabet_no_nl : forall s, over_alphabet s = true -> no_char nl_char s = true.
Proof.
  fix IH 1. intros [|c s] H; [reflexivity|].
  cbn [over_alphabet] in H. cbn [no_char].
  destruct (is_bslash c) eqn:Eb.
  - assert (Ascii.eqb c nl_char = false) as -> by (unfold is_bslash in Eb;
      apply Ascii.eqb_eq in Eb; subst c; reflexivity).
    destruct s as [|d r]; [reflexivity|]. apply andb_true_iff in H as [Hd H].
    apply andb_true_iff in Hd as [Hd _].
    apply negb_true_iff in Hd. cbn [no_char negb andb]. rewrite Hd. exact (IH r H).
  - apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 _].
    rewrite (alphabet_nl c H1). exact (IH s H3).
Qed.

(*
A verbatim, scanned
-------------------

The scanner reads a verbatim byte by byte: its opening run, then its
body with the backticks pending, until a run of the opening's width is
followed by anything but a backtick.
*)

Local Lemma iscan_open_ticks : forall k txt prev o, 0 < k ->
  iscan_str (ticks k) (IText false txt prev o) = IOpen k VVerb (flush_text txt o).
Proof.
  intros k txt prev o Hk. destruct k as [|k]; [lia|]. clear Hk.
  assert (G : forall j o', iscan_str (ticks k) (IOpen (S j) VVerb o') = IOpen (S j + k) VVerb o').
  { induction k as [|k IH]; intros j o'; [cbn; f_equal; lia|].
    cbn [ticks iscan_str]. unfold istep. cbn [istep_at]. change (is_tick tick) with true. cbn iota.
    rewrite IH. f_equal. lia. }
  cbn [ticks iscan_str]. unfold istep. cbn [istep_at]. unfold ilead.
  change (is_bslash tick) with false. change (is_tick tick) with true. cbn iota.
  rewrite G. reflexivity.
Qed.

Local Lemma verb_go_stop : forall s n run,
  snd (verb_go n run s) = true ->
  forall c, get (snd (fst (verb_go n run s))) s = Some c -> is_tick c = false.
Proof.
  induction s as [|d s IH]; intros n run; cbn [verb_go].
  - destruct (Nat.eqb run n); intros _ c E; discriminate E.
  - destruct (is_tick d) eqn:Ed.
    + specialize (IH n (S run)). destruct (verb_go n (S run) s) as [[b l] cl].
      cbn [fst snd] in *. exact IH.
    + destruct (Nat.eqb run n).
      * intros _ c E. cbn in E. injection E as <-. exact Ed.
      * specialize (IH n 0). destruct (verb_go n 0 s) as [[b l] cl]. cbn [fst snd] in *. exact IH.
Qed.

Local Lemma verb_go_scan : forall s n run txt vk o, n <> 0 ->
  let r := verb_go n run s in
  (forall k, k < snd (fst r) ->
     exists r' t, iscan_str (substring 0 k s) (IVerb n run txt vk o) = IVerb n r' t vk o
                  /\ (r' = n -> get k s = Some tick))
  /\ (snd r = true ->
       iscan_str (substring 0 (snd (fst r)) s) (IVerb n run txt vk o)
       = IVerb n n (txt ++ fst (fst r)) vk o)
  /\ (snd r = false -> snd (fst r) = String.length s
       /\ exists r' t, iscan_str s (IVerb n run txt vk o) = IVerb n r' t vk o /\ r' <> n
                       /\ (t ++ ticks r')%string = (txt ++ fst (fst r))%string).
Proof.
  induction s as [|c s IH]; intros n run txt vk o Hn; cbn [verb_go].
  - destruct (Nat.eqb run n) eqn:E; cbn [fst snd].
    + apply Nat.eqb_eq in E. subst run. split; [intros k Hk; lia|].
      split; [intros _; cbn; rewrite append_empty_r; reflexivity|intros H; discriminate H].
    + apply Nat.eqb_neq in E. split; [intros k Hk; lia|]. split; [intros H; discriminate H|].
      intros _. split; [reflexivity|]. exists run, txt. auto.
  - destruct (is_tick c) eqn:Ec.
    + (* a backtick joins the pending run *)
      specialize (IH n (S run) txt vk o Hn).
      destruct (verb_go n (S run) s) as [[b l] cl]. cbn [fst snd] in *.
      destruct IH as (I1 & I2 & I3).
      assert (St : istep c (IVerb n run txt vk o) = IVerb n (S run) txt vk o)
        by (unfold istep; cbn [istep_at]; rewrite Ec; reflexivity).
      split; [|split].
      * intros [|k] Hk.
        -- exists run, txt. split; [reflexivity|]. intros _. cbn.
           apply Ascii.eqb_eq in Ec. subst c. reflexivity.
        -- cbn [substring iscan_str]. rewrite St. apply I1. lia.
      * intros Hc. cbn [substring iscan_str]. rewrite St. exact (I2 Hc).
      * intros Hc. destruct (I3 Hc) as (El & r' & t & E1 & E2 & E3).
        split; [cbn; lia|]. exists r', t. cbn [iscan_str]. rewrite St. auto.
    + destruct (Nat.eqb run n) eqn:E.
      * (* the run before it closes *)
        apply Nat.eqb_eq in E. subst run. cbn [fst snd].
        split; [intros k Hk; lia|].
        split; [intros _; cbn; rewrite append_empty_r; reflexivity|intros H; discriminate H].
      * (* the run before it and the byte are body *)
        apply Nat.eqb_neq in E.
        specialize (IH n 0 (txt ++ ticks run ++ one c)%string vk o Hn).
        destruct (verb_go n 0 s) as [[b l] cl]. cbn [fst snd] in *.
        destruct IH as (I1 & I2 & I3).
        assert (St : istep c (IVerb n run txt vk o)
                     = IVerb n 0 (txt ++ ticks run ++ one c)%string vk o).
        { unfold istep; cbn [istep_at]. rewrite Ec. apply Nat.eqb_neq in E. rewrite E.
          reflexivity. }
        split; [|split].
        -- intros [|k] Hk.
           ++ exists run, txt. split; [reflexivity|]. intros H. contradiction.
           ++ cbn [substring iscan_str]. rewrite St. apply I1. lia.
        -- intros Hc. cbn [substring iscan_str]. rewrite St, (I2 Hc).
           rewrite !append_assoc. reflexivity.
        -- intros Hc. destruct (I3 Hc) as (El & r' & t & E1 & E2 & E3).
           split; [cbn; lia|]. exists r', t. cbn [iscan_str]. rewrite St.
           split; [exact E1|]. split; [exact E2|]. rewrite E3, !append_assoc. reflexivity.
Qed.

Local Lemma iscan_open_verb : forall c t m vk o,
  is_tick c = false -> m <> 0 ->
  iscan_str (String c t) (IOpen m vk o) = iscan_str (String c t) (IVerb m 0 "" vk o).
Proof.
  intros c t m vk o Hc Hm. cbn [iscan_str]. f_equal. unfold istep. cbn [istep_at]. rewrite Hc.
  replace (Nat.eqb 0 m) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.

Local Lemma substring_sdrop : forall ps p k, substring p k ps = substring 0 k (sdrop p ps).
Proof.
  induction ps as [|x ps IH]; intros [|p] k; cbn [substring sdrop]; try reflexivity.
  - destruct k; reflexivity.
  - apply IH.
Qed.

Local Lemma substring_app_r : forall a b j,
  substring 0 (String.length a + j) (a ++ b) = (a ++ substring 0 j b)%string.
Proof.
  induction a as [|x a IH]; intros b j; [reflexivity|]. cbn [String.length Nat.add append substring].
  rewrite IH. reflexivity.
Qed.

Local Lemma substring_ticks : forall m k x, k <= m -> substring 0 k (ticks m ++ x) = ticks k.
Proof.
  induction m as [|m IH]; intros [|k] x Hk; try lia; cbn [ticks append substring];
    [destruct x; reflexivity|reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.

Local Lemma get_add : forall p ps j, get (p + j) ps = get j (sdrop p ps).
Proof.
  induction p as [|p IH]; intros ps j; [reflexivity|].
  destruct ps as [|x ps]; [destruct j; reflexivity|]. exact (IH ps j).
Qed.

Local Lemma tick_run_split : forall w,
  w = (ticks (tick_run w) ++ sdrop (tick_run w) w)%string
  /\ starts_tick (sdrop (tick_run w) w) = false.
Proof.
  induction w as [|c w IH]; [split; reflexivity|]. cbn [tick_run].
  destruct (is_tick c) eqn:Ec.
  - destruct IH as [E1 E2]. cbn [ticks append sdrop]. split; [|exact E2].
    apply Ascii.eqb_eq in Ec. subst c. f_equal. exact E1.
  - split; [reflexivity|exact Ec].
Qed.

Local Lemma iscan_dollars_more : forall j t p o,
  iscan_str (chars dollar j) (IDollar true t p o)
  = IDollar true (t ++ chars dollar j) (match j with 0 => p | _ => Some dollar end) o.
Proof.
  induction j as [|j IH]; intros t p o; [cbn; rewrite append_empty_r; reflexivity|].
  cbn [chars iscan_str]. unfold istep. cbn [istep_at]. unfold idollar_step.
  rewrite Ascii.eqb_refl. tred. rewrite IH. rewrite append_assoc. destruct j; reflexivity.
Qed.

(* A run of dollars from text: the scanner holds it, the last two
   pending. *)
Local Lemma iscan_dollars : forall k txt prev o, 0 < k ->
  iscan_str (chars dollar k) (IText false txt prev o)
  = match k with
    | 1 => IDollar false txt prev o
    | _ => IDollar true (txt ++ chars dollar (k - 2)) (if Nat.ltb 2 k then Some dollar else prev) o
    end.
Proof.
  intros [|[|k]] txt prev o Hk; [lia| |].
  - cbn [chars iscan_str]. unfold istep. cbn [istep_at]. unfold ilead.
    change (is_bslash dollar) with false. change (is_tick dollar) with false.
    rewrite Ascii.eqb_refl. reflexivity.
  - cbn [chars iscan_str]. unfold istep at 2. cbn [istep_at]. unfold ilead.
    change (is_bslash dollar) with false. change (is_tick dollar) with false.
    rewrite Ascii.eqb_refl. unfold istep. cbn [istep_at]. unfold idollar_step.
    rewrite Ascii.eqb_refl. rewrite iscan_dollars_more. replace (S (S k) - 2) with k by lia.
    destruct k; reflexivity.
Qed.

Local Lemma dollar_run_split : forall w,
  w = (chars dollar (dollar_run w) ++ sdrop (dollar_run w) w)%string.
Proof.
  induction w as [|c w IH]; [reflexivity|]. cbn [dollar_run].
  destruct (Ascii.eqb c dollar) eqn:Ec; [|reflexivity].
  apply Ascii.eqb_eq in Ec. subst c. cbn [chars append sdrop]. f_equal. exact IH.
Qed.

(* The bytes a raw spec's format may hold. *)
Fixpoint fmt_ok (f : string) : bool :=
  match f with
  | EmptyString => true
  | String c r =>
      (negb (Ascii.eqb c rbrace) && negb (raw_stop c || Ascii.eqb c nl_char) && fmt_ok r)%bool
  end.

Local Lemma fmt_go_split : forall x f, fmt_go x = Some f ->
  fmt_ok f = true /\ exists rest, x = (f ++ String rbrace rest)%string.
Proof.
  induction x as [|c x IH]; intros f H; [discriminate|]. cbn [fmt_go] in H.
  destruct (Ascii.eqb c rbrace) eqn:Eb.
  { injection H as <-. apply Ascii.eqb_eq in Eb. subst c. split; [reflexivity|]. exists x.
    reflexivity. }
  destruct (raw_stop c || Ascii.eqb c nl_char)%bool eqn:Es; [discriminate|].
  destruct (fmt_go x) as [f'|] eqn:E; [|discriminate]. injection H as <-.
  destruct (IH f' eq_refl) as [Ok [rest ->]]. split.
  - cbn [fmt_ok]. rewrite Eb, Es, Ok. reflexivity.
  - exists rest. reflexivity.
Qed.

Local Lemma raw_spec_split : forall x f, raw_spec x = Some f ->
  f <> EmptyString /\ fmt_ok f = true
  /\ exists rest, x = String lbrace (String eqchar (f ++ String rbrace rest)).
Proof.
  intros [|b [|e r]] f H; try discriminate. cbn [raw_spec] in H.
  destruct (Ascii.eqb b lbrace && Ascii.eqb e eqchar)%bool eqn:Ebe; [|discriminate].
  apply andb_true_iff in Ebe as [Eb Ee]. apply Ascii.eqb_eq in Eb, Ee. subst b e.
  destruct (fmt_go r) as [[|c f']|] eqn:E; try discriminate. injection H as <-.
  destruct (fmt_go_split r _ E) as [Ok [rest ->]].
  split; [discriminate|]. split; [exact Ok|]. exists rest. reflexivity.
Qed.

Local Lemma iscan_raw_fmt : forall f spec t o, fmt_ok f = true -> spec <> EmptyString ->
  forall j, iscan_str (substring 0 j f) (IRaw spec t o) = IRaw (spec ++ substring 0 j f) t o.
Proof.
  induction f as [|c f IH]; intros spec t o Ok Hs j.
  - destruct j; cbn; rewrite append_empty_r; reflexivity.
  - destruct j as [|j]; [cbn; rewrite append_empty_r; reflexivity|].
    cbn [fmt_ok] in Ok. apply andb_true_iff in Ok as [Ok Okf]. apply andb_true_iff in Ok as [Eb Es].
    apply negb_true_iff in Eb, Es.
    cbn [substring iscan_str]. unfold istep. cbn [istep_at]. unfold iraw_step_at.
    rewrite Eb. cbn [andb].
    replace (tnonempty spec) with true by (destruct spec; [contradiction|reflexivity]).
    apply orb_false_iff in Es as [Es _]. rewrite Es. cbn [orb]. tred.
    rewrite (IH (spec ++ one c)%string t o Okf) by (destruct spec; discriminate).
    rewrite append_assoc. reflexivity.
Qed.

(* A raw spec after a verbatim's closing run: the scanner holds it, and
   its `}` makes the raw node. *)
Local Lemma iscan_raw_spec : forall m b o f, fmt_ok f = true -> f <> EmptyString ->
  raw_inline_enabled = true ->
  (forall j, 0 < j <= S (S (String.length f)) ->
     exists spec, iscan_str (substring 0 j (String lbrace (String eqchar f))) (IVerb m m b VVerb o)
                  = IRaw spec (trim_verb b) o /\ (spec = EmptyString -> j = 1))
  /\ iscan_str (String lbrace (String eqchar f) ++ one rbrace) (IVerb m m b VVerb o)
     = IText false "" (Some rbrace) (oemit (mk (RawInline f (trim_verb b))) o).
Proof.
  intros m b o f Ok Hf Hr.
  assert (S1 : istep lbrace (IVerb m m b VVerb o) = IRaw "" (trim_verb b) o).
  { unfold istep. cbn [istep_at]. change (is_tick lbrace) with false. rewrite Nat.eqb_refl.
    reflexivity. }
  assert (S2 : istep eqchar (IRaw "" (trim_verb b) o) = IRaw (one eqchar) (trim_verb b) o)
    by reflexivity.
  split.
  - intros [|[|j]] Hj; [lia| |].
    + exists "". cbn [substring iscan_str]. rewrite S1. split; reflexivity.
    + cbn [substring iscan_str]. rewrite S1, S2.
      rewrite iscan_raw_fmt by (exact Ok || discriminate). eexists.
      split; [reflexivity|intros E; discriminate E].
  - cbn [append iscan_str]. rewrite S1, S2.
    pose proof (iscan_raw_fmt f (one eqchar) (trim_verb b) o Ok ltac:(discriminate) (String.length f))
      as E.
    rewrite <- (Nat.sub_0_r (String.length f)), substring_rest in E. cbn [sdrop] in E.
    rewrite iscan_str_app, E.
    change (one rbrace) with (String rbrace ""). cbn [iscan_str]. unfold istep. cbn [istep_at].
    unfold iraw_step_at. change (Ascii.eqb rbrace rbrace) with true.
    replace (raw_spec_ok (tval (one eqchar ++ f))) with true
      by (destruct f; [contradiction|reflexivity]).
    cbn [andb]. rewrite Hr. reflexivity.
Qed.

Local Lemma tok_at_verb : forall ps p d m body cl r l,
  tok_at ps p = Some (TVerb d m body cl r, l) ->
  exists w, sdrop p ps = (chars dollar d ++ w)%string /\ starts_tick w = true
    /\ verb_tok d w = (TVerb d m body cl r, l - d) /\ d < l /\ (d = 0 \/ math_enabled = true).
Proof.
  intros ps p d m body cl r l H.
  unfold tok_at, next_tok in H. destruct (sdrop p ps) as [|c r0] eqn:Es; [discriminate|].
  injection H as H.
  destruct (Ascii.eqb c nl_char); [discriminate|].
  destruct (is_bslash c).
  { destruct (is_blank (line_rest r0)); [discriminate|].
    destruct r0 as [|d' r']; [discriminate|]. destruct (is_ws d'); discriminate. }
  destruct (is_tick c) eqn:Et.
  { assert (d = 0) as ->
      by (destruct (verb_tok_shape 0 (String c r0)) as (? & ? & ? & ? & ? & E); rewrite E in H;
          injection H as <- _ _ _ _ _; reflexivity).
    exists (String c r0). split; [reflexivity|]. split; [exact Et|].
    rewrite Nat.sub_0_r. split; [exact H|].
    pose proof (verb_tok_len 0 (String c r0) _ _ Et H). split; [lia|left; reflexivity]. }
  destruct (Ascii.eqb c dollar) eqn:Ed.
  { unfold dollar_tok in H. set (w0 := String c r0) in *.
    destruct (math_enabled && starts_with tick (sdrop (dollar_run w0) w0))%bool
      eqn:E; [|discriminate].
    apply andb_true_iff in E as [Em E].
    destruct (verb_tok (dollar_run w0) (sdrop (dollar_run w0) w0)) as [t0 l0] eqn:Ev.
    injection H as -> <-.
    assert (Dd : dollar_run w0 = d).
    { destruct (verb_tok_shape (dollar_run w0) (sdrop (dollar_run w0) w0))
        as (? & ? & ? & ? & ? & E1).
      rewrite E1 in Ev. injection Ev as E0 _ _ _ _ _. exact E0. }
    change (if (c =? dollar)%char then S (dollar_run r0) else 0) with (dollar_run w0).
    rewrite Dd in Ev, E |- *.
    exists (sdrop d w0).
    split; [rewrite <- Dd; apply dollar_run_split|]. split; [exact E|].
    replace (d + l0 - d) with l0 by lia.
    split; [exact Ev|]. pose proof (verb_tok_len _ _ _ _ E Ev). split; [lia|right; exact Em]. }
  exfalso. repeat match type of H with
  | context [if ?b then _ else _] => destruct b
  | context [match ?x with Some _ => _ | None => _ end] => destruct x
  | context [match ?x with EmptyString => _ | String _ _ => _ end] => destruct x
  | context [match ?x with O => _ | S _ => _ end] => destruct x
  end; inversion H.
Qed.

Local Lemma tok_verb_width : forall ps p d m body cl r l,
  tok_at ps p = Some (TVerb d m body cl r, l) -> m <> 0.
Proof.
  intros ps p d m body cl r l H.
  destruct (tok_at_verb ps p d m body cl r l H) as (w & _ & Hst & Hv & _).
  unfold verb_tok in Hv. destruct (verb_go (tick_run w) 0 (sdrop (tick_run w) w)) as [[b u] c0].
  assert (E : tick_run w = m)
    by (destruct (if (c0 && (d =? 0)%nat && raw_inline_enabled)%bool
                  then raw_spec (sdrop (tick_run w + u) w) else None);
        inversion Hv; reflexivity).
  subst m. destruct w; [discriminate|]. cbn in Hst |- *. rewrite Hst. discriminate.
Qed.

(* The scanner's kind of span for a verbatim with `d` dollars before it. *)
Definition vkind_of (d : nat) : vkind :=
  match d with 0 => VVerb | 1 => VMath InlineMath | _ => VMath DisplayMath end.

Local Lemma iscan_verb_open : forall d m txt prev o, 0 < m -> (d = 0 \/ math_enabled = true) ->
  iscan_str (chars dollar d ++ ticks m) (IText false txt prev o)
  = IOpen m (vkind_of d) (flush_text (txt ++ chars dollar (d - 2)) o).
Proof.
  intros d m txt prev o Hm Hd. destruct m as [|m]; [lia|]. clear Hm.
  assert (G : forall j vk o', iscan_str (ticks m) (IOpen (S j) vk o') = IOpen (S j + m) vk o').
  { induction m as [|m IH]; intros j vk o'; [cbn; f_equal; lia|].
    cbn [ticks iscan_str]. unfold istep. cbn [istep_at]. change (is_tick tick) with true. cbn iota.
    rewrite IH. f_equal. lia. }
  rewrite iscan_str_app. destruct d as [|d].
  - cbn [chars iscan_str ticks]. unfold istep. cbn [istep_at]. unfold ilead.
    change (is_bslash tick) with false. change (is_tick tick) with true. cbn iota.
    rewrite G. cbn [Nat.sub chars]. rewrite append_empty_r. reflexivity.
  - destruct Hd as [Hd|Hm]; [discriminate|].
    rewrite iscan_dollars by lia. cbn [ticks iscan_str].
    destruct d as [|d]; unfold istep; cbn [istep_at]; unfold idollar_step;
      change (Ascii.eqb tick dollar) with false; change (is_tick tick) with true; rewrite Hm;
      cbn [andb]; rewrite G.
    + cbn [Nat.sub chars]. rewrite append_empty_r. reflexivity.
    + replace (S (S d) - 2) with d by lia. reflexivity.
Qed.

Local Lemma substring_chars : forall c m k x, k <= m -> substring 0 k (chars c m ++ x) = chars c k.
Proof.
  intros c. induction m as [|m IH]; intros [|k] x Hk; try lia; cbn [chars append substring];
    [destruct x; reflexivity|destruct (chars c m ++ x); reflexivity|].
  rewrite IH by lia. reflexivity.
Qed.

Local Lemma get_chars_lt : forall c n k r, k < n -> get k (chars c n ++ r) = Some c.
Proof. intros c. induction n as [|n IH]; intros [|k] r Hk; try lia; [reflexivity|]. cbn. apply IH. lia. Qed.

(* Where a verbatim's reading can be between two of its bytes: past
   dollars, before a dollar or the backtick run; a closing run is
   complete only before a backtick or a raw spec; a raw spec is followed
   by a byte of it, never the newline. *)
Definition verb_state (X : iscan) (next : option ascii) : Prop :=
  match X with
  | IDollar _ _ _ _ => next = Some tick \/ next = Some dollar
  | IOpen _ _ _ => True
  | IVerb m r _ _ _ => r = m -> next = Some tick \/ next = Some lbrace
  | IRaw spec _ _ => exists c, next = Some c /\ c <> nl_char /\ (spec = EmptyString -> c = eqchar)
  | _ => False
  end.

Local Lemma vnode_of : forall d b, vnode (vkind_of d) (trim_verb b) = verb_node d None b.
Proof. intros [|[|d]] b; reflexivity. Qed.

Local Lemma fmt_ok_get : forall f i, fmt_ok f = true -> i < String.length f ->
  exists c, get i f = Some c /\ c <> nl_char.
Proof.
  induction f as [|c f IH]; intros i Ok Hi; [cbn in Hi; lia|].
  cbn [fmt_ok] in Ok. apply andb_true_iff in Ok as [Ok Okf]. apply andb_true_iff in Ok as [_ Es].
  apply negb_true_iff, orb_false_iff in Es as [_ En].
  destruct i as [|i].
  - exists c. split; [reflexivity|]. intros E. subst c. rewrite Ascii.eqb_refl in En. discriminate.
  - cbn [get]. apply IH; [exact Okf|cbn in Hi; lia].
Qed.

Local Lemma substring_split : forall x a j, a <= String.length x ->
  substring 0 (a + j) x = (substring 0 a x ++ substring 0 j (sdrop a x))%string.
Proof.
  induction x as [|c x IH]; intros a j Ha.
  - destruct a; [|cbn in Ha; lia]. destruct j; reflexivity.
  - destruct a as [|a].
    + cbn [Nat.add sdrop append]. rewrite substring_nil. reflexivity.
    + cbn [Nat.add substring sdrop append]. cbn in Ha. rewrite IH by lia. reflexivity.
Qed.

Local Lemma substring_app_l : forall a b j, j <= String.length a ->
  substring 0 j (a ++ b) = substring 0 j a.
Proof.
  induction a as [|c a IH]; intros b j Hj.
  - destruct j; [|cbn in Hj; lia]. rewrite !substring_nil. reflexivity.
  - destruct j as [|j]; [reflexivity|]. cbn [append substring]. cbn in Hj. rewrite IH by lia.
    reflexivity.
Qed.

Local Lemma verb_tok_scan : forall ps p d m body cl r l txt prev o,
  tok_at ps p = Some (TVerb d m body cl r, l) ->
  (forall k, 0 < k < l ->
     verb_state (iscan_str (substring p k ps) (IText false txt prev o)) (get (p + k) ps))
  /\ (cl = true -> r = None ->
      iscan_str (substring p l ps) (IText false txt prev o)
      = IVerb m m body (vkind_of d) (flush_text (txt ++ chars dollar (d - 2)) o)
      /\ (forall c, get (p + l) ps = Some c -> is_tick c = false)
      /\ (d = 0 -> raw_inline_enabled = true -> raw_spec (sdrop (p + l) ps) = None))
  /\ (forall f, r = Some f -> d = 0 /\ cl = true /\ get (p + pred l) ps = Some rbrace
      /\ iscan_str (substring p l ps) (IText false txt prev o)
         = IText false "" (Some rbrace) (oemit (mk (RawInline f (trim_verb body))) (flush_text txt o)))
  /\ (cl = false -> r = None /\ p + l = String.length ps
      /\ ifinish (iscan_str (substring p l ps) (IText false txt prev o))
         = ifinish (IText false "" None (oemit (mk (verb_node d None body))
                                           (flush_text (txt ++ chars dollar (d - 2)) o)))).
Proof.
  intros ps p d m body cl r l txt prev o H.
  destruct (tok_at_verb ps p d m body cl r l H) as (w & Es & Hst & Hv & Hdl & Hmath).
  set (o' := flush_text (txt ++ chars dollar (d - 2)) o).
  set (vk := vkind_of d).
  pose proof (tick_run_split w) as [Ew Ens].
  set (s' := sdrop (tick_run w) w) in *.
  unfold verb_tok in Hv. fold s' in Hv.
  pose proof (verb_go_scan s' (tick_run w) 0 "" vk o') as G.
  pose proof (verb_go_stop s' (tick_run w) 0) as Stop.
  destruct (verb_go (tick_run w) 0 s') as [[b u] cl0] eqn:Ev.
  assert (Hm : tick_run w <> 0)
    by (destruct w; [discriminate|]; cbn in Hst |- *; rewrite Hst; discriminate).
  specialize (G Hm). cbn [fst snd] in G. destruct G as (G1 & G2 & G3).
  set (m0 := tick_run w) in *.
  assert (Lt : String.length (ticks m0) = m0)
    by (clear; induction m0 as [|m0 IH]; [reflexivity|cbn; rewrite IH; reflexivity]).
  assert (Ld : String.length (chars dollar d) = d) by apply length_chars.
  assert (Sub : forall k, substring p k ps = substring 0 k (chars dollar d ++ ticks m0 ++ s'))
    by (intros k; rewrite substring_sdrop, Es, <- Ew; reflexivity).
  assert (Get : forall j, get (p + (d + m0 + j)) ps = get j s').
  { intros j. rewrite get_add, Es, Ew, <- Ld, <- Lt, <- Nat.add_assoc, get_add. clear.
    induction (chars dollar d) as [|c t IH]; cbn [append sdrop]; [|exact IH].
    rewrite get_add. induction (ticks m0) as [|c t IH]; [reflexivity|exact IH]. }
  (* the dollars and the opening run *)
  assert (Pre : forall k, 0 < k <= m0 ->
            iscan_str (substring p (d + k) ps) (IText false txt prev o) = IOpen k vk o').
  { intros k Hk. rewrite Sub, <- Ld at 1. rewrite substring_app_r, substring_ticks by lia.
    apply iscan_verb_open; [lia|exact Hmath]. }
  (* past them, the body *)
  assert (Body : forall j, 0 < j <= String.length s' ->
            iscan_str (substring p (d + m0 + j) ps) (IText false txt prev o)
            = iscan_str (substring 0 j s') (IVerb m0 0 "" vk o')).
  { intros j Hj. rewrite Sub, <- append_assoc.
    replace (d + m0 + j) with (String.length (chars dollar d ++ ticks m0) + j)
      by (rewrite length_append; lia).
    rewrite substring_app_r, iscan_str_app, iscan_verb_open by (lia || exact Hmath).
    destruct s' as [|c' t'] eqn:Es'; [cbn in Hj; lia|].
    destruct j as [|j]; [lia|]. cbn [substring]. apply iscan_open_verb; [exact Ens|exact Hm]. }
  assert (Hu : u <= String.length s')
    by (pose proof (verb_go_len s' m0 0) as Lu; rewrite Ev in Lu; exact Lu).
  assert (Upto : forall k, 0 < k < d + m0 + u ->
            verb_state (iscan_str (substring p k ps) (IText false txt prev o)) (get (p + k) ps)).
  { intros k Hk. destruct (Nat.le_gt_cases k d) as [Hkd|Hkd].
    - rewrite Sub, substring_chars by lia. rewrite iscan_dollars by lia.
      rewrite get_add, Es.
      assert (Gd : get k (chars dollar d ++ w) = Some tick
                   \/ get k (chars dollar d ++ w) = Some dollar).
      { destruct (Nat.lt_ge_cases k d) as [Hlt|Hge].
        - right. apply get_chars_lt, Hlt.
        - left. replace k with d by lia. rewrite get_chars.
          destruct w as [|cw w']; [discriminate|]. cbn in Hst |- *. apply Ascii.eqb_eq in Hst.
          rewrite Hst. reflexivity. }
      destruct k as [|[|k]]; [lia|exact Gd|exact Gd].
    - destruct (Nat.le_gt_cases k (d + m0)) as [Hkm|Hkm].
      + replace k with (d + (k - d)) by lia. rewrite Pre by lia. exact Logic.I.
      + replace k with (d + m0 + (k - d - m0)) by lia. rewrite Body by lia.
        destruct (G1 (k - d - m0) ltac:(lia)) as (r' & t & E1 & E2). rewrite E1. cbn [verb_state].
        rewrite Get. intros Er. left. exact (E2 Er). }
  (* the closing run, complete *)
  assert (Closed : cl0 = true ->
            0 < u /\ iscan_str (substring p (d + m0 + u) ps) (IText false txt prev o)
                     = IVerb m0 m0 b vk o').
  { intros ->. destruct u as [|u].
    - exfalso. specialize (G2 eq_refl). cbn in G2. rewrite substring_nil in G2.
      cbn [iscan_str] in G2. injection G2 as E. lia.
    - split; [lia|]. rewrite Body by lia. rewrite (G2 eq_refl). reflexivity. }
  destruct (if (cl0 && Nat.eqb d 0 && raw_inline_enabled)%bool
            then raw_spec (sdrop (m0 + u) w) else None) as [f|] eqn:Er.
  2: { (* no raw spec *)
    injection Hv as <- <- <- <- Hl. assert (El : l = d + m0 + u) by lia. subst l.
    split; [exact Upto|]. split; [|split; [intros f E; discriminate E|]].
    - intros -> _. destruct (Closed eq_refl) as [Hu0 Ec]. split; [exact Ec|]. split.
      + intros c E. rewrite Get in E. exact (Stop eq_refl c E).
      + intros -> Eraw. cbn [andb Nat.eqb] in Er. rewrite Eraw in Er. cbn in Er.
        rewrite <- Er. rewrite <- sdrop_sdrop, Es. cbn [chars append Nat.add]. reflexivity.
    - intros ->. split; [reflexivity|].
      destruct (G3 eq_refl) as (Eu & r' & t & E1 & E2 & E3). split.
      + pose proof (sdrop_length p ps) as Ls.
        rewrite Es, length_append, Ld, Ew, length_append, Lt in Ls.
        rewrite <- Eu in Ls.
        assert (p < String.length ps).
        { destruct (Nat.lt_ge_cases p (String.length ps)) as [Hlt|Hge]; [exact Hlt|].
          exfalso. pose proof (sdrop_length p ps) as L2. rewrite Es, length_append, Ld in L2.
          destruct w; [discriminate|]. cbn in L2. lia. }
        lia.
      + destruct u as [|u].
        * destruct s' as [|c' t'] eqn:Es'; [|cbn in Eu; lia].
          cbn [verb_go] in Ev.
          replace (Nat.eqb 0 m0) with false in Ev by (symmetry; apply Nat.eqb_neq; lia).
          injection Ev as Eb. subst b. rewrite Nat.add_0_r.
          destruct m0 as [|m']; [lia|]. rewrite Pre by lia.
          unfold ifinish, ifinish_rev. cbn [ifinish_ostate iresolve ifinish_ostate_flat].
          rewrite <- (vnode_of d ""). reflexivity.
        * rewrite Body by lia. rewrite Eu, <- (Nat.sub_0_r (String.length s')), substring_rest.
          cbn [sdrop]. rewrite E1. unfold ifinish, ifinish_rev.
          cbn [ifinish_ostate iresolve ifinish_ostate_flat].
          apply Nat.eqb_neq in E2. rewrite E2.
          change (tval (tpush t (ticks r'))) with (t ++ ticks r')%string. rewrite E3.
          rewrite <- vnode_of. reflexivity. }
  (* a raw spec *)
  injection Hv as <- <- <- <- Hl.
  destruct cl0; [|discriminate Er]. destruct (Nat.eqb d 0) eqn:Ed; [|discriminate Er].
  destruct raw_inline_enabled eqn:Eraw; [|discriminate Er]. cbn [andb] in Er.
  apply Nat.eqb_eq in Ed. subst d.
  destruct (raw_spec_split _ _ Er) as (Hf & Ok & rest & Esp).
  destruct (Closed eq_refl) as [Hu0 Ec].
  assert (Hs' : sdrop u s' = (String lbrace (String eqchar f) ++ String rbrace rest)%string).
  { cbn [append]. rewrite <- Esp. unfold s'. rewrite sdrop_sdrop. reflexivity. }
  assert (Spec : forall j, iscan_str (substring p (m0 + u + j) ps) (IText false txt prev o)
                           = iscan_str (substring 0 j (sdrop u s')) (IVerb m0 m0 b VVerb o')).
  { intros j. rewrite Sub. cbn [chars append].
    replace (m0 + u + j) with (String.length (ticks m0) + (u + j)) by lia.
    rewrite substring_app_r, substring_split by lia. rewrite <- append_assoc, iscan_str_app.
    rewrite <- substring_app_r, Lt.
    replace (substring 0 (m0 + u) (ticks m0 ++ s')) with (substring p (0 + m0 + u) ps)
      by (rewrite Sub; reflexivity).
    rewrite Ec. reflexivity. }
  assert (Gs : forall j, get (p + (m0 + u + j)) ps = get j (sdrop u s')).
  { intros j. replace (p + (m0 + u + j)) with (p + (0 + m0 + (u + j))) by lia.
    rewrite Get, <- get_add. reflexivity. }
  assert (Lf : String.length (String lbrace (String eqchar f)) = S (S (String.length f)))
    by reflexivity.
  replace l with (m0 + u + S (S (S (String.length f)))) by lia.
  split; [|split; [intros _ E; discriminate E|split; [|intros E; discriminate E]]].
  - intros k Hk. destruct (Nat.lt_ge_cases k (m0 + u)) as [Hlt|Hge].
    + apply Upto. cbn. lia.
    + replace k with (m0 + u + (k - m0 - u)) by lia. rewrite Spec, Gs, Hs'.
      destruct (k - m0 - u) as [|j] eqn:Ej.
      * rewrite substring_nil. cbn [iscan_str verb_state]. intros _. right. reflexivity.
      * rewrite substring_app_l by (rewrite Lf; lia).
        destruct (proj1 (iscan_raw_spec m0 b o' f Ok Hf Eraw) (S j) ltac:(lia))
          as (spec & Esp' & He).
        rewrite Esp'. cbn [verb_state].
        destruct j as [|j].
        -- exists eqchar. split; [reflexivity|]. split; [discriminate|intros _; reflexivity].
        -- destruct (Nat.lt_ge_cases j (String.length f)) as [Hj|Hj].
           ++ destruct (fmt_ok_get f j Ok Hj) as (c & Gc & Hc).
              exists c. split; [|split; [exact Hc|intros E; discriminate (He E)]].
              cbn [append get]. clear -Gc Hj. revert j Gc Hj.
              induction f as [|x f IH]; intros [|j] Gc Hj; cbn in *; try lia;
                [exact Gc|apply IH; [exact Gc|lia]].
           ++ assert (j = String.length f) by lia. subst j.
              exists rbrace. split; [|split; [discriminate|intros E; discriminate (He E)]].
              cbn [get]. clear. induction f as [|x f IH]; [reflexivity|exact IH].
  - intros f0 E. injection E as <-. split; [reflexivity|]. split; [reflexivity|]. split.
    + replace (pred (m0 + u + S (S (S (String.length f)))))
        with (m0 + u + S (S (String.length f))) by lia.
      rewrite Gs, Hs'. cbn [get]. clear. induction f as [|x f IH]; [reflexivity|exact IH].
    + rewrite Spec, Hs'.
      replace (String lbrace (String eqchar f) ++ String rbrace rest)%string
        with ((String lbrace (String eqchar f) ++ one rbrace) ++ rest)%string
        by (rewrite append_assoc; reflexivity).
      rewrite substring_app_l by (rewrite length_append; cbn; lia).
      replace (S (S (S (String.length f))))
        with (String.length (String lbrace (String eqchar f) ++ one rbrace) - 0)
        by (rewrite length_append; cbn; lia).
      rewrite substring_rest. cbn [sdrop].
      rewrite (proj2 (iscan_raw_spec m0 b o' f Ok Hf Eraw)).
      unfold o'. cbn [Nat.sub chars]. rewrite append_empty_r. reflexivity.
Qed.

(*
The simulation
==============

At a byte `n` of a line the scanner is in the view of the paragraph up
to `n`: in text mode, in a reference label, or in a destination that
the bytes ahead close; inside one reading per destination that they do
not close.
*)

Local Lemma pruns_trans : forall ps i h v j h1 v1 k h2 v2,
  pruns ps i h v j h1 v1 -> pruns ps j h1 v1 k h2 v2 -> pruns ps i h v k h2 v2.
Proof.
  intros ps i h v j h1 v1 k h2 v2 H. revert k h2 v2.
  induction H as [|i h v j' h' v' j h1 v1 Hu _ IH]; intros k h2 v2 H2; [exact H2|].
  apply (pruns_step ps i h v j' h' v'); [exact Hu|apply IH, H2].
Qed.

Local Lemma pruns_one : forall ps i h v j h1 v1,
  punit ps i h v = Some (j, h1, v1) -> pruns ps i h v j h1 v1.
Proof. intros. apply (pruns_step ps i h v j h1 v1); [assumption|constructor]. Qed.

Local Lemma sdrop_app_tail : forall ps n a b,
  sdrop n ps = (a ++ b)%string -> sdrop (n + String.length a) ps = b.
Proof.
  intros ps n a b H. rewrite <- sdrop_sdrop, H. clear.
  induction a as [|c a IH]; [reflexivity|exact IH].
Qed.

Local Lemma before_sdrop : forall ps n c r,
  sdrop n ps = String c r -> before ps (S n) = Some c.
Proof.
  intros ps n. cbn [before]. revert ps. induction n as [|n IH]; intros [|x ps] c r H;
    cbn [sdrop get] in *; try discriminate; [injection H as -> _; reflexivity|exact (IH ps c r H)].
Qed.

Local Lemma tok_at_line : forall ps n s after prev,
  sdrop n ps = (s ++ after)%string -> line_end after -> s <> EmptyString ->
  starts_tick s = false -> starts_with dollar s = false ->
  no_char nl_char s = true -> nonspace_at (before ps n) = nonspace_at prev ->
  tok_at ps n = next_tok prev s.
Proof.
  intros ps n s after prev Hs Ha Hne Htk Hdl Hn Hp. unfold tok_at. rewrite Hs.
  rewrite (next_tok_after _ s after Hn Ha Hne Htk Hdl). apply next_tok_prev, Hp.
Qed.

(* A destination reading that never closes passes every byte ahead. *)
Local Lemma dest_close_app : forall a b esc depth i dst,
  dest_close esc depth i (a ++ b) = None ->
  exists ds, dfeed a (DS esc depth dst) = Some ds
             /\ dest_close (ds_esc ds) (ds_depth ds) (i + String.length a) b = None.
Proof.
  induction a as [|c a IH]; intros b esc depth i dst H.
  - exists (DS esc depth dst). rewrite Nat.add_0_r. split; [reflexivity|exact H].
  - cbn [append dest_close] in H. cbn [dfeed String.length]. unfold dstep.
    cbn [ds_esc ds_depth ds_dst]. rewrite <- Nat.add_succ_comm.
    destruct esc; [apply IH, H|].
    destruct (is_bslash c); [apply IH, H|].
    unfold pstep_byte.
    destruct (Ascii.eqb c lparen); [apply IH, H|].
    destruct (Ascii.eqb c rparen); [|apply IH, H].
    destruct depth as [|d]; [discriminate|apply IH, H].
Qed.

Definition never (ps : string) (n : nat) (w : wlayer) : Prop :=
  dest_close (ds_esc (wl_ds w)) (wl_depth w) n (sdrop n ps) = None.

Local Lemma layers_pass : forall ps n ws bytes r,
  Forall (never ps n) ws -> sdrop n ps = (bytes ++ r)%string ->
  Forall (fun w => dfeed bytes (wl_ds w) <> None) ws
  /\ Forall (never ps (n + String.length bytes)) (map (wl_after bytes) ws).
Proof.
  intros ps n ws bytes r F Hs.
  assert (G : forall w, In w ws ->
            exists ds, dfeed bytes (wl_ds w) = Some ds
              /\ dest_close (ds_esc ds) (ds_depth ds) (n + String.length bytes) r = None).
  { intros [k o [e d dst] o'] Hw. rewrite Forall_forall in F. specialize (F _ Hw).
    unfold never, wl_depth in F. cbn [wl_ds ds_esc ds_depth] in *. rewrite Hs in F.
    exact (dest_close_app bytes r e d n dst F). }
  split.
  - rewrite Forall_forall. intros w Hw E. destruct (G w Hw) as (ds & E1 & _). congruence.
  - rewrite Forall_map, Forall_forall. intros w Hw. destruct (G w Hw) as (ds & E1 & E2).
    unfold never, wl_after, wl_depth. cbn [wl_ds]. rewrite E1.
    rewrite (sdrop_app_tail ps n bytes r Hs). exact E2.
Qed.

Definition vinv (ps : string) (n : nat) (h : bool) (v : pview) : Prop :=
  pv_ok ps n v /\ tidy v /\ (h = true -> top_filled v).

(* The backslash a region's reading holds, which escapes the next byte. *)
Definition pend_esc (core : iscan) : bool :=
  match core with
  | IDest _ _ _ e _ _ _ _ => e
  | IReference _ _ _ e _ _ => e
  | _ => false
  end.

Definition with_esc (e : bool) (s : string) : string :=
  if e then String bslash s else s.

Definition linked (ps : string) (n : nat) (h : bool) (v : pview) (prev : option ascii)
  (core : iscan) : Prop :=
  match pv_mode v with
  | PMNormal =>
      h = false /\ exists txt o, core = IText false txt prev o /\ sim v txt o
  | PMRegion false kids d e label =>
      S d < n /\ clean kids /\ h = false
      /\ exists esc label' open cm,
           e = label_close esc n (sdrop n ps)
           /\ label = (label' ++ if esc then one bslash else EmptyString)%string
           /\ core = IReference (map mk kids) false open esc label' (oview cm v)
  | PMRegion true kids d e raw =>
      S d < n /\ h = false /\ exists open sh cm ds,
        dfeed raw (DS false 0 "") = Some ds
        /\ e = dest_close (ds_esc ds) (ds_depth ds) n (sdrop n ps) /\ e <> None
        /\ core = IDest (map mk kids) false open (ds_esc ds) (ds_depth ds) (ds_dst ds) sh
                   (oview cm v)
  | PMAtom x e =>
      h = false /\ n <= e /\ exists p d m body cl r txt0 prev0 o0,
        p < n /\ tok_at ps p = Some (TVerb d m body cl r, S e - p) /\ x = verb_node d r body
        /\ sim (pv_setmode PMNormal v) (txt0 ++ chars dollar (d - 2)) o0
        /\ core = iscan_str (substring p (n - p) ps) (IText false txt0 prev0 o0)
        /\ verb_state core (get n ps)
  end.

(* What a hard break leaves at the end of a line in text mode: the view
   with the break, and the scanner with it pending. *)
Definition pending (h : bool) (v : pview) (core : iscan) : Prop :=
  exists ws0 txt p o vb,
    h = true /\ is_blank ws0 = true /\ core = esc_pending ws0 txt p o
    /\ pv_mode vb = PMNormal /\ sim vb txt o /\ v = pv_add HardBreak (pv_trim vb).

(* What a verbatim leaves when it ends a line: the view with its node,
   and the scanner holding its closing run, or, where the paragraph ends,
   a state that finishes as the node. *)
Definition vpending (ps : string) (n : nat) (h : bool) (v : pview) (core : iscan) : Prop :=
  exists x v0 cm,
    h = false /\ pv_mode v0 = PMNormal /\ v = pv_add x v0 /\ (forall s, x <> Str s)
    /\ ((exists d m body, core = IVerb m m body (vkind_of d) (oview cm v0) /\ x = verb_node d None body)
        \/ (sdrop n ps = EmptyString
            /\ ifinish core = ifinish (IText false "" None (oview cm (pv_add x v0))))).

Definition linked_end (ps : string) (n : nat) (h : bool) (v : pview) (prev : option ascii)
  (core : iscan) : Prop :=
  linked ps n h v prev core \/ pending h v core \/ vpending ps n h v core.

(* A line's bytes, scanned from a linked state, end in one. *)
Definition scanned (ps : string) (n : nat) (h : bool) (v : pview) (ws : list wlayer)
  (core : iscan) (s : string) : Prop :=
  exists ws' core' prev' h' v',
    rres (iscan_str s (wrap ws core)) = wrap ws' core'
    /\ pruns ps n h v (n + String.length s) h' v'
    /\ vinv ps (n + String.length s) h' v'
    /\ Forall (never ps (n + String.length s)) ws'
    /\ linked_end ps (n + String.length s) h' v' prev' core'.

(* What the alphabet says of the rest of a line: outside a token, past
   the backslash the scanner holds; inside one, past whatever backslash
   the line's bytes leave, which the token reads as a byte. *)
Definition alpha_ok (v : pview) (core : iscan) (s : string) : Prop :=
  match pv_mode v with
  | PMAtom _ _ => exists e, over_alphabet (with_esc e s) = true
  | _ => over_alphabet (with_esc (pend_esc core) s) = true
  end.

Local Lemma alpha_of : forall v core s,
  over_alphabet (with_esc (pend_esc core) s) = true -> alpha_ok v core s.
Proof. intros v core s H. unfold alpha_ok. destruct (pv_mode v); [exact H|exact H|eexists; exact H]. Qed.

Definition scan_ih (ps after : string) (len : nat) : Prop :=
  forall s prev n h v ws core,
    String.length s <= len -> alpha_ok v core s ->
    note_ok prev core s -> sdrop n ps = (s ++ after)%string ->
    nonspace_at (before ps n) = nonspace_at prev ->
    vinv ps n h v -> Forall (never ps n) ws -> linked ps n h v prev core ->
    scanned ps n h v ws core s.

Local Lemma wrap_app : forall a b core, wrap (a ++ b) core = wrap a (wrap b core).
Proof. induction a as [|w a IH]; intros b core; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

(* One step of the simulation: a chunk of bytes, then the rest of the
   line. *)
Local Lemma scan_advance_gen : forall ps after len,
  scan_ih ps after len ->
  forall s n h v ws core bytes rest prev1 extra core1 h1 v1,
    String.length s <= S len -> sdrop n ps = (s ++ after)%string ->
    Forall (never ps n) ws ->
    s = (bytes ++ rest)%string -> bytes <> "" ->
    pruns ps n h v (n + String.length bytes) h1 v1 ->
    vinv ps (n + String.length bytes) h1 v1 ->
    nonspace_at (before ps (n + String.length bytes)) = nonspace_at prev1 ->
    alpha_ok v1 core1 rest -> note_ok prev1 core1 rest ->
    settles (iscan_str bytes core) (wrap extra core1) (get 0 rest) ->
    Forall (never ps (n + String.length bytes)) extra ->
    linked ps (n + String.length bytes) h1 v1 prev1 core1 ->
    scanned ps n h v ws core s.
Proof.
  intros ps after len IH s n h v ws core bytes rest prev1 extra core1 h1 v1
    Hl Hs Fn Es Hne Hr V Hp Ha Hnote Hset Fx L.
  subst s. pose proof Hs as Hs0. rewrite append_assoc in Hs.
  destruct (layers_pass ps n ws (bytes ++ rest) after Fn Hs0) as [Hopen _].
  destruct (layers_pass ps n ws bytes (rest ++ after) Fn Hs) as [_ Fn'].
  pose proof (sdrop_app_tail ps n bytes _ Hs) as Hs'.
  assert (Hlen : String.length rest <= len).
  { rewrite length_append in Hl. destruct bytes; [contradiction|]. cbn in Hl. lia. }
  destruct (IH rest prev1 (n + String.length bytes) h1 v1
              (map (wl_after bytes) ws ++ extra)%list core1 Hlen Ha Hnote Hs' Hp V)
    as (ws' & core' & prev' & h' & v' & E & R & V' & Fn'' & L').
  { apply Forall_app. split; [exact Fn'|exact Fx]. }
  { exact L. }
  exists ws', core', prev', h', v'.
  rewrite length_append, Nat.add_assoc.
  split; [|split; [exact (pruns_trans _ _ _ _ _ _ _ _ _ _ Hr R)|split; [exact V'|split; [exact Fn''|exact L']]]].
  rewrite <- E, wrap_app.
  apply (step_through bytes rest ws core (iscan_str bytes core) (wrap extra core1));
    [exact Hopen|reflexivity|exact Hset].
Qed.

Local Lemma scan_advance : forall ps after len,
  scan_ih ps after len ->
  forall s n h v ws core bytes rest prev1 extra core1 h1 v1,
    String.length s <= S len -> sdrop n ps = (s ++ after)%string ->
    Forall (never ps n) ws ->
    s = (bytes ++ rest)%string -> bytes <> "" ->
    pruns ps n h v (n + String.length bytes) h1 v1 ->
    vinv ps (n + String.length bytes) h1 v1 ->
    nonspace_at (before ps (n + String.length bytes)) = nonspace_at prev1 ->
    over_alphabet (with_esc (pend_esc core1) rest) = true -> note_ok prev1 core1 rest ->
    settles (iscan_str bytes core) (wrap extra core1) (get 0 rest) ->
    Forall (never ps (n + String.length bytes)) extra ->
    linked ps (n + String.length bytes) h1 v1 prev1 core1 ->
    scanned ps n h v ws core s.
Proof.
  intros ps after len IH s n h v ws core bytes rest prev1 extra core1 h1 v1
    Hl Hs Fn Es Hne Hr V Hp Ha.
  exact (scan_advance_gen ps after len IH s n h v ws core bytes rest prev1 extra core1 h1 v1
           Hl Hs Fn Es Hne Hr V Hp (alpha_of v1 core1 rest Ha)).
Qed.

Local Lemma linked_normal : forall ps n v prev txt o,
  pv_mode v = PMNormal -> sim v txt o ->
  linked ps n false v prev (IText false txt prev o).
Proof.
  intros ps n v prev txt o Em Hs. unfold linked. rewrite Em.
  split; [reflexivity|]. exists txt, o. auto.
Qed.

Local Lemma region_close_linked : forall ps n v cm x prev,
  (forall s, x <> Str s) ->
  linked ps n false (pv_add x (pv_setmode PMNormal v)) prev
    (IText false "" prev (oemit (mk x) (oview cm v))).
Proof.
  intros ps n v cm x prev Hx. apply linked_normal.
  - rewrite (proj2 (pv_add_live _ _)). reflexivity.
  - exists (pv_add x (pv_setmode PMNormal v)), cm.
    split; [exact (oemit_view cm x (pv_setmode PMNormal v) Hx)|].
    split; [apply top_add_nonstr, Hx|reflexivity].
Qed.

Local Lemma get_sdrop : forall ps n c r, sdrop n ps = String c r -> get n ps = Some c.
Proof.
  intros ps n. revert ps. induction n as [|n IH]; intros [|x ps] c r H;
    cbn [sdrop get] in *; try discriminate; [injection H as -> _; reflexivity|exact (IH ps c r H)].
Qed.

Local Lemma sdrop_succ : forall ps n c r, sdrop n ps = String c r -> sdrop (S n) ps = r.
Proof.
  intros ps n c r H. replace (S n) with (n + 1) by lia. rewrite <- sdrop_sdrop, H. reflexivity.
Qed.

(* A destination's decoded text, as its reading builds it. *)
Local Lemma dfeed_text : forall raw esc depth dst ds,
  dfeed raw (DS esc depth dst) = Some ds -> ds_dst ds = (dst ++ dest_text esc raw)%string.
Proof.
  induction raw as [|c raw IH]; intros esc depth dst ds H.
  - injection H as <-. cbn. rewrite append_empty_r. reflexivity.
  - cbn [dfeed] in H. unfold dstep in H. cbn [ds_esc ds_depth ds_dst] in H.
    cbn [dest_text]. destruct esc.
    + rewrite (IH _ _ _ _ H), append_assoc. reflexivity.
    + destruct (is_bslash c); [exact (IH _ _ _ _ H)|].
      destruct (pstep_byte c depth); [|discriminate].
      rewrite (IH _ _ _ _ H), append_assoc. reflexivity.
Qed.

Local Lemma dest_close_step : forall c r esc depth dst ds i,
  dstep c (DS esc depth dst) = Some ds ->
  dest_close esc depth i (String c r) = dest_close (ds_esc ds) (ds_depth ds) (S i) r.
Proof.
  intros c r esc depth dst ds i H. unfold dstep in H. cbn [ds_esc ds_depth ds_dst] in H.
  cbn [dest_close]. destruct esc; [injection H as <-; reflexivity|].
  destruct (is_bslash c); [injection H as <-; reflexivity|].
  unfold pstep_byte in H.
  destruct (Ascii.eqb c lparen); [injection H as <-; reflexivity|].
  destruct (Ascii.eqb c rparen); [|injection H as <-; reflexivity].
  destruct depth; [discriminate|injection H as <-; reflexivity].
Qed.

Local Lemma dest_close_none : forall c r esc depth dst i,
  dstep c (DS esc depth dst) = None -> dest_close esc depth i (String c r) = Some i.
Proof.
  intros c r esc depth dst i H. unfold dstep in H. cbn [ds_esc ds_depth ds_dst] in H.
  cbn [dest_close]. destruct esc; [discriminate|].
  destruct (is_bslash c); [discriminate|].
  unfold pstep_byte in H.
  destruct (Ascii.eqb c lparen); [discriminate|].
  destruct (Ascii.eqb c rparen); [|discriminate].
  destruct depth; [reflexivity|discriminate].
Qed.

Local Lemma dstep_none : forall c esc depth dst,
  dstep c (DS esc depth dst) = None -> c = rparen /\ esc = false /\ depth = 0.
Proof.
  intros c esc depth dst H. unfold dstep in H. cbn [ds_esc ds_depth ds_dst] in H.
  destruct esc; [discriminate|]. destruct (is_bslash c); [discriminate|].
  unfold pstep_byte in H.
  destruct (Ascii.eqb c lparen); [discriminate|].
  destruct (Ascii.eqb c rparen) eqn:E; [|discriminate].
  apply Ascii.eqb_eq in E. destruct depth; [auto|discriminate].
Qed.

(* A byte of a region, through the region's reading. *)
Local Lemma scan_region : forall ps after len, scan_ih ps after len ->
  forall c s' prev n h v ws core,
    String.length (String c s') <= S len ->
    over_alphabet (with_esc (pend_esc core) (String c s')) = true ->
    sdrop n ps = (String c s' ++ after)%string ->
    vinv ps n h v -> Forall (never ps n) ws -> linked ps n h v prev core ->
    pv_mode v <> PMNormal -> (forall x e, pv_mode v <> PMAtom x e) ->
    scanned ps n h v ws core (String c s').
Proof.
  intros ps after len IH c s' prev n h v ws core Hl Ha Hs V Fn L Em Ea.
  pose proof (get_sdrop ps n c _ Hs) as Hg.
  pose proof (sdrop_succ ps n c _ Hs) as Hs1.
  change ((fix append (s1 s2 : string) {struct s1} : string :=
             match s1 with "" => s2 | String c s1' => String c (append s1' s2) end) s' after)
    with (s' ++ after)%string in Hs1.
  pose proof (before_sdrop ps n c _ Hs) as Hb.
  pose proof V as (Ok & Ti & _).
  assert (U : punit ps n h v = Some (S n, false, pbyte n c v)).
  { unfold punit. destruct (pv_mode v); [contradiction| |]; rewrite Hg; reflexivity. }
  assert (V1 : vinv ps (S n) false (pbyte n c v)).
  { split; [apply pv_ok_byte; assumption|]. split; [apply pbyte_tidy, Ti|]. discriminate. }
  assert (A : forall core1,
            over_alphabet (with_esc (pend_esc core1) s') = true -> note_ok (Some c) core1 s' ->
            settles (istep c core) core1 (get 0 s') ->
            linked ps (S n) false (pbyte n c v) (Some c) core1 ->
            scanned ps n h v ws core (String c s')).
  { intros core1 A1 N1 S1 L1.
    apply (scan_advance ps after len IH (String c s') n h v ws core (one c) s' (Some c) [] core1
             false (pbyte n c v)); cbn [String.length one]; try rewrite Nat.add_1_r;
      first [assumption | reflexivity | discriminate | exact (pruns_one _ _ _ _ _ _ _ U)
            | (rewrite Hb; reflexivity) | constructor | (cbn [iscan_str wrap]; exact S1)]. }
  unfold linked in L. unfold pbyte in A.
  rewrite Hs in L. change (String c s' ++ after)%string with (String c (s' ++ after)) in L.
  destruct (pv_mode v) as [|[|] kids d e txt|x e] eqn:Em'; [contradiction| | |];
    [| |destruct (Ea x e eq_refl)].
  - (* a destination *)
    destruct L as (Hd & _ & open & sh & cm & [e0 dp dst] & Hds & He & Hne & ->).
    cbn [ds_esc ds_depth ds_dst pend_esc] in *.
    replace (n =? S d)%nat with false in A by (symmetry; apply Nat.eqb_neq; lia).
    destruct (dstep c (DS e0 dp dst)) as [ds'|] eqn:Hst.
    + rewrite (dest_close_step c (s' ++ after) e0 dp dst ds' n Hst) in He.
      assert (Hen : match e with Some e' => (n =? e')%nat | None => false end = false).
      { destruct e as [e'|]; [|reflexivity]. symmetry in He. apply dest_close_bound in He.
        apply Nat.eqb_neq. lia. }
      rewrite Hen in A.
      apply (A (IDest (map mk kids) false open (ds_esc ds') (ds_depth ds') (ds_dst ds')
                  (istep c sh) (oview cm v))).
      * cbn [pend_esc]. unfold dstep in Hst. cbn [ds_esc ds_depth ds_dst] in Hst.
        destruct e0; [injection Hst as <-; cbn [with_esc over_alphabet] in Ha |- *;
                      apply andb_true_iff in Ha as [_ Ha]; exact Ha|].
        destruct (is_bslash c) eqn:Eb.
        { injection Hst as <-. unfold is_bslash in Eb. apply Ascii.eqb_eq in Eb. subst c.
          cbn [with_esc ds_esc] in *. exact Ha. }
        destruct (pstep_byte c dp); [|discriminate]. injection Hst as <-.
        exact (proj2 (proj2 (over_alphabet_cons c s' Eb Ha))).
      * right. intros t p o E. discriminate E.
      * rewrite (istep_idest c _ _ _ _ _ _ _ ds' Hst). apply settles_refl.
      * unfold linked. cbn [pv_setmode pv_mode]. split; [lia|]. split; [reflexivity|].
        exists open, (istep c sh), cm, ds'. split; [|split; [|split]].
        -- rewrite dfeed_app, Hds. cbn [one dfeed]. rewrite Hst. reflexivity.
        -- rewrite Hs1. exact He.
        -- exact Hne.
        -- reflexivity.
    + (* the `)` that closes it *)
      destruct (dstep_none c e0 dp dst Hst) as (-> & -> & ->).
      rewrite (dest_close_none rparen (s' ++ after) false 0 dst n Hst) in He. subst e.
      rewrite Nat.eqb_refl in A.
      pose proof (over_alphabet_cons rparen s' eq_refl Ha) as (_ & Hf & Hs').
      apply (A (IText false "" (Some rparen)
                  (oemit (mk (region_node true (map mk kids) (dest_text false txt))) (oview cm v)))).
      * exact Hs'.
      * left. exact Hf.
      * pose proof (dfeed_text txt false 0 "" _ Hds) as Ed. cbn [ds_dst append] in Ed. subst dst.
        unfold region_node. rewrite no_nl_drop. apply settles_refl.
      * apply region_close_linked, region_node_nonstr.
  - (* a reference label *)
    destruct L as (Hd & Hk & _ & esc & label' & open & cm & He & Hlab & ->).
    cbn [pend_esc] in Ha.
    replace (n =? S d)%nat with false in A by (symmetry; apply Nat.eqb_neq; lia).
    assert (Stay : forall esc' lab',
              e = label_close esc' (S n) (s' ++ after) ->
              (txt ++ one c)%string = (lab' ++ if esc' then one bslash else EmptyString)%string ->
              over_alphabet (with_esc esc' s') = true ->
              settles (istep c (IReference (map mk kids) false open esc label' (oview cm v)))
                (IReference (map mk kids) false open esc' lab' (oview cm v)) (get 0 s') ->
              scanned ps n h v ws (IReference (map mk kids) false open esc label' (oview cm v))
                (String c s')).
    { intros esc' lab' He' Ht Ha' Hset.
      assert (Hen : match e with Some e' => (n =? e')%nat | None => false end = false).
      { destruct e as [e'|]; [|reflexivity]. symmetry in He'. apply label_close_bound in He'.
        apply Nat.eqb_neq. lia. }
      rewrite Hen in A. apply (A (IReference (map mk kids) false open esc' lab' (oview cm v)));
        [exact Ha'|right; intros t p o E; discriminate E|exact Hset|].
      unfold linked. cbn [pv_setmode pv_mode]. split; [lia|]. split; [exact Hk|].
      split; [reflexivity|]. exists esc', lab', open, cm.
      split; [rewrite Hs1; exact He'|]. split; [exact Ht|reflexivity]. }
    destruct esc.
    + (* the escaped byte *)
      cbn [with_esc over_alphabet] in Ha. apply andb_true_iff in Ha as [_ Ha].
      apply (Stay false (label' ++ String bslash (one c))%string).
      * exact He.
      * subst txt. rewrite !append_assoc, append_empty_r. reflexivity.
      * exact Ha.
      * apply settles_refl.
    + cbn [with_esc] in Ha. rewrite append_empty_r in Hlab. subst txt.
      destruct (is_bslash c) eqn:Eb.
      * unfold is_bslash in Eb. apply Ascii.eqb_eq in Eb. subst c.
        apply (Stay true label'); [exact He|reflexivity|exact Ha|].
        unfold istep. cbn [istep_at]. apply settles_refl.
      * pose proof (over_alphabet_cons c s' Eb Ha) as (_ & Hf & Hs').
        destruct (Ascii.eqb c rbrack) eqn:Er.
        -- (* the `]` that ends it *)
           apply Ascii.eqb_eq in Er. subst c.
           cbn [label_close is_bslash] in He. rewrite Ascii.eqb_refl in He. subst e.
           change (is_bslash rbrack) with false in A. cbn iota in A.
           rewrite Nat.eqb_refl in A.
           apply (A (IText false "" (Some rbrack)
                       (oemit (mk (region_node false (map mk kids) label')) (oview cm v)))).
           ++ exact Hs'.
           ++ left. exact Hf.
           ++ apply settles_refl.
           ++ apply region_close_linked, region_node_nonstr.
        -- apply (Stay false (label' ++ one c)%string).
           ++ rewrite He. cbn [label_close]. rewrite Eb, Er. reflexivity.
           ++ rewrite append_empty_r. reflexivity.
           ++ exact Hs'.
           ++ unfold istep. cbn [istep_at]. rewrite Eb, Er. apply settles_refl.
Qed.

Local Lemma alpha_tail : forall e0 c s,
  over_alphabet (with_esc e0 (String c s)) = true ->
  over_alphabet (with_esc (negb e0 && is_bslash c) s) = true.
Proof.
  intros [|] c s H; cbn [with_esc negb andb] in *.
  - cbn [over_alphabet] in H. change (is_bslash bslash) with true in H. cbn iota in H.
    apply andb_true_iff in H as [_ H]. exact H.
  - destruct (is_bslash c) eqn:Eb; cbn [with_esc].
    + unfold is_bslash in Eb. apply Ascii.eqb_eq in Eb. subst c. exact H.
    + exact (proj2 (proj2 (over_alphabet_cons c s Eb H))).
Qed.

Local Lemma alpha_tick : forall e0 s,
  over_alphabet (with_esc e0 (String tick s)) = true -> starts_with lbrace s = true ->
  raw_ahead s = true.
Proof.
  intros [|] s H Hb; cbn [with_esc over_alphabet] in H.
  - change (is_bslash bslash) with true in H. cbn iota in H.
    apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
    change (is_tick tick) with true in H. rewrite Hb in H.
    destruct (raw_ahead s); [reflexivity|discriminate].
  - change (is_bslash tick) with false in H. cbn iota in H.
    apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
    unfold follow_ok in H. apply andb_true_iff in H as [_ H].
    change (is_tick tick) with true in H. rewrite Hb in H.
    destruct (raw_ahead s); [reflexivity|discriminate].
Qed.

(* A newline inside a verbatim is one of its bytes. *)
Local Lemma ibreak_verb : forall X, verb_state X (Some nl_char) ->
  ibreak X = istep nl_char X /\ pend_esc (ibreak X) = false.
Proof.
  intros [] H; cbn [verb_state] in H; try contradiction;
    try (destruct H as [E|E]; discriminate E);
    try (destruct H as (c & E & Hc & _); injection E as <-; contradiction).
  - split; reflexivity.
  - destruct (Nat.eqb run n) eqn:E.
    + apply Nat.eqb_eq in E. destruct (H E) as [E'|E']; discriminate E'.
    + unfold ibreak, istep. cbn [ibreak_at istep_at iresolve ibreak_flat]. rewrite E.
      split; reflexivity.
Qed.

Local Lemma verb_nl_not_text : forall X t0 p0 o0,
  verb_state X (Some nl_char) -> istep nl_char X <> IText false t0 p0 o0.
Proof.
  intros X t0 p0 o0 H E. destruct X; cbn [verb_state] in H; try contradiction;
    try (destruct H as [E'|E']; discriminate E');
    try (destruct H as (c & E' & Hc & _); injection E' as <-; contradiction).
  - discriminate E.
  - unfold istep in E. cbn [istep_at] in E. destruct (Nat.eqb run n) eqn:Er.
    + apply Nat.eqb_eq in Er. destruct (H Er) as [E'|E']; discriminate E'.
    + discriminate E.
Qed.

Local Lemma ilead_not_verb : forall c t p o n r t' vk o', ilead c t p o <> IVerb n r t' vk o'.
Proof.
  intros c t p o n r t' vk o' E. unfold ilead in E.
  repeat match goal with
  | H : context [if ?b then _ else _] |- _ => destruct b
  | H : context [match ?x with Some _ => _ | None => _ end] |- _ => destruct x
  end; try discriminate E;
  repeat match goal with q : _ * _ |- _ => destruct q end; discriminate E.
Qed.

(* A verbatim's closing run ends in a backtick. *)
Local Lemma verb_last_tick : forall X c m t vk o,
  verb_state X (Some c) -> istep c X = IVerb m m t vk o -> m <> 0 -> c = tick.
Proof.
  intros X c m t vk o H E Hm. destruct (is_tick c) eqn:Ec.
  { unfold is_tick in Ec. apply Ascii.eqb_eq in Ec. exact Ec. }
  exfalso. destruct X; cbn [verb_state] in H; try contradiction.
  all: try (destruct H as [Ht|Ht]; injection Ht as ->; [discriminate Ec|];
            unfold istep in E; cbn [istep_at] in E; unfold idollar_step in E;
            rewrite Ascii.eqb_refl in E; destruct two; discriminate E).
  - unfold istep in E; cbn [istep_at] in E; rewrite Ec in E. injection E as _ E. lia.
  - unfold istep in E; cbn [istep_at] in E; rewrite Ec in E.
    destruct (Nat.eqb run n) eqn:Er.
    + apply Nat.eqb_eq in Er. destruct (H Er) as [Ht|Ht]; injection Ht as ->; [discriminate Ec|].
      repeat match goal with
      | H : context [if ?b then _ else _] |- _ => destruct b
      | H : context [match ?x with _ => _ end] |- _ => destruct x
      end; try discriminate E; exact (ilead_not_verb _ _ _ _ _ _ _ _ _ E).
    + injection E as _ E. lia.
  - destruct H as (c' & Hc & _ & He). injection Hc as <-.
    destruct spec as [|s0 spec].
    + rewrite (He eq_refl) in E. discriminate E.
    + unfold istep in E; cbn [istep_at] in E; unfold iraw_step_at in E.
      cbn [tnonempty] in E. change (nonempty_str (String s0 spec)) with true in E.
      repeat match goal with
      | H : context [if ?b then _ else _] |- _ => destruct b
      end; try discriminate E; exact (ilead_not_verb _ _ _ _ _ _ _ _ _ E).
Qed.

(* After a closing run, a byte that does not continue it settles the
   scanner into text with the node out.  A `{` continues a verbatim's,
   as a raw spec, but not math's. *)
Local Lemma verb_close_settles : forall d m body o c,
  is_tick c = false -> (Ascii.eqb c lbrace = true -> d <> 0) ->
  (Ascii.eqb c dollar = true -> dollar_math_enabled = false) ->
  istep c (IVerb m m body (vkind_of d) o)
  = istep c (IText false "" (Some tick) (oemit (mk (verb_node d None body)) o)).
Proof.
  intros d m body o c Hc Hb Hd. unfold istep. cbn [istep_at]. rewrite Hc, Nat.eqb_refl.
  destruct d as [|[|d]]; cbn [vkind_of].
  - destruct (Ascii.eqb c lbrace) eqn:E; [destruct (Hb eq_refl eq_refl)|]. reflexivity.
  - destruct (Ascii.eqb c dollar) eqn:E; [rewrite (Hd eq_refl)|]; reflexivity.
  - cbn [vkind_verb]. rewrite andb_false_r. reflexivity.
Qed.

(* A raw spec reads the same from the line as from the paragraph. *)
Local Lemma raw_spec_app : forall s after, line_end after -> raw_spec (s ++ after) = raw_spec s.
Proof.
  intros s after Ha.
  assert (F : forall r, fmt_go (r ++ after) = fmt_go r).
  { induction r as [|x r IH]; [destruct Ha as [->|[r' ->]]; reflexivity|].
    cbn [append fmt_go]. rewrite IH. reflexivity. }
  destruct s as [|b [|e r]].
  - destruct Ha as [->|[r' ->]]; [reflexivity|]. destruct r'; reflexivity.
  - destruct Ha as [->|[r' ->]]; [reflexivity|]. cbn [append raw_spec].
    change (Ascii.eqb nl_char eqchar) with false. rewrite andb_false_r. reflexivity.
  - cbn [append raw_spec]. rewrite F. reflexivity.
Qed.

Local Lemma alpha_follow_tick : forall e0 s,
  over_alphabet (with_esc e0 (String tick s)) = true -> follow_ok tick s = true.
Proof.
  intros [|] s H; cbn [with_esc] in H.
  - cbn [over_alphabet] in H. change (is_bslash bslash) with true in H. cbn iota in H.
    apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
    unfold follow_ok. change (is_tick tick) with true in H |- *. exact H.
  - exact (proj1 (proj2 (over_alphabet_cons tick s eq_refl H))).
Qed.

(* A byte of a verbatim the view is inside. *)
Local Lemma scan_atom : forall ps after len, scan_ih ps after len ->
  line_end after ->
  forall c s' prev n h v ws core x e,
    String.length (String c s') <= S len ->
    (exists e0, over_alphabet (with_esc e0 (String c s')) = true) ->
    sdrop n ps = (String c s' ++ after)%string ->
    vinv ps n h v -> Forall (never ps n) ws -> linked ps n h v prev core ->
    pv_mode v = PMAtom x e ->
    scanned ps n h v ws core (String c s').
Proof.
  intros ps after len IH Hae c s' prev n h v ws core x e Hl [e0 Ha] Hs V Fn L Em.
  pose proof (get_sdrop ps n c _ Hs) as Hg.
  pose proof (sdrop_succ ps n c _ Hs) as Hs1.
  change ((fix append (s1 s2 : string) {struct s1} : string :=
             match s1 with "" => s2 | String c s1' => String c (append s1' s2) end) s' after)
    with (s' ++ after)%string in Hs1.
  pose proof (before_sdrop ps n c _ Hs) as Hb.
  pose proof V as (Ok & Ti & _).
  assert (U : punit ps n h v = Some (S n, false, pbyte n c v))
    by (unfold punit; rewrite Em, Hg; reflexivity).
  assert (V1 : vinv ps (S n) false (pbyte n c v)).
  { split; [apply pv_ok_byte; [exact Ok|rewrite Em; discriminate]|].
    split; [apply pbyte_tidy, Ti|]. discriminate. }
  assert (A : forall core1,
            alpha_ok (pbyte n c v) core1 s' -> note_ok (Some c) core1 s' ->
            settles (istep c core) core1 (get 0 s') ->
            linked ps (S n) false (pbyte n c v) (Some c) core1 ->
            scanned ps n h v ws core (String c s')).
  { intros core1 A1 N1 S1 L1.
    apply (scan_advance_gen ps after len IH (String c s') n h v ws core (one c) s' (Some c) []
             core1 false (pbyte n c v)); cbn [String.length one]; try rewrite Nat.add_1_r;
      first [assumption | reflexivity | discriminate | exact (pruns_one _ _ _ _ _ _ _ U)
            | (rewrite Hb; reflexivity) | constructor | (cbn [iscan_str wrap]; exact S1)]. }
  assert (End : s' = EmptyString ->
            vpending ps (S n) false (pbyte n c v) (rres (istep c core)) ->
            scanned ps n h v ws core (String c s')).
  { intros -> VP. destruct (layers_pass ps n ws (one c) after Fn Hs) as [Fo Fn'].
    exists (map (wl_after (one c)) ws), (rres (istep c core)), (Some c), false, (pbyte n c v).
    cbn [String.length] in *. rewrite Nat.add_1_r in *.
    split; [|split; [exact (pruns_one _ _ _ _ _ _ _ U)|split; [exact V1|split; [exact Fn'|]]]].
    - rewrite <- rres_wrap.
      exact (step_through (one c) "" ws core (istep c core) (istep c core) Fo eq_refl
               (settles_refl _ _)).
    - right. right. exact VP. }
  unfold linked in L. rewrite Em in L.
  destruct L as (-> & Hne & p & pre & m & body & cl & rw & txt0 & prev0 & o0 & Hp & Ht & -> & Hsim
                 & -> & Hvs).
  destruct (verb_tok_scan ps p pre m body cl rw (S e - p) txt0 prev0 o0 Ht) as (T1 & T2 & Traw & T3).
  pose proof (tok_at_len ps p _ _ Ht) as [_ Hle].
  pose proof (tok_verb_width ps p pre m body cl rw _ Ht) as Hm.
  set (X0 := IText false txt0 prev0 o0) in *.
  assert (Step : istep c (iscan_str (substring p (n - p) ps) X0)
                 = iscan_str (substring p (S n - p) ps) X0).
  { replace (S n - p) with (S (n - p)) by lia.
    rewrite (substring_snoc ps p (n - p) c) by (replace (p + (n - p)) with n by lia; exact Hg).
    rewrite iscan_str_app. reflexivity. }
  rewrite Hg in Hvs.
  destruct (Nat.eqb n e) eqn:Ene.
  2: { (* inside *)
    apply Nat.eqb_neq in Ene.
    assert (VS : verb_state (istep c (iscan_str (substring p (n - p) ps) X0)) (get (S n) ps)).
    { rewrite Step. replace (S n) with (p + (S n - p)) at 2 by lia. apply T1. lia. }
    assert (Pb : pbyte n c v = v)
      by (unfold pbyte; rewrite Em; apply Nat.eqb_neq in Ene; rewrite Ene; reflexivity).
    apply (A (istep c (iscan_str (substring p (n - p) ps) X0))); rewrite ?Pb.
    - unfold alpha_ok. rewrite Em. eexists. exact (alpha_tail e0 c s' Ha).
    - right. intros t q o E. rewrite E in VS. exact (False_ind _ VS).
    - apply settles_refl.
    - unfold linked. rewrite Em. split; [reflexivity|]. split; [lia|].
      exists p, pre, m, body, cl, rw, txt0, prev0, o0. split; [lia|]. split; [exact Ht|].
      split; [reflexivity|]. split; [exact Hsim|]. split; [exact Step|exact VS]. }
  (* the last byte *)
  apply Nat.eqb_eq in Ene. subst e.
  destruct Hsim as (v0 & cm & Eo & Ht0 & Ev).
  set (vN := pv_setmode PMNormal v) in *.
  assert (Fl : flush_text (txt0 ++ chars dollar (pre - 2)) o0 = oview cm vN)
    by (rewrite Eo, Ev; apply flush_view, Ht0).
  assert (Pb : pbyte n c v = pv_add (verb_node pre rw body) vN)
    by (unfold pbyte; rewrite Em, Nat.eqb_refl; reflexivity).
  assert (EmN : pv_mode vN = PMNormal) by (unfold vN; destruct v; reflexivity).
  destruct rw as [f|].
  { (* the `}` of a raw spec: the raw node, and text after it *)
    destruct (Traw f eq_refl) as (-> & -> & Gr & Ec).
    replace (p + pred (S n - p)) with n in Gr by lia. rewrite Hg in Gr. injection Gr as ->.
    cbn [Nat.sub chars] in Fl. rewrite append_empty_r in Fl. rewrite Ec, Fl in Step.
    apply (A (IText false "" (Some rbrace) (oemit (mk (RawInline f (trim_verb body))) (oview cm vN)))).
    - unfold alpha_ok. rewrite Pb, (proj2 (pv_add_live _ _)), EmN. cbn [pend_esc with_esc].
      pose proof (alpha_tail e0 rbrace s' Ha) as H. change (is_bslash rbrace) with false in H.
      rewrite andb_false_r in H. exact H.
    - left. reflexivity.
    - rewrite Step. apply settles_refl.
    - rewrite Pb. apply linked_normal; [rewrite (proj2 (pv_add_live _ _)); exact EmN|].
      exists (pv_add (verb_node 0 (Some f) body) vN), cm.
      split; [apply oemit_view; intros s0; discriminate|].
      split; [apply top_add_nonstr; intros s0; discriminate|reflexivity]. }
  destruct cl.
  - destruct (T2 eq_refl eq_refl) as (Ec & Stop & Nr).
    rewrite Ec, Fl in Step.
    destruct s' as [|d r].
    + (* at the end of the line *)
      apply End; [reflexivity|]. rewrite Step, Pb.
      exists (verb_node pre None body), vN, cm.
      split; [reflexivity|]. split; [exact EmN|]. split; [reflexivity|].
      split; [intros s0; apply verb_node_nonstr|]. left. exists pre, m, body. split; reflexivity.
    + (* before a byte of the line that does not continue the verbatim *)
      assert (Ect : c = tick) by exact (verb_last_tick _ c _ _ _ _ Hvs Step Hm).
      subst c.
      assert (Hd : is_tick d = false).
      { apply Stop. replace (p + (S n - p)) with (S n) by lia. exact (get_sdrop ps (S n) d _ Hs1). }
      pose proof (alpha_follow_tick e0 _ Ha) as Hf'.
      assert (Hbr : Ascii.eqb d lbrace = true -> pre <> 0).
      { intros Edb Hp0. subst pre. unfold follow_ok in Hf'.
        apply andb_true_iff in Hf' as [_ H4]. change (is_tick tick) with true in H4.
        cbn [starts_with] in H4. rewrite Edb in H4. cbn [andb] in H4.
        destruct (raw_ahead (String d r)) eqn:Ra; [|discriminate H4].
        unfold raw_ahead in Ra. apply andb_true_iff in Ra as [Eraw Rs].
        pose proof (Nr eq_refl Eraw) as N0. replace (p + (S n - p)) with (S n) in N0 by lia.
        rewrite Hs1, (raw_spec_app _ _ Hae) in N0. rewrite N0 in Rs. discriminate Rs. }
      assert (Hdm : Ascii.eqb d dollar = true -> dollar_math_enabled = false).
      { intros Edl. pose proof (alpha_tail e0 tick _ Ha) as H. rewrite andb_false_r in H.
        cbn [with_esc] in H. apply Ascii.eqb_eq in Edl. subst d.
        apply (over_alphabet_cons dollar r eq_refl) in H as (Hin & _).
        unfold in_alphabet in Hin. destruct dollar_math_enabled; [|reflexivity].
        exfalso. revert Hin. vm_compute. destruct (dstyle_of dollar); discriminate. }
      apply (A (IText false "" (Some tick) (oemit (mk (verb_node pre None body)) (oview cm vN)))).
      * unfold alpha_ok. rewrite Pb, (proj2 (pv_add_live _ _)), EmN. cbn [pend_esc with_esc].
        pose proof (alpha_tail e0 tick _ Ha) as H. rewrite andb_false_r in H. exact H.
      * left. exact Hf'.
      * cbn [get settles]. rewrite Step. apply verb_close_settles; [exact Hd|exact Hbr|exact Hdm].
      * rewrite Pb. apply linked_normal; [rewrite (proj2 (pv_add_live _ _)); exact EmN|].
        exists (pv_add (verb_node pre None body) vN), cm.
        split; [apply oemit_view; apply verb_node_nonstr|].
        split; [apply top_add_nonstr; apply verb_node_nonstr|reflexivity].
  - (* the paragraph ends unclosed *)
    destruct (T3 eq_refl) as (_ & Elen & Efin).
    assert (Hlen : String.length (sdrop n ps) = 1) by (rewrite sdrop_length; lia).
    rewrite Hs in Hlen. cbn [append String.length] in Hlen. rewrite length_append in Hlen.
    destruct s' as [|d r]; [|cbn in Hlen; lia].
    destruct after as [|a af]; [|cbn in Hlen; lia].
    apply End; [reflexivity|]. rewrite Pb.
    exists (verb_node pre None body), vN, cm.
    split; [reflexivity|]. split; [exact EmN|]. split; [reflexivity|].
    split; [intros s0; apply verb_node_nonstr|]. right. split; [exact Hs1|].
    rewrite ifinish_rres, Step, Efin, Fl, (oemit_view cm _ vN) by (intros s0; apply verb_node_nonstr).
    reflexivity.
Qed.

Local Lemma before_chunk : forall ps n a b,
  sdrop n ps = (a ++ b)%string -> before ps (n + String.length a) = str_last a (before ps n).
Proof.
  intros ps n a. revert n. induction a as [|c a IH]; intros n b H.
  - rewrite Nat.add_0_r. reflexivity.
  - cbn [String.length str_last]. rewrite <- Nat.add_succ_comm.
    rewrite (IH (S n) b); [rewrite (before_sdrop ps n c _ H); reflexivity|].
    exact (sdrop_succ ps n c _ H).
Qed.

Local Lemma top_filled_add : forall x v, top_filled (pv_add x v).
Proof.
  intros x [[|[p k c|d c] rest] out md]; unfold top_filled; cbn [pv_add pv_stk pv_mode fset fcontent];
    destruct md; try exact Logic.I; apply xsnoc_nonempty.
Qed.

Local Lemma vinv_step : forall ps n h t l v,
  vinv ps n h v -> pv_mode v = PMNormal -> tok_at ps n = Some (t, l) ->
  (forall k mr op cl, t = TDelim k mr op cl -> self_row k = true) ->
  vinv ps (n + l) (is_hard t) (pstep ps n h t v).
Proof.
  intros ps n h t l v (Ok & Ti & Hh) Em Ht Hb.
  assert (H0 : t <> TDollars 0)
    by (intros ->; pose proof (tok_at_dollars _ _ _ _ Ht) as ->;
        pose proof (tok_at_len _ _ _ _ Ht); lia).
  split; [|split; [apply pstep_tidy; [exact H0|exact Em|exact Ti]|]].
  - apply pv_ok_step; [exact Ok|exact Em|exact Ht|exact Hb|]. intros _ H. exact (Hh H).
  - destruct t; try discriminate. intros _. apply top_filled_add.
Qed.

Local Lemma punit_tok : forall ps n h t l v,
  pv_mode v = PMNormal -> tok_at ps n = Some (t, l) ->
  pv_mode (pstep ps n h t v) = PMNormal \/ l = 1 ->
  punit ps n h v = Some (n + l, is_hard t, pstep ps n h t v).
Proof.
  intros ps n h t l v Em Ht Hm. unfold punit. rewrite Em, Ht. cbv zeta.
  destruct Hm as [Hm| ->]; [rewrite Hm; reflexivity|].
  destruct (pv_mode (pstep ps n h t v)); rewrite ?Nat.add_1_r; reflexivity.
Qed.

(* A chunk that is one token of the chain, in text mode. *)
Local Lemma scan_tok : forall ps after len, scan_ih ps after len ->
  forall s n h v ws core t l rest prev1 core1,
    String.length s <= S len -> sdrop n ps = (s ++ after)%string -> Forall (never ps n) ws ->
    vinv ps n h v -> pv_mode v = PMNormal -> tok_at ps n = Some (t, l) ->
    (forall k mr op cl, t = TDelim k mr op cl -> self_row k = true) ->
    s = (tok_text t ++ rest)%string -> l = String.length (tok_text t) ->
    nonspace_at (str_last (tok_text t) (before ps n)) = nonspace_at prev1 ->
    over_alphabet (with_esc (pend_esc core1) rest) = true -> note_ok prev1 core1 rest ->
    settles (iscan_str (tok_text t) core) core1 (get 0 rest) ->
    linked ps (n + l) (is_hard t) (pstep ps n h t v) prev1 core1 ->
    pv_mode (pstep ps n h t v) = PMNormal \/ l = 1 ->
    scanned ps n h v ws core s.
Proof.
  intros ps after len IH s n h v ws core t l rest prev1 core1 Hl Hs Fn V Em Ht Hk Es El Hp Ha Hn Hset L
    Hm.
  pose proof Hs as Hs0. rewrite Es, append_assoc in Hs0.
  apply (scan_advance ps after len IH s n h v ws core (tok_text t) rest prev1 [] core1
           (is_hard t) (pstep ps n h t v) Hl Hs Fn Es).
  - intros E. rewrite E in El. pose proof (tok_at_len ps n t l Ht). cbn in El. lia.
  - rewrite <- El. exact (pruns_one _ _ _ _ _ _ _ (punit_tok ps n h t l v Em Ht Hm)).
  - rewrite <- El. exact (vinv_step ps n h t l v V Em Ht Hk).
  - rewrite (before_chunk ps n _ _ Hs0). exact Hp.
  - exact Ha.
  - exact Hn.
  - exact Hset.
  - constructor.
  - rewrite <- El. exact L.
Qed.

Local Lemma scan_esc : forall ps after len, scan_ih ps after len -> line_end after ->
  forall s' prev n h v ws core,
    String.length (String bslash s') <= S len -> over_alphabet (String bslash s') = true ->
    sdrop n ps = (String bslash s' ++ after)%string ->
    nonspace_at (before ps n) = nonspace_at prev ->
    vinv ps n h v -> Forall (never ps n) ws -> linked ps n h v prev core ->
    pv_mode v = PMNormal ->
    scanned ps n h v ws core (String bslash s').
Proof.
  intros ps after len IH Hae s' prev n h v ws core Hl Ha Hs Hpv V Fn L Em.
  unfold linked in L. rewrite Em in L. destruct L as (-> & txt & o & -> & Hsim).
  pose proof (alphabet_no_nl _ Ha) as Hnl. cbn [no_char] in Hnl. apply andb_true_iff in Hnl as [_ Hnl].
  assert (Ht0 : tok_at ps n = next_tok prev (String bslash s'))
    by (apply (tok_at_line ps n _ after prev Hs Hae); [discriminate|reflexivity|reflexivity| |exact Hpv];
        cbn [no_char]; rewrite Hnl; reflexivity).
  rewrite (nt_bs prev s' Hnl) in Ht0.
  pose proof (scan_tok ps after len IH (String bslash s') n false v ws (IText false txt prev o))
    as ST.
  destruct (is_blank s') eqn:Bl.
  { (* a hard break: the rest of the line *)
    destruct (layers_pass ps n ws (String bslash s') after Fn Hs) as [Hopen Fn'].
    exists (map (wl_after (String bslash s')) ws), (esc_pending s' txt (Some bslash) o),
      (Some bslash), true, (pstep ps n false (THard s') v).
    rewrite iscan_wrap by exact Hopen. rewrite rres_wrap, iscan_bs_blank by exact Bl.
    split; [destruct s'; reflexivity|].
    split; [exact (pruns_one _ _ _ _ _ _ _ (punit_tok ps n false (THard s') _ v Em Ht0
                      (or_introl (pstep_mode ps n false (THard s') v Em ltac:(discriminate) ltac:(discriminate)))))|].
    split; [exact (vinv_step ps n false (THard s') _ v V Em Ht0 ltac:(discriminate))|].
    split; [exact Fn'|].
    right. left. exists s', txt, (Some bslash), o, v. split; [reflexivity|]. split; [exact Bl|].
    split; [reflexivity|]. split; [exact Em|]. split; [exact Hsim|reflexivity]. }
  destruct s' as [|d r]; [discriminate|].
  cbn [over_alphabet] in Ha. change (is_bslash bslash) with true in Ha. cbn iota in Ha.
  apply andb_true_iff in Ha as [_ Ha1].
  destruct (is_ws d) eqn:Wd.
  - (* an escaped run of whitespace *)
    set (w1 := ws_run r).
    assert (Hw : ws_run (String d r) = String d w1) by (cbn [ws_run]; rewrite Wd; reflexivity).
    rewrite Hw in Ht0.
    set (rest := sdrop (String.length w1) r).
    assert (Ew : String d r = (String d w1 ++ rest)%string).
    { pose proof (ws_run_sdrop (String d r)) as E. rewrite Hw in E. symmetry. exact E. }
    assert (Hwb : is_blank (String d w1) = true) by (rewrite <- Hw; apply ws_run_blank).
    assert (Ha2 : over_alphabet rest = true) by (apply over_alphabet_ws_run, Ha1).
    destruct (str_last_blank w1 d Hwb) as (x & Ex & Hx).
    assert (Hnx : forall c', get 0 rest = Some c' -> is_ws c' = false).
    { intros c' E. apply (ws_run_next (String d r)). rewrite Hw. exact E. }
    assert (Hrest : exists c', get 0 rest = Some c').
    { destruct rest as [|c' r'] eqn:Er; [|exists c'; reflexivity].
      exfalso. rewrite append_empty_r in Ew. rewrite Ew in Bl. rewrite Hwb in Bl. discriminate. }
    destruct Hrest as (c' & G).
    pose proof (Hnx c' G) as Hc'.
    pose proof Hsim as (v0 & cm & Eo & Hts & Ev).
    assert (Scan : iscan_str (String bslash (String d w1)) (IText false txt prev o)
                   = IEscWs (String d w1) txt (Some bslash) o)
      by exact (iscan_bs_blank (String d w1) txt prev o Hwb).
    assert (Step : forall core1,
              settles (iscan_str (String bslash (String d w1)) (IText false txt prev o))
                core1 (get 0 rest) ->
              linked ps (n + S (String.length (String d w1))) false
                (pstep ps n false (TEscWs (String d w1)) v) (Some x) core1 ->
              pend_esc core1 = false -> note_ok (Some x) core1 rest ->
              scanned ps n false v ws (IText false txt prev o) (String bslash (String d r))).
    { intros core1 Hset L1 Pe N1.
      apply (ST (TEscWs (String d w1)) (S (String.length (String d w1))) rest (Some x) core1);
        try assumption.
      - intros k mr op cl E. discriminate E.
      - cbn [tok_text]. rewrite Ew. reflexivity.
      - reflexivity.
      - cbn [tok_text str_last]. rewrite Ex. reflexivity.
      - rewrite Pe. exact Ha2.
      - left. apply pstep_mode; [exact Em|discriminate|discriminate]. }
    destruct (Ascii.eqb d " "%char) eqn:Sp.
    + (* a non-breaking space, and the rest of the run as text *)
      apply Ascii.eqb_eq in Sp. subst d.
      apply (Step (IText false w1 (Some x) (oemit (mk NonBreakingSpace) (flush_text txt o)))).
      * rewrite G. cbn [settles]. rewrite Scan. unfold istep. cbn [istep_at].
        rewrite Hc', iescws_cons, Ascii.eqb_refl, Ex. reflexivity.
      * apply linked_normal; [apply pstep_mode; [exact Em|discriminate|discriminate]|].
        unfold pstep. cbn [nbsp_rest]. rewrite Ascii.eqb_refl.
        exists (pv_add NonBreakingSpace v), cm. split; [|split].
        -- change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s txt o)
             with (flush_text txt o).
           rewrite Eo, (flush_view cm txt v0 Hts), <- Ev.
           apply oemit_view. discriminate.
        -- apply top_add_nonstr. discriminate.
        -- unfold add_text. reflexivity.
      * reflexivity.
      * left. cbn [prev_ok]. apply ws_follow, Hx.
    + (* a tab or a carriage return first: the backslash and the run as text *)
      apply (Step (IText false (txt ++ String bslash (String d w1)) (Some x) o)).
      * rewrite G. cbn [settles]. rewrite Scan. unfold istep. cbn [istep_at].
        rewrite Hc', iescws_cons, Sp. cbn [str_last]. rewrite Ex. reflexivity.
      * apply linked_normal; [apply pstep_mode; [exact Em|discriminate|discriminate]|].
        unfold pstep. cbn [nbsp_rest]. rewrite Sp.
        apply sim_text; [exact Hsim|reflexivity].
      * reflexivity.
      * left. cbn [prev_ok]. apply ws_follow, Hx.
  - (* an escaped byte *)
    apply (ST (TEsc d) 2 r (Some d) (IText false (txt ++ esc_text d) (Some d) o));
      try assumption.
    + intros k mr op cl E. discriminate E.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + right. intros t p o' E. injection E as <- _ _.
      destruct txt; [|reflexivity]. cbn.
      destruct (esc_text d) eqn:E'; [destruct (esc_text_ne d E')|reflexivity].
    + cbn [iscan_str tok_text one]. rewrite istep_bslash_text, istep_esc_byte by exact Wd.
      apply settles_refl.
    + apply linked_normal; [apply pstep_mode; [exact Em|discriminate|discriminate]|].
      unfold pstep. apply sim_text; [exact Hsim|].
      destruct (esc_text d) eqn:E'; [destruct (esc_text_ne d E')|reflexivity].
    + left. apply pstep_mode; [exact Em|discriminate|discriminate].
Qed.

Local Lemma linked_rres : forall ps n h v prev core,
  line_end (sdrop n ps) -> linked ps n h v prev core -> linked ps n h v prev (rres core).
Proof.
  intros ps n h v prev core Hle L. unfold linked in *.
  destruct (pv_mode v) as [|[|] kids d e txt|x e].
  - destruct L as (Hh & t & o & -> & Hs). split; [exact Hh|]. exists t, o.
    split; [reflexivity|exact Hs].
  - destruct L as (Hd & Hh & open & sh & cm & ds & Hds & He & Hne & ->).
    split; [exact Hd|]. split; [exact Hh|]. exists open, (rres sh), cm, ds. auto.
  - destruct L as (Hd & Hk & Hh & esc & label' & open & cm & He & Hl & ->).
    split; [exact Hd|]. split; [exact Hk|]. split; [exact Hh|].
    exists esc, label', open, cm. auto.
  - destruct L as (Hh & He & p & dd & m & body & cl & rw & txt0 & prev0 & o0 & Hp & Ht & Ex & Hs & Ec
                   & Vs).
    assert (Ge : get n ps = None \/ get n ps = Some nl_char).
    { rewrite <- (Nat.add_0_r n), get_add.
      destruct Hle as [-> | [r ->]]; [left|right]; reflexivity. }
    assert (Er : rres core = core).
    { destruct core; cbn [verb_state] in Vs; try contradiction; try reflexivity.
      exfalso. destruct Ge as [G|G]; rewrite G in Vs; destruct Vs as [E|E]; discriminate E. }
    rewrite Er. split; [exact Hh|]. split; [exact He|].
    exists p, dd, m, body, cl, rw, txt0, prev0, o0. repeat split; assumption.
Qed.

Local Lemma scanned_nil : forall ps n h v ws core prev,
  vinv ps n h v -> Forall (never ps n) ws -> linked ps n h v prev core ->
  line_end (sdrop n ps) -> scanned ps n h v ws core "".
Proof.
  intros ps n h v ws core prev V Fn L He. exists ws, (rres core), prev, h, v.
  cbn [iscan_str String.length]. rewrite Nat.add_0_r, rres_wrap.
  split; [reflexivity|]. split; [constructor|]. split; [exact V|].
  split; [exact Fn|left; apply linked_rres; [exact He|exact L]].
Qed.

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
Local Lemma open_marked_sim : forall ps n k b txt v o,
  pv_ok ps n v -> sim v txt o ->
  sim (popen n (KDelim k true) true (tok_text (TDelim k true true false)) v) ""
    (oopen_marked k b txt o).
Proof.
  intros ps n k b txt v o Ok (v0 & cm & -> & Ht & ->).
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
    else IReference kids false null_span false "" o'.
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

Local Lemma no_nl_chars : forall k j r,
  no_char nl_char r = true -> no_char nl_char (chars (dchar k) j ++ r) = true.
Proof.
  intros k j r H. induction j as [|j IH]; [exact H|]. cbn [chars append no_char].
  rewrite dchar_nl, IH. reflexivity.
Qed.

(* A run of a row's character too short to be a token: a text token for
   each byte. *)
Local Lemma run_texts : forall ps k j n v txt o r after,
  dstyle_of (dchar k) = Some k -> j < dwidth k ->
  (forall d r', r = String d r' -> d <> dchar k) -> no_char nl_char r = true -> line_end after ->
  sdrop n ps = (chars (dchar k) j ++ r ++ after)%string ->
  vinv ps n false v -> pv_mode v = PMNormal -> sim v txt o ->
  exists v', pruns ps n false v (n + j) false v' /\ vinv ps (n + j) false v'
    /\ pv_mode v' = PMNormal /\ sim v' (txt ++ chars (dchar k) j) o.
Proof.
  intros ps k j. induction j as [|j IH]; intros n v txt o r after Hk Hj Hr Hn Ha Hs V Em Hsim.
  - exists v. rewrite Nat.add_0_r, append_empty_r. split; [constructor|auto].
  - assert (Ht : tok_at ps n = Some (TText (dchar k), 1)).
    { rewrite <- (nt_short k j (before ps n) r Hk Hj Hr). unfold tok_at. rewrite Hs.
      replace (chars (dchar k) (S j) ++ r ++ after)%string
        with (String (dchar k) (chars (dchar k) j ++ r) ++ after)%string
        by (cbn [chars append]; rewrite append_assoc; reflexivity).
      pose proof (dreserved_false _ (dchar_free k)) as (_ & Htk & _ & _ & _ & _ & _ & Hdl & _).
      apply next_tok_after; [|exact Ha|discriminate|exact Htk|exact Hdl].
      cbn [no_char]. rewrite dchar_nl. apply no_nl_chars, Hn. }
    pose proof (vinv_step ps n false _ 1 v V Em Ht ltac:(discriminate)) as V1.
    cbn [is_hard] in V1. rewrite Nat.add_1_r in V1.
    assert (Hs1 : sdrop (S n) ps = (chars (dchar k) j ++ r ++ after)%string)
      by exact (sdrop_succ ps n (dchar k) _ Hs).
    destruct (IH (S n) (pstep ps n false (TText (dchar k)) v) (txt ++ one (dchar k)) o r after
                Hk ltac:(lia) Hr Hn Ha Hs1 V1)
      as (v' & R & V' & Em' & Hsim').
    { apply pstep_mode; [exact Em|discriminate|discriminate]. }
    { unfold pstep. apply sim_text; [exact Hsim|reflexivity]. }
    exists v'. rewrite <- Nat.add_succ_comm. split; [|split; [exact V'|split; [exact Em'|]]].
    + apply (pruns_trans ps n false v (S n) false (pstep ps n false (TText (dchar k)) v));
        [|exact R].
      apply pruns_one. rewrite (punit_tok ps n false _ 1 v Em Ht (or_intror eq_refl)), Nat.add_1_r. reflexivity.
    + rewrite append_assoc in Hsim'. exact Hsim'.
Qed.

(* A verbatim or math from text mode: the view walks its bytes, or it is
   a lone backtick the paragraph ends in. *)
Local Lemma scan_verb : forall ps after len, scan_ih ps after len ->
  forall c s' prev n v ws txt o d m body cl r l,
    String.length (String c s') <= S len -> over_alphabet (String c s') = true ->
    sdrop n ps = (String c s' ++ after)%string ->
    vinv ps n false v -> Forall (never ps n) ws -> pv_mode v = PMNormal -> sim v txt o ->
    tok_at ps n = Some (TVerb d m body cl r, l) ->
    scanned ps n false v ws (IText false txt prev o) (String c s').
Proof.
  intros ps after len IH c s' prev n v ws txt o d m body cl r l Hl Ha Hs V Fn Em Hsim Htv.
  pose proof V as (Ok & Ti & _).
  pose proof Hsim as (v0 & cm & Eo & Ht & Ev).
  destruct (verb_tok_scan ps n d m body cl r l txt prev o Htv) as (T1 & T2 & Traw & T3).
  pose proof (tok_at_len ps n _ _ Htv) as [Hl0 Hle].
  destruct (tok_at_verb ps n d m body cl r l Htv) as (w & Ew & Hst & _ & Hdl & _).
  assert (Te : tok_end ps n = n + l) by (unfold tok_end; rewrite Htv; reflexivity).
  pose proof (get_sdrop ps n c _ Hs) as Hg.
  assert (Sub1 : substring n 1 ps = one c).
  { rewrite (substring_snoc ps n 0 c) by (rewrite Nat.add_0_r; exact Hg).
    rewrite substring_nil. reflexivity. }
  pose proof (before_sdrop ps n c _ Hs) as Hb.
  set (x := verb_node d r body). set (X := chars dollar (d - 2)).
  destruct (Nat.ltb (S n) (n + l)) eqn:Elt.
  - (* the view walks the token's bytes *)
    apply Nat.ltb_lt in Elt.
    set (v1 := pv_setmode (PMAtom x (pred (n + l))) (add_text X v)).
    assert (Pst : pstep ps n false (TVerb d m body cl r) v = v1)
      by (unfold pstep; rewrite Te; apply Nat.ltb_lt in Elt; rewrite Elt; reflexivity).
    assert (U : punit ps n false v = Some (S n, false, v1))
      by (unfold punit; rewrite Em, Htv; cbv zeta; rewrite Pst; reflexivity).
    assert (V1 : vinv ps (S n) false v1).
    { pose proof (vinv_step ps n false _ l v V Em Htv ltac:(discriminate)) as (Ok1 & Ti1 & _).
      rewrite Pst in Ok1, Ti1.
      split; [|split; [exact Ti1|discriminate]].
      destruct Ok1 as (A1 & A2 & A3 & A4 & A5 & A6 & _).
      split; [exact A1|].
      pose proof Ok as (D & Bd & Be & _).
      assert (Live : pv_live v1 = pv_live v)
        by (unfold v1; rewrite <- (proj1 (add_text_live X v)); destruct (add_text X v); reflexivity).
      assert (Stk : forall p k c0, In (PF p k c0) (pv_stk v1) ->
                      exists c', In (PF p k c') (pv_stk v)).
      { intros p k c0 H. unfold v1, add_text in H. destruct (nonempty_str X).
        - destruct (pv_add (Str X) v) eqn:E. cbn [pv_setmode pv_stk] in H.
          apply (in_stk_add (Str X) v p k c0). rewrite E. exact H.
        - destruct v. exists c0. exact H. }
      split; [intros y Hy; rewrite Live in Hy; specialize (Bd y Hy); lia|].
      split; [intros p k c0 H; destruct (Stk p k c0 H) as [c' H']; specialize (Be p k c' H'); lia|].
      split; [exact A4|]. split; [exact A5|]. split; [exact A6|].
      unfold v1. destruct (add_text X v); exact Logic.I. }
    assert (VS : verb_state (istep c (IText false txt prev o)) (get (S n) ps)).
    { pose proof (T1 1 ltac:(lia)) as H. rewrite Sub1, Nat.add_1_r in H. exact H. }
    assert (Nv : pv_setmode PMNormal v1 = add_text X v).
    { unfold v1. pose proof (proj2 (add_text_live X v)) as M. rewrite Em in M.
      destruct (add_text X v); cbn in *; subst; reflexivity. }
    assert (Sv : sim (add_text X v) (txt ++ X) o).
    { unfold add_text. destruct (nonempty_str X) eqn:E; [apply sim_text; assumption|].
      replace X with "" by (destruct X; [reflexivity|discriminate]).
      rewrite append_empty_r. exact Hsim. }
    apply (scan_advance_gen ps after len IH (String c s') n false v ws
             (IText false txt prev o) (one c) s' (Some c) []
             (istep c (IText false txt prev o)) false v1);
      cbn [String.length one]; try rewrite Nat.add_1_r;
      first [assumption | reflexivity | discriminate | exact (pruns_one _ _ _ _ _ _ _ U)
            | (rewrite Hb; reflexivity) | apply Forall_nil | idtac].
    + unfold alpha_ok, v1. cbn [pv_setmode pv_mode]. destruct (add_text X v). cbn [pv_mode].
      eexists. exact (alpha_tail false c s' Ha).
    + right. intros t q o' E. rewrite E in VS. exact (False_ind _ VS).
    + apply settles_refl.
    + unfold linked. replace (pv_mode v1) with (PMAtom x (pred (n + l)))
        by (unfold v1; destruct (add_text X v); reflexivity).
      split; [reflexivity|]. split; [lia|].
      exists n, d, m, body, cl, r, txt, prev, o. split; [lia|].
      split; [replace (S (pred (n + l)) - n) with l by lia; exact Htv|].
      split; [reflexivity|]. split; [rewrite Nv; exact Sv|].
      split; [replace (S n - n) with 1 by lia; rewrite Sub1; reflexivity|exact VS].
  - (* a lone backtick that ends the paragraph *)
    apply Nat.ltb_ge in Elt. assert (El : l = 1) by lia. subst l.
    assert (d = 0) as -> by lia.
    assert (c = tick) as ->.
    { cbn [chars append] in Ew. rewrite Hs in Ew. subst w. cbn in Hst.
      apply Ascii.eqb_eq in Hst. exact Hst. }
    destruct r as [f|].
    { exfalso. destruct (Traw f eq_refl) as (_ & _ & Gr & _). cbn [pred] in Gr.
      rewrite Nat.add_0_r, Hg in Gr. discriminate Gr. }
    cbn [Nat.sub chars] in T2, T3, X. rewrite append_empty_r in T2, T3.
    destruct cl.
    { exfalso. destruct (T2 eq_refl eq_refl) as [E _]. rewrite Sub1 in E.
      change (one tick) with (ticks 1) in E. rewrite iscan_open_ticks in E by lia. discriminate. }
    destruct (T3 eq_refl) as (_ & Elen & Efin).
    assert (Hlen : String.length (sdrop n ps) = 1) by (rewrite sdrop_length; lia).
    rewrite Hs in Hlen. cbn [append String.length] in Hlen. rewrite length_append in Hlen.
    destruct s' as [|d r]; [|cbn in Hlen; lia].
    destruct after as [|a af]; [|cbn in Hlen; lia].
    assert (Pst : pstep ps n false (TVerb 0 m body false None) v = pv_add x v).
    { unfold pstep. rewrite Te.
      replace (S n <? n + 1)%nat with false by (symmetry; apply Nat.ltb_ge; lia). reflexivity. }
    pose proof (punit_tok ps n false _ 1 v Em Htv (or_intror eq_refl)) as U.
    pose proof (vinv_step ps n false _ 1 v V Em Htv ltac:(discriminate)) as V1.
    rewrite Pst in U, V1. cbn [is_hard] in U, V1. rewrite Nat.add_1_r in U, V1.
    pose proof (sdrop_succ ps n tick _ Hs) as Hs1.
    destruct (layers_pass ps n ws (one tick) "" Fn Hs) as [Fo Fn'].
    exists (map (wl_after (one tick)) ws), (rres (istep tick (IText false txt prev o))),
      (Some tick), false, (pv_add x v).
    cbn [String.length] in *. rewrite Nat.add_1_r in *.
    split; [|split; [exact (pruns_one _ _ _ _ _ _ _ U)|split; [exact V1|split; [exact Fn'|]]]].
    + rewrite <- rres_wrap.
      exact (step_through (one tick) "" ws (IText false txt prev o)
               (istep tick (IText false txt prev o)) _ Fo eq_refl (settles_refl _ _)).
    + right. right. exists x, v, cm.
      split; [reflexivity|]. split; [exact Em|]. split; [reflexivity|].
      split; [intros s0; discriminate|]. right. split; [exact Hs1|].
      rewrite ifinish_rres. rewrite Sub1 in Efin. cbn [iscan_str] in Efin.
      change (istep tick (IText false txt prev o))
        with (iscan_str (one tick) (IText false txt prev o)).
      rewrite Efin, Eo, (flush_view cm txt v0 Ht), <- Ev, (oemit_view cm _ v)
        by (intros s0; discriminate).
      reflexivity.
Qed.

Local Lemma scan_sim : forall ps after, line_end after -> forall len, scan_ih ps after len.
Proof.
  intros ps after Hae len. induction len as [|len IH];
    intros s prev n h v ws core Hl Ha Hp Hs Hpv V Fn L;
    destruct s as [|c s'];
    try (apply (scanned_nil ps n h v ws core prev); [assumption|assumption|assumption|];
         rewrite Hs; exact Hae).
  { cbn in Hl. lia. }
  unfold alpha_ok in Ha.
  destruct (pv_mode v) as [|b kids d e txt|x e] eqn:Em.
  3: { (* inside a token *)
       exact (scan_atom ps after len IH Hae c s' prev n h v ws core x e Hl Ha Hs V Fn L Em). }
  2: { (* in a region *)
       apply (scan_region ps after len IH c s' prev n h v ws core); try assumption;
         [rewrite Em; discriminate|intros ? ?; rewrite Em; discriminate]. }
  (* in text mode *)
  pose proof L as L0. unfold linked in L. rewrite Em in L. destruct L as (-> & txt & o & -> & Hsim).
  cbn [pend_esc with_esc] in Ha.
  destruct (is_bslash c) eqn:Eb.
  { unfold is_bslash in Eb. apply Ascii.eqb_eq in Eb. subst c.
    exact (scan_esc ps after len IH Hae s' prev n false v ws _ Hl Ha Hs Hpv V Fn L0 Em). }
  pose proof V as (Ok & Ti & _). pose proof Ok as (_ & _ & _ & B & _).
  pose proof Hsim as (v0 & cm & Eo & Ht & Ev).
  pose proof Ha as Ha'. apply (over_alphabet_cons c s' Eb) in Ha' as (Hc & Hf & Hs').
  assert (Hn : no_note c txt prev = true) by exact (no_note_ok' prev c s' txt prev o Hp).
  destruct (is_tick c) eqn:Etk.
  { (* a verbatim *)
    unfold is_tick in Etk. apply Ascii.eqb_eq in Etk. subst c.
    assert (Htk : exists m body cl r l, tok_at ps n = Some (TVerb 0 m body cl r, l)).
    { unfold tok_at. rewrite Hs. unfold next_tok. cbn [append].
      change (Ascii.eqb tick nl_char) with false. change (is_bslash tick) with false.
      change (is_tick tick) with true. cbv iota.
      destruct (verb_tok_shape 0 (String tick (s' ++ after))) as (m & b & cl & r & l & E).
      rewrite E. eexists _, _, _, _, _. reflexivity. }
    destruct Htk as (m & body & cl & r & l & Htv).
    exact (scan_verb ps after len IH tick s' prev n v ws txt o 0 m body cl r l Hl Ha Hs V Fn Em Hsim
             Htv). }
  destruct (Ascii.eqb c dollar) eqn:Edl.
  { (* a run of dollars: math, or text *)
    apply Ascii.eqb_eq in Edl. subst c.
    assert (Hdm : dollar_math_enabled = false).
    { unfold in_alphabet in Hc. destruct dollar_math_enabled; [|reflexivity].
      exfalso. revert Hc. vm_compute. destruct (dstyle_of dollar); discriminate. }
    assert (Hdt : tok_at ps n = Some (dollar_tok (String dollar (s' ++ after))))
      by (unfold tok_at; rewrite Hs; reflexivity).
    destruct (dollar_tok (String dollar (s' ++ after))) as [t l] eqn:Edt.
    pose proof Edt as Edt'. unfold dollar_tok in Edt'.
    set (k := dollar_run (String dollar (s' ++ after))) in Edt'.
    destruct (math_enabled && starts_with tick (sdrop k (String dollar (s' ++ after))))%bool eqn:Ek.
    { destruct (verb_tok_shape k (sdrop k (String dollar (s' ++ after)))) as (m & b & cl & r & l0 & Evt).
      rewrite Evt in Edt'. injection Edt' as <- <-.
      exact (scan_verb ps after len IH dollar s' prev n v ws txt o k m b cl r _ Hl Ha Hs V Fn Em Hsim
               Hdt). }
    injection Edt' as <- <-.
    (* the run is in the line, and what follows it neither continues it nor opens math *)
    assert (Dr : forall a, dollar_run (a ++ after) = dollar_run a).
    { induction a as [|x a IHa]; [destruct Hae as [->|[r ->]]; reflexivity|].
      cbn [append dollar_run]. rewrite IHa. reflexivity. }
    assert (Dc : forall j x, dollar_run (chars dollar j ++ x) = j + dollar_run x).
    { induction j as [|j IHj]; intros x; [reflexivity|]. cbn [chars append dollar_run].
      rewrite Ascii.eqb_refl, IHj. reflexivity. }
    assert (Sc : forall j x, sdrop j (chars dollar j ++ x) = x)
      by (induction j as [|j IHj]; intros x; [reflexivity|exact (IHj x)]).
    change (String dollar (s' ++ after)) with (String dollar s' ++ after)%string in *.
    assert (Hkv : k = dollar_run (String dollar s')) by apply Dr. clearbody k.
    set (rest := sdrop k (String dollar s')).
    assert (Hsp : String dollar s' = (chars dollar k ++ rest)%string)
      by (unfold rest; rewrite Hkv; apply dollar_run_split).
    assert (Hk0 : 0 < k) by (rewrite Hkv; cbn [dollar_run]; rewrite Ascii.eqb_refl; lia).
    assert (Hra : sdrop k (String dollar s' ++ after) = (rest ++ after)%string)
      by (rewrite Hsp, append_assoc, Sc; reflexivity).
    rewrite Hra in Ek.
    assert (Hr1 : forall c' r', rest = String c' r' ->
                  Ascii.eqb c' dollar = false /\ (math_enabled = true -> is_tick c' = false)).
    { intros c' r' Er. split.
      - pose proof (Dc k rest) as D1. rewrite <- Hsp, <- Hkv in D1.
        rewrite Er in D1. cbn [dollar_run] in D1. destruct (Ascii.eqb c' dollar); [lia|reflexivity].
      - intros Hm. rewrite Er, Hm in Ek. exact Ek. }
    (* the scanner holds the run, and the byte after it makes it text *)
    assert (Cs : forall j, chars dollar j ++ String dollar (one dollar) = chars dollar (S (S j))).
    { induction j as [|j IHj]; [reflexivity|]. cbn [chars append]. rewrite IHj. reflexivity. }
    set (X := IText false (txt ++ chars dollar k) (Some dollar) o).
    assert (Ix : iresolve (iscan_str (chars dollar k) (IText false txt prev o)) = X
                 /\ forall c', Ascii.eqb c' dollar = false ->
                    (math_enabled = true -> is_tick c' = false) ->
                    istep c' (iscan_str (chars dollar k) (IText false txt prev o)) = istep c' X).
    { rewrite iscan_dollars by exact Hk0. unfold X.
      destruct k as [|[|k']]; [lia| |].
      - split; [reflexivity|]. intros c' E1 E2. unfold istep. cbn [istep_at].
        unfold idollar_step. rewrite E1, Hdm.
        destruct (is_tick c' && math_enabled)%bool eqn:E3.
        { apply andb_true_iff in E3 as [E3 E4]. rewrite (E2 E4) in E3. discriminate. }
        rewrite !andb_false_r. reflexivity.
      - split.
        + cbn [iresolve]. tred. change (InlineScan.dollars true) with (String dollar (one dollar)).
          rewrite append_assoc. replace (S (S k') - 2) with k' by lia. rewrite Cs. reflexivity.
        + intros c' E1 E2. unfold istep. cbn [istep_at].
          unfold idollar_step. rewrite E1, Hdm.
          destruct (is_tick c' && math_enabled)%bool eqn:E3.
          { apply andb_true_iff in E3 as [E3 E4]. rewrite (E2 E4) in E3. discriminate. }
          rewrite !andb_false_r. cbn [andb orb negb]. tred.
          change (InlineScan.dollars true) with (String dollar (one dollar)).
          rewrite append_assoc. replace (S (S k') - 2) with k' by lia. rewrite Cs. reflexivity. }
    destruct Ix as [Ix1 Ix2].
    assert (Rr : rres (iscan_str (chars dollar k) (IText false txt prev o))
                 = iresolve (iscan_str (chars dollar k) (IText false txt prev o)))
      by (rewrite iscan_dollars by exact Hk0; destruct k as [|[|]]; [lia| |]; cbn [rres];
          rewrite Hdm; reflexivity).
    assert (Sl : forall j p, str_last (chars dollar (S j)) p = Some dollar).
    { induction j as [|j IHj]; intros p; [reflexivity|]. exact (IHj (Some dollar)). }
    assert (Nb : forall j, no_bslash (chars dollar j) = true)
      by (induction j as [|j IHj]; [reflexivity|exact IHj]).
    apply (scan_tok ps after len IH (String dollar s') n false v ws (IText false txt prev o)
             (TDollars k) k rest (Some dollar) X Hl Hs Fn V Em Hdt).
    - intros k0 mr op cl E. discriminate E.
    - exact Hsp.
    - cbn [tok_text]. symmetry. apply length_chars.
    - cbn [tok_text]. destruct k as [|k]; [lia|]. rewrite Sl. reflexivity.
    - cbn [pend_esc with_esc]. rewrite Hsp in Ha. exact (over_alphabet_app_r _ rest (Nb k) Ha).
    - right. intros t q o' E. unfold X in E. injection E as <- _ _.
      destruct k as [|k]; [lia|]. destruct txt; reflexivity.
    - cbn [tok_text]. destruct rest as [|c' r'] eqn:Er; cbn [get settles].
      + rewrite Rr, Ix1. reflexivity.
      + destruct (Hr1 c' r' eq_refl) as [E1 E2]. exact (Ix2 c' E1 E2).
    - cbn [is_hard]. unfold pstep.
      apply linked_normal; [rewrite (proj2 (pv_add_live _ _)); exact Em|].
      cbn [tok_text]. apply sim_text; [exact Hsim|]. destruct k as [|k]; [lia|]. reflexivity.
    - left. apply pstep_mode; [exact Em|discriminate|discriminate]. }
  pose proof (alphabet_no_nl _ Ha) as Hnl.
  assert (Htok : tok_at ps n = next_tok prev (String c s'))
    by exact (tok_at_line ps n _ after prev Hs Hae ltac:(discriminate) Etk Edl Hnl Hpv).
  pose proof (fun t l rest prev1 core1 =>
                scan_tok ps after len IH (String c s') n false v ws (IText false txt prev o)
                  t l rest prev1 core1 Hl Hs Fn V Em) as ST.
  (* a token the view reads in text mode *)
  assert (Nrm : forall t l rest prev1 txt' o',
            tok_at ps n = Some (t, l) ->
            (forall k mr op cl, t = TDelim k mr op cl -> self_row k = true) ->
            String c s' = (tok_text t ++ rest)%string -> l = String.length (tok_text t) ->
            nonspace_at (str_last (tok_text t) (before ps n)) = nonspace_at prev1 ->
            over_alphabet rest = true -> prev_ok prev1 rest = true ->
            settles (iscan_str (tok_text t) (IText false txt prev o)) (IText false txt' prev1 o')
              (get 0 rest) ->
            is_hard t = false -> pv_mode (pstep ps n false t v) = PMNormal ->
            sim (pstep ps n false t v) txt' o' ->
            scanned ps n false v ws (IText false txt prev o) (String c s')).
  { intros t l rest prev1 txt' o' Ht0 Hk Es El Hp1 Ha1 Hf1 Hset Hh Em1 Hs1.
    apply (ST t l rest prev1 (IText false txt' prev1 o') Ht0 Hk Es El Hp1 Ha1 (or_introl Hf1) Hset);
      [rewrite Hh; apply linked_normal; assumption|left; exact Em1]. }
  destruct (Ascii.eqb c lbrack) eqn:Elk.
  { apply Ascii.eqb_eq in Elk. subst c.
    apply (Nrm TOpen 1 s' (Some lbrack) "" (bpush false (flush_text txt o)));
      [rewrite Htok; reflexivity|discriminate|reflexivity|reflexivity|reflexivity|exact Hs'|exact Hf| | | |].
    - cbn [iscan_str tok_text one]. unfold istep. cbn [istep_at].
      rewrite (ilead_lbrack txt prev o (note_free' prev lbrack s' txt prev o Hp (or_introl eq_refl))).
      apply settles_refl.
    - reflexivity.
    - apply pstep_mode; [exact Em|discriminate|discriminate].
    - unfold pstep. apply open_bracket_sim, Hsim. }
  assert (Vb : forall m h1 w c1, vinv ps m h1 w -> pv_mode w <> PMNormal ->
              vinv ps (S m) false (pbyte m c1 w)).
  { intros m h1 w c1 (Okw & Tiw & _) Ew. split; [apply pv_ok_byte; assumption|].
    split; [apply pbyte_tidy, Tiw|]. discriminate. }
  destruct (Ascii.eqb c rbrack) eqn:Erk.
  { apply Ascii.eqb_eq in Erk. subst c.
    assert (Hfl : flush_text txt o = oview cm v) by (rewrite Eo, Ev; apply flush_view, Ht).
    assert (Htag : tag_close (flush_text txt o) = None) by (rewrite Hfl; apply tag_close_oview).
    assert (Txt : forall t, tok_text t = one rbrack -> is_hard t = false ->
              (forall k mr op cl, t = TDelim k mr op cl -> self_row k = true) ->
              next_tok prev (String rbrack s') = Some (t, 1) ->
              pstep ps n false t v = pv_add (Str (one rbrack)) v ->
              (forall c0, get 0 s' = Some c0 ->
                 (Ascii.eqb c0 lparen || Ascii.eqb c0 lbrack
                  || (Ascii.eqb c0 lbrace && inline_attrs_enabled))%bool = true ->
                 bclose (flush_text txt o) = None) ->
              scanned ps n false v ws (IText false txt prev o) (String rbrack s')).
    { intros t Et Hh Hk El Ep Hb.
      apply (Nrm t 1 s' (Some rbrack) (txt ++ one rbrack) o);
        [rewrite Htok; exact El|exact Hk|rewrite Et; reflexivity|rewrite Et; reflexivity
        |rewrite Et; reflexivity|exact Hs'|exact Hf| |exact Hh| |].
      - rewrite Et. apply tok_rbrack_text; [exact Htag|exact Hb].
      - rewrite Ep, (proj2 (pv_add_live _ _)). exact Em.
      - rewrite Ep. apply sim_text; [exact Hsim|reflexivity]. }
    destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest']|] eqn:Hpc.
    2: { (* no bracket to close *)
      assert (Hb : bclose (flush_text txt o) = None).
      { rewrite Hfl. unfold oview. rewrite (bclose_embed cm _ _ B), Hpc. reflexivity. }
      destruct (starts_with lparen s') eqn:S1; [|destruct (starts_with lbrack s') eqn:S2].
      - apply (Txt (TClose true)); try reflexivity;
          [discriminate|rewrite nt_rbrack, S1; reflexivity
          |exact (pstep_close_none ps n false true v Hpc)|intros; exact Hb].
      - apply (Txt (TClose false)); try reflexivity;
          [discriminate|rewrite nt_rbrack, S1, S2; reflexivity
          |exact (pstep_close_none ps n false false v Hpc)|intros; exact Hb].
      - apply (Txt (TText rbrack)); try reflexivity;
          [discriminate|rewrite nt_rbrack, S1, S2; reflexivity|intros; exact Hb]. }
    destruct Ti as (_ & _ & Fnm & Fcl & _).
    destruct (pclose_go_normal KBracket (pv_stk v) [] content rest' Fnm Logic.I Hpc) as [Nc _].
    destruct (pclose_go_clean KBracket (pv_stk v) [] content rest' Fcl (Forall_nil _) Hpc)
      as [Cc _].
    set (kids := map mk (List.rev content)).
    set (o1 := oview cm (PView rest' (pv_out v) PMNormal)).
    assert (Hcl : forall c2, c2 = lparen \/ c2 = lbrack ->
              iscan_str (String rbrack (one c2)) (IText false txt prev o)
              = if Ascii.eqb c2 lparen
                then IDest kids false null_span false 0 "" (idest_open kids false null_span o1) o1
                else IReference kids false null_span false "" o1).
    { intros c2 H2. cbn [iscan_str one]. unfold istep at 2. cbn [istep_at].
      rewrite (ilead_rbrack_closed txt prev o Htag). rewrite Eo.
      pose proof (closed_step cm v0 txt c2 content rest' Ht) as Hcs.
      rewrite <- Ev in Hcs. exact (Hcs B Hpc H2). }
    (* `](` or `][`: the closer and the byte after it *)
    assert (Two : forall c2 r, s' = String c2 r ->
              tok_at ps n = Some (if Ascii.eqb c2 lparen then TClose true else TClose false, 1) ->
              forall h1 v1 core1 extra,
                pruns ps (S n) false (pstep ps n false
                   (if Ascii.eqb c2 lparen then TClose true else TClose false) v) (n + 2) h1 v1 ->
                vinv ps (n + 2) h1 v1 ->
                over_alphabet (with_esc (pend_esc core1) r) = true -> note_ok (Some c2) core1 r ->
                settles (iscan_str (String rbrack (one c2)) (IText false txt prev o))
                  (wrap extra core1) (get 0 r) ->
                Forall (never ps (n + 2)) extra ->
                linked ps (n + 2) h1 v1 (Some c2) core1 ->
                scanned ps n false v ws (IText false txt prev o) (String rbrack s')).
    { intros c2 r -> Ht2 h1 v1 core1 extra R2 V2 A2 N2 S2 F2 L2.
      apply (scan_advance ps after len IH (String rbrack (String c2 r)) n false v ws
               (IText false txt prev o) (String rbrack (one c2)) r (Some c2) extra core1 h1 v1);
        try assumption; cbn [String.length one]; try reflexivity; try discriminate.
      - apply (pruns_trans ps n false v (S n) false
                 (pstep ps n false (if Ascii.eqb c2 lparen then TClose true else TClose false) v));
          [|exact R2].
        apply pruns_one. rewrite (punit_tok ps n false _ 1 v Em Ht2 (or_intror eq_refl)), Nat.add_1_r.
        destruct (Ascii.eqb c2 lparen); reflexivity.
      - pose proof (before_chunk ps n (String rbrack (String c2 EmptyString)) (r ++ after) Hs)
          as Eb2.
        cbn [String.length str_last] in Eb2. rewrite Eb2. reflexivity. }
    destruct (starts_with lparen s') eqn:S1.
    { (* a destination *)
      destruct s' as [|c2 r]; [discriminate|]. cbn [starts_with] in S1.
      apply Ascii.eqb_eq in S1. subst c2.
      apply (over_alphabet_cons lparen r eq_refl) in Hs' as (Hc2 & Hf2 & Hr').
      assert (Ht1 : tok_at ps n = Some (TClose true, 1)) by (rewrite Htok, nt_rbrack; reflexivity).
      pose proof (vinv_step ps n false (TClose true) 1 v V Em Ht1 ltac:(discriminate)) as V1.
      cbn [is_hard] in V1. rewrite Nat.add_1_r in V1.
      assert (Hs1 : sdrop (S n) ps = String lparen (r ++ after))
        by exact (sdrop_succ ps n rbrack _ Hs).
      pose proof (Two lparen r eq_refl ltac:(rewrite Ht1; reflexivity)) as T2.
      rewrite Ascii.eqb_refl in T2.
      rewrite (pstep_close_found ps n false true v content rest' Hpc) in V1, T2.
      replace (n + 2) with (S (S n)) in T2 by lia.
      destruct (region_end ps n true) as [e|] eqn:R.
      - (* that closes: its region *)
        pose proof (region_end_bound ps n true e R) as Hbd.
        set (v1 := PView rest' (pv_out v) (PMRegion true (List.rev content) n (Some e) "")) in *.
        assert (U2 : punit ps (S n) false v1 = Some (S (S n), false, pbyte (S n) lparen v1)).
        { unfold punit. cbn [v1 pv_mode]. rewrite (get_sdrop ps (S n) lparen _ Hs1). reflexivity. }
        apply (T2 false (pbyte (S n) lparen v1)
                 (IDest kids false null_span false 0 "" (idest_open kids false null_span o1) o1) []).
        + exact (pruns_one _ _ _ _ _ _ _ U2).
        + apply (Vb (S n) false v1 lparen V1). discriminate.
        + exact Hr'.
        + right. intros t p o' E. discriminate E.
        + cbn [wrap]. rewrite (Hcl lparen (or_introl eq_refl)), Ascii.eqb_refl. apply settles_refl.
        + constructor.
        + unfold linked, pbyte. cbn [v1 pv_mode pv_setmode pv_stk pv_out].
          replace (S n =? e)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
          rewrite Nat.eqb_refl. cbn [pv_mode].
          split; [lia|]. split; [reflexivity|].
          exists null_span, (idest_open kids false null_span o1), cm, (DS false 0 "").
          split; [reflexivity|]. split; [|split; [discriminate|reflexivity]].
          rewrite <- R. reflexivity.
      - (* that does not close: a reading of its own, and the text after it *)
        destruct (dest_open_sim cm n content rest' (pv_out v) Nc Cc) as (txt' & o2 & Eo' & S').
        set (v1 := PView (PB n (xsnoc (Str (one rbrack)) content) :: rest') (pv_out v) PMNormal) in *.
        assert (Ht2 : tok_at ps (S n) = Some (TText lparen, 1)).
        { unfold tok_at. rewrite Hs1. apply nt_byte; try reflexivity.
          exact (alphabet_paren_none lparen Hc2 eq_refl). }
        apply (T2 false (pstep ps (S n) false (TText lparen) v1)
                 (IText false (txt' ++ one rbrack ++ one lparen) (Some lparen) o2)
                 [WL kids null_span (DS false 0 "") o1]).
        + apply pruns_one. rewrite (punit_tok ps (S n) false _ 1 v1 eq_refl Ht2 (or_intror eq_refl)), Nat.add_1_r.
          reflexivity.
        + pose proof (vinv_step ps (S n) false _ 1 v1 V1 eq_refl Ht2 ltac:(discriminate)) as V2.
          rewrite Nat.add_1_r in V2. exact V2.
        + exact Hr'.
        + left. cbn [prev_ok]. apply follow_ok_plain; reflexivity.
        + cbn [wrap wl_kids wl_open wl_ds wl_o ds_esc ds_depth ds_dst].
          rewrite (Hcl lparen (or_introl eq_refl)), Ascii.eqb_refl.
          fold kids o1 in Eo'. rewrite Eo'. apply settles_refl.
        + constructor; [|constructor]. unfold never, wl_depth. cbn [wl_ds ds_esc ds_depth].
          exact R.
        + apply linked_normal; [reflexivity|exact S']. }
    destruct (starts_with lbrack s') eqn:S2.
    { (* a reference label *)
      destruct s' as [|c2 r]; [discriminate|]. cbn [starts_with] in S1, S2.
      apply Ascii.eqb_eq in S2. subst c2.
      apply (over_alphabet_cons lbrack r eq_refl) in Hs' as (_ & Hf2 & Hr').
      assert (Ht1 : tok_at ps n = Some (TClose false, 1))
        by (rewrite Htok, nt_rbrack; cbn [starts_with]; rewrite S1, Ascii.eqb_refl; reflexivity).
      pose proof (vinv_step ps n false (TClose false) 1 v V Em Ht1 ltac:(discriminate)) as V1.
      cbn [is_hard] in V1. rewrite Nat.add_1_r in V1.
      assert (Hs1 : sdrop (S n) ps = String lbrack (r ++ after))
        by exact (sdrop_succ ps n rbrack _ Hs).
      pose proof (Two lbrack r eq_refl ltac:(rewrite Ht1; reflexivity)) as T2.
      change (Ascii.eqb lbrack lparen) with false in T2. cbn iota in T2.
      set (e := region_end ps n false).
      assert (Ev1 : pstep ps n false (TClose false) v
                    = PView rest' (pv_out v) (PMRegion false (List.rev content) n e "")).
      { rewrite (pstep_close_found ps n false false v content rest' Hpc). unfold e.
        destruct (region_end ps n false); reflexivity. }
      rewrite Ev1 in V1, T2.
      replace (n + 2) with (S (S n)) in T2 by lia.
      set (v1 := PView rest' (pv_out v) (PMRegion false (List.rev content) n e "")) in *.
      assert (U2 : punit ps (S n) false v1 = Some (S (S n), false, pbyte (S n) lbrack v1)).
      { unfold punit. cbn [v1 pv_mode]. rewrite (get_sdrop ps (S n) lbrack _ Hs1). reflexivity. }
      apply (T2 false (pbyte (S n) lbrack v1) (IReference kids false null_span false "" o1) []).
      + exact (pruns_one _ _ _ _ _ _ _ U2).
      + apply (Vb (S n) false v1 lbrack V1). discriminate.
      + exact Hr'.
      + right. intros t p o' E. discriminate E.
      + cbn [wrap]. rewrite (Hcl lbrack (or_intror eq_refl)). apply settles_refl.
      + constructor.
      + unfold linked, pbyte. cbn [v1 pv_mode pv_setmode pv_stk pv_out].
        replace (match e with Some e' => (S n =? e')%nat | None => false end) with false.
        2: { destruct e as [e'|] eqn:Ee; [|reflexivity]. unfold e in Ee.
             pose proof (region_end_bound ps n false e' Ee). symmetry. apply Nat.eqb_neq. lia. }
        rewrite Nat.eqb_refl. cbn [pv_mode].
        split; [lia|]. split; [apply Forall_rev, Cc|]. split; [reflexivity|].
        exists false, "", null_span, cm. split; [reflexivity|]. split; reflexivity. }
    (* a `]` before anything else *)
    apply (Txt (TText rbrack)); try reflexivity;
      [discriminate|rewrite nt_rbrack, S1, S2; reflexivity|].
    intros c0 E0 Hor. exfalso. destruct s' as [|c1 r]; [discriminate|].
    injection E0 as ->. cbn [starts_with] in S1, S2. rewrite S1, S2 in Hor. cbn [orb] in Hor.
    unfold follow_ok in Hf. apply andb_true_iff in Hf as [Hf _].
    apply andb_true_iff in Hf as [_ Hf]. cbn in Hf.
    apply negb_true_iff in Hf. rewrite Hf in Hor. discriminate. }
  assert (CL : forall c0 m, str_last (chars c0 m) (Some c0) = Some c0).
  { intros c0 m. induction m as [|m IHm]; [reflexivity|]. exact IHm. }
  assert (SL : forall k p, str_last (dtoken k) p = Some (dchar k)).
  { intros k p. destruct (dtoken_cons k) as (w & _ & ->). apply CL. }
  destruct (Ascii.eqb c lbrace) eqn:Elb.
  { (* `{`, which a row's character follows *)
    apply Ascii.eqb_eq in Elb. subst c.
    assert (Hrow : starts_row s' = true).
    { unfold follow_ok in Hf. rewrite Ascii.eqb_refl in Hf. cbn in Hf.
      rewrite !andb_true_r in Hf. exact Hf. }
    destruct s' as [|d s'']; [discriminate|].
    cbn [starts_row] in Hrow. unfold is_delim in Hrow.
    destruct (dstyle_of d) as [k|] eqn:Hd; [|discriminate].
    pose proof Hs' as Hd'.
    apply (over_alphabet_cons _ _ (delim_not_bslash d k Hd)) in Hd' as (Hdc & _ & _).
    pose proof (alphabet_self d k Hdc Hd) as Hk.
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
      pose proof Hs' as Hs2. rewrite Es in Hs2.
      apply (over_alphabet_app_r _ _ (no_bslash_dtoken k)) in Hs2.
      apply (Nrm (TDelim k true true false) (S (dwidth k)) rest (Some (dchar k)) ""
               (oopen_marked k (at_rbrace (get 0 rest)) txt o)).
      + rewrite Htok, Es. exact (nt_marked_open k prev rest Hd).
      + intros k' mr op cl E. injection E as <- _ _ _. exact Hk.
      + rewrite Es. reflexivity.
      + cbn [tok_text String.length]. unfold dtoken. rewrite length_append, length_chars.
        reflexivity.
      + cbn [tok_text one append str_last]. rewrite SL. reflexivity.
      + exact Hs2.
      + apply follow_ok_plain; try assumption; exact (proj1 (proj2 (dreserved_false _ (dchar_free k)))).
      + apply tok_marked_open, Hen.
      + reflexivity.
      + apply pstep_mode; [exact Em|discriminate|discriminate].
      + unfold pstep. exact (open_marked_sim ps n k _ txt v o Ok Hsim).
    - (* `{` and a run too short to be a token: text *)
      assert (Ht1 : tok_at ps n = Some (TText lbrace, 1)).
      { rewrite Htok. exact (nt_lbrace_short k j' prev rest0 Hd Hw Hr). }
      pose proof (vinv_step ps n false _ 1 v V Em Ht1 ltac:(discriminate)) as V1.
      cbn [is_hard] in V1. rewrite Nat.add_1_r in V1.
      assert (Hs1 : sdrop (S n) ps = (chars (dchar k) (S j') ++ rest0 ++ after)%string).
      { rewrite (sdrop_succ ps n lbrace _ Hs). cbn [chars append]. rewrite append_assoc.
        reflexivity. }
      assert (Hnl0 : no_char nl_char rest0 = true).
      { cbn [no_char] in Hnl. apply andb_true_iff in Hnl as [_ Hnl].
        change (String (dchar k) (chars (dchar k) j' ++ rest0))
          with (chars (dchar k) (S j') ++ rest0)%string in Hnl.
        rewrite no_char_app in Hnl. apply andb_true_iff in Hnl as [_ Hnl].
        apply andb_true_iff in Hnl as [_ Hnl]. exact Hnl. }
      destruct (run_texts ps k (S j') (S n) (pstep ps n false (TText lbrace) v) (txt ++ one lbrace)
                  o rest0 after Hd Hw Hr Hnl0 Hae Hs1 V1)
        as (v' & R & V' & Em' & S').
      { apply pstep_mode; [exact Em|discriminate|discriminate]. }
      { unfold pstep. apply sim_text; [exact Hsim|reflexivity]. }
      rewrite append_assoc in S'.
      apply (scan_advance ps after len IH _ n false v ws _ (String lbrace (chars (dchar k) (S j')))
               rest0 (Some (dchar k)) [] (IText false (txt ++ String lbrace (chars (dchar k) (S j')))
                                            (Some (dchar k)) o) false v' Hl Hs Fn).
      + reflexivity.
      + discriminate.
      + cbn [String.length]. rewrite length_chars, <- Nat.add_succ_comm.
        apply (pruns_trans ps n false v (S n) false (pstep ps n false (TText lbrace) v));
          [apply pruns_one; rewrite (punit_tok ps n false _ 1 v Em Ht1 (or_intror eq_refl)), Nat.add_1_r; reflexivity|].
        exact R.
      + cbn [String.length]. rewrite length_chars, <- Nat.add_succ_comm. exact V'.
      + rewrite (before_chunk ps n _ (rest0 ++ after)).
        2: { rewrite Hs. cbn [chars append]. rewrite append_assoc. reflexivity. }
        cbn [chars str_last]. rewrite CL. reflexivity.
      + exact (over_alphabet_chars (dchar k) (S j') rest0 (dchar_nb k) Hs').
      + left. apply follow_ok_plain; try assumption; exact (proj1 (proj2 (dreserved_false _ (dchar_free k)))).
      + apply tok_marked_partial; [exact Hen|lia|exact Hnext].
      + constructor.
      + cbn [String.length]. rewrite length_chars, <- Nat.add_succ_comm.
        apply linked_normal; [exact Em'|exact S']. }
  assert (SA : forall a b p, str_last (a ++ b) p = str_last b (str_last a p)).
  { induction a as [|x a IHa]; intros b p; [reflexivity|]. apply IHa. }
  destruct (dstyle_of c) as [k|] eqn:Hd.
  2: { (* a plain byte *)
    apply (Nrm (TText c) 1 s' (Some c) (txt ++ one c) o);
      [rewrite Htok; apply nt_byte;
         [exact (alphabet_nl c Hc)|exact Eb|exact Etk|exact Edl|exact Elk|exact Erk|exact Elb|exact Hd]
      |discriminate|reflexivity|reflexivity|reflexivity|exact Hs'|exact Hf| |reflexivity| |].
    - cbn [iscan_str tok_text one]. unfold istep. cbn [istep_at].
      rewrite (ilead_text c txt prev o Hc Elb Elk Erk Etk Edl Hd Hn). apply settles_refl.
    - apply pstep_mode; [exact Em|discriminate|discriminate].
    - unfold pstep. apply sim_text; [exact Hsim|reflexivity]. }
  pose proof (alphabet_self c k Hc Hd) as Hk.
  pose proof (alphabet_hyphen c Hc) as Hhy.
  pose proof (dstyle_of_enabled c k Hd) as Hen.
  pose proof (dstyle_of_char c k Hd) as Ec. subst c.
  destruct (dchar_plain k) as (Hlbk & Hrbk & Hlkk & Hrkk).
  destruct (run_split (dchar k) s') as (j' & rest0 & -> & Hr).
  assert (Hnext : forall c0, get 0 rest0 = Some c0 -> c0 <> dchar k).
  { intros c0 E0. destruct rest0 as [|d0 r]; [discriminate|]. injection E0 as <-.
    exact (Hr d0 r eq_refl). }
  assert (Hkk : forall mr op cl k' mr' op' cl',
            TDelim k mr op cl = TDelim k' mr' op' cl' -> self_row k' = true)
    by (intros mr op cl k' mr' op' cl' E; injection E as <- _ _ _; exact Hk).
  destruct (Nat.le_gt_cases (dwidth k) (S j')) as [Hw|Hw].
  - (* a whole token *)
    set (rest := (chars (dchar k) (S j' - dwidth k) ++ rest0)%string).
    assert (Es : String (dchar k) (chars (dchar k) j' ++ rest0) = (dtoken k ++ rest)%string).
    { unfold rest, dtoken. rewrite <- append_assoc, <- chars_add.
      replace (dwidth k + (S j' - dwidth k)) with (S j') by lia. reflexivity. }
    clearbody rest.
    rewrite Es in Ha. apply (over_alphabet_app_r _ _ (no_bslash_dtoken k)) in Ha.
    destruct (at_rbrace (get 0 rest)) eqn:Hat.
    + (* a marked closer *)
      destruct rest as [|e0 r]; [discriminate|]. cbn [get at_rbrace] in Hat.
      apply Ascii.eqb_eq in Hat. subst e0.
      destruct (resolve_sim ps n false k true txt prev (Some rbrace) v o Hk Ok Em Hsim)
        as (txt' & o' & Hres & Hsim').
      apply (Nrm (TDelim k true false true) (S (dwidth k)) r (Some rbrace) txt' o').
      * rewrite Htok, Es. exact (nt_marked_close k prev r Hd).
      * apply Hkk.
      * rewrite Es. cbn [tok_text]. rewrite append_assoc. reflexivity.
      * cbn [tok_text]. rewrite length_append. unfold dtoken. rewrite length_chars.
        cbn. lia.
      * cbn [tok_text]. rewrite SA. reflexivity.
      * exact (proj2 (proj2 (over_alphabet_cons rbrace r eq_refl Ha))).
      * reflexivity.
      * cbn [tok_text]. rewrite (tok_marked_close k txt prev o Hen Hhy Hn), Hres.
        apply settles_refl.
      * reflexivity.
      * apply pstep_mode; [exact Em|discriminate|discriminate].
      * exact Hsim'.
    + (* a bare token *)
      destruct (resolve_sim ps n false k false txt prev (get 0 rest) v o Hk Ok Em Hsim)
        as (txt' & o' & Hres & Hsim').
      apply (Nrm (TDelim k false (bare_opens k && nonspace_at (get 0 rest)) (nonspace_at prev))
               (dwidth k) rest (Some (dchar k)) txt' o').
      * rewrite Htok, Es. exact (nt_token k prev rest Hd Hat).
      * apply Hkk.
      * exact Es.
      * cbn [tok_text]. unfold dtoken. rewrite length_chars. reflexivity.
      * cbn [tok_text]. rewrite SL. reflexivity.
      * exact Ha.
      * apply follow_ok_plain; try assumption; exact (proj1 (proj2 (dreserved_false _ (dchar_free k)))).
      * cbn [tok_text]. apply (tok_bare k txt prev o (get 0 rest) txt' o' Hen Hhy Hn); [|exact Hres].
        intros c0 E0. rewrite E0 in Hat. exact Hat.
      * reflexivity.
      * apply pstep_mode; [exact Em|discriminate|discriminate].
      * exact Hsim'.
  - (* a run too short to be a token *)
    assert (Hnl0 : no_char nl_char rest0 = true).
    { change (String (dchar k) (chars (dchar k) j' ++ rest0))
        with (chars (dchar k) (S j') ++ rest0)%string in Hnl.
      rewrite no_char_app in Hnl. apply andb_true_iff in Hnl as [_ Hnl]. exact Hnl. }
    destruct (run_texts ps k (S j') n v txt o rest0 after Hd Hw Hr Hnl0 Hae
                ltac:(rewrite Hs; cbn [chars append]; rewrite append_assoc; reflexivity) V Em Hsim)
      as (v' & R & V' & Em' & S').
    apply (scan_advance ps after len IH _ n false v ws _ (chars (dchar k) (S j'))
             rest0 (Some (dchar k)) [] (IText false (txt ++ chars (dchar k) (S j')) (Some (dchar k)) o)
             false v' Hl Hs Fn).
    + reflexivity.
    + discriminate.
    + rewrite length_chars. exact R.
    + rewrite length_chars. exact V'.
    + rewrite (before_chunk ps n _ (rest0 ++ after)).
      2: { rewrite Hs. cbn [chars append]. rewrite append_assoc. reflexivity. }
      cbn [chars str_last]. rewrite CL. reflexivity.
    + exact (over_alphabet_chars (dchar k) (S j') rest0 (dchar_nb k) Ha).
    + left. apply follow_ok_plain; try assumption; exact (proj1 (proj2 (dreserved_false _ (dchar_free k)))).
    + apply tok_partial; [exact Hen|exact Hhy|exact Hn|lia|exact Hnext].
    + constructor.
    + rewrite length_chars. apply linked_normal; [exact Em'|exact S'].
Qed.

(*
Lines
-----

Between two lines the scanner resolves what is pending as at the end of
a line and takes the break: a soft break in text mode, a byte of the
region in a label or a destination.  That is the view's unit at the
newline.
*)

Local Lemma pv_trim_add_text : forall txt v0, starts_text (top_of v0) = false ->
  pv_trim (add_text txt v0) = add_text (strip_trailing_ws txt) v0.
Proof.
  intros txt [[|f rest] out md] Ht; unfold add_text, top_of in *; cbn [pv_stk] in Ht.
  - destruct (nonempty_str txt) eqn:En.
    + cbn [pv_add pv_stk pv_out pv_trim pv_mode].
      destruct out as [|y out]; [|destruct y; try discriminate Ht];
        cbn [xsnoc xtrim];
        destruct (strip_trailing_ws txt) eqn:Es; reflexivity.
    + destruct txt; [|discriminate]. cbn. unfold pv_trim; cbn.
      destruct out as [|y out]; [reflexivity|destruct y; try discriminate Ht; reflexivity].
  - destruct (nonempty_str txt) eqn:En.
    + cbn [pv_add pv_stk pv_out pv_trim pv_mode].
      destruct f as [p k c|d c]; cbn [fset fcontent] in *;
      (destruct c as [|y c]; [|destruct y; try discriminate Ht]);
        cbn [xsnoc xtrim fset fcontent];
        destruct (strip_trailing_ws txt) eqn:Es; reflexivity.
    + destruct txt; [|discriminate]. cbn. unfold pv_trim; cbn.
      destruct f as [p k c|d c]; cbn [fset fcontent] in *;
        (destruct c as [|y c]; [reflexivity|destruct y; try discriminate Ht; reflexivity]).
Qed.

Local Lemma ibreak_pending : forall ws0 txt p o,
  ibreak (esc_pending ws0 txt p o) = IText false "" None (oword_reset (iesc_hard ws0 txt o)).
Proof. intros [|w ws] txt p o; reflexivity. Qed.

Local Lemma ifinish_pending : forall ws0 txt p o,
  ifinish (esc_pending ws0 txt p o) = ifinish (IText false "" None (iesc_hard ws0 txt o)).
Proof. intros [|w ws] txt p o; reflexivity. Qed.

Local Lemma ifinish_ref_esc : forall kids im open label o,
  ifinish (IReference kids im open true label o)
  = ifinish (IReference kids im open false (label ++ one bslash) o).
Proof.
  intros. unfold ifinish, ifinish_rev. cbn [ifinish_ostate iresolve ifinish_ostate_flat]. tred.
  rewrite append_empty_r. reflexivity.
Qed.

Local Lemma blank_not_row : forall w, is_blank w = true -> starts_row w = false.
Proof.
  intros [|c w] H; [reflexivity|]. cbn [is_blank] in H.
  apply andb_true_iff in H as [Hc _]. cbn [starts_row]. unfold is_delim.
  destruct (dstyle_of c) as [k|] eqn:Hd; [|reflexivity].
  apply dstyle_of_char in Hd. subst c.
  rewrite (is_punct_not_ws _ (dchar_punct k)) in Hc. discriminate.
Qed.

(* Whitespace ends a raw spec's format, so trailing blanks do not change
   what a spec reads. *)
Local Lemma raw_spec_blank : forall a b, is_blank b = true -> raw_spec (a ++ b) = raw_spec a.
Proof.
  intros a b Hb.
  assert (Hw : forall c b', b = String c b' -> is_ws c = true /\ Ascii.eqb c rbrace = false
                                               /\ Ascii.eqb c lbrace = false
                                               /\ Ascii.eqb c eqchar = false).
  { intros c b' ->. cbn [is_blank] in Hb. apply andb_true_iff in Hb as [Hc _].
    split; [exact Hc|].
    destruct c as [[] [] [] [] [] [] [] []]; try discriminate Hc; repeat split; reflexivity. }
  assert (F : forall r, fmt_go (r ++ b) = fmt_go r).
  { induction r as [|x r IH].
    - destruct b as [|c b']; [reflexivity|]. destruct (Hw c b' eq_refl) as (Hc & Hr & _ & _).
      cbn [append fmt_go]. rewrite Hr. unfold raw_stop. rewrite Hc. reflexivity.
    - cbn [append fmt_go]. rewrite IH. reflexivity. }
  destruct a as [|x [|e r]].
  - destruct b as [|c b']; [reflexivity|]. destruct (Hw c b' eq_refl) as (_ & _ & Hl & _).
    destruct b'; cbn [append raw_spec]; [reflexivity|]. rewrite Hl. reflexivity.
  - destruct b as [|c b']; [reflexivity|]. destruct (Hw c b' eq_refl) as (_ & _ & _ & He).
    cbn [append raw_spec]. rewrite He, andb_false_r. reflexivity.
  - cbn [append raw_spec]. rewrite F. reflexivity.
Qed.

Local Lemma over_alphabet_app_l : forall a b,
  over_alphabet (a ++ b) = true -> is_blank b = true -> over_alphabet a = true.
Proof.
  intros a b. remember (String.length a) as m eqn:Em. revert a Em.
  induction m as [m IH] using lt_wf_ind. intros a Em H Hb.
  destruct a as [|c a]; [reflexivity|].
  destruct (is_bslash c) eqn:Eb.
  - unfold is_bslash in Eb. apply Ascii.eqb_eq in Eb. subst c.
    destruct a as [|d a]; [reflexivity|].
    cbn [append over_alphabet] in H. change (is_bslash bslash) with true in H. cbn iota in H.
    apply andb_true_iff in H as [Hd H]. apply andb_true_iff in Hd as [Hn Ht].
    cbn [over_alphabet]. change (is_bslash bslash) with true. cbn iota. rewrite Hn.
    unfold raw_ahead in Ht. rewrite (raw_spec_blank a b Hb) in Ht.
    replace (negb (is_tick d && starts_with lbrace a && negb (raw_ahead a))) with true
      by (destruct a; [cbn [starts_with]; rewrite andb_false_r; reflexivity|exact (eq_sym Ht)]).
    apply (IH (String.length a)); [cbn in Em; lia|reflexivity|exact H|exact Hb].
  - cbn [append] in H. apply (over_alphabet_cons c _ Eb) in H as (Hc & Hf & H).
    cbn [over_alphabet]. rewrite Eb, Hc.
    rewrite (IH (String.length a) ltac:(cbn in Em; lia) a eq_refl H Hb), andb_true_r. cbn [andb].
    destruct a as [|d a].
    + cbn [append] in Hf. unfold follow_ok in *. rewrite (blank_not_row b Hb) in Hf.
      apply andb_true_iff in Hf as [Hf _]. apply andb_true_iff in Hf as [Hf _].
      apply andb_true_iff in Hf as [Hf _].
      cbn. rewrite Hf, !andb_false_r. reflexivity.
    + unfold follow_ok, raw_ahead in *. rewrite (raw_spec_blank (String d a) b Hb) in Hf.
      exact Hf.
Qed.

Local Lemma over_alphabet_strip : forall x,
  over_alphabet x = true -> over_alphabet (strip_trailing_ws x) = true.
Proof.
  intros x Ha. destruct (strip_trailing_split x) as (w & Hw & E).
  rewrite E in Ha. exact (over_alphabet_app_l _ w Ha Hw).
Qed.

(* The newline after a line.  A verbatim the paragraph ends in may end
   at a newline before an empty last line. *)
Local Lemma break_linked : forall ps n h v prev core r,
  sdrop n ps = String nl_char r -> vinv ps n h v -> linked_end ps n h v prev core ->
  exists h' v', punit ps n h v = Some (S n, h', v') /\ vinv ps (S n) h' v'
    /\ ((linked ps (S n) h' v' None (ibreak core) /\ pend_esc (ibreak core) = false)
        \/ (sdrop (S n) ps = EmptyString /\ vpending ps (S n) h' v' (ibreak core))).
Proof.
  intros ps n h v prev core r Hs V LE.
  assert (Ht : tok_at ps n = Some (TBreak, 1)) by (unfold tok_at; rewrite Hs; reflexivity).
  pose proof (get_sdrop ps n nl_char r Hs) as Hg.
  pose proof V as (Ok & Ti & Hh).
  destruct LE as [L|[P|VP]].
  3: { (* a verbatim that ended the line *)
       destruct VP as (x & v0 & cm & -> & Em0 & -> & Hx & [(dd & m & body & -> & ->)|(Hs0 & _)]);
         [|rewrite Hs in Hs0; discriminate].
       set (v := pv_add (verb_node dd None body) v0) in *.
       assert (Em : pv_mode v = PMNormal)
         by (unfold v; rewrite (proj2 (pv_add_live _ _)); exact Em0).
       exists false, (pv_add SoftBreak v).
       split; [rewrite (punit_tok ps n false TBreak 1 v Em Ht (or_intror eq_refl)), Nat.add_1_r; reflexivity|].
       split; [pose proof (vinv_step ps n false TBreak 1 v V Em Ht ltac:(discriminate)) as V1;
               rewrite Nat.add_1_r in V1; exact V1|].
       assert (E : ibreak (IVerb m m body (vkind_of dd) (oview cm v0))
                   = IText false "" None (oview cm (pv_add SoftBreak v))).
       { unfold ibreak. cbn [ibreak_at iresolve ibreak_flat]. rewrite Nat.eqb_refl.
         change (imk_here SoftBreak) with (mk SoftBreak).
         change (tval body) with body. rewrite vnode_of.
         change (imk (text_start (oview cm v0)) cursor_start (verb_node dd None body))
           with (mk (verb_node dd None body)).
         rewrite (oemit_view cm _ v0) by exact Hx. fold v.
         rewrite (oemit_view cm SoftBreak v) by discriminate. reflexivity. }
       left. rewrite E. split; [|reflexivity].
       apply linked_normal; [rewrite (proj2 (pv_add_live _ _)); exact Em|].
       exists (pv_add SoftBreak v), cm.
       split; [reflexivity|]. split; [apply top_add_nonstr; discriminate|reflexivity]. }
  2: { (* the hard break the line ended with *)
       destruct P as (ws0 & txt & p & o & vb & -> & Hb & -> & Emb & Hsim & ->).
       destruct Hsim as (v0 & cm & -> & Ht0 & ->).
       set (v := pv_add HardBreak (pv_trim (add_text txt v0))) in *.
       assert (Em : pv_mode v = PMNormal)
         by (unfold v; rewrite (proj2 (pv_add_live _ _)), (proj2 (pv_trim_live _)); exact Emb).
       exists false, v.
       split; [rewrite (punit_tok ps n true TBreak 1 v Em Ht (or_intror eq_refl)), Nat.add_1_r; reflexivity|].
       split; [pose proof (vinv_step ps n true TBreak 1 v V Em Ht ltac:(discriminate)) as V1;
               rewrite Nat.add_1_r in V1; exact V1|].
       assert (E : ibreak (esc_pending ws0 txt p (oview cm v0))
                   = IText false "" None (oview cm v)).
       { unfold v. rewrite (pv_trim_add_text txt v0 Ht0).
         assert (X : iesc_hard ws0 txt (oview cm v0)
                     = oview cm (pv_add HardBreak (add_text (strip_trailing_ws txt) v0))).
         { unfold iesc_hard. tred.
           change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s
                     (strip_trailing_ws txt) (oview cm v0))
             with (flush_text (strip_trailing_ws txt) (oview cm v0)).
           rewrite (flush_view cm _ v0 Ht0). rewrite imk_here_semantic.
           apply oemit_view. discriminate. }
         rewrite ibreak_pending, X. reflexivity. }
       left. rewrite E. split; [|reflexivity]. apply linked_normal; [exact Em|].
       exists v, cm. split; [reflexivity|]. split; [apply top_add_nonstr; discriminate|reflexivity]. }
  unfold linked in L. destruct (pv_mode v) as [|[|] kids d e txt|x e] eqn:Em.
  - (* text mode: a soft break *)
    destruct L as (-> & txt & o & -> & Hsim). destruct Hsim as (v0 & cm & -> & Ht0 & Ev).
    exists false, (pv_add SoftBreak v).
    split; [rewrite (punit_tok ps n false TBreak 1 v Em Ht (or_intror eq_refl)), Nat.add_1_r; reflexivity|].
    split; [pose proof (vinv_step ps n false TBreak 1 v V Em Ht ltac:(discriminate)) as V1;
            rewrite Nat.add_1_r in V1; exact V1|].
    assert (E : ibreak (IText false txt prev (oview cm v0))
                = IText false "" None (oview cm (pv_add SoftBreak v))).
    { unfold ibreak, ibreak_at, ibreak_flat. cbn [iresolve].
      change (@flush_text_at semantic_pos semantic_inline_cursor (tval txt) (oview cm v0))
        with (flush_text txt (oview cm v0)).
      rewrite (flush_view cm txt v0 Ht0), <- Ev.
      change (imk_here SoftBreak) with (mk SoftBreak).
      rewrite (oemit_view cm SoftBreak v) by discriminate. reflexivity. }
    left. rewrite E. split; [|reflexivity].
    apply linked_normal; [rewrite (proj2 (pv_add_live _ _)); exact Em|].
    exists (pv_add SoftBreak v), cm.
    split; [reflexivity|]. split; [apply top_add_nonstr; discriminate|reflexivity].
  - (* a destination: the newline is one of its bytes *)
    destruct L as (Hd & -> & open & sh & cm & [e0 dp dst] & Hds & He & Hne & ->).
    cbn [ds_esc ds_depth ds_dst] in *.
    exists false, (pbyte n nl_char v).
    split; [unfold punit; rewrite Em, Hg; reflexivity|].
    split; [split; [apply pv_ok_byte; [exact Ok|rewrite Em; discriminate]|];
            split; [apply pbyte_tidy, Ti|discriminate]|].
    set (ds' := DS false dp (dst ++ if e0 then String bslash (one nl_char) else one nl_char)).
    assert (Hst : dstep nl_char (DS e0 dp dst) = Some ds') by (destruct e0; reflexivity).
    rewrite Hs, (dest_close_step nl_char r e0 dp dst ds' n Hst) in He.
    pose proof (sdrop_succ ps n nl_char r Hs) as Hs1.
    left. split; [|reflexivity].
    unfold linked, pbyte. rewrite Em.
    replace (match e with Some e' => (n =? e')%nat | None => false end) with false.
    2: { destruct e as [e'|]; [|reflexivity]. symmetry in He. apply dest_close_bound in He.
         symmetry. apply Nat.eqb_neq. lia. }
    replace (n =? S d)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    cbn [pv_mode pv_setmode]. split; [lia|]. split; [reflexivity|].
    exists open, (ibreak sh), cm, ds'. split; [|split; [|split]].
    + rewrite dfeed_app, Hds. cbn [one dfeed]. rewrite Hst. reflexivity.
    + rewrite Hs1. exact He.
    + exact Hne.
    + unfold ibreak at 1, ibreak_at at 1. tred. unfold ds'. cbn [ds_esc ds_depth ds_dst].
      destruct e0; reflexivity.
  - (* a reference label: likewise *)
    destruct L as (Hd & Hk & -> & esc & label' & open & cm & He & Hl & ->).
    exists false, (pbyte n nl_char v).
    split; [unfold punit; rewrite Em, Hg; reflexivity|].
    split; [split; [apply pv_ok_byte; [exact Ok|rewrite Em; discriminate]|];
            split; [apply pbyte_tidy, Ti|discriminate]|].
    rewrite Hs in He.
    pose proof (sdrop_succ ps n nl_char r Hs) as Hs1.
    assert (He' : e = label_close false (S n) (sdrop (S n) ps))
      by (rewrite Hs1, He; destruct esc; reflexivity).
    left. split; [|reflexivity].
    unfold linked, pbyte. rewrite Em.
    replace (match e with Some e' => (n =? e')%nat | None => false end) with false.
    2: { destruct e as [e'|]; [|reflexivity]. symmetry in He'. apply label_close_bound in He'.
         symmetry. apply Nat.eqb_neq. lia. }
    replace (n =? S d)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    cbn [pv_mode pv_setmode]. split; [lia|]. split; [exact Hk|]. split; [reflexivity|].
    exists false, (label' ++ (if esc then one bslash else "") ++ nl)%string, open, cm.
    split; [exact He'|]. split.
    + subst txt. rewrite append_empty_r, append_assoc. reflexivity.
    + unfold ibreak at 1, ibreak_at at 1. tred. reflexivity.
  - (* inside a verbatim: the newline is one of its bytes *)
    destruct L as (-> & Hne & p & pre & m & body & cl & rw & txt0 & prev0 & o0 & Hp & Htv & -> & Hsim
                   & -> & Hvs).
    rewrite Hg in Hvs.
    destruct (ibreak_verb _ Hvs) as [Eb Pe].
    destruct (verb_tok_scan ps p pre m body cl rw (S e - p) txt0 prev0 o0 Htv) as (T1 & T2 & Traw & T3).
    pose proof (tok_at_len ps p _ _ Htv) as [_ Hle].
    pose proof (tok_verb_width ps p pre m body cl rw _ Htv) as Hm.
    set (X0 := IText false txt0 prev0 o0) in *.
    assert (Step : istep nl_char (iscan_str (substring p (n - p) ps) X0)
                   = iscan_str (substring p (S n - p) ps) X0).
    { replace (S n - p) with (S (n - p)) by lia.
      rewrite (substring_snoc ps p (n - p) nl_char)
        by (replace (p + (n - p)) with n by lia; exact Hg).
      rewrite iscan_str_app. reflexivity. }
    rewrite Step in Eb. rewrite Eb in Pe |- *.
    exists false, (pbyte n nl_char v).
    split; [unfold punit; rewrite Em, Hg; reflexivity|].
    split; [split; [apply pv_ok_byte; [exact Ok|rewrite Em; discriminate]|];
            split; [apply pbyte_tidy, Ti|discriminate]|].
    destruct (Nat.eqb n e) eqn:Ene.
    2: { apply Nat.eqb_neq in Ene.
      assert (Pb : pbyte n nl_char v = v)
        by (unfold pbyte; rewrite Em; apply Nat.eqb_neq in Ene; rewrite Ene; reflexivity).
      left. split; [|exact Pe]. rewrite Pb.
      unfold linked. rewrite Em. split; [reflexivity|]. split; [lia|].
      exists p, pre, m, body, cl, rw, txt0, prev0, o0. split; [lia|]. split; [exact Htv|].
      split; [reflexivity|]. split; [exact Hsim|]. split; [reflexivity|].
      replace (S n) with (p + (S n - p)) at 2 by lia. apply T1. lia. }
    (* the verbatim's last byte: it never closed, and the last line is empty *)
    apply Nat.eqb_eq in Ene. subst e.
    destruct rw as [f|].
    { exfalso. destruct (Traw f eq_refl) as (_ & _ & _ & Ec). rewrite <- Step in Ec.
      exact (verb_nl_not_text _ _ _ _ Hvs Ec). }
    destruct cl.
    { exfalso. destruct (T2 eq_refl eq_refl) as [Ec _]. rewrite <- Step in Ec.
      pose proof (verb_last_tick _ _ _ _ _ _ Hvs Ec Hm) as E. discriminate E. }
    destruct (T3 eq_refl) as (_ & Elen & Efin).
    destruct Hsim as (v0 & cm & Eo & Ht0 & Ev).
    set (vN := pv_setmode PMNormal v) in *.
    assert (Fl : flush_text (txt0 ++ chars dollar (pre - 2)) o0 = oview cm vN) by (rewrite Eo, Ev; apply flush_view, Ht0).
    assert (Pb : pbyte n nl_char v = pv_add (verb_node pre None body) vN)
      by (unfold pbyte; rewrite Em, Nat.eqb_refl; reflexivity).
    assert (EmN : pv_mode vN = PMNormal) by (unfold vN; destruct v; reflexivity).
    pose proof (sdrop_succ ps n nl_char r Hs) as Hs1.
    assert (Hr : r = EmptyString).
    { assert (L1 : String.length (sdrop n ps) = 1) by (rewrite sdrop_length; lia).
      rewrite Hs in L1. destruct r; [reflexivity|cbn in L1; lia]. }
    subst r. right. split; [exact Hr|]. rewrite Pb.
    exists (verb_node pre None body), vN, cm.
    split; [reflexivity|]. split; [exact EmN|]. split; [reflexivity|].
    split; [intros s0; apply verb_node_nonstr|]. right. split; [exact Hr|].
    rewrite Efin, Fl, (oemit_view cm _ vN) by (intros s0; apply verb_node_nonstr). reflexivity.
Qed.

Local Lemma ifinish_verb : forall d m body cm v0,
  ifinish (IVerb m m body (vkind_of d) (oview cm v0))
  = ifinish (IText false "" None (oview cm (pv_add (verb_node d None body) v0))).
Proof.
  intros d m body cm v0. unfold ifinish, ifinish_rev.
  cbn [ifinish_ostate iresolve ifinish_ostate_flat]. rewrite Nat.eqb_refl.
  change (tval body) with body. rewrite vnode_of.
  change (imk (text_start (oview cm v0)) cursor_start (verb_node d None body))
    with (mk (verb_node d None body)).
  rewrite (oemit_view cm _ v0) by (intros s0; apply verb_node_nonstr). reflexivity.
Qed.

(* The paragraph's end, in a linked state or one a hard break or a
   verbatim left. *)
Local Lemma linked_finish : forall ps n h v ws prev core,
  vinv ps n h v -> linked_end ps n h v prev core -> sdrop n ps = EmptyString ->
  ifinish (wrap ws core) = map mk (List.rev (pflatten v)).
Proof.
  intros ps n h v ws prev core (Ok & Ti & _) [L|[P|VP]] Hs; pose proof Ok as (_ & _ & _ & B & _);
    rewrite ifinish_wrap.
  - unfold linked in L.
    destruct (pv_mode v) as [|[|] kids d e txt|x e] eqn:Em.
    + destruct L as (_ & txt & o & -> & Hsim). rewrite (sim_finish v txt prev o Hsim B).
      unfold pflatten, pfinish. rewrite Em. reflexivity.
    + (* a destination closes before the end *)
      destruct L as (_ & _ & open & sh & cm & ds & _ & He & Hne & _).
      rewrite Hs in He. destruct (ds_esc ds); cbn in He; contradiction.
    + (* a label the paragraph ends in *)
      destruct L as (_ & Hk & _ & esc & label' & open & cm & He & Hl & ->).
      rewrite Hs in He. assert (e = None) as -> by (destruct esc; exact He).
      destruct (tidy_top v Ti) as [Hn Hc].
      destruct esc.
      * rewrite ifinish_ref_esc. rewrite Hl in Em.
        exact (ref_finish cm v false kids d open (label' ++ one bslash) Em B Hn Hc Hk).
      * rewrite append_empty_r in Hl. subst txt.
        exact (ref_finish cm v false kids d open label' Em B Hn Hc Hk).
    + (* a verbatim covers a byte past the end *)
      destruct L as (_ & Hne & p & pre & m & body & cl & rw & _ & _ & _ & _ & Htv & _).
      pose proof (tok_at_len ps p _ _ Htv) as [_ Hle].
      pose proof (sdrop_length n ps) as L0. rewrite Hs in L0. cbn in L0. lia.
  - destruct P as (ws0 & txt & p & o & vb & _ & _ & -> & Emb & Hsim & ->).
    rewrite ifinish_pending. destruct Hsim as (v0 & cm & -> & Ht & ->).
    set (v := pv_add HardBreak (pv_trim (add_text txt v0))) in *.
    assert (X : iesc_hard ws0 txt (oview cm v0) = oview cm v).
    { unfold v. rewrite (pv_trim_add_text txt v0 Ht). unfold iesc_hard. tred.
      change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s
                (strip_trailing_ws txt) (oview cm v0))
        with (flush_text (strip_trailing_ws txt) (oview cm v0)).
      rewrite (flush_view cm _ v0 Ht). rewrite imk_here_semantic.
      apply oemit_view. discriminate. }
    rewrite X. rewrite (sim_finish v "" None (oview cm v)).
    + unfold pflatten, pfinish, v. rewrite (proj2 (pv_add_live _ _)), pv_trim_add, Emb. reflexivity.
    + exists v, cm. split; [reflexivity|]. split; [apply top_add_nonstr; discriminate|reflexivity].
    + exact B.
  - destruct VP as (x & v0 & cm & _ & Em0 & -> & Hx & Hc).
    assert (F : ifinish core = ifinish (IText false "" None (oview cm (pv_add x v0))))
      by (destruct Hc as [(dd & m & body & -> & ->)|(_ & F)]; [apply ifinish_verb|exact F]).
    rewrite F, (sim_finish (pv_add x v0) "" None (oview cm (pv_add x v0))).
    + unfold pflatten, pfinish. rewrite (proj2 (pv_add_live _ _)), Em0. reflexivity.
    + exists (pv_add x v0), cm. split; [reflexivity|].
      split; [apply top_add_nonstr; exact Hx|reflexivity].
    + exact B.
Qed.

Local Lemma scan_lines_sim : forall ps ls n h v ws core,
  Forall (fun x => over_alphabet x = true) ls ->
  sdrop n ps = para_string ls -> nonspace_at (before ps n) = false ->
  vinv ps n h v -> Forall (never ps n) ws -> linked ps n h v None core -> pend_esc core = false ->
  exists h' v', pruns ps n h v (n + String.length (para_string ls)) h' v'
    /\ ifinish (iscan_lines ls (wrap ws core)) = map mk (List.rev (pflatten v')).
Proof.
  intros ps ls. induction ls as [|x rest IH]; intros n h v ws core Ha Hs Hb V Fn L Pe.
  - exists h, v. cbn [para_string String.length iscan_lines]. rewrite Nat.add_0_r.
    split; [constructor|]. exact (linked_finish ps n h v ws None core V (or_introl L) Hs).
  - apply Forall_cons_iff in Ha as [Hx Ha].
    destruct rest as [|y rest'].
    + (* the last line, without its trailing whitespace *)
      cbn [para_string iscan_lines] in *.
      set (s := strip_trailing_ws x) in *.
      destruct (scan_sim ps "" (or_introl eq_refl) (String.length s) s None n h v ws core (le_n _))
        as (ws' & core' & prev' & h' & v' & E & R & V' & Fn' & L');
        [apply alpha_of; rewrite Pe; exact (over_alphabet_strip x Hx)|left; reflexivity
        |rewrite append_empty_r; exact Hs|rewrite Hb; reflexivity|exact V|exact Fn|exact L|].
      exists h', v'. split; [exact R|].
      rewrite <- ifinish_rres, E.
      apply (linked_finish ps _ h' v' ws' prev' core' V' L').
      rewrite <- (append_empty_r s) in Hs. exact (sdrop_app_tail ps n s "" Hs).
    + (* a line, the break, and the lines after it *)
      change (para_string (x :: y :: rest'))
        with (x ++ String nl_char (para_string (y :: rest')))%string in *.
      change (iscan_lines (x :: y :: rest') (wrap ws core))
        with (iscan_lines (y :: rest') (ibreak (iscan_str x (wrap ws core)))).
      destruct (scan_sim ps (String nl_char (para_string (y :: rest')))
                  (or_intror (ex_intro _ _ eq_refl)) (String.length x) x None n h v ws core (le_n _))
        as (ws' & core' & prev' & h' & v' & E & R & V' & Fn' & L');
        [apply alpha_of; rewrite Pe; exact Hx|left; reflexivity|exact Hs|rewrite Hb; reflexivity
        |exact V|exact Fn|exact L|].
      set (m := n + String.length x) in *.
      pose proof (sdrop_app_tail ps n x _ Hs) as Hsm. fold m in Hsm.
      destruct (break_linked ps m h' v' prev' core' _ Hsm V' L') as (h2 & v2 & U & V2 & LB).
      destruct (layers_pass ps m ws' (one nl_char) (para_string (y :: rest')) Fn' Hsm) as [_ Fn2].
      cbn [String.length one] in Fn2. rewrite Nat.add_1_r in Fn2.
      unfold ibreak at 1. rewrite <- ibreak_rres, E. fold (ibreak (wrap ws' core')).
      rewrite ibreak_wrap.
      assert (R2 : forall h3 v3,
                 pruns ps (S m) h2 v2 (S m + String.length (para_string (y :: rest'))) h3 v3 ->
                 pruns ps n h v
                   (n + String.length (x ++ String nl_char (para_string (y :: rest')))) h3 v3).
      { intros h3 v3 R3. rewrite length_append. cbn [String.length].
        replace (n + (String.length x + S (String.length (para_string (y :: rest')))))
          with (S m + String.length (para_string (y :: rest'))) by (unfold m; lia).
        apply (pruns_trans ps n h v m h' v'); [exact R|].
        apply (pruns_step ps m h' v' (S m) h2 v2); [exact U|exact R3]. }
      pose proof (sdrop_succ ps m nl_char _ Hsm) as Hs1.
      destruct LB as [[L2 Pe2]|[Hs2 VP2]].
      * destruct (IH (S m) h2 v2 (map (wl_after nl) ws') (ibreak core') Ha Hs1
                    ltac:(rewrite (before_sdrop ps m nl_char _ Hsm); reflexivity)
                    V2 Fn2 L2 Pe2)
          as (h3 & v3 & R3 & E3).
        exists h3, v3. split; [exact (R2 h3 v3 R3)|exact E3].
      * (* a verbatim the paragraph ends in, before an empty last line *)
        rewrite Hs2 in Hs1. symmetry in Hs1.
        destruct rest' as [|z rest''];
          [|cbn [para_string] in Hs1; destruct y; discriminate].
        exists h2, v2. split.
        -- apply R2. rewrite Hs1. rewrite Nat.add_0_r. constructor.
        -- cbn [iscan_lines]. cbn [para_string] in Hs1. rewrite Hs1. cbn [iscan_str].
           exact (linked_finish ps (S m) h2 v2 _ None (ibreak core') V2 (or_intror (or_intror VP2))
                    Hs2).
Qed.

(*
The theorem
===========

On a paragraph over the alphabet, the scanner builds the tree of the
unique reading the precedence rules allow. *)

Local Lemma vinv_start : forall ps, vinv ps 0 false pv0.
Proof.
  intros ps. split; [|split; [|intros H; discriminate H]].
  - split; [constructor|]. split; [intros x []|]. split; [intros p k c []|].
    split; [constructor|]. split; [constructor|]. split; [intros p k c []|exact Logic.I].
  - split; [exact Logic.I|]. split; [constructor|]. split; [constructor|].
    split; [constructor|exact Logic.I].
Qed.

Local Lemma linked_start : forall ps, linked ps 0 false pv0 None istart.
Proof.
  intros ps. split; [reflexivity|]. exists "", ostart. split; [reflexivity|].
  exists pv0, (fun _ => false). split; [reflexivity|]. split; reflexivity.
Qed.

(* A paragraph: its lines, each over the alphabet, read as one string with
   a newline between two of them and the last without its trailing
   whitespace. *)
Theorem para_inlines_matching : forall ls,
  Forall (fun x => over_alphabet x = true) ls ->
  para_inlines ls = tree_of (para_string ls) (fst (ref_read (para_string ls))).
Proof.
  intros ls Ha. unfold para_inlines.
  destruct (scan_lines_sim (para_string ls) ls 0 false pv0 [] istart Ha eq_refl eq_refl
              (vinv_start _) (Forall_nil _) (linked_start _) eq_refl) as (h' & v' & R & E).
  cbn [wrap] in E. rewrite E. symmetry. apply (tree_of_pruns _ h'). exact R.
Qed.

(* The same in the reference's terms: the paragraph is the tree of any
   reading the precedence rules allow (P1, P3, P4, P5), since there is
   one. *)

Local Lemma tree_of_members : forall s m1 m2,
  (forall i j, In (i, j) m1 <-> In (i, j) m2) -> tree_of s m1 = tree_of s m2.
Proof.
  intros s m1 m2 E.
  assert (Eo : forall i, is_opener m1 i = is_opener m2 i).
  { intros i. apply Bool.eq_true_iff_eq. rewrite !is_opener_iff.
    split; intros [j H]; exists j; apply E; exact H. }
  assert (Ec : forall i, is_closer m1 i = is_closer m2 i).
  { intros i. apply Bool.eq_true_iff_eq. rewrite !is_closer_iff.
    split; intros [j H]; exists j; apply E; exact H. }
  assert (En : forall p, chain_next s m1 p = chain_next s m2 p)
    by (intros p; unfold chain_next; rewrite Ec; reflexivity).
  unfold tree_of. f_equal.
  generalize 0 as i. generalize false as h. generalize ([] : tframes) as fs.
  generalize ([] : inlines) as top. generalize (S (String.length s)) as f.
  induction f as [|f IH]; intros top fs h i; cbn [tgo]; [reflexivity|].
  destruct (tok_of s i) as [t|]; [|reflexivity].
  replace (tstep s m1 i t h fs top) with (tstep s m2 i t h fs top).
  2: { unfold tstep. destruct t; rewrite ?Eo, ?Ec; reflexivity. }
  rewrite En. destruct (tstep s m2 i t h fs top) as [fs' top'].
  destruct (chain_next s m2 i); [apply IH|reflexivity].
Qed.

Corollary para_inlines_valid : forall ls m os,
  Forall (fun x => over_alphabet x = true) ls -> valid (para_string ls) (m, os) ->
  para_inlines ls = tree_of (para_string ls) m.
Proof.
  intros ls m os Ha Hv. rewrite (para_inlines_matching ls Ha).
  apply tree_of_members.
  pose proof (ref_read_valid (para_string ls)) as Hr.
  destruct (ref_read (para_string ls)) as [m0 os0].
  exact (proj1 (valid_unique _ _ _ _ _ Hr Hv)).
Qed.

End WithTable.
