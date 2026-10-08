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

(* `rstep`, keeping the content. *)
Definition pstep (ts : list token) (i : nat) (t : token) (v : pview) : pview :=
  match pv_mode v with
  | PMRegion b kids d e txt =>
      if match e with Some e' => Nat.eqb i e' | None => false end
      then pv_add (region_node b (map mk kids) txt) (pv_setmode PMNormal v)
      else pv_setmode (PMRegion b kids d e
                         (if Nat.eqb i (S d) then txt else (txt ++ tok_region b t)%string)) v
  | PMNormal =>
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
      | TBreak => if after_hard ts i then v else pv_add SoftBreak v
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
  destruct t as [c| |k mr op cl| |b|c|ws|ws]; try apply Add; [| | | | |].
  - (* a break: nothing after a hard break *)
    destruct (after_hard ts n); [|apply Add].
    split; [exact Hl|rewrite Ev; reflexivity].
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
  - (* an escaped whitespace run *)
    destruct (nbsp_rest ws) as [r|]; [|apply Add].
    destruct (nonempty_str r); [|apply Add].
    destruct (pv_add_live (Str r) (pv_add NonBreakingSpace v)) as [E1 E2].
    rewrite E1, E2. apply Add.
  - (* a hard break *)
    destruct (pv_trim_live v) as [T1 T2].
    destruct (pv_add_live HardBreak (pv_trim v)) as [E1 E2].
    rewrite E1, E2, T1, T2, Ev. split; [exact Hl|reflexivity].
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
  destruct t as [c| |k mr op cl| |b|c|ws|ws].
  - unfold v. cbn [tstep pstep pv_mode]. fold v. apply Str_.
  - unfold v. cbn [tstep pstep pv_mode]. fold v.
    destruct (after_hard ts n).
    + unfold vembed, tembed, v. cbn [pv_stk pv_out pv_mode membed]. fold real.
      rewrite Ec. reflexivity.
    + rewrite Emb.
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
  - (* an escape is text *)
    unfold v. cbn [tstep pstep pv_mode]. fold v. apply Str_.
  - (* an escaped whitespace run: a non-breaking space and the rest of
       the run, or text *)
    unfold v. cbn [tstep pstep pv_mode]. fold v.
    destruct (nbsp_rest ws) as [r|]; [|apply Str_].
    change (map (fun f : tkind * list inline => (fst f, map mk (snd f))) fs0)
      with (fst (tfr (fs0, top0))).
    change (map mk top0) with (snd (tfr (fs0, top0))).
    rewrite temit_embed.
    assert (Nb : vembed real (pv_add NonBreakingSpace v)
                 = (fst (tfr (xinner (cons NonBreakingSpace) (fs0, top0))),
                    snd (tfr (xinner (cons NonBreakingSpace) (fs0, top0))), TMNormal)).
    { rewrite Emb. rewrite (xinner_ext (xsnoc _) (cons NonBreakingSpace))
        by (intros l; apply xsnoc_nonstr; discriminate). reflexivity. }
    destruct (nonempty_str r).
    + rewrite vembed_add, collapse_add. cbn [pv_add pv_stk pv_out pv_mode].
      unfold v. cbn [pv_stk pv_out pv_mode membed]. fold real. rewrite Ec.
      rewrite (xinner_ext (xsnoc NonBreakingSpace) (cons NonBreakingSpace))
        by (intros l; apply xsnoc_nonstr; discriminate).
      rewrite (proj2 (pv_add_live NonBreakingSpace _)). cbn [pv_mode membed].
      destruct (xinner (cons NonBreakingSpace) (fs0, top0)) as [fs1 top1] eqn:E1.
      cbn [tfr fst snd].
      change (map (fun f : tkind * list inline => (fst f, map mk (snd f))) fs1)
        with (fst (tfr (fs1, top1))).
      change (map mk top1) with (snd (tfr (fs1, top1))).
      rewrite temit_str_embed. reflexivity.
    + rewrite Nb. reflexivity.
  - (* a hard break, after the text before it is trimmed *)
    unfold v. cbn [tstep pstep pv_mode]. fold v.
    change (map (fun f : tkind * list inline => (fst f, map mk (snd f))) fs0)
      with (fst (tfr (fs0, top0))).
    change (map mk top0) with (snd (tfr (fs0, top0))).
    rewrite ttrim_embed.
    destruct (tfr (xinner xtrim (fs0, top0))) as [fs1 top1] eqn:E1.
    unfold tnormal. cbn [fst snd].
    rewrite vembed_add, pv_trim_add, collapse_trim. unfold v. cbn [pv_stk pv_out pv_mode membed].
    fold real. rewrite Ec.
    rewrite (xinner_ext (xsnoc _) (cons HardBreak))
      by (intros l; apply xsnoc_nonstr; discriminate).
    replace fs1 with (fst (tfr (xinner xtrim (fs0, top0)))) by (rewrite E1; reflexivity).
    replace top1 with (snd (tfr (xinner xtrim (fs0, top0)))) by (rewrite E1; reflexivity).
    rewrite temit_embed. reflexivity.
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

Local Lemma pstep_normal : forall ts n t v, frames_normal v -> frames_normal (pstep ts n t v).
Proof.
  intros ts n t [stk out md] N. unfold pstep. cbn [pv_mode].
  destruct md as [|b kids d e txt].
  2: { destruct (match e with Some e' => Nat.eqb n e' | None => false end);
       [apply pv_add_normal; exact N|exact N]. }
  assert (Open : forall i k op txt, frames_normal (popen i k op txt {| pv_stk := stk; pv_out := out; pv_mode := PMNormal |})).
  { intros i k [|] txt; [constructor; [exact Logic.I|exact N]|apply pv_add_normal, N]. }
  destruct t as [c| |k mr op cl| |b|c|ws|ws]; try (apply pv_add_normal; exact N);
    [| | | | |].
  - destruct (after_hard ts n); [exact N|apply pv_add_normal, N].
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
  - destruct (nbsp_rest ws) as [r|]; [|apply pv_add_normal, N].
    destruct (nonempty_str r); repeat apply pv_add_normal; exact N.
  - apply pv_add_normal, pv_trim_normal, N.
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
  intros [c| |k [|] [|] cl| |b|c|ws|ws]; cbn; try discriminate;
    pose proof (dtoken_nonempty k) as H; destruct (dtoken k); discriminate.
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
  destruct t as [c| |k mr op cl| |b|c|ws|ws].
  - apply pv_add_clean; [discriminate|exact N].
  - destruct (after_hard ts n); [exact N|apply pv_add_clean; [discriminate|exact N]].
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
  - apply pv_add_clean; [apply Str_|exact N].
    unfold esc_text. destruct (is_punct c); discriminate.
  - destruct (nbsp_rest ws) as [r|];
      [|apply pv_add_clean; [apply Str_, (tok_text_ne (TEscWs ws))|exact N]].
    destruct (nonempty_str r) eqn:Er.
    + apply pv_add_clean; [|apply pv_add_clean; [discriminate|exact N]].
      apply Str_. intros ->. discriminate Er.
    + apply pv_add_clean; [discriminate|exact N].
  - apply pv_add_clean; [discriminate|apply pv_trim_clean, N].
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
  - destruct t as [c| |k mr op cl| |b|c|ws|ws]; try (split; left; reflexivity).
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
  destruct t as [c| |k mr op cl| |b|c|ws|ws]; try exact Logic.I.
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

Local Lemma pv_ok_step : forall ts n t v,
  pv_ok n v ->
  (forall k mr op cl, t = TDelim k mr op cl -> self_row k = true) ->
  (t = TBreak -> after_hard ts n = true -> top_filled v) ->
  pv_ok (S n) (pstep ts n t v).
Proof.
  intros ts n t v Ok Hb Hh. pose proof Ok as (D & Bd & B & Inn).
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
  destruct t as [c| |k mr op cl| |b|c|ws|ws]; try (apply pv_ok_add; assumption).
  - (* a break after a hard break adds nothing, to a frame already filled *)
    destruct (after_hard ts n) eqn:Ea; [|apply pv_ok_add; assumption].
    specialize (Hh eq_refl eq_refl). unfold top_filled in Hh. rewrite Em in Hh.
    split; [exact D|]. split; [intros y H; specialize (Bd y H); lia|].
    split; [exact B|]. rewrite Em.
    destruct (pv_stk v) as [|[p k c|d c] rest] eqn:Es; try exact Logic.I.
    assert (Hp : p < n) by (apply (Bd (LOpen p k)); unfold pv_live; rewrite Es; left; reflexivity).
    split; [intros Hc; contradiction|lia].
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
  - destruct (nbsp_rest ws) as [r|]; [|apply pv_ok_add; assumption].
    destruct (nonempty_str r); [|apply pv_ok_add; assumption].
    destruct (pv_add_live NonBreakingSpace v) as [E1 _].
    apply pv_ok_add; [rewrite E1; exact D|rewrite E1; exact Bd|apply self_frames_add, B].
  - destruct (pv_trim_live v) as [E1 _].
    apply pv_ok_add; [rewrite E1; exact D|rewrite E1; exact Bd|apply self_frames_trim, B].
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
    rewrite Hd. change (Ascii.eqb rbrace percent) with false.
    rewrite andb_false_r. reflexivity. }
  unfold in_alphabet in Ha. rewrite Hd in Ha.
  apply andb_true_iff in Ha as [Ha _]. apply andb_true_iff in Ha as [Ha Hhy].
  apply andb_true_iff in Ha as [_ Hres]. rewrite Hlb, Erb, Hlk, Hrk in Hres.
  cbn [orb] in Hres. apply andb_true_iff in Hres as [Hres Hpct].
  apply negb_true_iff in Hres, Hhy, Hpct.
  pose proof (dreserved_false c Hres)
    as (Hbs & Htk & _ & _ & _ & _ & Hbg & Hdol & Hpd & Hlt).
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
   readings.  A pending `$` is kept: a break may open display math from
   it, which its resolved text cannot. *)
Fixpoint rres (st : iscan) : iscan :=
  match st with
  | IDest k i o e d dst sh o' => IDest k i o e d dst (rres sh) o'
  | IDollar _ _ _ _ => st
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

Local Lemma sdrop_length : forall s, sdrop (String.length s) s = "".
Proof. induction s as [|c s IH]; [reflexivity|]. exact IH. Qed.

Local Lemma ws_run_sdrop : forall s, (ws_run s ++ sdrop (String.length (ws_run s)) s)%string = s.
Proof.
  induction s as [|c s IH]; [reflexivity|]. cbn [ws_run].
  destruct (is_ws c); [|reflexivity]. cbn [String.length sdrop append]. rewrite IH. reflexivity.
Qed.

Local Lemma lex_text : forall s prev skip, toks_text (lex prev skip s) = sdrop skip s.
Proof.
  induction s as [|c rest IH]; intros prev skip; [destruct skip; reflexivity|].
  cbn [lex]. destruct skip as [|skip]; [|apply IH]. cbn [sdrop].
  assert (One : forall t p, tok_text t = one c ->
            toks_text (t :: lex p 0 rest) = String c rest).
  { intros t p E. cbn [toks_text]. rewrite E, IH. reflexivity. }
  destruct (is_bslash c) eqn:Eb.
  { (* an escape spells its backslash and the bytes it takes *)
    unfold is_bslash in Eb. apply Ascii.eqb_eq in Eb. subst c.
    cbn [toks_text]. rewrite IH.
    destruct (is_blank rest) eqn:Bl.
    - cbn [tok_text]. rewrite sdrop_length, append_empty_r. reflexivity.
    - destruct rest as [|d r]; [discriminate Bl|]. destruct (is_ws d) eqn:Wd.
      + cbn [tok_text]. change (String bslash (ws_run (String d r)) ++ ?x)%string
          with (String bslash (ws_run (String d r) ++ x)). rewrite ws_run_sdrop. reflexivity.
      + reflexivity. }
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
  | TText c => is_bslash c = false
  | TDelim k _ _ _ =>
      self_row k = true /\ Ascii.eqb (dchar k) lparen = false
      /\ Ascii.eqb (dchar k) rparen = false
  | TEscWs ws => is_blank ws = true /\ ws <> EmptyString
  | THard ws => is_blank ws = true
  | _ => True
  end.

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

(* A backslash escapes the byte after it, which the alphabet does not
   draw on. *)
Local Lemma over_alphabet_bslash : forall s,
  over_alphabet (String bslash s) = true ->
  match s with EmptyString => True | String _ r => over_alphabet r = true end.
Proof. intros [|d r] H; [exact Logic.I|exact H]. Qed.

(* A byte of the alphabet is not a backslash. *)
Local Lemma alphabet_not_bslash : forall c, in_alphabet c = true -> is_bslash c = false.
Proof.
  intros c Hc. destruct (is_bslash c) eqn:E; [|reflexivity].
  unfold is_bslash in E. apply Ascii.eqb_eq in E. subst c. discriminate Hc.
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

Local Lemma alphabet_plain : forall c k b1 b2 b3,
  in_alphabet c = true -> dstyle_of c = Some k -> tok_plain (TDelim k b1 b2 b3).
Proof.
  intros c k b1 b2 b3 Hc Hd. pose proof (dstyle_of_char c k Hd) as E. subst c.
  split; [exact (alphabet_self _ k Hc Hd)|exact (alphabet_paren _ k Hc Hd)].
Qed.

Local Lemma over_alphabet_chars : forall c n r,
  is_bslash c = false -> over_alphabet (chars c n ++ r) = true -> over_alphabet r = true.
Proof.
  intros c n r Hb. induction n as [|n IHn]; intros H; [exact H|].
  cbn [chars append] in H. apply (over_alphabet_cons c _ Hb) in H as (_ & _ & H). exact (IHn H).
Qed.

(* Past a delimiter's bytes, a string of the alphabet still is one. *)
Local Lemma over_alphabet_token : forall k s,
  prefix (dtoken k) s = true -> over_alphabet s = true ->
  over_alphabet (sdrop (dwidth k) s) = true.
Proof.
  intros k s P H. pose proof (prefix_sdrop _ _ P) as E.
  unfold dtoken in E at 2. rewrite length_chars in E. rewrite E in H.
  exact (over_alphabet_chars (dchar k) (dwidth k) _ (proj1 (dreserved_false _ (dchar_free k))) H).
Qed.

Local Lemma lex_plain : forall s prev skip,
  over_alphabet (sdrop skip s) = true -> Forall tok_plain (lex prev skip s).
Proof.
  induction s as [|c rest IH]; intros prev skip Ha; [constructor|].
  cbn [lex]. destruct skip as [|skip]; [|apply IH, Ha]. cbn [sdrop] in Ha.
  destruct (is_bslash c) eqn:Eb.
  { (* an escape is plain, and the bytes it takes are skipped *)
    unfold is_bslash in Eb. apply Ascii.eqb_eq in Eb. subst c.
    apply over_alphabet_bslash in Ha.
    destruct (is_blank rest) eqn:Bl.
    { constructor; [exact Bl|]. apply IH. rewrite sdrop_length. reflexivity. }
    destruct rest as [|d r]; [discriminate Bl|].
    destruct (is_ws d) eqn:Wd.
    - constructor; [split; [apply ws_run_blank|cbn [ws_run]; rewrite Wd; discriminate]|].
      apply IH. cbn [ws_run]. rewrite Wd. cbn [String.length sdrop].
      apply over_alphabet_ws_run, Ha.
    - constructor; [exact Logic.I|]. apply IH, Ha. }
  pose proof Ha as Ha0. apply (over_alphabet_cons c rest Eb) in Ha as (Hc & _ & Hr).
  destruct (Ascii.eqb c lbrack); [constructor; [exact Logic.I|apply IH, Hr]|].
  destruct (Ascii.eqb c rbrack).
  { constructor; [|apply IH, Hr].
    destruct (starts_with lparen rest); [|destruct (starts_with lbrack rest)];
      first [exact Logic.I|exact Eb]. }
  destruct (Ascii.eqb c lbrace).
  { destruct rest as [|d r]; [constructor; [exact Eb|apply IH, Hr]|].
    destruct (dstyle_of d) as [k|] eqn:Hd; [|constructor; [exact Eb|apply IH, Hr]].
    destruct (prefix (dtoken k) (String d r)) eqn:P; [|constructor; [exact Eb|apply IH, Hr]].
    constructor; [|apply IH, (over_alphabet_token k _ P Hr)].
    apply (over_alphabet_cons d r (delim_not_bslash d k Hd)) in Hr as (Hdc & _).
    exact (alphabet_plain d k _ _ _ Hdc Hd). }
  destruct (dstyle_of c) as [k|] eqn:Hd; [|constructor; [exact Eb|apply IH, Hr]].
  destruct (prefix (dtoken k) (String c rest)) eqn:P; [|constructor; [exact Eb|apply IH, Hr]].
  pose proof (over_alphabet_token k _ P Ha0) as Hx.
  destruct (dwidth k) as [|w] eqn:Ew; [destruct (dwidth_nonzero k Ew)|].
  cbn [sdrop] in Hx. cbn [pred].
  destruct (at_rbrace _) eqn:Ar; (constructor; [exact (alphabet_plain c k _ _ _ Hc Hd)|apply IH]);
    [|exact Hx].
  (* a marked closer skips its `}` too *)
  assert (G : forall n u, at_rbrace (get n u) = true -> over_alphabet (sdrop n u) = true ->
            over_alphabet (sdrop (S n) u) = true).
  { intros n. induction n as [|n IHn]; intros u A H'.
    - destruct u as [|e u]; [discriminate|]. cbn [get at_rbrace] in A. apply Ascii.eqb_eq in A.
      subst e. cbn [sdrop] in H' |- *. exact (proj2 (proj2 (over_alphabet_cons rbrace u eq_refl H'))).
    - destruct u as [|e u]; [destruct n; discriminate|]. cbn [get] in A. cbn [sdrop] in H' |- *.
      exact (IHn u A H'). }
  apply G; [exact Ar|exact Hx].
Qed.

Local Lemma dfeed_chars : forall c n d dst,
  is_bslash c = false -> Ascii.eqb c lparen = false -> Ascii.eqb c rparen = false ->
  dfeed (chars c n) (DS false d dst) = Some (DS false d (dst ++ chars c n)).
Proof.
  intros c n d dst Hb H1 H2. revert dst. induction n as [|n IH]; intros dst.
  - cbn. rewrite append_empty_r. reflexivity.
  - cbn [chars dfeed]. unfold dstep. cbn [ds_esc ds_depth ds_dst]. rewrite Hb.
    unfold pstep_byte. rewrite H1, H2. rewrite IH, append_assoc. reflexivity.
Qed.

Local Lemma blank_byte : forall c, is_ws c = true ->
  is_bslash c = false /\ Ascii.eqb c lparen = false /\ Ascii.eqb c rparen = false
  /\ is_punct c = false.
Proof. intros c. destruct c as [[] [] [] [] [] [] [] []]; intros H; try discriminate H; auto. Qed.

Local Lemma dfeed_blank : forall s d dst, is_blank s = true ->
  dfeed s (DS false d dst) = Some (DS false d (dst ++ s)).
Proof.
  induction s as [|c s IH]; intros d dst H; [cbn; rewrite append_empty_r; reflexivity|].
  cbn [is_blank] in H. apply andb_true_iff in H as [Hc H].
  destruct (blank_byte c Hc) as (Hb & H1 & H2 & _).
  cbn [dfeed]. unfold dstep. cbn [ds_esc ds_depth ds_dst]. rewrite Hb.
  unfold pstep_byte. rewrite H1, H2. rewrite IH by exact H. rewrite append_assoc. reflexivity.
Qed.

(* A backslash and a run of whitespace: the first byte of the run is
   escaped, and kept with its backslash. *)
Local Lemma dfeed_esc_blank : forall ws d dst, is_blank ws = true ->
  dfeed (String bslash ws) (DS false d dst)
  = match ws with
    | EmptyString => Some (DS true d dst)
    | _ => Some (DS false d (dst ++ String bslash ws))
    end.
Proof.
  intros [|w ws] d dst H; [reflexivity|].
  cbn [is_blank] in H. apply andb_true_iff in H as [Hw H].
  destruct (blank_byte w Hw) as (_ & _ & _ & Hp).
  cbn [dfeed]. unfold dstep. cbn [ds_esc ds_depth ds_dst].
  change (is_bslash bslash) with true. cbn iota. unfold esc_text. rewrite Hp.
  cbn [ds_esc ds_depth ds_dst]. rewrite dfeed_blank by exact H. rewrite !append_assoc.
  reflexivity.
Qed.

(* What a token does to a destination's reading, from between two
   tokens: a token that is not a paren adds its destination text, and
   a hard break with no whitespace leaves its backslash pending. *)
Local Lemma tok_dfeed : forall t d dst, tok_plain t ->
  dfeed (tok_text t) (DS false d dst)
  = match t with
    | TText c => match pstep_byte c d with
                 | Some d' => Some (DS false d' (dst ++ one c))
                 | None => None
                 end
    | THard EmptyString => Some (DS true d dst)
    | _ => Some (DS false d (dst ++ tok_dest t))
    end.
Proof.
  intros t d dst Hp.
  destruct t as [c| |k mr op cl| |b|c|ws|ws]; cbn [tok_dest].
  - cbn [tok_text one dfeed]. unfold dstep. cbn [ds_esc ds_depth ds_dst].
    cbn [tok_plain] in Hp. rewrite Hp. destruct (pstep_byte c d); reflexivity.
  - cbn [tok_text one dfeed]. unfold dstep. cbn [ds_esc ds_depth ds_dst]. reflexivity.
  - destruct Hp as (_ & H1 & H2).
    pose proof (proj1 (dreserved_false _ (dchar_free k))) as Hb.
    destruct mr; [destruct op|]; cbn [tok_text]; unfold dtoken.
    + rewrite dfeed_app. cbn [one dfeed]. unfold dstep. cbn [ds_esc ds_depth ds_dst].
      change (is_bslash lbrace) with false. change (pstep_byte lbrace d) with (Some d).
      cbn iota. rewrite dfeed_chars by assumption. rewrite append_assoc. reflexivity.
    + rewrite dfeed_app, dfeed_chars by assumption. cbn [one dfeed]. unfold dstep.
      cbn [ds_esc ds_depth ds_dst]. change (is_bslash rbrace) with false.
      change (pstep_byte rbrace d) with (Some d). cbn iota. rewrite append_assoc. reflexivity.
    + rewrite dfeed_chars by assumption. reflexivity.
  - reflexivity.
  - reflexivity.
  - cbn [tok_text one dfeed]. unfold dstep. cbn [ds_esc ds_depth ds_dst].
    change (is_bslash bslash) with true. reflexivity.
  - destruct Hp as [Hb Hne]. cbn [tok_text]. rewrite dfeed_esc_blank by exact Hb.
    destruct ws; [contradiction|reflexivity].
  - cbn [tok_plain] in Hp. cbn [tok_text]. rewrite dfeed_esc_blank by exact Hp.
    destruct ws; reflexivity.
Qed.

Local Lemma paren_close_cons : forall t depth dst i rest,
  tok_plain t ->
  paren_close depth i (t :: rest)
  = match dfeed (tok_text t) (DS false depth dst) with
    | Some ds => paren_close (ds_depth ds) (S i) rest
    | None => Some i
    end.
Proof.
  intros t depth dst i rest Hp. rewrite (tok_dfeed t depth dst Hp).
  destruct t as [c| |k mr op cl| |b|c|ws|ws]; try reflexivity.
  - cbn [paren_close]. unfold pstep_byte.
    destruct (Ascii.eqb c lparen); [reflexivity|].
    destruct (Ascii.eqb c rparen); [destruct depth; reflexivity|reflexivity].
  - destruct ws; reflexivity.
Qed.

(* Only the `)` that balances ends a destination. *)
Local Lemma dfeed_none : forall t depth dst,
  tok_plain t -> dfeed (tok_text t) (DS false depth dst) = None ->
  tok_text t = one rparen /\ depth = 0.
Proof.
  intros t depth dst Hp H. rewrite (tok_dfeed t depth dst Hp) in H.
  destruct t as [c| |k mr op cl| |b|c|ws|ws]; try discriminate H.
  - unfold pstep_byte in H.
    destruct (Ascii.eqb c lparen); [discriminate|].
    destruct (Ascii.eqb c rparen) eqn:E; [|discriminate].
    apply Ascii.eqb_eq in E. subst c. destruct depth; [split; reflexivity|discriminate].
  - destruct ws; discriminate H.
Qed.

(* A hard break ends its line: no token follows it on the line. *)
Definition hard_last (toks : list token) : Prop :=
  forall a ws b, toks = (a ++ THard ws :: b)%list -> b = [].

Local Lemma hard_last_cons : forall t toks, hard_last (t :: toks) -> hard_last toks.
Proof.
  intros t toks H a ws b E. apply (H (t :: a) ws b). rewrite E. reflexivity.
Qed.

(* Tokens that leave a paren open: so do their bytes. *)
Local Lemma paren_close_app : forall toks depth dst i rest,
  Forall tok_plain toks -> hard_last toks ->
  paren_close depth i (toks ++ rest) = None ->
  exists ds, dfeed (toks_text toks) (DS false depth dst) = Some ds
             /\ paren_close (ds_depth ds) (i + length toks) rest = None
             /\ (Forall (fun t => t <> THard EmptyString) toks -> ds_esc ds = false).
Proof.
  induction toks as [|t toks IH]; intros depth dst i rest F Hl H.
  - exists (DS false depth dst). rewrite Nat.add_0_r. split; [reflexivity|split; [exact H|reflexivity]].
  - apply Forall_cons_iff in F as [Ft F]. cbn [app] in H.
    rewrite (paren_close_cons t depth dst i _ Ft) in H.
    cbn [toks_text length]. rewrite dfeed_app.
    pose proof (tok_dfeed t depth dst Ft) as Et.
    destruct (dfeed (tok_text t) (DS false depth dst)) as [d1|] eqn:E1; [|discriminate].
    assert (Hd1 : toks = [] \/ ds_esc d1 = false).
    { destruct t as [c| |k mr op cl| |b|c|ws|ws];
        try (right; injection Et as Et; subst d1; reflexivity).
      - destruct (pstep_byte c depth); [injection Et as Et; subst d1; right; reflexivity|discriminate].
      - destruct ws.
        + left. exact (Hl [] EmptyString toks eq_refl).
        + right. injection Et as Et. subst d1. reflexivity. }
    destruct Hd1 as [->|Hd1].
    + exists d1. cbn [dfeed toks_text length app] in *. rewrite Nat.add_1_r.
      split; [reflexivity|split; [exact H|]].
      intros G. apply Forall_cons_iff in G as [G _].
      destruct t as [c| |k mr op cl| |b|c|ws|ws];
        try (injection Et as Et; subst d1; reflexivity).
      * destruct (pstep_byte c depth); [injection Et as Et; subst d1; reflexivity|discriminate].
      * destruct ws; [contradiction|injection Et as Et; subst d1; reflexivity].
    + destruct d1 as [e1 dp1 dst1]. cbn [ds_esc ds_depth] in *. subst e1.
      destruct (IH dp1 dst1 (S i) rest F (hard_last_cons t toks Hl) H) as (ds & E2 & E3 & E4).
      exists ds. rewrite <- Nat.add_succ_comm. split; [assumption|split; [assumption|]].
      intros G. apply Forall_cons_iff in G as [_ G]. exact (E4 G).
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
  cbn [wrap map ibreak_at]. rewrite IH. destruct w as [k o [e dp dst] o'].
  unfold wl_after. destruct e; reflexivity.
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

Local Lemma pv_trim_out : forall v,
  pv_out (pv_trim v) = pv_out v \/ pv_out (pv_trim v) = xtrim (pv_out v).
Proof. intros [[|f rest] out md]; [right|left]; reflexivity. Qed.

(* The outermost content stays normal and clean. *)
Local Lemma pstep_out : forall ts n t v,
  normal (pv_out v) -> clean (pv_out v) ->
  normal (pv_out (pstep ts n t v)) /\ clean (pv_out (pstep ts n t v)).
Proof.
  intros ts n t v N0 C0.
  assert (Add : forall x v', x <> Str "" -> normal (pv_out v') -> clean (pv_out v') ->
            normal (pv_out (pv_add x v')) /\ clean (pv_out (pv_add x v'))).
  { intros x v' Hx N C. destruct (pv_add_out x v') as [H|H]; rewrite H;
      [split; assumption|split; [apply normal_xsnoc, N|apply clean_xsnoc; assumption]]. }
  assert (Txt : forall t', Str (tok_text t') <> Str "")
    by (intros t' E; injection E as E; exact (tok_text_ne t' E)).
  assert (Open : forall i k op t',
            normal (pv_out (popen i k op (tok_text t') v)) /\ clean (pv_out (popen i k op (tok_text t') v))).
  { intros i k [|] t'; [split; assumption|apply Add; [apply Txt|exact N0|exact C0]]. }
  unfold pstep. destruct (pv_mode v) as [|b kids d e txt].
  2: { destruct (match e with Some e' => Nat.eqb n e' | None => false end);
         [apply Add; [apply region_node_nonstr|exact N0|exact C0]|split; assumption]. }
  destruct t as [c| |k mr op cl| |b|c|ws|ws].
  - apply Add; [discriminate|exact N0|exact C0].
  - destruct (after_hard ts n); [split; assumption|apply Add; [discriminate|exact N0|exact C0]].
  - destruct (if cl then pick (KDelim k mr) (pv_live v) else PNone) as [p below| |];
      [|apply Add; [apply Txt|exact N0|exact C0]|apply Open].
    destruct (Nat.ltb (S p) n); [|apply Open].
    destruct (pclose_go (KDelim k mr) [] (pv_stk v)) as [[content rest]|]; [|split; assumption].
    apply Add; [apply dnode_nonstr|exact N0|exact C0].
  - apply Open.
  - destruct (pick KBracket (pv_live v));
      destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|];
      try (apply Add; [apply Txt|exact N0|exact C0]).
    destruct (region_end ts n b); [split; assumption|]. destruct b; split; assumption.
  - apply Add; [|exact N0|exact C0]. intros E. injection E as E.
    unfold esc_text in E. destruct (is_punct c); discriminate.
  - destruct (nbsp_rest ws) as [r|]; [|apply Add; [apply (Txt (TEscWs ws))|exact N0|exact C0]].
    destruct (Add NonBreakingSpace v ltac:(discriminate) N0 C0) as [N1 C1].
    destruct (nonempty_str r) eqn:Er; [|split; assumption].
    apply Add; [|exact N1|exact C1]. intros E. injection E as ->. discriminate Er.
  - assert (Tr : normal (pv_out (pv_trim v)) /\ clean (pv_out (pv_trim v))).
    { destruct (pv_trim_out v) as [H|H]; rewrite H;
        [split; assumption|split; [apply normal_xtrim, N0|apply clean_xtrim, C0]]. }
    apply Add; [discriminate|exact (proj1 Tr)|exact (proj2 Tr)].
Qed.

Local Lemma pstep_tidy : forall ts n t v, tidy v -> tidy (pstep ts n t v).
Proof.
  intros ts n t v (Hn & Hc & Fn & Fc).
  destruct (pstep_out ts n t v Hn Hc) as [N C].
  split; [exact N|split; [exact C|split; [apply pstep_normal, Fn|apply pstep_clean, Fc]]].
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

Local Lemma dchar_nb : forall k, is_bslash (dchar k) = false.
Proof. intros k. exact (proj1 (dreserved_false _ (dchar_free k))). Qed.

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
  rewrite Ed at 1. cbn [append lex]. rewrite dchar_nb, Hlk, Hrk, Hlb, Hk.
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
  rewrite Ed at 1. cbn [append lex]. rewrite dchar_nb, Hlk, Hrk, Hlb, Hk.
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
  cbn [lex]. change (is_bslash lbrace) with false. change (Ascii.eqb lbrace lbrack) with false.
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
  cbn [lex]. rewrite dchar_nb, Hlk, Hrk, Hlb, Hk.
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
  cbn [lex]. change (is_bslash lbrace) with false. change (Ascii.eqb lbrace lbrack) with false.
  change (Ascii.eqb lbrace rbrack) with false. rewrite Ascii.eqb_refl.
  cbn [chars append]. rewrite Hk.
  change (String (dchar k) (chars (dchar k) j ++ rest))
    with (chars (dchar k) (S j) ++ rest)%string.
  unfold dtoken. rewrite (prefix_chars_short (dchar k) (dwidth k) (S j) rest Hj Hr).
  reflexivity.
Qed.

(* A byte that is no row's character, no `{` and no bracket. *)
Local Lemma lex_byte : forall c prev rest,
  is_bslash c = false ->
  Ascii.eqb c lbrack = false -> Ascii.eqb c rbrack = false ->
  Ascii.eqb c lbrace = false -> dstyle_of c = None ->
  lex prev 0 (String c rest) = TText c :: lex (Some c) 0 rest.
Proof. intros c prev rest H0 H1 H2 H3 H4. cbn [lex]. rewrite H0, H1, H2, H3, H4. reflexivity. Qed.

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

(* The first token of a line that does not begin with a backslash, its
   bytes, and the line after it. *)
Local Lemma lex_cons : forall c s' prev,
  is_bslash c = false -> over_alphabet (String c s') = true ->
  exists t r prev1,
    String c s' = (tok_text t ++ r)%string /\ lex prev 0 (String c s') = t :: lex prev1 0 r
    /\ prev_ok prev1 r = true /\ String.length r < String.length (String c s')
    /\ (forall c0, tok_text t = one c0 -> prev1 = Some c0)
    /\ no_bslash (tok_text t) = true /\ over_alphabet r = true.
Proof.
  intros c s' prev Eb Ha.
  pose proof Ha as Ha'. apply (over_alphabet_cons c s' Eb) in Ha' as (Hc & Hf & Hs').
  assert (Nb : forall k, no_bslash (dtoken k) = true).
  { intros k. unfold dtoken. generalize (dwidth k). intros w. induction w as [|w IHw]; [reflexivity|].
    cbn [chars no_bslash]. rewrite dchar_nb, IHw. reflexivity. }
  assert (One : forall t, tok_text t = one c ->
            lex prev 0 (String c s') = t :: lex (Some c) 0 s' ->
            exists t r prev1,
              String c s' = (tok_text t ++ r)%string
              /\ lex prev 0 (String c s') = t :: lex prev1 0 r
              /\ prev_ok prev1 r = true /\ String.length r < String.length (String c s')
              /\ (forall c0, tok_text t = one c0 -> prev1 = Some c0)
              /\ no_bslash (tok_text t) = true /\ over_alphabet r = true).
  { intros t Et El. exists t, s', (Some c). rewrite Et. split; [reflexivity|].
    split; [exact El|]. split; [exact Hf|]. split; [cbn; lia|].
    split; [intros c0 E0; injection E0 as <-; reflexivity|].
    split; [cbn; rewrite Eb; reflexivity|exact Hs']. }
  destruct (Ascii.eqb c lbrack) eqn:Elk.
  { apply (One TOpen); [apply Ascii.eqb_eq in Elk; subst c; reflexivity|].
    cbn [lex]. rewrite Eb, Elk. reflexivity. }
  destruct (Ascii.eqb c rbrack) eqn:Erk.
  { assert (Ec : c = rbrack) by (apply Ascii.eqb_eq, Erk).
    cbn [lex] in One |- *. rewrite Eb, Elk, Erk in One |- *.
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
      pose proof Hs' as Hs2. rewrite Es in Hs2. apply (over_alphabet_app_r _ _ (Nb k)) in Hs2.
      rewrite Es. exists (TDelim k true true false), (chars (dchar k) (S j - dwidth k) ++ rest0)%string,
        (Some (dchar k)).
      split; [reflexivity|]. split; [apply lex_marked_open, Hd|].
      split; [apply follow_ok_plain; assumption|].
      split; [cbn [String.length]; rewrite !length_append; lia|].
      split; [intros c0 E0; cbn in E0; injection E0 as _ E0;
              pose proof (dtoken_nonempty k) as H; rewrite E0 in H; discriminate|].
      split; [cbn [tok_text one append no_bslash]; exact (Nb k)|exact Hs2].
    - rewrite E. exists (TText lbrace), (chars (dchar k) (S j) ++ rest0)%string, (Some lbrace).
      split; [reflexivity|]. split; [apply lex_lbrace_short; assumption|].
      split; [cbn [prev_ok]; rewrite <- E; exact Hf'|]. split; [cbn; lia|].
      split; [intros c0 E0; injection E0 as <-; reflexivity|].
      split; [reflexivity|rewrite <- E; exact Hs']. }
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
    pose proof Ha as Ha2. rewrite Es in Ha2. apply (over_alphabet_app_r _ _ (Nb k)) in Ha2.
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
      split; [intros c0 E0; cbn [tok_text] in E0; rewrite Ed in E0; cbn in E0;
              injection E0 as _ E0; destruct w; discriminate|].
      split; [cbn [tok_text]; rewrite no_bslash_app, (Nb k); reflexivity|].
      exact (proj2 (proj2 (over_alphabet_cons rbrace r eq_refl Ha2))).
    + exists (TDelim k false (bare_opens k && nonspace_at (get 0 rest)) (nonspace_at prev)),
        rest, (Some (dchar k)).
      split; [reflexivity|]. split; [apply lex_token; assumption|].
      split; [apply follow_ok_plain; assumption|]. split; [exact Hlen|].
      split; [intros c0 E0; cbn [tok_text] in E0; rewrite Ed in E0; injection E0 as <- _; reflexivity|].
      split; [exact (Nb k)|exact Ha2].
  - rewrite E. cbn [chars append]. exists (TText (dchar k)), (chars (dchar k) j ++ rest0)%string,
      (Some (dchar k)).
    split; [reflexivity|]. split; [apply lex_short; assumption|].
    split; [apply follow_ok_plain; assumption|]. split; [cbn; lia|].
    split; [intros c0 E0; injection E0 as <-; reflexivity|].
    split; [cbn [tok_text one no_bslash]; rewrite dchar_nb; reflexivity|].
    cbn [chars append] in E. injection E as E. rewrite <- E. exact Hs'.
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

(* Between two tokens of a line no destination reading holds a pending
   backslash; only a hard break leaves one, at the line's end. *)
Definition esc_off (w : wlayer) : Prop := ds_esc (wl_ds w) = false.

Definition vinv (ts : list token) (n : nat) (v : pview) : Prop :=
  pv_ok n v /\ tidy v /\ (after_hard ts n = true -> top_filled v).

Definition linked (ts : list token) (n : nat) (v : pview) (prev : option ascii)
  (core : iscan) : Prop :=
  match pv_mode v with
  | PMNormal =>
      after_hard ts n = false /\ exists txt o, core = IText false txt prev o /\ sim v txt o
  | PMRegion false kids d e label =>
      S d < n /\ e = rbrack_at n (skipn n ts) /\ clean kids
      /\ exists open cm, core = IReference (map mk kids) false open false label (oview cm v)
  | PMRegion true kids d e dst =>
      S d < n /\ exists open depth sh cm,
        e = paren_close depth n (skipn n ts) /\ e <> None
        /\ core = IDest (map mk kids) false open false depth dst sh (oview cm v)
  end.

(* A backslash and whitespace the line ended after, which the scanner
   holds until the line's end. *)
Definition esc_pending (ws0 txt : string) (p : option ascii) (o : ostate) : iscan :=
  match ws0 with
  | EmptyString => IText true txt p o
  | _ => IEscWs ws0 txt p o
  end.

(* What a hard break leaves at the end of a line: in text mode, the view
   with the break and the scanner with it pending; in a region whose
   backslash ended the line, the backslash pending in the scanner. *)
Definition pending (ts : list token) (n : nat) (v : pview) (core : iscan) : Prop :=
  (exists ws0 txt p o vb,
     after_hard ts n = true /\ is_blank ws0 = true /\ core = esc_pending ws0 txt p o
     /\ pv_mode vb = PMNormal /\ sim vb txt o /\ v = pv_add HardBreak (pv_trim vb))
  \/ (exists kids d e label open cm,
        pv_mode v = PMRegion false kids d e (label ++ one bslash)%string
        /\ S d < n /\ e = rbrack_at n (skipn n ts) /\ clean kids
        /\ core = IReference (map mk kids) false open true label (oview cm v))
  \/ (exists kids d e dst open depth sh cm,
        pv_mode v = PMRegion true kids d e (dst ++ one bslash)%string
        /\ S d < n /\ e = paren_close depth n (skipn n ts) /\ e <> None
        /\ core = IDest (map mk kids) false open true depth dst sh (oview cm v)).

Definition linked_end (ts : list token) (n : nat) (v : pview) (prev : option ascii)
  (core : iscan) : Prop :=
  linked ts n v prev core \/ pending ts n v core.

(* A `[` with nothing yet read after it would make a `^` a footnote's: the
   byte before the line, or the text the scanner holds, rules that out. *)
Definition note_ok (prev : option ascii) (core : iscan) (s : string) : Prop :=
  prev_ok prev s = true
  \/ (forall txt p o, core = IText false txt p o -> nonempty_str txt = true).

(* A line's bytes, scanned from a linked state, end in one. *)
Definition scanned (ts : list token) (n : nat) (v : pview) (ws : list wlayer)
  (core : iscan) (prev : option ascii) (s : string) : Prop :=
  exists ws' core' prev',
    rres (iscan_str s (wrap ws core)) = wrap ws' core'
    /\ vinv ts (n + length (lex prev 0 s)) (prun ts n (lex prev 0 s) v)
    /\ Forall (never ts (n + length (lex prev 0 s))) ws'
    /\ linked_end ts (n + length (lex prev 0 s)) (prun ts n (lex prev 0 s) v) prev' core'.

Definition scan_ih (ts after : list token) (len : nat) : Prop :=
  forall s prev n v ws core,
    String.length s <= len -> over_alphabet s = true -> note_ok prev core s ->
    skipn n ts = (lex prev 0 s ++ after)%list ->
    vinv ts n v -> Forall (never ts n) ws -> Forall esc_off ws -> linked ts n v prev core ->
    scanned ts n v ws core prev s.

Local Lemma prun_app : forall ts a b i v,
  prun ts i (a ++ b) v = prun ts (i + length a) b (prun ts i a v).
Proof.
  intros ts. induction a as [|t a IH]; intros b i v; cbn [app prun length];
    [rewrite Nat.add_0_r; reflexivity|].
  rewrite IH. f_equal. lia.
Qed.

Local Lemma skipn_app_tail : forall (ts a b : list token) n,
  skipn n ts = (a ++ b)%list -> skipn (n + length a) ts = b.
Proof.
  intros ts a b n H. rewrite Nat.add_comm, <- skipn_skipn, H.
  rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity.
Qed.

Local Lemma skipn_cons_tail : forall (ts : list token) n t rest,
  skipn n ts = t :: rest -> skipn (S n) ts = rest.
Proof.
  intros ts n t rest H. pose proof (skipn_app_tail ts [t] rest n H) as E.
  cbn [length] in E. rewrite Nat.add_1_r in E. exact E.
Qed.

Local Lemma top_filled_add : forall x v, top_filled (pv_add x v).
Proof.
  intros x [[|[p k c|d c] rest] out md]; unfold top_filled; cbn [pv_add pv_stk pv_mode fset fcontent];
    destruct md; try exact Logic.I; apply xsnoc_nonempty.
Qed.

Local Lemma vinv_step : forall ts n t v,
  vinv ts n v -> tok_plain t -> nth_error ts n = Some t -> vinv ts (S n) (pstep ts n t v).
Proof.
  intros ts n t v (Ok & Ti & Hh) Hp Hn. split; [|split; [apply pstep_tidy, Ti|]].
  - apply pv_ok_step; [exact Ok| |].
    + intros k mr op cl ->. exact (proj1 Hp).
    + intros _ H. exact (Hh H).
  - unfold after_hard. rewrite Hn. destruct t as [c| |k mr op cl| |b|c|ws|ws];
      try discriminate. intros _.
    unfold pstep. destruct (pv_mode v) as [|b kids d e txt] eqn:Em.
    + apply top_filled_add.
    + destruct (match e with Some e' => Nat.eqb n e' | None => false end);
        [apply top_filled_add|unfold top_filled; cbn [pv_setmode pv_mode]; exact Logic.I].
Qed.

Local Lemma vinv_prun : forall ts toks n v rest,
  vinv ts n v -> Forall tok_plain toks -> skipn n ts = (toks ++ rest)%list ->
  vinv ts (n + length toks) (prun ts n toks v).
Proof.
  intros ts. induction toks as [|t toks IH]; intros n v rest V F Hs; cbn [prun length];
    [rewrite Nat.add_0_r; exact V|].
  apply Forall_cons_iff in F as [Ft F]. rewrite <- Nat.add_succ_comm.
  assert (Hn : nth_error ts n = Some t).
  { rewrite <- (Nat.add_0_r n), <- nth_error_skipn, Hs. reflexivity. }
  apply (IH (S n) _ rest); [apply vinv_step; assumption|exact F|].
  apply (skipn_cons_tail ts n t). exact Hs.
Qed.


Local Lemma layers_step : forall ts n ws toks rest,
  Forall (never ts n) ws -> Forall esc_off ws ->
  skipn n ts = (toks ++ rest)%list -> Forall tok_plain toks -> hard_last toks ->
  Forall (fun w => dfeed (toks_text toks) (wl_ds w) <> None) ws
  /\ Forall (never ts (n + length toks)) (map (wl_after (toks_text toks)) ws)
  /\ (Forall (fun t => t <> THard EmptyString) toks ->
      Forall esc_off (map (wl_after (toks_text toks)) ws)).
Proof.
  intros ts n ws toks rest F Fe Hs Fp Hl.
  assert (G : forall w, In w ws ->
            exists ds, dfeed (toks_text toks) (wl_ds w) = Some ds
              /\ paren_close (ds_depth ds) (n + length toks) rest = None
              /\ (Forall (fun t => t <> THard EmptyString) toks -> ds_esc ds = false)).
  { intros [k o [e d dst] o'] Hw. rewrite Forall_forall in F, Fe.
    specialize (F _ Hw). specialize (Fe _ Hw). unfold never, esc_off, wl_depth in *.
    cbn [wl_ds ds_esc ds_depth] in *. subst e. rewrite Hs in F.
    exact (paren_close_app toks d dst n rest Fp Hl F). }
  split; [|split].
  - rewrite Forall_forall. intros w Hw E. destruct (G w Hw) as (ds & E1 & _). congruence.
  - rewrite Forall_map, Forall_forall. intros w Hw. destruct (G w Hw) as (ds & E1 & E2 & _).
    unfold never, wl_after, wl_depth. cbn [wl_ds]. rewrite E1.
    rewrite (skipn_app_tail ts toks rest n Hs). exact E2.
  - intros H. rewrite Forall_map, Forall_forall. intros w Hw. destruct (G w Hw) as (ds & E1 & _ & E3).
    unfold esc_off, wl_after. cbn [wl_ds]. rewrite E1. exact (E3 H).
Qed.

Local Lemma wrap_app : forall a b core, wrap (a ++ b) core = wrap a (wrap b core).
Proof. induction a as [|w a IH]; intros b core; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.


Local Lemma lex_skip_all : forall s p, lex p (String.length s) s = [].
Proof. induction s as [|d r IHr]; intros p; [reflexivity|]. cbn [String.length lex]. apply IHr. Qed.

(* `lex` puts a hard break only last: it takes the rest of the line. *)
Local Lemma lex_hard_last : forall s prev skip, hard_last (lex prev skip s).
Proof.
  induction s as [|c rest IH]; intros prev skip a ws b E.
  - destruct a; discriminate E.
  - cbn [lex] in E. destruct skip as [|skip]; [|exact (IH _ _ a ws b E)].
    assert (Tl : forall t prev' k, (t :: lex prev' k rest = a ++ THard ws :: b)%list ->
               (t = THard ws /\ a = [] /\ b = lex prev' k rest) \/ b = []).
    { intros t prev' k E'. destruct a as [|x a].
      - left. cbn in E'. injection E' as -> ->. auto.
      - right. cbn in E'. injection E' as _ E'. exact (IH _ _ a ws b E'). }
    destruct (is_bslash c).
    + destruct (is_blank rest) eqn:Bl.
      * destruct (Tl _ _ _ E) as [(_ & _ & ->)| ->]; [|reflexivity].
        apply lex_skip_all.
      * destruct (Tl _ _ _ E) as [(Et & _)| ->]; [|reflexivity].
        destruct rest as [|d r]; [discriminate Bl|]. destruct (is_ws d); discriminate Et.
    + repeat (match type of E with
              | context [if ?x then _ else _] => destruct x
              | context [match ?x with Some _ => _ | None => _ end] => destruct x
              | context [match ?x with EmptyString => _ | String _ _ => _ end] => destruct x
              end);
        (destruct (Tl _ _ _ E) as [(Et & _)| ->]; [discriminate Et|reflexivity]).
Qed.

Local Lemma hard_last_app_l : forall a b, hard_last (a ++ b) -> hard_last a.
Proof.
  intros a b H x ws y E. subst a. specialize (H x ws (y ++ b)%list).
  rewrite <- app_assoc in H. cbn in H. specialize (H eq_refl).
  destruct y; [reflexivity|discriminate H].
Qed.

(* One step of the simulation: a chunk of bytes and its tokens, then the
   rest of the line. *)
Local Lemma scan_advance : forall ts after len,
  scan_ih ts after len ->
  forall s prev n v ws core bytes rest toks prev1 extra core1,
    String.length s <= S len -> over_alphabet s = true ->
    skipn n ts = (lex prev 0 s ++ after)%list ->
    vinv ts n v -> Forall (never ts n) ws -> Forall esc_off ws ->
    s = (bytes ++ rest)%string -> bytes <> "" ->
    lex prev 0 s = (toks ++ lex prev1 0 rest)%list -> toks_text toks = bytes ->
    Forall (fun t => t <> THard EmptyString) toks ->
    over_alphabet rest = true -> note_ok prev1 core1 rest ->
    settles (iscan_str bytes core) (wrap extra core1) (get 0 rest) ->
    Forall (never ts (n + length toks)) extra -> Forall esc_off extra ->
    linked ts (n + length toks) (prun ts n toks v) prev1 core1 ->
    scanned ts n v ws core prev s.
Proof.
  intros ts after len IH s prev n v ws core bytes rest toks prev1 extra core1
    Hl Ha Hsk V Fn Fe Es Hne El Et Hh Ha' Hp Hset Fn2 Fe2 L.
  pose proof (lex_plain s prev 0 Ha) as Fp.
  destruct (layers_step ts n ws _ after Fn Fe Hsk Fp (lex_hard_last s prev 0)) as [Hopen _].
  rewrite lex_text in Hopen. cbn [sdrop] in Hopen.
  pose proof (lex_hard_last s prev 0) as Hl0. rewrite El in Fp, Hsk, Hl0.
  apply Forall_app in Fp as [Fp _].
  rewrite <- app_assoc in Hsk.
  destruct (layers_step ts n ws toks _ Fn Fe Hsk Fp (hard_last_app_l _ _ Hl0)) as (_ & Fn' & Fe').
  pose proof (skipn_app_tail ts toks _ n Hsk) as Hsk'.
  assert (Hlen : String.length rest <= len).
  { rewrite Es, length_append in Hl. destruct bytes; [contradiction|]. cbn in Hl. lia. }
  destruct (IH rest prev1 (n + length toks) (prun ts n toks v)
              (map (wl_after bytes) ws ++ extra)%list core1 Hlen Ha' Hp Hsk'
              (vinv_prun ts toks n v _ V Fp Hsk))
    as (ws' & core' & prev' & E & V' & Fn'' & L').
  { apply Forall_app. split; [rewrite <- Et; exact Fn'|exact Fn2]. }
  { apply Forall_app. split; [rewrite <- Et; exact (Fe' Hh)|exact Fe2]. }
  { exact L. }
  exists ws', core', prev'.
  rewrite El, length_app, prun_app, Nat.add_assoc.
  split; [|split; [exact V'|split; [exact Fn''|exact L']]].
  rewrite <- E, wrap_app. rewrite Es at 1.
  apply (step_through bytes rest ws core (iscan_str bytes core) (wrap extra core1));
    [|reflexivity|exact Hset].
  rewrite <- Es. exact Hopen.
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
  destruct t as [c| |k mr op cl| |b|c|ws|ws]; try apply Add; try apply Open.
  - destruct (after_hard ts n); [exact Em|apply Add].
  - destruct (if cl then pick (KDelim k mr) (pv_live v) else PNone); try apply Add; try apply Open.
    destruct (Nat.ltb (S p) n); [|apply Open].
    destruct (pclose_go (KDelim k mr) [] (pv_stk v)) as [[content rest]|]; [|exact Em].
    rewrite (proj2 (pv_add_live _ _)). reflexivity.
  - destruct (Ht b eq_refl).
  - destruct (nbsp_rest ws); [|apply Add].
    destruct (nonempty_str s); [rewrite (proj2 (pv_add_live _ _))|]; apply Add.
  - rewrite (proj2 (pv_add_live _ _)), pv_trim_add. exact Em.
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
  after_hard ts n = false -> pv_mode v = PMNormal -> sim v txt o ->
  linked ts n v prev (IText false txt prev o).
Proof.
  intros ts n v prev txt o Ha Em Hs. unfold linked. rewrite Em.
  split; [exact Ha|]. exists txt, o. auto.
Qed.

(* After a chunk whose last token is not a hard break. *)
Local Lemma after_chunk : forall ts n toks rest,
  skipn n ts = (toks ++ rest)%list -> toks <> [] ->
  Forall (fun t => forall ws, t <> THard ws) toks ->
  after_hard ts (n + length toks) = false.
Proof.
  intros ts n toks rest Hs Hne F.
  destruct (exists_last Hne) as (a & t & ->).
  rewrite length_app. cbn [length]. rewrite Nat.add_1_r, Nat.add_succ_r. cbn [after_hard].
  assert (Hn : nth_error ts (n + length a) = Some t).
  { rewrite <- nth_error_skipn, Hs, <- app_assoc. cbn [app].
    rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
  rewrite Hn. apply Forall_app in F as [_ F]. apply Forall_cons_iff in F as [Ft _].
  destruct t; try reflexivity. destruct (Ft ws eq_refl).
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
  pstep ts n t v = pv_setmode (PMRegion b kids d e (txt ++ tok_region b t)) v.
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
  after_hard ts n = false -> (forall s, x <> Str s) ->
  linked ts n (pv_add x (pv_setmode PMNormal v)) prev
    (IText false "" prev (oemit (mk x) (oview cm v))).
Proof.
  intros ts n v cm x prev Ha Hx. apply linked_normal; [exact Ha| |].
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

Fixpoint no_rbrack (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c rest => negb (Ascii.eqb c rbrack) && no_rbrack rest
  end.

Local Lemma iscan_ref : forall bytes kids im open label o,
  no_rbrack bytes = true -> no_bslash bytes = true ->
  iscan_str bytes (IReference kids im open false label o)
  = IReference kids im open false (label ++ bytes) o.
Proof.
  induction bytes as [|c bytes IH]; intros kids im open label o H Hb;
    [rewrite append_empty_r; reflexivity|].
  cbn [no_rbrack] in H. apply andb_true_iff in H as [Hc H]. apply negb_true_iff in Hc.
  cbn [no_bslash] in Hb. apply andb_true_iff in Hb as [Hbc Hb]. apply negb_true_iff in Hbc.
  cbn [iscan_str]. unfold istep. cbn [istep_at]. rewrite Hbc, Hc, IH by assumption.
  cbn [tpush]. rewrite append_assoc. reflexivity.
Qed.

Definition is_rb (t : token) : bool :=
  match t with TText c => Ascii.eqb c rbrack | TClose _ => true | _ => false end.

Local Lemma rbrack_at_cons : forall t i rest,
  rbrack_at i (t :: rest) = if is_rb t then Some i else rbrack_at (S i) rest.
Proof. intros [c| |k mr op cl| |b|c|ws|ws] i rest; reflexivity. Qed.

Local Lemma no_rbrack_chars : forall c n, Ascii.eqb c rbrack = false -> no_rbrack (chars c n) = true.
Proof. intros c n H. induction n as [|n IH]; [reflexivity|]. cbn. rewrite H, IH. reflexivity. Qed.

Local Lemma no_rbrack_app : forall a b, no_rbrack (a ++ b) = (no_rbrack a && no_rbrack b)%bool.
Proof. induction a as [|c a IH]; intros b; [reflexivity|]. cbn. rewrite IH. apply andb_assoc. Qed.

Local Lemma tok_rb : forall t, no_bslash (tok_text t) = true ->
  if is_rb t then tok_text t = one rbrack else no_rbrack (tok_text t) = true.
Proof.
  intros [c| |k mr op cl| |b|c|ws|ws] Hb; try reflexivity; try discriminate Hb.
  - cbn. destruct (Ascii.eqb c rbrack) eqn:E; [apply Ascii.eqb_eq in E; subst c; reflexivity|].
    reflexivity.
  - destruct (dchar_plain k) as (_ & _ & _ & Hrk).
    cbn [is_rb]. destruct mr; [destruct op|]; cbn [tok_text]; unfold dtoken;
      rewrite ?no_rbrack_app; cbn [one append no_rbrack];
      rewrite ?(no_rbrack_chars _ _ Hrk); reflexivity.
Qed.

Local Lemma iscan_dest : forall bytes kids open e depth dst sh o ds,
  dfeed bytes (DS e depth dst) = Some ds ->
  iscan_str bytes (IDest kids false open e depth dst sh o)
  = IDest kids false open (ds_esc ds) (ds_depth ds) (ds_dst ds) (iscan_str bytes sh) o.
Proof.
  intros bytes kids open e depth dst sh o ds Hp.
  pose proof (iscan_wrap bytes [WL kids open (DS e depth dst) o] sh) as E.
  cbn [wrap map wl_after wl_kids wl_open wl_ds wl_o ds_esc ds_depth ds_dst] in E.
  rewrite Hp in E. apply E. constructor; [|constructor].
  cbn [wl_ds]. rewrite Hp. discriminate.
Qed.

Local Lemma no_nl_drop : forall s, no_nl s = drop_nl s.
Proof. induction s as [|c s IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.


(*
A line
------
*)

Local Lemma linked_rres : forall ts n v prev core,
  linked ts n v prev core -> linked ts n v prev (rres core).
Proof.
  intros ts n v prev core L. unfold linked in *.
  destruct (pv_mode v) as [|[|] kids d e txt].
  - destruct L as (Ha & t & o & -> & Hs). split; [exact Ha|]. exists t, o. split; [reflexivity|exact Hs].
  - destruct L as (Hd & open & depth & sh & cm & He & Hne & ->).
    split; [exact Hd|]. exists open, depth, (rres sh), cm. auto.
  - destruct L as (Hd & He & Hk & open & cm & ->). split; [exact Hd|].
    split; [exact He|]. split; [exact Hk|]. exists open, cm. reflexivity.
Qed.

Local Lemma scanned_nil : forall ts n v ws core prev,
  vinv ts n v -> Forall (never ts n) ws -> linked ts n v prev core ->
  scanned ts n v ws core prev "".
Proof.
  intros ts n v ws core prev V Fn L. exists ws, (rres core), prev.
  cbn [lex length prun iscan_str]. rewrite Nat.add_0_r, rres_wrap.
  split; [reflexivity|]. split; [exact V|]. split; [exact Fn|left; apply linked_rres, L].
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

(* The same from `note_ok`, in text mode. *)
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

Local Lemma lex_rbrack : forall prev s',
  lex prev 0 (String rbrack s')
  = (if starts_with lparen s' then TClose true
     else if starts_with lbrack s' then TClose false else TText rbrack)
    :: lex (Some rbrack) 0 s'.
Proof. reflexivity. Qed.

Local Lemma no_bslash_chars : forall c n, is_bslash c = false -> no_bslash (chars c n) = true.
Proof. intros c n H. induction n as [|n IH]; [reflexivity|]. cbn [chars no_bslash]. rewrite H, IH. reflexivity. Qed.

Local Lemma no_bslash_dtoken : forall k, no_bslash (dtoken k) = true.
Proof. intros k. apply no_bslash_chars, dchar_nb. Qed.

Local Lemma toks_no_hard : forall toks, no_bslash (toks_text toks) = true ->
  Forall (fun t => forall ws, t <> THard ws) toks.
Proof.
  induction toks as [|t toks IH]; intros H; [constructor|].
  cbn [toks_text] in H. rewrite no_bslash_app in H. apply andb_true_iff in H as [Ht H].
  constructor; [|exact (IH H)]. intros ws E. subst t. discriminate Ht.
Qed.

Local Lemma toks_no_hard0 : forall toks, no_bslash (toks_text toks) = true ->
  Forall (fun t => t <> THard EmptyString) toks.
Proof.
  intros toks H. eapply Forall_impl; [|exact (toks_no_hard toks H)]. intros t Ht. apply Ht.
Qed.

Local Lemma after_one : forall ts n t rest, skipn n ts = t :: rest ->
  no_bslash (tok_text t) = true -> after_hard ts (S n) = false.
Proof.
  intros ts n t rest Hs Hb. pose proof (after_chunk ts n [t] rest Hs ltac:(discriminate)) as E.
  cbn [length] in E. rewrite Nat.add_1_r in E. apply E.
  apply (toks_no_hard [t]). cbn [toks_text]. rewrite append_empty_r. exact Hb.
Qed.

Local Lemma tok_dest_plain : forall t, no_bslash (tok_text t) = true -> tok_dest t = tok_text t.
Proof. intros [c| |k mr op cl| |b|c|ws|ws] H; try reflexivity. discriminate H. Qed.

Local Lemma dfeed_plain_tok : forall t d dst ds, tok_plain t -> no_bslash (tok_text t) = true ->
  dfeed (tok_text t) (DS false d dst) = Some ds -> ds = DS false (ds_depth ds) (dst ++ tok_text t).
Proof.
  intros t d dst ds Hp Hb E. rewrite (tok_dfeed t d dst Hp) in E.
  destruct t as [c| |k mr op cl| |b|c|ws|ws]; try discriminate Hb;
    try (injection E as <-; reflexivity).
  destruct (pstep_byte c d); [injection E as <-; reflexivity|discriminate].
Qed.

Local Ltac nb := unfold marked_open, dtoken; rewrite ?no_bslash_app;
  cbn [no_bslash one append]; rewrite ?no_bslash_chars by apply dchar_nb;
  rewrite ?dchar_nb; reflexivity.

(* Escapes
   -------

   A line that begins with a backslash: an escaped byte, an escaped run
   of whitespace, or the hard break that ends the line. *)

Fixpoint skip_prev (p : option ascii) (k : nat) (s : string) : option ascii :=
  match k, s with S k', String c r => skip_prev (Some c) k' r | _, _ => p end.

Local Lemma lex_skip_gen : forall s p k, lex p k s = lex (skip_prev p k s) 0 (sdrop k s).
Proof. induction s as [|c s IH]; intros p [|k]; try reflexivity. cbn [lex skip_prev sdrop]. apply IH. Qed.

Local Lemma skip_prev_run : forall s p,
  skip_prev p (String.length (ws_run s)) s = str_last (ws_run s) p.
Proof.
  induction s as [|c s IH]; intros p; [reflexivity|]. cbn [ws_run].
  destruct (is_ws c); [cbn [String.length skip_prev str_last]; apply IH|reflexivity].
Qed.

Local Lemma lex_bs : forall p s,
  lex p 0 (String bslash s)
  = if is_blank s then [THard s]
    else match s with
         | String d r =>
             if is_ws d
             then TEscWs (ws_run s)
                    :: lex (str_last (ws_run s) (Some bslash)) 0 (sdrop (String.length (ws_run s)) s)
             else TEsc d :: lex (Some d) 0 r
         | EmptyString => [THard EmptyString]
         end.
Proof.
  intros p s. cbn [lex]. change (is_bslash bslash) with true. cbn iota.
  destruct (is_blank s) eqn:Bl; [rewrite lex_skip_all; reflexivity|].
  destruct s as [|d r]; [discriminate|]. destruct (is_ws d) eqn:Wd.
  - rewrite lex_skip_gen, skip_prev_run. reflexivity.
  - reflexivity.
Qed.

Local Lemma after_tok : forall ts n t rest, skipn n ts = t :: rest ->
  (forall ws, t <> THard ws) -> after_hard ts (S n) = false.
Proof.
  intros ts n t rest Hs Ht. cbn [after_hard].
  rewrite <- (Nat.add_0_r n), <- nth_error_skipn, Hs. cbn.
  destruct t; try reflexivity. destruct (Ht ws eq_refl).
Qed.

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

Local Lemma iscan_ref_bs : forall d kids im open label o,
  iscan_str (String bslash (one d)) (IReference kids im open false label o)
  = IReference kids im open false (label ++ String bslash (one d)) o.
Proof. intros. reflexivity. Qed.

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

Local Lemma blank_no_rbrack : forall w, is_blank w = true -> no_rbrack w = true /\ no_bslash w = true.
Proof.
  induction w as [|c w IH]; intros H; [split; reflexivity|]. cbn [is_blank] in H.
  apply andb_true_iff in H as [Hc H]. destruct (IH H) as [H1 H2].
  destruct (blank_byte c Hc) as (Hb & _ & _ & Hp).
  cbn [no_rbrack no_bslash]. rewrite H1, H2, Hb, andb_true_r.
  split; [|reflexivity]. destruct c as [[] [] [] [] [] [] [] []]; try discriminate Hc; reflexivity.
Qed.

Local Lemma iscan_ref_ws : forall c w kids im open label o, is_blank w = true ->
  iscan_str (String bslash (String c w)) (IReference kids im open false label o)
  = IReference kids im open false (label ++ String bslash (String c w)) o.
Proof.
  intros c w kids im open label o H. destruct (blank_no_rbrack w H) as [H1 H2].
  change (iscan_str (String bslash (String c w)) (IReference kids im open false label o))
    with (iscan_str w (IReference kids im open false (label ++ String bslash (one c)) o)).
  rewrite iscan_ref by assumption. rewrite append_assoc. reflexivity.
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

Local Lemma scan_esc : forall ts after len, scan_ih ts after len ->
  forall s' prev n v ws core,
    String.length (String bslash s') <= S len -> over_alphabet (String bslash s') = true ->
    note_ok prev core (String bslash s') ->
    skipn n ts = (lex prev 0 (String bslash s') ++ after)%list ->
    vinv ts n v -> Forall (never ts n) ws -> Forall esc_off ws -> linked ts n v prev core ->
    scanned ts n v ws core prev (String bslash s').
Proof.
  intros ts after len IH s' prev n v ws core Hl Ha Hp Hsk V Fn Fe L.
  pose proof (fun bytes rest toks prev1 extra core1 =>
                scan_advance ts after len IH (String bslash s') prev n v ws core
                  bytes rest toks prev1 extra core1 Hl Ha Hsk V Fn Fe) as A.
  pose proof (over_alphabet_bslash s' Ha) as Ha1.
  pose proof V as (Ok & Ti & _).
  destruct (is_blank s') eqn:Bl.
  { (* a hard break: the rest of the line *)
    assert (El : lex prev 0 (String bslash s') = [THard s']) by (rewrite lex_bs, Bl; reflexivity).
    rewrite El in Hsk. cbn [app] in Hsk.
    pose proof (skipn_cons_tail ts n _ _ Hsk) as Hsk1.
    assert (Hpl : tok_plain (THard s')) by exact Bl.
    assert (Hn : nth_error ts n = Some (THard s'))
      by (rewrite <- (Nat.add_0_r n), <- nth_error_skipn, Hsk; reflexivity).
    assert (Hl1 : hard_last [THard s']).
    { intros a w b E. destruct a as [|y a]; [injection E as _ <-; reflexivity|].
      destruct a; discriminate E. }
    destruct (layers_step ts n ws [THard s'] after Fn Fe Hsk
                (Forall_cons _ Hpl (Forall_nil _)) Hl1) as (Hopen & Fn' & _).
    cbn [toks_text length tok_text] in Hopen, Fn'. rewrite append_empty_r in Hopen, Fn'.
    rewrite Nat.add_1_r in Fn'.
    pose proof (vinv_step ts n (THard s') v V Hpl Hn) as V'.
    unfold scanned. rewrite El. cbn [length prun]. rewrite Nat.add_1_r.
    exists (map (wl_after (String bslash s')) ws).
    rewrite iscan_wrap by exact Hopen. rewrite rres_wrap.
    unfold linked in L. destruct (pv_mode v) as [|[|] kids d0 e txt] eqn:Em.
    - destruct L as (Hah & txt & o & -> & Hs).
      rewrite iscan_bs_blank by exact Bl.
      exists (esc_pending s' txt (Some bslash) o), (Some bslash).
      split; [destruct s'; reflexivity|]. split; [exact V'|]. split; [exact Fn'|].
      right. left. exists s', txt, (Some bslash), o, v.
      split; [cbn [after_hard]; rewrite Hn; reflexivity|]. split; [exact Bl|]. split; [reflexivity|]. split; [exact Em|]. split; [exact Hs|].
      unfold pstep. rewrite Em. reflexivity.
    - destruct L as (Hd & open & depth & sh & cm & He & Hne & ->).
      rewrite Hsk in He. cbn [paren_close] in He.
      assert (Rs := region_stay ts n (THard s') v true kids d0 e txt Em Hd
                      ltac:(intros e' E'; rewrite E' in He; symmetry in He;
                            apply Precedence.paren_close_ge in He; lia)).
      rewrite Rs in V' |- *.
      pose proof (dfeed_esc_blank s' depth txt Bl) as Ed.
      destruct s' as [|w ws1].
      + rewrite (iscan_dest _ _ _ _ _ _ _ _ _ Ed). cbn [ds_esc ds_depth ds_dst].
        exists (IDest (map mk kids) false open true depth txt (rres (iscan_str (String bslash "") sh))
                  (oview cm v)), None.
        split; [reflexivity|]. split; [exact V'|]. split; [exact Fn'|].
        right. right. right. exists kids, d0, e, txt, open, depth, (rres (iscan_str (String bslash "") sh)), cm.
        cbn [pv_setmode pv_mode tok_region tok_dest tok_text].
        split; [reflexivity|]. split; [lia|]. rewrite Hsk1. split; [exact He|]. split; [exact Hne|].
        reflexivity.
      + rewrite (iscan_dest _ _ _ _ _ _ _ _ _ Ed). cbn [ds_esc ds_depth ds_dst].
        exists (IDest (map mk kids) false open false depth (txt ++ String bslash (String w ws1))
                  (rres (iscan_str (String bslash (String w ws1)) sh)) (oview cm v)), None.
        split; [reflexivity|]. split; [exact V'|]. split; [exact Fn'|].
        left. unfold linked. cbn [pv_setmode pv_mode tok_region tok_dest tok_text]. split; [lia|].
        exists open, depth, (rres (iscan_str (String bslash (String w ws1)) sh)), cm.
        rewrite Hsk1. split; [exact He|]. split; [exact Hne|reflexivity].
    - destruct L as (Hd & He & Hk & open & cm & ->).
      rewrite Hsk in He. cbn [rbrack_at] in He.
      assert (Rs := region_stay ts n (THard s') v false kids d0 e txt Em Hd
                      ltac:(intros e' E'; rewrite E' in He; symmetry in He;
                            apply Precedence.rbrack_at_ge in He; lia)).
      rewrite Rs in V' |- *.
      destruct s' as [|w ws1].
      + exists (IReference (map mk kids) false open true txt (oview cm v)), None.
        split; [reflexivity|]. split; [exact V'|]. split; [exact Fn'|].
        right. right. left. exists kids, d0, e, txt, open, cm.
        cbn [pv_setmode pv_mode tok_region tok_text].
        split; [reflexivity|]. split; [lia|]. rewrite Hsk1. split; [exact He|]. split; [exact Hk|].
        reflexivity.
      + cbn [is_blank] in Bl. apply andb_true_iff in Bl as [_ Bl].
        rewrite iscan_ref_ws by exact Bl.
        exists (IReference (map mk kids) false open false (txt ++ String bslash (String w ws1))
                  (oview cm v)), None.
        split; [reflexivity|]. split; [exact V'|]. split; [exact Fn'|].
        left. unfold linked. cbn [pv_setmode pv_mode tok_region tok_text]. split; [lia|].
        rewrite Hsk1. split; [exact He|]. split; [exact Hk|]. exists open, cm. reflexivity. }
  destruct s' as [|d r]; [discriminate|].
  destruct (is_ws d) eqn:Wd.
  { (* an escaped run of whitespace *)
    set (w1 := ws_run r).
    assert (Hw : ws_run (String d r) = String d w1) by (cbn [ws_run]; rewrite Wd; reflexivity).
    set (rest := sdrop (String.length w1) r).
    assert (Ew : String d r = (String d w1 ++ rest)%string).
    { pose proof (ws_run_sdrop (String d r)) as E. rewrite Hw in E. symmetry. exact E. }
    assert (Hwb : is_blank (String d w1) = true) by (rewrite <- Hw; apply ws_run_blank).
    assert (Ha2 : over_alphabet rest = true) by (apply over_alphabet_ws_run, Ha1).
    destruct (str_last_blank w1 d Hwb) as (x & Ex & Hx).
    assert (El : lex prev 0 (String bslash (String d r))
                 = ([TEscWs (String d w1)] ++ lex (Some x) 0 rest)%list).
    { rewrite lex_bs, Bl, Wd, Hw. cbn [str_last String.length sdrop]. rewrite Ex. reflexivity. }
    assert (Hnx : forall c', get 0 rest = Some c' -> is_ws c' = false).
    { intros c' E. apply (ws_run_next (String d r)). rewrite Hw. exact E. }
    rewrite El in Hsk. cbn [app] in Hsk.
    pose proof (skipn_cons_tail ts n _ _ Hsk) as Hsk1.
    assert (Step : forall core1,
              note_ok (Some x) core1 rest ->
              settles (iscan_str (String bslash (String d w1)) core) core1 (get 0 rest) ->
              linked ts (S n) (pstep ts n (TEscWs (String d w1)) v) (Some x) core1 ->
              scanned ts n v ws core prev (String bslash (String d r))).
    { intros core1 N1 Hset L1.
      apply (A (String bslash (String d w1)) rest [TEscWs (String d w1)] (Some x) [] core1);
        [rewrite Ew; reflexivity|discriminate|exact El|cbn; rewrite append_empty_r; reflexivity
        |constructor; [discriminate|constructor]|exact Ha2|exact N1|exact Hset|constructor|constructor|].
      cbn [length prun]. rewrite Nat.add_1_r. exact L1. }
    unfold linked in L. destruct (pv_mode v) as [|[|] kids d0 e txt] eqn:Em.
    - destruct L as (Hah & txt & o & -> & Hs).
      pose proof Hs as (v0 & cm & Eo & Ht & Ev).
      assert (Hrest : exists c', get 0 rest = Some c').
      { destruct rest as [|c' r'] eqn:Er; [|exists c'; reflexivity].
        exfalso. rewrite append_empty_r in Ew. rewrite Ew in Bl. rewrite Hwb in Bl. discriminate. }
      destruct Hrest as (c' & G).
      pose proof (Hnx c' G) as Hc'.
      assert (Scan : iscan_str (String bslash (String d w1)) (IText false txt prev o)
                     = IEscWs (String d w1) txt (Some bslash) o)
        by exact (iscan_bs_blank (String d w1) txt prev o Hwb).
      destruct (Ascii.eqb d " "%char) eqn:Sp.
      + (* a non-breaking space, and the rest of the run as text *)
        apply Ascii.eqb_eq in Sp. subst d.
        apply (Step (IText false w1 (Some x) (oemit (mk NonBreakingSpace) (flush_text txt o)))).
        * left. cbn [prev_ok]. apply ws_follow, Hx.
        * rewrite G. cbn [settles]. rewrite Scan. unfold istep. cbn [istep_at].
          rewrite Hc', iescws_cons, Ascii.eqb_refl, Ex. reflexivity.
        * apply linked_normal.
          { apply (after_tok ts n _ _ Hsk). discriminate. }
          { apply pstep_mode; [exact Em|discriminate]. }
          unfold pstep. rewrite Em. cbn [nbsp_rest]. rewrite Ascii.eqb_refl.
          exists (pv_add NonBreakingSpace v), cm. split; [|split].
          -- change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s txt o)
               with (flush_text txt o).
             rewrite Eo, (flush_view cm txt v0 Ht), <- Ev.
             apply oemit_view. discriminate.
          -- apply top_add_nonstr. discriminate.
          -- unfold add_text. reflexivity.
      + (* a tab or a carriage return first: the backslash and the run as text *)
        apply (Step (IText false (txt ++ String bslash (String d w1)) (Some x) o)).
        * left. cbn [prev_ok]. apply ws_follow, Hx.
        * rewrite G. cbn [settles]. rewrite Scan. unfold istep. cbn [istep_at].
          rewrite Hc', iescws_cons, Sp. cbn [str_last]. rewrite Ex. reflexivity.
        * apply linked_normal.
          { apply (after_tok ts n _ _ Hsk). discriminate. }
          { apply pstep_mode; [exact Em|discriminate]. }
          unfold pstep. rewrite Em. cbn [nbsp_rest]. rewrite Sp.
          apply sim_text; [exact Hs|reflexivity].
    - destruct L as (Hd & open & depth & sh & cm & He & Hne & ->).
      rewrite Hsk in He. cbn [paren_close] in He.
      apply (Step (IDest (map mk kids) false open false depth (txt ++ String bslash (String d w1))
                    (iscan_str (String bslash (String d w1)) sh) (oview cm v))).
      + right. intros t p o' E. discriminate E.
      + rewrite (iscan_dest _ _ _ _ _ _ _ _ (DS false depth (txt ++ String bslash (String d w1)))).
        * apply settles_refl.
        * assert (Hpl : tok_plain (TEscWs (String d w1))) by (split; [exact Hwb|discriminate]).
          pose proof (tok_dfeed (TEscWs (String d w1)) depth txt Hpl) as E.
          cbn [tok_text tok_dest] in E. rewrite E. reflexivity.
      + rewrite (region_stay ts n _ v true kids d0 e txt Em Hd).
        2: { intros e' E'. rewrite E' in He. symmetry in He.
             apply Precedence.paren_close_ge in He. lia. }
        unfold linked. cbn [pv_setmode pv_mode tok_region tok_dest tok_text]. split; [lia|].
        exists open, depth, (iscan_str (String bslash (String d w1)) sh), cm.
        rewrite Hsk1. split; [exact He|]. split; [exact Hne|reflexivity].
    - destruct L as (Hd & He & Hk & open & cm & ->).
      rewrite Hsk in He. cbn [rbrack_at] in He.
      apply (Step (IReference (map mk kids) false open false (txt ++ String bslash (String d w1))
                    (oview cm v))).
      + right. intros t p o' E. discriminate E.
      + cbn [is_blank] in Hwb. apply andb_true_iff in Hwb as [_ Hwb].
        rewrite iscan_ref_ws by exact Hwb. apply settles_refl.
      + rewrite (region_stay ts n _ v false kids d0 e txt Em Hd).
        2: { intros e' E'. rewrite E' in He. symmetry in He.
             apply Precedence.rbrack_at_ge in He. lia. }
        unfold linked. cbn [pv_setmode pv_mode tok_region tok_text]. split; [lia|].
        rewrite Hsk1. split; [exact He|]. split; [exact Hk|].
        exists open, cm. reflexivity. }
  (* an escaped byte *)
  assert (El : lex prev 0 (String bslash (String d r)) = ([TEsc d] ++ lex (Some d) 0 r)%list)
    by (rewrite lex_bs, Bl, Wd; reflexivity).
  rewrite El in Hsk. cbn [app] in Hsk.
  pose proof (skipn_cons_tail ts n _ _ Hsk) as Hsk1.
  assert (Step : forall core1,
            note_ok (Some d) core1 r ->
            settles (iscan_str (String bslash (one d)) core) core1 (get 0 r) ->
            linked ts (S n) (pstep ts n (TEsc d) v) (Some d) core1 ->
            scanned ts n v ws core prev (String bslash (String d r))).
  { intros core1 N1 Hset L1.
    apply (A (String bslash (one d)) r [TEsc d] (Some d) [] core1);
      [reflexivity|discriminate|exact El|reflexivity|constructor; [discriminate|constructor]
      |exact Ha1|exact N1|exact Hset|constructor|constructor|].
    cbn [length prun]. rewrite Nat.add_1_r. exact L1. }
  unfold linked in L. destruct (pv_mode v) as [|[|] kids d0 e txt] eqn:Em.
  - destruct L as (Hah & txt & o & -> & Hs).
    apply (Step (IText false (txt ++ esc_text d) (Some d) o)).
    + right. intros t p o' E. injection E as <- _ _.
      destruct txt; [|reflexivity]. cbn. destruct (esc_text d) eqn:E'; [destruct (esc_text_ne d E')|reflexivity].
    + cbn [iscan_str one]. rewrite istep_bslash_text, istep_esc_byte by exact Wd. apply settles_refl.
    + apply linked_normal.
      * apply (after_tok ts n (TEsc d) _ Hsk). discriminate.
      * apply pstep_mode; [exact Em|discriminate].
      * unfold pstep. rewrite Em. apply sim_text; [exact Hs|].
        destruct (esc_text d) eqn:E'; [destruct (esc_text_ne d E')|reflexivity].
  - destruct L as (Hd & open & depth & sh & cm & He & Hne & ->).
    rewrite Hsk in He. cbn [paren_close] in He.
    apply (Step (IDest (map mk kids) false open false depth (txt ++ esc_text d)
                  (iscan_str (String bslash (one d)) sh) (oview cm v))).
    + right. intros t p o' E. discriminate E.
    + rewrite (iscan_dest _ _ _ _ _ _ _ _ (DS false depth (txt ++ esc_text d))).
      * apply settles_refl.
      * exact (tok_dfeed (TEsc d) depth txt Logic.I).
    + rewrite (region_stay ts n (TEsc d) v true kids d0 e txt Em Hd).
      2: { intros e' E'. rewrite E' in He. symmetry in He.
           apply Precedence.paren_close_ge in He. lia. }
      unfold linked. cbn [pv_setmode pv_mode tok_region tok_dest]. split; [lia|].
      exists open, depth, (iscan_str (String bslash (one d)) sh), cm.
      rewrite Hsk1. split; [exact He|]. split; [exact Hne|reflexivity].
  - destruct L as (Hd & He & Hk & open & cm & ->).
    rewrite Hsk in He. cbn [rbrack_at] in He.
    apply (Step (IReference (map mk kids) false open false (txt ++ String bslash (one d)) (oview cm v))).
    + right. intros t p o' E. discriminate E.
    + rewrite iscan_ref_bs. apply settles_refl.
    + rewrite (region_stay ts n (TEsc d) v false kids d0 e txt Em Hd).
      2: { intros e' E'. rewrite E' in He. symmetry in He.
           apply Precedence.rbrack_at_ge in He. lia. }
      unfold linked. cbn [pv_setmode pv_mode tok_region tok_text]. split; [lia|].
      rewrite Hsk1. split; [exact He|]. split; [exact Hk|].
      exists open, cm. reflexivity.
Qed.

Local Lemma scan_sim : forall ts after len, scan_ih ts after len.
Proof.
  intros ts after. induction len as [|len IH]; intros s prev n v ws core Hl Ha Hp Hsk V Fn Fe L;
    destruct s as [|c s']; try (apply scanned_nil; assumption).
  { cbn [String.length] in Hl. lia. }
  pose proof (fun bytes rest toks prev1 extra core1 =>
                scan_advance ts after len IH (String c s') prev n v ws core
                  bytes rest toks prev1 extra core1 Hl Ha Hsk V Fn Fe) as A.
  assert (A' : forall bytes rest toks prev1 extra core1,
            String c s' = (bytes ++ rest)%string -> bytes <> "" ->
            lex prev 0 (String c s') = (toks ++ lex prev1 0 rest)%list ->
            toks_text toks = bytes -> no_bslash bytes = true ->
            note_ok prev1 core1 rest ->
            settles (iscan_str bytes core) (wrap extra core1) (get 0 rest) ->
            Forall (never ts (n + length toks)) extra -> Forall esc_off extra ->
            linked ts (n + length toks) (prun ts n toks v) prev1 core1 ->
            scanned ts n v ws core prev (String c s')).
  { intros bytes rest toks prev1 extra core1 E1 E2 E3 E4 Nb E5 E6 E7 E8 E9.
    apply (A bytes rest toks prev1 extra core1 E1 E2 E3 E4); try assumption.
    - apply toks_no_hard0. rewrite E4. exact Nb.
    - pose proof Ha as Ha2. rewrite E1 in Ha2. exact (over_alphabet_app_r _ _ Nb Ha2). }
  pose proof V as (Ok & Ti & _). pose proof Ok as (_ & _ & B & _).
  destruct (is_bslash c) eqn:Eb.
  { unfold is_bslash in Eb. apply Ascii.eqb_eq in Eb. subst c.
    exact (scan_esc ts after len IH s' prev n v ws core Hl Ha Hp Hsk V Fn Fe L). }
  unfold linked in L. destruct (pv_mode v) as [|b kids d e txt] eqn:Em.
  2: { (* in a region *)
    destruct (lex_cons c s' prev Eb Ha)
      as (t & r & prev1 & Es & El & Hp1 & _ & Hlast & Hb & _).
    pose proof (lex_plain _ prev 0 Ha) as Fp. rewrite El in Fp.
    apply Forall_cons_iff in Fp as [Ft _].
    rewrite El in Hsk. cbn [app] in Hsk.
    pose proof (skipn_cons_tail ts n t _ Hsk) as Hsk1.
    assert (Step : forall core1,
              settles (iscan_str (tok_text t) core) core1 (get 0 r) ->
              linked ts (S n) (pstep ts n t v) prev1 core1 ->
              scanned ts n v ws core prev (String c s')).
    { intros core1 Hset L1.
      apply (A' (tok_text t) r [t] prev1 [] core1);
        [exact Es|apply tok_text_ne|exact El|cbn; apply append_empty_r
        |exact Hb|left; exact Hp1|exact Hset|constructor|constructor|].
      cbn [length prun]. rewrite Nat.add_1_r. exact L1. }
    pose proof (after_one ts n t _ Hsk Hb) as Hah.
    destruct b.
    - destruct L as (Hd & open & depth & sh & cm & He & Hne & ->).
      rewrite Hsk, (paren_close_cons t depth txt n _ Ft) in He.
      destruct (dfeed (tok_text t) (DS false depth txt)) as [ds|] eqn:Pd.
      + pose proof (dfeed_plain_tok t depth txt ds Ft Hb Pd) as Eds.
        apply (Step (IDest (map mk kids) false open false (ds_depth ds) (txt ++ tok_text t)
                      (iscan_str (tok_text t) sh) (oview cm v))).
        * rewrite (iscan_dest _ _ _ _ _ _ _ _ _ Pd).
          destruct ds as [e1 dp1 dst1]. injection Eds as -> ->. apply settles_refl.
        * rewrite (region_stay ts n t v true kids d e txt Em Hd).
          2: { intros e' E'. rewrite E' in He. symmetry in He.
               apply Precedence.paren_close_ge in He. lia. }
          unfold linked. cbn [pv_setmode pv_mode]. split; [lia|].
          cbn [tok_region]. rewrite (tok_dest_plain t Hb).
          exists open, (ds_depth ds), (iscan_str (tok_text t) sh), cm.
          rewrite Hsk1. split; [exact He|]. split; [exact Hne|reflexivity].
      + destruct (dfeed_none t depth txt Ft Pd) as [Et ->]. subst e.
        pose proof (Hlast _ Et) as ->.
        apply (Step (IText false "" (Some rparen)
                       (oemit (mk (region_node true (map mk kids) txt)) (oview cm v)))).
        * rewrite Et. unfold region_node. rewrite no_nl_drop. apply settles_refl.
        * rewrite (region_close ts n t v true kids d txt Em).
          apply region_close_linked; [exact Hah|apply region_node_nonstr].
    - destruct L as (Hd & He & Hk & open & cm & ->).
      rewrite Hsk, rbrack_at_cons in He. pose proof (tok_rb t Hb) as Hrb.
      destruct (is_rb t).
      + subst e. pose proof (Hlast _ Hrb) as ->.
        apply (Step (IText false "" (Some rbrack)
                       (oemit (mk (region_node false (map mk kids) txt)) (oview cm v)))).
        * rewrite Hrb. apply settles_refl.
        * rewrite (region_close ts n t v false kids d txt Em).
          apply region_close_linked; [exact Hah|apply region_node_nonstr].
      + apply (Step (IReference (map mk kids) false open false (txt ++ tok_text t) (oview cm v))).
        * rewrite (iscan_ref _ _ _ _ _ _ Hrb Hb). apply settles_refl.
        * rewrite (region_stay ts n t v false kids d e txt Em Hd).
          2: { intros e' E'. rewrite E' in He. symmetry in He.
               apply Precedence.rbrack_at_ge in He. lia. }
          unfold linked. cbn [pv_setmode pv_mode]. split; [lia|].
          rewrite Hsk1. split; [exact He|]. split; [exact Hk|].
          exists open, cm. reflexivity. }
  (* in text mode *)
  destruct L as (Hah & txt & o & -> & Hs).
  pose proof Hs as (v0 & cm & Eo & Ht & Ev).
  pose proof Ha as Ha'. apply (over_alphabet_cons c s' Eb) in Ha' as (Hc & Hf & Hs').
  assert (Hn : no_note c txt prev = true) by exact (no_note_ok' prev c s' txt prev o Hp).
  assert (Nrm : forall bytes rest toks prev1 txt' o',
            String c s' = (bytes ++ rest)%string -> bytes <> "" ->
            lex prev 0 (String c s') = (toks ++ lex prev1 0 rest)%list ->
            toks_text toks = bytes -> no_bslash bytes = true -> prev_ok prev1 rest = true ->
            settles (iscan_str bytes (IText false txt prev o)) (IText false txt' prev1 o')
              (get 0 rest) ->
            pv_mode (prun ts n toks v) = PMNormal -> sim (prun ts n toks v) txt' o' ->
            scanned ts n v ws (IText false txt prev o) prev (String c s')).
  { intros bytes rest toks prev1 txt' o' H1 H2 H3 H4 Nb H5 H6 H7 H8.
    apply (A' bytes rest toks prev1 [] (IText false txt' prev1 o')); try assumption;
      [left; exact H5|constructor|constructor|].
    apply linked_normal; [|exact H7|exact H8].
    apply (after_chunk ts n toks (lex prev1 0 rest ++ after)).
    - rewrite Hsk, H3, app_assoc. reflexivity.
    - intros ->. cbn in H4. subst bytes. contradiction.
    - apply toks_no_hard. rewrite H4. exact Nb. }
  destruct (Ascii.eqb c lbrack) eqn:Elk.
  { apply Ascii.eqb_eq in Elk. subst c.
    apply (Nrm (one lbrack) s' [TOpen] (Some lbrack) "" (bpush false (flush_text txt o)));
      [reflexivity|discriminate|reflexivity|reflexivity|reflexivity|exact Hf| | |].
    - cbn [iscan_str one]. unfold istep. cbn [istep_at].
      rewrite (ilead_lbrack txt prev o (note_free' prev lbrack s' txt prev o Hp (or_introl eq_refl))).
      apply settles_refl.
    - cbn [prun]. apply pstep_mode; [exact Em|discriminate].
    - cbn [prun]. unfold pstep. rewrite Em. apply open_bracket_sim, Hs. }
  destruct (Ascii.eqb c rbrack) eqn:Erk.
  { apply Ascii.eqb_eq in Erk. subst c.
    assert (Htag : tag_close (flush_text txt o) = None).
    { assert (Hfl : flush_text txt o = oview cm v)
        by (rewrite Eo, Ev; apply flush_view, Ht).
      rewrite Hfl. apply tag_close_oview. }
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
        [reflexivity|discriminate|exact El|cbn; rewrite Et; reflexivity|reflexivity|exact Hf| | |].
      - apply tok_rbrack_text; [exact Htag|exact Hb].
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
                else IReference kids false null_span false "" o1).
    { intros c2 H2. cbn [iscan_str one]. unfold istep at 2. cbn [istep_at].
      rewrite (ilead_rbrack_closed txt prev o Htag). rewrite Eo.
      pose proof (closed_step cm v0 txt c2 content rest' Ht) as Hcs.
      rewrite <- Ev in Hcs. exact (Hcs B Hpc H2). }
    destruct (starts_with lparen s') eqn:S1.
    { (* a destination *)
      destruct s' as [|c2 r]; [discriminate|]. cbn [starts_with] in S1.
      apply Ascii.eqb_eq in S1. subst c2.
      apply (over_alphabet_cons lparen r eq_refl) in Hs' as (Hc2 & _ & Hr').
      assert (El : lex prev 0 (String rbrack (String lparen r))
                   = ([TClose true; TText lparen] ++ lex (Some lparen) 0 r)%list).
      { rewrite lex_rbrack. cbn [starts_with app].
        rewrite (lex_byte lparen (Some rbrack) r eq_refl eq_refl eq_refl eq_refl
                   (alphabet_paren_none lparen Hc2 eq_refl)). reflexivity. }
      assert (Hcp : iscan_str (String rbrack (one lparen)) (IText false txt prev o)
                    = IDest kids false null_span false 0 ""
                        (idest_open kids false null_span o1) o1)
        by exact (Hcl lparen (or_introl eq_refl)).
      clear Hcl. rename Hcp into Hcl.
      destruct (region_end ts n true) as [e|] eqn:R.
      - apply (A' (String rbrack (one lparen)) r [TClose true; TText lparen] (Some lparen) []
                 (IDest kids false null_span false 0 "" (idest_open kids false null_span o1) o1));
          [reflexivity|discriminate|exact El|reflexivity|reflexivity|left; reflexivity
          |rewrite Hcl; apply settles_refl|constructor|constructor|].
        cbn [length prun]. rewrite (pstep_close_found ts n true v content rest' Em Hpc), R.
        rewrite region_first.
        2: { intros e' E'. injection E' as <-.
             pose proof (Precedence.region_end_ge ts n true e R). lia. }
        unfold linked. cbn [pv_mode]. split; [lia|].
        exists null_span, 0, (idest_open kids false null_span o1), cm.
        replace (n + 2) with (S (S n)) by lia.
        split; [symmetry; exact R|]. split; [discriminate|reflexivity].
      - destruct (dest_open_sim cm n content rest' (pv_out v) Nc Cc) as (txt' & o2 & Eo' & S').
        apply (A' (String rbrack (one lparen)) r [TClose true; TText lparen] (Some lparen)
                 [WL kids null_span (DS false 0 "") o1]
                 (IText false (txt' ++ one rbrack ++ one lparen) (Some lparen) o2));
          [reflexivity|discriminate|exact El|reflexivity|reflexivity|left; reflexivity| | | |].
        + rewrite Hcl. cbn [wrap wl_kids wl_open wl_ds wl_o ds_esc ds_depth ds_dst].
          fold kids o1 in Eo'. rewrite Eo'. apply settles_refl.
        + constructor; [|constructor]. unfold never, wl_depth. cbn [wl_ds ds_depth length].
          replace (n + 2) with (S (S n)) by lia. exact R.
        + constructor; [reflexivity|constructor].
        + cbn [length prun]. rewrite (pstep_close_found ts n true v content rest' Em Hpc), R.
          apply linked_normal; [| |exact S'].
          { apply (after_chunk ts n [TClose true; TText lparen] (lex (Some lparen) 0 r ++ after)).
            - rewrite Hsk, El, app_assoc. reflexivity.
            - discriminate.
            - apply (toks_no_hard [TClose true; TText lparen]). reflexivity. }
          unfold pstep. cbn [pv_mode]. rewrite (proj2 (pv_add_live _ _)). reflexivity. }
    destruct (starts_with lbrack s') eqn:S2.
    { (* a reference label *)
      destruct s' as [|c2 r]; [discriminate|]. cbn [starts_with] in S2.
      apply Ascii.eqb_eq in S2. subst c2.
      apply (over_alphabet_cons lbrack r eq_refl) in Hs' as (_ & Hf2 & _).
      assert (Hcp : iscan_str (String rbrack (one lbrack)) (IText false txt prev o)
                    = IReference kids false null_span false "" o1)
        by exact (Hcl lbrack (or_intror eq_refl)).
      clear Hcl. rename Hcp into Hcl.
      set (e := region_end ts n false).
      assert (Ev1 : pstep ts n (TClose false) v
                    = PView rest' (pv_out v) (PMRegion false (List.rev content) n e "")).
      { rewrite (pstep_close_found ts n false v content rest' Em Hpc). unfold e.
        destruct (region_end ts n false); reflexivity. }
      apply (A' (String rbrack (one lbrack)) r [TClose false; TOpen] (Some lbrack) []
               (IReference kids false null_span false "" o1));
        [reflexivity|discriminate|reflexivity|reflexivity|reflexivity|left; exact Hf2
        |rewrite Hcl; apply settles_refl|constructor|constructor|].
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
    pose proof Hs' as Hd'. apply (over_alphabet_cons _ _ (delim_not_bslash d k Hd)) in Hd' as (Hdc & _ & _).
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
      + nb.
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
      + nb.
      + apply follow_ok_plain; assumption.
      + apply tok_marked_partial; [exact Hen|lia|exact Hnext].
      + exact M2.
      + exact S2. }
  destruct (dstyle_of c) as [k|] eqn:Hd.
  2: { (* a plain byte *)
    apply (Nrm (one c) s' [TText c] (Some c) (txt ++ one c) o);
      [reflexivity|discriminate|exact (lex_byte c prev s' Eb Elk Erk Elb Hd)|reflexivity
      |cbn; rewrite Eb; reflexivity|exact Hf| | |].
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
      * nb.
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
      * nb.
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
    + nb.
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

Local Lemma break_linked : forall ts n v prev core rest,
  skipn n ts = TBreak :: rest -> linked_end ts n v prev core ->
  linked ts (S n) (pstep ts n TBreak v) None (ibreak core).
Proof.
  intros ts n v prev core rest Hsk [L|P]; pose proof (skipn_cons_tail ts n _ _ Hsk) as Hsk1;
    assert (Ha1 : after_hard ts (S n) = false) by (apply (after_tok ts n TBreak rest Hsk); discriminate).
  - unfold linked in L. destruct (pv_mode v) as [|[|] kids d e txt] eqn:Em.
    + destruct L as (Ha & txt & o & -> & Hs). destruct Hs as (v0 & cm & -> & Ht & Ev).
      assert (E : ibreak (IText false txt prev (oview cm v0))
                  = IText false "" None (oview cm (pv_add SoftBreak v))).
      { unfold ibreak, ibreak_at, ibreak_flat. cbn [iresolve].
        change (@flush_text_at semantic_pos semantic_inline_cursor (tval txt) (oview cm v0))
          with (flush_text txt (oview cm v0)).
        rewrite (flush_view cm txt v0 Ht), <- Ev.
        change (imk_here SoftBreak) with (mk SoftBreak).
        rewrite (oemit_view cm SoftBreak v) by discriminate. reflexivity. }
      rewrite E. unfold pstep. rewrite Em, Ha.
      apply linked_normal; [exact Ha1|rewrite (proj2 (pv_add_live _ _)); exact Em|].
      exists (pv_add SoftBreak v), cm.
      split; [reflexivity|]. split; [apply top_add_nonstr; discriminate|reflexivity].
    + destruct L as (Hd & open & depth & sh & cm & He & Hne & ->).
      rewrite Hsk in He. cbn [paren_close] in He.
      rewrite (region_stay ts n TBreak v true kids d e txt Em Hd).
      2: { intros e' E'. rewrite E' in He. symmetry in He.
           apply Precedence.paren_close_ge in He. lia. }
      unfold linked. cbn [pv_setmode pv_mode]. split; [lia|].
      exists open, depth, (ibreak sh), cm. rewrite Hsk1.
      split; [exact He|]. split; [exact Hne|reflexivity].
    + destruct L as (Hd & He & Hk & open & cm & ->).
      rewrite Hsk in He. cbn [rbrack_at] in He.
      rewrite (region_stay ts n TBreak v false kids d e txt Em Hd).
      2: { intros e' E'. rewrite E' in He. symmetry in He.
           apply Precedence.rbrack_at_ge in He. lia. }
      unfold linked. cbn [pv_setmode pv_mode]. split; [lia|].
      rewrite Hsk1. split; [exact He|]. split; [exact Hk|].
      exists open, cm. reflexivity.
  - destruct P as [(ws0 & txt & p & o & vb & Ha & Hb & -> & Emb & Hs & ->)
                  |[(kids & d & e & label & open & cm & Em & Hd & He & Hk & ->)
                   |(kids & d & e & dst & open & depth & sh & cm & Em & Hd & He & Hne & ->)]].
    + (* the hard break the line ended with *)
      destruct Hs as (v0 & cm & -> & Ht & ->).
      assert (Em : pv_mode (pv_add HardBreak (pv_trim (add_text txt v0))) = PMNormal)
        by (rewrite (proj2 (pv_add_live _ _)), pv_trim_add; exact Emb).
      unfold pstep. rewrite Em, Ha.
      assert (E : ibreak (esc_pending ws0 txt p (oview cm v0))
                  = IText false "" None (oview cm (pv_add HardBreak (pv_trim (add_text txt v0))))).
      { rewrite (pv_trim_add_text txt v0 Ht).
        assert (X : iesc_hard ws0 txt (oview cm v0)
                    = oview cm (pv_add HardBreak (add_text (strip_trailing_ws txt) v0))).
        { unfold iesc_hard. tred.
          change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s
                    (strip_trailing_ws txt) (oview cm v0))
            with (flush_text (strip_trailing_ws txt) (oview cm v0)).
          rewrite (flush_view cm _ v0 Ht). rewrite imk_here_semantic.
          apply oemit_view. discriminate. }
        rewrite ibreak_pending, X. reflexivity. }
      rewrite E. apply linked_normal; [exact Ha1|exact Em|].
      exists (pv_add HardBreak (pv_trim (add_text txt v0))), cm.
      split; [reflexivity|]. split; [apply top_add_nonstr; discriminate|reflexivity].
    + (* a label whose backslash ended the line *)
      rewrite Hsk in He. cbn [rbrack_at] in He.
      rewrite (region_stay ts n TBreak v false kids d e _ Em Hd).
      2: { intros e' E'. rewrite E' in He. symmetry in He.
           apply Precedence.rbrack_at_ge in He. lia. }
      unfold linked. cbn [pv_setmode pv_mode tok_region tok_text]. split; [lia|].
      rewrite Hsk1. split; [exact He|]. split; [exact Hk|].
      exists open, cm. unfold ibreak, ibreak_at, ibreak_flat. tred.
      rewrite append_assoc. reflexivity.
    + (* a destination whose backslash ended the line *)
      rewrite Hsk in He. cbn [paren_close] in He.
      rewrite (region_stay ts n TBreak v true kids d e _ Em Hd).
      2: { intros e' E'. rewrite E' in He. symmetry in He.
           apply Precedence.paren_close_ge in He. lia. }
      unfold linked. cbn [pv_setmode pv_mode tok_region tok_dest tok_text]. split; [lia|].
      exists open, depth, (ibreak sh), cm. rewrite Hsk1.
      split; [exact He|]. split; [exact Hne|].
      unfold ibreak at 1, ibreak_at at 1. tred. rewrite append_assoc. reflexivity.
Qed.

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

(* The paragraph's end, in a linked state or one a hard break left. *)
Local Lemma linked_finish : forall ts n v ws prev core,
  vinv ts n v -> linked_end ts n v prev core -> skipn n ts = [] ->
  ifinish (wrap ws core) = map mk (List.rev (pflatten v)).
Proof.
  intros ts n v ws prev core (Ok & Ti & _) [L|P] Hsk; pose proof Ok as (_ & _ & B & _);
    rewrite ifinish_wrap.
  - unfold linked in L.
    destruct (pv_mode v) as [|[|] kids d e txt] eqn:Em.
    + destruct L as (_ & txt & o & -> & Hs). rewrite (sim_finish v txt prev o Hs B).
      unfold pflatten, pfinish. rewrite Em. reflexivity.
    + destruct L as (_ & open & depth & sh & cm & He & Hne & _).
      rewrite Hsk in He. destruct (Hne He).
    + destruct L as (_ & He & Hk & open & cm & ->). rewrite Hsk in He. cbn in He. subst e.
      destruct (tidy_top v Ti) as [Hn Hc].
      exact (ref_finish cm v false kids d open txt Em B Hn Hc Hk).
  - destruct P as [(ws0 & txt & p & o & vb & _ & _ & -> & Emb & Hs & ->)
                  |[(kids & d & e & label & open & cm & Em & Hd & He & Hk & ->)
                   |(kids & d & e & dst & open & depth & sh & cm & Em & Hd & He & Hne & ->)]].
    + rewrite ifinish_pending. destruct Hs as (v0 & cm & -> & Ht & ->).
      set (v := pv_add HardBreak (pv_trim (add_text txt v0))) in *.
      assert (X : iesc_hard ws0 txt (oview cm v0) = oview cm v).
      { unfold v. rewrite (pv_trim_add_text txt v0 Ht). unfold iesc_hard. tred.
        change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s
                  (strip_trailing_ws txt) (oview cm v0))
          with (flush_text (strip_trailing_ws txt) (oview cm v0)).
        rewrite (flush_view cm _ v0 Ht). rewrite imk_here_semantic.
        apply oemit_view. discriminate. }
      rewrite X. rewrite (sim_finish v "" None (oview cm v)).
      * unfold pflatten, pfinish, v. rewrite (proj2 (pv_add_live _ _)), pv_trim_add, Emb. reflexivity.
      * exists v, cm. split; [reflexivity|]. split; [apply top_add_nonstr; discriminate|reflexivity].
      * exact B.
    + rewrite ifinish_ref_esc. rewrite Hsk in He. cbn in He. subst e.
      destruct (tidy_top v Ti) as [Hn Hc].
      exact (ref_finish cm v false kids d open (label ++ one bslash) Em B Hn Hc Hk).
    + rewrite Hsk in He. destruct (Hne He).
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
  over_alphabet (a ++ b) = true -> is_blank b = true -> over_alphabet a = true.
Proof.
  intros a b. remember (String.length a) as m eqn:Em. revert a Em.
  induction m as [m IH] using lt_wf_ind. intros a Em H Hb.
  destruct a as [|c a]; [reflexivity|].
  destruct (is_bslash c) eqn:Eb.
  - unfold is_bslash in Eb. apply Ascii.eqb_eq in Eb. subst c.
    destruct a as [|d a]; [reflexivity|].
    cbn [append] in H. apply over_alphabet_bslash in H.
    cbn [over_alphabet]. change (is_bslash bslash) with true. cbn iota.
    apply (IH (String.length a)); [cbn in Em; lia|reflexivity|exact H|exact Hb].
  - cbn [append] in H. apply (over_alphabet_cons c _ Eb) in H as (Hc & Hf & H).
    cbn [over_alphabet]. rewrite Eb, Hc.
    rewrite (IH (String.length a) ltac:(cbn in Em; lia) a eq_refl H Hb), andb_true_r. cbn [andb].
    destruct a as [|d a]; [|exact Hf].
    cbn [append] in Hf. unfold follow_ok in *. rewrite (blank_not_row b Hb) in Hf.
    apply andb_true_iff in Hf as [Hf _]. apply andb_true_iff in Hf as [Hf _].
    cbn. rewrite Hf, !andb_false_r. reflexivity.
Qed.

Local Lemma over_alphabet_strip : forall x,
  over_alphabet x = true -> over_alphabet (strip_trailing_ws x) = true.
Proof.
  intros x Ha. destruct (strip_trailing_split x) as (w & Hw & E).
  rewrite E in Ha. exact (over_alphabet_app_l _ w Ha Hw).
Qed.

(* A break clears a destination reading's pending backslash. *)
Local Lemma layers_break : forall ts m rest ws,
  skipn m ts = TBreak :: rest -> Forall (never ts m) ws ->
  Forall (never ts (S m)) (map (wl_after nl) ws) /\ Forall esc_off (map (wl_after nl) ws).
Proof.
  intros ts m rest ws Hs F. pose proof (skipn_cons_tail ts m _ _ Hs) as Hs1.
  assert (D : forall w, exists dst, dfeed nl (wl_ds w) = Some (DS false (wl_depth w) dst)).
  { intros [k o [[|] d dst] o']; unfold wl_depth; cbn [wl_ds ds_depth]; eexists; reflexivity. }
  rewrite !Forall_map. split.
  - eapply Forall_impl; [|exact F]. intros w Hw. unfold never in *.
    destruct (D w) as (dst & E). unfold wl_after, wl_depth in *. cbn [wl_ds]. rewrite E.
    cbn [ds_depth]. rewrite Hs in Hw. rewrite Hs1. exact Hw.
  - apply Forall_forall. intros w _. destruct (D w) as (dst & E).
    unfold esc_off, wl_after. cbn [wl_ds]. rewrite E. reflexivity.
Qed.

Local Lemma scan_lines_sim : forall ts ls n v ws core,
  Forall (fun x => over_alphabet x = true) ls ->
  skipn n ts = para_tokens ls ->
  vinv ts n v -> Forall (never ts n) ws -> Forall esc_off ws -> linked ts n v None core ->
  ifinish (iscan_lines ls (wrap ws core))
  = map mk (List.rev (pflatten (prun ts n (para_tokens ls) v))).
Proof.
  intros ts. induction ls as [|x rest IH]; intros n v ws core Ha Hsk V Fn Fe L.
  - cbn [iscan_lines para_tokens prun]. exact (linked_finish ts n v ws None core V (or_introl L) Hsk).
  - apply Forall_cons_iff in Ha as [Hx Ha].
    destruct rest as [|y rest'].
    + cbn [iscan_lines para_tokens] in *. unfold tokens in *.
      rewrite <- (app_nil_r (lex None 0 (strip_trailing_ws x))) in Hsk.
      destruct (scan_sim ts [] _ (strip_trailing_ws x) None n v ws core (le_n _)
                  (over_alphabet_strip x Hx) (or_introl eq_refl) Hsk V Fn Fe L)
        as (ws' & core' & prev' & E & V' & Fn' & L').
      rewrite <- ifinish_rres, E.
      exact (linked_finish ts _ _ ws' prev' core' V' L' (skipn_app_tail ts _ [] n Hsk)).
    + change (iscan_lines (x :: y :: rest') (wrap ws core))
        with (iscan_lines (y :: rest') (ibreak (iscan_str x (wrap ws core)))).
      change (para_tokens (x :: y :: rest'))
        with (lex None 0 x ++ TBreak :: para_tokens (y :: rest'))%list in *.
      destruct (scan_sim ts _ _ x None n v ws core (le_n _) Hx (or_introl eq_refl) Hsk V Fn Fe L)
        as (ws' & core' & prev' & E & V' & Fn' & L').
      pose proof (skipn_app_tail ts _ _ n Hsk) as Hsk'.
      unfold ibreak at 1. rewrite <- ibreak_rres, E. fold (ibreak (wrap ws' core')).
      rewrite ibreak_wrap, prun_app. cbn [prun].
      destruct (layers_break ts _ _ ws' Hsk' Fn') as [Fn2 Fe2].
      assert (Hn : nth_error ts (n + length (lex None 0 x)) = Some TBreak)
        by (rewrite <- (Nat.add_0_r (n + _)), <- nth_error_skipn, Hsk'; reflexivity).
      rewrite <- Nat.add_succ_r in Fn2 |- *.
      apply IH; [exact Ha|rewrite Nat.add_succ_r; exact (skipn_cons_tail ts _ _ _ Hsk')
                |rewrite Nat.add_succ_r; apply vinv_step; [exact V'|exact Logic.I|exact Hn]
                |rewrite Nat.add_succ_r in *; exact Fn2|exact Fe2
                |rewrite Nat.add_succ_r; exact (break_linked ts _ _ _ _ _ Hsk' L')].
Qed.

(*
The theorem
===========

On a paragraph over the alphabet, the scanner builds the tree of the
unique reading the precedence rules allow. *)

Local Lemma vinv_start : forall ts, vinv ts 0 pv0.
Proof.
  intros ts.
  split; [split; [constructor|]; split; [intros x []|]; split; [constructor|exact Logic.I]|].
  split; [|intros H; discriminate H].
  split; [exact Logic.I|]. split; [constructor|]. split; constructor.
Qed.

Local Lemma linked_start : forall ts, linked ts 0 pv0 None istart.
Proof.
  intros ts. split; [reflexivity|]. exists "", ostart. split; [reflexivity|].
  exists pv0, (fun _ => false). split; [reflexivity|]. split; reflexivity.
Qed.

Theorem parse_inline_line_matching : forall s,
  over_alphabet s = true ->
  parse_inline_line s = tree_of (tokens s) (fst (ref_read (tokens s))).
Proof.
  intros s Ha. unfold parse_inline_line. rewrite tree_of_prun.
  assert (Hsk : skipn 0 (tokens s) = (lex None 0 s ++ [])%list) by (rewrite app_nil_r; reflexivity).
  destruct (scan_sim (tokens s) [] _ s None 0 pv0 [] istart (le_n _) Ha (or_introl eq_refl) Hsk
              (vinv_start _) (Forall_nil _) (Forall_nil _) (linked_start _))
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
  exact (scan_lines_sim (para_tokens ls) ls 0 pv0 [] istart Ha eq_refl (vinv_start _)
           (Forall_nil _) (Forall_nil _) (linked_start _)).
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
