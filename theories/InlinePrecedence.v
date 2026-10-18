(* ai-disclosure: autonomous *)

(* The inline scanner builds the tree the precedence rules describe
   (`Precedence.v`): on a paragraph of delimiters, bare or marked with
   braces, brackets with their destinations and labels, and plain bytes,
   `para_inlines` is `tree_of` of the unique valid reading. *)

From Stdlib Require Import String Ascii List Bool Lia Arith Sorted.
From DjotV Require Import Strings Ast Attributes InlineTable InlineView InlineScan
  InlineInvert Precedence PrecedenceFacts.
Import ListNotations.

Local Open Scope string_scope.

Section WithTable.
Context {T : dtable}.

(*
The prefix view
===============

What the scanner holds after a prefix of the paragraph: the openers
still open, innermost first, each with what has been read since it,
above what was read before the outermost one; and, after a bracket's
closer, the region being read.  The view reads the units the scanner does: a token of the
chain, or a byte of a region.
An opener dies with the pair that closes over it, and at the end every
frame still open is text.

`tree_of` instead knows the whole matching and opens a frame only for
an opener that will be closed.  The two agree because a frame of the
view whose opener is never closed reads, once it is text, as its
opener's spelling followed by its content (`collapse`).

A content's nodes are kept as `inline` values: all but a span and the
nodes a closed pair gives back are built with `mk`, and merging text is
then associative on the nose. *)

(* A node with no attributes, a node with some, or a spec waiting. *)
Inductive vitem : Type :=
  | VIn (x : inline)
  | VAt (kv : string * string) (a : attr) (x : inline)
  | VMark (a : attr).

Coercion VIn : inline >-> vitem.

Definition vof (n : node inline) : vitem :=
  match n with
  | Node _ [] x => VIn x
  | Node _ (kv :: a) x => VAt kv a x
  end.

Definition et (x : vitem) : titem :=
  match x with
  | VIn x => TIn (mk x)
  | VAt kv a x => TIn (Node NoPos (kv :: a) x)
  | VMark a => TMark a
  end.

(* A content once its pair closes, latest first and in order. *)
Definition vsettle (c : list vitem) : inlines := resolve_rev (map et c).
Definition vres (c : list vitem) : inlines := resolve (map et c).

(* Push onto a reversed list, merging two `Str`s at the seam. *)
Definition xsnoc (x : vitem) (out : list vitem) : list vitem :=
  match out, x with
  | VIn (Str t) :: rest, VIn (Str s) => VIn (Str (t ++ s)) :: rest
  | _, _ => x :: out
  end.

(* `cur`, reversed, in front of `out`, reversed. *)
Fixpoint xapp (cur out : list vitem) : list vitem :=
  match cur with
  | [] => out
  | [x] => xsnoc x out
  | x :: rest => x :: xapp rest out
  end.

(* A frame's key, and a bit the opener's text needs: whether a bracket
   is an image's, or whether a `}` comes right after a delimiter marked
   with `{`, which chooses the side a quote decays to. *)
Definition fkey : Type := (key * bool)%type.

(* A token that is not an opener, as a node: a quote's is smart
   punctuation (`decay_node`), any other its text. *)
Definition kdecay (k : fkey) (txt : string) : inline :=
  match fst k with
  | KDelim k' _ => decay_node k' txt
  | KBracket => Str txt
  end.

(* An opener's node, which it reads as once it is not an opener. *)
Definition lit (k : fkey) : inline :=
  kdecay k (match fst k with
            | KDelim k' mr => ddecay_str k' mr (snd k)
            | KBracket => bracket_open (snd k)
            end).

(* An opener's frame: where it is, its key, and its content. *)
Inductive pframe : Type := PF (p : nat) (k : fkey) (c : list vitem).

Definition fcontent (f : pframe) : list vitem := match f with PF _ _ c => c end.

Definition flit (f : pframe) : inline := match f with PF _ k _ => lit k end.

Definition fitem (f : pframe) : litem := match f with PF p k _ => (p, fst k) end.

Definition fset (f : pframe) (c : list vitem) : pframe :=
  match f with PF p k _ => PF p k c end.

(* As the chain's jump past a region, with what a region has gathered:
   whether its bracket is an image's, its link text and its bytes so far,
   its `(` or `[` aside; or inside a
   token of several bytes whose item `x` is added at its last byte `e`;
   or inside a span's spec, whose node is added at its `}` at `e`. *)
Inductive pmode : Type :=
  | PMNormal
  | PMRegion (dest image : bool) (kids : inlines) (d e : nat) (txt : string)
  | PMAtom (x : vitem) (e : nat)
  | PMSpan (image : bool) (kids : inlines) (a : attr) (e : nat).

Record pview : Type := PView {
  pv_stk : list pframe;
  pv_out : list vitem;
  pv_mode : pmode
}.

Definition pv0 : pview := PView [] [] PMNormal.

(* The stack, as `rstep` keeps it. *)
Definition pv_live (v : pview) : list litem := map fitem (pv_stk v).

Definition pv_add (x : vitem) (v : pview) : pview :=
  match pv_stk v with
  | [] => PView [] (xsnoc x (pv_out v)) (pv_mode v)
  | f :: rest => PView (fset f (xsnoc x (fcontent f)) :: rest) (pv_out v) (pv_mode v)
  end.

(* Several nodes, in order, as `temit_items` puts them. *)
Definition pv_add_items (xs : list inline) (v : pview) : pview :=
  fold_left (fun v x => pv_add (VIn x) v) xs v.

Definition pv_setmode (md : pmode) (v : pview) : pview :=
  PView (pv_stk v) (pv_out v) md.

(* Close the innermost frame of key `k`, turning the frames above it
   into text in its content. *)
Fixpoint pclose_go (k : key) (pend : list vitem) (stk : list pframe)
  : option (list vitem * list pframe) :=
  match stk with
  | [] => None
  | PF p k' c :: rest =>
      let content := xapp pend c in
      if key_eq k (fst k') then Some (content, rest)
      else pclose_go k (xapp content [VIn (lit k')]) rest
  end.

(* Whether the bracket frame `pclose_go KBracket` closes is an image's. *)
Fixpoint pclose_im (stk : list pframe) : bool :=
  match stk with
  | PF _ (KBracket, im) _ :: _ => im
  | PF _ _ _ :: rest => pclose_im rest
  | _ => false
  end.

(* What a hard break trims: the text it ends, as `item_trim`. *)
Definition xtrim (l : list vitem) : list vitem :=
  match l with
  | VIn (Str t) :: rest =>
      match strip_trailing_ws t with
      | EmptyString => rest
      | t' => VIn (Str t') :: rest
      end
  | _ => l
  end.

Definition pv_trim (v : pview) : pview :=
  match pv_stk v with
  | [] => PView [] (xtrim (pv_out v)) (pv_mode v)
  | f :: rest => PView (fset f (xtrim (fcontent f)) :: rest) (pv_out v) (pv_mode v)
  end.

Local Lemma kdecay_ne : forall k txt, txt <> "" -> VIn (kdecay k txt) <> VIn (Str "").
Proof.
  intros [[k mr|] im] txt H E; cbn [kdecay fst] in E;
    [unfold decay_node in E; destruct (dc_decay cfg k)|];
    injection E as E; try discriminate E; contradiction.
Qed.

(* A token that does not close opens if it may, or is its own text. *)
Definition popen (i : nat) (k : fkey) (op : bool) (txt : string) (v : pview)
  : pview :=
  if op then PView (PF i k [] :: pv_stk v) (pv_out v) (pv_mode v)
  else pv_add (kdecay k txt) v.

Definition add_text (txt : string) (v : pview) : pview :=
  if nonempty_str txt then pv_add (Str txt) v else v.

(* A closed pair's nodes back in a content, latest first. *)
Definition vback (ns : inlines) : list vitem := List.rev (map vof ns).

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
  | TAuto src => pv_add (auto_node src) v
  | TSymbol a => pv_add (Symbol a) v
  | TAttr _ a => pv_setmode (PMAtom (VMark a) (pred (tok_end s i))) v
  | TNote l => pv_setmode (PMAtom (FootnoteReference (normalize_label l)) (pred (tok_end s i))) v
  | TDots n => pv_add_items (dots_items n) v
  | TDash n => pv_add_items (dash_items n) v
  | TSpan b a =>
      match pick KBracket (pv_live v), pclose_go KBracket [] (pv_stk v) with
      | PFound _ _, Some (content, rest) =>
          PView rest (pv_out v)
            (PMSpan (pclose_im (pv_stk v)) (vres content) a (i + S (S (String.length b))))
      | _, _ => pv_add (Str (tok_text t)) v
      end
  | TClose b r =>
      match pick KBracket (pv_live v), pclose_go KBracket [] (pv_stk v) with
      | PFound _ _, Some (content, rest) =>
          PView rest (pv_out v)
            (PMRegion b (pclose_im (pv_stk v)) (vres content) i
               (i + S (S (String.length r))) "")
      | _, _ => pv_add (Str (tok_text t)) v
      end
  | TOpen im => popen i (KBracket, im) true (tok_text t) v
  | TDelim k mr op cl =>
      let cm := at_rbrace (get (tok_end s i) s) in
      let txt := delim_lit k mr op cm in
      match (if cl then pick (KDelim k mr) (pv_live v) else PNone) with
      | PFound p _ =>
          if Nat.ltb (tok_end s p) i
          then match pclose_go (KDelim k mr) [] (pv_stk v) with
               | Some (content, rest) =>
                   pv_add (dnode k (vres content))
                     (PView rest (pv_out v) PMNormal)
               | None => v
               end
          else popen i (KDelim k mr, (mr && cm)%bool) op txt v
      | PNone => popen i (KDelim k mr, (mr && cm)%bool) op txt v
      end
  end.

(* A byte of a region: the `(` or `[` that opens it is skipped, and the
   byte that ends it makes the link.  A byte of a token: the last one
   adds its node. *)
Definition pbyte (i : nat) (c : ascii) (v : pview) : pview :=
  match pv_mode v with
  | PMAtom x e => if Nat.eqb i e then pv_add x (pv_setmode PMNormal v) else v
  | PMSpan im kids a e =>
      if Nat.eqb i e
      then pv_add (vof (Node NoPos a (Span EmptyString kids)))
             (let v' := pv_setmode PMNormal v in
              if im then pv_add (Str (one bang)) v' else v')
      else v
  | PMRegion b im kids d e txt =>
      if Nat.eqb i e
      then pv_add (region_node b im kids (if b then dest_text false txt else txt))
             (pv_setmode PMNormal v)
      else pv_setmode (PMRegion b im kids d e
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
  | PMRegion _ _ _ _ _ _ | PMAtom _ _ | PMSpan _ _ _ _ =>
      match get i s with
      | Some c => Some (S i, false, pbyte i c v)
      | None => None
      end
  end.

Inductive pruns (s : string) : nat -> bool -> pview -> nat -> bool -> pview -> Prop :=
  | pruns_refl : forall i h v, pruns s i h v i h v
  | pruns_step : forall i h v j h1 v1 k h2 v2,
      punit s i h v = Some (j, h1, v1) -> pruns s j h1 v1 k h2 v2 -> pruns s i h v k h2 v2.

(* Every open frame read as text, as at the end of the paragraph. *)
Fixpoint pflatten_go (pend : list vitem) (stk : list pframe)
  (bottom : list vitem) : list vitem :=
  match stk with
  | [] => xapp pend bottom
  | f :: rest => pflatten_go (xapp (xapp pend (fcontent f)) [VIn (flit f)]) rest bottom
  end.

Definition pflatten (v : pview) : list vitem := pflatten_go [] (pv_stk v) (pv_out v).

(* The frames of `tgo` that a view stands for, given which openers the
   whole paragraph closes: a frame whose opener is closed stays a frame,
   and any other is its opener's text and its content, in the frame
   below it. *)
Definition xinner (g : list vitem -> list vitem)
  (st : list (tkind * list vitem) * list vitem)
  : list (tkind * list vitem) * list vitem :=
  match st with
  | ([], top) => ([], g top)
  | ((k, c) :: fs, top) => ((k, g c) :: fs, top)
  end.

Definition tkind_of (k : fkey) : tkind :=
  match fst k with KDelim k' _ => TKDelim k' | KBracket => TKBracket (snd k) end.

Fixpoint collapse (real : nat -> bool) (stk : list pframe) (out : list vitem)
  : list (tkind * list vitem) * list vitem :=
  match stk with
  | [] => ([], out)
  | PF p k c :: rest =>
      if real p then ((tkind_of k, c) :: fst (collapse real rest out),
                      snd (collapse real rest out))
      else xinner (fun acc => xapp c (xsnoc (lit k) acc)) (collapse real rest out)
  end.

Definition tfr (st : list (tkind * list vitem) * list vitem) : tframes * list titem :=
  (map (fun f => (fst f, map et (snd f))) (fst st), map et (snd st)).

Definition vembed (real : nat -> bool) (v : pview) : tframes * list titem :=
  tfr (collapse real (pv_stk v) (pv_out v)).

(* An item on the innermost content, as `temit` and `tmark` put one. *)
Definition tput (it : titem) (fs : tframes) (top : list titem) : tframes * list titem :=
  match fs with
  | [] => ([], it :: top)
  | (k, acc) :: rest => ((k, it :: acc) :: rest, top)
  end.

(*
Merging text
------------
*)

(* The cases of an element, the `Str` first. *)
Ltac dv x := destruct x as [x|? ? ?|?]; [destruct x|..].

Local Lemma xsnoc_nonstr : forall (x : vitem) l,
  (forall s, x <> VIn (Str s)) -> xsnoc x l = x :: l.
Proof.
  intros x l H. dv x; [destruct (H s eq_refl)|..];
    (destruct l as [|[[]| |] l]; reflexivity).
Qed.

Local Lemma vin_nonstr : forall x : inline,
  (forall s, x <> Str s) -> forall s, VIn x <> VIn (Str s).
Proof. intros x H s E. injection E as E. exact (H s E). Qed.

Local Lemma str_view : forall x : vitem,
  {s | x = VIn (Str s)} + {forall s, x <> VIn (Str s)}.
Proof.
  intros x. dv x; [left; eexists; reflexivity|..];
    right; intros s' E; discriminate E.
Defined.

Local Lemma xsnoc_str_nonstr : forall t (w : vitem) b,
  (forall u, w <> VIn (Str u)) -> xsnoc (Str t) (w :: b) = VIn (Str t) :: w :: b.
Proof. intros t w b H. dv w; [destruct (H s eq_refl)|..]; reflexivity. Qed.

Local Lemma xapp_xsnoc : forall (x : vitem) a b, xapp (xsnoc x a) b = xsnoc x (xapp a b).
Proof.
  intros x a b. destruct (str_view x) as [[s ->]|Hx].
  - destruct a as [|y r]; [reflexivity|].
    destruct (str_view y) as [[t ->]|Hy].
    + destruct r as [|z r]; cbn [xsnoc xapp]; [|reflexivity].
      destruct b as [|w b]; [reflexivity|].
      destruct (str_view w) as [[u ->]|Hw].
      * cbn. rewrite append_assoc. reflexivity.
      * rewrite (xsnoc_str_nonstr t w b Hw). cbn.
        dv w; [destruct (Hw _ eq_refl)|..]; reflexivity.
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
  dv y; try discriminate. dv x; discriminate.
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

Local Lemma item_snoc_et : forall s l,
  item_snoc s (map et l) = map et (xsnoc (Str s) l).
Proof.
  intros s l. destruct l as [|y l]; [reflexivity|].
  destruct (str_view y) as [[t ->]|Hy]; [reflexivity|].
  rewrite (xsnoc_str_nonstr s y l Hy).
  dv y; [destruct (Hy _ eq_refl)|..]; reflexivity.
Qed.

(*
Normal contents
---------------

A content never has two `Str`s side by side.
*)

Definition is_str (x : vitem) : bool :=
  match x with VIn (Str _) => true | _ => false end.

Fixpoint normal (l : list vitem) : Prop :=
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
  intros x [|y l] H; [dv x; exact Logic.I|].
  destruct (str_view x) as [[s ->]|Hx].
  - destruct (str_view y) as [[t ->]|Hy].
    + cbn. destruct l as [|z l]; [exact Logic.I|]. split; [|exact (proj2 H)].
      destruct H as [[H|H] _]; [discriminate|right; exact H].
    + rewrite (xsnoc_str_nonstr s y l Hy). split; [|exact H].
      right. dv y; [destruct (Hy _ eq_refl)|..]; reflexivity.
  - rewrite (xsnoc_nonstr x _ Hx). split; [|exact H].
    left. dv x; [destruct (Hx _ eq_refl)|..]; reflexivity.
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


(* A node the view can hold as it is: it has no position. *)
Definition bare (n : node inline) : Prop :=
  match n with Node p _ _ => p = NoPos end.

Local Lemma et_vof : forall n, bare n -> et (vof n) = TIn n.
Proof. intros [p [|kv a] x] H; cbn in H; subst p; reflexivity. Qed.

Local Lemma vof_nonstr : forall n,
  (forall p s, n <> Node p [] (Str s)) -> forall s, vof n <> VIn (Str s).
Proof.
  intros [p [|kv a] x] H s E; cbn in E; [|discriminate].
  injection E as ->. exact (H p s eq_refl).
Qed.

(*
Resolving a content
-------------------

What a closed pair gives back has no position and no two `Str`s side by
side, so it can go back into a content as it is.
*)

Local Lemma normal_cons : forall (x : vitem) l,
  is_str x = false -> normal l -> normal (x :: l).
Proof. intros x [|y l] Hx N; [exact Logic.I|]. split; [left; exact Hx|exact N]. Qed.

Local Lemma vof_str_snoc : forall s out,
  map vof (str_snoc s out) = xsnoc (Str s) (map vof out).
Proof.
  intros s [|[p [|kv a] x] out]; [reflexivity| |reflexivity].
  destruct x; reflexivity.
Qed.

Definition bare_item (it : titem) : Prop :=
  match it with TIn n => bare n | TMark _ => True end.

(* What is before a word keeps the invariants of the nodes it came from,
   and the word's pieces have no position. *)
Local Lemma word_split_ok : forall out,
  Forall bare out -> normal (map vof out) ->
  Forall bare (fst (word_split out)) /\ Forall bare (snd (word_split out))
  /\ normal (map vof (snd (word_split out))).
Proof.
  induction out as [|[p a v] rest IH]; intros B N; [repeat split; constructor|].
  pose proof (proj1 (Forall_cons_iff _ _ _) B) as [Bp Br]. cbn in Bp. subst p.
  pose proof (normal_tail _ _ N) as Nr. specialize (IH Br Nr).
  destruct a as [|kv a]; [|repeat split; [constructor|exact B|exact N]].
  destruct v; try (repeat split; [constructor|exact B|exact N]); cbn [word_split].
  - destruct (last_ws_split s) as [pre w].
    destruct (nonempty_str w); [|repeat split; [constructor|exact B|exact N]].
    destruct (nonempty_str pre).
    + cbn [fst snd]. repeat split;
        [constructor; [reflexivity|constructor]|constructor; [reflexivity|exact Br]|].
      destruct rest as [|r0 rest]; [exact Logic.I|]. exact N.
    + destruct (word_split rest) as [ws before]; cbn [fst snd] in IH |- *.
      destruct IH as (Iw & Ib & In). repeat split; [constructor; [reflexivity|exact Iw]|..];
        assumption.
  - destruct (word_split rest) as [ws before]; cbn [fst snd] in IH |- *.
    destruct IH as (Iw & Ib & In). repeat split; [constructor; [reflexivity|exact Iw]|..];
      assumption.
Qed.

Local Lemma word_node_bare : forall a ws, Forall bare ws -> bare (word_node a ws).
Proof.
  intros a [|[q b x] [|y ws]] H; try reflexivity.
  inversion H; assumption.
Qed.

Local Lemma attach_ok : forall a out,
  Forall bare out -> normal (map vof out) ->
  Forall bare (attach a out) /\ normal (map vof (attach a out)).
Proof.
  intros a out B N. unfold attach.
  destruct (word_split_ok out B N) as (Bw & Bb & Nb).
  destruct (word_split out) as [[|y ws] before]; cbn [fst snd] in Bw, Bb, Nb.
  - destruct out as [|[p a' v] rest]; [split; assumption|].
    pose proof (proj1 (Forall_cons_iff _ _ _) B) as [Bp Br]. cbn in Bp. subst p.
    pose proof (normal_tail _ _ N) as Nr.
    assert (Other : forall b y, (b <> [] \/ forall s, y <> Str s) ->
              Forall bare (Node NoPos b y :: rest)
              /\ normal (map vof (Node NoPos b y :: rest))).
    { intros b z H. split; [constructor; [reflexivity|exact Br]|].
      cbn [map]. apply normal_cons; [|exact Nr].
      destruct b as [|kv b]; [|reflexivity]. destruct H as [H|H]; [contradiction|].
      destruct z; try reflexivity. destruct (H _ eq_refl). }
    destruct a' as [|kv a'].
    + destruct v; try (apply Other; right; intros s0 E; discriminate E);
        split; assumption.
    + destruct (Attr.merge_cons a kv a') as (x & r & E).
      destruct v; try (rewrite E; apply Other; left; discriminate); split; assumption.
  - destruct a as [|kv a]; [split; assumption|]. split.
    + constructor; [apply word_node_bare, Bw|exact Bb].
    + cbn [map]. apply normal_cons; [|exact Nb].
      destruct ws as [|z w']; destruct y; reflexivity.
Qed.

Local Lemma resolve_rev_ok : forall l, Forall bare_item l ->
  Forall bare (resolve_rev l) /\ normal (map vof (resolve_rev l)).
Proof.
  induction l as [|[n|a] l IH]; intros B; [split; [constructor|exact Logic.I]| |];
    apply Forall_cons_iff in B as [Bn B]; destruct (IH B) as [Bo No]; cbn [resolve_rev].
  - assert (Other : (forall p s, n <> Node p [] (Str s)) ->
              Forall bare (n :: resolve_rev l) /\ normal (map vof (n :: resolve_rev l))).
    { intros Hn. split; [constructor; assumption|]. cbn [map].
      apply normal_cons; [|exact No].
      pose proof (vof_nonstr n Hn) as H. destruct (vof n) as [[]| |]; try reflexivity.
      destruct (H _ eq_refl). }
    destruct n as [p [|kv a] x]; [|apply Other; intros p' s' E; discriminate E].
    destruct x; try (apply Other; intros p' s' E; discriminate E).
    cbn [push]. rewrite vof_str_snoc. split; [|apply normal_xsnoc, No].
    unfold str_snoc. destruct (resolve_rev l) as [|[q [|kv b] y] r];
      try (constructor; [reflexivity|exact Bo]).
    destruct y; try (constructor; [reflexivity|exact Bo]).
    apply Forall_cons_iff in Bo as [Bq Br]. constructor; assumption.
  - apply attach_ok; assumption.
Qed.

Local Lemma et_bare : forall c, Forall bare_item (map et c).
Proof.
  intros c. apply Forall_forall. intros it Hi. apply in_map_iff in Hi as (x & <- & _).
  destruct x as [x|kv a x|a]; exact eq_refl || exact Logic.I.
Qed.

Local Lemma vback_vres : forall c, vback (vres c) = map vof (vsettle c).
Proof.
  intros c. unfold vback, vres, vsettle, resolve. rewrite map_rev, rev_involutive.
  reflexivity.
Qed.

Local Lemma vres_ok : forall c, Forall bare (vres c) /\ normal (vback (vres c)).
Proof.
  intros c. destruct (resolve_rev_ok (map et c) (et_bare c)) as [B N]. split.
  - apply Forall_rev, B.
  - rewrite vback_vres. exact N.
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
  destruct stk as [|[p k c] rest]; [reflexivity|];
    cbn [pv_stk pv_out pv_mode fset fcontent collapse].
  destruct (real p); [reflexivity|].
  destruct (collapse real rest out) as [[|[k' c'] fs] top]; cbn [xinner];
    rewrite xapp_xsnoc; reflexivity.
Qed.

Local Lemma collapse_add_items : forall real xs v,
  collapse real (pv_stk (pv_add_items xs v)) (pv_out (pv_add_items xs v))
  = fold_left (fun st x => xinner (xsnoc (VIn x)) st) xs
      (collapse real (pv_stk v) (pv_out v)).
Proof.
  intros real. induction xs as [|x xs IH]; intros v; [reflexivity|].
  cbn [pv_add_items fold_left]. fold (pv_add_items xs (pv_add (VIn x) v)).
  rewrite IH, collapse_add. reflexivity.
Qed.

(* The frames a closer passes over are openers of other keys. *)
Definition passes (k : key) (f : pframe) : Prop :=
  match f with PF _ k' _ => key_eq k (fst k') = false end.

Local Lemma pick_split : forall k stk p below,
  pick k (map fitem stk) = PFound p below ->
  exists above im c rest,
    stk = (above ++ PF p (k, im) c :: rest)%list
    /\ Forall (passes k) above
    /\ map fitem rest = below.
Proof.
  intros k stk. induction stk as [|[q [k' im'] c] stk IH]; intros p below H;
    [discriminate|].
  cbn [map fitem pick fst] in H. destruct (key_eq k k') eqn:E.
  - injection H as <- <-. apply key_eq_iff in E. subst k'.
    exists [], im', c, stk. split; [reflexivity|]. split; [constructor|reflexivity].
  - destruct (IH p below H) as (above & im & c' & rest & -> & F & Hb).
    exists (PF q (k', im') c :: above)%list, im, c', rest. split; [reflexivity|].
    split; [constructor; [exact E|exact F]|exact Hb].
Qed.

Local Lemma pclose_split : forall k im above p c rest pend,
  Forall (passes k) above ->
  exists content,
    pclose_go k pend (above ++ PF p (k, im) c :: rest) = Some (content, rest).
Proof.
  intros k im above. induction above as [|f above IH]; intros p c rest pend F;
    cbn [app pclose_go fst].
  - rewrite key_eq_refl. eexists. reflexivity.
  - apply Forall_cons_iff in F as [E F].
    destruct f as [q k1 c1]. cbn [passes] in E. rewrite E.
    apply IH, F.
Qed.

Local Lemma pclose_im_split : forall above im p c rest,
  Forall (passes KBracket) above ->
  pclose_im (above ++ PF p (KBracket, im) c :: rest) = im.
Proof.
  induction above as [|[q [[k mr|] im'] c'] above IH]; intros im p c rest F;
    cbn [app pclose_im]; [reflexivity|..]; apply Forall_cons_iff in F as [E F];
    [apply IH, F|discriminate E].
Qed.

Local Lemma close_collapse : forall real k im above p c rest out pend,
  Forall (fun f => passes k f /\ match f with PF q _ _ => real q = false end) above ->
  real p = true ->
  exists content,
    pclose_go k pend (above ++ PF p (k, im) c :: rest) = Some (xapp pend content, rest)
    /\ collapse real (above ++ PF p (k, im) c :: rest) out
       = ((tkind_of (k, im), content) :: fst (collapse real rest out),
          snd (collapse real rest out)).
Proof.
  intros real k im above.
  induction above as [|f above IH]; intros p c rest out pend F Hp; cbn [app pclose_go collapse fst].
  - rewrite key_eq_refl, Hp. exists c. split; reflexivity.
  - apply Forall_cons_iff in F as [[E Hq] F].
    destruct f as [q k1 c1]. cbn [passes] in E.
    rewrite E, Hq.
    destruct (IH p c rest out (xapp (xapp pend c1) [VIn (lit k1)]) F Hp)
      as (content & Hc & Hl).
    exists (xapp c1 (xsnoc (lit k1) content)). rewrite Hc, Hl.
    split; [|reflexivity]. rewrite !xapp_assoc. reflexivity.
Qed.

Local Lemma flatten_collapse : forall real stk out pend,
  Forall (fun f => match f with PF q _ _ => real q = false end) stk ->
  collapse real stk out = ([], snd (collapse real stk out))
  /\ pflatten_go pend stk out = xapp pend (snd (collapse real stk out)).
Proof.
  intros real stk out.
  induction stk as [|f stk IH]; intros pend F;
    cbn [collapse pflatten_go]; [split; reflexivity|].
  apply Forall_cons_iff in F as [Hq F].
  destruct f as [q k c]; cbn [fcontent flit] in *. rewrite Hq.
  destruct (IH (xapp (xapp pend c) [VIn (lit k)]) F) as [E1 E2].
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
  intros s [[|[k c] fs] top]; cbn; rewrite item_snoc_et; reflexivity.
Qed.

Local Lemma temit_embed : forall (x : inline) st,
  temit (mk x) (fst (tfr st)) (snd (tfr st)) = tfr (xinner (cons (VIn x)) st).
Proof. intros x [[|[k c] fs] top]; reflexivity. Qed.

Local Lemma tput_embed : forall x st,
  tput (et x) (fst (tfr st)) (snd (tfr st)) = tfr (xinner (cons x) st).
Proof. intros x [[|[k c] fs] top]; reflexivity. Qed.

Local Lemma xinner_ext : forall g h st,
  (forall l, g l = h l) -> xinner g st = xinner h st.
Proof. intros g h [[|[k c] fs] top] H; cbn; rewrite H; reflexivity. Qed.

Local Lemma xinner_comp : forall g h st, xinner g (xinner h st) = xinner (fun l => g (h l)) st.
Proof. intros g h [[|[k c] fs] top]; reflexivity. Qed.

Local Lemma temit_item_embed : forall (x : inline) st,
  temit_item x (fst (tfr st)) (snd (tfr st)) = tfr (xinner (xsnoc x) st).
Proof.
  intros x st. destruct x; try apply temit_str_embed;
    rewrite (xinner_ext (xsnoc _) (cons _)) by (intros l; apply xsnoc_nonstr; discriminate);
    apply temit_embed.
Qed.

Local Lemma temit_items_embed : forall xs st,
  temit_items xs (fst (tfr st)) (snd (tfr st))
  = tfr (fold_left (fun st x => xinner (xsnoc (VIn x)) st) xs st).
Proof.
  induction xs as [|x xs IH]; intros st; [destruct st; reflexivity|].
  cbn [temit_items fold_left]. rewrite temit_item_embed.
  destruct (tfr (xinner (xsnoc x) st)) as [fs' top'] eqn:E. rewrite <- IH, E. reflexivity.
Qed.

Local Lemma temit_vof : forall n st, bare n ->
  temit n (fst (tfr st)) (snd (tfr st)) = tfr (xinner (cons (vof n)) st).
Proof.
  intros n [[|[k c] fs] top] Bn; unfold tfr, xinner; cbn [temit fst snd map];
    rewrite (et_vof n Bn); reflexivity.
Qed.

(*
The view and the computed reading
---------------------------------
*)

Local Lemma pv_add_live : forall x v,
  pv_live (pv_add x v) = pv_live v /\ pv_mode (pv_add x v) = pv_mode v.
Proof. intros x [[|[p k c] rest] out md]; split; reflexivity. Qed.

Local Lemma pv_add_items_live : forall xs v,
  pv_live (pv_add_items xs v) = pv_live v /\ pv_mode (pv_add_items xs v) = pv_mode v.
Proof.
  induction xs as [|x xs IH]; intros v; [split; reflexivity|]. cbn [pv_add_items fold_left].
  destruct (IH (pv_add (VIn x) v)) as [A B]. fold (pv_add_items xs (pv_add (VIn x) v)).
  rewrite A, B. apply pv_add_live.
Qed.

Local Lemma add_text_live : forall t v,
  pv_live (add_text t v) = pv_live v /\ pv_mode (add_text t v) = pv_mode v.
Proof. intros t v. unfold add_text. destruct (nonempty_str t); [apply pv_add_live|split; reflexivity]. Qed.

Local Lemma verb_node_nonstr : forall d r b s, verb_node d r b <> Str s.
Proof. intros [|[|d]] [f|] b s; discriminate. Qed.

Local Lemma auto_node_nonstr : forall src s, auto_node src <> Str s.
Proof. intros src s. unfold auto_node. destruct (auto_email src); discriminate. Qed.

Local Lemma pv_trim_live : forall v,
  pv_live (pv_trim v) = pv_live v /\ pv_mode (pv_trim v) = pv_mode v.
Proof. intros [[|[p k c] rest] out md]; split; reflexivity. Qed.

Local Lemma pclose_found : forall k stk p below,
  pick k (map fitem stk) = PFound p below ->
  exists content rest, pclose_go k [] stk = Some (content, rest) /\ map fitem rest = below.
Proof.
  intros k stk p below P.
  destruct (pick_split k stk p below P) as (above & im & c & rest & -> & F & Hb).
  destruct (pclose_split k im above p c rest [] F) as [content Hc].
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
            pv_live (popen i k op txt v) = rs_live (ropen i (fst k) op (RState lv m os))).
  { intros i k [|] txt; unfold popen, ropen; cbn [pv_live pv_stk rs_live map fitem].
    - unfold pv_live in Hl. rewrite Hl. reflexivity.
    - apply Add. }
  destruct t as [c| |k mr op cl|oi|b rg|c|ws|ws|vp vn vb vc vr|dk|asrc|sa|ab aa|sb sa'|nl|dn|hn];
    try apply Add; try exact Hl.
  - destruct h; [exact Hl|apply Add].
  - rewrite Hl. destruct (if cl then pick (KDelim k mr) lv else PNone) as [p below|] eqn:P;
      [|apply Open].
    destruct (Nat.ltb (tok_end s p) n); [|apply Open].
    destruct cl; [|discriminate].
    unfold pv_live in Hl. rewrite <- Hl in P.
    destruct (pclose_found _ _ _ _ P) as (content & rest & Hc & Hb).
    rewrite Hc. rewrite (proj1 (pv_add_live _ _)). exact Hb.
  - apply Open.
  - rewrite Hl. destruct (pick KBracket lv) as [p below|] eqn:P; [|apply Add].
    unfold pv_live in Hl. rewrite <- Hl in P.
    destruct (pclose_found _ _ _ _ P) as (content & rest & Hc & Hb).
    rewrite Hc. cbn [pv_live pv_stk map fitem]. rewrite ?Hb. reflexivity.
  - destruct (nbsp_rest ws) as [r|]; [|apply Add].
    destruct (nonempty_str r); [|apply Add].
    rewrite (proj1 (pv_add_live _ _)). apply Add.
  - rewrite (proj1 (pv_add_live _ _)), (proj1 (pv_trim_live v)). exact Hl.
  - assert (At : pv_live (add_text (chars dollar (vp - 2)) v) = lv)
      by (unfold add_text; destruct (nonempty_str _); [apply Add|exact Hl]).
    destruct (Nat.ltb _ _); [exact At|rewrite (proj1 (pv_add_live _ _)); exact At].
  - rewrite Hl. destruct (pick KBracket lv) as [p below|] eqn:P; [|apply Add].
    unfold pv_live in Hl. rewrite <- Hl in P.
    destruct (pclose_found _ _ _ _ P) as (content & rest & Hc & Hb).
    rewrite Hc. cbn [pv_live pv_stk map fitem]. rewrite ?Hb. reflexivity.
  - rewrite (proj1 (pv_add_items_live _ v)). exact Hl.
  - rewrite (proj1 (pv_add_items_live _ v)). exact Hl.
Qed.

Local Lemma pstep_mode : forall s n h t v,
  pv_mode v = PMNormal -> (forall b r, t <> TClose b r) -> (forall d m b c r, t <> TVerb d m b c r) ->
  (forall b a, t <> TSpan b a) -> (forall l, t <> TNote l) -> (forall b a, t <> TAttr b a) ->
  pv_mode (pstep s n h t v) = PMNormal.
Proof.
  intros s n h t v Em Ht Hv Hsp Hn Ha. unfold pstep.
  assert (Add : forall x, pv_mode (pv_add x v) = PMNormal)
    by (intros x; rewrite (proj2 (pv_add_live x v)); exact Em).
  assert (Open : forall i k op txt, pv_mode (popen i k op txt v) = PMNormal)
    by (intros i k [|] txt; [exact Em|apply Add]).
  destruct t as [c| |k mr op cl|oi|b rg|c|ws|ws|vp vn vb vc vr|dk|asrc|sa|ab aa|sb sa'|nl|dn|hn]; try apply Add; try apply Open.
  all: try (rewrite (proj2 (pv_add_items_live _ v)); exact Em).
  - destruct h; [exact Em|apply Add].
  - destruct (if cl then pick (KDelim k mr) (pv_live v) else PNone); try apply Add; try apply Open.
    destruct (Nat.ltb (tok_end s p) n); [|apply Open].
    destruct (pclose_go (KDelim k mr) [] (pv_stk v)) as [[content rest]|]; [|exact Em].
    rewrite (proj2 (pv_add_live _ _)). reflexivity.
  - destruct (Ht b rg eq_refl).
  - destruct (nbsp_rest ws); [|apply Add].
    destruct (nonempty_str s0); [rewrite (proj2 (pv_add_live _ _))|]; apply Add.
  - rewrite (proj2 (pv_add_live _ _)), (proj2 (pv_trim_live _)). exact Em.
  - destruct (Hv vp vn vb vc vr eq_refl).
  - destruct (Ha ab aa eq_refl).
  - destruct (Hsp sb sa' eq_refl).
  - destruct (Hn nl eq_refl).
Qed.

Local Lemma pclose_none : forall k stk pend,
  (forall p below, pick k (map fitem stk) <> PFound p below) ->
  pclose_go k pend stk = None.
Proof.
  intros k stk. induction stk as [|[q [k' im'] c] stk IH]; intros pend H; [reflexivity|].
  cbn [pclose_go fst]. cbn [map fitem pick fst] in H.
  destruct (key_eq k k'); [destruct (H q (map fitem stk) eq_refl)|]. apply IH, H.
Qed.

Local Lemma pstep_close_found : forall s n h b r v content rest,
  pclose_go KBracket [] (pv_stk v) = Some (content, rest) ->
  pstep s n h (TClose b r) v
  = PView rest (pv_out v)
      (PMRegion b (pclose_im (pv_stk v)) (vres content) n (n + S (S (String.length r))) "").
Proof.
  intros s n h b r v content rest Hc. unfold pstep. rewrite Hc.
  destruct (pick KBracket (pv_live v)) eqn:P; [reflexivity|];
    rewrite (pclose_none KBracket (pv_stk v) []) in Hc
      by (intros p' b'; unfold pv_live in P; rewrite P; discriminate);
    discriminate.
Qed.

Local Lemma pstep_close_none : forall s n h b r v,
  pclose_go KBracket [] (pv_stk v) = None ->
  pstep s n h (TClose b r) v = pv_add (Str (one rbrack)) v.
Proof.
  intros s n h b r v Hc. unfold pstep. rewrite Hc.
  destruct (pick KBracket (pv_live v)); reflexivity.
Qed.

Local Lemma pstep_span_found : forall s n h b a v content rest,
  pclose_go KBracket [] (pv_stk v) = Some (content, rest) ->
  pstep s n h (TSpan b a) v
  = PView rest (pv_out v)
      (PMSpan (pclose_im (pv_stk v)) (vres content) a (n + S (S (String.length b)))).
Proof.
  intros s n h b a v content rest Hc. unfold pstep. rewrite Hc.
  destruct (pick KBracket (pv_live v)) eqn:P; [reflexivity|];
    rewrite (pclose_none KBracket (pv_stk v) []) in Hc
      by (intros p' b'; unfold pv_live in P; rewrite P; discriminate);
    discriminate.
Qed.

Local Lemma pstep_span_none : forall s n h b a v,
  pclose_go KBracket [] (pv_stk v) = None ->
  pstep s n h (TSpan b a) v = pv_add (Str (one rbrack)) v.
Proof.
  intros s n h b a v Hc. unfold pstep. rewrite Hc.
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
  /\ (forall q k', In (q, k') lv -> p < q -> is_opener m q = false).

Definition step_facts (s : string) (m : matching) (n : nat) (t : token)
  (lv : list litem) : Prop :=
  match t with
  | TDelim k mr op cl =>
      match (if cl then pick (KDelim k mr) lv else PNone) with
      | PFound p _ =>
          if Nat.ltb (tok_end s p) n then is_opener m n = false /\ closes_here m n p lv
          else is_closer m n = false /\ (op = false -> is_opener m n = false)
      | PNone => is_closer m n = false /\ (op = false -> is_opener m n = false)
      end
  | TClose _ _ | TSpan _ _ =>
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

Local Lemma region_node_nonstr : forall b im l t s, region_node b im l t <> Str s.
Proof. intros [] [] l t s E; discriminate E. Qed.

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

Local Lemma xtrim_solid : forall w r, solid w -> xtrim (VIn (Str w) :: r) = VIn (Str w) :: r.
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
  exists w r, xsnoc (Str s) acc = VIn (Str w) :: r /\ solid w.
Proof.
  intros s [|y acc] Hs; [exists s, []; split; [reflexivity|exact Hs]|].
  destruct (str_view y) as [[u ->]|Hy].
  - exists (u ++ s)%string, acc. split; [reflexivity|apply solid_app, Hs].
  - exists s, (y :: acc). split; [apply xsnoc_str_nonstr, Hy|exact Hs].
Qed.

Local Lemma xtrim_xapp_solid : forall c w r, solid w ->
  xtrim (xapp c (VIn (Str w) :: r)) = xapp (xtrim c) (VIn (Str w) :: r).
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
      dv y; [destruct (Hy _ eq_refl)|..]; reflexivity.
  - change (xapp (y :: z :: c) (VIn (Str w) :: r)) with (y :: xapp (z :: c) (VIn (Str w) :: r)).
    destruct (str_view y) as [[t ->]|Hy].
    + cbn [xtrim]. destruct (strip_trailing_ws t); reflexivity.
    + dv y; [destruct (Hy _ eq_refl)|..]; reflexivity.
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

(* An opener read as text is text a trim leaves alone, or a quote's node,
   which is no text at all. *)
Local Lemma lit_solid : forall k,
  (exists s, lit k = Str s /\ solid s) \/ (forall s, lit k <> Str s).
Proof.
  intros [[k mr|] im];
    [|left; exists (bracket_open im); split; [reflexivity|destruct im; (split; [reflexivity|discriminate])]].
  cbn [lit kdecay fst snd]. unfold decay_node.
  destruct (dc_decay cfg k) as [|dfl l r] eqn:Ed; [|right; intros s E; discriminate E].
  left.
  pose proof (ws_punct _ (dchar_punct k)) as Hw.
  destruct (dwidth k) as [|n] eqn:En; [destruct (dwidth_nonzero k En)|].
  assert (Ht : solid (dtoken k))
    by (unfold dtoken; rewrite En, chars_last; apply solid_last, Hw).
  exists (ddecay_str k mr im). split; [reflexivity|].
  split; [|intros E; pose proof (ddecay_str_nonempty k mr im) as H; rewrite E in H;
            discriminate H].
  unfold ddecay_str. rewrite Ed.
  assert (Hc : solid (dtoken k ++ one rbrace))
    by (apply solid_last; reflexivity).
  destruct mr, im; cbn [andb negb append]; rewrite ?append_empty_r;
    first [exact (proj1 Ht) | exact (proj1 Hc)
          | exact (proj1 (solid_app (one lbrace) _ Ht))].
Qed.

Local Lemma xtrim_xapp_nonstr : forall c (x : vitem) r, (forall s, x <> VIn (Str s)) ->
  xtrim (xapp c (x :: r)) = xapp (xtrim c) (x :: r).
Proof.
  intros c x r Hx. destruct c as [|y [|z c]].
  - cbn [xapp]. dv x; [destruct (Hx _ eq_refl)|..]; reflexivity.
  - cbn [xapp]. destruct (str_view y) as [[t ->]|Hy].
    + rewrite (xsnoc_str_nonstr t x r Hx). cbn [xtrim].
      destruct (strip_trailing_ws t) as [|a t']; [reflexivity|].
      cbn [xapp]. rewrite (xsnoc_str_nonstr _ x r Hx). reflexivity.
    + rewrite (xsnoc_nonstr y _ Hy). dv y; [destruct (Hy _ eq_refl)|..];
        cbn [xtrim xapp]; rewrite (xsnoc_nonstr _ _ Hy); reflexivity.
  - change (xapp (y :: z :: c) (x :: r)) with (y :: xapp (z :: c) (x :: r)).
    destruct (str_view y) as [[t ->]|Hy].
    + cbn [xtrim]. destruct (strip_trailing_ws t); reflexivity.
    + dv y; [destruct (Hy _ eq_refl)|..]; reflexivity.
Qed.

Local Lemma xtrim_collapsed : forall c x acc,
  (exists s, x = Str s /\ solid s) \/ (forall s, x <> Str s) ->
  xtrim (xapp c (xsnoc x acc)) = xapp (xtrim c) (xsnoc x acc).
Proof.
  intros c x acc [(s & -> & Hs)|Hx].
  - destruct (xsnoc_solid s acc Hs) as (w & r & E & Hw). rewrite E.
    apply xtrim_xapp_solid, Hw.
  - rewrite (xsnoc_nonstr x acc (vin_nonstr x Hx)).
    apply xtrim_xapp_nonstr, vin_nonstr, Hx.
Qed.

Local Lemma collapse_trim : forall real v,
  collapse real (pv_stk (pv_trim v)) (pv_out (pv_trim v))
  = xinner xtrim (collapse real (pv_stk v) (pv_out v)).
Proof.
  intros real [[|[p k c] rest] out md]; cbn [pv_trim pv_stk pv_out fset fcontent collapse].
  - reflexivity.
  - destruct (real p); [reflexivity|].
    rewrite xinner_comp. apply xinner_ext. intros acc.
    symmetry. apply xtrim_collapsed, lit_solid.
Qed.

Local Lemma item_trim_et : forall l, item_trim (map et l) = map et (xtrim l).
Proof.
  intros [|x l]; [reflexivity|]. destruct (str_view x) as [[t ->]|Hx].
  - cbn [map et mk item_trim xtrim]. destruct (strip_trailing_ws t); reflexivity.
  - dv x; [destruct (Hx _ eq_refl)|..]; reflexivity.
Qed.

Local Lemma ttrim_embed : forall st,
  ttrim (fst (tfr st)) (snd (tfr st)) = tfr (xinner xtrim st).
Proof.
  intros [[|[k c] fs] top]; cbn [tfr ttrim xinner fst snd map]; rewrite item_trim_et;
    reflexivity.
Qed.


Local Lemma vembed_add : forall real x v,
  vembed real (pv_add x v) = tfr (xinner (xsnoc x) (collapse real (pv_stk v) (pv_out v))).
Proof. intros real x v. unfold vembed. rewrite collapse_add. reflexivity. Qed.

Local Lemma ldesc_above : forall above f rest,
  ldesc (map fitem (above ++ f :: rest)) ->
  forall g, In g above -> fst (fitem f) < fst (fitem g).
Proof.
  induction above as [|h above IH]; intros f rest D g Hg; [destruct Hg|].
  cbn [app map] in D. apply StronglySorted_inv in D as [D F].
  destruct Hg as [<-|Hg]; [|exact (IH f rest D g Hg)].
  rewrite Forall_forall in F. apply (F (fitem f)).
  apply in_map. apply in_or_app. right. left. reflexivity.
Qed.

(* The frames a found closer passes over are never closed. *)
Local Lemma passed_unreal : forall m k im p c rest above v,
  pv_stk v = (above ++ PF p (k, im) c :: rest)%list ->
  ldesc (pv_live v) -> Forall (passes k) above ->
  (forall q k', In (q, k') (pv_live v) -> p < q -> is_opener m q = false) ->
  Forall (fun f => passes k f /\ match f with PF q _ _ => is_opener m q = false end) above.
Proof.
  intros m k im p c rest above v E D F Habove.
  unfold pv_live in D, Habove. rewrite E in D, Habove.
  rewrite Forall_forall in F |- *. intros g Hg. split; [exact (F g Hg)|].
  destruct g as [q k' c'].
  apply (Habove q (fst k')).
  - apply in_map_iff. exists (PF q k' c'). split; [reflexivity|].
    apply in_or_app. left. exact Hg.
  - exact (ldesc_above above (PF p (k, im) c) rest D _ Hg).
Qed.

Local Lemma lit_normal : forall k, normal [VIn (lit k)].
Proof. intros k. exact Logic.I. Qed.

Local Lemma pclose_go_normal : forall k stk pend content rest,
  Forall (fun f => normal (fcontent f)) stk -> normal pend ->
  pclose_go k pend stk = Some (content, rest) ->
  normal content /\ Forall (fun f => normal (fcontent f)) rest.
Proof.
  intros k stk. induction stk as [|[q [k' im'] c] stk IH]; intros pend content rest N Hp H;
    [discriminate|cbn [pclose_go fst] in H].
  apply Forall_cons_iff in N as [Nc N]. cbn [fcontent] in Nc.
  destruct (key_eq k k').
  - injection H as <- <-. split; [apply normal_xapp; assumption|exact N].
  - apply (IH (xapp (xapp pend c) [VIn (lit (k', im'))]) _ _ N); [|exact H].
    apply normal_xapp; [apply normal_xapp; assumption|apply lit_normal].
Qed.

(* The bytes of a region, after the `]` at `d` and its `(` or `[`, up to
   the byte at `e` that closes it. *)
Definition region_src (s : string) (d e : nat) : string :=
  substring (S (S d)) (e - S (S d)) s.

(* What `tstep` does with a view, region and all: a region is its link,
   and a token of several bytes is its node. *)
Definition vafter (s : string) (real : nat -> bool) (v : pview)
  : tframes * list titem :=
  let '(fs, top) := vembed real v in
  match pv_mode v with
  | PMNormal => (fs, top)
  | PMRegion b im kids d e _ =>
      temit (mk (region_node b im kids (region_text b (region_src s d e)))) fs top
  | PMAtom x _ => tput (et x) fs top
  | PMSpan im kids a _ =>
      let '(fs1, top1) := if im then temit_str (one bang) fs top else (fs, top) in
      temit (Node NoPos a (Span EmptyString kids)) fs1 top1
  end.

Local Lemma pstep_tstep : forall s m n h t v,
  pv_mode v = PMNormal -> ldesc (pv_live v) -> frames_normal v ->
  step_facts s m n t (pv_live v) ->
  (forall b r, t = TClose b r -> region_src s n (n + S (S (String.length r))) = r) ->
  tstep s m n t h (fst (vembed (is_opener m) v)) (snd (vembed (is_opener m) v))
  = vafter s (is_opener m) (pstep s n h t v).
Proof.
  intros s m n h t [stk out md] Em D N Hf Hreg. set (real := is_opener m).
  cbn [pv_mode] in Em. subst md.
  unfold pv_live in D, Hf. cbn [pv_stk pv_out pv_mode] in D, N, Hf.
  unfold vembed at 1. cbn [pv_stk pv_out].
  destruct (collapse real stk out) as [fs0 top0] eqn:Ec. cbn [tfr fst snd].
  set (v := {| pv_stk := stk; pv_out := out; pv_mode := PMNormal |}).
  assert (Norm : forall v', pv_mode v' = PMNormal -> vafter s real v' = vembed real v')
    by (intros v' E; unfold vafter; rewrite E; destruct (vembed real v'); reflexivity).
  assert (Emb : forall x, vembed real (pv_add x v) = tfr (xinner (xsnoc x) (fs0, top0))).
  { intros x. rewrite vembed_add. unfold v. cbn [pv_stk pv_out]. fold real. rewrite Ec.
    reflexivity. }
  assert (AddN : forall x, vafter s real (pv_add x v) = tfr (xinner (xsnoc x) (fs0, top0))).
  { intros x. rewrite Norm; [apply Emb|]. rewrite (proj2 (pv_add_live _ _)). reflexivity. }
  assert (Str_ : forall s',
            temit_str s' (map (fun f => (fst f, map et (snd f))) fs0) (map et top0)
            = vafter s real (pv_add (Str s') v)).
  { intros s'. rewrite AddN.
    change (map (fun f : tkind * list vitem => (fst f, map et (snd f))) fs0)
      with (fst (tfr (fs0, top0))).
    change (map et top0) with (snd (tfr (fs0, top0))).
    apply temit_str_embed. }
  assert (Item_ : forall x,
            temit_item x (map (fun f => (fst f, map et (snd f))) fs0) (map et top0)
            = vafter s real (pv_add (VIn x) v)).
  { intros x. rewrite AddN.
    change (map (fun f : tkind * list vitem => (fst f, map et (snd f))) fs0)
      with (fst (tfr (fs0, top0))).
    change (map et top0) with (snd (tfr (fs0, top0))).
    apply temit_item_embed. }
  replace (snd (vembed real v)) with (map et top0)
    by (unfold vembed, v; cbn [pv_stk pv_out]; fold real; rewrite Ec; reflexivity).
  (* a closer that pairs with `p`, and the frame it closes *)
  assert (Close : forall K p below,
            pick K (map fitem stk) = PFound p below ->
            closes_here m n p (map fitem stk) ->
            exists im content rest,
              pclose_go K [] stk = Some (content, rest)
              /\ fs0 = (tkind_of (K, im), content) :: fst (collapse real rest out)
              /\ top0 = snd (collapse real rest out)
              /\ normal content
              /\ (K = KBracket -> pclose_im stk = im)).
  { intros K p below P (Hcn & Hop & Habove).
    destruct (pick_split K stk p below P) as (above & im & c & rest & E & F & Hb).
    pose proof (passed_unreal m K im p c rest above v E D F Habove) as Fr.
    rewrite E in Ec.
    destruct (close_collapse real K im above p c rest out [] Fr Hop) as (content & Hpc & Hcol).
    rewrite Hcol in Ec. injection Ec as <- <-.
    exists im, content, rest. rewrite E. split; [exact Hpc|]. split; [reflexivity|].
    split; [reflexivity|].
    split; [|intros ->; apply pclose_im_split, F].
    unfold frames_normal in N. cbn [pv_stk] in N. rewrite E in N.
    exact (proj1 (pclose_go_normal K _ [] content rest N Logic.I Hpc)). }
  destruct t as [c| |k mr op cl|oi|b rg|c|ws|ws|vp vn vb vc vr|dk|asrc|sa|ab aa|sb sa'|nl|dn|hn].
  - cbn [tstep pstep]. apply Str_.
  - cbn [tstep pstep]. destruct h.
    + rewrite Norm by reflexivity. unfold vembed, v. cbn [pv_stk pv_out]. fold real.
      rewrite Ec. reflexivity.
    + rewrite AddN.
      rewrite (xinner_ext (xsnoc _) (cons (A:=vitem) SoftBreak))
        by (intros l; apply xsnoc_nonstr; discriminate).
      destruct fs0 as [|[k c] fs]; reflexivity.
  - (* a delimiter *)
    set (K := KDelim k mr).
    set (cmr := at_rbrace (get (tok_end s n) s)).
    assert (Popen : (op = false -> is_opener m n = false) -> is_closer m n = false ->
              tstep s m n (TDelim k mr op cl) h
                (map (fun f => (fst f, map et (snd f))) fs0) (map et top0)
              = vafter s real (popen n (K, (mr && cmr)%bool) op (delim_lit k mr op cmr) v)).
    { intros Ho Hc. cbn [tstep]. unfold popen. destruct op.
      - rewrite Norm by reflexivity. unfold vembed, v. cbn [pv_stk pv_out collapse].
        fold real. rewrite Ec. destruct (real n) eqn:Hr; [reflexivity|].
        cbn [xapp]. rewrite Hc.
        change (map (fun f : tkind * list vitem => (fst f, map et (snd f))) fs0)
          with (fst (tfr (fs0, top0))).
        change (map et top0) with (snd (tfr (fs0, top0))).
        rewrite temit_item_embed.
        assert (E : delim_lit k mr true cmr = ddecay_str k mr (mr && cmr))
          by (destruct mr; reflexivity).
        unfold lit, kdecay, K. cbn [fst snd]. fold cmr. rewrite E. reflexivity.
      - rewrite (Ho eq_refl), Hc. apply Item_. }
    cbn [step_facts] in Hf. unfold v. cbn [pstep]. fold v. unfold pv_live. cbn [pv_stk pv_out].
    fold K in Hf |- *. change (pv_stk v) with stk. change (pv_out v) with out.
    destruct (if cl then pick K (map fitem stk) else PNone) as [p below|] eqn:P.
    2: { destruct Hf as [Hc Ho]. apply Popen; assumption. }
    destruct (Nat.ltb (tok_end s p) n); [|destruct Hf as [Hc Ho]; apply Popen; assumption].
    destruct Hf as (Hon & Hcl).
    destruct cl; [|discriminate].
    destruct (Close K p below P Hcl) as (im & content & rest & Hpc & -> & -> & _ & _).
    pose proof Hcl as (Hcn & _).
    rewrite Hpc. cbn [tstep]. rewrite Hon, Hcn. cbn [map fst snd tkind_of K].
    rewrite Norm by (rewrite (proj2 (pv_add_live _ _)); reflexivity).
    rewrite vembed_add. cbn [pv_stk pv_out].
    rewrite (xinner_ext (xsnoc _) (cons (A:=vitem) (dnode k (vres content))))
      by (intros l; apply xsnoc_nonstr; intros s0 E; injection E; apply dnode_nonstr).
    destruct (collapse real rest out) as [[|[k1 c1] fs1] top1]; reflexivity.
  - (* a `[` *)
    cbn [tstep pstep]. unfold popen. rewrite Norm by reflexivity. unfold vembed.
    cbn [pv_stk pv_out collapse v]. fold real. rewrite Ec.
    cbn [xapp]. destruct (real n); [reflexivity|].
    change (map (fun f : tkind * list vitem => (fst f, map et (snd f))) fs0)
      with (fst (tfr (fs0, top0))).
    change (map et top0) with (snd (tfr (fs0, top0))).
    rewrite temit_str_embed. reflexivity.
  - (* a `]` *)
    cbn [step_facts] in Hf. unfold v. cbn [pstep]. fold v. unfold pv_live. cbn [pv_stk pv_out].
    change (pv_stk v) with stk. change (pv_out v) with out.
    destruct (pick KBracket (map fitem stk)) as [p below|] eqn:P.
    2: cbn [tstep]; rewrite Hf; apply Str_.
    destruct (Close KBracket p below P Hf) as (im & content & rest & Hpc & -> & -> & Hn & Him).
    pose proof Hf as (Hcn & _).
    rewrite Hpc, (Him eq_refl). cbn [tstep]. rewrite Hcn. cbn [map fst snd tkind_of tk_image].
    unfold vafter, vembed. cbn [pv_stk pv_out pv_mode tfr].
    rewrite (Hreg b rg eq_refl). reflexivity.
  - (* an escape is text *)
    cbn [tstep pstep]. apply Str_.
  - (* an escaped whitespace run: a non-breaking space and the rest of
       the run, or text *)
    cbn [tstep pstep].
    destruct (nbsp_rest ws) as [r|]; [|apply Str_].
    change (map (fun f : tkind * list vitem => (fst f, map et (snd f))) fs0)
      with (fst (tfr (fs0, top0))).
    change (map et top0) with (snd (tfr (fs0, top0))).
    rewrite temit_embed.
    destruct (nonempty_str r).
    + rewrite Norm by (rewrite !(proj2 (pv_add_live _ _)); reflexivity).
      rewrite vembed_add, collapse_add. unfold v. cbn [pv_add pv_stk pv_out pv_mode].
      fold real. rewrite Ec.
      rewrite (xinner_ext (xsnoc NonBreakingSpace) (cons (A:=vitem) NonBreakingSpace))
        by (intros l; apply xsnoc_nonstr; discriminate).
      destruct (xinner (cons (A:=vitem) NonBreakingSpace) (fs0, top0)) as [fs1 top1] eqn:E1.
      cbn [tfr fst snd].
      change (map (fun f : tkind * list vitem => (fst f, map et (snd f))) fs1)
        with (fst (tfr (fs1, top1))).
      change (map et top1) with (snd (tfr (fs1, top1))).
      rewrite temit_str_embed. reflexivity.
    + rewrite AddN. rewrite (xinner_ext (xsnoc _) (cons (A:=vitem) NonBreakingSpace))
        by (intros l; apply xsnoc_nonstr; discriminate). reflexivity.
  - (* a hard break, after the text before it is trimmed *)
    cbn [tstep pstep].
    change (map (fun f : tkind * list vitem => (fst f, map et (snd f))) fs0)
      with (fst (tfr (fs0, top0))).
    change (map et top0) with (snd (tfr (fs0, top0))).
    rewrite ttrim_embed.
    destruct (tfr (xinner xtrim (fs0, top0))) as [fs1 top1] eqn:E1.
    rewrite Norm by (rewrite (proj2 (pv_add_live _ _)), (proj2 (pv_trim_live _)); reflexivity).
    rewrite vembed_add, collapse_trim. unfold v. cbn [pv_stk pv_out].
    fold real. rewrite Ec.
    rewrite (xinner_ext (xsnoc _) (cons (A:=vitem) HardBreak))
      by (intros l; apply xsnoc_nonstr; discriminate).
    replace fs1 with (fst (tfr (xinner xtrim (fs0, top0)))) by (rewrite E1; reflexivity).
    replace top1 with (snd (tfr (xinner xtrim (fs0, top0)))) by (rewrite E1; reflexivity).
    rewrite temit_embed. reflexivity.
  - (* a verbatim: the dollars before it, then its node, now or at its last byte *)
    cbn [tstep pstep].
    set (X := chars dollar (vp - 2)). set (w := add_text X v).
    assert (Hw : (if Nat.ltb 2 vp
                  then temit_str X (map (fun f : tkind * list vitem => (fst f, map et (snd f))) fs0)
                         (map et top0)
                  else (map (fun f : tkind * list vitem => (fst f, map et (snd f))) fs0, map et top0))
                 = tfr (collapse real (pv_stk w) (pv_out w))).
    { unfold w, add_text. destruct (Nat.ltb 2 vp) eqn:E.
      - replace (nonempty_str X) with true
          by (unfold X; destruct vp as [|[|[|vp]]]; try discriminate; reflexivity).
        change (map (fun f : tkind * list vitem => (fst f, map et (snd f))) fs0)
          with (fst (tfr (fs0, top0))).
        change (map et top0) with (snd (tfr (fs0, top0))).
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
      change (map (fun f : tkind * list vitem => (fst f, map et (snd f))) fs1)
        with (fst (tfr (fs1, top1))).
      change (map et top1) with (snd (tfr (fs1, top1))).
      change (temit (mk (verb_node vp vr vb)) (fst (tfr (fs1, top1))) (snd (tfr (fs1, top1)))
              = tfr (xinner (xsnoc (verb_node vp vr vb)) (fs1, top1))).
      rewrite temit_embed. rewrite (xinner_ext (xsnoc _) (cons (A:=vitem) (verb_node vp vr vb)))
        by (intros l; apply xsnoc_nonstr, vin_nonstr; intros ?; apply verb_node_nonstr). reflexivity.
  - (* a run of dollars: text *)
    cbn [tstep pstep]. apply Str_.
  - (* an autolink *)
    cbn [tstep pstep]. rewrite AddN.
    change (map (fun f : tkind * list vitem => (fst f, map et (snd f))) fs0)
      with (fst (tfr (fs0, top0))).
    change (map et top0) with (snd (tfr (fs0, top0))).
    rewrite temit_embed. rewrite (xinner_ext (xsnoc _) (cons (A:=vitem) (auto_node asrc)))
      by (intros l; apply xsnoc_nonstr; intros s0; unfold auto_node; destruct (auto_email asrc);
          discriminate). reflexivity.
  - (* a symbol *)
    cbn [tstep pstep]. rewrite AddN.
    change (map (fun f : tkind * list vitem => (fst f, map et (snd f))) fs0)
      with (fst (tfr (fs0, top0))).
    change (map et top0) with (snd (tfr (fs0, top0))).
    rewrite temit_embed. rewrite (xinner_ext (xsnoc _) (cons (A:=vitem) (Symbol sa)))
      by (intros l; apply xsnoc_nonstr; discriminate). reflexivity.
  - (* a spec waits where it stands, added at its `}` *)
    cbn [tstep pstep]. unfold vafter, vembed, v. cbn [pv_setmode pv_stk pv_out pv_mode].
    fold real. rewrite Ec. destruct fs0 as [|[k c] fs]; reflexivity.
  - (* a `]` before a span's spec *)
    cbn [step_facts] in Hf. unfold v. cbn [pstep]. fold v. unfold pv_live. cbn [pv_stk pv_out].
    change (pv_stk v) with stk. change (pv_out v) with out.
    destruct (pick KBracket (map fitem stk)) as [p below|] eqn:P.
    2: cbn [tstep]; rewrite Hf; apply Str_.
    destruct (Close KBracket p below P Hf) as (im & content & rest & Hpc & -> & -> & Hn & Him).
    pose proof Hf as (Hcn & _).
    rewrite Hpc, (Him eq_refl). cbn [tstep]. rewrite Hcn. cbn [map fst snd tkind_of tk_image].
    unfold vafter, vembed. cbn [pv_stk pv_out pv_mode tfr]. reflexivity.
  - (* a footnote reference, added at its `]` *)
    cbn [tstep pstep]. unfold vafter, vembed, v. cbn [pv_setmode pv_stk pv_out pv_mode].
    fold real. rewrite Ec. destruct fs0 as [|[k c] fs]; reflexivity.
  - (* a run of periods *)
    cbn [tstep pstep].
    rewrite Norm by (rewrite (proj2 (pv_add_items_live _ v)); reflexivity).
    unfold vembed. rewrite collapse_add_items.
    change (map (fun f : tkind * list vitem => (fst f, map et (snd f))) fs0)
      with (fst (tfr (fs0, top0))).
    change (map et top0) with (snd (tfr (fs0, top0))).
    rewrite temit_items_embed. unfold v. cbn [pv_stk pv_out]. fold real. rewrite Ec.
    reflexivity.
  - (* a run of hyphens *)
    cbn [tstep pstep].
    rewrite Norm by (rewrite (proj2 (pv_add_items_live _ v)); reflexivity).
    unfold vembed. rewrite collapse_add_items.
    change (map (fun f : tkind * list vitem => (fst f, map et (snd f))) fs0)
      with (fst (tfr (fs0, top0))).
    change (map et top0) with (snd (tfr (fs0, top0))).
    rewrite temit_items_embed. unfold v. cbn [pv_stk pv_out]. fold real. rewrite Ec.
    reflexivity.
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
  - dv x; [destruct (Hx _ eq_refl)|..]; exact N.
Qed.

Local Lemma pv_trim_normal : forall v, frames_normal v -> frames_normal (pv_trim v).
Proof.
  intros [[|f rest] out md] N; [constructor|].
  unfold frames_normal in *. cbn [pv_trim pv_stk] in *.
  apply Forall_cons_iff in N as [Nf N]. constructor; [|exact N].
  destruct f; cbn [fset fcontent] in *; apply normal_xtrim, Nf.
Qed.

Local Lemma pv_add_items_normal : forall xs v,
  frames_normal v -> frames_normal (pv_add_items xs v).
Proof.
  induction xs as [|x xs IH]; intros v N; [exact N|].
  apply IH, pv_add_normal, N.
Qed.

Local Lemma pstep_normal : forall s n h t v,
  frames_normal v -> frames_normal (pstep s n h t v).
Proof.
  intros s n h t [stk out md] N. unfold pstep.
  assert (Open : forall i k op txt, frames_normal (popen i k op txt {| pv_stk := stk; pv_out := out; pv_mode := md |})).
  { intros i k [|] txt; [constructor; [exact Logic.I|exact N]|apply pv_add_normal, N]. }
  destruct t as [c| |k mr op cl|oi|b rg|c|ws|ws|vp vn vb vc vr|dk|asrc|sa|ab aa|sb sa'|nl|dn|hn];
    try (apply pv_add_normal; exact N); try exact N.
  - destruct h; [exact N|apply pv_add_normal, N].
  - unfold pv_live. cbn [pv_stk pv_out].
    destruct (if cl then pick (KDelim k mr) (map fitem stk) else PNone) as [p below|];
      [|apply Open].
    destruct (Nat.ltb (tok_end s p) n); [|apply Open].
    destruct (pclose_go (KDelim k mr) [] stk) as [[content rest]|] eqn:Hc; [|exact N].
    apply pv_add_normal. exact (proj2 (pclose_go_normal _ stk [] content rest N Logic.I Hc)).
  - apply Open.
  - unfold pv_live. cbn [pv_stk pv_out].
    destruct (pick KBracket (map fitem stk));
      destruct (pclose_go KBracket [] stk) as [[content rest]|] eqn:Hc;
      try (apply pv_add_normal; exact N).
    exact (proj2 (pclose_go_normal _ stk [] content rest N Logic.I Hc)).
  - destruct (nbsp_rest ws) as [r|]; [|apply pv_add_normal, N].
    destruct (nonempty_str r); repeat apply pv_add_normal; exact N.
  - apply pv_add_normal, pv_trim_normal, N.
  - assert (N' : frames_normal (add_text (chars dollar (vp - 2)) (PView stk out md)))
      by (unfold add_text; destruct (nonempty_str _); [apply pv_add_normal|]; exact N).
    destruct (Nat.ltb _ _); [exact N'|apply pv_add_normal, N'].
  - unfold pv_live. cbn [pv_stk pv_out].
    destruct (pick KBracket (map fitem stk));
      destruct (pclose_go KBracket [] stk) as [[content rest]|] eqn:Hc;
      try (apply pv_add_normal; exact N).
    exact (proj2 (pclose_go_normal _ stk [] content rest N Logic.I Hc)).
  - apply pv_add_items_normal, N.
  - apply pv_add_items_normal, N.
Qed.

(* Nor an empty `Str`: every text the view adds is a token's, and a
   token is never empty. *)
Definition clean (l : list vitem) : Prop := Forall (fun x : vitem => x <> VIn (Str "")) l.

Definition frames_clean (v : pview) : Prop :=
  Forall (fun f => clean (fcontent f)) (pv_stk v).

Local Lemma clean_xsnoc : forall (x : vitem) l,
  x <> VIn (Str "") -> clean l -> clean (xsnoc x l).
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

Local Lemma lit_clean : forall k, clean [VIn (lit k)].
Proof.
  intros k. destruct (lit_solid k) as [(s & E & _ & Hs)|Hn].
  - rewrite E. constructor; [|constructor]. intros X. injection X as X. exact (Hs X).
  - constructor; [|constructor]. intros X. injection X as X. exact (Hn _ X).
Qed.

Local Lemma pclose_go_clean : forall k stk pend content rest,
  Forall (fun f => clean (fcontent f)) stk -> clean pend ->
  pclose_go k pend stk = Some (content, rest) ->
  clean content /\ Forall (fun f => clean (fcontent f)) rest.
Proof.
  intros k stk. induction stk as [|[q [k' im'] c] stk IH]; intros pend content rest N Hp H;
    [discriminate|cbn [pclose_go fst] in H].
  apply Forall_cons_iff in N as [Nc N]. cbn [fcontent] in Nc.
  destruct (key_eq k k').
  - injection H as <- <-. split; [apply clean_xapp; assumption|exact N].
  - apply (IH (xapp (xapp pend c) [VIn (lit (k', im'))]) _ _ N); [|exact H].
    apply clean_xapp; [apply clean_xapp; assumption|apply lit_clean].
Qed.

Local Lemma word_split_clean : forall out,
  clean (map vof out) -> clean (map vof (snd (word_split out))).
Proof.
  induction out as [|[p a v] rest IH]; intros C; [exact C|].
  pose proof (proj1 (Forall_cons_iff _ _ _) C) as [Cp Cr]. specialize (IH Cr).
  destruct a as [|kv a]; [|exact C].
  destruct v; try exact C; cbn [word_split].
  - destruct (last_ws_split s) as [pre w].
    destruct (nonempty_str w); [|exact C].
    destruct (nonempty_str pre) eqn:Ep.
    + cbn [snd map vof]. constructor; [|exact Cr].
      intros E. injection E as ->. discriminate Ep.
    + destruct (word_split rest) as [ws before]; exact IH.
  - destruct (word_split rest) as [ws before]; exact IH.
Qed.

(* What a closed pair gives back holds no empty `Str` either. *)
Local Lemma vres_clean : forall c, clean c -> clean (vback (vres c)).
Proof.
  intros c. rewrite vback_vres. unfold vsettle.
  induction c as [|x c IH]; intros C; [constructor|].
  apply Forall_cons_iff in C as [Cx C]. specialize (IH C).
  destruct x as [x|kv a x|a]; cbn [map et resolve_rev].
  - destruct x; try (constructor; [discriminate|exact IH]).
    cbn [push mk]. rewrite vof_str_snoc. apply clean_xsnoc; assumption.
  - constructor; [discriminate|exact IH].
  - pose proof (word_split_clean _ IH) as Cb. unfold attach.
    destruct (word_split (resolve_rev (map et c))) as [[|y ws] before]; cbn [snd] in Cb.
    + destruct (resolve_rev (map et c)) as [|[p a' v] rest]; [exact IH|].
      apply Forall_cons_iff in IH as [Ih It].
      destruct a' as [|kv a'].
      * destruct v; try (constructor; [destruct (Attr.merge a []); discriminate|exact It]);
          constructor; assumption.
      * destruct (Attr.merge_cons a kv a') as (y & r & E).
        destruct v; try (rewrite E; constructor; [discriminate|exact It]);
          constructor; assumption.
    + destruct a as [|kv a]; [exact IH|]. constructor; [|exact Cb].
      destruct ws as [|z w']; destruct y; discriminate.
Qed.

(* A closed pair's nodes, as a region holds them. *)
Definition kids_ok (kids : inlines) : Prop := Forall bare kids /\ clean (map vof kids).

Local Lemma kids_ok_vres : forall c, clean c -> kids_ok (vres c).
Proof.
  intros c C. split; [apply vres_ok|].
  rewrite <- (rev_involutive (map vof (vres c))). apply Forall_rev. exact (vres_clean c C).
Qed.

Local Lemma pv_add_clean : forall (x : vitem) v,
  x <> VIn (Str "") -> frames_clean v -> frames_clean (pv_add x v).
Proof.
  intros x [[|f rest] out md] Hx N; [constructor|].
  unfold frames_clean in *. cbn [pv_add pv_stk] in *.
  apply Forall_cons_iff in N as [Nf N]. constructor; [|exact N].
  destruct f; cbn [fset fcontent] in *; apply clean_xsnoc; assumption.
Qed.

(* A run token of no bytes, which `tok_at` never gives. *)
Definition empty_run (t : token) : Prop := t = TDollars 0 \/ t = TDots 0 \/ t = TDash 0.

Ltac norun := first [discriminate | (let E := fresh in intros [E|[E|E]]; discriminate E)].

Local Lemma app_ne_r : forall a b, b <> "" -> (a ++ b)%string <> "".
Proof. intros [|c a] b H; [exact H|discriminate]. Qed.

Local Lemma dots_items_ne : forall n, n <> 0 ->
  Forall (fun x : inline => VIn x <> VIn (Str "")) (dots_items n).
Proof.
  intros n Hn. unfold dots_items. destruct smart_typography.
  - apply Forall_app. split.
    + apply Forall_forall. intros x Hx. apply repeat_spec in Hx. subst x.
      unfold ellipsis_node. discriminate.
    + destruct (Nat.modulo n 3) as [|r]; cbn [Nat.eqb]; [constructor|].
      constructor; [|constructor]. cbn [chars]. discriminate.
  - destruct n as [|n]; [contradiction|].
    constructor; [|constructor]. cbn [chars]. discriminate.
Qed.

Local Lemma dots_items_nonempty : forall n, n <> 0 -> dots_items n <> [].
Proof.
  intros n Hn. unfold dots_items. destruct smart_typography; [|discriminate].
  destruct (Nat.div n 3) as [|q] eqn:Eq; [|discriminate].
  pose proof (Nat.div_mod_eq n 3) as D. rewrite Eq in D.
  destruct (Nat.modulo n 3) as [|r]; [lia|discriminate].
Qed.

Local Lemma dash_items_nonempty : forall n, n <> 0 -> dash_items n <> [].
Proof.
  intros n Hn. unfold dash_items. destruct (dash_run_smart n) eqn:Ed; [|discriminate].
  assert (H2 : 2 <= n)
    by (unfold dash_run_smart in Ed; apply andb_true_iff in Ed as [Ed _];
        apply Nat.leb_le, Ed).
  pose proof (dash_counts_some n H2) as Hc.
  destruct (dash_counts n) as [[[|em] [|en]] lit]; cbn in Hc |- *; try lia; discriminate.
Qed.

Local Lemma dash_items_ne : forall n, n <> 0 ->
  Forall (fun x : inline => VIn x <> VIn (Str "")) (dash_items n).
Proof.
  intros n Hn. unfold dash_items. destruct (dash_run_smart n).
  - destruct (dash_counts n) as [[em en] lit]. apply Forall_app. split;
      apply Forall_forall; intros x Hx; apply repeat_spec in Hx; subst x;
      [unfold emdash_node|unfold endash_node]; discriminate.
  - destruct n as [|n]; [contradiction|].
    constructor; [|constructor]. cbn [chars]. discriminate.
Qed.

Local Lemma pv_add_items_clean : forall xs v,
  Forall (fun x : inline => VIn x <> VIn (Str "")) xs ->
  frames_clean v -> frames_clean (pv_add_items xs v).
Proof.
  induction xs as [|x xs IH]; intros v Hx N; [exact N|].
  apply Forall_cons_iff in Hx as [Hx Hxs]. apply IH; [exact Hxs|].
  apply pv_add_clean; assumption.
Qed.

Local Lemma tok_text_ne : forall t,
  (forall d m b c r, t <> TVerb d m b c r) -> ~ empty_run t -> tok_text t <> "".
Proof.
  intros [c| |k [|] [|] cl|[|]|b rg|c|ws|ws|d m b c r|[|dk]|asrc|sa|ab aa|sb sa'|nl|[|dn]|[|hn]]
    Hv H0; cbn; try discriminate;
    try (pose proof (dtoken_nonempty k) as H; destruct (dtoken k); discriminate).
  - destruct (Hv d m b c r eq_refl).
  - destruct H0. left. reflexivity.
  - destruct H0. right. left. reflexivity.
  - destruct H0. right. right. reflexivity.
Qed.

Local Lemma delim_lit_ne : forall k mr op cm, delim_lit k mr op cm <> "".
Proof.
  intros k mr op cm E. unfold delim_lit in E.
  destruct (mr && op)%bool;
    [pose proof (ddecay_str_nonempty k true cm) as H
    |pose proof (ddecay_str_nonempty k false mr) as H]; rewrite E in H; discriminate H.
Qed.

Local Lemma clean_xtrim : forall l, clean l -> clean (xtrim l).
Proof.
  intros [|x l] N; [constructor|]. destruct (str_view x) as [[t ->]|Hx].
  - apply Forall_cons_iff in N as [_ N]. cbn [xtrim].
    destruct (strip_trailing_ws t) as [|a t']; [exact N|].
    constructor; [discriminate|exact N].
  - dv x; [destruct (Hx _ eq_refl)|..]; exact N.
Qed.

Local Lemma pv_trim_clean : forall v, frames_clean v -> frames_clean (pv_trim v).
Proof.
  intros [[|f rest] out md] N; [constructor|].
  unfold frames_clean in *. cbn [pv_trim pv_stk] in *.
  apply Forall_cons_iff in N as [Nf N]. constructor; [|exact N].
  destruct f; cbn [fset fcontent] in *; apply clean_xtrim, Nf.
Qed.

Local Lemma pstep_clean : forall s n h t v,
  ~ empty_run t -> frames_clean v -> frames_clean (pstep s n h t v).
Proof.
  intros s n h t [stk out md] H0 N.
  assert (Str_ : forall s', s' <> "" -> VIn (Str s') <> VIn (Str ""))
    by (intros s' H E; injection E as E; contradiction).
  unfold pstep.
  assert (Open : forall i k op txt, txt <> "" ->
                 frames_clean (popen i k op txt {| pv_stk := stk; pv_out := out; pv_mode := md |})).
  { intros i k [|] txt Ht; [constructor; [constructor|exact N]|apply pv_add_clean; [apply kdecay_ne, Ht|exact N]]. }
  destruct t as [c| |k mr op cl|oi|b rg|c|ws|ws|vp vn vb vc vr|dk|asrc|sa|ab aa|sb sa'|nl|dn|hn].
  - apply pv_add_clean; [discriminate|exact N].
  - destruct h; [exact N|apply pv_add_clean; [discriminate|exact N]].
  - unfold pv_live. cbn [pv_stk pv_out].
    destruct (if cl then pick (KDelim k mr) (map fitem stk) else PNone) as [p below|];
      [|apply Open, delim_lit_ne].
    destruct (Nat.ltb (tok_end s p) n); [|apply Open, delim_lit_ne].
    destruct (pclose_go (KDelim k mr) [] stk) as [[content rest]|] eqn:Hc; [|exact N].
    apply pv_add_clean; [apply vin_nonstr, dnode_nonstr|].
    exact (proj2 (pclose_go_clean _ stk [] content rest N (Forall_nil _) Hc)).
  - apply Open. destruct oi; discriminate.
  - unfold pv_live. cbn [pv_stk pv_out].
    destruct (pick KBracket (map fitem stk));
      destruct (pclose_go KBracket [] stk) as [[content rest]|] eqn:Hc;
      try (apply pv_add_clean; [apply Str_, tok_text_ne; norun|exact N]).
    exact (proj2 (pclose_go_clean _ stk [] content rest N (Forall_nil _) Hc)).
  - apply pv_add_clean; [apply Str_|exact N].
    unfold esc_text. destruct (is_punct c); discriminate.
  - destruct (nbsp_rest ws) as [r|];
      [|apply pv_add_clean; [apply Str_, (tok_text_ne (TEscWs ws)); norun|exact N]].
    destruct (nonempty_str r) eqn:Er.
    + apply pv_add_clean; [|apply pv_add_clean; [discriminate|exact N]].
      apply Str_. intros ->. discriminate Er.
    + apply pv_add_clean; [discriminate|exact N].
  - apply pv_add_clean; [discriminate|apply pv_trim_clean, N].
  - assert (N' : frames_clean (add_text (chars dollar (vp - 2)) (PView stk out md))).
    { unfold add_text. destruct (nonempty_str _) eqn:Ene; [|exact N].
      apply pv_add_clean; [|exact N]. apply Str_. intros E. rewrite E in Ene. discriminate. }
    destruct (Nat.ltb _ _); [exact N'|apply pv_add_clean; [apply vin_nonstr, verb_node_nonstr|exact N']].
  - apply pv_add_clean; [apply Str_, tok_text_ne; [discriminate|exact H0]|exact N].
  - apply pv_add_clean; [apply vin_nonstr, auto_node_nonstr|exact N].
  - apply pv_add_clean; [discriminate|exact N].
  - exact N.
  - unfold pv_live. cbn [pv_stk pv_out].
    destruct (pick KBracket (map fitem stk));
      destruct (pclose_go KBracket [] stk) as [[content rest]|] eqn:Hc;
      try (apply pv_add_clean; [apply Str_; discriminate|exact N]).
    exact (proj2 (pclose_go_clean _ stk [] content rest N (Forall_nil _) Hc)).
  - exact N.
  - apply pv_add_items_clean; [|exact N].
    apply dots_items_ne. intros ->. apply H0. right. left. reflexivity.
  - apply pv_add_items_clean; [|exact N].
    apply dash_items_ne. intros ->. apply H0. right. right. reflexivity.
Qed.

Local Lemma pbyte_normal : forall i c v, frames_normal v -> frames_normal (pbyte i c v).
Proof.
  intros i c [stk out md] N. unfold pbyte. cbn [pv_mode].
  destruct md as [|b im kids d e txt|x e|im sk sat se]; [exact N| | |].
  - destruct (Nat.eqb i e); [apply pv_add_normal; exact N|exact N].
  - destruct (Nat.eqb i e); [apply pv_add_normal; exact N|exact N].
  - destruct (Nat.eqb i se); [apply pv_add_normal; destruct im; [apply pv_add_normal|]; exact N|exact N].
Qed.

(* The node a token of several bytes adds is no text. *)
Definition atom_ok (v : pview) : Prop :=
  match pv_mode v with PMAtom x _ => forall s, x <> Str s | _ => True end.

Local Lemma pbyte_clean : forall i c v,
  atom_ok v -> frames_clean v -> frames_clean (pbyte i c v).
Proof.
  intros i c [stk out md] A N. unfold atom_ok in A. unfold pbyte. cbn [pv_mode] in *.
  destruct md as [|b im kids d e txt|x e|im sk sat se]; [exact N| | |].
  - destruct (Nat.eqb i e);
      [apply pv_add_clean; [apply vin_nonstr, region_node_nonstr|exact N]|exact N].
  - destruct (Nat.eqb i e); [apply pv_add_clean; [apply A|exact N]|exact N].
  - destruct (Nat.eqb i se); [|exact N].
    apply pv_add_clean; [destruct sat; discriminate|].
    destruct im; [apply pv_add_clean; [discriminate|exact N]|exact N].
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
    apply is_opener_iff in E as [j Hj]. destruct (P q j Hj) as (_ & _ & _ & [(Hin & _) _] & _).
    exact (Hq Hin). }
  assert (NoClose : rs_pairs (rstep s n t st) = rs_pairs st -> is_closer m n = false).
  { intros E. destruct (is_closer m n) eqn:C; [|reflexivity]. exfalso.
    apply is_closer_iff in C as [i Hi]. apply (Hp i n (le_n n)) in Hi. rewrite E in Hi.
    specialize (ri_bound_pairs s n st I i n Hi). lia. }
  assert (NotOs : rs_os (rstep s n t st) = rs_os st -> ~ In n os).
  { intros E H. apply (Ho n (le_n n)) in H. rewrite E in H.
    specialize (ri_bound_os s n st I n H). lia. }
  assert (Above : forall p, In (p, n) m ->
            forall q k', In (q, k') (rs_live st) -> p < q -> is_opener m q = false).
  { intros p Hpn q k' Hq Hpq. destruct (is_opener m q) eqn:E; [|reflexivity]. exfalso.
    apply is_opener_iff in E as [j Hj].
    apply (ri_live s n st I) in Hq as (_ & Hqn & _ & _ & Hd).
    destruct (P q j Hj) as (kq & Hkq & _ & Cq & _).
    pose proof Cq as [(_ & _ & _ & _ & Hdq) _].
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
    apply NoOpen. intros Hin. apply O in Hin as (_ & _ & Hc). apply Hc. exists p. exact Hpn. }
  assert (Paired : forall p, (forall a b, b <= n -> In (a, b) m <-> In (a, b) ((p, n) :: rs_pairs st)) ->
            closes_here m n p (rs_live st) /\ is_opener m n = false).
  { intros p H. assert (Hpn : In (p, n) m) by (apply (H p n (le_n n)); left; reflexivity).
    split; [split; [apply is_closer_iff; exists p; exact Hpn|]; split|].
    - apply is_opener_iff. exists n. exact Hpn.
    - exact (Above p Hpn).
    - apply NoOpen. intros Hin. apply O in Hin as (_ & _ & Hc). apply Hc.
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
  destruct t as [c| |k mr op cl|oi|b rg|c|ws|ws|vp vn vb vc vr|dk|asrc|sa|ab aa|sb sa'|nl|dn|hn]; try exact Logic.I.
  - remember (if cl then pick (KDelim k mr) lv else PNone) as r eqn:P'.
    destruct r as [p below|].
    + remember (Nat.ltb (tok_end s p) n) as l eqn:L. destruct l.
      * destruct (Paired p Hp) as [A B]. split; assumption.
      * unfold ropen in Hp, Ho. split; [apply Unpaired; destruct op; exact Hp|].
        intros ->. apply Unopened. exact Ho.
    + unfold ropen in Hp, Ho. split; [apply Unpaired; destruct op; exact Hp|].
      intros ->. apply Unopened. exact Ho.
  - remember (pick KBracket lv) as r eqn:P'. destruct r as [p below|].
    2: exact (Unpaired Hp).
    exact (proj1 (Paired p Hp)).
  - remember (pick KBracket lv) as r eqn:P'. destruct r as [p below|].
    2: exact (Unpaired Hp).
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


(* Through a region that ends at `e`. *)
Local Lemma region_walk : forall s b im kids d e rest out i h2 v2,
  S (S d) <= e < String.length s -> S d <= i <= e ->
  pruns s i false
    (PView rest out (PMRegion b im kids d e (substring (S (S d)) (i - S (S d)) s)))
    (String.length s) h2 v2 ->
  pruns s (S e) false
    (pv_add (region_node b im kids (region_text b (region_src s d e)))
       (PView rest out PMNormal))
    (String.length s) h2 v2.
Proof.
  intros s b im kids d e rest out i h2 v2 Hb Hi.
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

Local Lemma substring_nil : forall s a, substring a 0 s = "".
Proof. induction s as [|x s IH]; intros [|a]; cbn; try reflexivity; apply IH. Qed.

Local Lemma substring_sdrop : forall ps p k, substring p k ps = substring 0 k (sdrop p ps).
Proof.
  induction ps as [|x ps IH]; intros [|p] k; cbn [substring sdrop]; try reflexivity.
  - destruct k; reflexivity.
  - apply IH.
Qed.

Local Lemma substring_prefix : forall r t, substring 0 (String.length r) (r ++ t) = r.
Proof. induction r as [|x r IH]; intros t; [destruct t; reflexivity|cbn; rewrite IH; reflexivity]. Qed.

(* A closing `]`'s region is the bytes after its `(` or `[`, up to the
   byte that closes it. *)
Local Lemma tok_at_region : forall s n b r l,
  tok_at s n = Some (TClose b r, l) ->
  region_src s n (n + S (S (String.length r))) = r
  /\ n + S (S (String.length r)) < String.length s.
Proof.
  intros s n b r l Hat. destruct (tok_at_close s n b r l Hat) as [_ [rest Er]].
  pose proof (sdrop_length n s) as L. rewrite Er in L. cbn [String.length] in L.
  rewrite length_append in L. cbn [String.length] in L.
  split; [|lia].
  unfold region_src. replace (n + S (S (String.length r)) - S (S n)) with (String.length r) by lia.
  rewrite substring_sdrop. replace (S (S n)) with (n + 2) by lia. rewrite <- sdrop_sdrop, Er.
  apply substring_prefix.
Qed.

(* The view enters a region exactly where the chain jumps. *)
Local Lemma pstep_chain : forall s n h t l v st,
  rinv s n st -> tok_at s n = Some (t, l) -> pv_live v = rs_live st -> pv_mode v = PMNormal ->
  chain_next s (rs_pairs (rstep s n t st)) n
  = match pv_mode (pstep s n h t v) with
    | PMNormal => Some (n + l)
    | PMRegion _ _ _ _ e _ => Some (S e)
    | PMAtom _ _ => Some (n + l)
    | PMSpan _ _ _ e => Some (S e)
    end.
Proof.
  intros s n h t l v st I Ht Hl Em. unfold chain_next. rewrite Ht.
  destruct t as [c| |k mr op cl|oi|b rg|c|ws|ws|vp vn vb vc vr|dk|asrc|sa|ab aa|sb sa'|nl|dn|hn];
    try (rewrite pstep_mode by (assumption || discriminate); reflexivity).
  5: reflexivity.
  3: reflexivity.
  3: { pose proof (tok_at_span s n sb sa' l Ht) as [-> _].
       assert (Nc : is_closer (rs_pairs st) n = false).
       { destruct (is_closer (rs_pairs st) n) eqn:C; [|reflexivity].
         apply is_closer_iff in C as [i Hi]. specialize (ri_bound_pairs s n st I i n Hi). lia. }
       destruct st as [lv m os]. cbn [rs_live rs_pairs] in *. unfold rstep, pstep.
       cbn [rs_live rs_pairs]. rewrite Hl.
       destruct (pick KBracket lv) as [p below|] eqn:P.
       2: cbn [rs_pairs]; rewrite Nc, (proj2 (pv_add_live _ _)), Em; reflexivity.
       unfold pv_live in Hl. rewrite <- Hl in P.
       destruct (pclose_found _ _ _ _ P) as (content & rest & Hc & _).
       rewrite Hc. cbn [pv_mode rs_pairs].
       assert (C : is_closer ((p, n) :: m) n = true) by (cbn; rewrite Nat.eqb_refl; reflexivity).
       rewrite C. f_equal. lia. }
  2: { unfold pstep. destruct (Nat.ltb (S n) (tok_end s n)); [reflexivity|].
       rewrite (proj2 (pv_add_live _ _)), (proj2 (add_text_live _ _)), Em. reflexivity. }
  pose proof (tok_at_close s n b rg l Ht) as [-> _].
  assert (Nc : is_closer (rs_pairs st) n = false).
  { destruct (is_closer (rs_pairs st) n) eqn:C; [|reflexivity].
    apply is_closer_iff in C as [i Hi]. specialize (ri_bound_pairs s n st I i n Hi). lia. }
  destruct st as [lv m os]. cbn [rs_live rs_pairs] in *. unfold rstep. cbn [rs_live rs_pairs].
  destruct (pick KBracket lv) as [p below|] eqn:P.
  2: cbn [rs_pairs]; rewrite Nc, pstep_close_none;
       [rewrite (proj2 (pv_add_live _ _)), Em; reflexivity|];
       apply pclose_none; intros p' b'; unfold pv_live in Hl; rewrite Hl, P; discriminate.
  unfold pv_live in Hl. rewrite <- Hl in P.
  destruct (pclose_found _ _ _ _ P) as (content & rest & Hc & _).
  rewrite (pstep_close_found s n h b rg v content rest Hc).
  assert (C : is_closer ((p, n) :: m) n = true) by (cbn; rewrite Nat.eqb_refl; reflexivity).
  cbn [pv_mode rs_pairs]. rewrite C. f_equal. lia.
Qed.

(* Openers of the stack at the end of the reading are never closed. *)
Local Lemma final_unreal : forall s n st q k,
  rinv s n st -> In (q, k) (rs_live st) -> is_opener (rs_pairs st) q = false.
Proof.
  intros s n st q k I H. apply (ri_live s n st I) in H as (_ & _ & _ & _ & Hd).
  destruct (is_opener (rs_pairs st) q) eqn:O; [|reflexivity]. exfalso.
  apply is_opener_iff in O as [j Hj]. apply Hd. left. exists j.
  split; [exact (ri_bound_pairs s n st I q j Hj)|exact Hj].
Qed.

Local Lemma frames_unreal : forall real v,
  (forall q k, In (q, k) (pv_live v) -> real q = false) ->
  Forall (fun f => match f with PF q _ _ => real q = false end) (pv_stk v).
Proof.
  intros real v H. apply Forall_forall. intros [q k c] Hf.
  apply (H q (fst k)). unfold pv_live. apply in_map_iff. exists (PF q k c). auto.
Qed.

(* A view with no frame that will be closed reads as its flattening. *)
Local Lemma flatten_tree : forall real v,
  Forall (fun f => match f with PF q _ _ => real q = false end) (pv_stk v) ->
  snd (vembed real v) = map et (pflatten_go [] (pv_stk v) (pv_out v)).
Proof.
  intros real v F. destruct (flatten_collapse real (pv_stk v) (pv_out v) [] F) as [_ E2].
  rewrite E2. reflexivity.
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

(* Through a span's spec. *)
Local Lemma span_walk : forall s im kids a e v i h2 v2,
  pv_mode v = PMSpan im kids a e -> i <= e -> e < String.length s ->
  pruns s i false v (String.length s) h2 v2 ->
  pruns s (S e) false
    (pv_add (vof (Node NoPos a (Span EmptyString kids)))
       (let v' := pv_setmode PMNormal v in if im then pv_add (Str (one bang)) v' else v'))
    (String.length s) h2 v2.
Proof.
  intros s im kids a e v i h2 v2 Em Hi He. remember (e - i) as k eqn:Hk. revert i Hi Hk.
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
  snd (tgo s m f n h (fst (vembed (is_opener m) v)) (snd (vembed (is_opener m) v)))
  = map et (pflatten v2).
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
       unfold pflatten.
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
  pose proof (pstep_tstep s m n h t v Em ltac:(rewrite Hl; exact (ri_desc s n st I)) N Hfacts
                (fun b r E => proj1 (tok_at_region s n b r l ltac:(rewrite <- E; exact Hat))))
    as E.
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
  destruct (pv_mode (pstep s n h t v)) as [|b im kids d e txt|x e|im sk sat se] eqn:Em'.
  - (* the next token *)
    destruct Nx as [I' Hq'].
    destruct (vembed real (pstep s n h t v)) as [fs top] eqn:Ev.
    replace fs with (fst (vembed real (pstep s n h t v))) by (rewrite Ev; reflexivity).
    replace top with (snd (vembed real (pstep s n h t v))) by (rewrite Ev; reflexivity).
    apply (IH (n + l) st' (is_hard t) (pstep s n h t v) h2 v2 Hm I' Hq' ltac:(lia) Hr Em' Hl' N' H).
  - (* a region: its bytes, then the token after it *)
    assert (Rg : exists r rest, t = TClose b r /\ d = n /\ txt = ""
              /\ e = n + S (S (String.length r))
              /\ pstep s n h t v = PView rest (pv_out v) (PMRegion b im kids n e "")).
    { destruct t as [c| |k mr op cl|oi|b0 rg0|c|ws|ws|vp vn vb vc vr|dk|asrc|sa|ab aa|sb sa'|nl|dn|hn];
        try (rewrite pstep_mode in Em' by (assumption || discriminate); discriminate);
        try (cbn [pstep pv_setmode pv_mode] in Em'; discriminate Em');
        try (destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|] eqn:Hc;
             [rewrite (pstep_span_found s n h _ _ v content rest Hc) in Em'
             |rewrite (pstep_span_none s n h _ _ v Hc), (proj2 (pv_add_live _ _)), Em in Em'];
             discriminate Em');
        try (unfold pstep in Em'; destruct (Nat.ltb _ _); cbn [pv_mode pv_setmode] in Em';
             [discriminate
             |rewrite (proj2 (pv_add_live _ _)), (proj2 (add_text_live _ _)), Em in Em';
              discriminate]).
      destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|] eqn:Hc.
      2: { rewrite pstep_close_none in Em' by exact Hc.
           rewrite (proj2 (pv_add_live _ _)), Em in Em'. discriminate. }
      rewrite (pstep_close_found s n h b0 rg0 v content rest Hc) in Em' |- *.
      cbn [pv_mode] in Em'. inversion Em'; subst. exists rg0, rest. auto. }
    destruct Rg as (r & rest & -> & -> & -> & -> & Ep).
    destruct (tok_at_region s n b r l Hat) as [_ Hb].
    pose proof (tok_at_close s n b r l Hat) as [-> _].
    rewrite Ep in H, Hl', N' |- *. cbn [is_hard] in *.
    set (e := n + S (S (String.length r))) in *.
    rewrite <- (substring_nil s (S (S n))), <- (Nat.sub_diag (S (S n))) in H.
    replace (S (S n) - S (S n)) with (S n - S (S n)) in H by lia.
    apply (region_walk s b im kids n e rest (pv_out v) (S n) h2 v2 ltac:(lia) ltac:(lia)) in H.
    destruct Nx as [I' Hq'].
    set (node := region_node b im kids (region_text b (region_src s n e))) in *.
    set (ve := pv_add node (PView rest (pv_out v) PMNormal)) in H.
    assert (Eve : vembed real ve
                  = temit (mk node)
                      (fst (vembed real (PView rest (pv_out v) (PMRegion b im kids n e ""))))
                      (snd (vembed real (PView rest (pv_out v) (PMRegion b im kids n e ""))))).
    { unfold ve. rewrite vembed_add. unfold vembed. cbn [pv_stk pv_out].
      rewrite temit_embed. f_equal. apply xinner_ext. intros acc.
      apply xsnoc_nonstr, vin_nonstr, region_node_nonstr. }
    destruct (vembed real (PView rest (pv_out v) (PMRegion b im kids n e ""))) as [fs top].
    cbn [fst snd] in Eve.
    destruct (temit (mk node) fs top) as [fs' top'].
    replace fs' with (fst (vembed real ve)) by (rewrite Eve; reflexivity).
    replace top' with (snd (vembed real ve)) by (rewrite Eve; reflexivity).
    apply (IH (S e) st' false ve h2 v2 Hm I' Hq' ltac:(lia) Hr).
    + unfold ve. rewrite (proj2 (pv_add_live _ _)). reflexivity.
    + unfold ve. rewrite (proj1 (pv_add_live _ _)). exact Hl'.
    + unfold ve. apply pv_add_normal. exact N'.
    + exact H.
  - (* a token of several bytes: its bytes, then the token after it *)
    assert (Ra : exists w, (forall s0, x <> Str s0) /\ e = pred (tok_end s n) /\ S n < tok_end s n
                 /\ pv_mode w = PMNormal /\ pv_live w = pv_live v /\ frames_normal w
                 /\ is_hard t = false /\ pstep s n h t v = pv_setmode (PMAtom x e) w).
    { destruct t as [c| |k mr op cl|oi|b0 rg0|c|ws|ws|vp vn vb vc vr|dk|asrc|sa|ab aa|sb sa'|nl|dn|hn];
        try (rewrite pstep_mode in Em' by (assumption || discriminate); discriminate);
        try (cbn [pstep pv_setmode pv_mode] in Em'; discriminate Em');
        try (destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|] eqn:Hc;
             [rewrite (pstep_span_found s n h _ _ v content rest Hc) in Em'
             |rewrite (pstep_span_none s n h _ _ v Hc), (proj2 (pv_add_live _ _)), Em in Em'];
             discriminate Em').
      - destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|] eqn:Hc.
        2: { rewrite pstep_close_none in Em' by exact Hc.
             rewrite (proj2 (pv_add_live _ _)), Em in Em'. discriminate. }
        rewrite (pstep_close_found s n h b0 rg0 v content rest Hc) in Em'.
        discriminate Em'.
      - unfold pstep in Em' |- *. destruct (Nat.ltb (S n) (tok_end s n)) eqn:L.
        + cbn [pv_setmode pv_mode] in Em'. injection Em' as <- <-.
          apply Nat.ltb_lt in L. exists (add_text (chars dollar (vp - 2)) v).
          split; [apply vin_nonstr; intros s0; apply verb_node_nonstr|].
          split; [reflexivity|]. split; [exact L|].
          split; [unfold add_text; destruct (nonempty_str (chars dollar (vp - 2)));
                  [rewrite (proj2 (pv_add_live _ _))|]; exact Em|].
          split; [unfold add_text; destruct (nonempty_str (chars dollar (vp - 2)));
                  [rewrite (proj1 (pv_add_live _ _))|]; reflexivity|].
          split; [unfold add_text; destruct (nonempty_str (chars dollar (vp - 2)));
                  [apply pv_add_normal|]; exact N|].
          split; reflexivity.
        + rewrite (proj2 (pv_add_live _ _)), (proj2 (add_text_live _ _)), Em in Em'. discriminate.
      - cbn [pstep pv_setmode pv_mode] in Em' |- *. injection Em' as <- <-.
        pose proof (tok_at_attr s n ab aa l Hat) as [El _].
        assert (Hend : tok_end s n = n + l) by (unfold tok_end; rewrite Hat; reflexivity).
        exists v. split; [discriminate|]. split; [reflexivity|]. split; [lia|].
        split; [exact Em|]. split; [reflexivity|]. split; [exact N|]. split; reflexivity.
      - cbn [pstep pv_setmode pv_mode] in Em' |- *. injection Em' as <- <-.
        pose proof (tok_at_note s n nl l Hat) as [El _].
        assert (Hend : tok_end s n = n + l) by (unfold tok_end; rewrite Hat; reflexivity).
        exists v. split; [discriminate|]. split; [reflexivity|]. split; [lia|].
        split; [exact Em|]. split; [reflexivity|]. split; [exact N|]. split; reflexivity. }
    destruct Ra as (w & Hx & -> & Hlt & Emw & Hlw & Nw & Hh & Ep). rewrite Hh in H |- *.
    assert (Hend : tok_end s n = n + l) by (unfold tok_end; rewrite Hat; reflexivity).
    rewrite Hend in Hlt, Ep. rewrite Ep in H, Hl', N' |- *.
    apply (atom_walk s _ (pred (n + l))
             (pv_setmode (PMAtom x (pred (n + l))) w) (S n) h2 v2 eq_refl
             ltac:(lia) ltac:(lia)) in H.
    replace (S (pred (n + l))) with (n + l) in H by lia.
    destruct Nx as [I' Hq'].
    set (ve := pv_add x (pv_setmode PMNormal (pv_setmode (PMAtom x (pred (n + l))) w))) in H.
    assert (Eve : vembed real ve
                  = tput (et x)
                      (fst (vembed real (pv_setmode (PMAtom x (pred (n + l))) w)))
                      (snd (vembed real (pv_setmode (PMAtom x (pred (n + l))) w)))).
    { unfold ve. rewrite vembed_add. unfold vembed. cbn [pv_stk pv_out pv_setmode].
      rewrite tput_embed. f_equal. apply xinner_ext. intros acc.
      apply xsnoc_nonstr, Hx. }
    unfold vafter. cbn [pv_mode pv_setmode].
    destruct (vembed real (pv_setmode (PMAtom x (pred (n + l))) w)) as [fs top].
    cbn [fst snd] in Eve.
    destruct (tput (et x) fs top) as [fs' top'].
    replace fs' with (fst (vembed real ve)) by (rewrite Eve; reflexivity).
    replace top' with (snd (vembed real ve)) by (rewrite Eve; reflexivity).
    apply (IH (n + l) st' false ve h2 v2 Hm I' Hq' ltac:(lia) Hr).
    + unfold ve. rewrite (proj2 (pv_add_live _ _)). reflexivity.
    + unfold ve. rewrite (proj1 (pv_add_live _ _)). exact Hl'.
    + unfold ve. apply pv_add_normal. exact N'.
    + exact H.
  - (* a span: its spec's bytes, then the token after it *)
    assert (Rs : exists sb content rest,
              t = TSpan sb sat /\ sk = vres content /\ se = n + S (S (String.length sb))
              /\ pstep s n h t v = PView rest (pv_out v) (PMSpan im sk sat se)).
    { destruct t as [c| |k mr op cl|oi|b0 rg0|c|ws|ws|vp vn vb vc vr|dk|asrc|sa|ab aa|sb sa'|nl|dn|hn];
        try (rewrite pstep_mode in Em' by (assumption || discriminate); discriminate).
      - destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|] eqn:Hc.
        2: { rewrite pstep_close_none in Em' by exact Hc.
             rewrite (proj2 (pv_add_live _ _)), Em in Em'. discriminate. }
        rewrite (pstep_close_found s n h b0 rg0 v content rest Hc) in Em'.
        discriminate Em'.
      - unfold pstep in Em'. destruct (Nat.ltb (S n) (tok_end s n));
          [discriminate Em'|].
        rewrite (proj2 (pv_add_live _ _)), (proj2 (add_text_live _ _)), Em in Em'. discriminate.
      - destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|] eqn:Hc.
        2: { rewrite (pstep_span_none s n h _ _ v Hc), (proj2 (pv_add_live _ _)), Em in Em'.
             discriminate. }
        rewrite (pstep_span_found s n h _ _ v content rest Hc) in Em' |- *.
        injection Em' as <- <- <- <-. exists sb, content, rest. auto. }
    destruct Rs as (sb & content & rest & -> & -> & -> & Ep).
    pose proof (tok_at_span s n sb sat l Hat) as [-> [r Er]].
    assert (Hse : n + S (S (String.length sb)) < String.length s).
    { pose proof (sdrop_length n s) as L. rewrite Er in L. cbn [String.length] in L.
      rewrite length_append in L. cbn [String.length] in L. lia. }
    rewrite Ep in H, Hl', N' |- *. cbn [is_hard] in *.
    set (vs := PView rest (pv_out v)
                 (PMSpan im (vres content) sat (n + S (S (String.length sb))))) in *.
    apply (span_walk s _ _ _ _ vs (S n) h2 v2 eq_refl ltac:(lia) Hse) in H.
    destruct Nx as [I' Hq'].
    set (node := Node NoPos sat (Span EmptyString (vres content))) in *.
    set (vb := if im then pv_add (Str (one bang)) (pv_setmode PMNormal vs)
               else pv_setmode PMNormal vs).
    change (let v' := pv_setmode PMNormal vs in if im then pv_add (Str (one bang)) v' else v')
      with vb in H.
    assert (Evb : (if im then temit_str (one bang) (fst (vembed real vs)) (snd (vembed real vs))
                   else vembed real vs) = vembed real vb).
    { unfold vb. destruct im; [|reflexivity]. rewrite vembed_add. unfold vembed.
      cbn [pv_stk pv_out pv_setmode vs]. apply temit_str_embed. }
    set (ve := pv_add (vof node) vb) in H.
    assert (Eve : vembed real ve = temit node (fst (vembed real vb)) (snd (vembed real vb))).
    { unfold ve. rewrite vembed_add. unfold vembed.
      rewrite (temit_vof node _ eq_refl). f_equal. apply xinner_ext. intros acc.
      apply xsnoc_nonstr, vof_nonstr. intros p s0 E. discriminate E. }
    destruct (vembed real vs) as [fs top] eqn:Evs. cbn [fst snd] in Evb.
    replace (if im then temit_str (one bang) fs top else (fs, top)) with (vembed real vb)
      by (rewrite <- Evb; destruct im; reflexivity).
    destruct (vembed real vb) as [fs1 top1]. cbn [fst snd] in Eve.
    destruct (temit node fs1 top1) as [fs' top'].
    replace fs' with (fst (vembed real ve)) by (rewrite Eve; reflexivity).
    replace top' with (snd (vembed real ve)) by (rewrite Eve; reflexivity).
    apply (IH (S (n + S (S (String.length sb)))) st' false ve h2 v2 Hm I' Hq' ltac:(lia) Hr).
    + unfold ve, vb. rewrite (proj2 (pv_add_live _ _)).
      destruct im; [rewrite (proj2 (pv_add_live _ _))|]; reflexivity.
    + unfold ve, vb. rewrite (proj1 (pv_add_live _ _)).
      destruct im; [rewrite (proj1 (pv_add_live _ _))|]; exact Hl'.
    + unfold ve, vb. apply pv_add_normal. destruct im; [apply pv_add_normal|]; exact N'.
    + exact H.
Qed.

Theorem tree_of_pruns : forall s h2 v2,
  pruns s 0 false pv0 (String.length s) h2 v2 ->
  tree_of s (fst (ref_read s)) = vres (pflatten v2).
Proof.
  intros s h2 v2 H. unfold tree_of.
  pose proof (walk_tree s _ (S (String.length s)) 0 rstart false pv0 h2 v2 eq_refl
                (rinv_start s) (chain_start _ _) ltac:(lia) eq_refl eq_refl eq_refl
                (Forall_nil _) H) as W.
  unfold vres. rewrite <- W. reflexivity.
Qed.

(*
The scanner
===========

Between units the scanner's state is a text-mode state or a region's.
In text mode its scope stack is the view: a frame per open opener,
holding what the view holds.  The one difference is
text not yet flushed, which the view has already added to its innermost
content; the scanner's innermost content never ends in text, so the two
meet by consing it back.
 *)

Definition eo (x : vitem) : oitem :=
  match x with
  | VIn x => OIn (mk x)
  | VAt kv a x => OIn (Node NoPos (kv :: a) x)
  | VMark a => OMark a null_span None
  end.

Definition oframe (f : pframe) : frame :=
  match f with
  | PF p (KDelim k mr, b) c =>
      Frame (FKDelim k b) mr null_span (map eo c)
  | PF _ (KBracket, im) c => Frame (FKBracket im) false null_span (map eo c)
  end.

Definition oview (v : pview) : ostate :=
  OState (map eo (pv_out v)) (map oframe (pv_stk v)) None.

(* The view has no named bracket: `:` is outside the alphabet. *)
Lemma tag_close_oview : forall v, tag_close (oview v) = None.
Proof.
  intros v. unfold tag_close, oview. cbn [os_stk].
  assert (H : forall stk pend, tag_close_go pend (map oframe stk) = None).
  { induction stk as [|f stk IH]; intros pend; [reflexivity|].
    destruct f as [p [[k mr|] im'] c]; cbn [map oframe tag_close_go fr_kind];
      [apply IH|reflexivity]. }
  rewrite H. reflexivity.
Qed.

Definition top_of (v : pview) : list vitem :=
  match pv_stk v with [] => pv_out v | f :: _ => fcontent f end.

Definition starts_text (l : list vitem) : bool :=
  match l with VIn (Str _) :: _ => true | _ => false end.

Definition sim (v : pview) (txt : string) (o : ostate) : Prop :=
  exists v0, o = oview v0 /\ starts_text (top_of v0) = false
                /\ v = add_text txt v0.

(*
The view, embedded
------------------
*)

Local Lemma osnoc_embed : forall (x : vitem) b,
  osnoc (eo x) (map eo b) = map eo (xsnoc x b).
Proof.
  intros x b. destruct b as [|y b]; [reflexivity|].
  destruct (str_view y) as [[t ->]|Hy].
  - destruct (str_view x) as [[s ->]|Hx]; [reflexivity|].
    rewrite (xsnoc_nonstr x _ Hx).
    dv x; [destruct (Hx _ eq_refl)|..]; reflexivity.
  - destruct (str_view x) as [[s ->]|Hx].
    + rewrite (xsnoc_str_nonstr s y b Hy).
      dv y; [destruct (Hy _ eq_refl)|..]; reflexivity.
    + rewrite (xsnoc_nonstr x _ Hx).
      dv y; [destruct (Hy _ eq_refl)|..]; reflexivity.
Qed.

Local Lemma oapp_embed : forall a b,
  oapp (map eo a) (map eo b) = map eo (xapp a b).
Proof.
  induction a as [|x a IH]; intros b; [reflexivity|].
  destruct a as [|y r]; [apply osnoc_embed|].
  change (map eo (x :: y :: r))
    with (eo x :: eo y :: map eo r).
  rewrite oapp_cons2.
  change (eo y :: map eo r) with (map eo (y :: r)).
  rewrite IH. reflexivity.
Qed.

Local Lemma fr_lit_oframe : forall f, fr_lit (oframe f) = mk (flit f).
Proof.
  intros [p [[k mr|] im'] c];
    unfold fr_lit, oframe, fr_src; cbn [fr_kind fr_marked flit lit]; reflexivity.
Qed.

Local Lemma oflatten_embed : forall stk pend out,
  oflatten (map eo pend) (map oframe stk) (map eo out)
  = map eo (pflatten_go pend stk out).
Proof.
  induction stk as [|f stk IH]; intros pend out;
    cbn [map oflatten pflatten_go]; [apply oapp_embed|].
  rewrite fr_lit_oframe.
  replace (fr_out (oframe f)) with (map eo (fcontent f))
    by (destruct f as [p [[k mr|] im'] c]; reflexivity).
  rewrite oapp_embed.
  change [OIn (mk (flit f))] with (map eo [VIn (flit f)]).
  rewrite oapp_embed. apply IH.
Qed.

Local Lemma fr_out_oframe : forall f, fr_out (oframe f) = map eo (fcontent f).
Proof. intros [p [[k mr|] im'] c]; reflexivity. Qed.

Local Lemma oclose_go_embed : forall k mr pend stk,
  oclose_go k mr (map eo pend) (map oframe stk)
  = match pclose_go (KDelim k mr) pend stk with
    | Some (content, rest) =>
        if nonempty content
        then Some (map eo content, null_span, map oframe rest)
        else None
    | None => None
    end.
Proof.
  intros k mr pend stk. revert pend.
  induction stk as [|f stk IH]; intros pend; [reflexivity|].
  cbn [map oclose_go]. rewrite fr_out_oframe, oapp_embed.
  rewrite fr_lit_oframe.
  change [OIn (mk (flit f))] with (map eo [VIn (flit f)]).
  destruct f as [p [[k' m'|] im'] c]; cbn [pclose_go key_eq fst snd fcontent flit].
  - unfold dmatch. cbn [oframe fr_kind fr_marked fr_open].
    destruct (dstyle_eq k k' && Bool.eqb mr m')%bool;
      [destruct (xapp pend c); reflexivity|].
    rewrite oapp_embed. apply IH.
  - unfold dmatch. cbn [oframe fr_kind].
    rewrite oapp_embed. apply IH.
Qed.

(* The scanner settles a scope's content as `resolve` does. *)
Local Lemma isnoc_attr : forall q kv b y l,
  isnoc (Node q (kv :: b) y) l = Node q (kv :: b) y :: l.
Proof. intros q kv b y [|[? [|] []] l0]; reflexivity. Qed.

Local Lemma oword_split_embed : forall out,
  Forall bare out -> normal (map vof out) -> oword_split None out = word_split out.
Proof.
  induction out as [|[p a v] rest IH]; intros B N; [reflexivity|].
  pose proof (proj1 (Forall_cons_iff _ _ _) B) as [Bp Br]. cbn in Bp. subst p.
  specialize (IH Br (normal_tail _ _ N)).
  destruct a as [|kv a]; [|destruct v; reflexivity].
  destruct v; try reflexivity; cbn [oword_split word_split]; rewrite IH.
  - destruct (last_ws_split s) as [pre w].
    destruct (nonempty_str w); [|reflexivity].
    destruct (nonempty_str pre); cbn [split_text_pos].
    + f_equal. destruct rest as [|[q [|kw b] y] rest]; try reflexivity.
      destruct y; try reflexivity. destruct N as [[N|N] _]; discriminate N.
    + destruct (word_split rest) as [[|x ws] before]; reflexivity.
  - reflexivity.
Qed.

Local Lemma oattach_embed : forall a sp out,
  Forall bare out -> normal (map vof out) -> oattach_list a sp None out = attach a out.
Proof.
  intros a sp out B N. unfold oattach_list, attach.
  pose proof (proj1 (word_split_ok out B N)) as Bw.
  rewrite (oword_split_embed out B N).
  destruct (word_split out) as [[|y ws] before]; cbn [fst] in Bw.
  - destruct out as [|[p a' v] rest]; [reflexivity|].
    destruct a' as [|kv a']; destruct v; reflexivity.
  - destruct a as [|x a]; [reflexivity|].
    unfold add_inline_role, add_roles. cbn [pos_records semantic_pos].
    destruct ws as [|z ws]; [destruct y; apply isnoc_attr|].
    (* a span of several pieces: its range is no range, as theirs are *)
    assert (L : forall l d, Forall bare l -> bare d -> bare (last l d)).
    { induction l as [|u l IHl]; intros d Hl Hd; [exact Hd|].
      apply Forall_cons_iff in Hl as [Hu Hl].
      destruct l as [|v l]; [exact Hu|]. apply IHl; assumption. }
    destruct y as [q b x0].
    pose proof (proj1 (Forall_cons_iff _ _ _) Bw) as [Bq _]. cbn in Bq. subst q.
    pose proof (L (Node NoPos b x0 :: z :: ws) (Node NoPos [] SoftBreak) Bw eq_refl) as Hl.
    cbn [oword_node word_node].
    destruct (last (Node NoPos b x0 :: z :: ws) (Node NoPos [] SoftBreak)) as [p' c' z'].
    cbn in Hl. subst p'. apply isnoc_attr.
Qed.

Local Lemma oresolve_go_embed : forall c, normal c ->
  oresolve_go (map eo c)
  = (vsettle c, match c with VMark _ :: _ => istarts_str (vsettle c) | _ => false end).
Proof.
  induction c as [|x c IH]; intros N; [reflexivity|].
  pose proof (normal_tail _ _ N) as Nc. specialize (IH Nc).
  destruct (resolve_rev_ok (map et c) (et_bare c)) as [Bo No]. fold (vsettle c) in Bo, No.
  assert (Node_ : forall n, (forall p s, n <> Node p [] (Str s)) ->
            (let '(out, m) := oresolve_go (map eo c) in
             ((if m then isnoc n out else n :: out), false))
            = (push n (vsettle c), false)).
  { intros n Hn. rewrite IH.
    assert (E1 : forall l, isnoc n l = n :: l).
    { intros l. destruct n as [p [|kv a] y]; [|apply isnoc_attr].
      destruct y; [destruct (Hn p s eq_refl)|..]; destruct l as [|[? [|] []] l0]; reflexivity. }
    assert (E2 : push n (vsettle c) = n :: vsettle c).
    { destruct n as [p [|kv a] y]; [|reflexivity].
      destruct y; [destruct (Hn p s eq_refl)|..]; reflexivity. }
    rewrite E1, E2.
    destruct (match c with VMark _ :: _ => istarts_str (vsettle c) | _ => false end);
      reflexivity. }
  destruct x as [x|kv a x|a]; cbn [map eo oresolve_go].
  - destruct x; try (apply Node_; intros p s0 E; discriminate E).
    rewrite IH. change (vsettle (VIn (Str s) :: c)) with (str_snoc s (vsettle c)). f_equal.
    destruct c as [|y c]; [reflexivity|].
    destruct y as [y|kv a y|a].
    + destruct N as [[N|N] _]; [discriminate N|].
      change (vsettle (VIn y :: c)) with (push (mk y) (vsettle c)).
      destruct y; try discriminate N; reflexivity.
    + reflexivity.
    + destruct (vsettle (VMark a :: c)) as [|[p [|kv b] y] r]; try reflexivity.
      destruct y; try reflexivity. cbn. destruct p; reflexivity.
  - apply Node_. intros p s0 E; discriminate E.
  - rewrite IH. rewrite (oattach_embed a null_span _ Bo No). reflexivity.
Qed.

Local Lemma oresolve_embed : forall c, normal c -> oresolve (map eo c) = vsettle c.
Proof. intros c N. unfold oresolve. rewrite (oresolve_go_embed c N). reflexivity. Qed.

Local Lemma bclose_embed : forall out stk,
  Forall (fun f => normal (fcontent f)) stk ->
  bclose (OState (map eo out) (map oframe stk) None)
  = match pclose_go KBracket [] stk with
    | Some (content, rest) =>
        Some (vres content, pclose_im stk, null_span,
              OState (map eo out) (map oframe rest) None)
    | None => None
    end.
Proof.
  intros out stk Ns. unfold bclose. cbn [os_stk os_out os_word_start].
  change (@nil oitem) with (map eo (@nil vitem)).
  assert (G : forall stk0 pend,
            bclose_go (map eo pend) (map oframe stk0)
            = match pclose_go KBracket pend stk0 with
              | Some (content, rest) =>
                  Some (map eo content, pclose_im stk0, null_span, map oframe rest)
              | None => None
              end).
  { induction stk0 as [|f stk0 IH]; intros pend; [reflexivity|].
    cbn [map bclose_go]. rewrite fr_out_oframe, oapp_embed.
    rewrite fr_lit_oframe.
    change [OIn (mk (flit f))] with (map eo [VIn (flit f)]).
    destruct f as [p [[k' m'|] im'] c];
      cbn [pclose_go pclose_im key_eq fst snd fcontent flit oframe fr_kind fr_open].
    - rewrite oapp_embed. apply IH.
    - reflexivity. }
  rewrite (G stk []). destruct (pclose_go KBracket [] stk) as [[content rest]|] eqn:Hc; [|reflexivity].
  rewrite (oresolve_embed content (proj1 (pclose_go_normal _ stk [] content rest Ns Logic.I Hc))).
  reflexivity.
Qed.

Local Lemma flush_view : forall txt v0,
  starts_text (top_of v0) = false ->
  flush_text txt (oview v0) = oview (add_text txt v0).
Proof.
  intros txt [stk out md] H. unfold flush_text, flush_text_at, add_text.
  destruct (nonempty_str txt); [|reflexivity].
  assert (X : forall l, starts_text l = false -> xsnoc (Str txt) l = VIn (Str txt) :: l)
    by (intros [|[[]| |] l] Hl; try reflexivity; discriminate).
  unfold pv_add, oview, oemit.
  cbn [pv_stk pv_out os_stk os_out os_word_start] in *.
  destruct stk as [|f rest]; cbn [top_of pv_stk pv_out] in H;
    [rewrite (X _ H); reflexivity|].
  cbn [map]. rewrite (X _ H).
  destruct f as [p [[k mr|] im'] c]; reflexivity.
Qed.

Local Lemma pflatten_go_normal : forall stk pend bottom,
  Forall (fun f => normal (fcontent f)) stk -> normal pend -> normal bottom ->
  normal (pflatten_go pend stk bottom).
Proof.
  induction stk as [|f stk IH]; intros pend bottom N Np Nb; cbn [pflatten_go];
    [apply normal_xapp; assumption|].
  apply Forall_cons_iff in N as [Nf N]. apply IH; [exact N| |exact Nb].
  apply normal_xapp; [apply normal_xapp; assumption|exact Logic.I].
Qed.

Local Lemma ifinish_view : forall txt prev v0,
  starts_text (top_of v0) = false ->
  normal (pflatten_go [] (pv_stk (add_text txt v0)) (pv_out (add_text txt v0))) ->
  ifinish (IText false txt prev (oview v0))
  = vres (pflatten_go [] (pv_stk (add_text txt v0)) (pv_out (add_text txt v0))).
Proof.
  intros txt prev v0 H Nf.
  unfold ifinish, ifinish_rev, ofinish. rewrite oitems_of_spec.
  cbn [ifinish_ostate ifinish_ostate_flat iresolve].
  change (tval txt) with txt.
  change (@flush_text_at semantic_pos semantic_inline_cursor txt (oview v0))
    with (flush_text txt (oview v0)).
  rewrite (flush_view txt v0 H).
  unfold oview at 1 2. cbn [os_stk os_out].
  change (@nil oitem) with (map eo (@nil vitem)).
  rewrite oflatten_embed, (oresolve_embed _ Nf). reflexivity.
Qed.

(*
The view's invariant
--------------------

The stack is ordered, its positions are before `n` and its openers'
tokens end by `n`; and outside a region the innermost frame is empty
exactly when its opener's token ends at `n`. *)

Definition fend (ps : string) (f : pframe) : nat :=
  match f with PF p _ _ => tok_end ps p end.

(* A frame's token ends before any frame above it opens. *)
Definition stk_order (ps : string) (stk : list pframe) : Prop :=
  StronglySorted (fun a b => fend ps b <= fst (fitem a)) stk.

Definition pv_ok (ps : string) (n : nat) (v : pview) : Prop :=
  ldesc (pv_live v) /\ (forall x, In x (pv_live v) -> fst x < n)
  /\ (forall p k c, In (PF p k c) (pv_stk v) -> tok_end ps p <= n)
  /\ stk_order ps (pv_stk v)
  /\ (forall p k c, In (PF p k c) (pv_stk v) -> p < tok_end ps p)
  /\ match pv_mode v, pv_stk v with
     | PMNormal, PF p _ c :: _ => c = [] <-> tok_end ps p = n
     | _, _ => True
     end.

Local Lemma xsnoc_nonempty : forall x l, xsnoc x l <> [].
Proof.
  intros x [|y l]; unfold xsnoc; [discriminate|].
  destruct y as [[]| |], x as [[]| |]; discriminate.
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
  destruct f as [q k' c']; cbn [fset] in E.
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
  ldesc (pv_live v) -> (forall y, In y (pv_live v) -> fst y < n) ->
  (forall p k c, In (PF p k c) (pv_stk v) -> tok_end ps p <= n) ->
  stk_order ps (pv_stk v) ->
  (forall p k c, In (PF p k c) (pv_stk v) -> p < tok_end ps p) ->
  n < n' -> pv_ok ps n' (pv_add x v).
Proof.
  intros ps n n' x v D Bd Be So Bt Hn. destruct (pv_add_live x v) as [E1 E2].
  split; [rewrite E1; exact D|].
  split; [intros y H; rewrite E1 in H; specialize (Bd y H); lia|].
  split; [intros p k c H; destruct (in_stk_add x v p k c H) as [c' H']; specialize (Be p k c' H'); lia|].
  split; [apply stk_order_add, So|].
  split; [intros p k c H; destruct (in_stk_add x v p k c H) as [c' H']; exact (Bt p k c' H')|].
  rewrite E2. unfold pv_add. destruct (pv_stk v) as [|f rest] eqn:E; [destruct (pv_mode v); exact Logic.I|].
  cbn [pv_stk pv_mode]. destruct (pv_mode v); try exact Logic.I.
  destruct f as [p k c]; cbn [fset fcontent].
  assert (tok_end ps p <= n) by (apply (Be p k c); left; reflexivity).
  split; [intros Hc; destruct (xsnoc_nonempty x c Hc)|lia].
Qed.

Local Lemma pv_ok_add_items : forall ps n n' xs v, xs <> [] ->
  ldesc (pv_live v) -> (forall y, In y (pv_live v) -> fst y < n) ->
  (forall p k c, In (PF p k c) (pv_stk v) -> tok_end ps p <= n) ->
  stk_order ps (pv_stk v) ->
  (forall p k c, In (PF p k c) (pv_stk v) -> p < tok_end ps p) ->
  n < n' -> pv_ok ps n' (pv_add_items xs v).
Proof.
  intros ps n n'. induction xs as [|x xs IH]; intros v Hne D Bd Be So Bt Hn;
    [contradiction|].
  destruct xs as [|y xs]; [apply (pv_ok_add ps n); assumption|].
  cbn [pv_add_items fold_left]. fold (pv_add_items (y :: xs) (pv_add (VIn x) v)).
  destruct (pv_add_live x v) as [E1 _].
  apply IH; [discriminate|rewrite E1; exact D|intros z H; rewrite E1 in H; exact (Bd z H)
            | | | |exact Hn].
  - intros p k c H. destruct (in_stk_add _ _ p k c H) as [c' H']. exact (Be p k c' H').
  - apply stk_order_add, So.
  - intros p k c H. destruct (in_stk_add _ _ p k c H) as [c' H']. exact (Bt p k c' H').
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
  ldesc (map fitem rest) /\ (forall y, In y (map fitem rest) -> fst y < p)
  /\ (forall q k c, In (PF q k c) rest -> tok_end ps q <= n)
  /\ stk_order ps rest
  /\ (forall q k c, In (PF q k c) rest -> q < tok_end ps q) /\ p < n.
Proof.
  intros ps n v K p below content rest (D & Bd & Be & So & Bt & _) P Hc.
  unfold pv_live in P, D, Bd.
  destruct (pick_split K _ p below P) as (above & im0 & c & rest' & E & F & Hb).
  rewrite E in Hc, D, Bd, Be, So, Bt.
  destruct (pclose_split K im0 above p c rest' [] F) as [content' Hc'].
  rewrite Hc in Hc'. injection Hc' as <- <-.
  assert (Hpn : p < n).
  { apply (Bd (p, K)). rewrite map_app. apply in_or_app. right. left. reflexivity. }
  split; [exact (ldesc_below above _ rest D)|].
  split; [|split; [|split; [|split; [|exact Hpn]]]].
  - intros y Hy. rewrite map_app in D. cbn [map] in D.
    clear -D Hy. induction above as [|g above IH]; cbn [app] in D.
    + apply StronglySorted_inv in D as [_ F]. rewrite Forall_forall in F. exact (F y Hy).
    + apply StronglySorted_inv in D as [D _]. exact (IH D).
  - intros q k c' H. apply (Be q k c'). apply in_or_app. right. right. exact H.
  - clear -So. induction above as [|g above IH]; cbn [app] in So.
    + apply StronglySorted_inv in So as [So _]. exact So.
    + apply StronglySorted_inv in So as [So _]. exact (IH So).
  - intros q k c' H. apply (Bt q k c'). apply in_or_app. right. right. exact H.
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
  destruct f as [q k' c']; cbn [fset] in E.
  injection E as -> -> _. exists c'. left. reflexivity.
Qed.

(* Everything on the stack ends by `n`. *)
Local Lemma fend_le : forall ps n v f,
  (forall x, In x (pv_live v) -> fst x < n) ->
  (forall p k c, In (PF p k c) (pv_stk v) -> tok_end ps p <= n) ->
  In f (pv_stk v) -> fend ps f <= n.
Proof.
  intros ps n v [p k c] Bd Be H; cbn [fend]. exact (Be p k c H).
Qed.

Local Lemma pv_ok_step : forall ps n h t l v,
  pv_ok ps n v -> pv_mode v = PMNormal -> tok_at ps n = Some (t, l) ->
  (t = TBreak -> h = true -> top_filled v) ->
  pv_ok ps (n + l) (pstep ps n h t v).
Proof.
  intros ps n h t l v Ok Em Ht Hh. pose proof Ok as (D & Bd & Be & So & Bt & Inn).
  pose proof (tok_at_len ps n t l Ht) as Hl.
  assert (Hend : tok_end ps n = n + l) by (unfold tok_end; rewrite Ht; reflexivity).
  assert (Add : forall x, pv_ok ps (n + l) (pv_add x v))
    by (intros x; apply (pv_ok_add ps n); [exact D|exact Bd|exact Be|exact So|exact Bt|lia]).
  assert (Open : forall k op txt, pv_ok ps (n + l) (popen n k op txt v)).
  { intros k [|] txt; [|apply Add].
    unfold popen. split; [|split; [|split; [|split; [|split]]]].
    - unfold pv_live. cbn [pv_stk map]. constructor; [exact D|].
      apply Forall_forall. intros y H. exact (Bd y H).
    - unfold pv_live. cbn [pv_stk map fitem fst].
      intros y [<-|H]; [cbn; lia|]. specialize (Bd y H). lia.
    - cbn [pv_stk]. intros p k' c [E|H]; [injection E as <- _ _; lia|].
      specialize (Be p k' c H). lia.
    - constructor; [exact So|]. apply Forall_forall. intros f Hf. cbn [fitem fst].
      exact (fend_le ps n v f Bd Be Hf).
    - cbn [pv_stk]. intros p k' c [E|H]; [injection E as <- _ _; lia|exact (Bt p k' c H)].
    - cbn [pv_stk pv_mode]. rewrite Em. split; [intros _; exact Hend|reflexivity]. }
  unfold pstep.
  destruct t as [c| |k mr op cl|oi|b rg|c|ws|ws|vp vn vb vc vr|dk|asrc|sa|ab aa|sb sa'|nl|dn|hn]; try apply Add.
  - (* a break after a hard break adds nothing, to a frame already filled *)
    destruct h; [|apply Add].
    specialize (Hh eq_refl eq_refl). unfold top_filled in Hh. rewrite Em in Hh.
    split; [exact D|]. split; [intros y H; specialize (Bd y H); lia|].
    split; [intros p k c H; specialize (Be p k c H); lia|].
    split; [exact So|]. split; [exact Bt|]. rewrite Em.
    destruct (pv_stk v) as [|[p k c] rest] eqn:Es; try exact Logic.I.
    assert (Hp : tok_end ps p <= n) by (apply (Be p k c); left; reflexivity).
    split; [intros Hc; contradiction|lia].
  - destruct (if cl then pick (KDelim k mr) (pv_live v) else PNone) as [p below|] eqn:P;
      [|apply Open].
    destruct (Nat.ltb (tok_end ps p) n); [|apply Open].
    destruct cl; [|discriminate].
    destruct (pclose_go (KDelim k mr) [] (pv_stk v)) as [[content rest]|] eqn:Hc;
      [|destruct (pclose_found _ _ _ _ P) as (? & ? & E & _); congruence].
    destruct (pv_ok_close ps n v _ p below content rest Ok P Hc) as (D' & Bd' & Be' & So' & Bt' & Hpn).
    apply (pv_ok_add ps n _ _ (PView rest (pv_out v) PMNormal)); unfold pv_live; cbn [pv_stk].
    + exact D'.
    + intros y H. specialize (Bd' y H). lia.
    + exact Be'.
    + exact So'.
    + exact Bt'.
    + lia.
  - apply Open.
  - destruct (pick KBracket (pv_live v)) as [p below|] eqn:P;
      destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|] eqn:Hc;
      try apply Add.
    destruct (pv_ok_close ps n v _ p below content rest Ok P Hc) as (D' & Bd' & Be' & So' & Bt' & Hpn).
    split; [exact D'|]. split; [intros y H; specialize (Bd' y H); cbn; lia|].
    split; [intros q k c H; specialize (Be' q k c H); lia|].
    split; [exact So'|]. split; [exact Bt'|exact Logic.I].
  - destruct (nbsp_rest ws) as [r|]; [|apply Add].
    destruct (nonempty_str r); [|apply Add].
    destruct (pv_add_live NonBreakingSpace v) as [E1 _].
    apply (pv_ok_add ps n); [rewrite E1; exact D|rewrite E1; exact Bd| |apply stk_order_add, So| |lia];
      intros p k c H; destruct (in_stk_add _ _ p k c H) as [c' H'];
      first [exact (Be p k c' H')|exact (Bt p k c' H')].
  - destruct (pv_trim_live v) as [E1 _].
    apply (pv_ok_add ps n); [rewrite E1; exact D|rewrite E1; exact Bd| |apply stk_order_trim, So| |lia];
      intros p k c H; destruct (in_stk_trim _ p k c H) as [c' H'];
      first [exact (Be p k c' H')|exact (Bt p k c' H')].
  - set (w := add_text (chars dollar (vp - 2)) v).
    assert (Fw : ldesc (pv_live w) /\ (forall y, In y (pv_live w) -> fst y < n)
                 /\ (forall p k c, In (PF p k c) (pv_stk w) -> tok_end ps p <= n)
                 /\ stk_order ps (pv_stk w)
                 /\ (forall p k c, In (PF p k c) (pv_stk w) -> p < tok_end ps p)).
    { unfold w, add_text.
      destruct (nonempty_str _); [|exact (conj D (conj Bd (conj Be (conj So Bt))))].
      destruct (pv_add_live (Str (chars dollar (vp - 2))) v) as [E1 _]. rewrite E1.
      split; [exact D|]. split; [exact Bd|].
      split; [intros p k c H; destruct (in_stk_add _ _ p k c H) as [c' H']; exact (Be p k c' H')|].
      split; [apply stk_order_add, So|].
      intros p k c H; destruct (in_stk_add _ _ p k c H) as [c' H']; exact (Bt p k c' H'). }
    destruct Fw as (Dw & Bdw & Bew & Sow & Btw).
    destruct (Nat.ltb _ _).
    + split; [exact Dw|]. split; [intros y H; specialize (Bdw y H); lia|].
      split; [intros p k c H; specialize (Bew p k c H); lia|].
      split; [exact Sow|]. split; [exact Btw|exact Logic.I].
    + apply (pv_ok_add ps n); [exact Dw|exact Bdw|exact Bew|exact Sow|exact Btw|lia].
  - split; [exact D|]. split; [intros y H; specialize (Bd y H); lia|].
    split; [intros p k c H; specialize (Be p k c H); lia|].
    split; [exact So|]. split; [exact Bt|exact Logic.I].
  - destruct (pick KBracket (pv_live v)) as [p below|] eqn:P;
      destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|] eqn:Hc;
      try apply Add.
    destruct (pv_ok_close ps n v _ p below content rest Ok P Hc)
      as (D' & Bd' & Be' & So' & Bt' & Hpn).
    split; [exact D'|]. split; [intros y H; specialize (Bd' y H); cbn; lia|].
    split; [intros q k c H; specialize (Be' q k c H); lia|].
    split; [exact So'|]. split; [exact Bt'|exact Logic.I].
  - split; [exact D|]. split; [intros y H; specialize (Bd y H); lia|].
    split; [intros p k c H; specialize (Be p k c H); lia|].
    split; [exact So|]. split; [exact Bt|exact Logic.I].
  - (* a run of periods *)
    pose proof (tok_at_dots ps n dn l Ht) as El.
    apply (pv_ok_add_items ps n); [|exact D|exact Bd|exact Be|exact So|exact Bt|lia].
    apply dots_items_nonempty. lia.
  - (* a run of hyphens *)
    pose proof (tok_at_dash ps n hn l Ht) as El.
    apply (pv_ok_add_items ps n); [|exact D|exact Bd|exact Be|exact So|exact Bt|lia].
    apply dash_items_nonempty. lia.
Qed.

Local Lemma pv_ok_byte : forall ps n c v,
  pv_ok ps n v -> pv_mode v <> PMNormal -> pv_ok ps (S n) (pbyte n c v).
Proof.
  intros ps n c v Ok Em. pose proof Ok as (D & Bd & Be & So & Bt & _).
  assert (Keep : pv_mode v <> PMNormal -> pv_ok ps (S n) v).
  { intros E. unfold pv_ok. split; [exact D|]. split; [intros y H; specialize (Bd y H); lia|].
    split; [intros p k c' H; specialize (Be p k c' H); lia|].
    split; [exact So|]. split; [exact Bt|].
    destruct (pv_mode v); [contradiction| | |]; destruct (pv_stk v) as [|[] ?]; exact Logic.I. }
  unfold pbyte. destruct (pv_mode v) as [|b im kids d e txt|x e|im sk sat se] eqn:Ev; [contradiction| | |].
  - destruct (Nat.eqb n e).
    + apply (pv_ok_add ps n); [exact D|exact Bd|exact Be|exact So|exact Bt|lia].
    + split; [exact D|]. split; [intros y H; specialize (Bd y H); lia|].
      split; [intros p k c' H; specialize (Be p k c' H); lia|].
      split; [exact So|]. split; [exact Bt|exact Logic.I].
  - destruct (Nat.eqb n e).
    + apply (pv_ok_add ps n); [exact D|exact Bd|exact Be|exact So|exact Bt|lia].
    + apply Keep. discriminate.
  - destruct (Nat.eqb n se); [|apply Keep; discriminate].
    destruct im; [|apply (pv_ok_add ps n); [exact D|exact Bd|exact Be|exact So|exact Bt|lia]].
    destruct (pv_add_live (Str (one bang)) (pv_setmode PMNormal v)) as [E1 _].
    apply (pv_ok_add ps n); [rewrite E1; exact D|rewrite E1; exact Bd| |apply stk_order_add, So| |lia];
      intros p k c' H; destruct (in_stk_add _ _ p k c' H) as [c'' H'];
      first [exact (Be p k c'' H')|exact (Bt p k c'' H')].
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
    by (intros [|[[]| |] l] Hl; try reflexivity; discriminate).
  unfold add_text. destruct txt as [|a t'].
  - cbn [append]. rewrite Hs. reflexivity.
  - cbn [nonempty_str append]. unfold pv_add.
    destruct v0 as [[|f rest] out md]; cbn [top_of pv_stk pv_out pv_mode] in Ht |- *;
      [rewrite (X _ Ht); reflexivity|].
    destruct f as [p k c]; cbn [fset fcontent] in *; rewrite (X _ Ht); reflexivity.
Qed.

(* What `ilead` asks of a byte that is not a footnote's `^`. *)
Definition no_note (c : ascii) (txt : string) (prev : option ascii) : bool :=
  negb (Ascii.eqb c hat && note_pos txt prev && notes_enabled).

(* A byte no construct claims by position goes to the table. *)
Local Lemma ilead_itable : forall c txt prev o,
  no_note c txt prev = true -> is_bslash c = false -> is_tick c = false ->
  Ascii.eqb c dollar = false -> Ascii.eqb c period = false -> Ascii.eqb c hyphen = false ->
  Ascii.eqb c lbrace = false -> Ascii.eqb c bang = false -> Ascii.eqb c lt = false ->
  Ascii.eqb c ":"%char = false -> Ascii.eqb c lbrack = false -> Ascii.eqb c rbrack = false ->
  ilead c txt prev o = itable c txt prev o.
Proof.
  intros c txt prev o Hn Hbs Htk Hdol Hpd Hhy Hlb Hbg Hlt Hco Hlk Hrk.
  unfold no_note in Hn. apply negb_true_iff in Hn. unfold ilead.
  rewrite Hbs, Htk, Hdol, Hpd, Hhy, Hlb, Hbg, Hlt, Hco, Hlk, Hrk, Hn. reflexivity.
Qed.

(* A plain byte, a paren, and `}`, which no row spells, are text. *)
Local Lemma table_text : forall c txt prev o,
  in_alphabet c = true -> Ascii.eqb c lbrace = false ->
  Ascii.eqb c lbrack = false -> Ascii.eqb c rbrack = false -> is_tick c = false ->
  Ascii.eqb c dollar = false -> Ascii.eqb c lt = false -> Ascii.eqb c ":"%char = false ->
  Ascii.eqb c bang = false -> Ascii.eqb c period = false -> dstyle_of c = None ->
  itable c txt prev o = IText false (txt ++ one c) (Some c) o.
Proof.
  intros c txt prev o Ha Hlb Hlk Hrk Htk Hdl Hlt' Hco Hbg0 Hpd0 Hd.
  unfold itable. rewrite Hd.
  destruct (Ascii.eqb c rbrace) eqn:Erb.
  { apply Ascii.eqb_eq in Erb. subst c. change (Ascii.eqb rbrace percent) with false.
    rewrite andb_false_r. reflexivity. }
  unfold in_alphabet in Ha. rewrite Hd in Ha.
  apply andb_true_iff in Ha as [Ha _]. apply andb_true_iff in Ha as [Ha _].
  apply andb_true_iff in Ha as [_ Hres].
  rewrite Hlb, Erb, Hlk, Hrk, Htk, Hdl, Hlt', Hco, Hbg0, Hpd0 in Hres.
  cbn [orb] in Hres. apply andb_true_iff in Hres as [_ Hpct].
  apply negb_true_iff in Hpct. rewrite Hpct. reflexivity.
Qed.

Local Lemma alphabet_hyphen_row : in_alphabet hyphen = true -> hyphen_row_ok = true.
Proof.
  intros H. unfold in_alphabet in H.
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H]. exact H.
Qed.

Local Lemma alphabet_paren : forall c k,
  in_alphabet c = true -> dstyle_of c = Some k ->
  Ascii.eqb c lparen = false /\ Ascii.eqb c rparen = false.
Proof.
  intros c k H Hd. unfold in_alphabet in H. rewrite Hd in H.
  apply andb_true_iff in H as [_ H].
  apply negb_true_iff, orb_false_iff in H. exact H.
Qed.


(* A row's token but its first byte, which the table has read. *)
Definition dtail (k : dstyle) : string := chars (dchar k) (pred (dwidth k)).

Local Lemma dtoken_tail : forall k, dtoken k = String (dchar k) (dtail k).
Proof.
  intros k. unfold dtoken, dtail.
  destruct (dwidth k) as [|w] eqn:Ew; [destruct (dwidth_nonzero k Ew)|]. reflexivity.
Qed.

Local Lemma table_dchar : forall k txt prev o,
  denabled_of k = true -> itable (dchar k) txt prev o = IDelim k 0 txt prev false o.
Proof. intros k txt prev o Hen. unfold itable. rewrite (dstyle_of_dchar k Hen). reflexivity. Qed.

Local Lemma table_dtail : forall k txt prev o,
  denabled_of k = true ->
  iscan_str (dtail k) (itable (dchar k) txt prev o) = IDelim k (pred (dwidth k)) txt prev false o.
Proof.
  intros k txt prev o Hen. rewrite (table_dchar k txt prev o Hen). unfold dtail.
  destruct (dwidth k) as [|w] eqn:Ew; [destruct (dwidth_nonzero k Ew)|].
  rewrite (iscan_chars_delim w k 0 txt _ o) by lia. reflexivity.
Qed.

Local Lemma oemit_view : forall x v,
  (forall s, x <> Str s) -> oemit (mk x) (oview v) = oview (pv_add x v).
Proof.
  intros x [[|f rest] out md] Hx; unfold oemit, oview, pv_add;
    cbn [pv_stk pv_out os_stk os_out os_word_start map];
    rewrite (xsnoc_nonstr x _ (vin_nonstr x Hx)); [reflexivity|].
  destruct f as [p [[k mr|] im'] c]; reflexivity.
Qed.

Local Lemma top_add_nonstr : forall x v,
  (forall s, x <> Str s) -> starts_text (top_of (pv_add x v)) = false.
Proof.
  intros x [[|f rest] out md] Hx; unfold pv_add, top_of; cbn [pv_stk pv_out];
    [|destruct f; cbn [fset fcontent]];
    rewrite (xsnoc_nonstr x _ (vin_nonstr x Hx)); destruct x; try reflexivity; destruct (Hx _ eq_refl).
Qed.

Local Lemma pclose_grows : forall k stk pend content rest,
  pclose_go k pend stk = Some (content, rest) -> pend <> [] -> content <> [].
Proof.
  intros k stk. induction stk as [|[q [k' im'] c] stk IH];
    intros pend content rest H Hp; [discriminate|].
  cbn [pclose_go fst] in H. destruct (key_eq k k').
  - injection H as <- _. apply xapp_nonempty, Hp.
  - apply (IH _ _ _ H). apply xapp_nonempty_r. discriminate.
Qed.

(* Outside a region, a closer finds its opener's content empty exactly
   when the opener is the token right before it. *)
Local Lemma close_empty : forall ps n v above p k im c rest content rest',
  pv_ok ps n v -> pv_mode v = PMNormal ->
  pv_stk v = (above ++ PF p (k, im) c :: rest)%list ->
  Forall (passes k) above ->
  pclose_go k [] (pv_stk v) = Some (content, rest') ->
  (content = [] <-> tok_end ps p = n).
Proof.
  intros ps n v above p k im c rest content rest' (D & Bd & Be & So & Bt & Inn) Em E F H.
  unfold pv_live in D, Bd. rewrite E in D, Bd, Be, H, Inn, So, Bt. rewrite Em in Inn.
  destruct above as [|g above'].
  - cbn [app pclose_go fst] in H. rewrite key_eq_refl in H. injection H as <- _. exact Inn.
  - apply Forall_cons_iff in F as [Fk F].
    destruct g as [q k1 c1]. cbn [passes] in Fk.
    cbn [app pclose_go] in H. rewrite Fk in H.
    apply pclose_grows in H; [|apply xapp_nonempty_r; discriminate].
    assert (Hq : tok_end ps q <= n) by (apply (Be q k1 c1); left; reflexivity).
    (* the opener below ends where the one above at the latest starts *)
    assert (Hpq : tok_end ps p <= q).
    { apply StronglySorted_inv in So as [_ G]. rewrite Forall_forall in G.
      apply (G (PF p (k, im) c)). apply in_or_app. right. left. reflexivity. }
    assert (Hqe : q < tok_end ps q) by (apply (Bt q k1 c1); left; reflexivity).
    split; [intros; contradiction|lia].
Qed.

(* A node after the text: the text is flushed and the node emitted. *)
Local Lemma sim_node : forall v txt o (x : inline),
  sim v txt o -> (forall s, x <> Str s) ->
  sim (pv_add x v) "" (oemit (mk x) (flush_text txt o)).
Proof.
  intros v txt o x (v0 & -> & Ht & ->) Hx.
  rewrite (flush_view txt v0 Ht), (oemit_view x _ Hx).
  exists (pv_add x (add_text txt v0)).
  split; [reflexivity|]. split; [apply top_add_nonstr, Hx|reflexivity].
Qed.

(* A completed token, bare or with `}` after it (`mr`), resolved. *)
Local Lemma resolve_sim : forall ps n h k mr txt prev next v o,
  pv_ok ps n v -> pv_mode v = PMNormal -> frames_normal v ->
  sim v txt o ->
  exists txt' o',
    idelim_resolve k txt prev mr next o
    = IText false txt' (Some (if mr then rbrace else dchar k)) o'
    /\ sim (pstep ps n h (TDelim k mr (negb mr && dbare k prev && nonspace_at next)
                          (mr || nonspace_at prev)) v) txt' o'.
Proof.
  intros ps n h k mr txt prev next v o Ok Em Nv (v0 & -> & Ht & ->).
  pose proof Ok as (_ & Bd & Be & _).
  set (v := add_text txt v0) in *.
  set (op := (negb mr && dbare k prev && nonspace_at next)%bool).
  set (K := KDelim k mr).
  set (cmr := at_rbrace (get (tok_end ps n) ps)).
  assert (El : delim_lit k mr op cmr = ddecay_str k false mr)
    by (unfold delim_lit, op; destruct mr; reflexivity).
  assert (Hv : flush_text txt (oview v0) = oview v)
    by (apply flush_view, Ht).
  assert (Lv : pv_live v = pv_live v0).
  { unfold v, add_text. destruct (nonempty_str txt); [apply pv_add_live|reflexivity]. }
  (* the token as text *)
  assert (Lit : sim (pv_add (Str (ddecay_str k false mr)) v)
                  (txt ++ ddecay_str k false mr) (oview v0)).
  { apply sim_text; [|apply ddecay_str_nonempty].
    exists v0. split; [reflexivity|]. split; [exact Ht|reflexivity]. }
  (* the token does not close: it opens if it may, or it is text *)
  assert (Done : exists txt' o',
            idelim_done k txt prev mr next (oview v0)
            = IText false txt' (Some (if mr then rbrace else dchar k)) o'
            /\ sim (popen n (K, (mr && cmr)%bool) op (ddecay_str k false mr) v) txt' o').
  { unfold idelim_done.
    replace (dbare k prev && negb mr && nonspace_at next)%bool with op
      by (unfold op; destruct mr, (dbare k prev); reflexivity).
    destruct op eqn:Op.
    - assert (mr = false) as -> by (destruct mr; [discriminate Op|reflexivity]).
      change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s
                (tval txt) (oview v0))
        with (flush_text txt (oview v0)).
      rewrite Hv. eexists "", _. split; [reflexivity|].
      exists (PView (PF n (KDelim k false, false) [] :: pv_stk v) (pv_out v) (pv_mode v)).
      split; [reflexivity|]. split; reflexivity.
    - (* a quote is a node after the flushed text, any other token text *)
      unfold popen, odecay, K. cbn [kdecay fst]. unfold decay_node.
      destruct (dc_decay cfg k) eqn:Ed.
      + exists (txt ++ ddecay_str k false mr), (oview v0). split; [reflexivity|]. exact Lit.
      + eexists "", _. split; [reflexivity|].
        apply sim_node; [|discriminate].
        exists v0. split; [reflexivity|]. split; [exact Ht|reflexivity]. }
  unfold idelim_resolve, pstep. fold op cmr K. cbv zeta. rewrite El.
  destruct (nonspace_at prev || mr)%bool eqn:Hc.
  2: { apply orb_false_iff in Hc as [Hp ->]. rewrite Hp. cbn [orb]. exact Done. }
  rewrite orb_comm, Hc.
  rewrite oclose_guard.
  change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s
            (tval txt) (oview v0))
    with (flush_text txt (oview v0)).
  rewrite Hv. unfold oclose. unfold oview at 1.
  cbn [os_stk os_out os_word_start].
  change (@nil oitem) with (map eo (@nil vitem)).
  rewrite (oclose_go_embed k mr [] (pv_stk v)).
  fold K.
  destruct (pick K (pv_live v)) as [p below|] eqn:P.
  2: { rewrite (pclose_none K (pv_stk v) []) by (intros p' b'; unfold pv_live in P; rewrite P; discriminate).
       exact Done. }
  unfold pv_live in P.
  destruct (pick_split K (pv_stk v) p below P)
    as (above & im0 & c & rest & E & F & Hbl).
  destruct (pclose_split K im0 above p c rest [] F) as [content Hc'].
  rewrite <- E in Hc'. rewrite Hc'.
  pose proof (close_empty ps n v above p K im0 c rest content rest Ok Em E F Hc')
    as Hce.
  pose proof (proj1 (pclose_go_normal K _ [] content rest Nv Logic.I Hc')) as Ncont.
  assert (Hpn : p < n).
  { apply (Bd (p, K)). unfold pv_live. rewrite E, map_app.
    apply in_or_app. right. left. reflexivity. }
  assert (Hpe : tok_end ps p <= n).
  { apply (Be p (K, im0) c). rewrite E. apply in_or_app. right. left. reflexivity. }
  destruct (Nat.ltb (tok_end ps p) n) eqn:L.
  - apply Nat.ltb_lt in L.
    assert (content <> []) as Hne by (intros H0; apply Hce in H0; lia).
    destruct content as [|x0 content']; [contradiction|]. cbn [nonempty].
    set (content := x0 :: content').
    eexists "", _. split; [destruct mr; reflexivity|].
    exists (pv_add (dnode k (vres content)) (PView rest (pv_out v) PMNormal)).
    split; [|split; [apply top_add_nonstr, dnode_nonstr|reflexivity]].
    rewrite (oresolve_embed content Ncont).
    change (List.rev (vsettle content)) with (vres content).
    destruct mr;
      change ({| os_out := os_out (oview v); os_stk := map oframe rest;
                 os_word_start := os_word_start (oview v) |})
        with (oview (PView rest (pv_out v) PMNormal));
      apply oemit_view, dnode_nonstr.
  - apply Nat.ltb_ge in L.
    assert (content = []) as -> by (apply Hce; lia). exact Done.
Qed.

(*
Readings that never close
-------------------------

A destination that does not close is read twice: as a destination,
which the balanced `)` would end and never does, and as the ordinary
reading of its `]` and what follows, which is what the paragraph keeps.
So is a reference label or a footnote label that does not close: as a
label, which a `]` would end, and as the ordinary reading of its `][`
or `[^` and what follows; and so is an attribute spec that does not
close, bare or a span's, as a spec and as the ordinary reading of its
`{`.  The scanner's state is the paragraph's reading inside one
`IDest`, `IReference`, `INote`, `IAttr` or `ISpan` per such construct
(a layer).  A byte passes through each of them as long as
it is not the byte that would end one.  A spec's layer is gone at the
byte its machine fails at, and the reading inside it is what is left.

What a layer keeps besides the reading inside it is a small machine of
its own: for a destination (`dstep`) a pending backslash, the paren
depth and the text so far; for a label of either kind (`nstep`) a
pending backslash and the label so far; for a spec (`sstep`) the
attribute machine and the bytes so far. *)

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

Record nstate : Type := NS { ns_esc : bool; ns_lab : string }.

(* One byte, as `INote` and `IReference` read it, or `None` if the byte
   ends the label. *)
Definition nstep (c : ascii) (s : nstate) : option nstate :=
  if ns_esc s then Some (NS false (ns_lab s ++ one bslash ++ one c))
  else if is_bslash c then Some (NS true (ns_lab s))
  else if Ascii.eqb c rbrack then None
  else Some (NS false (ns_lab s ++ one c)).

Fixpoint nfeed (s : string) (st : nstate) : option nstate :=
  match s with
  | EmptyString => Some st
  | String c rest => match nstep c st with Some st' => nfeed rest st' | None => None end
  end.

(* One byte, as `IAttr` and `ISpan` read it, or `None` if the byte closes
   the spec.  A failed machine stays failed. *)
Definition sstep (c : ascii) (p : aparser) : option aparser :=
  let p' := astep p c in if ap_done p' then None else Some p'.

Fixpoint sfeed (s : string) (p : aparser) : option aparser :=
  match s with
  | EmptyString => Some p
  | String c rest => match sstep c p with Some p' => sfeed rest p' | None => None end
  end.

Inductive wlayer : Type :=
  | WDest (kids : inlines) (im : bool) (open : span) (ds : dstate) (o : ostate)
  | WRef (kids : inlines) (im : bool) (open : span) (ns : nstate) (o : ostate)
  | WNote (im : bool) (open : span) (ns : nstate) (o : ostate)
  | WAttr (p : aparser) (src txt : string) (prev : option ascii) (o : ostate)
  | WSpan (kids : inlines) (im : bool) (open : span) (p : aparser) (src : string) (o : ostate).

Definition wstep (c : ascii) (w : wlayer) : option wlayer :=
  match w with
  | WDest k i op ds o => option_map (fun d => WDest k i op d o) (dstep c ds)
  | WRef k i op ns o => option_map (fun d => WRef k i op d o) (nstep c ns)
  | WNote i op ns o => option_map (fun d => WNote i op d o) (nstep c ns)
  | WAttr p src txt prev o =>
      option_map (fun p' => WAttr p' (src ++ one c) txt prev o) (sstep c p)
  | WSpan k i op p src o => option_map (fun p' => WSpan k i op p' (src ++ one c) o) (sstep c p)
  end.

Fixpoint wfeed (s : string) (w : wlayer) : option wlayer :=
  match s with
  | EmptyString => Some w
  | String c rest => match wstep c w with Some w' => wfeed rest w' | None => None end
  end.

Local Lemma wfeed_app : forall a b w,
  wfeed (a ++ b) w = match wfeed a w with Some w' => wfeed b w' | None => None end.
Proof.
  induction a as [|c a IH]; intros b w; [reflexivity|].
  cbn [append wfeed]. destruct (wstep c w); [apply IH|reflexivity].
Qed.

Local Lemma wfeed_dest : forall s k i op ds o,
  wfeed s (WDest k i op ds o) = option_map (fun d => WDest k i op d o) (dfeed s ds).
Proof.
  induction s as [|c s IH]; intros k i op ds o; [reflexivity|].
  cbn [wfeed dfeed wstep]. destruct (dstep c ds); [apply IH|reflexivity].
Qed.

Local Lemma wfeed_ref : forall s k i op ns o,
  wfeed s (WRef k i op ns o) = option_map (fun d => WRef k i op d o) (nfeed s ns).
Proof.
  induction s as [|c s IH]; intros k i op ns o; [reflexivity|].
  cbn [wfeed nfeed wstep]. destruct (nstep c ns); [apply IH|reflexivity].
Qed.

Local Lemma wfeed_note : forall s i op ns o,
  wfeed s (WNote i op ns o) = option_map (fun d => WNote i op d o) (nfeed s ns).
Proof.
  induction s as [|c s IH]; intros i op ns o; [reflexivity|].
  cbn [wfeed nfeed wstep]. destruct (nstep c ns); [apply IH|reflexivity].
Qed.

Local Lemma wfeed_attr : forall s p src txt prev o,
  wfeed s (WAttr p src txt prev o)
  = option_map (fun p' => WAttr p' (src ++ s) txt prev o) (sfeed s p).
Proof.
  induction s as [|c s IH]; intros p src txt prev o;
    [cbn; rewrite append_empty_r; reflexivity|].
  cbn [wfeed sfeed wstep]. destruct (sstep c p); [|reflexivity].
  cbn [option_map]. rewrite IH. destruct (sfeed s _); [|reflexivity]. cbn [option_map].
  rewrite append_assoc. reflexivity.
Qed.

Local Lemma wfeed_span : forall s k i op p src o,
  wfeed s (WSpan k i op p src o)
  = option_map (fun p' => WSpan k i op p' (src ++ s) o) (sfeed s p).
Proof.
  induction s as [|c s IH]; intros k i op p src o;
    [cbn; rewrite append_empty_r; reflexivity|].
  cbn [wfeed sfeed wstep]. destruct (sstep c p); [|reflexivity].
  cbn [option_map]. rewrite IH. destruct (sfeed s _); [|reflexivity]. cbn [option_map].
  rewrite append_assoc. reflexivity.
Qed.

Fixpoint wrap (ws : list wlayer) (core : iscan) : iscan :=
  match ws with
  | [] => core
  | WDest k i op ds o :: rest =>
      IDest k i op (ds_esc ds) (ds_depth ds) (ds_dst ds) (wrap rest core) o
  | WRef k i op ns o :: rest => IReference k i op (ns_esc ns) (ns_lab ns) (wrap rest core) o
  | WNote i op ns o :: rest => INote (ns_esc ns) i (ns_lab ns) op (wrap rest core) o
  | WAttr p src txt prev o :: rest =>
      if ap_failed p then wrap rest core else IAttr p src txt prev (wrap rest core) o
  | WSpan k i op p src o :: rest =>
      if ap_failed p then wrap rest core else ISpan k i op p src (wrap rest core) o
  end.

Definition wl_after (s : string) (w : wlayer) : wlayer :=
  match wfeed s w with Some w' => w' | None => w end.

Fixpoint no_bslash (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c rest => negb (is_bslash c) && no_bslash rest
  end.

Local Lemma istep_idest : forall c kids im op e depth dst sh o d,
  dstep c (DS e depth dst) = Some d ->
  istep c (IDest kids im op e depth dst sh o)
  = IDest kids im op (ds_esc d) (ds_depth d) (ds_dst d) (istep c sh) o.
Proof.
  intros c kids im op e depth dst sh o d H. unfold dstep in H. cbn [ds_esc ds_depth ds_dst] in H.
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

Local Lemma istep_inote : forall c e im lab op sh o d,
  nstep c (NS e lab) = Some d ->
  istep c (INote e im lab op sh o) = INote (ns_esc d) im (ns_lab d) op (istep c sh) o.
Proof.
  intros c e im lab op sh o d H. unfold nstep in H. cbn [ns_esc ns_lab] in H.
  unfold istep. cbn [istep_at]. unfold inote_step.
  destruct e; [injection H as <-; reflexivity|].
  destruct (is_bslash c); [injection H as <-; reflexivity|].
  destruct (Ascii.eqb c rbrack); [discriminate|injection H as <-; reflexivity].
Qed.

Local Lemma istep_iref : forall c kids im op e lab sh o d,
  nstep c (NS e lab) = Some d ->
  istep c (IReference kids im op e lab sh o)
  = IReference kids im op (ns_esc d) (ns_lab d) (istep c sh) o.
Proof.
  intros c kids im op e lab sh o d H. unfold nstep in H. cbn [ns_esc ns_lab] in H.
  unfold istep. cbn [istep_at]. unfold iref_step.
  destruct e; [injection H as <-; reflexivity|].
  destruct (is_bslash c); [injection H as <-; reflexivity|].
  destruct (Ascii.eqb c rbrack); [discriminate|injection H as <-; reflexivity].
Qed.

Local Lemma astep_failed : forall p c, ap_failed p = true -> astep p c = p.
Proof. intros [st tok key at'] c H. destruct st; try discriminate H; reflexivity. Qed.

(* A spec's machine, past a byte that does not close it. *)
Local Lemma sstep_cases : forall c p p',
  sstep c p = Some p' ->
  p' = astep p c /\ ap_done p' = false /\ (ap_failed p = true -> ap_failed p' = true).
Proof.
  intros c p p' H. unfold sstep in H. destruct (ap_done (astep p c)) eqn:Ed; [discriminate|].
  injection H as <-. split; [reflexivity|]. split; [exact Ed|].
  intros F. rewrite (astep_failed p c F). exact F.
Qed.

Local Lemma istep_layer : forall c w w' sh,
  wstep c w = Some w' -> istep c (wrap [w] sh) = wrap [w'] (istep c sh).
Proof.
  intros c [k i op [e d dst] o|k i op [e lab] o|i op [e lab] o|p src txt prev o|k i op p src o] w' sh H;
    cbn [wstep] in H.
  - destruct (dstep c (DS e d dst)) as [d'|] eqn:Hd; [|discriminate]. injection H as <-.
    exact (istep_idest c k i op e d dst sh o d' Hd).
  - destruct (nstep c (NS e lab)) as [d'|] eqn:Hd; [|discriminate]. injection H as <-.
    exact (istep_iref c k i op e lab sh o d' Hd).
  - destruct (nstep c (NS e lab)) as [d'|] eqn:Hd; [|discriminate]. injection H as <-.
    exact (istep_inote c e i lab op sh o d' Hd).
  - destruct (sstep c p) as [p'|] eqn:Hp; [|discriminate]. injection H as <-.
    destruct (sstep_cases c p p' Hp) as (-> & Hd & Hf). cbn [wrap].
    destruct (ap_failed p) eqn:F; [rewrite (Hf eq_refl); reflexivity|].
    unfold istep at 1. cbn [istep_at]. unfold iattr_feed.
    destruct (ap_failed (astep p c)); [reflexivity|]. rewrite Hd. reflexivity.
  - destruct (sstep c p) as [p'|] eqn:Hp; [|discriminate]. injection H as <-.
    destruct (sstep_cases c p p' Hp) as (-> & Hd & Hf). cbn [wrap].
    destruct (ap_failed p) eqn:F; [rewrite (Hf eq_refl); reflexivity|].
    unfold istep at 1. cbn [istep_at]. unfold ispan_feed.
    destruct (ap_failed (astep p c)); [reflexivity|]. rewrite Hd. reflexivity.
Qed.

Local Lemma istep_wrap : forall c ws core,
  Forall (fun w => wstep c w <> None) ws ->
  istep c (wrap ws core)
  = wrap (map (fun w => match wstep c w with Some w' => w' | None => w end) ws) (istep c core).
Proof.
  intros c ws core. induction ws as [|w ws IHw]; intros G; [reflexivity|].
  apply Forall_cons_iff in G as [Gw G].
  destruct (wstep c w) as [w'|] eqn:Hw; [|contradiction].
  change (wrap (w :: ws) core) with (wrap [w] (wrap ws core)).
  rewrite (istep_layer c w w' _ Hw), (IHw G). cbn [map]. rewrite Hw. reflexivity.
Qed.

Local Lemma iscan_wrap : forall s ws core,
  Forall (fun w => wfeed s w <> None) ws ->
  iscan_str s (wrap ws core) = wrap (map (wl_after s) ws) (iscan_str s core).
Proof.
  induction s as [|c s IH]; intros ws core F.
  - cbn [iscan_str]. f_equal. rewrite <- (map_id ws) at 1. apply map_ext. reflexivity.
  - cbn [iscan_str]. rewrite istep_wrap.
    2: { rewrite Forall_forall in F |- *. intros w Hw E. apply (F w Hw).
         cbn [wfeed]. rewrite E. reflexivity. }
    rewrite IH.
    + f_equal. rewrite map_map. apply map_ext_in. intros w Hw.
      rewrite Forall_forall in F. specialize (F _ Hw). cbn [wfeed] in F.
      unfold wl_after. cbn [wfeed]. destruct (wstep c w) as [w0|]; [|contradiction].
      destruct (wfeed s w0); [reflexivity|contradiction].
    + rewrite Forall_map. rewrite Forall_forall in F |- *. intros w Hw E.
      apply (F w Hw). cbn [wfeed]. destruct (wstep c w); [exact E|reflexivity].
Qed.

(* A state resolved as at the end of a line, through the readings that
   cross it.  A pending `$` is kept while dollar math is on: a break may
   open display math from it, which its resolved text cannot.  A `{` is a
   spec that has read nothing yet, beside the `{` read as text, while
   inline attributes are on.  An autolink candidate, a symbol or a raw
   spec the line ends inside is its ordinary reading. *)
Fixpoint rres (st : iscan) : iscan :=
  match st with
  | IDest k i o e d dst sh o' => IDest k i o e d dst (rres sh) o'
  | IReference k i op e l sh o => IReference k i op e l (rres sh) o
  | INote e i l op sh o => INote e i l op (rres sh) o
  | IAttr p src txt prev sh o => IAttr p src txt prev (rres sh) o
  | ISpan k i op p src sh o => ISpan k i op p src (rres sh) o
  | ISymbol _ _ sh _ => rres sh
  | IRaw _ _ sh _ => rres sh
  | IBrace txt prev o =>
      if inline_attrs_enabled then IAttr ap_init "" txt prev (iresolve st) o else iresolve st
  | IDollar _ _ _ _ => if dollar_math_enabled then st else iresolve st
  | IAuto _ _ sh _ => rres sh
  | _ => iresolve st
  end.

Local Lemma rres_wrap : forall ws core, rres (wrap ws core) = wrap ws (rres core).
Proof.
  induction ws as [|w ws IH]; intros core; [reflexivity|].
  destruct w; cbn [wrap]; try destruct (ap_failed p); cbn [rres]; rewrite IH; reflexivity.
Qed.

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
  Forall (fun w => wfeed (bytes ++ rest) w <> None) ws ->
  iscan_str bytes core = X -> settles X st (get 0 rest) ->
  rres (iscan_str (bytes ++ rest) (wrap ws core))
  = rres (iscan_str rest (wrap (map (wl_after bytes) ws) st)).
Proof.
  intros bytes rest ws core X st F HX Hs.
  rewrite iscan_str_app, iscan_wrap, HX.
  2: { rewrite Forall_forall in F |- *. intros w Hw E. apply (F w Hw).
       rewrite wfeed_app, E. reflexivity. }
  destruct rest as [|c r].
  - cbn [iscan_str]. rewrite !rres_wrap. cbn [get settles] in Hs. rewrite Hs. reflexivity.
  - cbn [iscan_str]. cbn [get settles] in Hs.
    assert (Fc : Forall (fun w => wstep c w <> None) (map (wl_after bytes) ws)).
    { rewrite Forall_map. rewrite Forall_forall in F |- *. intros w Hw E. apply (F w Hw).
      rewrite wfeed_app. unfold wl_after in E.
      destruct (wfeed bytes w) as [w'|]; [|reflexivity].
      cbn [wfeed]. rewrite E. reflexivity. }
    rewrite !(istep_wrap c _ _ Fc), Hs. reflexivity.
Qed.

(* The same where the scanner decides later than the byte after the
   token: the two states agree once some prefix of the rest of the line
   is read, or at its end.  A run of hyphens before a `}` is one, where
   the scanner holds the run until the `}` and the reading has cut it
   into a dash and a closer. *)
Definition settles_in (X st : iscan) (rest : string) : Prop :=
  exists p r', rest = (p ++ r')%string
    /\ (iscan_str p X = iscan_str p st
        \/ (r' = EmptyString /\ rres (iscan_str p X) = rres (iscan_str p st))).

Local Lemma settles_in_of : forall X st rest, settles X st (get 0 rest) -> settles_in X st rest.
Proof.
  intros X st [|c r] H; cbn [get settles] in H.
  - exists "", "". split; [reflexivity|right; split; [reflexivity|exact H]].
  - exists (one c), r. split; [reflexivity|left; exact H].
Qed.

Local Lemma step_through_in : forall bytes rest ws core X st,
  Forall (fun w => wfeed (bytes ++ rest) w <> None) ws ->
  iscan_str bytes core = X -> settles_in X st rest ->
  rres (iscan_str (bytes ++ rest) (wrap ws core))
  = rres (iscan_str rest (wrap (map (wl_after bytes) ws) st)).
Proof.
  intros bytes rest ws core X st F HX (p & r' & -> & Hs).
  rewrite iscan_str_app, iscan_wrap, HX.
  2: { rewrite Forall_forall in F |- *. intros w Hw E. apply (F w Hw).
       rewrite wfeed_app, E. reflexivity. }
  assert (Fp : Forall (fun w => wfeed p w <> None) (map (wl_after bytes) ws)).
  { rewrite Forall_map. rewrite Forall_forall in F |- *. intros w Hw E. apply (F w Hw).
    rewrite wfeed_app. unfold wl_after in E.
    destruct (wfeed bytes w) as [w'|]; [|reflexivity].
    rewrite wfeed_app, E. reflexivity. }
  rewrite !iscan_str_app, !(iscan_wrap p _ _ Fp).
  destruct Hs as [E | [-> E]]; [rewrite E; reflexivity|].
  cbn [iscan_str]. rewrite !rres_wrap, E. reflexivity.
Qed.

(*
Tokens, in text mode
--------------------
*)

Local Lemma settles_refl : forall X next, settles X X next.
Proof. intros X [c|]; reflexivity. Qed.

(* A bare token, past its first byte: the byte after it resolves it. *)
Local Lemma tok_bare : forall k txt prev o next txt' o',
  denabled_of k = true ->
  (forall c, next = Some c -> Ascii.eqb c rbrace = false) ->
  idelim_resolve k txt prev false next o = IText false txt' (Some (dchar k)) o' ->
  settles (iscan_str (dtail k) (itable (dchar k) txt prev o))
          (IText false txt' (Some (dchar k)) o') next.
Proof.
  intros k txt prev o next txt' o' Hen Hr Hres.
  rewrite (table_dtail k txt prev o Hen).
  assert (Hw : Nat.ltb (S (pred (dwidth k))) (dwidth k) = false).
  { pose proof (dwidth_nonzero k). apply Nat.ltb_ge. lia. }
  destruct next as [c|]; cbn [settles].
  - unfold istep at 1. cbn [istep_at]. rewrite Hw, (Hr c eq_refl), Hres. reflexivity.
  - cbn [rres iresolve]. rewrite Hw, Hres. reflexivity.
Qed.

(* A token with `}` after it, past its first byte: a marked closer, the
   `}` with it. *)
Local Lemma tok_marked_close : forall k txt prev o,
  denabled_of k = true ->
  iscan_str (dtail k ++ one rbrace) (itable (dchar k) txt prev o)
  = idelim_resolve k txt prev true (Some rbrace) o.
Proof.
  intros k txt prev o Hen.
  rewrite iscan_str_app, (table_dtail k txt prev o Hen).
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

(* A run of a row's character too short to be a token is text; past its
   first byte. *)
Local Lemma tok_partial : forall k j txt prev o next,
  denabled_of k = true -> 0 < j < dwidth k ->
  (forall c, next = Some c -> c <> dchar k) ->
  settles (iscan_str (chars (dchar k) (pred j)) (itable (dchar k) txt prev o))
          (IText false (txt ++ chars (dchar k) j) (Some (dchar k)) o) next.
Proof.
  intros k j txt prev o next Hen [Hj0 Hjw] Hr.
  destruct j as [|j]; [lia|]. cbn [pred].
  rewrite (table_dchar k txt prev o Hen).
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
  intros txt prev o Ht. unfold ilead, itable. cbn [is_bslash is_tick Ascii.eqb Ascii.ascii_dec].
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

(* Two bytes the flanking rules cannot tell apart: the one before a
   token in the paragraph, and the one the scanner holds, which is none
   at the start of a line. *)
Definition same_prev (a b : option ascii) : Prop :=
  nonspace_at a = nonspace_at b /\ forall k, dbare k a = dbare k b.

Local Lemma same_prev_refl : forall a, same_prev a a.
Proof. intros a. split; reflexivity. Qed.

#[local] Instance same_prev_Reflexive : RelationClasses.Reflexive same_prev := same_prev_refl.

Local Lemma next_tok_prev : forall p1 p2 s,
  same_prev p1 p2 -> next_tok p1 s = next_tok p2 s.
Proof.
  intros p1 p2 [|c r] [H1 H2]; [reflexivity|].
  unfold next_tok, esc_tok, dots_tok, dash_tok, bang_tok, lbrack_tok, rbrack_tok, lbrace_tok, delim_tok.
  rewrite H1. destruct (dstyle_of c) as [k|]; [rewrite (H2 k)|]; reflexivity.
Qed.

Local Lemma auto_tok_app : forall r after,
  no_char nl_char r = true -> line_end after -> auto_tok (r ++ after) = auto_tok r.
Proof.
  intros r after Hn Ha.
  set (is_gt := fun o : option ascii => match o with Some c => Ascii.eqb c gt | None => false end).
  assert (G : forall r, no_char nl_char r = true ->
            fst (auto_go (r ++ after)) = fst (auto_go r)
            /\ is_gt (snd (auto_go (r ++ after))) = is_gt (snd (auto_go r))).
  { clear r Hn. induction r as [|c r IH]; intros Hn.
    - destruct Ha as [->|[r' ->]]; split; reflexivity.
    - cbn [no_char] in Hn. apply andb_true_iff in Hn as [_ Hn].
      cbn [append auto_go]. destruct (auto_stop c); [split; reflexivity|].
      destruct (IH Hn) as [E1 E2].
      destruct (auto_go (r ++ after)) as [s1 t1], (auto_go r) as [s2 t2].
      cbn [fst snd] in *. subst s2. split; [reflexivity|exact E2]. }
  destruct (G r Hn) as [E1 E2]. unfold auto_tok.
  destruct (auto_go (r ++ after)) as [s1 t1], (auto_go r) as [s2 t2]. cbn [fst snd] in *.
  subst s2. unfold is_gt in E2. rewrite E2. reflexivity.
Qed.

Local Lemma substring_app_l : forall a b j, j <= String.length a ->
  substring 0 j (a ++ b) = substring 0 j a.
Proof.
  induction a as [|c a IH]; intros b j Hj.
  - destruct j; [|cbn in Hj; lia]. rewrite !substring_nil. reflexivity.
  - destruct j as [|j]; [reflexivity|]. cbn [append substring]. cbn in Hj. rewrite IH by lia.
    reflexivity.
Qed.

Local Lemma sym_tok_app : forall r after,
  no_char nl_char r = true -> line_end after -> sym_tok (r ++ after) = sym_tok r.
Proof.
  intros r after Hn Ha.
  assert (SR : forall r0, symbol_run (r0 ++ after) = symbol_run r0).
  { induction r0 as [|x r0 IH]; [destruct Ha as [->|[r' ->]]; reflexivity|].
    cbn [append symbol_run]. rewrite IH. reflexivity. }
  assert (SD : forall r0 k, k <= String.length r0 ->
             sdrop k (r0 ++ after) = (sdrop k r0 ++ after)%string).
  { induction r0 as [|x r0 IH]; intros [|k] Hk; cbn in Hk |- *; try lia; try reflexivity.
    apply IH. lia. }
  pose proof (symbol_run_le r) as Le.
  unfold sym_tok. rewrite SR, SD by exact Le.
  destruct (sdrop (symbol_run r) r) as [|c r'] eqn:Es.
  - cbn [append]. replace (starts_with ":"%char after) with false
      by (destruct Ha as [->|[r'' ->]]; reflexivity).
    cbn [starts_with]. rewrite !andb_false_r. reflexivity.
  - cbn [append starts_with]. rewrite substring_app_l by exact Le. reflexivity.
Qed.

Local Lemma run_of_app : forall c s after,
  c <> nl_char -> line_end after -> run_of c (s ++ after) = run_of c s.
Proof.
  intros c s after Hc Ha. induction s as [|d s IH]; [|cbn [append run_of]; rewrite IH; reflexivity].
  destruct Ha as [->|[r ->]]; [reflexivity|]. cbn [append run_of].
  destruct (Ascii.eqb nl_char c) eqn:E; [|reflexivity].
  apply Ascii.eqb_eq in E. symmetry in E. contradiction.
Qed.

Local Lemma dash_tok_app : forall s after, line_end after -> dash_tok (s ++ after) = dash_tok s.
Proof.
  intros s after Ha. unfold dash_tok.
  rewrite (run_of_app hyphen s after ltac:(discriminate) Ha).
  assert (SD : forall r k, k <= String.length r ->
             sdrop k (r ++ after) = (sdrop k r ++ after)%string).
  { induction r as [|x r IH]; intros [|k] Hk; cbn in Hk |- *; try lia; try reflexivity.
    apply IH. lia. }
  rewrite (SD s _ (run_of_le hyphen s)).
  replace (starts_with rbrace (sdrop (run_of hyphen s) s ++ after))
    with (starts_with rbrace (sdrop (run_of hyphen s) s)); [reflexivity|].
  destruct (sdrop (run_of hyphen s) s); [|reflexivity].
  destruct Ha as [->|[r ->]]; reflexivity.
Qed.

(* A token within its line, but for a verbatim, which may cross a line
   break, a `[` or a `!`, which may begin a footnote reference that does,
   and a `]` or a `{` before anything but a row's character, which may
   begin an attribute spec that does. *)
Local Lemma next_tok_after : forall prev s after,
  no_char nl_char s = true -> line_end after -> s <> EmptyString -> starts_tick s = false ->
  starts_with dollar s = false -> starts_with bang s = false -> starts_with lbrack s = false ->
  starts_with lbrace s = false \/ starts_row (sdrop 1 s) = true -> starts_with rbrack s = false ->
  next_tok prev (s ++ after) = next_tok prev s.
Proof.
  intros prev s after Hn Ha Hne Htk Hdl Hbg Hlk Hlb Hrb. destruct s as [|c rest]; [contradiction|].
  cbn [starts_tick starts_with] in Htk, Hdl, Hbg, Hlk, Hrb. cbn [starts_with sdrop] in Hlb.
  cbn [no_char] in Hn. apply andb_true_iff in Hn as [Hc Hn]. apply negb_true_iff in Hc.
  assert (SW : forall x, x <> nl_char -> starts_with x (rest ++ after) = starts_with x rest).
  { intros x Hx. destruct rest as [|y r]; [|reflexivity].
    destruct Ha as [->|[r ->]]; [reflexivity|]. cbn [append starts_with].
    apply Ascii.eqb_neq. intros E. apply Hx. symmetry. exact E. }
  assert (Pf : forall k s', prefix (dtoken k) (s' ++ after) = prefix (dtoken k) s')
    by (intros k s'; unfold dtoken; apply prefix_chars_app; [apply dchar_not_nl|exact Ha]).
  cbn [append]. unfold next_tok, esc_tok, bang_tok, lbrack_tok, rbrack_tok, lbrace_tok, delim_tok. f_equal.
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
  destruct (Ascii.eqb c lt).
  { rewrite (auto_tok_app rest after Hn Ha). reflexivity. }
  destruct (Ascii.eqb c ":"%char).
  { rewrite (sym_tok_app rest after Hn Ha). reflexivity. }
  destruct (Ascii.eqb c period).
  { unfold dots_tok. change (String c (rest ++ after)) with (String c rest ++ after)%string.
    rewrite (run_of_app period _ after ltac:(discriminate) Ha). reflexivity. }
  destruct (Ascii.eqb c hyphen).
  { change (String c (rest ++ after)) with (String c rest ++ after)%string.
    rewrite (dash_tok_app _ after Ha). reflexivity. }
  rewrite Hbg, Hlk, Hrb.
  destruct (Ascii.eqb c lbrace) eqn:Elb.
  { destruct Hlb as [Hlb|Hrow]; [discriminate Hlb|].
    destruct rest as [|d r]; [discriminate Hrow|]. cbn [starts_row] in Hrow. unfold is_delim in Hrow.
    cbn [append]. destruct (dstyle_of d) as [k|]; [|discriminate Hrow].
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
  intros st. destruct st; try (right; reflexivity); try (left; cbn [iresolve]; eauto; fail);
    try (left; cbn [iresolve]; destruct (odashes _ _ _ _); eauto; fail).
  left. cbn [iresolve]. destruct (Nat.ltb (S extra) (dwidth k)); [eauto|].
  destruct marked; [unfold idelim_open_marked; eauto|].
  unfold idelim_resolve, idelim_done.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    repeat match goal with |- context [match ?b with Some _ => _ | None => _ end] => destruct b end;
    repeat match goal with |- context [odecay ?a ?b ?c ?d] => destruct (odecay a b c d) end;
    eauto.
Qed.

Local Lemma ifinish_ostate_rres : forall st : iscan,
  ifinish_ostate (rres st) = ifinish_ostate st.
Proof.
  induction st; try reflexivity; try (cbn [rres]; destruct dollar_math_enabled; reflexivity);
    try (cbn [rres ifinish_ostate]; exact IHst).
  - cbn [rres]. destruct inline_attrs_enabled; reflexivity.
  - destruct (iresolve_shape (IDelim k extra txt before marked o)) as [(t & p & o' & E)|E];
      cbn [rres ifinish_ostate]; rewrite !E; cbn [ifinish_ostate]; rewrite ?E; reflexivity.
  - cbn [rres iresolve ifinish_ostate]. destruct (odashes _ _ _ _); reflexivity.
Qed.

Local Lemma ifinish_rres : forall st : iscan, ifinish (rres st) = ifinish st.
Proof. intros st. unfold ifinish, ifinish_rev. rewrite ifinish_ostate_rres. reflexivity. Qed.

Local Lemma ibreak_rres : forall st : iscan, ibreak (rres st) = ibreak st.
Proof.
  unfold ibreak. induction st; try reflexivity;
    try (cbn [rres]; destruct dollar_math_enabled eqn:Edm; [reflexivity|];
         cbn [ibreak_at iresolve]; rewrite Edm, !andb_false_r; reflexivity);
    try (cbn [rres ibreak_at]; apply IHst);
    try (cbn [rres ibreak_at]; rewrite IHst; reflexivity).
  - cbn [rres]. destruct inline_attrs_enabled; reflexivity.
  - destruct (iresolve_shape (IDelim k extra txt before marked o)) as [(t & p & o' & E)|E];
      cbn [rres ibreak_at]; rewrite !E; cbn [ibreak_at]; rewrite ?E; reflexivity.
  - cbn [rres iresolve ibreak_at]. destruct (odashes _ _ _ _); reflexivity.
Qed.

Local Lemma ifinish_wrap : forall ws core, ifinish (wrap ws core) = ifinish core.
Proof.
  intros ws core. unfold ifinish, ifinish_rev.
  induction ws as [|w ws IH]; [reflexivity|].
  destruct w; cbn [wrap]; try destruct (ap_failed p); cbn [ifinish_ostate]; exact IH.
Qed.

(* Layers the newline passes. *)
Local Lemma ibreak_layer : forall w sh,
  wstep nl_char w <> None -> ibreak (wrap [w] sh) = wrap [wl_after nl w] (ibreak sh).
Proof.
  intros [k wi o [e dp dst] o'|k wi o [e lab] o'|wi o [e lab] o'|p src txt prev o|k wi op p src o] sh H;
    unfold ibreak, wl_after, nl; cbn [wfeed wstep one] in *; unfold sstep in *;
    change nl_char with "010"%char in *.
  - destruct e; reflexivity.
  - destruct e; reflexivity.
  - destruct e; reflexivity.
  - destruct (ap_done (astep p "010")) eqn:Hd; [contradiction H; reflexivity|].
    cbn [option_map wrap].
    destruct (ap_failed p) eqn:Fp; [rewrite (astep_failed p _ Fp), Fp; reflexivity|].
    cbn [ibreak_at]. unfold iattr_feed. change nl_char with "010"%char.
    destruct (ap_failed (astep p "010")); [reflexivity|].
    rewrite Hd. reflexivity.
  - destruct (ap_done (astep p "010")) eqn:Hd; [contradiction H; reflexivity|].
    cbn [option_map wrap].
    destruct (ap_failed p) eqn:Fp; [rewrite (astep_failed p _ Fp), Fp; reflexivity|].
    cbn [ibreak_at]. unfold ispan_feed. change nl_char with "010"%char.
    destruct (ap_failed (astep p "010")); [reflexivity|].
    rewrite Hd. reflexivity.
Qed.

Local Lemma ibreak_wrap : forall ws core,
  Forall (fun w => wstep nl_char w <> None) ws ->
  ibreak (wrap ws core) = wrap (map (wl_after nl) ws) (ibreak core).
Proof.
  induction ws as [|w ws IH]; intros core F; [reflexivity|].
  apply Forall_cons_iff in F as [Fw F].
  change (wrap (w :: ws) core) with (wrap [w] (wrap ws core)).
  rewrite (ibreak_layer w _ Fw), (IH core F). reflexivity.
Qed.

Local Lemma eo_vof : forall n, bare n -> eo (vof n) = OIn n.
Proof. intros [p [|kv a] x] H; cbn in H; subst p; reflexivity. Qed.

Local Lemma oemit_vof : forall n v,
  bare n -> (forall p s, n <> Node p [] (Str s)) ->
  oemit n (oview v) = oview (pv_add (vof n) v)
  /\ starts_text (top_of (pv_add (vof n) v)) = false.
Proof.
  intros n [[|f rest] out md] Bn Hn; unfold oemit, oview, pv_add, top_of;
    cbn [pv_stk pv_out os_stk os_out os_word_start map];
    rewrite (xsnoc_nonstr (vof n) _ (vof_nonstr n Hn)); cbn [map]; rewrite ?(eo_vof n Bn).
  - split; [reflexivity|].
    pose proof (vof_nonstr n Hn) as H. destruct (vof n) as [[]| |]; try reflexivity.
    destruct (H _ eq_refl).
  - split; [destruct f as [p [[k mr|] im'] c]; cbn [oframe fset fcontent map];
            rewrite (eo_vof n Bn); reflexivity|].
    destruct f; cbn [fset fcontent];
      pose proof (vof_nonstr n Hn) as H; destruct (vof n) as [[]| |]; try reflexivity;
      destruct (H _ eq_refl).
Qed.

(* Taking back the text before a bracket. *)
Local Lemma opop_sim : forall v,
  normal (top_of v) -> clean (top_of v) ->
  exists pre o1, opop_str (oview v) = (pre, o1) /\ sim v pre o1.
Proof.
  intros [stk out md] Hn Hc.
  assert (Tail : forall s l, normal (VIn (Str s) :: l) -> starts_text l = false).
  { intros s [|y l] H; [reflexivity|]. destruct H as [[H|H] _]; [discriminate|].
    destruct y as [[]| |]; try discriminate H; reflexivity. }
  assert (Head : forall s l, clean (VIn (Str s) :: l) -> nonempty_str s = true).
  { intros s l H. apply Forall_cons_iff in H as [H _]. destruct s; [contradiction|reflexivity]. }
  assert (Cons : forall s l, starts_text l = false -> xsnoc (Str s) l = VIn (Str s) :: l)
    by (intros s [|[[]| |] l] Hl; try reflexivity; discriminate).
  destruct stk as [|f rest]; cbn [top_of pv_stk pv_out fcontent] in Hn, Hc.
  - destruct out as [|x l].
    + exists "", (oview (PView [] [] md)). split; [reflexivity|].
      exists (PView [] [] md). split; [reflexivity|]. split; reflexivity.
    + destruct (str_view x) as [[s ->]|Hx].
      * exists s, (oview (PView [] l md)). split; [reflexivity|].
        exists (PView [] l md). split; [reflexivity|].
        split; [exact (Tail s l Hn)|].
        unfold add_text. rewrite (Head s l Hc). unfold pv_add. cbn [pv_stk pv_out pv_mode].
        rewrite (Cons s l (Tail s l Hn)). reflexivity.
      * exists "", (oview (PView [] (x :: l) md)).
        split; [dv x; [destruct (Hx _ eq_refl)|..]; reflexivity|].
        exists (PView [] (x :: l) md). split; [reflexivity|].
        split; [dv x; [destruct (Hx _ eq_refl)|..]; reflexivity|reflexivity].
  - destruct (fcontent f) as [|x l] eqn:Ef.
    + exists "", (oview (PView (f :: rest) out md)).
      split; [unfold opop_str, oview; cbn [os_stk map pv_stk]; rewrite fr_out_oframe, Ef; reflexivity|].
      exists (PView (f :: rest) out md). split; [reflexivity|].
      split; [cbn [top_of pv_stk]; rewrite Ef; reflexivity|reflexivity].
    + destruct (str_view x) as [[s ->]|Hx].
      * exists s, (oview (PView (fset f l :: rest) out md)).
        split; [destruct f as [p [[k mr|] im'] c]; cbn [fcontent] in Ef; subst c; reflexivity|].
        exists (PView (fset f l :: rest) out md). split; [reflexivity|].
        assert (El : fcontent (fset f l) = l) by (destruct f; reflexivity).
        split; [cbn [top_of pv_stk]; rewrite El; exact (Tail s l Hn)|].
        unfold add_text. rewrite (Head s l Hc). unfold pv_add. cbn [pv_stk pv_out pv_mode].
        rewrite El, (Cons s l (Tail s l Hn)).
        destruct f; cbn [fset fcontent] in *; subst; reflexivity.
      * exists "", (oview (PView (f :: rest) out md)).
        split; [unfold opop_str, oview; cbn [os_stk map pv_stk]; rewrite fr_out_oframe, Ef;
                dv x; [destruct (Hx _ eq_refl)|..]; reflexivity|].
        exists (PView (f :: rest) out md). split; [reflexivity|].
        split; [cbn [top_of pv_stk]; rewrite Ef;
                dv x; [destruct (Hx _ eq_refl)|..]; reflexivity|reflexivity].
Qed.

(* The `!` of an image's bracket that closes as a span, put back as
   text. *)
Local Lemma ospan_bang_view : forall im v,
  normal (top_of v) -> clean (top_of v) ->
  ospan_bang im null_span (oview v) = oview (if im then pv_add (Str (one bang)) v else v).
Proof.
  intros [|] v Hn Hc; [|reflexivity].
  destruct (opop_sim v Hn Hc) as (pre & o1 & Ep & S1).
  destruct (sim_text _ _ _ (one bang) S1 eq_refl) as (v0 & -> & Ht & Ev).
  unfold ospan_bang. rewrite Ep.
  change (@flush_text_to_at semantic_pos semantic_inline_cursor ?st ?t ?o) with (flush_text t o).
  rewrite Ev. apply flush_view, Ht.
Qed.

Local Lemma sim_finish : forall v txt prev o,
  sim v txt o ->
  normal (pflatten_go [] (pv_stk v) (pv_out v)) ->
  ifinish (IText false txt prev o) = vres (pflatten_go [] (pv_stk v) (pv_out v)).
Proof.
  intros v txt prev o (v0 & -> & Ht & ->) Nf. apply ifinish_view; [exact Ht|exact Nf].
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


(* What the byte before allows: what may follow it, and after a `[` no
   `^`, which a footnote reference has already taken with its `[`, or
   which `note_ok` admits on its own. *)
Definition prev_ok (prev : option ascii) (s : string) : bool :=
  match prev with
  | Some p => (follow_ok p s && negb (Ascii.eqb p lbrack && starts_with hat s))%bool
  | None => true
  end.

Local Lemma prev_ok_plain : forall p s, Ascii.eqb p lbrack = false -> prev_ok (Some p) s = true.
Proof. intros p s H. unfold prev_ok, follow_ok. rewrite H. reflexivity. Qed.

Local Lemma prev_ok_follow : forall c s,
  follow_ok c s = true -> Ascii.eqb c lbrack = false -> prev_ok (Some c) s = true.
Proof. intros c s H E. cbn [prev_ok]. rewrite H, E. reflexivity. Qed.

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

Local Lemma ws_prev_ok : forall x s, is_ws x = true -> prev_ok (Some x) s = true.
Proof.
  intros x s H. apply prev_ok_follow; [apply ws_follow, H|].
  destruct (Ascii.eqb x lbrack) eqn:E; [|reflexivity].
  apply Ascii.eqb_eq in E. subst x. discriminate H.
Qed.

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

(* Right after a `[`, a `^` would mark a footnote and, with wikilinks
   on, a `[` a wikilink; `prev_ok` has neither there. *)
Local Lemma note_free : forall prev c s' txt,
  prev_ok prev (String c s') = true -> (c = lbrack /\ wikilinks_enabled = true) \/ c = hat ->
  note_pos txt prev = false.
Proof.
  intros prev c s' txt H Hc. unfold note_pos.
  destruct prev as [p|]; [|apply andb_false_r].
  destruct (Ascii.eqb p lbrack) eqn:E; [|apply andb_false_r]. exfalso.
  cbn [prev_ok] in H. apply andb_true_iff in H as [H Hh]. rewrite E in Hh.
  destruct Hc as [[-> Hw] | ->]; [|discriminate Hh].
  unfold follow_ok in H. rewrite E, Hw in H. discriminate H.
Qed.

(* A `[` right after a `[` is a wikilink's only with wikilinks on. *)
Local Lemma wiki_free : forall prev s' txt,
  prev_ok prev (String lbrack s') = true -> (note_pos txt prev && wikilinks_enabled)%bool = false.
Proof.
  intros prev s' txt H. destruct wikilinks_enabled eqn:Hw; [|apply andb_false_r].
  rewrite (note_free prev lbrack s' txt H (or_introl (conj eq_refl Hw))). reflexivity.
Qed.

(* A `[` with nothing yet read after it would make a `^` a footnote's: the
   byte before the line, or the text the scanner holds, rules that out,
   or else the `^` is one whose label never closes in the rest of the
   paragraph, `rest`.  So would a `[` a wikilink's, which the alphabet
   rules out. *)
Definition note_ok (prev : option ascii) (core : iscan) (s rest : string) : Prop :=
  prev_ok prev s = true
  \/ (forall txt p o, core = IText false txt p o -> nonempty_str txt = true)
  \/ (exists im o r, core = IText false "" (Some lbrack) (bpush im o) /\ rest = String hat r
        /\ (notes_enabled = true -> note_go false r = None)).

Local Lemma note_free' : forall prev s' txt p o after,
  note_ok prev (IText false txt p o) (String lbrack s') (String lbrack s' ++ after) ->
  wikilinks_enabled = true -> note_pos txt prev = false.
Proof.
  intros prev s' txt p o after [H|[H|(im & o1 & r & _ & E & _)]] Hw.
  - exact (note_free prev lbrack s' txt H (or_introl (conj eq_refl Hw))).
  - unfold note_pos. tred. rewrite (H txt p o eq_refl). reflexivity.
  - discriminate E.
Qed.

(* A byte the scanner reads with no footnote in sight, or the `^` of a
   footnote whose label never closes, which opens the label's layer. *)
Local Lemma no_note_ok' : forall prev c s' txt o after,
  note_ok prev (IText false txt prev o) (String c s') (String c s' ++ after) ->
  no_note c txt prev = true
  \/ (c = hat /\ notes_enabled = true /\ txt = "" /\ prev = Some lbrack
      /\ exists im o1, o = bpush im o1 /\ note_go false (s' ++ after) = None).
Proof.
  intros prev c s' txt o after H. unfold no_note.
  destruct (Ascii.eqb c hat) eqn:E; [|left; reflexivity].
  apply Ascii.eqb_eq in E. subst c.
  destruct notes_enabled eqn:Hen; [|left; rewrite !andb_false_r; reflexivity].
  destruct H as [H|[H|(im & o1 & r & Ec & Er & Hr)]].
  - left. rewrite (note_free prev hat s' txt H (or_intror eq_refl)). reflexivity.
  - left. unfold note_pos. tred. rewrite (H txt prev o eq_refl). reflexivity.
  - right. injection Ec as -> <- ->. cbn [append] in Er. injection Er as <-.
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    exists im, o1. split; [reflexivity|exact (Hr Hen)].
Qed.

Local Lemma ilead_lbrack : forall txt prev o,
  (note_pos txt prev && wikilinks_enabled)%bool = false ->
  ilead lbrack txt prev o = IText false "" (Some lbrack) (bpush false (flush_text txt o)).
Proof. intros txt prev o H. unfold ilead, itable. cbn. rewrite H. reflexivity. Qed.

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

Local Lemma pv_add_items_out : forall xs v,
  Forall (fun x : inline => VIn x <> VIn (Str "")) xs ->
  normal (pv_out v) -> clean (pv_out v) ->
  normal (pv_out (pv_add_items xs v)) /\ clean (pv_out (pv_add_items xs v)).
Proof.
  induction xs as [|x xs IH]; intros v Hx N C; [split; assumption|].
  apply Forall_cons_iff in Hx as [Hx Hxs]. apply IH; [exact Hxs| |];
    destruct (pv_add_out x v) as [H|H]; rewrite H;
    [exact N|apply normal_xsnoc, N|exact C|apply clean_xsnoc; assumption].
Qed.

(* The outermost content stays normal and clean. *)
Local Lemma pstep_out : forall ps n h t v,
  ~ empty_run t -> normal (pv_out v) -> clean (pv_out v) ->
  normal (pv_out (pstep ps n h t v)) /\ clean (pv_out (pstep ps n h t v)).
Proof.
  intros ps n h t v H0 N0 C0.
  assert (Add : forall (x : vitem) v', x <> VIn (Str "") -> normal (pv_out v') -> clean (pv_out v') ->
            normal (pv_out (pv_add x v')) /\ clean (pv_out (pv_add x v'))).
  { intros x v' Hx N C. destruct (pv_add_out x v') as [H|H]; rewrite H;
      [split; assumption|split; [apply normal_xsnoc, N|apply clean_xsnoc; assumption]]. }
  assert (Txt : forall t', (forall d m b c r, t' <> TVerb d m b c r) -> ~ empty_run t' ->
                 VIn (Str (tok_text t')) <> VIn (Str ""))
    by (intros t' Hv Hd E; injection E as E; exact (tok_text_ne t' Hv Hd E)).
  assert (Open : forall i k op txt, txt <> "" ->
            normal (pv_out (popen i k op txt v)) /\ clean (pv_out (popen i k op txt v))).
  { intros i k [|] txt Hne; [split; assumption|apply Add; [|exact N0|exact C0]].
    apply kdecay_ne, Hne. }
  unfold pstep.
  destruct t as [c| |k mr op cl|oi|b rg|c|ws|ws|vp vn vb vc vr|dk|asrc|sa|ab aa|sb sa'|nl|dn|hn].
  - apply Add; [discriminate|exact N0|exact C0].
  - destruct h; [split; assumption|apply Add; [discriminate|exact N0|exact C0]].
  - cbv zeta.
    pose proof (delim_lit_ne k mr op (at_rbrace (get (tok_end ps n) ps))) as Hl.
    destruct (if cl then pick (KDelim k mr) (pv_live v) else PNone) as [p below|];
      [|apply Open, Hl].
    destruct (Nat.ltb (tok_end ps p) n); [|apply Open, Hl].
    destruct (pclose_go (KDelim k mr) [] (pv_stk v)) as [[content rest]|]; [|split; assumption].
    apply Add; [apply vin_nonstr, dnode_nonstr|exact N0|exact C0].
  - apply Open. destruct oi; discriminate.
  - destruct (pick KBracket (pv_live v));
      destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|];
      try (apply Add; [apply Txt; norun|exact N0|exact C0]).
    split; assumption.
  - apply Add; [|exact N0|exact C0]. intros E. injection E as E.
    unfold esc_text in E. destruct (is_punct c); discriminate.
  - destruct (nbsp_rest ws) as [r|]; [|apply Add; [apply (Txt (TEscWs ws)); norun|exact N0|exact C0]].
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
    apply Add; [apply vin_nonstr, verb_node_nonstr|exact (proj1 A1)|exact (proj2 A1)].
  - apply Add; [apply Txt; [discriminate|exact H0]|exact N0|exact C0].
  - apply Add; [apply vin_nonstr, auto_node_nonstr|exact N0|exact C0].
  - apply Add; [discriminate|exact N0|exact C0].
  - split; assumption.
  - destruct (pick KBracket (pv_live v));
      destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|];
      try (apply Add; [discriminate|exact N0|exact C0]).
    split; assumption.
  - split; assumption.
  - apply pv_add_items_out; [|exact N0|exact C0].
    apply dots_items_ne. intros ->. apply H0. right. left. reflexivity.
  - apply pv_add_items_out; [|exact N0|exact C0].
    apply dash_items_ne. intros ->. apply H0. right. right. reflexivity.
Qed.

Local Lemma pstep_atom : forall ps n h t v,
  pv_mode v = PMNormal -> atom_ok (pstep ps n h t v).
Proof.
  intros ps n h t v Em. unfold atom_ok.
  destruct t as [c| |k mr op cl|oi|b rg|c|ws|ws|vp vn vb vc vr|dk|asrc|sa|ab aa|sb sa'|nl|dn|hn];
    try (rewrite pstep_mode by (assumption || discriminate); exact Logic.I).
  - destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|] eqn:Hc.
    + rewrite (pstep_close_found ps n h b rg v content rest Hc). exact Logic.I.
    + rewrite pstep_close_none by exact Hc. rewrite (proj2 (pv_add_live _ _)), Em. exact Logic.I.
  - unfold pstep. destruct (Nat.ltb _ _); cbn [pv_mode pv_setmode];
      [apply vin_nonstr; intros s; apply verb_node_nonstr
      |rewrite (proj2 (pv_add_live _ _)), (proj2 (add_text_live _ _)), Em; exact Logic.I].
  - cbn [pstep pv_mode pv_setmode]. discriminate.
  - destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest]|] eqn:Hc.
    + rewrite (pstep_span_found ps n h _ _ v content rest Hc). exact Logic.I.
    + rewrite (pstep_span_none ps n h _ _ v Hc), (proj2 (pv_add_live _ _)), Em. exact Logic.I.
  - cbn [pstep pv_mode pv_setmode]. discriminate.
Qed.

Local Lemma pstep_tidy : forall ps n h t v,
  ~ empty_run t -> pv_mode v = PMNormal -> tidy v -> tidy (pstep ps n h t v).
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

(* The `!` a span's image bracket leaves as text. *)
Local Lemma pv_bang : forall (im : bool) v,
  let w := if im then pv_add (Str (one bang)) v else v in
  pv_mode w = pv_mode v /\ (normal (pv_out v) -> normal (pv_out w))
  /\ (clean (pv_out v) -> clean (pv_out w)).
Proof.
  intros [|] v; cbn zeta; [|auto].
  split; [apply pv_add_live|].
  destruct (pv_add_out (Str (one bang)) v) as [H|H]; rewrite H; split; auto.
  - apply normal_xsnoc.
  - intros Hc. apply clean_xsnoc; [discriminate|exact Hc].
Qed.

Local Lemma pbyte_tidy : forall i c v, tidy v -> tidy (pbyte i c v).
Proof.
  intros i c v (Hn & Hc & Fn & Fc & A).
  assert (Ao : atom_ok (pbyte i c v)).
  { unfold atom_ok, pbyte in *. destruct (pv_mode v) as [|b im kids d e txt|x e|im sk sat se] eqn:Em.
    - rewrite Em. exact Logic.I.
    - destruct (Nat.eqb i e).
      + rewrite (proj2 (pv_add_live _ _)). exact Logic.I.
      + exact Logic.I.
    - destruct (Nat.eqb i e); [rewrite (proj2 (pv_add_live _ _)); exact Logic.I|rewrite Em; exact A].
    - destruct (Nat.eqb i se); [|rewrite Em; exact Logic.I].
      rewrite (proj2 (pv_add_live _ _)). cbn zeta.
      rewrite (proj1 (pv_bang im (pv_setmode PMNormal v))). exact Logic.I. }
  split; [|split; [|split; [apply pbyte_normal, Fn|split; [apply pbyte_clean; assumption|exact Ao]]]];
    unfold atom_ok, pbyte in *; destruct (pv_mode v) as [|b im kids d e txt|x e|im sk sat se]; try assumption.
  - destruct (Nat.eqb i e); [|assumption].
    destruct (pv_add_out (region_node b im kids (if b then dest_text false txt else txt))
                (pv_setmode PMNormal v)) as [H|H]; rewrite H; [assumption|apply normal_xsnoc, Hn].
  - destruct (Nat.eqb i e); [|assumption].
    destruct (pv_add_out x (pv_setmode PMNormal v)) as [H|H]; rewrite H; [assumption|apply normal_xsnoc, Hn].
  - destruct (Nat.eqb i se); [|assumption]. cbn zeta.
    pose proof (proj1 (proj2 (pv_bang im (pv_setmode PMNormal v))) Hn) as Hn'. cbn zeta in Hn'.
    destruct (pv_add_out (vof (Node NoPos sat (Span EmptyString sk)))
                (if im then pv_add (Str (one bang)) (pv_setmode PMNormal v)
                 else pv_setmode PMNormal v))
      as [H|H]; rewrite H; [assumption|apply normal_xsnoc, Hn'].
  - destruct (Nat.eqb i e); [|assumption].
    destruct (pv_add_out (region_node b im kids (if b then dest_text false txt else txt))
                (pv_setmode PMNormal v)) as [H|H]; rewrite H;
      [assumption|apply clean_xsnoc; [apply vin_nonstr, region_node_nonstr|exact Hc]].
  - destruct (Nat.eqb i e); [|assumption].
    destruct (pv_add_out x (pv_setmode PMNormal v)) as [H|H]; rewrite H;
      [assumption|apply clean_xsnoc; [apply A|exact Hc]].
  - destruct (Nat.eqb i se); [|assumption]. cbn zeta.
    pose proof (proj2 (proj2 (pv_bang im (pv_setmode PMNormal v))) Hc) as Hc'. cbn zeta in Hc'.
    destruct (pv_add_out (vof (Node NoPos sat (Span EmptyString sk)))
                (if im then pv_add (Str (one bang)) (pv_setmode PMNormal v)
                 else pv_setmode PMNormal v))
      as [H|H]; rewrite H; [assumption|apply clean_xsnoc; [destruct sat; discriminate|exact Hc']].
Qed.

(*
Tokens of a line
----------------
*)

Local Lemma dchar_nl : forall k, Ascii.eqb (dchar k) nl_char = false.
Proof. intros k. apply Ascii.eqb_neq, dchar_not_nl. Qed.

Local Lemma dchar_tick : forall k, is_tick (dchar k) = false.
Proof. intros k. exact (proj1 (proj2 (dreserved_false _ (dchar_free k)))). Qed.

Local Lemma dchar_lt : forall k, Ascii.eqb (dchar k) lt = false.
Proof.
  intros k. pose proof (dreserved_false _ (dchar_free k)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H).
  exact H.
Qed.

Local Lemma dchar_colon : forall k, Ascii.eqb (dchar k) ":"%char = false.
Proof.
  intros k. pose proof (dchar_free k) as H. unfold dreserved in H.
  repeat (apply orb_false_iff in H as [H ?]). assumption.
Qed.

Local Lemma dchar_period : forall k, Ascii.eqb (dchar k) period = false.
Proof.
  intros k. pose proof (dchar_free k) as H. unfold dreserved in H.
  repeat (apply orb_false_iff in H as [H ?]). assumption.
Qed.

Local Lemma dchar_bang : forall k, Ascii.eqb (dchar k) bang = false.
Proof.
  intros k. pose proof (dchar_free k) as H. unfold dreserved in H.
  repeat (apply orb_false_iff in H as [H ?]). assumption.
Qed.

Local Lemma dchar_dollar : forall k, Ascii.eqb (dchar k) dollar = false.
Proof.
  intros k. pose proof (dreserved_false _ (dchar_free k)) as (_ & _ & _ & _ & _ & _ & _ & H & _).
  exact H.
Qed.

(* A token with no `}` after it. *)
Local Lemma nt_token : forall k prev rest,
  dstyle_of (dchar k) = Some k -> at_rbrace (get 0 rest) = false ->
  Ascii.eqb (dchar k) hyphen = false ->
  next_tok prev (dtoken k ++ rest)
  = Some (TDelim k false (dbare k prev && nonspace_at (get 0 rest)) (nonspace_at prev), dwidth k).
Proof.
  intros k prev rest Hk Hr Hhy. destruct (dchar_plain k) as (Hlb & _ & Hlk & Hrk).
  assert (Hpre : prefix (dtoken k) (dtoken k ++ rest) = true) by (apply prefix_chars; lia).
  destruct (dtoken_cons k) as (w & Ew & Ed).
  rewrite Ed at 1. cbn [append next_tok]. unfold delim_tok. rewrite dchar_nl, dchar_nb, dchar_tick, dchar_dollar, dchar_lt, dchar_colon, dchar_period, Hhy, dchar_bang, Hlk, Hrk, Hlb, Hk.
  replace (String (dchar k) (chars (dchar k) w ++ rest))
    with (dtoken k ++ rest)%string by (rewrite Ed; reflexivity).
  rewrite Hpre. unfold dtoken. rewrite Ew, get_chars, Hr. reflexivity.
Qed.

Local Lemma nt_marked_close : forall k prev r,
  dstyle_of (dchar k) = Some k -> Ascii.eqb (dchar k) hyphen = false ->
  next_tok prev (dtoken k ++ String rbrace r) = Some (TDelim k true false true, S (dwidth k)).
Proof.
  intros k prev r Hk Hhy. destruct (dchar_plain k) as (Hlb & _ & Hlk & Hrk).
  assert (Hpre : prefix (dtoken k) (dtoken k ++ String rbrace r) = true)
    by (apply prefix_chars; lia).
  destruct (dtoken_cons k) as (w & Ew & Ed).
  rewrite Ed at 1. cbn [append next_tok]. unfold delim_tok. rewrite dchar_nl, dchar_nb, dchar_tick, dchar_dollar, dchar_lt, dchar_colon, dchar_period, Hhy, dchar_bang, Hlk, Hrk, Hlb, Hk.
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
  cbn [next_tok]. unfold lbrace_tok. change (Ascii.eqb lbrace nl_char) with false.
  change (is_bslash lbrace) with false. change (is_tick lbrace) with false. try change (Ascii.eqb lbrace dollar) with false.
  try change (Ascii.eqb lbrace lt) with false. try change (Ascii.eqb lbrace ":"%char) with false.
  change (Ascii.eqb lbrace period) with false. change (Ascii.eqb lbrace hyphen) with false.
  change (Ascii.eqb lbrace bang) with false.
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
  (forall d r, rest = String d r -> d <> dchar k) -> Ascii.eqb (dchar k) hyphen = false ->
  next_tok prev (String (dchar k) (chars (dchar k) j ++ rest)) = Some (TText (dchar k), 1).
Proof.
  intros k j prev rest Hk Hj Hr Hhy. destruct (dchar_plain k) as (Hlb & _ & Hlk & Hrk).
  cbn [next_tok]. unfold delim_tok. rewrite dchar_nl, dchar_nb, dchar_tick, dchar_dollar, dchar_lt, dchar_colon, dchar_period, Hhy, dchar_bang, Hlk, Hrk, Hlb, Hk.
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
  cbn [next_tok]. unfold lbrace_tok. change (Ascii.eqb lbrace nl_char) with false.
  change (is_bslash lbrace) with false. change (is_tick lbrace) with false. try change (Ascii.eqb lbrace dollar) with false.
  try change (Ascii.eqb lbrace lt) with false. try change (Ascii.eqb lbrace ":"%char) with false.
  change (Ascii.eqb lbrace period) with false. change (Ascii.eqb lbrace hyphen) with false.
  change (Ascii.eqb lbrace bang) with false.
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
  Ascii.eqb c dollar = false -> Ascii.eqb c lt = false -> Ascii.eqb c ":"%char = false ->
  Ascii.eqb c period = false -> Ascii.eqb c hyphen = false -> Ascii.eqb c bang = false ->
  Ascii.eqb c lbrack = false -> Ascii.eqb c rbrack = false ->
  Ascii.eqb c lbrace = false -> dstyle_of c = None ->
  next_tok prev (String c rest) = Some (TText c, 1).
Proof.
  intros c prev rest H H0 Ht Hdl Hlt' Hco Hpd Hhy Hbg H1 H2 H3 H4. cbn [next_tok]. unfold delim_tok.
  rewrite H, H0, Ht, Hdl, Hlt', Hco, Hpd, Hhy, Hbg, H1, H2, H3, H4.
  reflexivity.
Qed.


Local Lemma rbrack_tok_shape : forall s,
  (exists b r, rbrack_tok s = (TClose b r, 1))
  \/ (exists b a, rbrack_tok s = (TSpan b a, 1)) \/ rbrack_tok s = (TText rbrack, 1).
Proof.
  intros [|c r]; [right; right; reflexivity|]. unfold rbrack_tok. cbv zeta.
  destruct (Ascii.eqb c lparen);
    [destruct (dest_close false 0 0 r); [left; eauto|right; right; reflexivity]|].
  destruct (Ascii.eqb c lbrack);
    [destruct (label_close false 0 r); [left; eauto|right; right; reflexivity]|].
  destruct (Ascii.eqb c lbrace);
    [destruct (spec_at r) as [[b a]|]; [right; left; eauto|right; right; reflexivity]|].
  right; right; reflexivity.
Qed.

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
  intros p s H. cbn [next_tok]. unfold esc_tok. change (Ascii.eqb bslash nl_char) with false.
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
  cbn [ticks iscan_str]. unfold istep. cbn [istep_at]. unfold ilead, itable.
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
  - cbn [chars iscan_str]. unfold istep. cbn [istep_at]. unfold ilead, itable.
    change (is_bslash dollar) with false. change (is_tick dollar) with false.
    rewrite Ascii.eqb_refl. reflexivity.
  - cbn [chars iscan_str]. unfold istep at 2. cbn [istep_at]. unfold ilead, itable.
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




Local Lemma iscan_raw_fmt : forall f spec t o, fmt_ok f = true -> spec <> EmptyString ->
  forall j sh, iscan_str (substring 0 j f) (IRaw spec t sh o)
               = IRaw (spec ++ substring 0 j f) t (iscan_str (substring 0 j f) sh) o.
Proof.
  induction f as [|c f IH]; intros spec t o Ok Hs j sh.
  - destruct j; cbn; rewrite append_empty_r; reflexivity.
  - destruct j as [|j]; [cbn; rewrite append_empty_r; reflexivity|].
    cbn [fmt_ok] in Ok. apply andb_true_iff in Ok as [Ok Okf]. apply andb_true_iff in Ok as [Eb Es].
    apply negb_true_iff in Eb, Es.
    cbn [substring iscan_str]. unfold istep at 1. cbn [istep_at]. unfold iraw_step.
    rewrite Eb, andb_false_r. cbn [andb].
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
     exists spec sh,
       iscan_str (substring 0 j (String lbrace (String eqchar f))) (IVerb m m b VVerb o)
       = IRaw spec (trim_verb b) sh o /\ (spec = EmptyString -> j = 1))
  /\ iscan_str (String lbrace (String eqchar f) ++ one rbrace) (IVerb m m b VVerb o)
     = IText false "" (Some rbrace) (oemit (mk (RawInline f (trim_verb b))) o).
Proof.
  intros m b o f Ok Hf Hr.
  set (sh0 := IBrace "" (Some tick)
                 (oemit (imk (text_start o) cursor_start (Verbatim (trim_verb b))) o)).
  assert (S1 : istep lbrace (IVerb m m b VVerb o) = IRaw "" (trim_verb b) sh0 o).
  { unfold istep. cbn [istep_at]. change (is_tick lbrace) with false. rewrite Nat.eqb_refl.
    reflexivity. }
  assert (S2 : forall sh, istep eqchar (IRaw "" (trim_verb b) sh o)
                          = IRaw (one eqchar) (trim_verb b) (istep eqchar sh) o).
  { intros sh. unfold istep at 1. cbn [istep_at]. unfold iraw_step.
    change (Ascii.eqb eqchar rbrace) with false. rewrite andb_false_r. reflexivity. }
  split.
  - intros [|[|j]] Hj; [lia| |].
    + exists "", sh0. cbn [substring iscan_str]. rewrite S1. split; reflexivity.
    + cbn [substring iscan_str]. rewrite S1, S2.
      rewrite iscan_raw_fmt by (exact Ok || discriminate). do 2 eexists.
      split; [reflexivity|intros E; discriminate E].
  - cbn [append iscan_str]. rewrite S1, S2.
    pose proof (iscan_raw_fmt f (one eqchar) (trim_verb b) o Ok ltac:(discriminate) (String.length f))
      as E.
    rewrite <- (Nat.sub_0_r (String.length f)), substring_rest in E. cbn [sdrop] in E.
    rewrite iscan_str_app, E.
    change (one rbrace) with (String rbrace ""). cbn [iscan_str]. unfold istep at 1. cbn [istep_at].
    unfold iraw_step. change (Ascii.eqb rbrace rbrace) with true.
    replace (raw_spec_ok (tval (one eqchar ++ f))) with true
      by (destruct f; [contradiction|reflexivity]).
    rewrite Hr. reflexivity.
Qed.

Local Lemma tok_at_verb : forall ps p d m body cl r l,
  tok_at ps p = Some (TVerb d m body cl r, l) ->
  exists w, sdrop p ps = (chars dollar d ++ w)%string /\ starts_tick w = true
    /\ verb_tok d w = (TVerb d m body cl r, l - d) /\ d < l /\ (d = 0 \/ math_enabled = true).
Proof.
  intros ps p d m body cl r l H.
  unfold tok_at, next_tok, esc_tok, dots_tok, dash_tok, bang_tok, lbrack_tok, rbrack_tok, lbrace_tok, delim_tok in H. destruct (sdrop p ps) as [|c r0] eqn:Es; [discriminate|].
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
  destruct (Ascii.eqb c lt).
  { destruct (auto_tok_shape r0) as [(? & ? & E)|E]; rewrite E in H; discriminate H. }
  destruct (Ascii.eqb c ":"%char).
  { destruct (sym_tok_shape r0) as [(? & ? & E)|E]; rewrite E in H; discriminate H. }
  exfalso. repeat match type of H with
  | context [if ?b then _ else _] => destruct b
  | context [match ?x with Some _ => _ | None => _ end] => destruct x
  | context [match ?x with EmptyString => _ | String _ _ => _ end] => destruct x
  | context [match ?x with O => _ | S _ => _ end] => destruct x
  | context [match ?x with pair _ _ => _ end] => destruct x
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
  - cbn [chars iscan_str ticks]. unfold istep. cbn [istep_at]. unfold ilead, itable.
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
  | IRaw spec _ _ _ => exists c, next = Some c /\ c <> nl_char /\ (spec = EmptyString -> c = eqchar)
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
          as (spec & sh & Esp' & He).
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
An attribute spec, scanned
--------------------------

The scanner reads a spec with the machine the lexer uses, beside the
ordinary reading of the same bytes; a spec that closes discards that
reading and leaves a mark in the scope.  The view reads a spec that
closes byte by byte, as a token of several bytes whose item is the mark
(`attr_in`).
*)

Local Lemma omark_view : forall a v,
  omark a null_span (oview v) = oview (pv_add (VMark a) v).
Proof.
  intros a [[|f rest] out md]; unfold omark, oview, pv_add;
    cbn [pv_stk pv_out os_stk os_out os_word_start map];
    rewrite (xsnoc_nonstr (VMark a)) by (intros s E; discriminate E); [reflexivity|].
  destruct f as [p [[k mr|] im'] c]; reflexivity.
Qed.

Local Lemma top_add_mark : forall a v, starts_text (top_of (pv_add (VMark a) v)) = false.
Proof.
  intros a [[|f rest] out md]; unfold pv_add, top_of; cbn [pv_stk pv_out];
    [|destruct f; cbn [fset fcontent]];
    rewrite (xsnoc_nonstr (VMark a)) by (intros s E; discriminate E); reflexivity.
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
  starts_with bang s = false -> starts_with lbrack s = false ->
  starts_with lbrace s = false \/ starts_row (sdrop 1 s) = true -> starts_with rbrack s = false ->
  no_char nl_char s = true -> same_prev (before ps n) prev ->
  tok_at ps n = next_tok prev s.
Proof.
  intros ps n s after prev Hs Ha Hne Htk Hdl Hbg Hlk Hlb Hrb Hn Hp. unfold tok_at. rewrite Hs.
  rewrite (next_tok_after _ s after Hn Ha Hne Htk Hdl Hbg Hlk Hlb Hrb).
  apply next_tok_prev, Hp.
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

(* So does a label's that never closes. *)
Local Lemma note_go_app : forall a b esc lab,
  note_go esc (a ++ b) = None ->
  exists ns, nfeed a (NS esc lab) = Some ns /\ note_go (ns_esc ns) b = None.
Proof.
  induction a as [|c a IH]; intros b esc lab H.
  - exists (NS esc lab). split; [reflexivity|exact H].
  - cbn [append note_go] in H. cbn [nfeed]. unfold nstep. cbn [ns_esc ns_lab].
    destruct esc.
    { apply IH. destruct (note_go false (a ++ b)); [discriminate|reflexivity]. }
    destruct (is_bslash c).
    { apply IH. destruct (note_go true (a ++ b)); [discriminate|reflexivity]. }
    destruct (Ascii.eqb c rbrack); [discriminate|].
    apply IH. destruct (note_go false (a ++ b)); [discriminate|reflexivity].
Qed.

(* So does a spec's, until its machine fails, and after. *)
Local Lemma spec_go_failed : forall s p, ap_failed p = true -> spec_go p s = None.
Proof.
  induction s as [|c s IH]; intros p H; [reflexivity|]. cbn [spec_go].
  rewrite (astep_failed p c H), H. reflexivity.
Qed.

Local Lemma spec_go_app : forall a b p,
  spec_go p (a ++ b) = None -> exists p', sfeed a p = Some p' /\ spec_go p' b = None.
Proof.
  induction a as [|c a IH]; intros b p H; [exists p; split; [reflexivity|exact H]|].
  cbn [append spec_go] in H. cbn [sfeed]. unfold sstep.
  destruct (ap_failed (astep p c)) eqn:Ef.
  - assert (Ed : ap_done (astep p c) = false)
      by (destruct (astep p c) as [[] ? ? ?]; try discriminate Ef; reflexivity).
    rewrite Ed. apply IH. exact (spec_go_failed _ _ Ef).
  - destruct (ap_done (astep p c)); [discriminate H|]. apply IH.
    destruct (spec_go (astep p c) (a ++ b)) as [[]|]; [discriminate H|reflexivity].
Qed.

(* A layer whose reading the rest of the paragraph never closes. *)
Definition never (ps : string) (n : nat) (w : wlayer) : Prop :=
  match w with
  | WDest _ _ _ ds _ => dest_close (ds_esc ds) (ds_depth ds) n (sdrop n ps) = None
  | WRef _ _ _ ns _ | WNote _ _ ns _ => note_go (ns_esc ns) (sdrop n ps) = None
  | WAttr p _ _ _ _ | WSpan _ _ _ p _ _ => spec_go p (sdrop n ps) = None
  end.

Local Lemma layers_pass : forall ps n ws bytes r,
  Forall (never ps n) ws -> sdrop n ps = (bytes ++ r)%string ->
  Forall (fun w => wfeed bytes w <> None) ws
  /\ Forall (never ps (n + String.length bytes)) (map (wl_after bytes) ws).
Proof.
  intros ps n ws bytes r F Hs.
  pose proof (sdrop_app_tail ps n bytes r Hs) as Hs'.
  assert (G : forall w, In w ws ->
            exists w', wfeed bytes w = Some w' /\ never ps (n + String.length bytes) w').
  { intros w Hw. rewrite Forall_forall in F. specialize (F _ Hw).
    destruct w as [k wi o [e d dst] o'|k wi o [e lab] o'|wi o [e lab] o'|p src txt prev o|k wi op p src o];
      unfold never in F |- *; rewrite Hs in F; cbn [ds_esc ds_depth ns_esc] in F.
    - destruct (dest_close_app bytes r e d n dst F) as (ds & E1 & E2).
      exists (WDest k wi o ds o'). rewrite wfeed_dest, E1. split; [reflexivity|].
      cbn. rewrite Hs'. exact E2.
    - destruct (note_go_app bytes r e lab F) as (ns & E1 & E2).
      exists (WRef k wi o ns o'). rewrite wfeed_ref, E1. split; [reflexivity|].
      cbn. rewrite Hs'. exact E2.
    - destruct (note_go_app bytes r e lab F) as (ns & E1 & E2).
      exists (WNote wi o ns o'). rewrite wfeed_note, E1. split; [reflexivity|].
      cbn. rewrite Hs'. exact E2.
    - destruct (spec_go_app bytes r p F) as (p' & E1 & E2).
      exists (WAttr p' (src ++ bytes) txt prev o). rewrite wfeed_attr, E1.
      split; [reflexivity|]. cbn. rewrite Hs'. exact E2.
    - destruct (spec_go_app bytes r p F) as (p' & E1 & E2).
      exists (WSpan k wi op p' (src ++ bytes) o). rewrite wfeed_span, E1.
      split; [reflexivity|]. cbn. rewrite Hs'. exact E2. }
  split.
  - rewrite Forall_forall. intros w Hw E. destruct (G w Hw) as (w' & E1 & _). congruence.
  - rewrite Forall_map, Forall_forall. intros w Hw. destruct (G w Hw) as (w' & E1 & E2).
    unfold wl_after. rewrite E1. exact E2.
Qed.

Definition vinv (ps : string) (n : nat) (h : bool) (v : pview) : Prop :=
  pv_ok ps n v /\ tidy v /\ (h = true -> top_filled v).

(* The backslash a region's reading holds, which escapes the next byte. *)
Definition pend_esc (core : iscan) : bool :=
  match core with
  | IDest _ _ _ e _ _ _ _ => e
  | IReference _ _ _ e _ _ _ => e
  | INote e _ _ _ _ _ => e
  | _ => false
  end.

Definition with_esc (e : bool) (s : string) : string :=
  if e then String bslash s else s.

(* Inside a footnote reference's label, past its `[^`: the label so far
   and the backslash the scanner holds, against the rest of the label the
   reading has, with an image's `!` before the bracket already put back.
   The ordinary reading the scanner holds beside the label is dropped at
   the `]`. *)
Definition note_in (ps : string) (n : nat) (v : pview) (x : vitem) (e : nat) (core : iscan)
  : Prop :=
  exists esc im lab sh o r,
    core = INote esc im lab null_span sh o /\ ospan_bang im null_span o = oview v
    /\ note_go esc (sdrop n ps) = Some r /\ e = n + String.length r
    /\ x = FootnoteReference (normalize_label (lab ++ with_esc esc r)).

(* Inside an attribute spec that closes, past its `{`: the scanner reads
   it with the attribute machine, and the mark it leaves goes after the
   text it held at the `{`.  The ordinary reading beside the spec is
   dropped at the `}`. *)
Definition attr_in (ps : string) (n : nat) (v : pview) (x : vitem) (e : nat) (core : iscan)
  : Prop :=
  exists p src txt prev sh o b a,
    core = IAttr p src txt prev sh o /\ flush_text txt o = oview v
    /\ ap_done p = false /\ spec_go p (sdrop n ps) = Some (b, a) /\ e = n + String.length b
    /\ x = VMark a.

(* The same inside a span's spec, past its `{`, with the bracket the span
   closes already taken off the scope. *)
Definition span_in (ps : string) (n : nat) (v : pview) (im : bool) (kids : inlines) (a : attr)
  (e : nat) (core : iscan) : Prop :=
  Forall bare kids /\ exists p src open b sh,
    ap_done p = false /\ spec_go p (sdrop n ps) = Some (b, a) /\ e = n + String.length b
    /\ core = ISpan kids im open p src sh (oview v).

Definition linked (ps : string) (n : nat) (h : bool) (v : pview) (prev : option ascii)
  (core : iscan) : Prop :=
  match pv_mode v with
  | PMNormal =>
      h = false /\ exists txt o, core = IText false txt prev o /\ sim v txt o
  | PMRegion false im kids d e label =>
      S d < n /\ kids_ok kids /\ h = false
      /\ exists esc label' open sh,
           Some e = label_close esc n (sdrop n ps)
           /\ label = (label' ++ if esc then one bslash else EmptyString)%string
           /\ core = IReference kids im open esc label' sh (oview v)
  | PMRegion true im kids d e raw =>
      S d < n /\ h = false /\ exists open sh ds,
        dfeed raw (DS false 0 "") = Some ds
        /\ Some e = dest_close (ds_esc ds) (ds_depth ds) n (sdrop n ps)
        /\ core = IDest kids im open (ds_esc ds) (ds_depth ds) (ds_dst ds) sh
                   (oview v)
  | PMAtom x e =>
      h = false /\ n <= e
      /\ ((exists p d m body cl r txt0 prev0 o0,
            p < n /\ tok_at ps p = Some (TVerb d m body cl r, S e - p) /\ x = verb_node d r body
            /\ sim (pv_setmode PMNormal v) (txt0 ++ chars dollar (d - 2)) o0
            /\ core = iscan_str (substring p (n - p) ps) (IText false txt0 prev0 o0)
            /\ verb_state core (get n ps))
          \/ note_in ps n v x e core \/ attr_in ps n v x e core)
  | PMSpan im kids a e => h = false /\ span_in ps n v im kids a e core
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
  exists (x : inline) v0,
    h = false /\ pv_mode v0 = PMNormal /\ v = pv_add x v0 /\ (forall s, x <> Str s)
    /\ ((exists d m body, core = IVerb m m body (vkind_of d) (oview v0) /\ x = verb_node d None body)
        \/ (sdrop n ps = EmptyString
            /\ ifinish core = ifinish (IText false "" None (oview (pv_add x v0))))).

Definition linked_end (ps : string) (n : nat) (h : bool) (v : pview) (prev : option ascii)
  (core : iscan) : Prop :=
  linked ps n h v prev core \/ pending h v core \/ vpending ps n h v core.

(* A line's bytes, scanned from a linked state, end in one, inside the
   layers it began in and the ones it opened. *)
Definition scanned (ps : string) (n : nat) (h : bool) (v : pview) (ws : list wlayer)
  (core : iscan) (s : string) : Prop :=
  exists ws' core' prev' h' v',
    rres (iscan_str s (wrap ws core)) = wrap (map (wl_after s) ws ++ ws') core'
    /\ pruns ps n h v (n + String.length s) h' v'
    /\ vinv ps (n + String.length s) h' v'
    /\ Forall (never ps (n + String.length s)) (map (wl_after s) ws ++ ws')
    /\ linked_end ps (n + String.length s) h' v' prev' core'.

(* What the alphabet says of the rest of a line: outside a token, past
   the backslash the scanner holds; inside a verbatim or a spec, past
   whatever backslash the line's bytes leave, which they read their own
   way; inside a footnote label, which reads a backslash as the alphabet
   does, past the one the label holds. *)
Definition alpha_ok (v : pview) (core : iscan) (s : string) : Prop :=
  match pv_mode v, core with
  | PMAtom _ _, INote _ _ _ _ _ _ => over_alphabet (with_esc (pend_esc core) s) = true
  | PMAtom _ _, _ | PMSpan _ _ _ _, _ => exists e, over_alphabet (with_esc e s) = true
  | _, _ => over_alphabet (with_esc (pend_esc core) s) = true
  end.

Local Lemma alpha_of : forall v core s,
  over_alphabet (with_esc (pend_esc core) s) = true -> alpha_ok v core s.
Proof.
  intros v core s H. unfold alpha_ok.
  destruct (pv_mode v); try exact H; destruct core; first [exact H|eexists; exact H].
Qed.

Definition scan_ih (ps after : string) (len : nat) : Prop :=
  forall s prev n h v ws core,
    String.length s <= len -> alpha_ok v core s ->
    note_ok prev core s (s ++ after) -> sdrop n ps = (s ++ after)%string ->
    same_prev (before ps n) prev ->
    vinv ps n h v -> Forall (never ps n) ws -> linked ps n h v prev core ->
    scanned ps n h v ws core s.

Local Lemma wrap_app : forall a b core, wrap (a ++ b) core = wrap a (wrap b core).
Proof. induction a as [|w a IH]; intros b core; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Local Lemma wl_after_app : forall a b w,
  wfeed (a ++ b) w <> None -> wl_after b (wl_after a w) = wl_after (a ++ b) w.
Proof.
  intros a b w H. unfold wl_after. rewrite wfeed_app in *.
  destruct (wfeed a w) as [w'|]; [|contradiction H; reflexivity].
  destruct (wfeed b w'); [reflexivity|contradiction H; reflexivity].
Qed.

Local Lemma map_after_app : forall a b ws,
  Forall (fun w => wfeed (a ++ b) w <> None) ws ->
  map (wl_after b) (map (wl_after a) ws) = map (wl_after (a ++ b)) ws.
Proof.
  intros a b ws H. rewrite map_map. apply map_ext_in. intros w Hw.
  rewrite Forall_forall in H. exact (wl_after_app a b w (H w Hw)).
Qed.

Local Lemma map_after_nil : forall ws, map (wl_after "") ws = ws.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map]. rewrite IH. reflexivity. Qed.

Local Lemma wrap_inj : forall ws a b, wrap ws a = wrap ws b -> a = b.
Proof.
  induction ws as [|w ws IH]; intros a b H; [exact H|].
  destruct w; cbn [wrap] in H; try destruct (ap_failed p);
    try (apply IH; exact H); injection H; intros; apply IH; assumption.
Qed.

(* One step of the simulation: a chunk of bytes, then the rest of the
   line. *)
Local Lemma scan_advance_gen_in : forall ps after len,
  scan_ih ps after len ->
  forall s n h v ws core bytes rest prev1 extra core1 h1 v1,
    String.length s <= S len -> sdrop n ps = (s ++ after)%string ->
    Forall (never ps n) ws ->
    s = (bytes ++ rest)%string -> bytes <> "" ->
    pruns ps n h v (n + String.length bytes) h1 v1 ->
    vinv ps (n + String.length bytes) h1 v1 ->
    same_prev (before ps (n + String.length bytes)) prev1 ->
    alpha_ok v1 core1 rest -> note_ok prev1 core1 rest (rest ++ after) ->
    settles_in (iscan_str bytes core) (wrap extra core1) rest ->
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
  rewrite map_app, (map_after_app bytes rest ws Hopen), <- app_assoc in E, Fn''.
  exists (map (wl_after rest) extra ++ ws')%list, core', prev', h', v'.
  rewrite length_append, Nat.add_assoc.
  split; [|split; [exact (pruns_trans _ _ _ _ _ _ _ _ _ _ Hr R)|split; [exact V'|split; [exact Fn''|exact L']]]].
  rewrite <- E, wrap_app.
  apply (step_through_in bytes rest ws core (iscan_str bytes core) (wrap extra core1));
    [exact Hopen|reflexivity|exact Hset].
Qed.

Local Lemma scan_advance_gen : forall ps after len,
  scan_ih ps after len ->
  forall s n h v ws core bytes rest prev1 extra core1 h1 v1,
    String.length s <= S len -> sdrop n ps = (s ++ after)%string ->
    Forall (never ps n) ws ->
    s = (bytes ++ rest)%string -> bytes <> "" ->
    pruns ps n h v (n + String.length bytes) h1 v1 ->
    vinv ps (n + String.length bytes) h1 v1 ->
    same_prev (before ps (n + String.length bytes)) prev1 ->
    alpha_ok v1 core1 rest -> note_ok prev1 core1 rest (rest ++ after) ->
    settles (iscan_str bytes core) (wrap extra core1) (get 0 rest) ->
    Forall (never ps (n + String.length bytes)) extra ->
    linked ps (n + String.length bytes) h1 v1 prev1 core1 ->
    scanned ps n h v ws core s.
Proof.
  intros ps after len IH s n h v ws core bytes rest prev1 extra core1 h1 v1
    Hl Hs Fn Es Hne Hr V Hp Ha Hnote Hset.
  exact (scan_advance_gen_in ps after len IH s n h v ws core bytes rest prev1 extra core1 h1 v1
           Hl Hs Fn Es Hne Hr V Hp Ha Hnote (settles_in_of _ _ _ Hset)).
Qed.

Local Lemma scan_advance_in : forall ps after len,
  scan_ih ps after len ->
  forall s n h v ws core bytes rest prev1 extra core1 h1 v1,
    String.length s <= S len -> sdrop n ps = (s ++ after)%string ->
    Forall (never ps n) ws ->
    s = (bytes ++ rest)%string -> bytes <> "" ->
    pruns ps n h v (n + String.length bytes) h1 v1 ->
    vinv ps (n + String.length bytes) h1 v1 ->
    same_prev (before ps (n + String.length bytes)) prev1 ->
    over_alphabet (with_esc (pend_esc core1) rest) = true -> note_ok prev1 core1 rest (rest ++ after) ->
    settles_in (iscan_str bytes core) (wrap extra core1) rest ->
    Forall (never ps (n + String.length bytes)) extra ->
    linked ps (n + String.length bytes) h1 v1 prev1 core1 ->
    scanned ps n h v ws core s.
Proof.
  intros ps after len IH s n h v ws core bytes rest prev1 extra core1 h1 v1
    Hl Hs Fn Es Hne Hr V Hp Ha.
  exact (scan_advance_gen_in ps after len IH s n h v ws core bytes rest prev1 extra core1 h1 v1
           Hl Hs Fn Es Hne Hr V Hp (alpha_of v1 core1 rest Ha)).
Qed.

Local Lemma scan_advance : forall ps after len,
  scan_ih ps after len ->
  forall s n h v ws core bytes rest prev1 extra core1 h1 v1,
    String.length s <= S len -> sdrop n ps = (s ++ after)%string ->
    Forall (never ps n) ws ->
    s = (bytes ++ rest)%string -> bytes <> "" ->
    pruns ps n h v (n + String.length bytes) h1 v1 ->
    vinv ps (n + String.length bytes) h1 v1 ->
    same_prev (before ps (n + String.length bytes)) prev1 ->
    over_alphabet (with_esc (pend_esc core1) rest) = true -> note_ok prev1 core1 rest (rest ++ after) ->
    settles (iscan_str bytes core) (wrap extra core1) (get 0 rest) ->
    Forall (never ps (n + String.length bytes)) extra ->
    linked ps (n + String.length bytes) h1 v1 prev1 core1 ->
    scanned ps n h v ws core s.
Proof.
  intros ps after len IH s n h v ws core bytes rest prev1 extra core1 h1 v1
    Hl Hs Fn Es Hne Hr V Hp Ha Hnote Hset.
  exact (scan_advance_in ps after len IH s n h v ws core bytes rest prev1 extra core1 h1 v1
           Hl Hs Fn Es Hne Hr V Hp Ha Hnote (settles_in_of _ _ _ Hset)).
Qed.

(* A chunk scanned exactly, and the rest of the line scanned from where it
   leaves the scanner. *)
Local Lemma scanned_cons : forall ps n h v ws core bytes rest h1 v1 after,
  sdrop n ps = (bytes ++ rest ++ after)%string -> Forall (never ps n) ws ->
  pruns ps n h v (n + String.length bytes) h1 v1 ->
  scanned ps (n + String.length bytes) h1 v1 (map (wl_after bytes) ws) (iscan_str bytes core) rest ->
  scanned ps n h v ws core (bytes ++ rest).
Proof.
  intros ps n h v ws core bytes rest h1 v1 after Hs Fn R
    (ws' & core' & prev' & h' & v' & E & R' & V' & F' & L').
  pose proof Hs as Hs0. rewrite <- append_assoc in Hs0.
  destruct (layers_pass ps n ws (bytes ++ rest) after Fn Hs0) as [Hopen _].
  rewrite (map_after_app bytes rest ws Hopen) in E, F'.
  exists ws', core', prev', h', v'. rewrite length_append, Nat.add_assoc.
  split; [|split; [exact (pruns_trans _ _ _ _ _ _ _ _ _ _ R R')|split; [exact V'|split; [exact F'|exact L']]]].
  rewrite <- E, iscan_str_app, (iscan_wrap bytes ws core); [reflexivity|].
  rewrite Forall_forall in Hopen |- *. intros w Hw E0. apply (Hopen w Hw).
  rewrite wfeed_app, E0. reflexivity.
Qed.

(* A layer that opens at the first byte of what is scanned: the rest
   scans inside it as it would without it. *)
Local Lemma scanned_lift : forall ps n h v ws core X c r W,
  Forall (fun w => wfeed (String c r) w <> None) ws ->
  istep c X = wrap [W] (istep c core) -> wfeed r W <> None ->
  never ps (n + String.length (String c r)) (wl_after r W) ->
  scanned ps n h v ws core (String c r) -> scanned ps n h v ws X (String c r).
Proof.
  intros ps n h v ws core X c r W Fo Hx Hw Nw (ws' & core' & prev' & h' & v' & E & R & V & F & L).
  assert (Fc : Forall (fun w => wstep c w <> None) ws).
  { rewrite Forall_forall in Fo |- *. intros w Hin E0. apply (Fo w Hin). cbn [wfeed].
    rewrite E0. reflexivity. }
  set (ws1 := map (fun w => match wstep c w with Some w' => w' | None => w end) ws).
  assert (Fr : Forall (fun w => wfeed r w <> None) ws1).
  { unfold ws1. rewrite Forall_map. rewrite Forall_forall in Fo |- *. intros w Hin E0.
    apply (Fo w Hin). cbn [wfeed]. destruct (wstep c w) as [w0|]; [exact E0|reflexivity]. }
  assert (M1 : map (wl_after r) ws1 = map (wl_after (String c r)) ws).
  { unfold ws1. rewrite map_map. apply map_ext_in. intros w Hin. unfold wl_after. cbn [wfeed].
    rewrite Forall_forall in Fo. specialize (Fo w Hin). cbn [wfeed] in Fo.
    destruct (wstep c w) as [w0|]; [|contradiction Fo; reflexivity].
    destruct (wfeed r w0); [reflexivity|contradiction Fo; reflexivity]. }
  assert (Hcore : rres (iscan_str r (istep c core)) = wrap ws' core').
  { cbn [iscan_str] in E. rewrite (istep_wrap c ws core Fc) in E. fold ws1 in E.
    rewrite (iscan_wrap r ws1 _ Fr), rres_wrap, M1, wrap_app in E. exact (wrap_inj _ _ _ E). }
  exists (wl_after r W :: ws')%list, core', prev', h', v'.
  split; [|split; [exact R|split; [exact V|split; [|exact L]]]].
  - cbn [iscan_str]. rewrite (istep_wrap c ws X Fc), Hx. fold ws1. rewrite <- wrap_app.
    rewrite (iscan_wrap r (ws1 ++ [W]) _).
    2: { apply Forall_app. split; [exact Fr|constructor; [exact Hw|constructor]]. }
    rewrite rres_wrap, map_app, M1, Hcore, !wrap_app. reflexivity.
  - apply Forall_app in F as [F1 F2]. apply Forall_app.
    split; [exact F1|constructor; [exact Nw|exact F2]].
Qed.

Local Lemma linked_normal : forall ps n v prev txt o,
  pv_mode v = PMNormal -> sim v txt o ->
  linked ps n false v prev (IText false txt prev o).
Proof.
  intros ps n v prev txt o Em Hs. unfold linked. rewrite Em.
  split; [reflexivity|]. exists txt, o. auto.
Qed.

Local Lemma region_close_linked : forall ps n v x prev,
  (forall s, x <> Str s) ->
  linked ps n false (pv_add x (pv_setmode PMNormal v)) prev
    (IText false "" prev (oemit (mk x) (oview v))).
Proof.
  intros ps n v x prev Hx. apply linked_normal.
  - rewrite (proj2 (pv_add_live _ _)). reflexivity.
  - exists (pv_add x (pv_setmode PMNormal v)).
    split; [exact (oemit_view x (pv_setmode PMNormal v) Hx)|].
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

(* Where a region closes does not depend on where its bytes are counted
   from. *)
(* A reference label that never closes is read as a footnote label is. *)
Local Lemma label_close_note_go : forall s esc i,
  label_close esc i s = None -> note_go esc s = None.
Proof.
  induction s as [|c s IH]; intros esc i H; [reflexivity|]. cbn [label_close] in H. cbn [note_go].
  destruct esc; [rewrite (IH _ _ H); reflexivity|].
  destruct (is_bslash c); [rewrite (IH _ _ H); reflexivity|].
  destruct (Ascii.eqb c rbrack); [discriminate|rewrite (IH _ _ H); reflexivity].
Qed.

Local Lemma substring_length0 : forall s k,
  k <= String.length s -> String.length (substring 0 k s) = k.
Proof.
  induction s as [|c s IH]; intros [|k] H; cbn [String.length substring] in *; try lia;
    try reflexivity.
  f_equal. apply IH. lia.
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
    (forall im kids a e, pv_mode v <> PMSpan im kids a e) ->
    scanned ps n h v ws core (String c s').
Proof.
  intros ps after len IH c s' prev n h v ws core Hl Ha Hs V Fn L Em Ea Esp.
  pose proof (get_sdrop ps n c _ Hs) as Hg.
  pose proof (sdrop_succ ps n c _ Hs) as Hs1.
  change ((fix append (s1 s2 : string) {struct s1} : string :=
             match s1 with "" => s2 | String c s1' => String c (append s1' s2) end) s' after)
    with (s' ++ after)%string in Hs1.
  pose proof (before_sdrop ps n c _ Hs) as Hb.
  pose proof V as (Ok & Ti & _).
  assert (U : punit ps n h v = Some (S n, false, pbyte n c v)).
  { unfold punit. destruct (pv_mode v); [contradiction| | |]; rewrite Hg; reflexivity. }
  assert (V1 : vinv ps (S n) false (pbyte n c v)).
  { split; [apply pv_ok_byte; assumption|]. split; [apply pbyte_tidy, Ti|]. discriminate. }
  assert (A : forall core1,
            over_alphabet (with_esc (pend_esc core1) s') = true -> note_ok (Some c) core1 s' (s' ++ after) ->
            settles (istep c core) core1 (get 0 s') ->
            linked ps (S n) false (pbyte n c v) (Some c) core1 ->
            scanned ps n h v ws core (String c s')).
  { intros core1 A1 N1 S1 L1.
    apply (scan_advance ps after len IH (String c s') n h v ws core (one c) s' (Some c) [] core1
             false (pbyte n c v)); cbn [String.length one]; try rewrite Nat.add_1_r;
      first [assumption | reflexivity | discriminate | exact (pruns_one _ _ _ _ _ _ _ U)
            | (rewrite Hb; apply same_prev_refl) | constructor | (cbn [iscan_str wrap]; exact S1)]. }
  unfold linked in L. unfold pbyte in A.
  rewrite Hs in L. change (String c s' ++ after)%string with (String c (s' ++ after)) in L.
  destruct (pv_mode v) as [|[|] im kids d e txt|x e|im sk sat se] eqn:Em'; [contradiction| | | |];
    [| |destruct (Ea x e eq_refl)|destruct (Esp im sk sat se eq_refl)].
  - (* a destination *)
    destruct L as (Hd & _ & open & sh & [e0 dp dst] & Hds & He & ->).
    cbn [ds_esc ds_depth ds_dst pend_esc] in *.
    replace (n =? S d)%nat with false in A by (symmetry; apply Nat.eqb_neq; lia).
    destruct (dstep c (DS e0 dp dst)) as [ds'|] eqn:Hst.
    + rewrite (dest_close_step c (s' ++ after) e0 dp dst ds' n Hst) in He.
      assert (Hen : Nat.eqb n e = false).
      { symmetry in He. apply dest_close_bound in He. apply Nat.eqb_neq. lia. }
      rewrite Hen in A.
      apply (A (IDest kids im open (ds_esc ds') (ds_depth ds') (ds_dst ds')
                  (istep c sh) (oview v))).
      * cbn [pend_esc]. unfold dstep in Hst. cbn [ds_esc ds_depth ds_dst] in Hst.
        destruct e0; [injection Hst as <-; cbn [with_esc over_alphabet] in Ha |- *;
                      apply andb_true_iff in Ha as [_ Ha]; exact Ha|].
        destruct (is_bslash c) eqn:Eb.
        { injection Hst as <-. unfold is_bslash in Eb. apply Ascii.eqb_eq in Eb. subst c.
          cbn [with_esc ds_esc] in *. exact Ha. }
        destruct (pstep_byte c dp); [|discriminate]. injection Hst as <-.
        exact (proj2 (proj2 (over_alphabet_cons c s' Eb Ha))).
      * right; left. intros t p o E. discriminate E.
      * rewrite (istep_idest c _ _ _ _ _ _ _ _ ds' Hst). apply settles_refl.
      * unfold linked. cbn [pv_setmode pv_mode]. split; [lia|]. split; [reflexivity|].
        exists open, (istep c sh), ds'. split; [|split].
        -- rewrite dfeed_app, Hds. cbn [one dfeed]. rewrite Hst. reflexivity.
        -- rewrite Hs1. exact He.
        -- reflexivity.
    + (* the `)` that closes it *)
      destruct (dstep_none c e0 dp dst Hst) as (-> & -> & ->).
      rewrite (dest_close_none rparen (s' ++ after) false 0 dst n Hst) in He.
      injection He as ->.
      rewrite Nat.eqb_refl in A.
      pose proof (over_alphabet_cons rparen s' eq_refl Ha) as (_ & Hf & Hs').
      apply (A (IText false "" (Some rparen)
                  (oemit (mk (region_node true im kids (dest_text false txt))) (oview v)))).
      * exact Hs'.
      * left. apply prev_ok_follow; [exact Hf|reflexivity].
      * pose proof (dfeed_text txt false 0 "" _ Hds) as Ed. cbn [ds_dst append] in Ed. subst dst.
        unfold region_node. rewrite no_nl_drop. apply settles_refl.
      * apply region_close_linked, region_node_nonstr.
  - (* a reference label *)
    destruct L as (Hd & Hk & _ & esc & label' & open & sh & He & Hlab & ->).
    cbn [pend_esc] in Ha.
    replace (n =? S d)%nat with false in A by (symmetry; apply Nat.eqb_neq; lia).
    assert (Stay : forall esc' lab',
              Some e = label_close esc' (S n) (s' ++ after) ->
              (txt ++ one c)%string = (lab' ++ if esc' then one bslash else EmptyString)%string ->
              over_alphabet (with_esc esc' s') = true ->
              settles (istep c (IReference kids im open esc label' sh (oview v)))
                (IReference kids im open esc' lab' (istep c sh) (oview v)) (get 0 s') ->
              scanned ps n h v ws (IReference kids im open esc label' sh (oview v))
                (String c s')).
    { intros esc' lab' He' Ht Ha' Hset.
      assert (Hen : Nat.eqb n e = false).
      { symmetry in He'. apply label_close_bound in He'. apply Nat.eqb_neq. lia. }
      rewrite Hen in A. apply (A (IReference kids im open esc' lab' (istep c sh) (oview v)));
        [exact Ha'|right; left; intros t p o E; discriminate E|exact Hset|].
      unfold linked. cbn [pv_setmode pv_mode]. split; [lia|]. split; [exact Hk|].
      split; [reflexivity|]. exists esc', lab', open, (istep c sh).
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
        unfold istep. cbn [istep_at]. unfold iref_step. apply settles_refl.
      * pose proof (over_alphabet_cons c s' Eb Ha) as (_ & Hf & Hs').
        destruct (Ascii.eqb c rbrack) eqn:Er.
        -- (* the `]` that ends it *)
           apply Ascii.eqb_eq in Er. subst c.
           cbn [label_close is_bslash] in He. rewrite Ascii.eqb_refl in He.
           injection He as ->.
           change (is_bslash rbrack) with false in A. cbn iota in A.
           rewrite Nat.eqb_refl in A.
           apply (A (IText false "" (Some rbrack)
                       (oemit (mk (region_node false im kids label')) (oview v)))).
           ++ exact Hs'.
           ++ left. apply prev_ok_follow; [exact Hf|reflexivity].
           ++ apply settles_refl.
           ++ apply region_close_linked, region_node_nonstr.
        -- apply (Stay false (label' ++ one c)%string).
           ++ rewrite He. cbn [label_close]. rewrite Eb, Er. reflexivity.
           ++ rewrite append_empty_r. reflexivity.
           ++ exact Hs'.
           ++ unfold istep. cbn [istep_at]. unfold iref_step. rewrite Eb, Er.
              apply settles_refl.
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
  intros c t p o n r t' vk o' E. unfold ilead, itable in E.
  repeat match goal with
  | H : context [if ?b then _ else _] |- _ => destruct b
  | H : context [match ?x with Some _ => _ | None => _ end] |- _ => destruct x
  end; try discriminate E;
  repeat match goal with q : _ * _ |- _ => destruct q end; discriminate E.
Qed.

(* Only a backtick completes a closing run: any other byte leaves a
   verbatim, its own or a shadow's, with no backticks pending. *)
Local Lemma step_nontick_run : forall a c X n r t vk o,
  is_tick c = false -> istep_at a c X = IVerb n r t vk o -> r = 0.
Proof.
  intros a c X. revert a. induction X; intros a n0 r0 t0 vk0 o0 Ec E; cbn [istep_at] in E;
    unfold ibrace_step_at, iattr_feed, ispan_feed, ibang_step, idollar_step, iperiod_step,
      idash_step, inote_step, iwiki_step, iwiki_close, iauto_step, iref_step, isymbol_step,
      iraw_step, ipercent_step, iattr_mark, iraw_open, idelim_resolve, idelim_done in E;
    rewrite ?Ec in E;
    repeat match goal with
    | H : context [if ?b then _ else _] |- _ => destruct b
    | H : context [match ?x with Some _ => _ | None => _ end] |- _ => destruct x
    | H : context [let '(_, _) := ?x in _] |- _ => destruct x
    | H : context [match ?x with VVerb => _ | _ => _ end] |- _ => destruct x as [|[]|?|]
    | H : context [match ?x with O => _ | S _ => _ end] |- _ => destruct x
    | H : context [match ?x with EmptyString => _ | String _ _ => _ end] |- _ => destruct x
    end;
    try discriminate E;
    try (exfalso; exact (ilead_not_verb _ _ _ _ _ _ _ _ _ E));
    try (injection E; intros; lia);
    try (eapply IHX; [exact Ec|exact E]).
Qed.

(* A verbatim's closing run ends in a backtick. *)
Local Lemma verb_last_tick : forall X c m t vk o,
  istep c X = IVerb m m t vk o -> m <> 0 -> c = tick.
Proof.
  intros X c m t vk o E Hm. destruct (is_tick c) eqn:Ec.
  - unfold is_tick in Ec. apply Ascii.eqb_eq in Ec. exact Ec.
  - exfalso. exact (Hm (step_nontick_run _ _ _ _ _ _ _ _ Ec E)).
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

Local Lemma fmt_go_close : forall f x, fmt_ok f = true -> fmt_go (f ++ String rbrace x) = Some f.
Proof.
  induction f as [|c f IH]; intros x Ok; [reflexivity|].
  cbn [fmt_ok] in Ok. apply andb_true_iff in Ok as [Ok Okf]. apply andb_true_iff in Ok as [Eb Es].
  apply negb_true_iff in Eb, Es. cbn [append fmt_go]. rewrite Eb, Es, (IH x Okf). reflexivity.
Qed.

Local Lemma fmt_ok_snoc : forall f c, fmt_ok f = true ->
  Ascii.eqb c rbrace = false -> (raw_stop c || Ascii.eqb c nl_char)%bool = false ->
  fmt_ok (f ++ one c) = true.
Proof.
  induction f as [|x f IH]; intros c Ok Eb Es.
  - cbn. rewrite Eb, Es. reflexivity.
  - cbn [fmt_ok append] in Ok |- *. apply andb_true_iff in Ok as [Ok Okf].
    rewrite Ok, (IH c Okf Eb Es). reflexivity.
Qed.

(* A raw spec that does not close: the scanner holds it beside its
   ordinary reading, and takes that reading at the byte that fails it,
   or at the end of the line. *)
Local Lemma raw_fail_settles : forall r spec t sh o,
  no_char nl_char r = true ->
  (spec = EmptyString \/ exists f, spec = String eqchar f /\ fmt_ok f = true) ->
  (raw_inline_enabled = false \/ raw_spec (String lbrace (spec ++ r)) = None) ->
  settles_in (IRaw spec t sh o) sh r.
Proof.
  induction r as [|c r IH]; intros spec t sh o Hn Hs Hr.
  { exists "", "". split; [reflexivity|right]. split; reflexivity. }
  cbn [no_char] in Hn. apply andb_true_iff in Hn as [Hc Hn]. apply negb_true_iff in Hc.
  assert (Fail : istep c (IRaw spec t sh o) = istep c sh -> settles_in (IRaw spec t sh o) sh (String c r)).
  { intros E. exists (one c), r. split; [reflexivity|left]. exact E. }
  destruct Hs as [->|(f & -> & Ok)].
  - destruct (Ascii.eqb c eqchar) eqn:Ee.
    2: { apply Fail. unfold istep at 1. cbn [istep_at]. unfold iraw_step. tred.
         rewrite Ee, !andb_false_r. reflexivity. }
    apply Ascii.eqb_eq in Ee. subst c.
    destruct (IH (one eqchar) t (istep eqchar sh) o Hn (or_intror (ex_intro _ "" (conj eq_refl eq_refl))) Hr)
      as (q & r' & -> & E).
    exists (String eqchar q), r'. split; [reflexivity|]. cbn [iscan_str].
    replace (istep eqchar (IRaw "" t sh o)) with (IRaw (one eqchar) t (istep eqchar sh) o)
      by (unfold istep at 2; cbn [istep_at]; unfold iraw_step; tred; rewrite !andb_false_r; reflexivity).
    exact E.
  - destruct (Ascii.eqb c rbrace) eqn:Eb.
    + apply Fail. apply Ascii.eqb_eq in Eb. subst c.
      unfold istep at 1. cbn [istep_at]. unfold iraw_step. tred.
      replace (raw_inline_enabled && Ascii.eqb rbrace rbrace && raw_spec_ok (String eqchar f))%bool
        with false; [reflexivity|].
      change (Ascii.eqb rbrace rbrace) with true. cbn [raw_spec_ok]. rewrite andb_true_r.
      change (Ascii.eqb eqchar eqchar) with true. cbn [andb].
      destruct Hr as [-> | Hr]; [reflexivity|].
      cbn [append raw_spec] in Hr. change (Ascii.eqb lbrace lbrace && Ascii.eqb eqchar eqchar)%bool with true in Hr.
      cbv iota in Hr. rewrite (fmt_go_close f r Ok) in Hr. destruct f; [|discriminate Hr].
      rewrite andb_false_r. reflexivity.
    + destruct (raw_stop c) eqn:Es.
      * apply Fail. unfold istep at 1. cbn [istep_at]. unfold iraw_step. tred.
        rewrite Eb, andb_false_r. cbn [nonempty_str]. rewrite Es. reflexivity.
      * destruct (IH (String eqchar (f ++ one c)) t (istep c sh) o Hn) as (q & r' & -> & E).
        { right. exists (f ++ one c)%string. split; [reflexivity|].
          apply fmt_ok_snoc; [exact Ok|exact Eb|rewrite Es, Hc; reflexivity]. }
        { cbn [append] in Hr |- *. rewrite append_assoc. exact Hr. }
        exists (String c q), r'. split; [reflexivity|]. cbn [iscan_str].
        replace (istep c (IRaw (String eqchar f) t sh o))
          with (IRaw (String eqchar (f ++ one c)) t (istep c sh) o).
        2: { unfold istep at 2. cbn [istep_at]. unfold iraw_step. tred.
             rewrite Eb, andb_false_r. cbn [nonempty_str]. rewrite Es. reflexivity. }
        exact E.
Qed.

Local Lemma tick_follow_ok : forall s, follow_ok tick s = true.
Proof. reflexivity. Qed.

(* A byte of an attribute spec that closes, bare or a span's: the
   machine reads it, and the `}` adds the mark or the span. *)
Local Lemma scan_spec : forall ps after len, scan_ih ps after len ->
  forall c s' n v ws core,
    String.length (String c s') <= S len ->
    (exists e0, over_alphabet (with_esc e0 (String c s')) = true) ->
    sdrop n ps = (String c s' ++ after)%string ->
    vinv ps n false v -> Forall (never ps n) ws ->
    (exists x e, pv_mode v = PMAtom x e /\ attr_in ps n v x e core)
    \/ (exists im kids a e, pv_mode v = PMSpan im kids a e /\ span_in ps n v im kids a e core) ->
    scanned ps n false v ws core (String c s').
Proof.
  intros ps after len IH c s' n v ws core Hl [e0 Ha] Hs V Fn M.
  pose proof (get_sdrop ps n c _ Hs) as Hg.
  pose proof (sdrop_succ ps n c _ Hs) as Hs1.
  change ((fix append (s1 s2 : string) {struct s1} : string :=
             match s1 with "" => s2 | String c s1' => String c (append s1' s2) end) s' after)
    with (s' ++ after)%string in Hs1.
  pose proof (before_sdrop ps n c _ Hs) as Hb.
  pose proof V as (Ok & Ti & _).
  assert (Enn : pv_mode v <> PMNormal)
    by (destruct M as [(x & e & E & _)|(im & kids & a & e & E & _)]; rewrite E; discriminate).
  assert (U : punit ps n false v = Some (S n, false, pbyte n c v)).
  { unfold punit. destruct (pv_mode v); [contradiction| | |]; rewrite Hg; reflexivity. }
  assert (V1 : vinv ps (S n) false (pbyte n c v)).
  { split; [apply pv_ok_byte; [exact Ok|exact Enn]|]. split; [apply pbyte_tidy, Ti|].
    discriminate. }
  assert (A : forall core1,
            alpha_ok (pbyte n c v) core1 s' -> note_ok (Some c) core1 s' (s' ++ after) ->
            settles (istep c core) core1 (get 0 s') ->
            linked ps (S n) false (pbyte n c v) (Some c) core1 ->
            scanned ps n false v ws core (String c s')).
  { intros core1 A1 N1 S1 L1.
    apply (scan_advance_gen ps after len IH (String c s') n false v ws core (one c) s' (Some c) []
             core1 false (pbyte n c v)); cbn [String.length one]; try rewrite Nat.add_1_r;
      first [assumption | reflexivity | discriminate | exact (pruns_one _ _ _ _ _ _ _ U)
            | (rewrite Hb; apply same_prev_refl) | constructor | (cbn [iscan_str wrap]; exact S1)]. }
  (* what the alphabet says after the `}` *)
  assert (Close : c = rbrace -> over_alphabet s' = true /\ prev_ok (Some c) s' = true).
  { intros ->. pose proof (alpha_tail e0 rbrace s' Ha) as H.
    change (is_bslash rbrace) with false in H. rewrite andb_false_r in H.
    split; [exact H|]. apply prev_ok_plain; reflexivity. }
  destruct M as [(x & e & Em & p & src & txt & pv & sh & o & b & a & -> & Hfl & Hp & Hgo & He & ->)
                |(im & kids & a & e & Em & Bk & p & src & open & b & sh & Hp & Hgo & He & ->)];
    rewrite Hs in Hgo; cbn [append spec_go] in Hgo;
    (destruct (ap_failed (astep p c)) eqn:Ef; [discriminate Hgo|]);
    destruct (ap_done (astep p c)) eqn:Ed.
  - (* the `}` of a bare spec: its mark *)
    injection Hgo as <- <-. pose proof (astep_done p c Hp Ed) as Ec. subst c.
    cbn [String.length] in He. rewrite Nat.add_0_r in He. subst e.
    set (a' := ap_attrs (astep p rbrace)).
    set (vN := pv_setmode PMNormal v).
    assert (Pb : pbyte n rbrace v = pv_add (VMark a') vN)
      by (unfold pbyte; rewrite Em, Nat.eqb_refl; reflexivity).
    assert (EmN : pv_mode vN = PMNormal) by (unfold vN; destruct v; reflexivity).
    destruct (Close eq_refl) as [Ha' Hp'].
    apply (A (IText false "" (Some rbrace) (omark a' null_span (flush_text txt o))));
      rewrite ?Pb.
    + unfold alpha_ok. rewrite (proj2 (pv_add_live _ _)), EmN. exact Ha'.
    + left. exact Hp'.
    + unfold istep. cbn [istep_at]. rewrite Ef. unfold iattr_feed. rewrite Ef, Ed.
      apply settles_refl.
    + apply linked_normal; [rewrite (proj2 (pv_add_live _ _)); exact EmN|].
      exists (pv_add (VMark a') vN). split; [|split; [apply top_add_mark|reflexivity]].
      rewrite Hfl. change (oview v) with (oview vN). apply omark_view.
  - (* a byte inside a bare spec *)
    destruct (spec_go (astep p c) (s' ++ after)) as [[b1 a1]|] eqn:E1; [|discriminate Hgo].
    injection Hgo as <- <-. cbn [String.length] in He.
    assert (Pb : pbyte n c v = v).
    { unfold pbyte. rewrite Em. replace (n =? e)%nat with false; [reflexivity|].
      symmetry. apply Nat.eqb_neq. lia. }
    apply (A (IAttr (astep p c) (src ++ one c) txt pv (istep c sh) o)); rewrite ?Pb.
    + unfold alpha_ok. rewrite Em. eexists. exact (alpha_tail e0 c s' Ha).
    + right; left. intros t q o' E. discriminate E.
    + unfold istep. cbn [istep_at]. rewrite Ef. unfold iattr_feed. rewrite Ef, Ed.
      apply settles_refl.
    + unfold linked. rewrite Em. split; [reflexivity|]. split; [lia|]. right; right.
      exists (astep p c), (src ++ one c)%string, txt, pv, (istep c sh), o, b1, a1.
      split; [reflexivity|]. split; [exact Hfl|]. split; [exact Ed|].
      split; [rewrite Hs1; exact E1|]. split; [lia|reflexivity].
  - (* the `}` of a span's spec: the span *)
    injection Hgo as <- <-. pose proof (astep_done p c Hp Ed) as Ec. subst c.
    cbn [String.length] in He. rewrite Nat.add_0_r in He. subst e.
    destruct (Close eq_refl) as [Ha' Hp'].
    set (node := Node NoPos (ap_attrs (astep p rbrace)) (Span EmptyString kids)) in *.
    destruct (tidy_top v Ti) as [Tn Tc].
    set (vb := if im then pv_add (Str (one bang)) (pv_setmode PMNormal v)
               else pv_setmode PMNormal v) in *.
    assert (EmB : pv_mode vb = PMNormal)
      by (unfold vb; destruct im; [rewrite (proj2 (pv_add_live _ _))|]; destruct v; reflexivity).
    pose proof (ospan_bang_view im (pv_setmode PMNormal v)
                  ltac:(destruct v as [[|f r] o0 md]; exact Tn)
                  ltac:(destruct v as [[|f r] o0 md]; exact Tc)) as Eb.
    fold vb in Eb. change (oview (pv_setmode PMNormal v)) with (oview v) in Eb.
    destruct (oemit_vof node vb eq_refl ltac:(intros q s0 E; discriminate E)) as [Eo Et].
    assert (Pb : pbyte n rbrace v = pv_add (vof node) vb)
      by (unfold pbyte; rewrite Em, Nat.eqb_refl; reflexivity).
    apply (A (IText false "" (Some rbrace) (oemit node (ospan_bang im null_span (oview v)))));
      rewrite ?Pb.
    + unfold alpha_ok. rewrite (proj2 (pv_add_live _ _)), EmB. exact Ha'.
    + left. exact Hp'.
    + unfold istep. cbn [istep_at]. unfold ispan_feed. rewrite Ef, Ed. apply settles_refl.
    + apply linked_normal; [rewrite (proj2 (pv_add_live _ _)); exact EmB|].
      exists (pv_add (vof node) vb).
      split; [rewrite Eb; exact Eo|]. split; [exact Et|reflexivity].
  - (* a byte inside a span's spec *)
    destruct (spec_go (astep p c) (s' ++ after)) as [[b1 a1]|] eqn:E1; [|discriminate Hgo].
    injection Hgo as <- <-. cbn [String.length] in He.
    assert (Pb : pbyte n c v = v).
    { unfold pbyte. rewrite Em. replace (n =? e)%nat with false; [reflexivity|].
      symmetry. apply Nat.eqb_neq. lia. }
    apply (A (ISpan kids im open (astep p c) (src ++ one c) (istep c sh) (oview v)));
      rewrite ?Pb.
    + unfold alpha_ok. rewrite Em. eexists. exact (alpha_tail e0 c s' Ha).
    + right; left. intros t q o' E. discriminate E.
    + unfold istep. cbn [istep_at]. unfold ispan_feed. rewrite Ef, Ed. apply settles_refl.
    + unfold linked. rewrite Em. split; [reflexivity|]. split; [exact Bk|].
      exists (astep p c), (src ++ one c)%string, open, b1, (istep c sh).
      split; [exact Ed|]. split; [rewrite Hs1; exact E1|]. split; [lia|reflexivity].
Qed.

(* A byte of a verbatim, of a footnote reference or of a spec the view
   is inside. *)
Local Lemma scan_atom : forall ps after len, scan_ih ps after len ->
  line_end after ->
  forall c s' prev n h v ws core x e,
    String.length (String c s') <= S len ->
    alpha_ok v core (String c s') ->
    sdrop n ps = (String c s' ++ after)%string ->
    vinv ps n h v -> Forall (never ps n) ws -> linked ps n h v prev core ->
    pv_mode v = PMAtom x e ->
    scanned ps n h v ws core (String c s').
Proof.
  intros ps after len IH Hae c s' prev n h v ws core x e Hl Ha0 Hs V Fn L Em.
  unfold alpha_ok in Ha0. rewrite Em in Ha0.
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
            alpha_ok (pbyte n c v) core1 s' -> note_ok (Some c) core1 s' (s' ++ after) ->
            settles_in (istep c core) core1 s' ->
            linked ps (S n) false (pbyte n c v) (Some c) core1 ->
            scanned ps n h v ws core (String c s')).
  { intros core1 A1 N1 S1 L1.
    apply (scan_advance_gen_in ps after len IH (String c s') n h v ws core (one c) s' (Some c) []
             core1 false (pbyte n c v)); cbn [String.length one]; try rewrite Nat.add_1_r;
      first [assumption | reflexivity | discriminate | exact (pruns_one _ _ _ _ _ _ _ U)
            | (rewrite Hb; apply same_prev_refl) | constructor | (cbn [iscan_str wrap]; exact S1)]. }
  assert (End : s' = EmptyString ->
            vpending ps (S n) false (pbyte n c v) (rres (istep c core)) ->
            scanned ps n h v ws core (String c s')).
  { intros -> VP. destruct (layers_pass ps n ws (one c) after Fn Hs) as [Fo Fn'].
    exists [], (rres (istep c core)), (Some c), false, (pbyte n c v). rewrite app_nil_r.
    cbn [String.length] in *. rewrite Nat.add_1_r in *.
    split; [|split; [exact (pruns_one _ _ _ _ _ _ _ U)|split; [exact V1|split; [exact Fn'|]]]].
    - rewrite <- rres_wrap.
      exact (step_through (one c) "" ws core (istep c core) (istep c core) Fo eq_refl
               (settles_refl _ _)).
    - right. right. exact VP. }
  unfold linked in L. rewrite Em in L.
  destruct L as (-> & Hne & [(p & pre & m & body & cl & rw & txt0 & prev0 & o0 & Hp & Ht & -> & Hsim
                              & -> & Vs0)|[N|Na]]).
  3: { (* a byte of an attribute spec *)
    assert (Ha1 : exists e0, over_alphabet (with_esc e0 (String c s')) = true)
      by (destruct Na as (p & src & txt & pv & sh & o & b & a & -> & _); exact Ha0).
    exact (scan_spec ps after len IH c s' n v ws core Hl Ha1 Hs V Fn
             (or_introl (ex_intro _ x (ex_intro _ e (conj Em Na))))). }
  2: { (* a byte of a footnote label *)
    destruct N as (esc & im & lab & sh & o & r & -> & Hob & Hgo & -> & ->).
    cbn [pend_esc] in Ha0. rename Ha0 into Ha.
    rewrite Hs in Hgo. cbn [append note_go] in Hgo.
    (* a byte that does not end the label *)
    assert (In : forall esc' lab' r',
               nstep c (NS esc lab) = Some (NS esc' lab') ->
               note_go esc' (s' ++ after) = Some r' ->
               r = (if esc then String c r' else if is_bslash c then String bslash r'
                    else String c r') ->
               esc' = (negb esc && is_bslash c)%bool ->
               (lab ++ with_esc esc r = lab' ++ with_esc esc' r')%string ->
               scanned ps n false v ws (INote esc im lab null_span sh o) (String c s')).
    { intros esc' lab' r' Hst Hg' Er Ee El.
      assert (Pb : pbyte n c v = v).
      { unfold pbyte. rewrite Em. replace (n =? n + String.length r)%nat with false; [reflexivity|].
        symmetry. apply Nat.eqb_neq. destruct esc, (is_bslash c); subst r; cbn; lia. }
      apply (A (INote esc' im lab' null_span (istep c sh) o)); rewrite ?Pb.
      - unfold alpha_ok. rewrite Em. cbn [pend_esc]. subst esc'. exact (alpha_tail esc c s' Ha).
      - right; left. intros t q o' E. discriminate E.
      - apply settles_in_of. rewrite (istep_inote c esc im lab null_span sh o _ Hst).
        apply settles_refl.
      - unfold linked. rewrite Em. split; [reflexivity|].
        assert (Lr : String.length r = S (String.length r'))
          by (destruct esc, (is_bslash c); subst r; reflexivity).
        split; [lia|]. right; left.
        exists esc', im, lab', (istep c sh), o, r'.
        split; [reflexivity|]. split; [exact Hob|]. split; [rewrite Hs1; exact Hg'|].
        split; [lia|]. rewrite El. reflexivity. }
    destruct esc.
    { destruct (note_go false (s' ++ after)) as [r'|] eqn:Hg'; [|discriminate Hgo].
      injection Hgo as <-.
      apply (In false (lab ++ one bslash ++ one c) r'); try reflexivity; [exact Hg'|].
      cbn [with_esc]. rewrite !append_assoc. reflexivity. }
    destruct (is_bslash c) eqn:Eb.
    { destruct (note_go true (s' ++ after)) as [r'|] eqn:Hg'; [|discriminate Hgo].
      injection Hgo as <-. unfold is_bslash in Eb. apply Ascii.eqb_eq in Eb. subst c.
      apply (In true lab r'); try reflexivity; exact Hg'. }
    destruct (Ascii.eqb c rbrack) eqn:Er.
    2: { destruct (note_go false (s' ++ after)) as [r'|] eqn:Hg'; [|discriminate Hgo].
      injection Hgo as <-.
      apply (In false (lab ++ one c) r'); try reflexivity.
      - unfold nstep. cbn [ns_esc ns_lab]. rewrite Eb, Er. reflexivity.
      - exact Hg'.
      - cbn [with_esc]. rewrite append_assoc. reflexivity. }
    (* the `]` that ends it: the reference *)
    injection Hgo as <-. apply Ascii.eqb_eq in Er. subst c.
    cbn [with_esc String.length] in *. rewrite append_empty_r, Nat.add_0_r in *.
    set (x := FootnoteReference (normalize_label lab)).
    set (vN := pv_setmode PMNormal v).
    assert (Pb : pbyte n rbrack v = pv_add x vN)
      by (unfold pbyte; rewrite Em, Nat.eqb_refl; reflexivity).
    assert (EmN : pv_mode vN = PMNormal) by (unfold vN; destruct v; reflexivity).
    apply (over_alphabet_cons rbrack s' eq_refl) in Ha as (_ & Hf & Ha).
    apply (A (IText false "" (Some rbrack) (oemit (mk x) (oview vN)))); rewrite ?Pb.
    - unfold alpha_ok. rewrite (proj2 (pv_add_live _ _)), EmN. exact Ha.
    - left. apply prev_ok_follow; [exact Hf|reflexivity].
    - apply settles_in_of. unfold istep. cbn [istep_at]. unfold inote_step.
      change (is_bslash rbrack) with false. rewrite Ascii.eqb_refl. cbn iota. rewrite Hob.
      tred. apply settles_refl.
    - apply linked_normal; [rewrite (proj2 (pv_add_live _ _)); exact EmN|].
      exists (pv_add x vN). split; [apply oemit_view; discriminate|].
      split; [apply top_add_nonstr; discriminate|reflexivity]. }
  assert (Ha1 : exists e0, over_alphabet (with_esc e0 (String c s')) = true)
    by (destruct (iscan_str (substring p (n - p) ps) (IText false txt0 prev0 o0));
        first [exact Ha0|eexists; exact Ha0]).
  clear Ha0. destruct Ha1 as [e0 Ha].
  destruct (verb_tok_scan ps p pre m body cl rw (S e - p) txt0 prev0 o0 Ht) as (T1 & T2 & Traw & T3).
  pose proof (tok_at_len ps p _ _ Ht) as [_ Hle].
  pose proof (tok_verb_width ps p pre m body cl rw _ Ht) as Hm.
  set (X0 := IText false txt0 prev0 o0) in *.
  assert (Step : istep c (iscan_str (substring p (n - p) ps) X0)
                 = iscan_str (substring p (S n - p) ps) X0).
  { replace (S n - p) with (S (n - p)) by lia.
    rewrite (substring_snoc ps p (n - p) c) by (replace (p + (n - p)) with n by lia; exact Hg).
    rewrite iscan_str_app. reflexivity. }
  destruct (Nat.eqb n e) eqn:Ene.
  2: { (* inside *)
    apply Nat.eqb_neq in Ene.
    assert (VS : verb_state (istep c (iscan_str (substring p (n - p) ps) X0)) (get (S n) ps)).
    { rewrite Step. replace (S n) with (p + (S n - p)) at 2 by lia. apply T1. lia. }
    assert (Pb : pbyte n c v = v)
      by (unfold pbyte; rewrite Em; apply Nat.eqb_neq in Ene; rewrite Ene; reflexivity).
    apply (A (istep c (iscan_str (substring p (n - p) ps) X0))); rewrite ?Pb.
    - unfold alpha_ok. rewrite Em.
      destruct (istep c (iscan_str (substring p (n - p) ps) X0)); cbn in VS; try contradiction;
        eexists; exact (alpha_tail e0 c s' Ha).
    - right; left. intros t q o E. rewrite E in VS. exact (False_ind _ VS).
    - apply settles_in_of, settles_refl.
    - unfold linked. rewrite Em. split; [reflexivity|]. split; [lia|]. left.
      exists p, pre, m, body, cl, rw, txt0, prev0, o0. split; [lia|]. split; [exact Ht|].
      split; [reflexivity|]. split; [exact Hsim|]. split; [exact Step|exact VS]. }
  (* the last byte *)
  apply Nat.eqb_eq in Ene. subst e.
  destruct Hsim as (v0 & Eo & Ht0 & Ev).
  set (vN := pv_setmode PMNormal v) in *.
  assert (Fl : flush_text (txt0 ++ chars dollar (pre - 2)) o0 = oview vN)
    by (rewrite Eo, Ev; apply flush_view, Ht0).
  assert (Pb : pbyte n c v = pv_add (verb_node pre rw body) vN)
    by (unfold pbyte; rewrite Em, Nat.eqb_refl; reflexivity).
  assert (EmN : pv_mode vN = PMNormal) by (unfold vN; destruct v; reflexivity).
  destruct rw as [f|].
  { (* the `}` of a raw spec: the raw node, and text after it *)
    destruct (Traw f eq_refl) as (-> & -> & Gr & Ec).
    replace (p + pred (S n - p)) with n in Gr by lia. rewrite Hg in Gr. injection Gr as ->.
    cbn [Nat.sub chars] in Fl. rewrite append_empty_r in Fl. rewrite Ec, Fl in Step.
    apply (A (IText false "" (Some rbrace) (oemit (mk (RawInline f (trim_verb body))) (oview vN)))).
    - unfold alpha_ok. rewrite Pb, (proj2 (pv_add_live _ _)), EmN. cbn [pend_esc with_esc].
      pose proof (alpha_tail e0 rbrace s' Ha) as H. change (is_bslash rbrace) with false in H.
      rewrite andb_false_r in H. exact H.
    - left. reflexivity.
    - apply settles_in_of. rewrite Step. apply settles_refl.
    - rewrite Pb. apply linked_normal; [rewrite (proj2 (pv_add_live _ _)); exact EmN|].
      exists (pv_add (verb_node 0 (Some f) body) vN).
      split; [apply oemit_view; intros s0; discriminate|].
      split; [apply top_add_nonstr; intros s0; discriminate|reflexivity]. }
  destruct cl.
  - destruct (T2 eq_refl eq_refl) as (Ec & Stop & Nr).
    rewrite Ec, Fl in Step.
    destruct s' as [|d r].
    + (* at the end of the line *)
      apply End; [reflexivity|]. rewrite Step, Pb.
      exists (verb_node pre None body), vN.
      split; [reflexivity|]. split; [exact EmN|]. split; [reflexivity|].
      split; [intros s0; apply verb_node_nonstr|]. left. exists pre, m, body. split; reflexivity.
    + (* before a byte of the line that does not continue the verbatim *)
      assert (Ect : c = tick) by exact (verb_last_tick _ c _ _ _ _ Step Hm).
      subst c.
      assert (Hd : is_tick d = false).
      { apply Stop. replace (p + (S n - p)) with (S n) by lia. exact (get_sdrop ps (S n) d _ Hs1). }
      pose proof (tick_follow_ok (String d r)) as Hf'.
      assert (Hdm : Ascii.eqb d dollar = true -> dollar_math_enabled = false).
      { intros Edl. pose proof (alpha_tail e0 tick _ Ha) as H. rewrite andb_false_r in H.
        cbn [with_esc] in H. apply Ascii.eqb_eq in Edl. subst d.
        apply (over_alphabet_cons dollar r eq_refl) in H as (Hin & _).
        unfold in_alphabet in Hin. destruct dollar_math_enabled; [|reflexivity].
        exfalso. revert Hin. vm_compute. destruct (dstyle_of dollar); discriminate. }
      apply (A (IText false "" (Some tick) (oemit (mk (verb_node pre None body)) (oview vN)))).
      * unfold alpha_ok. rewrite Pb, (proj2 (pv_add_live _ _)), EmN. cbn [pend_esc with_esc].
        pose proof (alpha_tail e0 tick _ Ha) as H. rewrite andb_false_r in H. exact H.
      * left. apply prev_ok_follow; [exact Hf'|reflexivity].
      * rewrite Step.
        destruct (Ascii.eqb d lbrace && Nat.eqb pre 0)%bool eqn:Ebr.
        2: { apply settles_in_of. apply verb_close_settles; [exact Hd| |exact Hdm].
             intros Edb Hp0. rewrite Edb, (proj2 (Nat.eqb_eq pre 0) Hp0) in Ebr. discriminate Ebr. }
        (* a raw spec that does not close: the `{` is read as usual *)
        apply andb_true_iff in Ebr as [Ebr Ep]. apply Ascii.eqb_eq in Ebr. apply Nat.eqb_eq in Ep.
        subst d pre.
        assert (Hn : no_char nl_char r = true).
        { pose proof (alpha_tail e0 tick _ Ha) as H. rewrite andb_false_r in H.
          apply alphabet_no_nl in H. cbn [no_char] in H. apply andb_true_iff in H as [_ H]. exact H. }
        assert (Hraw : raw_inline_enabled = false \/ raw_spec (String lbrace ("" ++ r)) = None).
        { destruct raw_inline_enabled eqn:Eraw; [right|left; reflexivity].
          pose proof (Nr eq_refl eq_refl) as N0. replace (p + (S n - p)) with (S n) in N0 by lia.
          rewrite Hs1, (raw_spec_app _ _ Hae) in N0. exact N0. }
        set (sh0 := IBrace "" (Some tick) (oemit (mk (verb_node 0 None body)) (oview vN))).
        destruct (raw_fail_settles r "" (trim_verb body) sh0 (oview vN) Hn (or_introl eq_refl) Hraw)
          as (q & r' & -> & E).
        assert (S1 : istep lbrace (IVerb m m body (vkind_of 0) (oview vN))
                     = IRaw "" (trim_verb body) sh0 (oview vN)).
        { unfold istep. cbn [istep_at]. change (is_tick lbrace) with false. rewrite Nat.eqb_refl.
          reflexivity. }
        exists (String lbrace q), r'. split; [reflexivity|]. cbn [iscan_str]. rewrite S1. exact E.
      * rewrite Pb. apply linked_normal; [rewrite (proj2 (pv_add_live _ _)); exact EmN|].
        exists (pv_add (verb_node pre None body) vN).
        split; [apply oemit_view; apply verb_node_nonstr|].
        split; [apply top_add_nonstr; apply verb_node_nonstr|reflexivity].
  - (* the paragraph ends unclosed *)
    destruct (T3 eq_refl) as (_ & Elen & Efin).
    assert (Hlen : String.length (sdrop n ps) = 1) by (rewrite sdrop_length; lia).
    rewrite Hs in Hlen. cbn [append String.length] in Hlen. rewrite length_append in Hlen.
    destruct s' as [|d r]; [|cbn in Hlen; lia].
    destruct after as [|a af]; [|cbn in Hlen; lia].
    apply End; [reflexivity|]. rewrite Pb.
    exists (verb_node pre None body), vN.
    split; [reflexivity|]. split; [exact EmN|]. split; [reflexivity|].
    split; [intros s0; apply verb_node_nonstr|]. right. split; [exact Hs1|].
    rewrite ifinish_rres, Step, Efin, Fl, (oemit_view _ vN) by (intros s0; apply verb_node_nonstr).
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
  intros x [[|[p k c] rest] out md]; unfold top_filled; cbn [pv_add pv_stk pv_mode fset fcontent];
    destruct md; try exact Logic.I; apply xsnoc_nonempty.
Qed.

Local Lemma vinv_step : forall ps n h t l v,
  vinv ps n h v -> pv_mode v = PMNormal -> tok_at ps n = Some (t, l) ->
  vinv ps (n + l) (is_hard t) (pstep ps n h t v).
Proof.
  intros ps n h t l v (Ok & Ti & Hh) Em Ht.
  assert (H0 : ~ empty_run t).
  { pose proof (tok_at_len _ _ _ _ Ht) as Hl.
    intros [->|[->| ->]];
      [pose proof (tok_at_dollars _ _ _ _ Ht)|pose proof (tok_at_dots _ _ _ _ Ht)
      |pose proof (tok_at_dash _ _ _ _ Ht)]; lia. }
  split; [|split; [apply pstep_tidy; [exact H0|exact Em|exact Ti]|]].
  - apply pv_ok_step; [exact Ok|exact Em|exact Ht|]. intros _ H. exact (Hh H).
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
Local Lemma scan_tok_in : forall ps after len, scan_ih ps after len ->
  forall s n h v ws core t l rest prev1 core1,
    String.length s <= S len -> sdrop n ps = (s ++ after)%string -> Forall (never ps n) ws ->
    vinv ps n h v -> pv_mode v = PMNormal -> tok_at ps n = Some (t, l) ->
    s = (tok_text t ++ rest)%string -> l = String.length (tok_text t) ->
    same_prev (str_last (tok_text t) (before ps n)) prev1 ->
    over_alphabet (with_esc (pend_esc core1) rest) = true -> note_ok prev1 core1 rest (rest ++ after) ->
    settles_in (iscan_str (tok_text t) core) core1 rest ->
    linked ps (n + l) (is_hard t) (pstep ps n h t v) prev1 core1 ->
    pv_mode (pstep ps n h t v) = PMNormal \/ l = 1 ->
    scanned ps n h v ws core s.
Proof.
  intros ps after len IH s n h v ws core t l rest prev1 core1 Hl Hs Fn V Em Ht Es El Hp Ha Hn Hset L
    Hm.
  pose proof Hs as Hs0. rewrite Es, append_assoc in Hs0.
  apply (scan_advance_in ps after len IH s n h v ws core (tok_text t) rest prev1 [] core1
           (is_hard t) (pstep ps n h t v) Hl Hs Fn Es).
  - intros E. rewrite E in El. pose proof (tok_at_len ps n t l Ht). cbn in El. lia.
  - rewrite <- El. exact (pruns_one _ _ _ _ _ _ _ (punit_tok ps n h t l v Em Ht Hm)).
  - rewrite <- El. exact (vinv_step ps n h t l v V Em Ht).
  - rewrite (before_chunk ps n _ _ Hs0). exact Hp.
  - exact Ha.
  - exact Hn.
  - exact Hset.
  - constructor.
  - rewrite <- El. exact L.
Qed.

Local Lemma scan_tok : forall ps after len, scan_ih ps after len ->
  forall s n h v ws core t l rest prev1 core1,
    String.length s <= S len -> sdrop n ps = (s ++ after)%string -> Forall (never ps n) ws ->
    vinv ps n h v -> pv_mode v = PMNormal -> tok_at ps n = Some (t, l) ->
    s = (tok_text t ++ rest)%string -> l = String.length (tok_text t) ->
    same_prev (str_last (tok_text t) (before ps n)) prev1 ->
    over_alphabet (with_esc (pend_esc core1) rest) = true -> note_ok prev1 core1 rest (rest ++ after) ->
    settles (iscan_str (tok_text t) core) core1 (get 0 rest) ->
    linked ps (n + l) (is_hard t) (pstep ps n h t v) prev1 core1 ->
    pv_mode (pstep ps n h t v) = PMNormal \/ l = 1 ->
    scanned ps n h v ws core s.
Proof.
  intros ps after len IH s n h v ws core t l rest prev1 core1 Hl Hs Fn V Em Ht Es El Hp Ha Hn Hset.
  exact (scan_tok_in ps after len IH s n h v ws core t l rest prev1 core1 Hl Hs Fn V Em Ht Es El
           Hp Ha Hn (settles_in_of _ _ _ Hset)).
Qed.

Local Lemma scan_esc : forall ps after len, scan_ih ps after len -> line_end after ->
  forall s' prev n h v ws core,
    String.length (String bslash s') <= S len -> over_alphabet (String bslash s') = true ->
    sdrop n ps = (String bslash s' ++ after)%string ->
    same_prev (before ps n) prev ->
    vinv ps n h v -> Forall (never ps n) ws -> linked ps n h v prev core ->
    pv_mode v = PMNormal ->
    scanned ps n h v ws core (String bslash s').
Proof.
  intros ps after len IH Hae s' prev n h v ws core Hl Ha Hs Hpv V Fn L Em.
  unfold linked in L. rewrite Em in L. destruct L as (-> & txt & o & -> & Hsim).
  pose proof (alphabet_no_nl _ Ha) as Hnl. cbn [no_char] in Hnl. apply andb_true_iff in Hnl as [_ Hnl].
  assert (Ht0 : tok_at ps n = next_tok prev (String bslash s'))
    by (apply (tok_at_line ps n _ after prev Hs Hae);
          [discriminate|reflexivity|reflexivity|reflexivity|reflexivity|left; reflexivity
          |reflexivity| |exact Hpv];
        cbn [no_char]; rewrite Hnl; reflexivity).
  rewrite (nt_bs prev s' Hnl) in Ht0.
  pose proof (scan_tok ps after len IH (String bslash s') n false v ws (IText false txt prev o))
    as ST.
  destruct (is_blank s') eqn:Bl.
  { (* a hard break: the rest of the line *)
    destruct (layers_pass ps n ws (String bslash s') after Fn Hs) as [Hopen Fn'].
    exists [], (esc_pending s' txt (Some bslash) o),
      (Some bslash), true, (pstep ps n false (THard s') v). rewrite app_nil_r.
    rewrite iscan_wrap by exact Hopen. rewrite rres_wrap, iscan_bs_blank by exact Bl.
    split; [destruct s'; reflexivity|].
    split; [exact (pruns_one _ _ _ _ _ _ _ (punit_tok ps n false (THard s') _ v Em Ht0
                      (or_introl (pstep_mode ps n false (THard s') v Em ltac:(discriminate) ltac:(discriminate)
                                    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)))))|].
    split; [exact (vinv_step ps n false (THard s') _ v V Em Ht0)|].
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
    pose proof Hsim as (v0 & Eo & Hts & Ev).
    assert (Scan : iscan_str (String bslash (String d w1)) (IText false txt prev o)
                   = IEscWs (String d w1) txt (Some bslash) o)
      by exact (iscan_bs_blank (String d w1) txt prev o Hwb).
    assert (Step : forall core1,
              settles (iscan_str (String bslash (String d w1)) (IText false txt prev o))
                core1 (get 0 rest) ->
              linked ps (n + S (String.length (String d w1))) false
                (pstep ps n false (TEscWs (String d w1)) v) (Some x) core1 ->
              pend_esc core1 = false -> note_ok (Some x) core1 rest (rest ++ after) ->
              scanned ps n false v ws (IText false txt prev o) (String bslash (String d r))).
    { intros core1 Hset L1 Pe N1.
      apply (ST (TEscWs (String d w1)) (S (String.length (String d w1))) rest (Some x) core1);
        try assumption.
      - cbn [tok_text]. rewrite Ew. reflexivity.
      - reflexivity.
      - cbn [tok_text str_last]. rewrite Ex. reflexivity.
      - rewrite Pe. exact Ha2.
      - left. apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate]. }
    destruct (Ascii.eqb d " "%char) eqn:Sp.
    + (* a non-breaking space, and the rest of the run as text *)
      apply Ascii.eqb_eq in Sp. subst d.
      apply (Step (IText false w1 (Some x) (oemit (mk NonBreakingSpace) (flush_text txt o)))).
      * rewrite G. cbn [settles]. rewrite Scan. unfold istep. cbn [istep_at].
        rewrite Hc', iescws_cons, Ascii.eqb_refl, Ex. reflexivity.
      * apply linked_normal; [apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate]|].
        unfold pstep. cbn [nbsp_rest]. rewrite Ascii.eqb_refl.
        exists (pv_add NonBreakingSpace v). split; [|split].
        -- change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s txt o)
             with (flush_text txt o).
           rewrite Eo, (flush_view txt v0 Hts), <- Ev.
           apply oemit_view. discriminate.
        -- apply top_add_nonstr. discriminate.
        -- unfold add_text. reflexivity.
      * reflexivity.
      * left. apply ws_prev_ok, Hx.
    + (* a tab or a carriage return first: the backslash and the run as text *)
      apply (Step (IText false (txt ++ String bslash (String d w1)) (Some x) o)).
      * rewrite G. cbn [settles]. rewrite Scan. unfold istep. cbn [istep_at].
        rewrite Hc', iescws_cons, Sp. cbn [str_last]. rewrite Ex. reflexivity.
      * apply linked_normal; [apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate]|].
        unfold pstep. cbn [nbsp_rest]. rewrite Sp.
        apply sim_text; [exact Hsim|reflexivity].
      * reflexivity.
      * left. apply ws_prev_ok, Hx.
  - (* an escaped byte *)
    apply (ST (TEsc d) 2 r (Some d) (IText false (txt ++ esc_text d) (Some d) o));
      try assumption.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + right; left. intros t p o' E. injection E as <- _ _.
      destruct txt; [|reflexivity]. cbn.
      destruct (esc_text d) eqn:E'; [destruct (esc_text_ne d E')|reflexivity].
    + cbn [iscan_str tok_text one]. rewrite istep_bslash_text, istep_esc_byte by exact Wd.
      apply settles_refl.
    + apply linked_normal; [apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate]|].
      unfold pstep. apply sim_text; [exact Hsim|].
      destruct (esc_text d) eqn:E'; [destruct (esc_text_ne d E')|reflexivity].
    + left. apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate].
Qed.

Local Lemma linked_rres : forall ps n h v prev core,
  line_end (sdrop n ps) -> linked ps n h v prev core -> linked ps n h v prev (rres core).
Proof.
  intros ps n h v prev core Hle L. unfold linked in *.
  destruct (pv_mode v) as [|[|] im kids d e txt|x e|im sk sat se].
  - destruct L as (Hh & t & o & -> & Hs). split; [exact Hh|]. exists t, o.
    split; [reflexivity|exact Hs].
  - destruct L as (Hd & Hh & open & sh & ds & Hds & He & ->).
    split; [exact Hd|]. split; [exact Hh|]. exists open, (rres sh), ds. auto.
  - destruct L as (Hd & Hk & Hh & esc & label' & open & sh & He & Hl & ->).
    split; [exact Hd|]. split; [exact Hk|]. split; [exact Hh|].
    exists esc, label', open, (rres sh). auto.
  - destruct L as (Hh & He & [(p & dd & m & body & cl & rw & txt0 & prev0 & o0 & Hp & Ht & Ex & Hs
                                & Ec & Vs)|[N|Na]]).
    3: { (* the spec carries on *)
      destruct Na as (p & src & txt & pv & sh & o & b & a & -> & Na).
      split; [exact Hh|]. split; [exact He|]. right; right.
      exists p, src, txt, pv, (rres sh), o, b, a. split; [reflexivity|exact Na]. }
    2: { (* the label carries on *)
      destruct N as (esc & im & lab & sh & o & r & -> & N).
      split; [exact Hh|]. split; [exact He|]. right; left.
      exists esc, im, lab, (rres sh), o, r. split; [reflexivity|exact N]. }
    assert (Ge : get n ps = None \/ get n ps = Some nl_char).
    { rewrite <- (Nat.add_0_r n), get_add.
      destruct Hle as [-> | [r ->]]; [left|right]; reflexivity. }
    assert (Er : rres core = core).
    { destruct core; cbn [verb_state] in Vs; try contradiction; try reflexivity.
      - exfalso. destruct Ge as [G|G]; rewrite G in Vs; destruct Vs as [E|E]; discriminate E.
      - exfalso. destruct Vs as (c & E & Hc & _).
        destruct Ge as [G|G]; rewrite G in E; [discriminate E|injection E as <-; contradiction]. }
    rewrite Er. split; [exact Hh|]. split; [exact He|]. left.
    exists p, dd, m, body, cl, rw, txt0, prev0, o0. repeat split; assumption.
  - (* the span's spec carries on *)
    destruct L as (Hh & Bk & p & src & open & b & sh & Hp & Hgo & He & ->).
    split; [exact Hh|]. split; [exact Bk|]. exists p, src, open, b, (rres sh). auto.
Qed.

Local Lemma scanned_nil : forall ps n h v ws core prev,
  vinv ps n h v -> Forall (never ps n) ws -> linked ps n h v prev core ->
  line_end (sdrop n ps) -> scanned ps n h v ws core "".
Proof.
  intros ps n h v ws core prev V Fn L He. exists [], (rres core), prev, h, v.
  cbn [iscan_str String.length]. rewrite Nat.add_0_r, rres_wrap, app_nil_r, map_after_nil.
  split; [reflexivity|]. split; [constructor|]. split; [exact V|].
  split; [exact Fn|left; apply linked_rres; [exact He|exact L]].
Qed.

(* A `[` pushes the view's frame. *)
Local Lemma open_bracket_sim : forall n im v txt o,
  sim v txt o ->
  sim (popen n (KBracket, im) true (bracket_open im) v) "" (bpush im (flush_text txt o)).
Proof.
  intros n im v txt o (v0 & -> & Ht & ->).
  rewrite (flush_view txt v0 Ht). set (v := add_text txt v0).
  exists (popen n (KBracket, im) true (bracket_open im) v). split; [|split; reflexivity].
  reflexivity.
Qed.

(* A marked opener pushes the view's frame, with the bit the scanner
   records: whether a `}` comes right after it. *)
Local Lemma open_marked_sim : forall n k b lit0 txt v o,
  sim v txt o ->
  sim (popen n (KDelim k true, b) true lit0 v) "" (oopen_marked k b txt o).
Proof.
  intros n k b lit0 txt v o (v0 & -> & Ht & ->).
  unfold oopen_marked.
  change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s
            (tval txt) (oview v0))
    with (flush_text txt (oview v0)).
  rewrite (flush_view txt v0 Ht).
  exists (popen n (KDelim k true, b) true lit0 (add_text txt v0)).
  split; [|split; reflexivity]. reflexivity.
Qed.

(* A `]` before `(` or `[`, with a bracket open. *)
Local Lemma closed_step : forall v0 txt c2 content rest,
  starts_text (top_of v0) = false ->
  Forall (fun f => normal (fcontent f)) (pv_stk (add_text txt v0)) ->
  pclose_go KBracket [] (pv_stk (add_text txt v0)) = Some (content, rest) ->
  c2 = lparen \/ c2 = lbrack ->
  istep c2 (IClosed txt (oview v0))
  = let kids := vres content in
    let im := pclose_im (pv_stk (add_text txt v0)) in
    let o' := oview (PView rest (pv_out (add_text txt v0)) PMNormal) in
    let sh := ilead c2 (txt ++ one rbrack) (Some rbrack) (oview v0) in
    if Ascii.eqb c2 lparen
    then IDest kids im null_span false 0 "" sh o'
    else IReference kids im null_span false "" sh o'.
Proof.
  intros v0 txt c2 content rest Ht Nf Hc Hc2.
  unfold istep. cbn [istep_at].
  change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s (tval txt) (oview v0))
    with (flush_text txt (oview v0)).
  rewrite (flush_view txt v0 Ht). unfold oview at 1.
  rewrite (bclose_embed _ _ Nf), Hc.
  destruct Hc2 as [-> | ->]; reflexivity.
Qed.

(* A `]` before `{`, with a bracket open: a span's spec begins. *)
Local Lemma closed_step_span : forall v0 txt content rest,
  starts_text (top_of v0) = false ->
  Forall (fun f => normal (fcontent f)) (pv_stk (add_text txt v0)) ->
  pclose_go KBracket [] (pv_stk (add_text txt v0)) = Some (content, rest) ->
  inline_attrs_enabled = true ->
  istep lbrace (IClosed txt (oview v0))
  = ISpan (vres content) (pclose_im (pv_stk (add_text txt v0))) null_span ap_init ""
      (IBrace (txt ++ one rbrack) (Some rbrack) (oview v0))
      (oview (PView rest (pv_out (add_text txt v0)) PMNormal)).
Proof.
  intros v0 txt content rest Ht Nf Hc Hen.
  unfold istep. cbn [istep_at]. rewrite Hen.
  change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s (tval txt) (oview v0))
    with (flush_text txt (oview v0)).
  rewrite (flush_view txt v0 Ht). unfold oview at 1.
  rewrite (bclose_embed _ _ Nf), Hc. reflexivity.
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
  dstyle_of (dchar k) = Some k -> j < dwidth k -> Ascii.eqb (dchar k) hyphen = false ->
  (forall d r', r = String d r' -> d <> dchar k) -> no_char nl_char r = true -> line_end after ->
  sdrop n ps = (chars (dchar k) j ++ r ++ after)%string ->
  vinv ps n false v -> pv_mode v = PMNormal -> sim v txt o ->
  exists v', pruns ps n false v (n + j) false v' /\ vinv ps (n + j) false v'
    /\ pv_mode v' = PMNormal /\ sim v' (txt ++ chars (dchar k) j) o.
Proof.
  intros ps k j. induction j as [|j IH]; intros n v txt o r after Hk Hj Hhy Hr Hn Ha Hs V Em Hsim.
  - exists v. rewrite Nat.add_0_r, append_empty_r. split; [constructor|auto].
  - assert (Ht : tok_at ps n = Some (TText (dchar k), 1)).
    { rewrite <- (nt_short k j (before ps n) r Hk Hj Hr Hhy). unfold tok_at. rewrite Hs.
      replace (chars (dchar k) (S j) ++ r ++ after)%string
        with (String (dchar k) (chars (dchar k) j ++ r) ++ after)%string
        by (cbn [chars append]; rewrite append_assoc; reflexivity).
      pose proof (dreserved_false _ (dchar_free k))
        as (_ & Htk & _ & _ & Hlk & _ & Hbg & Hdl & _).
      destruct (dchar_plain k) as (Hlbk & _ & _ & Hrkk).
      apply next_tok_after;
        [|exact Ha|discriminate|exact Htk|exact Hdl|exact Hbg|exact Hlk|left; exact Hlbk|exact Hrkk].
      cbn [no_char]. rewrite dchar_nl. apply no_nl_chars, Hn. }
    pose proof (vinv_step ps n false _ 1 v V Em Ht) as V1.
    cbn [is_hard] in V1. rewrite Nat.add_1_r in V1.
    assert (Hs1 : sdrop (S n) ps = (chars (dchar k) j ++ r ++ after)%string)
      by exact (sdrop_succ ps n (dchar k) _ Hs).
    destruct (IH (S n) (pstep ps n false (TText (dchar k)) v) (txt ++ one (dchar k)) o r after
                Hk ltac:(lia) Hhy Hr Hn Ha Hs1 V1)
      as (v' & R & V' & Em' & Hsim').
    { apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate]. }
    { unfold pstep. apply sim_text; [exact Hsim|reflexivity]. }
    exists v'. rewrite <- Nat.add_succ_comm. split; [|split; [exact V'|split; [exact Em'|]]].
    + apply (pruns_trans ps n false v (S n) false (pstep ps n false (TText (dchar k)) v));
        [|exact R].
      apply pruns_one. rewrite (punit_tok ps n false _ 1 v Em Ht (or_intror eq_refl)), Nat.add_1_r. reflexivity.
    + rewrite append_assoc in Hsim'. exact Hsim'.
Qed.

(*
Autolinks
---------
*)



(* The byte that ends a candidate's region is drawn on the alphabet
   whether or not a backslash at the region's end escapes it, so the
   region can be split off the alphabet's reading of the line. *)
Local Lemma auto_stop_alpha : forall d r,
  auto_stop d = true -> Ascii.eqb d nl_char = false -> over_alphabet r = true ->
  over_alphabet (String d r) = true.
Proof.
  intros d r Hs Hn Hr. cbn [over_alphabet].
  destruct d as [[] [] [] [] [] [] [] []]; try discriminate Hs; try discriminate Hn;
    unfold in_alphabet, follow_ok; cbn; rewrite ?andb_false_r, Hr;
    destruct (dstyle_of _); reflexivity.
Qed.

Local Lemma over_alphabet_after_auto : forall src rest,
  auto_free src = true ->
  (rest = EmptyString \/ exists c r, rest = String c r /\ auto_stop c = true) ->
  over_alphabet (src ++ rest) = true -> over_alphabet rest = true.
Proof.
  intros src. remember (String.length src) as m eqn:Em. revert src Em.
  induction m as [m IH] using lt_wf_ind. intros src Em rest Fr Hr H.
  destruct src as [|c src']; [exact H|].
  cbn [auto_free] in Fr. apply andb_true_iff in Fr as [Fc Fr].
  destruct (is_bslash c) eqn:Eb.
  - destruct src' as [|e src''].
    + destruct Hr as [-> | (d & r & -> & Hd)]; [reflexivity|].
      cbn [append over_alphabet] in H. rewrite Eb in H.
      apply andb_true_iff in H as [Hn Hr'].
      apply negb_true_iff in Hn. exact (auto_stop_alpha d r Hd Hn Hr').
    + cbn [append over_alphabet] in H. rewrite Eb in H.
      apply andb_true_iff in H as [_ H].
      cbn [auto_free] in Fr. apply andb_true_iff in Fr as [_ Fr].
      apply (IH (String.length src'')) with (src := src''); try assumption; [|reflexivity].
      subst m. cbn. lia.
  - cbn [append] in H. apply (over_alphabet_cons c _ Eb) in H as (_ & _ & H).
    apply (IH (String.length src')) with (src := src'); try assumption; [|reflexivity].
    subst m. cbn. lia.
Qed.

Local Lemma iscan_auto : forall src s0 t sh o, auto_free src = true ->
  iscan_str src (IAuto s0 t sh o) = IAuto (s0 ++ src) t (iscan_str src sh) o.
Proof.
  induction src as [|c src IH]; intros s0 t sh o Hf; [cbn; rewrite append_empty_r; reflexivity|].
  cbn [auto_free] in Hf. apply andb_true_iff in Hf as [Hs Hf]. apply negb_true_iff in Hs.
  unfold auto_stop in Hs. apply orb_false_iff in Hs as [Hs Hn].
  apply orb_false_iff in Hs as [Hs Hlt]. apply orb_false_iff in Hs as [Hgt Hws].
  cbn [iscan_str]. unfold istep at 1. cbn [istep_at]. unfold iauto_step.
  rewrite Hgt. cbn [andb orb]. rewrite Hws, Hlt. cbn [orb]. tred.
  rewrite IH by exact Hf. rewrite append_assoc. reflexivity.
Qed.

(* The `<` opens a candidate, with the `<` read as text beside it. *)
Local Lemma auto_open : forall txt prev o,
  istep lt (IText false txt prev o)
  = IAuto "" txt (IText false (txt ++ one lt) (Some lt) o) o.
Proof. reflexivity. Qed.

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
  pose proof Hsim as (v0 & Eo & Ht & Ev).
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
    { pose proof (vinv_step ps n false _ l v V Em Htv) as (Ok1 & Ti1 & _).
      rewrite Pst in Ok1, Ti1.
      split; [|split; [exact Ti1|discriminate]].
      destruct Ok1 as (A1 & A2 & A3 & A5 & A6 & _).
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
      split; [exact A5|]. split; [exact A6|].
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
            | (rewrite Hb; apply same_prev_refl) | apply Forall_nil | idtac].
    + unfold alpha_ok, v1. cbn [pv_setmode pv_mode]. destruct (add_text X v). cbn [pv_mode].
      destruct (istep c (IText false txt prev o)); cbn in VS; try contradiction;
        eexists; exact (alpha_tail false c s' Ha).
    + right; left. intros t q o' E. rewrite E in VS. exact (False_ind _ VS).
    + apply settles_refl.
    + unfold linked. replace (pv_mode v1) with (PMAtom x (pred (n + l)))
        by (unfold v1; destruct (add_text X v); reflexivity).
      split; [reflexivity|]. split; [lia|]. left.
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
    pose proof (vinv_step ps n false _ 1 v V Em Htv) as V1.
    rewrite Pst in U, V1. cbn [is_hard] in U, V1. rewrite Nat.add_1_r in U, V1.
    pose proof (sdrop_succ ps n tick _ Hs) as Hs1.
    destruct (layers_pass ps n ws (one tick) "" Fn Hs) as [Fo Fn'].
    exists [], (rres (istep tick (IText false txt prev o))),
      (Some tick), false, (pv_add x v). rewrite app_nil_r.
    cbn [String.length] in *. rewrite Nat.add_1_r in *.
    split; [|split; [exact (pruns_one _ _ _ _ _ _ _ U)|split; [exact V1|split; [exact Fn'|]]]].
    + rewrite <- rres_wrap.
      exact (step_through (one tick) "" ws (IText false txt prev o)
               (istep tick (IText false txt prev o)) _ Fo eq_refl (settles_refl _ _)).
    + right. right. exists x, v.
      split; [reflexivity|]. split; [exact Em|]. split; [reflexivity|].
      split; [intros s0; discriminate|]. right. split; [exact Hs1|].
      rewrite ifinish_rres. rewrite Sub1 in Efin. cbn [iscan_str] in Efin.
      change (istep tick (IText false txt prev o))
        with (iscan_str (one tick) (IText false txt prev o)).
      rewrite Efin, Eo, (flush_view txt v0 Ht), <- Ev, (oemit_view _ v)
        by (intros s0; discriminate).
      reflexivity.
Qed.

(* An autolink candidate from text mode: its link, or its text. *)
Local Lemma scan_auto : forall ps after len, scan_ih ps after len -> line_end after ->
  forall s' prev n v ws txt o,
    String.length (String lt s') <= S len -> over_alphabet (String lt s') = true ->
    sdrop n ps = (String lt s' ++ after)%string -> same_prev (before ps n) prev ->
    vinv ps n false v -> Forall (never ps n) ws -> pv_mode v = PMNormal -> sim v txt o ->
    scanned ps n false v ws (IText false txt prev o) (String lt s').
Proof.
  intros ps after len IH Hae s' prev n v ws txt o Hl Ha Hs Hpv V Fn Em Hsim.
  pose proof (alphabet_no_nl _ Ha) as Hnl.
  assert (Ht : tok_at ps n = Some (auto_tok s')).
  { rewrite (tok_at_line ps n _ after prev Hs Hae ltac:(discriminate) eq_refl eq_refl eq_refl eq_refl
                (or_introl eq_refl) eq_refl Hnl Hpv).
    reflexivity. }
  pose proof Ha as Ha'. apply (over_alphabet_cons lt s' eq_refl) in Ha' as (_ & Hf & Hs').
  destruct (auto_go s') as [src stop] eqn:Eg.
  destruct (auto_go_split _ _ _ Eg) as [Fr (rest & Es' & Hr)].
  assert (Hrest : over_alphabet rest = true).
  { rewrite Es' in Hs'. refine (over_alphabet_after_auto src rest Fr _ Hs').
    destruct Hr as [[_ ->]|(c & r & _ & -> & Hc)]; [left; reflexivity|right; eauto]. }
  set (sh0 := IText false (txt ++ one lt) (Some lt) o).
  assert (Sc : iscan_str (String lt src) (IText false txt prev o)
               = IAuto src txt (iscan_str src sh0) o)
    by (cbn [iscan_str]; rewrite auto_open, iscan_auto by exact Fr; reflexivity).
  pose proof Hsim as (v0 & Eo & Ht0 & Ev).
  assert (Fl : flush_text txt o = oview v) by (rewrite Eo, Ev; apply flush_view, Ht0).
  unfold auto_tok in Ht. rewrite Eg in Ht.
  destruct (match stop with Some c => Ascii.eqb c gt | None => false end
            && auto_body_ok src && auto_kind_ok src)%bool eqn:Ok.
  - (* a link *)
    destruct Hr as [[-> _]|(c & r & -> & -> & Hst)]; [discriminate Ok|].
    apply andb_true_iff in Ok as [Ok Hk]. apply andb_true_iff in Ok as [Eg' Hb].
    apply Ascii.eqb_eq in Eg'. subst c.
    set (x := auto_node src).
    assert (Hx : forall s0, x <> Str s0) by (intros s0; apply auto_node_nonstr).
    apply (scan_tok ps after len IH (String lt s') n false v ws (IText false txt prev o)
             (TAuto src) (S (S (String.length src))) r (Some gt)
             (IText false "" (Some gt) (oemit (mk x) (oview v))) Hl Hs Fn V Em Ht).
    + cbn [tok_text]. rewrite Es', append_assoc. reflexivity.
    + cbn [tok_text String.length]. rewrite length_append. cbn. lia.
    + cbn [tok_text]. rewrite str_last_app. reflexivity.
    + cbn [pend_esc with_esc]. exact (proj2 (proj2 (over_alphabet_cons gt r eq_refl Hrest))).
    + left. apply prev_ok_plain; reflexivity.
    + cbn [tok_text]. rewrite iscan_str_app, Sc.
      change (one gt) with (String gt ""). cbn [iscan_str]. unfold istep. cbn [istep_at].
      unfold iauto_step. change (Ascii.eqb gt gt) with true.
      change (tval src) with src. change (tval txt) with txt. rewrite Hb, Hk. cbn [andb].
      change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s txt o)
        with (flush_text txt o).
      rewrite Fl. apply settles_refl.
    + cbn [is_hard]. unfold pstep.
      apply linked_normal; [rewrite (proj2 (pv_add_live _ _)); exact Em|].
      exists (pv_add x v). split; [apply oemit_view, Hx|].
      split; [apply top_add_nonstr, Hx|reflexivity].
    + left. apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate].
  - (* the `<` as text: the candidate reads its region while the `<`'s
       ordinary reading reads the same bytes, and takes that reading at
       the byte that ends the region, or at the end of the line *)
    apply (scan_tok_in ps after len IH (String lt s') n false v ws (IText false txt prev o)
             (TText lt) 1 s' (Some lt) sh0 Hl Hs Fn V Em Ht).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + cbn [pend_esc with_esc]. exact Hs'.
    + right; left. intros t q o' E. injection E as <- _ _. destruct txt; reflexivity.
    + cbn [tok_text one iscan_str]. rewrite auto_open, Es'. fold sh0.
      destruct Hr as [[-> ->]|(c & r & -> & -> & Hst)].
      * exists src, "". rewrite append_empty_r. split; [reflexivity|right].
        split; [reflexivity|]. rewrite iscan_auto by exact Fr. reflexivity.
      * assert (Hcn : Ascii.eqb c nl_char = false).
        { rewrite Es' in Hnl. cbn [no_char] in Hnl. apply andb_true_iff in Hnl as [_ Hnl].
          clear -Hnl. induction src as [|x src IH]; cbn [append no_char] in Hnl.
          - apply andb_true_iff in Hnl as [Hn _]. apply negb_true_iff in Hn. exact Hn.
          - apply andb_true_iff in Hnl as [_ Hnl]. exact (IH Hnl). }
        exists (src ++ one c)%string, r. split; [rewrite append_assoc; reflexivity|left].
        rewrite !iscan_str_app, iscan_auto by exact Fr. cbn [append].
        change (one c) with (String c ""). cbn [iscan_str].
        unfold istep at 1. cbn [istep_at]. unfold iauto_step. change (tval src) with src.
        rewrite Ok. unfold auto_stop in Hst. rewrite Hcn, orb_false_r in Hst. rewrite Hst.
        reflexivity.
    + cbn [is_hard]. unfold pstep.
      apply linked_normal; [rewrite (proj2 (pv_add_live _ _)); exact Em|].
      apply sim_text; [exact Hsim|reflexivity].
    + left. apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate].
Qed.

(* Whether every byte is a symbol character. *)
Fixpoint sym_all (a : string) : bool :=
  match a with EmptyString => true | String c r => (symbol_char c && sym_all r)%bool end.

Local Lemma sym_all_run : forall s, sym_all (substring 0 (symbol_run s) s) = true.
Proof.
  induction s as [|c s IH]; [reflexivity|]. cbn [symbol_run].
  destruct (symbol_char c) eqn:E; [|reflexivity]. cbn [substring sym_all]. rewrite E. exact IH.
Qed.

Local Lemma iscan_symbol : forall a al txt sh o, sym_all a = true ->
  exists sh', iscan_str a (ISymbol al txt sh o) = ISymbol (al ++ a) txt sh' o.
Proof.
  induction a as [|c a IH]; intros al txt sh o H.
  - exists sh. rewrite append_empty_r. reflexivity.
  - cbn [sym_all] in H. apply andb_true_iff in H as [Hc H].
    cbn [iscan_str]. unfold istep. cbn [istep_at]. unfold isymbol_step. rewrite Hc. tred.
    destruct (IH (al ++ one c)%string txt (istep_at inline_attrs_enabled c sh) o H) as [sh' E].
    exists sh'. rewrite E, append_assoc. reflexivity.
Qed.

Local Lemma sym_all_bslash : forall a, sym_all a = true -> no_bslash a = true.
Proof.
  induction a as [|c a IH]; intros H; [reflexivity|]. cbn [sym_all] in H.
  apply andb_true_iff in H as [Hc H]. cbn [no_bslash]. rewrite (IH H), andb_true_r.
  destruct c as [[] [] [] [] [] [] [] []]; try discriminate Hc; reflexivity.
Qed.

(* The alphabet has the `:` only while tags are off. *)
Local Lemma colon_tags_off : in_alphabet ":"%char = true -> tags_enabled = false.
Proof.
  unfold in_alphabet. cbn. destruct tags_enabled; [|reflexivity]. cbn. discriminate.
Qed.

(* A symbol that does not close: the scanner reads its run while the
   shadow reads the same bytes as text, and takes the shadow at the byte
   that ends the run, or at the end of the line. *)
Local Lemma symbol_fail_settles : forall s' al txt sh o,
  tags_enabled = false ->
  ((nonempty_str al || Nat.ltb 0 (symbol_run s'))%bool = true ->
   starts_with ":"%char (sdrop (symbol_run s') s') = false) ->
  settles_in (ISymbol al txt sh o) sh s'.
Proof.
  induction s' as [|c r IH]; intros al txt sh o Htag H.
  - exists "", "". split; [reflexivity|right]. split; reflexivity.
  - cbn [symbol_run] in H. destruct (symbol_char c) eqn:Ec.
    + destruct (IH (al ++ one c)%string txt (istep c sh) o Htag) as (p & r' & -> & E).
      { intros _. apply H. rewrite orb_true_r. reflexivity. }
      exists (String c p), r'. split; [reflexivity|].
      assert (S1 : istep c (ISymbol al txt sh o) = ISymbol (al ++ one c) txt (istep c sh) o).
      { unfold istep. cbn [istep_at]. unfold isymbol_step. rewrite Ec. tred. reflexivity. }
      cbn [iscan_str]. rewrite S1. exact E.
    + exists (one c), r. split; [reflexivity|left].
      change (one c) with (String c ""). cbn [iscan_str].
      unfold istep. cbn [istep_at]. unfold isymbol_step. rewrite Ec, Htag. tred.
      rewrite !andb_false_r. cbn [sdrop starts_with] in H.
      destruct (nonempty_str al) eqn:Ea; [rewrite (H eq_refl) | rewrite andb_false_r];
        reflexivity.
Qed.

(* A `:` from text mode: a symbol, or the `:` as text. *)
Local Lemma scan_symbol : forall ps after len, scan_ih ps after len -> line_end after ->
  forall s' prev n v ws txt o,
    String.length (String ":"%char s') <= S len -> over_alphabet (String ":"%char s') = true ->
    sdrop n ps = (String ":"%char s' ++ after)%string ->
    same_prev (before ps n) prev ->
    vinv ps n false v -> Forall (never ps n) ws -> pv_mode v = PMNormal -> sim v txt o ->
    scanned ps n false v ws (IText false txt prev o) (String ":"%char s').
Proof.
  intros ps after len IH Hae s' prev n v ws txt o Hl Ha Hs Hpv V Fn Em Hsim.
  pose proof (alphabet_no_nl _ Ha) as Hnl.
  assert (Ht : tok_at ps n = Some (sym_tok s')).
  { rewrite (tok_at_line ps n _ after prev Hs Hae ltac:(discriminate) eq_refl eq_refl eq_refl eq_refl
                (or_introl eq_refl) eq_refl Hnl Hpv).
    reflexivity. }
  pose proof Ha as Ha'. apply (over_alphabet_cons ":"%char s' eq_refl) in Ha' as (_ & Hf & Hs').
  pose proof (colon_tags_off (proj1 (over_alphabet_cons ":"%char s' eq_refl Ha))) as Htag.
  pose proof Hsim as (v0 & Eo & Ht0 & Ev).
  assert (Fl : flush_text txt o = oview v) by (rewrite Eo, Ev; apply flush_view, Ht0).
  assert (S0 : istep ":"%char (IText false txt prev o)
               = ISymbol "" txt (IText false (txt ++ one ":"%char) (Some ":"%char) o) o)
    by (unfold istep; cbn [istep_at]; unfold ilead, itable; cbn; reflexivity).
  assert (Split : forall x j, x = (substring 0 j x ++ sdrop j x)%string).
  { induction x as [|y x IHx]; intros [|j]; try reflexivity. cbn. f_equal. apply IHx. }
  unfold sym_tok in Ht.
  destruct (Nat.ltb 0 (symbol_run s') && starts_with ":"%char (sdrop (symbol_run s') s'))%bool
    eqn:Ok.
  - (* a symbol *)
    apply andb_true_iff in Ok as [Hk Hc]. apply Nat.ltb_lt in Hk.
    pose proof (symbol_run_le s') as Le.
    pose proof (sym_all_run s') as Sa.
    pose proof (Split s' (symbol_run s')) as Es'.
    set (k := symbol_run s') in *. set (a := substring 0 k s') in *.
    destruct (sdrop k s') as [|c r] eqn:Ed; [discriminate|]. cbn [starts_with] in Hc.
    apply Ascii.eqb_eq in Hc. subst c.
    assert (La : String.length a = k).
    { pose proof (sdrop_length k s') as L. rewrite Ed in L. cbn in L.
      pose proof (f_equal String.length Es') as L2. rewrite length_append in L2. cbn in L2. lia. }
    assert (Ha0 : a <> EmptyString) by (intros E; rewrite E in La; cbn in La; lia).
    assert (Nb : no_bslash a = true) by exact (sym_all_bslash a Sa).
    rewrite Es' in Hs'. pose proof (over_alphabet_app_r _ _ Nb Hs') as Hc'.
    apply (over_alphabet_cons ":"%char r eq_refl) in Hc' as (_ & Hfr & Hr).
    assert (Sc : iscan_str (String ":"%char a ++ one ":"%char) (IText false txt prev o)
                 = IText false "" (Some ":"%char) (oemit (mk (Symbol a)) (oview v))).
    { cbn [append iscan_str]. rewrite S0. rewrite iscan_str_app.
      destruct (iscan_symbol a "" txt (IText false (txt ++ one ":"%char) (Some ":"%char) o) o Sa)
        as [sh' E]. rewrite E. cbn [append].
      change (one ":"%char) with (String ":"%char ""). cbn [iscan_str]. unfold istep.
      cbn [istep_at]. unfold isymbol_step. change (symbol_char ":"%char) with false. cbn iota.
      replace (tnonempty a) with true by (destruct a; [contradiction|reflexivity]).
      change (Ascii.eqb ":"%char ":"%char) with true. cbn [andb].
      change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s (tval txt) o)
        with (flush_text txt o).
      rewrite Fl. reflexivity. }
    apply (scan_tok ps after len IH (String ":"%char s') n false v ws (IText false txt prev o)
             (TSymbol a) (S (S k)) r (Some ":"%char)
             (IText false "" (Some ":"%char) (oemit (mk (Symbol a)) (oview v))) Hl Hs Fn V Em Ht).
    + cbn [tok_text]. rewrite Es' at 1. cbn [append]. rewrite append_assoc. reflexivity.
    + change (tok_text (TSymbol a)) with (String ":"%char (a ++ one ":"%char)).
      cbn [String.length]. rewrite length_append, La. cbn. lia.
    + cbn [tok_text]. rewrite str_last_app. reflexivity.
    + cbn [pend_esc with_esc]. exact Hr.
    + left. apply prev_ok_follow; [exact Hfr|reflexivity].
    + change (tok_text (TSymbol a)) with (String ":"%char a ++ one ":"%char)%string.
      rewrite Sc. apply settles_refl.
    + cbn [is_hard]. unfold pstep.
      apply linked_normal; [rewrite (proj2 (pv_add_live _ _)); exact Em|].
      exists (pv_add (Symbol a) v). split; [apply oemit_view; discriminate|].
      split; [apply top_add_nonstr; discriminate|reflexivity].
    + left. apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate].
  - (* the `:` as text, and a run after it that does not close *)
    apply (scan_tok_in ps after len IH (String ":"%char s') n false v ws (IText false txt prev o)
             (TText ":"%char) 1 s' (Some ":"%char)
             (IText false (txt ++ one ":"%char) (Some ":"%char) o) Hl Hs Fn V Em Ht).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + cbn [pend_esc with_esc]. exact Hs'.
    + right; left. intros t q o' E. injection E as <- _ _. destruct txt; reflexivity.
    + cbn [tok_text one iscan_str]. rewrite S0. apply (symbol_fail_settles s' "" txt _ o Htag).
      cbn [nonempty_str orb]. intros Hk.
      destruct (starts_with ":"%char (sdrop (symbol_run s') s')) eqn:E; [|reflexivity].
      rewrite Hk in Ok. discriminate Ok.
    + cbn [is_hard]. unfold pstep.
      apply linked_normal; [rewrite (proj2 (pv_add_live _ _)); exact Em|].
      apply sim_text; [exact Hsim|reflexivity].
    + left. apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate].
Qed.

(* `n` copies of a node, emitted one after another. *)
Fixpoint emits (n : nat) (x : node inline) (o : ostate) : ostate :=
  match n with O => o | S m => emits m x (oemit x o) end.

(* Where a run of `3 * q + r` periods from text leaves the text and the
   scope: with smart typography, an ellipsis node for every three and the
   one or two left over still pending; without it, all of it pending. *)
Definition dots_end (q r : nat) (txt : string) (o : ostate) : string * ostate :=
  if smart_typography
  then match q with
       | O => (txt ++ chars period r, o)
       | S _ => (chars period r, emits q (mk ellipsis_node) (flush_text txt o))
       end
  else (txt ++ chars period (3 * q + r), o).

Local Lemma dots3 : forall txt prev o,
  iscan_str (chars period 3) (IText false txt prev o)
  = if smart_typography
    then IText false "" (Some period) (oemit (mk ellipsis_node) (flush_text txt o))
    else IText false (txt ++ chars period 3) (Some period) o.
Proof. intros. reflexivity. Qed.

(* A run of periods from text, resolved. *)
Local Lemma dots_scan : forall q r txt prev o, r < 3 -> 0 < 3 * q + r ->
  rres (iscan_str (chars period (3 * q + r)) (IText false txt prev o))
  = IText false (fst (dots_end q r txt o)) (Some period) (snd (dots_end q r txt o))
  /\ forall c', Ascii.eqb c' period = false ->
     istep c' (iscan_str (chars period (3 * q + r)) (IText false txt prev o))
     = istep c' (IText false (fst (dots_end q r txt o)) (Some period)
                   (snd (dots_end q r txt o))).
Proof.
  induction q as [|q IH]; intros r txt prev o Hr Hpos.
  - assert (E : dots_end 0 r txt o = ((txt ++ chars period r)%string, o))
      by (unfold dots_end; destruct smart_typography; reflexivity).
    rewrite E. cbn [fst snd Nat.mul Nat.add]. destruct r as [|[|[|r]]]; [lia| | |lia].
    + change (iscan_str (chars period 1) (IText false txt prev o)) with (IPeriod false txt prev o).
      split; [reflexivity|]. intros c' Hc. unfold istep. cbn [istep_at].
      unfold iperiod_step. rewrite Hc. reflexivity.
    + change (iscan_str (chars period 2) (IText false txt prev o)) with (IPeriod true txt prev o).
      split; [reflexivity|]. intros c' Hc. unfold istep. cbn [istep_at].
      unfold iperiod_step. rewrite Hc. reflexivity.
  - replace (3 * S q + r) with (3 + (3 * q + r)) by lia.
    rewrite chars_add, iscan_str_app, dots3.
    destruct (Nat.eq_dec (3 * q + r) 0) as [E0|E0].
    + assert (q = 0) by lia. assert (r = 0) by lia. subst q r.
      unfold dots_end. cbn [Nat.mul Nat.add chars iscan_str].
      destruct smart_typography; split; reflexivity.
    + destruct smart_typography eqn:Es.
      * destruct (IH r "" (Some period) (oemit (mk ellipsis_node) (flush_text txt o)) Hr
                    ltac:(lia)) as [A B].
        assert (E : dots_end q r "" (oemit (mk ellipsis_node) (flush_text txt o))
                    = dots_end (S q) r txt o)
          by (unfold dots_end; rewrite Es; destruct q; reflexivity).
        rewrite E in A, B. split; [exact A|exact B].
      * destruct (IH r (txt ++ chars period 3)%string (Some period) o Hr ltac:(lia)) as [A B].
        assert (E : dots_end q r (txt ++ chars period 3) o = dots_end (S q) r txt o).
        { unfold dots_end. rewrite Es. rewrite append_assoc, <- chars_add.
          replace (3 + (3 * q + r)) with (3 * S q + r) by lia. reflexivity. }
        rewrite E in A, B. split; [exact A|exact B].
Qed.

Local Lemma sim_emits : forall q v o (x : inline),
  sim v "" o -> (forall s, x <> Str s) ->
  sim (pv_add_items (repeat x q) v) "" (emits q (mk x) o).
Proof.
  induction q as [|q IH]; intros v o x Hs Hx; [exact Hs|].
  cbn [repeat emits]. apply IH; [|exact Hx].
  exact (sim_node v "" o x Hs Hx).
Qed.

Local Lemma dots_sim : forall k v txt o, 0 < k -> sim v txt o ->
  sim (pv_add_items (dots_items k) v)
    (fst (dots_end (Nat.div k 3) (Nat.modulo k 3) txt o))
    (snd (dots_end (Nat.div k 3) (Nat.modulo k 3) txt o)).
Proof.
  intros k v txt o Hk Hs.
  pose proof (Nat.div_mod_eq k 3) as Dk.
  assert (Hn : forall s, ellipsis_node <> Str s)
    by (intros s0; unfold ellipsis_node; discriminate).
  unfold dots_items, dots_end. destruct smart_typography.
  - unfold pv_add_items. rewrite fold_left_app.
    fold (pv_add_items (repeat ellipsis_node (Nat.div k 3)) v).
    destruct (Nat.div k 3) as [|q] eqn:Eq.
    + cbn [repeat pv_add_items fold_left fst snd].
      destruct (Nat.modulo k 3) as [|r]; [lia|]. cbn [Nat.eqb fold_left].
      apply sim_text; [exact Hs|reflexivity].
    + cbn [fst snd].
      assert (H1 : sim (pv_add_items (repeat ellipsis_node (S q)) v) ""
                     (emits (S q) (mk ellipsis_node) (flush_text txt o))).
      { cbn [repeat emits pv_add_items fold_left].
        apply (sim_emits q (pv_add ellipsis_node v)); [|exact Hn].
        exact (sim_node v txt o _ Hs Hn). }
      destruct (Nat.modulo k 3) as [|r]; cbn [Nat.eqb fold_left]; [exact H1|].
      exact (sim_text _ "" _ (chars period (S r)) H1 eq_refl).
  - cbn [fst snd pv_add_items fold_left]. rewrite <- Dk. apply sim_text; [exact Hs|].
    destruct k; [lia|reflexivity].
Qed.

Local Lemma dstyle_of_rbrace : dstyle_of rbrace = None.
Proof.
  destruct (dstyle_of rbrace) as [k|] eqn:E; [|reflexivity].
  pose proof (dstyle_of_char _ _ E) as Ec. destruct (dchar_plain k) as (_ & Hr & _).
  rewrite Ec in Hr. discriminate Hr.
Qed.

(* A run of hyphens from text: the scanner holds it. *)
Local Lemma iscan_dashes : forall j n txt prev o,
  iscan_str (chars hyphen j) (IDash n txt prev o) = IDash (j + n) txt prev o.
Proof.
  induction j as [|j IH]; intros n txt prev o; [reflexivity|]. cbn [chars iscan_str].
  change (istep hyphen (IDash n txt prev o)) with (IDash (S n) txt prev o).
  rewrite IH. f_equal. lia.
Qed.

Local Lemma dash_run_scan : forall n txt prev o, 0 < n ->
  iscan_str (chars hyphen n) (IText false txt prev o) = IDash n txt prev o.
Proof.
  intros [|n] txt prev o Hn; [lia|]. cbn [chars iscan_str].
  change (istep hyphen (IText false txt prev o)) with (IDash 1 txt prev o).
  rewrite iscan_dashes. f_equal. lia.
Qed.

(* The byte after a run cuts it into dashes, unless it is the `}` of the
   row spelled with the hyphen. *)
Local Lemma dash_settle : forall n txt prev o c', Ascii.eqb c' hyphen = false ->
  (Ascii.eqb c' rbrace = true -> dstyle_of hyphen = None) ->
  istep c' (IDash n txt prev o)
  = istep c' (IText false (fst (odashes n cursor_start txt o)) (Some hyphen)
                (snd (odashes n cursor_start txt o))).
Proof.
  intros n txt prev o c' Hh Hr. unfold istep. cbn [istep_at]. unfold idash_step. rewrite Hh.
  destruct (Ascii.eqb c' rbrace) eqn:E;
    [|destruct (odashes n cursor_start txt o); reflexivity].
  rewrite (Hr eq_refl). apply Ascii.eqb_eq in E. subst c'.
  destruct (odashes n cursor_start txt o) as [t o']. cbn [fst snd].
  tred. unfold ilead, itable.
  change (is_bslash rbrace) with false. change (is_tick rbrace) with false.
  change (Ascii.eqb rbrace dollar) with false. change (Ascii.eqb rbrace period) with false.
  change (Ascii.eqb rbrace hyphen) with false. change (Ascii.eqb rbrace lbrace) with false.
  change (Ascii.eqb rbrace bang) with false. change (Ascii.eqb rbrace lt) with false.
  change (Ascii.eqb rbrace ":"%char) with false. change (Ascii.eqb rbrace lbrack) with false.
  change (Ascii.eqb rbrace rbrack) with false. change (Ascii.eqb rbrace hat) with false.
  cbn [andb]. rewrite dstyle_of_rbrace. change (Ascii.eqb rbrace percent) with false.
  rewrite andb_false_r. tred. reflexivity.
Qed.

(* Without positions a run of dash nodes is copies of one node, and
   where the run stops is not looked at. *)
Local Lemma odash_run_emits : forall w x count after stop o,
  @odash_run semantic_pos w x count after stop o = emits count (mk x) o.
Proof.
  intros w x count. induction count as [|m IH]; intros after stop o; [reflexivity|].
  cbn [odash_run emits]. apply IH.
Qed.

Local Lemma odashes_stop : forall n stop stop' txt o,
  odashes n stop txt o = odashes n stop' txt o.
Proof.
  intros n stop stop' txt o. unfold odashes. destruct (dash_run_smart n); [|reflexivity].
  destruct (dash_counts n) as [[em en] lit]. rewrite !odash_run_emits. reflexivity.
Qed.

Local Lemma sim_emits_after : forall q v txt o (x : inline),
  sim v txt o -> (forall s, x <> Str s) ->
  sim (pv_add_items (repeat x (S q)) v) "" (emits (S q) (mk x) (flush_text txt o)).
Proof.
  intros q v txt o x Hs Hx. cbn [repeat emits].
  apply (sim_emits q (pv_add x v)); [|exact Hx]. exact (sim_node v txt o x Hs Hx).
Qed.

(* A run of hyphens, cut or not, as the view and the scanner hold it. *)
Local Lemma dash_sim : forall k v txt o, 0 < k -> sim v txt o ->
  sim (pv_add_items (dash_items k) v)
    (fst (odashes k cursor_start txt o)) (snd (odashes k cursor_start txt o)).
Proof.
  intros k v txt o Hk Hs. unfold dash_items, odashes.
  destruct (dash_run_smart k) eqn:Ed.
  - assert (H2 : 2 <= k)
      by (unfold dash_run_smart in Ed; apply andb_true_iff in Ed as [Ed _];
          apply Nat.leb_le, Ed).
    pose proof (dash_counts_some k H2) as Hc.
    destruct (dash_counts k) as [[em en] lit]. cbn [fst snd].
    rewrite !odash_run_emits.
    assert (Hm : forall s, emdash_node <> Str s) by (intros s0; discriminate).
    assert (Hn : forall s, endash_node <> Str s) by (intros s0; discriminate).
    unfold pv_add_items. rewrite fold_left_app.
    fold (pv_add_items (repeat emdash_node em) v).
    fold (pv_add_items (repeat endash_node en) (pv_add_items (repeat emdash_node em) v)).
    destruct em as [|em].
    + destruct en as [|en]; [cbn in Hc; lia|].
      cbn [repeat pv_add_items fold_left emits].
      exact (sim_emits_after en v txt o endash_node Hs Hn).
    + apply sim_emits; [|exact Hn].
      exact (sim_emits_after em v txt o emdash_node Hs Hm).
  - cbn [fst snd pv_add_items fold_left]. apply sim_text; [exact Hs|].
    destruct k; [lia|reflexivity].
Qed.

Local Lemma run_of_split : forall c j rest,
  (forall d r, rest = String d r -> d <> c) -> run_of c (chars c j ++ rest) = j.
Proof.
  intros c j rest Hr. induction j as [|j IH]; cbn [chars append run_of].
  - destruct rest as [|d r]; [reflexivity|]. cbn [run_of].
    destruct (Ascii.eqb d c) eqn:E; [|reflexivity]. apply Ascii.eqb_eq in E.
    destruct (Hr d r eq_refl E).
  - rewrite Ascii.eqb_refl, IH. reflexivity.
Qed.

Local Lemma sdrop_chars : forall c j x, sdrop j (chars c j ++ x) = x.
Proof. intros c j x. induction j as [|j IH]; [reflexivity|exact IH]. Qed.

(* A `^` right after a bracket opens, with footnotes on: the bracket is
   taken back, and the `^` read as usual inside the label's layer. *)
Local Lemma istep_hat_note : forall im o, notes_enabled = true ->
  istep hat (IText false "" (Some lbrack) (bpush im o))
  = wrap [WNote im null_span (NS false "") o] (itable hat "" (Some lbrack) (bpush im o)).
Proof.
  intros im o Hen. unfold istep. cbn [istep_at]. unfold ilead.
  change (is_bslash hat) with false. change (is_tick hat) with false.
  change (Ascii.eqb hat dollar) with false. change (Ascii.eqb hat period) with false.
  change (Ascii.eqb hat hyphen) with false. change (Ascii.eqb hat lbrace) with false.
  change (Ascii.eqb hat bang) with false. change (Ascii.eqb hat lt) with false.
  change (Ascii.eqb hat ":"%char) with false. change (Ascii.eqb hat lbrack) with false.
  change (Ascii.eqb hat rbrack) with false. change (Ascii.eqb hat hat) with true. cbn iota.
  change (note_pos "" (Some lbrack)) with true. cbn [andb]. rewrite Hen, bunpush_bpush.
  reflexivity.
Qed.

(* Layers the byte after a token passes keep the token's settling. *)
Local Lemma settles_wrap : forall ws X st next,
  (forall c, next = Some c -> Forall (fun w => wstep c w <> None) ws) ->
  settles X st next -> settles (wrap ws X) (wrap ws st) next.
Proof.
  intros ws X st [c|] Hw H; cbn [settles] in *.
  - rewrite !(istep_wrap c ws _ (Hw c eq_refl)), H. reflexivity.
  - rewrite !rres_wrap, H. reflexivity.
Qed.

(* The view enters a token of several bytes at its first. *)
Local Lemma vinv_atom : forall ps n v t l x e,
  vinv ps n false v -> pv_mode v = PMNormal -> tok_at ps n = Some (t, l) ->
  pstep ps n false t v = pv_setmode (PMAtom x e) v ->
  vinv ps (S n) false (pv_setmode (PMAtom x e) v).
Proof.
  intros ps n v t l x e V Em Ht Hp.
  pose proof (vinv_step ps n false _ l v V Em Ht) as (Ok1 & Ti1 & _). rewrite Hp in Ok1, Ti1.
  split; [|split; [exact Ti1|discriminate]].
  destruct Ok1 as (A1 & _ & _ & A5 & A6 & _). pose proof V as ((D & Bd & Be & _) & _).
  split; [exact A1|].
  split; [intros y Hy; specialize (Bd y Hy); lia|].
  split; [intros p k c0 H; specialize (Be p k c0 H); lia|].
  split; [exact A5|]. split; [exact A6|exact Logic.I].
Qed.

(* The `!` an image's bracket put back, against the `!` read as text. *)
Local Lemma bang_flush : forall v txt o, sim v txt o -> tidy v ->
  ospan_bang true null_span (flush_text txt o) = flush_text (txt ++ one bang) o.
Proof.
  intros v txt o Hsim Ti. destruct (tidy_top v Ti) as [Hn Hc].
  pose proof Hsim as (v0 & Eo & Ht0 & Ev).
  assert (Fl : flush_text txt o = oview v) by (rewrite Eo, Ev; apply flush_view, Ht0).
  rewrite Fl, (ospan_bang_view true v Hn Hc).
  destruct (sim_text v txt o (one bang) Hsim eq_refl) as (v1 & Eo1 & Ht1 & Ev1).
  rewrite Eo1, (flush_view _ _ Ht1), Ev1. reflexivity.
Qed.

(* A footnote reference from text mode: its `[` and its `^`, after which
   the view walks the label byte by byte.  `pre` is the `!` of an image's
   bracket, which the reading has as text before the reference. *)
Local Lemma scan_note : forall ps after len, scan_ih ps after len ->
  forall pre s'' n v ws core w lab im o sh,
    String.length (pre ++ String lbrack (String hat s'')) <= S len ->
    over_alphabet s'' = true ->
    sdrop n ps = ((pre ++ String lbrack (String hat s'')) ++ after)%string ->
    Forall (never ps n) ws ->
    pruns ps n false v (n + String.length pre) false w ->
    vinv ps (n + String.length pre) false w -> pv_mode w = PMNormal ->
    tok_at ps (n + String.length pre) = Some (TNote lab, S (S (S (String.length lab)))) ->
    ospan_bang im null_span o = oview w ->
    iscan_str (pre ++ String lbrack (one hat)) core = INote false im "" null_span sh o ->
    scanned ps n false v ws core (pre ++ String lbrack (String hat s'')).
Proof.
  intros ps after len IH pre s'' n v ws core w lab im o sh Hl Ha Hs Fn R W Emw Ht Hob Sc.
  set (m := n + String.length pre) in *.
  pose proof (tok_at_note ps m lab _ Ht) as [_ (r & Hen & Hsm & Hgo)].
  set (x := FootnoteReference (normalize_label lab)).
  set (w1 := pv_setmode (PMAtom x (S (S m) + String.length lab)) w).
  assert (Pst : pstep ps m false (TNote lab) w = w1).
  { cbn [pstep]. unfold tok_end. rewrite Ht. unfold w1. do 2 f_equal. lia. }
  assert (U1 : punit ps m false w = Some (S m, false, w1))
    by (unfold punit; rewrite Emw, Ht; cbv zeta; rewrite Pst; reflexivity).
  pose proof (sdrop_succ ps m lbrack _ Hsm) as Hs1.
  pose proof (get_sdrop ps (S m) hat _ Hs1) as Hg1.
  pose proof (sdrop_succ ps (S m) hat _ Hs1) as Hs2.
  assert (Pb : pbyte (S m) hat w1 = w1).
  { unfold pbyte, w1. cbn [pv_mode pv_setmode].
    replace (S m =? S (S m) + String.length lab)%nat with false
      by (symmetry; apply Nat.eqb_neq; lia). reflexivity. }
  assert (U2 : punit ps (S m) false w1 = Some (S (S m), false, w1)).
  { unfold punit. replace (pv_mode w1) with (PMAtom x (S (S m) + String.length lab))
      by reflexivity. rewrite Hg1, Pb. reflexivity. }
  assert (V1 : vinv ps (S m) false w1)
    by exact (vinv_atom ps m w _ _ x _ W Emw Ht Pst).
  assert (V2 : vinv ps (S (S m)) false w1).
  { rewrite <- Pb. destruct V1 as (Ok1 & Ti1 & _).
    split; [apply pv_ok_byte; [exact Ok1|unfold w1; discriminate]|].
    split; [apply pbyte_tidy, Ti1|discriminate]. }
  set (bytes := (pre ++ String lbrack (one hat))%string).
  assert (Lb : n + String.length bytes = S (S m))
    by (unfold bytes, m; rewrite length_append; cbn [String.length one]; lia).
  assert (Es : (pre ++ String lbrack (String hat s''))%string = (bytes ++ s'')%string)
    by (unfold bytes; rewrite append_assoc; reflexivity).
  pose proof Hs as Hs'. rewrite Es, append_assoc in Hs'.
  apply (scan_advance_gen ps after len IH (pre ++ String lbrack (String hat s'')) n false v ws
           core bytes s'' (Some hat) [] (INote false im "" null_span sh o) false w1 Hl Hs Fn Es);
    rewrite ?Lb.
  - unfold bytes. apply app_ne_r. discriminate.
  - apply (pruns_trans ps n false v m false w); [exact R|].
    exact (pruns_step _ _ _ _ _ _ _ _ _ _ U1 (pruns_one _ _ _ _ _ _ _ U2)).
  - exact V2.
  - rewrite <- Lb, (before_chunk ps n bytes _ Hs'). unfold bytes.
    rewrite str_last_app. apply same_prev_refl.
  - cbn [pend_esc with_esc]. exact Ha.
  - right; left. intros t q o' E. discriminate E.
  - cbn [wrap]. unfold bytes. rewrite Sc. apply settles_refl.
  - constructor.
  - unfold linked. replace (pv_mode w1) with (PMAtom x (S (S m) + String.length lab))
      by reflexivity.
    split; [reflexivity|]. split; [lia|]. right; left.
    exists false, im, "", sh, o, lab. split; [reflexivity|]. split; [exact Hob|].
    split; [rewrite Hs2; exact Hgo|]. split; reflexivity.
Qed.

Local Lemma scan_sim : forall ps after, line_end after -> forall len, scan_ih ps after len.
Proof.
  intros ps after Hae len. induction len as [|len IH];
    intros s prev n h v ws core Hl Ha Hp Hs Hpv V Fn L;
    destruct s as [|c s'];
    try (apply (scanned_nil ps n h v ws core prev); [assumption|assumption|assumption|];
         rewrite Hs; exact Hae).
  { cbn in Hl. lia. }
  pose proof Ha as Ha0. unfold alpha_ok in Ha.
  destruct (pv_mode v) as [|b im kids d e txt|x e|im sk sat se] eqn:Em.
  3: { (* inside a token *)
       exact (scan_atom ps after len IH Hae c s' prev n h v ws core x e Hl Ha0 Hs V Fn L Em). }
  3: { (* in a span's spec *)
       pose proof L as L1. unfold linked in L1. rewrite Em in L1. destruct L1 as (-> & Si).
       exact (scan_spec ps after len IH c s' n v ws core Hl Ha Hs V Fn
                (or_intror (ex_intro _ im (ex_intro _ sk (ex_intro _ sat
                   (ex_intro _ se (conj Em Si))))))). }
  2: { (* in a region *)
       apply (scan_region ps after len IH c s' prev n h v ws core); try assumption;
         [rewrite Em; discriminate|intros ? ?; rewrite Em; discriminate
         |intros ? ? ? ?; rewrite Em; discriminate]. }
  (* in text mode *)
  pose proof L as L0. unfold linked in L. rewrite Em in L. destruct L as (-> & txt & o & -> & Hsim).
  cbn [pend_esc with_esc] in Ha.
  destruct (is_bslash c) eqn:Eb.
  { unfold is_bslash in Eb. apply Ascii.eqb_eq in Eb. subst c.
    exact (scan_esc ps after len IH Hae s' prev n false v ws _ Hl Ha Hs Hpv V Fn L0 Em). }
  pose proof V as (Ok & Ti & _).
  pose proof Hsim as (v0 & Eo & Ht & Ev).
  pose proof Ha as Ha'. apply (over_alphabet_cons c s' Eb) in Ha' as (Hc & Hf & Hs').
  pose proof (no_note_ok' prev c s' txt o after Hp) as Hnote.
  destruct (is_tick c) eqn:Etk.
  { (* a verbatim *)
    unfold is_tick in Etk. apply Ascii.eqb_eq in Etk. subst c.
    assert (Htk : exists m body cl r l, tok_at ps n = Some (TVerb 0 m body cl r, l)).
    { unfold tok_at. rewrite Hs. unfold next_tok, esc_tok, dots_tok, dash_tok, bang_tok, lbrack_tok, rbrack_tok, lbrace_tok, delim_tok. cbn [append].
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
    - exact Hsp.
    - cbn [tok_text]. symmetry. apply length_chars.
    - cbn [tok_text]. destruct k as [|k]; [lia|]. rewrite Sl. reflexivity.
    - cbn [pend_esc with_esc]. rewrite Hsp in Ha. exact (over_alphabet_app_r _ rest (Nb k) Ha).
    - right; left. intros t q o' E. unfold X in E. injection E as <- _ _.
      destruct k as [|k]; [lia|]. destruct txt; reflexivity.
    - cbn [tok_text]. destruct rest as [|c' r'] eqn:Er; cbn [get settles].
      + rewrite Rr, Ix1. reflexivity.
      + destruct (Hr1 c' r' eq_refl) as [E1 E2]. exact (Ix2 c' E1 E2).
    - cbn [is_hard]. unfold pstep.
      apply linked_normal; [rewrite (proj2 (pv_add_live _ _)); exact Em|].
      cbn [tok_text]. apply sim_text; [exact Hsim|]. destruct k as [|k]; [lia|]. reflexivity.
    - left. apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate]. }
  pose proof (alphabet_no_nl _ Ha) as Hnl.
  assert (Htok : Ascii.eqb c bang = false -> Ascii.eqb c lbrack = false ->
                 Ascii.eqb c lbrace = false -> Ascii.eqb c rbrack = false ->
                 tok_at ps n = next_tok prev (String c s'))
    by (intros Hbg Hlk Hlb Hrb;
        exact (tok_at_line ps n _ after prev Hs Hae ltac:(discriminate) Etk Edl Hbg Hlk
                 (or_introl Hlb) Hrb Hnl Hpv)).
  pose proof (fun t l rest prev1 core1 =>
                scan_tok ps after len IH (String c s') n false v ws (IText false txt prev o)
                  t l rest prev1 core1 Hl Hs Fn V Em) as ST.
  (* a token the view reads in text mode *)
  assert (NrmN : forall t l rest prev1 txt' o',
            tok_at ps n = Some (t, l) ->
            String c s' = (tok_text t ++ rest)%string -> l = String.length (tok_text t) ->
            same_prev (str_last (tok_text t) (before ps n)) prev1 ->
            over_alphabet rest = true ->
            note_ok prev1 (IText false txt' prev1 o') rest (rest ++ after) ->
            settles (iscan_str (tok_text t) (IText false txt prev o)) (IText false txt' prev1 o')
              (get 0 rest) ->
            is_hard t = false -> pv_mode (pstep ps n false t v) = PMNormal ->
            sim (pstep ps n false t v) txt' o' ->
            scanned ps n false v ws (IText false txt prev o) (String c s')).
  { intros t l rest prev1 txt' o' Ht0 Es El Hp1 Ha1 Hf1 Hset Hh Em1 Hs1.
    apply (ST t l rest prev1 (IText false txt' prev1 o') Ht0 Es El Hp1 Ha1 Hf1 Hset);
      [rewrite Hh; apply linked_normal; assumption|left; exact Em1]. }
  assert (Nrm : forall t l rest prev1 txt' o',
            tok_at ps n = Some (t, l) ->
            String c s' = (tok_text t ++ rest)%string -> l = String.length (tok_text t) ->
            same_prev (str_last (tok_text t) (before ps n)) prev1 ->
            over_alphabet rest = true -> prev_ok prev1 rest = true ->
            settles (iscan_str (tok_text t) (IText false txt prev o)) (IText false txt' prev1 o')
              (get 0 rest) ->
            is_hard t = false -> pv_mode (pstep ps n false t v) = PMNormal ->
            sim (pstep ps n false t v) txt' o' ->
            scanned ps n false v ws (IText false txt prev o) (String c s'))
    by (intros t l rest prev1 txt' o' Ht0 Es El Hp1 Ha1 Hf1;
        exact (NrmN t l rest prev1 txt' o' Ht0 Es El Hp1 Ha1 (or_introl Hf1))).
  destruct (Ascii.eqb c period) eqn:Epd.
  { (* a run of periods *)
    apply Ascii.eqb_eq in Epd. subst c.
    destruct (run_split period s') as (j & rest & Es' & Hr).
    set (k := S j).
    assert (Hsp : String period s' = (chars period k ++ rest)%string) by (rewrite Es'; reflexivity).
    assert (Hrun : run_of period (String period s') = k)
      by (rewrite Hsp; apply run_of_split, Hr).
    pose proof (Nat.div_mod_eq k 3) as Dk.
    pose proof (Nat.mod_upper_bound k 3 ltac:(lia)) as Mk.
    destruct (dots_scan (Nat.div k 3) (Nat.modulo k 3) txt prev o Mk ltac:(unfold k in *; lia))
      as [D1 D2].
    rewrite <- Dk in D1, D2.
    apply (Nrm (TDots k) k rest (Some period)
             (fst (dots_end (Nat.div k 3) (Nat.modulo k 3) txt o))
             (snd (dots_end (Nat.div k 3) (Nat.modulo k 3) txt o))).
    - rewrite Htok by first [reflexivity|assumption]. unfold next_tok, dots_tok. rewrite Hrun. reflexivity.
    - exact Hsp.
    - cbn [tok_text]. symmetry. apply length_chars.
    - cbn [tok_text]. unfold k.
      assert (Sl : forall m p, str_last (chars period (S m)) p = Some period)
        by (induction m as [|m IHm]; intros p; [reflexivity|exact (IHm (Some period))]).
      rewrite Sl. reflexivity.
    - rewrite Hsp in Ha. exact (over_alphabet_app_r _ rest (no_bslash_chars period k eq_refl) Ha).
    - apply prev_ok_plain; reflexivity.
    - cbn [tok_text]. destruct rest as [|c' r'] eqn:Er; cbn [get settles].
      + rewrite D1. reflexivity.
      + apply D2. destruct (Ascii.eqb c' period) eqn:E; [|reflexivity].
        apply Ascii.eqb_eq in E. destruct (Hr c' r' eq_refl E).
    - reflexivity.
    - apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate].
    - unfold pstep. apply dots_sim; [unfold k; lia|exact Hsim]. }
  destruct (Ascii.eqb c hyphen) eqn:Ehy.
  { (* a run of hyphens, or the closer of the row spelled with one *)
    apply Ascii.eqb_eq in Ehy. subst c.
    destruct (run_split hyphen s') as (j & rest & Es' & Hr).
    set (k := S j).
    assert (Hsp : String hyphen s' = (chars hyphen k ++ rest)%string) by (rewrite Es'; reflexivity).
    assert (Hrun : run_of hyphen (String hyphen s') = k)
      by (rewrite Hsp; apply run_of_split, Hr).
    assert (Sd : sdrop k (String hyphen s') = rest) by (rewrite Hsp; apply sdrop_chars).
    assert (Hrh : starts_with hyphen rest = false).
    { destruct rest as [|d r]; [reflexivity|]. cbn [starts_with].
      destruct (Ascii.eqb d hyphen) eqn:E; [|reflexivity]. apply Ascii.eqb_eq in E.
      destruct (Hr d r eq_refl E). }
    assert (Hfh : forall s, prev_ok (Some hyphen) s = true)
      by (intros s; apply prev_ok_plain; reflexivity).
    destruct (match dstyle_of hyphen with Some _ => starts_with rbrace rest | None => false end)
      eqn:Cl.
    - (* the row's closer, after a dash when the run is longer than its
         one hyphen *)
      destruct (dstyle_of hyphen) as [kd|] eqn:Ek; [|discriminate Cl].
      pose proof (alphabet_hyphen_row Hc) as Hrow. unfold hyphen_row_ok in Hrow.
      rewrite Ek in Hrow. apply Nat.eqb_eq in Hrow.
      destruct j as [|j].
      2: { (* a dash of all but the last hyphen, which the scanner holds with
              the run until the `}` *)
        destruct rest as [|c' r]; [discriminate Cl|]. cbn [starts_with] in Cl.
        apply Ascii.eqb_eq in Cl. subst c'.
        assert (Hsp2 : String hyphen s'
                       = (chars hyphen (S j) ++ String hyphen (String rbrace r))%string).
        { rewrite Hsp. unfold k. clear. generalize (String rbrace r).
          induction j as [|j IHj]; intros x; [reflexivity|].
          cbn [chars append] in *. rewrite IHj. reflexivity. }
        assert (Sl : forall m p, str_last (chars hyphen (S m)) p = Some hyphen)
          by (induction m as [|m IHm]; intros p; [reflexivity|exact (IHm (Some hyphen))]).
        apply (scan_tok_in ps after len IH (String hyphen s') n false v ws
                 (IText false txt prev o) (TDash (S j)) (S j)
                 (String hyphen (String rbrace r)) (Some hyphen)
                 (IText false (fst (odashes (S j) cursor_start txt o)) (Some hyphen)
                    (snd (odashes (S j) cursor_start txt o)))
                 Hl Hs Fn V Em).
        - rewrite Htok by first [reflexivity|assumption]. unfold next_tok, dash_tok. rewrite Hrun, Ek, Sd, Hrow. cbn. reflexivity.
        - exact Hsp2.
        - cbn [tok_text]. symmetry. apply length_chars.
        - cbn [tok_text]. rewrite Sl. reflexivity.
        - cbn [pend_esc with_esc]. rewrite Hsp2 in Ha.
          exact (over_alphabet_app_r _ _ (no_bslash_chars hyphen (S j) eq_refl) Ha).
        - left. apply Hfh.
        - (* the two agree once the closer's hyphen and the `}` are read *)
          exists (String hyphen (one rbrace)), r. split; [reflexivity|left].
          cbn [tok_text]. rewrite (dash_run_scan (S j) txt prev o ltac:(lia)).
          cbn [iscan_str one].
          change (istep hyphen (IText false (fst (odashes (S j) cursor_start txt o))
                                  (Some hyphen) (snd (odashes (S j) cursor_start txt o))))
            with (IDash 1 (fst (odashes (S j) cursor_start txt o)) (Some hyphen)
                    (snd (odashes (S j) cursor_start txt o))).
          unfold istep. cbn [istep_at]. unfold idash_step. rewrite Ascii.eqb_refl.
          cbn [istep_at]. unfold idash_step. change (Ascii.eqb rbrace hyphen) with false.
          rewrite Ascii.eqb_refl, Ek, Hrow. cbn [Nat.leb Nat.sub].
          replace (S (S j) - 1) with (S j) by lia.
          rewrite (odashes_stop (S j) _ cursor_start).
          destruct (odashes (S j) cursor_start txt o) as [t o']. cbn [fst snd].
          change (odashes 0 _ t o') with ((t ++ "")%string, o').
          cbv beta iota. rewrite append_empty_r. reflexivity.
        - cbn [is_hard]. apply linked_normal.
          + apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate].
          + unfold pstep. apply dash_sim; [lia|exact Hsim].
        - left. apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate]. }
      unfold k in *. clear k.
      pose proof (dstyle_of_char _ _ Ek) as Ekc.
      destruct rest as [|c' r]; [discriminate Cl|]. cbn [starts_with] in Cl.
      apply Ascii.eqb_eq in Cl. subst c'.
      assert (Et : tok_text (TDelim kd true false true) = String hyphen (one rbrace))
        by (cbn [tok_text]; unfold dtoken; rewrite Hrow, Ekc; reflexivity).
      cbn [chars append] in Hsp. injection Hsp as Hs''.
      pose proof Hs' as Hx. rewrite Hs'' in Hx.
      apply (over_alphabet_cons rbrace r eq_refl) in Hx as (_ & Hfr & Hr').
      destruct (resolve_sim ps n false kd true txt None (Some rbrace) v o Ok Em
                  (proj1 (proj2 (proj2 Ti))) Hsim) as (txt' & o' & Er & Ss).
      apply (Nrm (TDelim kd true false true) 2 r (Some rbrace) txt' o').
      + rewrite Htok by first [reflexivity|assumption]. unfold next_tok, dash_tok. rewrite Hrun, Ek, Sd, Hrow. reflexivity.
      + rewrite Et, Hs''. reflexivity.
      + rewrite Et. reflexivity.
      + rewrite Et. reflexivity.
      + exact Hr'.
      + apply prev_ok_follow; [exact Hfr|reflexivity].
      + rewrite Et. cbn [iscan_str one].
        change (istep hyphen (IText false txt prev o)) with (IDash 1 txt prev o).
        unfold istep. cbn [istep_at]. unfold idash_step.
        change (Ascii.eqb rbrace hyphen) with false. rewrite Ascii.eqb_refl, Ek, Hrow.
        cbn [Nat.leb Nat.sub].
        change (odashes 0 _ txt o) with ((txt ++ "")%string, o).
        cbv beta iota. tred. rewrite append_empty_r, Er.
        apply settles_refl.
      + reflexivity.
      + apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate].
      + exact Ss.
    - (* dashes *)
      assert (Hnc : forall c' r', rest = String c' r' -> Ascii.eqb c' rbrace = true ->
                dstyle_of hyphen = None).
      { intros c' r' -> E. cbn [starts_with] in Cl. rewrite E in Cl.
        destruct (dstyle_of hyphen); [discriminate Cl|reflexivity]. }
      apply (Nrm (TDash k) k rest (Some hyphen) (fst (odashes k cursor_start txt o))
               (snd (odashes k cursor_start txt o))).
      + rewrite Htok by first [reflexivity|assumption]. unfold next_tok, dash_tok. rewrite Hrun, Sd.
        destruct (dstyle_of hyphen); [rewrite Cl|]; reflexivity.
      + exact Hsp.
      + cbn [tok_text]. symmetry. apply length_chars.
      + cbn [tok_text]. unfold k.
        assert (Sl : forall m p, str_last (chars hyphen (S m)) p = Some hyphen)
          by (induction m as [|m IHm]; intros p; [reflexivity|exact (IHm (Some hyphen))]).
        rewrite Sl. reflexivity.
      + rewrite Hsp in Ha. exact (over_alphabet_app_r _ rest (no_bslash_chars hyphen k eq_refl) Ha).
      + apply Hfh.
      + cbn [tok_text]. rewrite (dash_run_scan k txt prev o ltac:(unfold k; lia)).
        destruct rest as [|c' r'] eqn:Er; cbn [get settles].
        * cbn [rres iresolve]. destruct (odashes k cursor_start txt o); reflexivity.
        * apply dash_settle; [|exact (Hnc c' r' eq_refl)].
          cbn [starts_with] in Hrh. exact Hrh.
      + reflexivity.
      + apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate].
      + unfold pstep. apply dash_sim; [unfold k; lia|exact Hsim]. }
  destruct (Ascii.eqb c bang) eqn:Ebg.
  { (* a `!`: an image's bracket before a `[`, or text *)
    apply Ascii.eqb_eq in Ebg. subst c.
    assert (S0 : istep bang (IText false txt prev o) = IBang txt prev o) by reflexivity.
    assert (Hbt : tok_at ps n = Some (bang_tok (s' ++ after)))
      by (unfold tok_at; rewrite Hs; reflexivity).
    destruct (starts_with lbrack s') eqn:Sb.
    - destruct s' as [|d s'']; [discriminate|]. cbn [starts_with] in Sb.
      apply Ascii.eqb_eq in Sb. subst d.
      pose proof (over_alphabet_cons lbrack s'' eq_refl Hs') as (_ & Hf2 & Hs'').
      assert (Sc1 : istep lbrack (IBang txt prev o)
                    = IText false "" (Some lbrack) (bpush true (flush_text txt o))).
      { unfold istep. cbn [istep_at]. unfold ibang_step. rewrite Ascii.eqb_refl.
        change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s (tval txt) o)
          with (flush_text txt o). tred. reflexivity. }
      destruct (note_at (s'' ++ after)) as [lab|] eqn:Na.
      { (* a footnote reference after it: the `!` is text *)
        destruct s'' as [|h0 s3];
          [destruct Hae as [->|[r ->]]; cbn [append note_at] in Na; [discriminate Na|];
           change (Ascii.eqb nl_char hat) with false in Na; rewrite andb_false_r in Na;
           discriminate Na|].
        cbn [append note_at] in Na.
        destruct (notes_enabled && Ascii.eqb h0 hat)%bool eqn:E0; [|discriminate Na].
        apply andb_true_iff in E0 as [Hen E0]. apply Ascii.eqb_eq in E0. subst h0.
        apply (over_alphabet_cons hat s3 eq_refl) in Hs'' as (_ & _ & Hs3).
        assert (Ht0 : tok_at ps n = Some (TText bang, 1)).
        { rewrite Hbt. unfold bang_tok. cbn [append starts_with sdrop].
          rewrite Ascii.eqb_refl. cbn [note_at]. rewrite Hen. cbn [andb].
          change (Ascii.eqb hat hat) with true. cbn iota. rewrite Na. reflexivity. }
        apply (scan_note ps after len IH (one bang) s3 n v ws (IText false txt prev o)
                 (pv_add (Str (one bang)) v) lab true (flush_text txt o)
                 (itable hat "" (Some lbrack) (bpush true (flush_text txt o))) Hl Hs3 Hs Fn).
        - exact (pruns_one _ _ _ _ _ _ _ (punit_tok ps n false (TText bang) 1 v Em Ht0
                                            (or_intror eq_refl))).
        - exact (vinv_step ps n false (TText bang) 1 v V Em Ht0).
        - rewrite (proj2 (pv_add_live _ _)). exact Em.
        - cbn [String.length one]. rewrite Nat.add_1_r.
          unfold tok_at. rewrite (sdrop_succ ps n bang _ Hs). cbn [append].
          unfold next_tok, esc_tok, dots_tok, dash_tok, bang_tok, lbrack_tok, rbrack_tok,
            lbrace_tok, delim_tok.
          change (Ascii.eqb lbrack nl_char) with false. change (is_bslash lbrack) with false.
          change (is_tick lbrack) with false. change (Ascii.eqb lbrack dollar) with false.
          change (Ascii.eqb lbrack lt) with false. change (Ascii.eqb lbrack ":"%char) with false.
          change (Ascii.eqb lbrack period) with false. change (Ascii.eqb lbrack hyphen) with false.
          change (Ascii.eqb lbrack bang) with false. rewrite Ascii.eqb_refl. cbn iota.
          cbn [note_at]. rewrite Hen. change (Ascii.eqb hat hat) with true. cbn [andb].
          match goal with |- context [note_go false ?x] =>
            replace (note_go false x) with (Some lab) by (symmetry; exact Na) end.
          reflexivity.
        - rewrite (bang_flush v txt o Hsim Ti).
          destruct (sim_text v txt o (one bang) Hsim eq_refl) as (v1 & Eo1 & Ht1 & Ev1).
          rewrite Eo1, (flush_view _ _ Ht1), Ev1. reflexivity.
        - cbn [append iscan_str one]. rewrite S0, Sc1. exact (istep_hat_note true _ Hen). }
      apply (NrmN (TOpen true) 2 s'' (Some lbrack) "" (bpush true (flush_text txt o)));
        [rewrite Hbt; unfold bang_tok; cbn [starts_with sdrop append];
         rewrite Ascii.eqb_refl, Na; reflexivity
        |reflexivity|reflexivity|reflexivity|exact Hs''| | | | |].
      + destruct (starts_with hat s'') eqn:Sh.
        * right; right. destruct s'' as [|h0 s3]; [discriminate Sh|].
          cbn [starts_with] in Sh. apply Ascii.eqb_eq in Sh. subst h0.
          exists true, (flush_text txt o), (s3 ++ after).
          split; [reflexivity|]. split; [reflexivity|].
          intros Hen. cbn [append note_at] in Na. rewrite Hen in Na. exact Na.
        * left. cbn [prev_ok]. rewrite Hf2, Sh. reflexivity.
      + cbn [iscan_str tok_text bracket_open]. rewrite S0. apply settles_refl.
      + reflexivity.
      + apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate].
      + unfold pstep. apply open_bracket_sim, Hsim.
    - apply (Nrm (TText bang) 1 s' (Some bang) (txt ++ one bang) o);
        [rewrite Hbt; unfold bang_tok; destruct s' as [|d s''];
           [destruct Hae as [->|[r ->]]; reflexivity|];
         cbn [append starts_with] in Sb |- *; rewrite Sb; reflexivity
        |reflexivity|reflexivity|reflexivity|exact Hs'
        |apply prev_ok_follow; [exact Hf|reflexivity]| | | |].
      + cbn [iscan_str tok_text one]. rewrite S0.
        destruct s' as [|d s'']; cbn [get settles]; [reflexivity|].
        cbn [starts_with] in Sb. unfold istep. cbn [istep_at]. unfold ibang_step.
        rewrite Sb. reflexivity.
      + reflexivity.
      + apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate].
      + unfold pstep. apply sim_text; [exact Hsim|reflexivity]. }
  destruct (Ascii.eqb c lbrack) eqn:Elk.
  { apply Ascii.eqb_eq in Elk. subst c.
    assert (Hnp : (note_pos txt prev && wikilinks_enabled)%bool = false).
    { destruct wikilinks_enabled eqn:Hw; [|apply andb_false_r].
      rewrite (note_free' prev s' txt prev o after Hp Hw). reflexivity. }
    assert (Hlt : tok_at ps n = Some (lbrack_tok (s' ++ after)))
      by (unfold tok_at; rewrite Hs; reflexivity).
    destruct (note_at (s' ++ after)) as [lab|] eqn:Na.
    { (* a footnote reference *)
      destruct s' as [|h0 s3];
          [destruct Hae as [->|[r ->]]; cbn [append note_at] in Na; [discriminate Na|];
           change (Ascii.eqb nl_char hat) with false in Na; rewrite andb_false_r in Na;
           discriminate Na|].
      cbn [append note_at] in Na.
      destruct (notes_enabled && Ascii.eqb h0 hat)%bool eqn:E0; [|discriminate Na].
      apply andb_true_iff in E0 as [Hen E0]. apply Ascii.eqb_eq in E0. subst h0.
      apply (over_alphabet_cons hat s3 eq_refl) in Hs' as (_ & _ & Hs3).
      assert (Fl : flush_text txt o = oview v) by (rewrite Eo, Ev; apply flush_view, Ht).
      apply (scan_note ps after len IH "" s3 n v ws (IText false txt prev o) v lab false
               (flush_text txt o) (itable hat "" (Some lbrack) (bpush false (flush_text txt o)))
               Hl Hs3 Hs Fn); rewrite ?Nat.add_0_r.
      - constructor.
      - exact V.
      - exact Em.
      - rewrite Hlt. unfold lbrack_tok. cbn [append note_at]. rewrite Hen.
        change (Ascii.eqb hat hat) with true. cbn [andb]. rewrite Na. reflexivity.
      - exact Fl.
      - cbn [append iscan_str one]. unfold istep at 2. cbn [istep_at].
        rewrite (ilead_lbrack txt prev o Hnp). exact (istep_hat_note false _ Hen). }
    apply (NrmN (TOpen false) 1 s' (Some lbrack) "" (bpush false (flush_text txt o)));
      [rewrite Hlt; unfold lbrack_tok; rewrite Na; reflexivity
      |reflexivity|reflexivity|reflexivity|exact Hs'| | | | |].
    - destruct (starts_with hat s') eqn:Sh.
      + right; right. destruct s' as [|h0 s3]; [discriminate Sh|].
        cbn [starts_with] in Sh. apply Ascii.eqb_eq in Sh. subst h0.
        exists false, (flush_text txt o), (s3 ++ after).
        split; [reflexivity|]. split; [reflexivity|].
        intros Hen. cbn [append note_at] in Na. rewrite Hen in Na. exact Na.
      + left. cbn [prev_ok]. rewrite Hf, Sh. reflexivity.
    - cbn [iscan_str tok_text bracket_open one]. unfold istep. cbn [istep_at].
      rewrite (ilead_lbrack txt prev o Hnp).
      apply settles_refl.
    - reflexivity.
    - apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate].
    - unfold pstep. apply open_bracket_sim, Hsim. }
  assert (Vb : forall m h1 w c1, vinv ps m h1 w -> pv_mode w <> PMNormal ->
              vinv ps (S m) false (pbyte m c1 w)).
  { intros m h1 w c1 (Okw & Tiw & _) Ew. split; [apply pv_ok_byte; assumption|].
    split; [apply pbyte_tidy, Tiw|]. discriminate. }
  destruct (Ascii.eqb c rbrack) eqn:Erk.
  { apply Ascii.eqb_eq in Erk. subst c.
    assert (Hfl : flush_text txt o = oview v) by (rewrite Eo, Ev; apply flush_view, Ht).
    assert (Htag : tag_close (flush_text txt o) = None) by (rewrite Hfl; apply tag_close_oview).
    (* what a `]` is depends on the paragraph after it: on whether a
       region or a span's spec after it closes *)
    assert (Hrt : tok_at ps n = Some (rbrack_tok (s' ++ after)))
      by (unfold tok_at; rewrite Hs; reflexivity).
    assert (Txt : forall t, tok_text t = one rbrack -> is_hard t = false ->
              tok_at ps n = Some (t, 1) ->
              pstep ps n false t v = pv_add (Str (one rbrack)) v ->
              (forall c0, get 0 s' = Some c0 ->
                 (Ascii.eqb c0 lparen || Ascii.eqb c0 lbrack
                  || (Ascii.eqb c0 lbrace && inline_attrs_enabled))%bool = true ->
                 bclose (flush_text txt o) = None) ->
              scanned ps n false v ws (IText false txt prev o) (String rbrack s')).
    { intros t Et Hh El Ep Hb.
      apply (Nrm t 1 s' (Some rbrack) (txt ++ one rbrack) o);
        [exact El|rewrite Et; reflexivity|rewrite Et; reflexivity
        |rewrite Et; reflexivity|exact Hs'|apply prev_ok_follow; [exact Hf|reflexivity]| |exact Hh| |].
      - rewrite Et. apply tok_rbrack_text; [exact Htag|exact Hb].
      - rewrite Ep, (proj2 (pv_add_live _ _)). exact Em.
      - rewrite Ep. apply sim_text; [exact Hsim|reflexivity]. }
    destruct (pclose_go KBracket [] (pv_stk v)) as [[content rest']|] eqn:Hpc.
    2: { (* no bracket to close: whatever the `]` is, the view adds it as text *)
      assert (Hb : bclose (flush_text txt o) = None).
      { rewrite Hfl. unfold oview.
        rewrite (bclose_embed _ _ (proj1 (proj2 (proj2 Ti)))), Hpc. reflexivity. }
      destruct (rbrack_tok_shape (s' ++ after)) as [(b & rg & E)|[(b & a & E)|E]];
        rewrite E in Hrt.
      - apply (Txt (TClose b rg)); try reflexivity;
          [exact Hrt|exact (pstep_close_none ps n false b rg v Hpc)|intros; exact Hb].
      - apply (Txt (TSpan b a)); try reflexivity;
          [exact Hrt|exact (pstep_span_none ps n false b a v Hpc)|intros; exact Hb].
      - apply (Txt (TText rbrack)); try reflexivity; [exact Hrt|intros; exact Hb]. }
    destruct Ti as (_ & _ & Fnm & Fcl & _).
    destruct (pclose_go_normal KBracket (pv_stk v) [] content rest' Fnm Logic.I Hpc) as [Nc _].
    destruct (pclose_go_clean KBracket (pv_stk v) [] content rest' Fcl (Forall_nil _) Hpc)
      as [Cc _].
    set (kids := vres content).
    set (im := pclose_im (pv_stk v)).
    set (o1 := oview (PView rest' (pv_out v) PMNormal)).
    set (core1 := IText false (txt ++ one rbrack) (Some rbrack) o).
    (* the scanner closes the bracket at the byte after the `]`, and reads
       the `]` as text beside what it opens *)
    assert (Hcl : forall c2, c2 = lparen \/ c2 = lbrack ->
              istep c2 (IClosed txt o)
              = if Ascii.eqb c2 lparen
                then IDest kids im null_span false 0 "" (istep c2 core1) o1
                else IReference kids im null_span false "" (istep c2 core1) o1).
    { intros c2 H2. rewrite Eo. pose proof (closed_step v0 txt c2 content rest' Ht) as Hcs.
      rewrite <- Ev in Hcs. rewrite (Hcs Fnm Hpc H2). rewrite <- Eo. reflexivity. }
    assert (Hc2 : forall c2, iscan_str (String rbrack (one c2)) (IText false txt prev o)
                             = istep c2 (IClosed txt o)).
    { intros c2. cbn [iscan_str one]. unfold istep at 2. cbn [istep_at].
      rewrite (ilead_rbrack_closed txt prev o Htag). reflexivity. }
    (* `](` or `][` whose region closes: the closer and the byte after it *)
    assert (Two : forall c2 r rg, s' = String c2 r ->
              tok_at ps n = Some (TClose (Ascii.eqb c2 lparen) rg, 1) ->
              forall h1 v1 core2 extra,
                pruns ps (S n) false (pstep ps n false (TClose (Ascii.eqb c2 lparen) rg) v)
                  (n + 2) h1 v1 ->
                vinv ps (n + 2) h1 v1 ->
                over_alphabet (with_esc (pend_esc core2) r) = true ->
                note_ok (Some c2) core2 r (r ++ after) ->
                settles (iscan_str (String rbrack (one c2)) (IText false txt prev o))
                  (wrap extra core2) (get 0 r) ->
                Forall (never ps (n + 2)) extra ->
                linked ps (n + 2) h1 v1 (Some c2) core2 ->
                scanned ps n false v ws (IText false txt prev o) (String rbrack s')).
    { intros c2 r rg -> Ht2 h1 v1 core2 extra R2 V2 A2 N2 S2 F2 L2.
      apply (scan_advance ps after len IH (String rbrack (String c2 r)) n false v ws
               (IText false txt prev o) (String rbrack (one c2)) r (Some c2) extra core2 h1 v1);
        try assumption; cbn [String.length one]; try reflexivity; try discriminate.
      - apply (pruns_trans ps n false v (S n) false
                 (pstep ps n false (TClose (Ascii.eqb c2 lparen) rg) v)); [|exact R2].
        apply pruns_one. rewrite (punit_tok ps n false _ 1 v Em Ht2 (or_intror eq_refl)), Nat.add_1_r.
        reflexivity.
      - pose proof (before_chunk ps n (String rbrack (String c2 EmptyString)) (r ++ after) Hs)
          as Eb2.
        cbn [String.length str_last] in Eb2. rewrite Eb2. apply same_prev_refl. }
    (* `](`, `][` or `]{` whose region never closes: the `]` is text, and
       the construct the scanner opens at the byte after it is a layer
       around that text *)
    assert (Fails : forall c2 r W, s' = String c2 r ->
              tok_at ps n = Some (TText rbrack, 1) ->
              istep c2 (IClosed txt o) = wrap [W] (istep c2 core1) ->
              never ps (S (S n)) W ->
              scanned ps n false v ws (IText false txt prev o) (String rbrack s')).
    { intros c2 r W -> Ht1 Sp FW0.
      set (v1 := pstep ps n false (TText rbrack) v).
      assert (Hs1 : sdrop (S n) ps = (String c2 r ++ after)%string)
        by exact (sdrop_succ ps n rbrack _ Hs).
      pose proof (vinv_step ps n false _ 1 v V Em Ht1) as V1.
      cbn [is_hard] in V1. rewrite Nat.add_1_r in V1.
      pose proof (punit_tok ps n false _ 1 v Em Ht1 (or_intror eq_refl)) as U1.
      rewrite Nat.add_1_r in U1.
      assert (Hs0 : sdrop n ps = (one rbrack ++ String c2 r ++ after)%string) by exact Hs.
      destruct (layers_pass ps n ws (one rbrack) (String c2 r ++ after) Fn Hs0) as [_ Fn1].
      cbn [String.length one] in Fn1. rewrite Nat.add_1_r in Fn1.
      destruct (layers_pass ps (S n) _ (String c2 r) after Fn1 Hs1) as [Fo _].
      pose proof (sdrop_succ ps (S n) c2 _ Hs1) as Hs2.
      assert (FW : Forall (never ps (S (S n))) [W]) by (constructor; [exact FW0|constructor]).
      destruct (layers_pass ps (S (S n)) [W] r after FW Hs2) as [PW FW'].
      apply Forall_cons_iff in PW as [PW _]. apply Forall_cons_iff in FW' as [FW' _].
      change (String rbrack (String c2 r)) with (one rbrack ++ String c2 r)%string.
      apply (scanned_cons ps n false v ws (IText false txt prev o) (one rbrack) (String c2 r)
               false v1 after Hs Fn).
      - cbn [String.length one]. rewrite Nat.add_1_r. exact (pruns_one _ _ _ _ _ _ _ U1).
      - cbn [String.length one iscan_str]. rewrite Nat.add_1_r.
        change (istep rbrack (IText false txt prev o)) with (ilead rbrack txt prev o).
        rewrite (ilead_rbrack_closed txt prev o Htag).
        apply (scanned_lift ps (S n) false v1 _ core1 (IClosed txt o) c2 r W Fo).
        + exact Sp.
        + exact PW.
        + replace (S n + String.length (String c2 r)) with (S (S n) + String.length r)
            by (cbn [String.length]; lia).
          exact FW'.
        + apply (IH (String c2 r) (Some rbrack) (S n) false v1 _ core1).
          * cbn [String.length] in Hl |- *. lia.
          * apply alpha_of. cbn [pend_esc with_esc]. exact Hs'.
          * left. apply prev_ok_plain; reflexivity.
          * exact Hs1.
          * rewrite (before_sdrop ps n rbrack _ Hs). apply same_prev_refl.
          * exact V1.
          * exact Fn1.
          * apply linked_normal.
            -- unfold v1, pstep. rewrite (proj2 (pv_add_live _ _)). exact Em.
            -- unfold v1, pstep. apply sim_text; [exact Hsim|reflexivity]. }
    destruct (starts_with lparen s') eqn:S1.
    { (* a `(` after it *)
      destruct s' as [|c2 r]; [discriminate|]. cbn [starts_with] in S1.
      apply Ascii.eqb_eq in S1. subst c2.
      pose proof (over_alphabet_cons lparen r eq_refl Hs') as (_ & _ & Hr').
      assert (Hs1 : sdrop (S n) ps = String lparen (r ++ after))
        by exact (sdrop_succ ps n rbrack _ Hs).
      assert (Hs2 : sdrop (S (S n)) ps = (r ++ after)%string)
        by exact (sdrop_succ ps (S n) lparen _ Hs1).
      destruct (dest_close false 0 0 (r ++ after)) as [e0|] eqn:R.
      - (* a destination that closes: its region *)
        set (rg := substring 0 e0 (r ++ after)).
        assert (Ht1 : tok_at ps n = Some (TClose true rg, 1))
          by (rewrite Hrt; unfold rbrack_tok; cbn [append]; rewrite R; reflexivity).
        pose proof (dest_close_bound _ _ _ _ _ R) as Hbd.
        assert (Lrg : String.length rg = e0) by (apply substring_length0; lia).
        set (e := n + S (S (String.length rg))).
        pose proof (vinv_step ps n false (TClose true rg) 1 v V Em Ht1) as V1.
        cbn [is_hard] in V1. rewrite Nat.add_1_r in V1.
        pose proof (Two lparen r rg eq_refl ltac:(rewrite Ht1; reflexivity)) as T2.
        rewrite Ascii.eqb_refl in T2.
        rewrite (pstep_close_found ps n false true rg v content rest' Hpc) in V1, T2.
        fold im kids e in V1, T2.
        replace (n + 2) with (S (S n)) in T2 by lia.
        set (v1 := PView rest' (pv_out v) (PMRegion true im kids n e "")) in *.
        assert (U2 : punit ps (S n) false v1 = Some (S (S n), false, pbyte (S n) lparen v1)).
        { unfold punit. cbn [v1 pv_mode]. rewrite (get_sdrop ps (S n) lparen _ Hs1). reflexivity. }
        apply (T2 false (pbyte (S n) lparen v1)
                 (IDest kids im null_span false 0 "" (istep lparen core1) o1) []).
        + exact (pruns_one _ _ _ _ _ _ _ U2).
        + apply (Vb (S n) false v1 lparen V1). discriminate.
        + exact Hr'.
        + right; left. intros t p o' E. discriminate E.
        + cbn [wrap]. rewrite Hc2, (Hcl lparen (or_introl eq_refl)), Ascii.eqb_refl.
          apply settles_refl.
        + constructor.
        + unfold linked, pbyte. cbn [v1 pv_mode pv_setmode pv_stk pv_out].
          replace (S n =? e)%nat with false by (symmetry; apply Nat.eqb_neq; unfold e; lia).
          rewrite Nat.eqb_refl. cbn [pv_mode].
          split; [lia|]. split; [reflexivity|].
          exists null_span, (istep lparen core1), (DS false 0 "").
          split; [reflexivity|]. split; [|reflexivity].
          cbn [ds_esc ds_depth]. rewrite Hs2.
          replace (S (S n)) with (0 + S (S n)) by lia.
          rewrite dest_close_shift, R. cbn [option_map]. f_equal. unfold e. lia.
      - (* a destination that never closes *)
        assert (Ht1 : tok_at ps n = Some (TText rbrack, 1))
          by (rewrite Hrt; unfold rbrack_tok; cbn [append]; rewrite R; reflexivity).
        apply (Fails lparen r (WDest kids im null_span (DS false 0 "") o1) eq_refl Ht1).
        + rewrite (Hcl lparen (or_introl eq_refl)). reflexivity.
        + unfold never. cbn [ds_esc ds_depth]. rewrite Hs2.
          replace (S (S n)) with (0 + S (S n)) by lia.
          rewrite dest_close_shift, R. reflexivity. }
    destruct (starts_with lbrack s') eqn:S2.
    { (* a `[` after it *)
      destruct s' as [|c2 r]; [discriminate|]. cbn [starts_with] in S1, S2.
      apply Ascii.eqb_eq in S2. subst c2.
      pose proof (over_alphabet_cons lbrack r eq_refl Hs') as (_ & _ & Hr').
      assert (Hs1 : sdrop (S n) ps = String lbrack (r ++ after))
        by exact (sdrop_succ ps n rbrack _ Hs).
      assert (Hs2 : sdrop (S (S n)) ps = (r ++ after)%string)
        by exact (sdrop_succ ps (S n) lbrack _ Hs1).
      destruct (label_close false 0 (r ++ after)) as [e0|] eqn:R.
      - (* a reference label that closes: its region *)
        set (rg := substring 0 e0 (r ++ after)).
        assert (Ht1 : tok_at ps n = Some (TClose false rg, 1))
          by (rewrite Hrt; unfold rbrack_tok; cbn [append]; rewrite R; reflexivity).
        pose proof (label_close_bound _ _ _ _ R) as Hbd.
        assert (Lrg : String.length rg = e0) by (apply substring_length0; lia).
        set (e := n + S (S (String.length rg))).
        pose proof (vinv_step ps n false (TClose false rg) 1 v V Em Ht1) as V1.
        cbn [is_hard] in V1. rewrite Nat.add_1_r in V1.
        pose proof (Two lbrack r rg eq_refl ltac:(rewrite Ht1; reflexivity)) as T2.
        change (Ascii.eqb lbrack lparen) with false in T2.
        rewrite (pstep_close_found ps n false false rg v content rest' Hpc) in V1, T2.
        fold im kids e in V1, T2.
        replace (n + 2) with (S (S n)) in T2 by lia.
        set (v1 := PView rest' (pv_out v) (PMRegion false im kids n e "")) in *.
        assert (U2 : punit ps (S n) false v1 = Some (S (S n), false, pbyte (S n) lbrack v1)).
        { unfold punit. cbn [v1 pv_mode]. rewrite (get_sdrop ps (S n) lbrack _ Hs1). reflexivity. }
        apply (T2 false (pbyte (S n) lbrack v1)
                 (IReference kids im null_span false "" (istep lbrack core1) o1) []).
        + exact (pruns_one _ _ _ _ _ _ _ U2).
        + apply (Vb (S n) false v1 lbrack V1). discriminate.
        + exact Hr'.
        + right; left. intros t p o' E. discriminate E.
        + cbn [wrap]. rewrite Hc2, (Hcl lbrack (or_intror eq_refl)). apply settles_refl.
        + constructor.
        + unfold linked, pbyte. cbn [v1 pv_mode pv_setmode pv_stk pv_out].
          replace (S n =? e)%nat with false by (symmetry; apply Nat.eqb_neq; unfold e; lia).
          rewrite Nat.eqb_refl. cbn [pv_mode].
          split; [lia|]. split; [apply kids_ok_vres, Cc|]. split; [reflexivity|].
          exists false, "", null_span, (istep lbrack core1).
          split; [|split; reflexivity].
          rewrite Hs2. replace (S (S n)) with (0 + S (S n)) by lia.
          rewrite label_close_shift, R. cbn [option_map]. f_equal. unfold e. lia.
      - (* a reference label that never closes *)
        assert (Ht1 : tok_at ps n = Some (TText rbrack, 1))
          by (rewrite Hrt; unfold rbrack_tok; cbn [append]; rewrite R; reflexivity).
        apply (Fails lbrack r (WRef kids im null_span (NS false "") o1) eq_refl Ht1).
        + rewrite (Hcl lbrack (or_intror eq_refl)). reflexivity.
        + unfold never. cbn [ns_esc]. rewrite Hs2. exact (label_close_note_go _ false 0 R). }
    destruct (starts_with lbrace s') eqn:S3.
    { (* a `{` after it: a span, or a spec that never closes *)
      destruct s' as [|c2 r]; [discriminate|]. cbn [starts_with] in S1, S2, S3.
      apply Ascii.eqb_eq in S3. subst c2.
      assert (Hs1 : sdrop (S n) ps = String lbrace (r ++ after))
        by exact (sdrop_succ ps n rbrack _ Hs).
      assert (Hrt' : tok_at ps n = Some (match spec_at (r ++ after) with
                                         | Some (b, a) => TSpan b a
                                         | None => TText rbrack
                                         end, 1))
        by (rewrite Hrt; reflexivity).
      clear Hrt. rename Hrt' into Hrt.
      destruct (spec_at (r ++ after)) as [[b a]|] eqn:Hat.
      2: { (* a spec that never closes: the `]` is text *)
        destruct inline_attrs_enabled eqn:Hen.
        2: { apply (Txt (TText rbrack)); try reflexivity; [exact Hrt|].
             intros c0 E0 Hor. injection E0 as <-. discriminate Hor. }
        apply (Fails lbrace r (WSpan kids im null_span ap_init "" o1) eq_refl Hrt).
        + rewrite Eo. pose proof (closed_step_span v0 txt content rest' Ht) as Hcs.
          rewrite <- Ev in Hcs. rewrite (Hcs Fnm Hpc Hen). rewrite <- Eo. reflexivity.
        + unfold never. rewrite (sdrop_succ ps (S n) lbrace _ Hs1).
          unfold spec_at in Hat. rewrite Hen in Hat. exact Hat. }
      (* a span: the closer, the `{`, and its spec, which the view walks *)
      assert (Hen : inline_attrs_enabled = true)
        by (unfold spec_at in Hat; destruct inline_attrs_enabled; [reflexivity|discriminate Hat]).
      assert (Hgo : spec_go ap_init (r ++ after) = Some (b, a))
        by (unfold spec_at in Hat; rewrite Hen in Hat; exact Hat).
      assert (Ht1 : tok_at ps n = Some (TSpan b a, 1)) by exact Hrt.
      pose proof (vinv_step ps n false (TSpan b a) 1 v V Em Ht1) as V1.
      cbn [is_hard] in V1. rewrite Nat.add_1_r in V1.
      pose proof (pstep_span_found ps n false b a v content rest' Hpc) as Ep.
      rewrite Ep in V1. fold kids im in Ep, V1.
      set (v1 := PView rest' (pv_out v) (PMSpan im kids a (n + S (S (String.length b))))) in *.
      assert (U2 : punit ps (S n) false v1 = Some (S (S n), false, pbyte (S n) lbrace v1)).
      { unfold punit. cbn [v1 pv_mode]. rewrite (get_sdrop ps (S n) lbrace _ Hs1). reflexivity. }
      assert (Eb1 : pbyte (S n) lbrace v1 = v1).
      { unfold pbyte. cbn [v1 pv_mode].
        replace (S n =? n + S (S (String.length b)))%nat with false
          by (symmetry; apply Nat.eqb_neq; lia). reflexivity. }
      assert (Hsp : iscan_str (String rbrack (one lbrace)) (IText false txt prev o)
                    = ISpan kids im null_span ap_init ""
                        (IBrace (txt ++ one rbrack) (Some rbrack) o) o1).
      { rewrite Hc2, Eo. pose proof (closed_step_span v0 txt content rest' Ht) as Hcs.
        rewrite <- Ev in Hcs. rewrite (Hcs Fnm Hpc Hen). rewrite <- Eo. reflexivity. }
      apply (scan_advance ps after len IH (String rbrack (String lbrace r)) n false v ws
               (IText false txt prev o) (String rbrack (one lbrace)) r (Some lbrace) []
               (ISpan kids im null_span ap_init ""
                  (IBrace (txt ++ one rbrack) (Some rbrack) o) o1) false v1);
        try assumption; cbn [String.length one]; try reflexivity; try discriminate.
      - apply (pruns_trans ps n false v (S n) false v1).
        + apply pruns_one.
          rewrite (punit_tok ps n false _ 1 v Em Ht1 (or_intror eq_refl)), Nat.add_1_r, Ep.
          reflexivity.
        + replace (n + 2) with (S (S n)) by lia. rewrite <- Eb1 at 2.
          exact (pruns_one _ _ _ _ _ _ _ U2).
      - replace (n + 2) with (S (S n)) by lia. rewrite <- Eb1.
        apply (Vb (S n) false v1 lbrace V1). discriminate.
      - pose proof (before_chunk ps n (String rbrack (String lbrace EmptyString)) (r ++ after) Hs)
          as Eb2.
        cbn [String.length str_last] in Eb2. rewrite Eb2. apply same_prev_refl.
      - cbn [pend_esc with_esc]. exact (proj2 (proj2 (over_alphabet_cons lbrace r eq_refl Hs'))).
      - right; left. intros t p o' E. discriminate E.
      - cbn [wrap]. rewrite Hsp. apply settles_refl.
      - constructor.
      - unfold linked. cbn [v1 pv_mode]. split; [reflexivity|]. split; [apply vres_ok|].
        exists ap_init, "", null_span, b,
          (IBrace (txt ++ one rbrack) (Some rbrack) o).
        split; [reflexivity|].
        split; [|split; [lia|reflexivity]].
        replace (n + 2) with (S (S n)) by lia. rewrite (sdrop_succ ps (S n) lbrace _ Hs1).
        exact Hgo. }
    (* a `]` before anything else *)
    assert (HrtT : tok_at ps n = Some (TText rbrack, 1)).
    { rewrite Hrt. destruct s' as [|c1 r].
      - destruct Hae as [->|[r ->]]; reflexivity.
      - cbn [starts_with] in S1, S2, S3. cbn [append]. unfold rbrack_tok. cbv zeta.
        rewrite S1, S2, S3. reflexivity. }
    apply (Txt (TText rbrack)); try reflexivity; [exact HrtT|].
    intros c0 E0 Hor. exfalso. destruct s' as [|c1 r]; [discriminate|].
    injection E0 as ->. cbn [starts_with] in S1, S2, S3. rewrite S1, S2, S3 in Hor.
    discriminate Hor. }
  assert (CL : forall c0 m, str_last (chars c0 m) (Some c0) = Some c0).
  { intros c0 m. induction m as [|m IHm]; [reflexivity|]. exact IHm. }
  assert (SL : forall k p, str_last (dtoken k) p = Some (dchar k)).
  { intros k p. destruct (dtoken_cons k) as (w & _ & ->). apply CL. }
  destruct (Ascii.eqb c lbrace) eqn:Elb.
  { apply Ascii.eqb_eq in Elb. subst c.
    destruct (starts_row s') eqn:Hrow.
    2: { (* an attribute spec, or a `{` that begins none *)
      assert (Hlt : tok_at ps n = Some (lbrace_tok (s' ++ after)))
        by (unfold tok_at; rewrite Hs; reflexivity).
      assert (Hnr : match (s' ++ after)%string with
                    | String d _ => dstyle_of d | EmptyString => None end = None).
      { destruct s' as [|d r].
        - destruct Hae as [->|[r ->]]; [reflexivity|exact dstyle_of_nl].
        - cbn [starts_row] in Hrow. unfold is_delim in Hrow. cbn [append].
          destruct (dstyle_of d); [discriminate Hrow|reflexivity]. }
      pose proof (sdrop_succ ps n lbrace _ Hs) as Hs1.
      change ((fix append (s1 s2 : string) {struct s1} : string :=
                 match s1 with "" => s2 | String c s1' => String c (append s1' s2) end) s' after)
        with (s' ++ after)%string in Hs1.
      assert (Hfl : flush_text txt o = oview v) by (rewrite Eo, Ev; apply flush_view, Ht).
      set (X := IText false (txt ++ one lbrace) (Some lbrace) o).
      (* the scanner holds the `{` for a byte, and then holds a spec that
         has read nothing yet beside the `{` read as text *)
      assert (SY : settles (iscan_str (one lbrace) (IText false txt prev o))
                     (wrap (if inline_attrs_enabled then [WAttr ap_init "" txt prev o] else []) X)
                     (get 0 s')).
      { cbn [iscan_str one]. change (istep lbrace (IText false txt prev o)) with (IBrace txt prev o).
        destruct s' as [|d r]; cbn [get settles].
        - cbn [rres]. destruct inline_attrs_enabled; reflexivity.
        - cbn [starts_row] in Hrow. unfold is_delim in Hrow.
          destruct (dstyle_of d) eqn:Hd; [discriminate Hrow|].
          unfold istep. cbn [istep_at]. unfold ibrace_step_at. rewrite Hd.
          destruct inline_attrs_enabled; [|reflexivity].
          change (wrap [WAttr ap_init "" txt prev o] X) with (IAttr ap_init "" txt prev X o).
          cbn [istep_at]. unfold iattr_feed. destruct (ap_failed (astep ap_init d)); reflexivity. }
      destruct (spec_at (s' ++ after)) as [[b a]|] eqn:Hat.
      - (* a spec that closes, here or on a later line: the view walks it *)
        assert (Hen : inline_attrs_enabled = true)
          by (unfold spec_at in Hat; destruct inline_attrs_enabled; [reflexivity|discriminate Hat]).
        assert (Hgo : spec_go ap_init (s' ++ after) = Some (b, a))
          by (unfold spec_at in Hat; rewrite Hen in Hat; exact Hat).
        assert (Ht1 : tok_at ps n = Some (TAttr b a, S (S (String.length b)))).
        { rewrite Hlt. unfold lbrace_tok. rewrite Hnr, Hat. reflexivity. }
        set (e := pred (tok_end ps n)).
        assert (He : e = S n + String.length b) by (unfold e, tok_end; rewrite Ht1; lia).
        set (w1 := pv_setmode (PMAtom (VMark a) e) v).
        assert (Pst : pstep ps n false (TAttr b a) v = w1) by reflexivity.
        assert (U1 : punit ps n false v = Some (S n, false, w1))
          by (unfold punit; rewrite Em, Ht1; cbv zeta; rewrite Pst; reflexivity).
        assert (V1 : vinv ps (S n) false w1) by exact (vinv_atom ps n v _ _ _ e V Em Ht1 Pst).
        rewrite Hen in SY.
        change (wrap [WAttr ap_init "" txt prev o] X) with (IAttr ap_init "" txt prev X o) in SY.
        apply (scan_advance_gen ps after len IH (String lbrace s') n false v ws
                 (IText false txt prev o) (one lbrace) s' (Some lbrace) []
                 (IAttr ap_init "" txt prev X o) false w1 Hl Hs Fn);
          cbn [String.length one]; rewrite ?Nat.add_1_r.
        + reflexivity.
        + discriminate.
        + exact (pruns_one _ _ _ _ _ _ _ U1).
        + exact V1.
        + rewrite (before_sdrop ps n lbrace _ Hs). apply same_prev_refl.
        + unfold alpha_ok. cbn [w1 pv_mode pv_setmode]. exists false. exact Hs'.
        + right; left. intros t q o' E. discriminate E.
        + cbn [wrap]. exact SY.
        + constructor.
        + unfold linked. cbn [w1 pv_mode pv_setmode]. split; [reflexivity|]. split; [lia|].
          right; right. exists ap_init, "", txt, prev, X, o, b, a.
          split; [reflexivity|]. split; [exact Hfl|]. split; [reflexivity|].
          split; [rewrite Hs1; exact Hgo|]. split; [exact He|reflexivity].
      - (* a `{` that begins no spec is text, and the spec the scanner
           reads beside it is a layer, gone at the byte that fails it *)
        assert (Ht1 : tok_at ps n = Some (TText lbrace, 1)).
        { rewrite Hlt. unfold lbrace_tok. rewrite Hnr, Hat. reflexivity. }
        apply (scan_advance_gen ps after len IH (String lbrace s') n false v ws
                 (IText false txt prev o) (one lbrace) s' (Some lbrace)
                 (if inline_attrs_enabled then [WAttr ap_init "" txt prev o] else []) X
                 false (pstep ps n false (TText lbrace) v) Hl Hs Fn);
          cbn [String.length one]; rewrite ?Nat.add_1_r.
        + reflexivity.
        + discriminate.
        + pose proof (punit_tok ps n false _ 1 v Em Ht1 (or_intror eq_refl)) as U.
          rewrite Nat.add_1_r in U. exact (pruns_one _ _ _ _ _ _ _ U).
        + pose proof (vinv_step ps n false _ 1 v V Em Ht1) as V1.
          rewrite Nat.add_1_r in V1. exact V1.
        + rewrite (before_sdrop ps n lbrace _ Hs). apply same_prev_refl.
        + apply alpha_of. cbn [pend_esc with_esc]. exact Hs'.
        + right; left. intros t q o' E. injection E as <- _ _. destruct txt; reflexivity.
        + exact SY.
        + destruct inline_attrs_enabled eqn:Hen; [|constructor].
          constructor; [|constructor]. unfold never. rewrite Hs1.
          unfold spec_at in Hat. rewrite Hen in Hat. exact Hat.
        + apply linked_normal.
          * apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate].
          * unfold pstep. apply sim_text; [exact Hsim|reflexivity]. }
    assert (HtokR : tok_at ps n = next_tok prev (String lbrace s'))
      by exact (tok_at_line ps n _ after prev Hs Hae ltac:(discriminate) Etk Edl eq_refl eq_refl
                  (or_intror Hrow) eq_refl Hnl Hpv).
    (* `{`, which a row's character follows *)
    destruct s' as [|d s'']; [discriminate|].
    cbn [starts_row] in Hrow. unfold is_delim in Hrow.
    destruct (dstyle_of d) as [k|] eqn:Hd; [|discriminate].
    pose proof Hs' as Hd'.
    apply (over_alphabet_cons _ _ (delim_not_bslash d k Hd)) in Hd' as (Hdc & _ & _).
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
      + rewrite HtokR; rewrite Es. exact (nt_marked_open k prev rest Hd).
      + rewrite Es. reflexivity.
      + cbn [tok_text String.length]. unfold dtoken. rewrite length_append, length_chars.
        reflexivity.
      + cbn [tok_text one append str_last]. rewrite SL. reflexivity.
      + exact Hs2.
      + (* what may follow the token's last byte, from the alphabet *)
        apply prev_ok_follow; [|exact Hlkk].
        pose proof Hs' as Hs3. rewrite Es in Hs3.
        destruct (dwidth k) as [|w] eqn:Ew; [destruct (dwidth_nonzero k Ew)|].
        unfold dtoken in Hs3. rewrite Ew, chars_last, append_assoc in Hs3.
        apply (over_alphabet_app_r _ _ (no_bslash_chars _ w (dchar_nb k))) in Hs3.
        exact (proj1 (proj2 (over_alphabet_cons _ _ (dchar_nb k) Hs3))).
      + apply tok_marked_open, Hen.
      + reflexivity.
      + apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate].
      + assert (Ecm : at_rbrace (get (tok_end ps n) ps) = at_rbrace (get 0 rest)).
        { unfold tok_end. rewrite HtokR; rewrite Es, (nt_marked_open k prev rest Hd).
          rewrite get_add, Hs, Es. cbn [sdrop append].
          assert (G2 : forall w x, get w (chars (dchar k) w ++ x) = get 0 x)
            by (induction w as [|w IHw]; intros x; [reflexivity|exact (IHw x)]).
          cbn [get]. unfold dtoken. rewrite append_assoc, G2.
          destruct rest as [|c0 r0]; [|reflexivity].
          destruct Hae as [->|[r' ->]]; reflexivity. }
        unfold pstep. cbv zeta. rewrite Ecm. cbn [andb].
        exact (open_marked_sim n k _ _ txt v o Hsim).
    - (* `{` and a run too short to be a token: text *)
      assert (Hhy : Ascii.eqb (dchar k) hyphen = false).
      { (* a row spelled with the hyphen is one hyphen wide *)
        destruct (Ascii.eqb (dchar k) hyphen) eqn:E; [|reflexivity]. exfalso.
        apply Ascii.eqb_eq in E. rewrite E in Hdc, Hd.
        pose proof (alphabet_hyphen_row Hdc) as Hrow'. unfold hyphen_row_ok in Hrow'.
        rewrite Hd in Hrow'. apply Nat.eqb_eq in Hrow'. lia. }
      assert (Ht1 : tok_at ps n = Some (TText lbrace, 1)).
      { rewrite HtokR. exact (nt_lbrace_short k j' prev rest0 Hd Hw Hr). }
      pose proof (vinv_step ps n false _ 1 v V Em Ht1) as V1.
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
                  o rest0 after Hd Hw Hhy Hr Hnl0 Hae Hs1 V1)
        as (v' & R & V' & Em' & S').
      { apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate]. }
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
      + left. apply prev_ok_plain; first [assumption|exact (dchar_tick k)|exact (dchar_lt k)|exact (dchar_bang k)
        |exact (dchar_colon k)].
      + apply tok_marked_partial; [exact Hen|lia|exact Hnext].
      + constructor.
      + cbn [String.length]. rewrite length_chars, <- Nat.add_succ_comm.
        apply linked_normal; [exact Em'|exact S']. }
  assert (SA : forall a b p, str_last (a ++ b) p = str_last b (str_last a p)).
  { induction a as [|x a IHa]; intros b p; [reflexivity|]. apply IHa. }
  destruct (Ascii.eqb c lt) eqn:Elt.
  { (* an autolink candidate *)
    apply Ascii.eqb_eq in Elt. subst c.
    exact (scan_auto ps after len IH Hae s' prev n v ws txt o Hl Ha Hs Hpv V Fn Em Hsim). }
  destruct (Ascii.eqb c ":"%char) eqn:Eco.
  { (* a symbol, or a `:` *)
    apply Ascii.eqb_eq in Eco. subst c.
    exact (scan_symbol ps after len IH Hae s' prev n v ws txt o Hl Ha Hs Hpv V Fn Em Hsim). }
  (* A chunk the table reads from its first byte.  A `^` that marks a
     footnote whose label never closes is read so too, inside the label's
     layer, which every byte after it passes. *)
  assert (Lead : forall bytes rest prev1 txt' o' v1,
            s' = (bytes ++ rest)%string ->
            pruns ps n false v (n + S (String.length bytes)) false v1 ->
            vinv ps (n + S (String.length bytes)) false v1 ->
            same_prev (before ps (n + S (String.length bytes))) prev1 ->
            over_alphabet rest = true -> prev_ok prev1 rest = true ->
            settles (iscan_str bytes (itable c txt prev o)) (IText false txt' prev1 o')
              (get 0 rest) ->
            pv_mode v1 = PMNormal -> sim v1 txt' o' ->
            scanned ps n false v ws (IText false txt prev o) (String c s')).
  { intros bytes rest prev1 txt' o' v1 Es R V1 Hp1 Ha1 Hf1 Hset Em1 Hs1.
    destruct Hnote as [Hn|(-> & Hen & -> & -> & im & o1 & -> & Hnv)].
    - apply (scan_advance ps after len IH (String c s') n false v ws (IText false txt prev o)
               (String c bytes) rest prev1 [] (IText false txt' prev1 o') false v1 Hl Hs Fn);
        [rewrite Es; reflexivity|discriminate|exact R|exact V1|exact Hp1| |left; exact Hf1| | |].
      + cbn [pend_esc with_esc]. exact Ha1.
      + cbn [iscan_str wrap]. change (istep c (IText false txt prev o)) with (ilead c txt prev o).
        rewrite (ilead_itable c txt prev o Hn Eb Etk Edl Epd Ehy Elb Ebg Elt Eco Elk Erk).
        exact Hset.
      + constructor.
      + apply linked_normal; [exact Em1|exact Hs1].
    - (* the `^` of a footnote whose label never closes *)
      set (W0 := WNote im null_span (NS false "") o1).
      pose proof (sdrop_succ ps n hat _ Hs) as Hs1'.
      assert (Hs2 : sdrop (S n) ps = (bytes ++ rest ++ after)%string)
        by (rewrite Hs1', Es, append_assoc; reflexivity).
      assert (F0 : Forall (never ps (S n)) [W0]).
      { constructor; [|constructor]. unfold never, W0. cbn [ns_esc]. rewrite Hs1'. exact Hnv. }
      destruct (layers_pass ps (S n) [W0] bytes (rest ++ after) F0 Hs2) as [P1 F1].
      replace (S n + String.length bytes) with (n + S (String.length bytes)) in F1 by lia.
      apply (scan_advance_gen ps after len IH (String hat s') n false v ws
               (IText false "" (Some lbrack) (bpush im o1)) (String hat bytes) rest prev1
               (map (wl_after bytes) [W0]) (IText false txt' prev1 o') false v1 Hl Hs Fn);
        [rewrite Es; reflexivity|discriminate|exact R|exact V1|exact Hp1| |left; exact Hf1| |exact F1|].
      + apply alpha_of. cbn [pend_esc with_esc]. exact Ha1.
      + cbn [iscan_str]. rewrite (istep_hat_note im o1 Hen), (iscan_wrap bytes [W0] _ P1).
        apply settles_wrap; [|exact Hset]. intros c' Ec'.
        destruct rest as [|c'' r'']; [discriminate Ec'|]. cbn [get] in Ec'. injection Ec' as <-.
        pose proof (sdrop_app_tail ps (S n) bytes _ Hs2) as Hr2.
        replace (S n + String.length bytes) with (n + S (String.length bytes)) in Hr2 by lia.
        destruct (layers_pass ps _ _ (one c'') (r'' ++ after) F1 Hr2) as [P2 _].
        rewrite Forall_forall in P2 |- *. intros w Hw E. apply (P2 w Hw).
        cbn [wfeed one]. rewrite E. reflexivity.
      + apply linked_normal; [exact Em1|exact Hs1]. }
  (* the same, for a chunk that is one token of the chain *)
  assert (LeadT : forall t l rest prev1 txt' o' bytes,
            tok_at ps n = Some (t, l) -> tok_text t = String c bytes ->
            s' = (bytes ++ rest)%string -> l = String.length (tok_text t) ->
            same_prev (str_last (tok_text t) (before ps n)) prev1 ->
            over_alphabet rest = true -> prev_ok prev1 rest = true ->
            settles (iscan_str bytes (itable c txt prev o)) (IText false txt' prev1 o')
              (get 0 rest) ->
            is_hard t = false -> pv_mode (pstep ps n false t v) = PMNormal ->
            sim (pstep ps n false t v) txt' o' ->
            scanned ps n false v ws (IText false txt prev o) (String c s')).
  { intros t l rest prev1 txt' o' bytes Ht0 Et Es El Hp1 Ha1 Hf1 Hset Hh Em1 Hs1.
    assert (Ln : n + l = n + S (String.length bytes)) by (rewrite El, Et; reflexivity).
    apply (Lead bytes rest prev1 txt' o' (pstep ps n false t v) Es); rewrite <- ?Ln.
    - pose proof (punit_tok ps n false t l v Em Ht0 (or_introl Em1)) as U. rewrite Hh in U.
      exact (pruns_one _ _ _ _ _ _ _ U).
    - pose proof (vinv_step ps n false t l v V Em Ht0) as V1. rewrite Hh in V1. exact V1.
    - rewrite El, (before_chunk ps n (tok_text t) (rest ++ after)); [exact Hp1|].
      rewrite Hs, Et, Es. cbn [append]. rewrite append_assoc. reflexivity.
    - exact Ha1.
    - exact Hf1.
    - exact Hset.
    - exact Em1.
    - exact Hs1. }
  destruct (dstyle_of c) as [k|] eqn:Hd.
  2: { (* a plain byte *)
    apply (LeadT (TText c) 1 s' (Some c) (txt ++ one c) o "");
      [rewrite Htok by first [reflexivity|assumption]; apply nt_byte;
         [exact (alphabet_nl c Hc)|exact Eb|exact Etk|exact Edl|exact Elt|exact Eco|exact Epd|exact Ehy
         |exact Ebg|exact Elk
         |exact Erk|exact Elb|exact Hd]
      |reflexivity|reflexivity|reflexivity|reflexivity|exact Hs'
      |apply prev_ok_follow; [exact Hf|exact Elk]| |reflexivity| |].
    - cbn [iscan_str].
      rewrite (table_text c txt prev o Hc Elb Elk Erk Etk Edl Elt Eco Ebg Epd Hd). apply settles_refl.
    - apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate].
    - unfold pstep. apply sim_text; [exact Hsim|reflexivity]. }
  pose proof Ehy as Hhy.
  pose proof (dstyle_of_enabled c k Hd) as Hen.
  pose proof (dstyle_of_char c k Hd) as Ec. subst c.
  destruct (dchar_plain k) as (Hlbk & Hrbk & Hlkk & Hrkk).
  destruct (run_split (dchar k) s') as (j' & rest0 & -> & Hr).
  assert (Hnext : forall c0, get 0 rest0 = Some c0 -> c0 <> dchar k).
  { intros c0 E0. destruct rest0 as [|d0 r]; [discriminate|]. injection E0 as <-.
    exact (Hr d0 r eq_refl). }
  destruct (Nat.le_gt_cases (dwidth k) (S j')) as [Hw|Hw].
  - (* a whole token *)
    set (rest := (chars (dchar k) (S j' - dwidth k) ++ rest0)%string).
    assert (Es : String (dchar k) (chars (dchar k) j' ++ rest0) = (dtoken k ++ rest)%string).
    { unfold rest, dtoken. rewrite <- append_assoc, <- chars_add.
      replace (dwidth k + (S j' - dwidth k)) with (S j') by lia. reflexivity. }
    clearbody rest.
    assert (Es2 : (chars (dchar k) j' ++ rest0)%string = (dtail k ++ rest)%string).
    { rewrite dtoken_tail in Es. cbn [append] in Es. injection Es as Es. exact Es. }
    rewrite Es in Ha. apply (over_alphabet_app_r _ _ (no_bslash_dtoken k)) in Ha.
    destruct (at_rbrace (get 0 rest)) eqn:Hat.
    + (* a marked closer *)
      destruct rest as [|e0 r]; [discriminate|]. cbn [get at_rbrace] in Hat.
      apply Ascii.eqb_eq in Hat. subst e0.
      destruct (resolve_sim ps n false k true txt prev (Some rbrace) v o Ok Em (proj1 (proj2 (proj2 Ti))) Hsim)
        as (txt' & o' & Hres & Hsim').
      apply (LeadT (TDelim k true false true) (S (dwidth k)) r (Some rbrace) txt' o'
               (dtail k ++ one rbrace)).
      * (rewrite Htok by first [reflexivity|assumption]); rewrite Es. exact (nt_marked_close k prev r Hd Hhy).
      * cbn [tok_text]. rewrite dtoken_tail. reflexivity.
      * rewrite Es2, append_assoc. reflexivity.
      * cbn [tok_text]. rewrite length_append. unfold dtoken. rewrite length_chars.
        cbn. lia.
      * cbn [tok_text]. rewrite SA. reflexivity.
      * exact (proj2 (proj2 (over_alphabet_cons rbrace r eq_refl Ha))).
      * reflexivity.
      * rewrite (tok_marked_close k txt prev o Hen), Hres. apply settles_refl.
      * reflexivity.
      * apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate].
      * exact Hsim'.
    + (* a bare token *)
      destruct (resolve_sim ps n false k false txt prev (get 0 rest) v o Ok Em (proj1 (proj2 (proj2 Ti))) Hsim)
        as (txt' & o' & Hres & Hsim').
      apply (LeadT (TDelim k false (dbare k prev && nonspace_at (get 0 rest)) (nonspace_at prev))
               (dwidth k) rest (Some (dchar k)) txt' o' (dtail k)).
      * (rewrite Htok by first [reflexivity|assumption]); rewrite Es. exact (nt_token k prev rest Hd Hat Hhy).
      * cbn [tok_text]. apply dtoken_tail.
      * exact Es2.
      * cbn [tok_text]. unfold dtoken. rewrite length_chars. reflexivity.
      * cbn [tok_text]. rewrite SL. reflexivity.
      * exact Ha.
      * apply prev_ok_plain; first [assumption|exact (dchar_tick k)|exact (dchar_lt k)|exact (dchar_bang k)
        |exact (dchar_colon k)].
      * apply (tok_bare k txt prev o (get 0 rest) txt' o' Hen); [|exact Hres].
        intros c0 E0. rewrite E0 in Hat. exact Hat.
      * reflexivity.
      * apply pstep_mode; [exact Em|discriminate|discriminate|discriminate|discriminate|discriminate].
      * exact Hsim'.
  - (* a run too short to be a token *)
    assert (Hnl0 : no_char nl_char rest0 = true).
    { change (String (dchar k) (chars (dchar k) j' ++ rest0))
        with (chars (dchar k) (S j') ++ rest0)%string in Hnl.
      rewrite no_char_app in Hnl. apply andb_true_iff in Hnl as [_ Hnl]. exact Hnl. }
    destruct (run_texts ps k (S j') n v txt o rest0 after Hd Hw Hhy Hr Hnl0 Hae
                ltac:(rewrite Hs; cbn [chars append]; rewrite append_assoc; reflexivity) V Em Hsim)
      as (v' & R & V' & Em' & S').
    apply (Lead (chars (dchar k) j') rest0 (Some (dchar k)) (txt ++ chars (dchar k) (S j')) o v');
      rewrite ?length_chars.
    + reflexivity.
    + exact R.
    + exact V'.
    + rewrite <- (length_chars (dchar k) (S j')).
      rewrite (before_chunk ps n _ (rest0 ++ after)).
      2: { rewrite Hs. cbn [chars append]. rewrite append_assoc. reflexivity. }
      cbn [chars str_last]. rewrite CL. reflexivity.
    + exact (over_alphabet_chars (dchar k) (S j') rest0 (dchar_nb k) Ha).
    + apply prev_ok_plain; first [assumption|exact (dchar_tick k)|exact (dchar_lt k)|exact (dchar_bang k)
        |exact (dchar_colon k)].
    + apply (tok_partial k (S j')); [exact Hen|lia|exact Hnext].
    + exact Em'.
    + exact S'.
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
      destruct out as [|y out]; [|destruct y as [[]| |]; try discriminate Ht];
        cbn [xsnoc xtrim];
        destruct (strip_trailing_ws txt) eqn:Es; reflexivity.
    + destruct txt; [|discriminate]. cbn. unfold pv_trim; cbn.
      destruct out as [|y out]; [reflexivity|destruct y as [[]| |]; try discriminate Ht; reflexivity].
  - destruct (nonempty_str txt) eqn:En.
    + cbn [pv_add pv_stk pv_out pv_trim pv_mode].
      destruct f as [p k c]; cbn [fset fcontent] in *;
      (destruct c as [|y c]; [|destruct y as [[]| |]; try discriminate Ht]);
        cbn [xsnoc xtrim fset fcontent];
        destruct (strip_trailing_ws txt) eqn:Es; reflexivity.
    + destruct txt; [|discriminate]. cbn. unfold pv_trim; cbn.
      destruct f as [p k c]; cbn [fset fcontent] in *;
        (destruct c as [|y c]; [reflexivity|destruct y as [[]| |]; try discriminate Ht; reflexivity]).
Qed.

Local Lemma ibreak_pending : forall ws0 txt p o,
  ibreak (esc_pending ws0 txt p o) = IText false "" None (oword_reset (iesc_hard ws0 txt o)).
Proof. intros [|w ws] txt p o; reflexivity. Qed.

Local Lemma ifinish_pending : forall ws0 txt p o,
  ifinish (esc_pending ws0 txt p o) = ifinish (IText false "" None (iesc_hard ws0 txt o)).
Proof. intros [|w ws] txt p o; reflexivity. Qed.

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
    apply andb_true_iff in H as [Hn H].
    cbn [over_alphabet]. change (is_bslash bslash) with true. cbn iota. rewrite Hn.
    apply (IH (String.length a)); [cbn in Em; lia|reflexivity|exact H|exact Hb].
  - cbn [append] in H. apply (over_alphabet_cons c _ Eb) in H as (Hc & Hf & H).
    cbn [over_alphabet]. rewrite Eb, Hc.
    rewrite (IH (String.length a) ltac:(cbn in Em; lia) a eq_refl H Hb), andb_true_r. cbn [andb].
    destruct a as [|d a].
    + (* at the end of the line every byte may stand *)
      unfold follow_ok. cbn [starts_with]. rewrite !andb_false_r. reflexivity.
    + exact Hf.
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
       destruct VP as (x & v0 & -> & Em0 & -> & Hx & [(dd & m & body & -> & ->)|(Hs0 & _)]);
         [|rewrite Hs in Hs0; discriminate].
       set (v := pv_add (verb_node dd None body) v0) in *.
       assert (Em : pv_mode v = PMNormal)
         by (unfold v; rewrite (proj2 (pv_add_live _ _)); exact Em0).
       exists false, (pv_add SoftBreak v).
       split; [rewrite (punit_tok ps n false TBreak 1 v Em Ht (or_intror eq_refl)), Nat.add_1_r; reflexivity|].
       split; [pose proof (vinv_step ps n false TBreak 1 v V Em Ht) as V1;
               rewrite Nat.add_1_r in V1; exact V1|].
       assert (E : ibreak (IVerb m m body (vkind_of dd) (oview v0))
                   = IText false "" None (oview (pv_add SoftBreak v))).
       { unfold ibreak. cbn [ibreak_at iresolve ibreak_flat]. rewrite Nat.eqb_refl.
         change (imk_here SoftBreak) with (mk SoftBreak).
         change (tval body) with body. rewrite vnode_of.
         change (imk (text_start (oview v0)) cursor_start (verb_node dd None body))
           with (mk (verb_node dd None body)).
         rewrite (oemit_view _ v0) by exact Hx. fold v.
         rewrite (oemit_view SoftBreak v) by discriminate. reflexivity. }
       left. rewrite E. split; [|reflexivity].
       apply linked_normal; [rewrite (proj2 (pv_add_live _ _)); exact Em|].
       exists (pv_add SoftBreak v).
       split; [reflexivity|]. split; [apply top_add_nonstr; discriminate|reflexivity]. }
  2: { (* the hard break the line ended with *)
       destruct P as (ws0 & txt & p & o & vb & -> & Hb & -> & Emb & Hsim & ->).
       destruct Hsim as (v0 & -> & Ht0 & ->).
       set (v := pv_add HardBreak (pv_trim (add_text txt v0))) in *.
       assert (Em : pv_mode v = PMNormal)
         by (unfold v; rewrite (proj2 (pv_add_live _ _)), (proj2 (pv_trim_live _)); exact Emb).
       exists false, v.
       split; [rewrite (punit_tok ps n true TBreak 1 v Em Ht (or_intror eq_refl)), Nat.add_1_r; reflexivity|].
       split; [pose proof (vinv_step ps n true TBreak 1 v V Em Ht) as V1;
               rewrite Nat.add_1_r in V1; exact V1|].
       assert (E : ibreak (esc_pending ws0 txt p (oview v0))
                   = IText false "" None (oview v)).
       { unfold v. rewrite (pv_trim_add_text txt v0 Ht0).
         assert (X : iesc_hard ws0 txt (oview v0)
                     = oview (pv_add HardBreak (add_text (strip_trailing_ws txt) v0))).
         { unfold iesc_hard. tred.
           change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s
                     (strip_trailing_ws txt) (oview v0))
             with (flush_text (strip_trailing_ws txt) (oview v0)).
           rewrite (flush_view _ v0 Ht0). rewrite imk_here_semantic.
           apply oemit_view. discriminate. }
         rewrite ibreak_pending, X. reflexivity. }
       left. rewrite E. split; [|reflexivity]. apply linked_normal; [exact Em|].
       exists v. split; [reflexivity|]. split; [apply top_add_nonstr; discriminate|reflexivity]. }
  unfold linked in L. destruct (pv_mode v) as [|[|] im kids d e txt|x e|im sk sat se] eqn:Em.
  - (* text mode: a soft break *)
    destruct L as (-> & txt & o & -> & Hsim). destruct Hsim as (v0 & -> & Ht0 & Ev).
    exists false, (pv_add SoftBreak v).
    split; [rewrite (punit_tok ps n false TBreak 1 v Em Ht (or_intror eq_refl)), Nat.add_1_r; reflexivity|].
    split; [pose proof (vinv_step ps n false TBreak 1 v V Em Ht) as V1;
            rewrite Nat.add_1_r in V1; exact V1|].
    assert (E : ibreak (IText false txt prev (oview v0))
                = IText false "" None (oview (pv_add SoftBreak v))).
    { unfold ibreak, ibreak_at, ibreak_flat. cbn [iresolve].
      change (@flush_text_at semantic_pos semantic_inline_cursor (tval txt) (oview v0))
        with (flush_text txt (oview v0)).
      rewrite (flush_view txt v0 Ht0), <- Ev.
      change (imk_here SoftBreak) with (mk SoftBreak).
      rewrite (oemit_view SoftBreak v) by discriminate. reflexivity. }
    left. rewrite E. split; [|reflexivity].
    apply linked_normal; [rewrite (proj2 (pv_add_live _ _)); exact Em|].
    exists (pv_add SoftBreak v).
    split; [reflexivity|]. split; [apply top_add_nonstr; discriminate|reflexivity].
  - (* a destination: the newline is one of its bytes *)
    destruct L as (Hd & -> & open & sh & [e0 dp dst] & Hds & He & ->).
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
    replace (Nat.eqb n e) with false.
    2: { symmetry in He. apply dest_close_bound in He. symmetry. apply Nat.eqb_neq. lia. }
    replace (n =? S d)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    cbn [pv_mode pv_setmode]. split; [lia|]. split; [reflexivity|].
    exists open, (ibreak sh), ds'. split; [|split].
    + rewrite dfeed_app, Hds. cbn [one dfeed]. rewrite Hst. reflexivity.
    + rewrite Hs1. exact He.
    + unfold ibreak at 1, ibreak_at at 1. tred. unfold ds'. cbn [ds_esc ds_depth ds_dst].
      destruct e0; reflexivity.
  - (* a reference label: likewise *)
    destruct L as (Hd & Hk & -> & esc & label' & open & sh & He & Hl & ->).
    exists false, (pbyte n nl_char v).
    split; [unfold punit; rewrite Em, Hg; reflexivity|].
    split; [split; [apply pv_ok_byte; [exact Ok|rewrite Em; discriminate]|];
            split; [apply pbyte_tidy, Ti|discriminate]|].
    rewrite Hs in He.
    pose proof (sdrop_succ ps n nl_char r Hs) as Hs1.
    assert (He' : Some e = label_close false (S n) (sdrop (S n) ps))
      by (rewrite Hs1, He; destruct esc; reflexivity).
    left. split; [|reflexivity].
    unfold linked, pbyte. rewrite Em.
    replace (Nat.eqb n e) with false.
    2: { symmetry in He'. apply label_close_bound in He'. symmetry. apply Nat.eqb_neq. lia. }
    replace (n =? S d)%nat with false by (symmetry; apply Nat.eqb_neq; lia).
    cbn [pv_mode pv_setmode]. split; [lia|]. split; [exact Hk|]. split; [reflexivity|].
    exists false, (label' ++ (if esc then one bslash else "") ++ nl)%string, open, (ibreak sh).
    split; [exact He'|]. split.
    + subst txt. rewrite append_empty_r, append_assoc. reflexivity.
    + unfold ibreak at 1, ibreak_at at 1. tred. reflexivity.
  - destruct L as (-> & Hne & [(p & pre & m & body & cl & rw & txt0 & prev0 & o0 & Hp & Htv & -> & Hsim
                                & -> & Hvs)|[N|Na]]).
    3: { (* inside a spec: the newline is one of its bytes *)
      destruct Na as (p & src & txt & pv & sh & o & b & a & -> & Hfl & Hp & Hgo & He & ->).
      rewrite Hs in Hgo. cbn [spec_go] in Hgo.
      destruct (ap_failed (astep p nl_char)) eqn:Ef; [discriminate Hgo|].
      destruct (ap_done (astep p nl_char)) eqn:Ed.
      { pose proof (astep_done p nl_char Hp Ed) as E. discriminate E. }
      destruct (spec_go (astep p nl_char) r) as [[b1 a1]|] eqn:E1; [|discriminate Hgo].
      injection Hgo as <- <-. cbn [String.length] in He.
      exists false, (pbyte n nl_char v).
      split; [unfold punit; rewrite Em, Hg; reflexivity|].
      split; [split; [apply pv_ok_byte; [exact Ok|rewrite Em; discriminate]|];
              split; [apply pbyte_tidy, Ti|discriminate]|].
      assert (Pb : pbyte n nl_char v = v).
      { unfold pbyte. rewrite Em. replace (n =? e)%nat with false; [reflexivity|].
        symmetry. apply Nat.eqb_neq. lia. }
      pose proof (sdrop_succ ps n nl_char r Hs) as Hs1.
      assert (Eb : ibreak (IAttr p src txt pv sh o)
                   = IAttr (astep p nl_char) (src ++ nl) txt pv (ibreak sh) o).
      { unfold ibreak at 1. cbn [ibreak_at]. unfold iattr_feed. rewrite Ef, Ed. reflexivity. }
      left. rewrite Pb, Eb. split; [|reflexivity].
      unfold linked. rewrite Em. split; [reflexivity|]. split; [lia|]. right; right.
      exists (astep p nl_char), (src ++ nl)%string, txt, pv, (ibreak sh), o, b1, a1.
      split; [reflexivity|]. split; [exact Hfl|]. split; [exact Ed|].
      split; [rewrite Hs1; exact E1|]. split; [lia|reflexivity]. }
    2: { (* inside a footnote label: the newline is one of its bytes *)
      destruct N as (esc & im & lab & sh & o & rr & -> & Hob & Hgo & -> & ->).
      rewrite Hs in Hgo. cbn [note_go] in Hgo.
      assert (Hgo' : exists r', note_go false r = Some r' /\ rr = String nl_char r').
      { destruct esc; [|change (is_bslash nl_char) with false in Hgo;
                        change (Ascii.eqb nl_char rbrack) with false in Hgo; cbn iota in Hgo];
          (destruct (note_go false r) as [r'|]; [injection Hgo as <-; exists r'; auto
                                                 |discriminate Hgo]). }
      destruct Hgo' as (r' & Hr' & ->).
      exists false, (pbyte n nl_char v).
      split; [unfold punit; rewrite Em, Hg; reflexivity|].
      split; [split; [apply pv_ok_byte; [exact Ok|rewrite Em; discriminate]|];
              split; [apply pbyte_tidy, Ti|discriminate]|].
      assert (Pb : pbyte n nl_char v = v).
      { unfold pbyte. rewrite Em. cbn [String.length].
        replace (n =? n + S (String.length r'))%nat with false
          by (symmetry; apply Nat.eqb_neq; lia). reflexivity. }
      pose proof (sdrop_succ ps n nl_char r Hs) as Hs1.
      left. rewrite Pb. split; [|reflexivity].
      unfold linked. rewrite Em. split; [reflexivity|]. split; [cbn [String.length]; lia|]. right; left.
      exists false, im, (lab ++ ((if esc then one bslash else "") ++ nl))%string,
        (ibreak_at inline_attrs_enabled sh), o, r'.
      split; [unfold ibreak; cbn [ibreak_at]; tred; reflexivity|].
      split; [exact Hob|]. split; [rewrite Hs1; exact Hr'|].
      split; [cbn [String.length]; lia|].
      destruct esc; cbn [with_esc]; rewrite !append_assoc; reflexivity. }
    (* inside a verbatim: the newline is one of its bytes *)
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
      unfold linked. rewrite Em. split; [reflexivity|]. split; [lia|]. left.
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
      pose proof (verb_last_tick _ _ _ _ _ _ Ec Hm) as E. discriminate E. }
    destruct (T3 eq_refl) as (_ & Elen & Efin).
    destruct Hsim as (v0 & Eo & Ht0 & Ev).
    set (vN := pv_setmode PMNormal v) in *.
    assert (Fl : flush_text (txt0 ++ chars dollar (pre - 2)) o0 = oview vN) by (rewrite Eo, Ev; apply flush_view, Ht0).
    assert (Pb : pbyte n nl_char v = pv_add (verb_node pre None body) vN)
      by (unfold pbyte; rewrite Em, Nat.eqb_refl; reflexivity).
    assert (EmN : pv_mode vN = PMNormal) by (unfold vN; destruct v; reflexivity).
    pose proof (sdrop_succ ps n nl_char r Hs) as Hs1.
    assert (Hr : r = EmptyString).
    { assert (L1 : String.length (sdrop n ps) = 1) by (rewrite sdrop_length; lia).
      rewrite Hs in L1. destruct r; [reflexivity|cbn in L1; lia]. }
    subst r. right. split; [exact Hr|]. rewrite Pb.
    exists (verb_node pre None body), vN.
    split; [reflexivity|]. split; [exact EmN|]. split; [reflexivity|].
    split; [intros s0; apply verb_node_nonstr|]. right. split; [exact Hr|].
    rewrite Efin, Fl, (oemit_view _ vN) by (intros s0; apply verb_node_nonstr). reflexivity.
  - (* inside a span's spec: likewise *)
    destruct L as (-> & Bk & p & src & open & b & sh & Hp & Hgo & He & ->).
    rewrite Hs in Hgo. cbn [spec_go] in Hgo.
    destruct (ap_failed (astep p nl_char)) eqn:Ef; [discriminate Hgo|].
    destruct (ap_done (astep p nl_char)) eqn:Ed.
    { pose proof (astep_done p nl_char Hp Ed) as E. discriminate E. }
    destruct (spec_go (astep p nl_char) r) as [[b1 a1]|] eqn:E1; [|discriminate Hgo].
    injection Hgo as <- <-. cbn [String.length] in He.
    exists false, (pbyte n nl_char v).
    split; [unfold punit; rewrite Em, Hg; reflexivity|].
    split; [split; [apply pv_ok_byte; [exact Ok|rewrite Em; discriminate]|];
            split; [apply pbyte_tidy, Ti|discriminate]|].
    assert (Pb : pbyte n nl_char v = v).
    { unfold pbyte. rewrite Em. replace (n =? se)%nat with false; [reflexivity|].
      symmetry. apply Nat.eqb_neq. lia. }
    pose proof (sdrop_succ ps n nl_char r Hs) as Hs1.
    assert (Eb : ibreak (ISpan sk im open p src sh (oview v))
                 = ISpan sk im open (astep p nl_char) (src ++ nl) (ibreak sh) (oview v)).
    { unfold ibreak at 1. cbn [ibreak_at]. unfold ispan_feed. rewrite Ef, Ed. reflexivity. }
    left. rewrite Pb, Eb. split; [|reflexivity].
    unfold linked. rewrite Em. split; [reflexivity|]. split; [exact Bk|].
    exists (astep p nl_char), (src ++ nl)%string, open, b1, (ibreak sh).
    split; [exact Ed|]. split; [rewrite Hs1; exact E1|]. split; [lia|reflexivity].
Qed.

Local Lemma ifinish_verb : forall d m body v0,
  ifinish (IVerb m m body (vkind_of d) (oview v0))
  = ifinish (IText false "" None (oview (pv_add (verb_node d None body) v0))).
Proof.
  intros d m body v0. unfold ifinish, ifinish_rev.
  cbn [ifinish_ostate iresolve ifinish_ostate_flat]. rewrite Nat.eqb_refl.
  change (tval body) with body. rewrite vnode_of.
  change (imk (text_start (oview v0)) cursor_start (verb_node d None body))
    with (mk (verb_node d None body)).
  rewrite (oemit_view _ v0) by (intros s0; apply verb_node_nonstr). reflexivity.
Qed.

Local Lemma tidy_flat : forall v, tidy v -> normal (pflatten v).
Proof.
  intros v (No & _ & Nf & _). unfold pflatten.
  apply pflatten_go_normal; [exact Nf|exact Logic.I|exact No].
Qed.

Local Lemma sim_finish_tidy : forall v txt prev o,
  sim v txt o -> tidy v -> ifinish (IText false txt prev o) = vres (pflatten v).
Proof.
  intros v txt prev o Hsim Ti. pose proof (tidy_flat v Ti) as Nf.
  unfold pflatten in Nf |- *. exact (sim_finish v txt prev o Hsim Nf).
Qed.

(* The paragraph's end, in a linked state or one a hard break or a
   verbatim left. *)
Local Lemma linked_finish : forall ps n h v ws prev core,
  vinv ps n h v -> linked_end ps n h v prev core -> sdrop n ps = EmptyString ->
  ifinish (wrap ws core) = vres (pflatten v).
Proof.
  intros ps n h v ws prev core (Ok & Ti & _) [L|[P|VP]] Hs;
    rewrite ifinish_wrap.
  - unfold linked in L.
    destruct (pv_mode v) as [|[|] im kids d e txt|x e|im sk sat se] eqn:Em.
    + destruct L as (_ & txt & o & -> & Hsim).
      exact (sim_finish_tidy v txt prev o Hsim Ti).
    + (* a destination closes before the end *)
      destruct L as (_ & _ & open & sh & ds & _ & He & _).
      rewrite Hs in He. destruct (ds_esc ds); discriminate He.
    + (* and so does a label *)
      destruct L as (_ & _ & _ & esc & label' & open & sh & He & _ & _).
      rewrite Hs in He. destruct esc; discriminate He.
    + (* a verbatim covers a byte past the end, and a label or a spec ends
         before it *)
      destruct L as (_ & Hne & [(p & pre & m & body & cl & rw & _ & _ & _ & _ & Htv & _)|[N|Na]]).
      * pose proof (tok_at_len ps p _ _ Htv) as [_ Hle].
        pose proof (sdrop_length n ps) as L0. rewrite Hs in L0. cbn in L0. lia.
      * destruct N as (esc & im & lab & sh & o & r & _ & _ & Hgo & _).
        rewrite Hs in Hgo. discriminate Hgo.
      * destruct Na as (p & src & txt & pv & sh & o & b & a & _ & _ & _ & Hgo & _).
        rewrite Hs in Hgo. discriminate Hgo.
    + (* a span's spec ends before the end *)
      destruct L as (_ & _ & p & src & open & b & sh & _ & Hgo & _).
      rewrite Hs in Hgo. discriminate Hgo.
  - destruct P as (ws0 & txt & p & o & vb & _ & _ & -> & Emb & Hsim & ->).
    rewrite ifinish_pending. destruct Hsim as (v0 & -> & Ht & ->).
    set (v := pv_add HardBreak (pv_trim (add_text txt v0))) in *.
    assert (X : iesc_hard ws0 txt (oview v0) = oview v).
    { unfold v. rewrite (pv_trim_add_text txt v0 Ht). unfold iesc_hard. tred.
      change (@flush_text_to_at semantic_pos semantic_inline_cursor ?s
                (strip_trailing_ws txt) (oview v0))
        with (flush_text (strip_trailing_ws txt) (oview v0)).
      rewrite (flush_view _ v0 Ht). rewrite imk_here_semantic.
      apply oemit_view. discriminate. }
    rewrite X. apply (sim_finish_tidy v "" None (oview v)).
    + exists v. split; [reflexivity|]. split; [apply top_add_nonstr; discriminate|reflexivity].
    + exact Ti.
  - destruct VP as (x & v0 & _ & Em0 & -> & Hx & Hc).
    assert (F : ifinish core = ifinish (IText false "" None (oview (pv_add x v0))))
      by (destruct Hc as [(dd & m & body & -> & ->)|(_ & F)]; [apply ifinish_verb|exact F]).
    rewrite F. apply (sim_finish_tidy (pv_add x v0) "" None (oview (pv_add x v0))).
    + exists (pv_add x v0). split; [reflexivity|].
      split; [apply top_add_nonstr; exact Hx|reflexivity].
    + exact Ti.
Qed.

(* The newline before a line is to the flanking rules what the scanner
   holds at a line's start. *)
Local Lemma same_prev_nl : same_prev (Some nl_char) None.
Proof.
  split; [reflexivity|]. intros k. unfold dbare. destruct (dsyntax_of k); reflexivity.
Qed.

Local Lemma scan_lines_sim : forall ps ls n h v ws core,
  Forall (fun x => over_alphabet x = true) ls ->
  sdrop n ps = para_string ls -> same_prev (before ps n) None ->
  vinv ps n h v -> Forall (never ps n) ws -> linked ps n h v None core -> pend_esc core = false ->
  exists h' v', pruns ps n h v (n + String.length (para_string ls)) h' v'
    /\ ifinish (iscan_lines ls (wrap ws core)) = vres (pflatten v').
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
        as (ws0 & core' & prev' & h' & v' & E & R & V' & Fn' & L');
        [apply alpha_of; rewrite Pe; exact (over_alphabet_strip x Hx)|left; reflexivity
        |rewrite append_empty_r; exact Hs|exact Hb|exact V|exact Fn|exact L|].
      set (ws' := (map (wl_after s) ws ++ ws0)%list) in *.
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
        as (ws0 & core' & prev' & h' & v' & E & R & V' & Fn' & L');
        [apply alpha_of; rewrite Pe; exact Hx|left; reflexivity|exact Hs|exact Hb
        |exact V|exact Fn|exact L|].
      set (ws' := (map (wl_after x) ws ++ ws0)%list) in *.
      set (m := n + String.length x) in *.
      pose proof (sdrop_app_tail ps n x _ Hs) as Hsm. fold m in Hsm.
      destruct (break_linked ps m h' v' prev' core' _ Hsm V' L') as (h2 & v2 & U & V2 & LB).
      destruct (layers_pass ps m ws' (one nl_char) (para_string (y :: rest')) Fn' Hsm)
        as [Fnl Fn2].
      cbn [String.length one] in Fn2. rewrite Nat.add_1_r in Fn2.
      rewrite <- ibreak_rres, E.
      rewrite ibreak_wrap.
      2: { rewrite Forall_forall in Fnl |- *. intros w Hw E0. apply (Fnl w Hw).
           cbn [wfeed one]. rewrite E0. reflexivity. }
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
                    ltac:(rewrite (before_sdrop ps m nl_char _ Hsm); exact same_prev_nl)
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
    split; [constructor|]. split; [intros p k c []|exact Logic.I].
  - split; [exact Logic.I|]. split; [constructor|]. split; [constructor|].
    split; [constructor|exact Logic.I].
Qed.

Local Lemma linked_start : forall ps, linked ps 0 false pv0 None istart.
Proof.
  intros ps. split; [reflexivity|]. exists "", ostart. split; [reflexivity|].
  exists pv0. split; [reflexivity|]. split; reflexivity.
Qed.

(* A paragraph: its lines, each over the alphabet, read as one string with
   a newline between two of them and the last without its trailing
   whitespace. *)
Theorem para_inlines_matching : forall ls,
  Forall (fun x => over_alphabet x = true) ls ->
  para_inlines ls = tree_of (para_string ls) (fst (ref_read (para_string ls))).
Proof.
  intros ls Ha. unfold para_inlines.
  destruct (scan_lines_sim (para_string ls) ls 0 false pv0 [] istart Ha eq_refl (same_prev_refl None)
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
  generalize ([] : list titem) as top. generalize (S (String.length s)) as f.
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

(* With no option claiming a byte the alphabet leaves out, every
   paragraph: a line holds no newline. *)
Corollary para_inlines_valid_lines : alphabet_total = true -> forall ls m os,
  Forall (fun x => no_char nl_char x = true) ls -> valid (para_string ls) (m, os) ->
  para_inlines ls = tree_of (para_string ls) m.
Proof.
  intros Ht ls m os Hn Hv. apply (para_inlines_valid ls m os); [|exact Hv].
  apply (Forall_impl _ (alphabet_total_line Ht) Hn).
Qed.

End WithTable.
