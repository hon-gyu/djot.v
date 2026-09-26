(* ai-disclosure: autonomous *)

(* The located scan, and erasure: the located and semantic scans agree
   once coordinates are dropped. *)

From Stdlib Require Import String Ascii List Bool Lia Wf_nat Arith.
From DjotV Require Import Config Strings Ast Attributes InlineTable InlineView InlineScan.
Import ListNotations.

Local Open Scope string_scope.

Section WithTable.
Context {T : dtable}.

Ltac sem_flush :=
  try change (@flush_text_at semantic_pos semantic_inline_cursor)
    with flush_text;
  repeat match goal with
  | |- context [@flush_text_to_at semantic_pos semantic_inline_cursor
                  ?stop ?txt ?o] =>
      change (@flush_text_to_at semantic_pos semantic_inline_cursor
                stop txt o)
        with (flush_text txt o)
  end;
  (* the same for a close, whose node the semantic policy builds without
     reading the span it is handed *)
  repeat match goal with
  | |- context [@oclose T semantic_pos ?k ?m ?stop ?o] =>
      change (@oclose T semantic_pos k m stop o) with (sclose k m o)
  end.

(*
The located scan
----------------

The same transition, driven so that each byte arrives with its own
`spot`s installed.  Nothing here decides anything: at `semantic_pos`
every use of the cursor is behind `pos_records`, so this is `iscan_lines`
with an argument the scanner ignores.

Coordinates are counted, never measured: `rem` starts at one length per
line and a predecessor carries it down.  That count is the distance to the end of the *source*
line because a stored line is a suffix of its line with nothing trimmed
from the end (`.project/260916.plan.source-locations.md`, F2).
*)

(* The origin is a spot rather than a column because a text run can
   begin on an earlier line than the byte being scanned: a spec that
   spans a break is not flushed at the break, so the run it precedes is
   still open when the next line starts (`text_start`'s fallback). *)
Local Definition cursor_in (k rem : nat) (origin : spot) : InlineCursor :=
  CursorAt (Spot k rem) (Spot k (pred rem)) origin.

Local Fixpoint iscan_str_located `{PosPolicy} (allow : bool) (k : nat)
  (origin : spot) (rem : nat) (s : string) (st : iscan) : iscan :=
  match s with
  | EmptyString => st
  | String c rest =>
      iscan_str_located allow k origin (pred rem) rest
        (@istep_at T _ (cursor_in k rem origin) allow c st)
  end.

(* Where a line's stored text begins, and where a paragraph's content
   ends: its last line stripped, since `iscan_lines` scans it stripped. *)
Local Definition lines_start (l : list (nat * string)) : spot :=
  match l with
  | [] => Spot 0 0
  | (k, x) :: _ => Spot k (String.length x)
  end.

Local Fixpoint lines_stop (l : list (nat * string)) : spot :=
  match l with
  | [] => Spot 0 0
  | [(k, x)] => Spot k (String.length x - String.length (strip_trailing_ws x))
  | _ :: rest => lines_stop rest
  end.

(* Attributes are off for the leading lines a failed block spec handed
   back, as in `iscan_lines_off`, and off for the break that ends one. *)
Local Definition allow_attrs (off : nat) : bool :=
  match off with O => inline_attrs_enabled | S _ => false end.

(* A break runs from the end of its line to the start of the next one,
   so the text after it starts where that line's content does: the stop
   of the `SoftBreak` is what `text_start` reads.  Container prefixes are
   why this is not the byte after the terminator. *)
Local Fixpoint iscan_lines_located `{PosPolicy} (off : nat) (origin : spot)
  (l : list (nat * string)) (st : iscan) : iscan :=
  match l with
  | [] => st
  | [(k, x)] =>
      iscan_str_located (allow_attrs off) k origin
        (String.length x) (strip_trailing_ws x) st
  | (k, x) :: rest =>
      iscan_lines_located (pred off) origin rest
        (@ibreak_at T _
           (CursorAt (Spot k 0) (lines_start rest) (Spot k (String.length x)))
           (allow_attrs off)
           (iscan_str_located (allow_attrs off) k origin
              (String.length x) x st))
  end.

(* The paragraph ends where its last line's content does, and a text run
   with nothing before it starts at the first line's first byte. *)
Local Definition ifinish_located `{PosPolicy} (l : list (nat * string))
  (st : iscan) : inlines :=
  @ifinish T _ (CursorAt (lines_stop l) (lines_stop l) (lines_start l)) st.

End WithTable.
Module ScanErase.

Section WithTable.
Context {T : dtable}.
Ltac sem_flush :=
  try change (@flush_text_at semantic_pos semantic_inline_cursor)
    with flush_text;
  repeat match goal with
  | |- context [@flush_text_to_at semantic_pos semantic_inline_cursor
                  ?stop ?txt ?o] =>
      change (@flush_text_to_at semantic_pos semantic_inline_cursor
                stop txt o)
        with (flush_text txt o)
  end;
  (* the same for a close, whose node the semantic policy builds without
     reading the span it is handed *)
  repeat match goal with
  | |- context [@oclose T semantic_pos ?k ?m ?stop ?o] =>
      change (@oclose T semantic_pos k m stop o) with (sclose k m o)
  end.

(*
Erasure of a scan
-----------------

What the located scan and the semantic one have to agree on: the tree,
once the coordinates are dropped.  One function serves both sides,
because `iscan` is the same type at every policy -- and because a policy
that records nothing stores no coordinates at all (`imk`, `pspan`,
`remember_word_start` each ask it first), a semantic state is its own
erasure, so the refinement is one equation rather than an equation and
an invariant over the state.
*)

Local Definition of_oitem (i : oitem) : oitem :=
  match i with
  | OIn n => OIn (Erase.inode n)
  | OMark a _ _ => OMark a null_span None
  end.

Local Fixpoint of_oitems (l : oitems) : oitems :=
  match l with
  | [] => []
  | i :: rest => of_oitem i :: of_oitems rest
  end.

Local Lemma oitems_map : forall l, of_oitems l = map of_oitem l.
Proof. induction l as [|i l IH]; cbn [of_oitems map]; congruence. Qed.

Local Definition of_frame (f : frame) : frame :=
  Frame (fr_kind f) (fr_marked f) null_span (of_oitems (fr_out f)).

Local Definition of_ostate (o : ostate) : ostate :=
  OState (of_oitems (os_out o)) (map of_frame (os_stk o)) None.

Fixpoint of_iscan (st : iscan) : iscan :=
  match st with
  | IText esc txt prev o => IText esc txt prev (of_ostate o)
  | IEscWs ws txt prev o => IEscWs ws txt prev (of_ostate o)
  | IBrace txt prev o => IBrace txt prev (of_ostate o)
  | IDelim k extra txt before marked o =>
      IDelim k extra txt before marked (of_ostate o)
  | IOpen n vk o => IOpen n vk (of_ostate o)
  | IVerb n run txt vk o => IVerb n run txt vk (of_ostate o)
  | IDollar two txt prev o => IDollar two txt prev (of_ostate o)
  | IPeriod two txt prev o => IPeriod two txt prev (of_ostate o)
  | IDash n txt prev o => IDash n txt prev (of_ostate o)
  | IBang txt prev o => IBang txt prev (of_ostate o)
  | IClosed txt o => IClosed txt (of_ostate o)
  | ISpan kids image _ p src o =>
      ISpan (Erase.of_inlines kids) image null_span p src (of_ostate o)
  | IAttr p src txt prev sh o =>
      IAttr p src txt prev (of_iscan sh) (of_ostate o)
  | IReference kids image _ label o =>
      IReference (Erase.of_inlines kids) image null_span label (of_ostate o)
  | INote esc image label _ o =>
      INote esc image label null_span (of_ostate o)
  | IWiki esc rb image region _ o =>
      IWiki esc rb image region null_span (of_ostate o)
  | IDest kids image _ esc depth dst sh o =>
      IDest (Erase.of_inlines kids) image null_span esc depth dst
        (of_iscan sh) (of_ostate o)
  | IAuto src txt o => IAuto src txt (of_ostate o)
  | ISymbol alias txt sh o =>
      ISymbol alias txt (of_iscan sh) (of_ostate o)
  | IRaw spec txt o => IRaw spec txt (of_ostate o)
  end.

(* A node the policy built: its payload survives, its provenance does
   not, and the roles a spec attached to it are provenance. *)
Local Lemma of_imk : forall `{P : PosPolicy} start stop x,
  Erase.inode (@imk P start stop x) = mk (Erase.of_inline x).
Proof.
  intros P start stop x. unfold imk, posnode, mk, Erase.inode.
  destruct pos_records; reflexivity.
Qed.

Local Lemma of_add_inline_role : forall `{P : PosPolicy} role r n,
  Erase.inode (@add_inline_role P role r n) = Erase.inode n.
Proof.
  intros P role r [p a x]. unfold add_inline_role, add_roles.
  destruct pos_records; [destruct p|]; reflexivity.
Qed.

Local Lemma of_osnoc : forall n l,
  of_oitems (osnoc n l) = osnoc (of_oitem n) (of_oitems l).
Proof.
  intros [n|a sp w] [|[m|b sq w'] l]; try reflexivity;
    destruct m as [q [|lv b'] u]; try reflexivity;
    destruct u; try reflexivity;
    destruct n as [p [|kv a'] v]; try reflexivity;
    destruct v; reflexivity.
Qed.

Local Lemma of_oapp : forall cur out,
  of_oitems (oapp cur out) = oapp (of_oitems cur) (of_oitems out).
Proof.
  induction cur as [|n cur IH]; intros out; [reflexivity|].
  destruct cur as [|n' cur']; cbn [oapp].
  - apply of_osnoc.
  - change (of_oitems (n :: n' :: cur')%list)
      with (of_oitem n :: of_oitems (n' :: cur')%list)%list.
    cbn [oapp]. rewrite <- IH. reflexivity.
Qed.

Local Lemma of_oemit : forall n o,
  of_ostate (oemit n o) = oemit (Erase.inode n) (of_ostate o).
Proof. intros n [out [|f stk] word]; [reflexivity|destruct f; reflexivity]. Qed.

Local Lemma oemit_node : forall p a x o,
  oemit (Node NoPos a (Erase.of_inline x)) (of_ostate o) =
  of_ostate (oemit (Node p a x) o).
Proof. intros p a x o. rewrite of_oemit. reflexivity. Qed.

Local Lemma of_imk_here : forall `{P : PosPolicy} `{C : InlineCursor} x,
  Erase.inode (@imk_here P C x) =
  @imk_here semantic_pos semantic_inline_cursor (Erase.of_inline x).
Proof. intros P C x. unfold imk_here. rewrite of_imk. reflexivity. Qed.

Local Lemma of_oemit_merge : forall n o,
  of_ostate (oemit_merge n o) =
  oemit_merge (Erase.inode n) (of_ostate o).
Proof.
  intros n [out [|f stk] word]; [|destruct f as [fk fm fo fout]];
    unfold oemit_merge, of_ostate, of_frame;
    cbn [os_stk os_out os_word_start fr_kind fr_marked fr_out map];
    rewrite (of_osnoc (OIn n)); reflexivity.
Qed.

Local Lemma of_omark : forall a spec o,
  of_ostate (omark a spec o) = omark a null_span (of_ostate o).
Proof. intros a spec [out [|f stk] word]; [reflexivity|destruct f; reflexivity]. Qed.

Local Lemma of_oemit_all : forall ns o,
  of_ostate (oemit_all ns o) = oemit_all (Erase.of_inlines ns) (of_ostate o).
Proof.
  induction ns as [|n ns IH]; intros o; [reflexivity|].
  cbn [oemit_all]. rewrite IH, of_oemit. reflexivity.
Qed.

Local Lemma of_oemit_all_merge : forall ns o,
  of_ostate (oemit_all_merge ns o) =
  oemit_all_merge (Erase.of_inlines ns) (of_ostate o).
Proof.
  induction ns as [|n ns IH]; intros o; [reflexivity|].
  cbn [oemit_all_merge]. rewrite IH, of_oemit_merge. reflexivity.
Qed.

Local Lemma of_oset_cur : forall l o,
  of_ostate (oset_cur l o) = oset_cur (of_oitems l) (of_ostate o).
Proof. intros l [out [|f stk] word]; [reflexivity|destruct f; reflexivity]. Qed.

Local Lemma of_oword_reset : forall o,
  of_ostate (oword_reset o) = oword_reset (of_ostate o).
Proof. intros [out stk word]; reflexivity. Qed.

Local Lemma of_remember_word_start : forall `{P : PosPolicy} `{C : InlineCursor} c o,
  of_ostate (@remember_word_start P C c o) = of_ostate o.
Proof.
  intros P C c [out stk word]. unfold remember_word_start.
  destruct (pos_records && is_ws c)%bool; reflexivity.
Qed.

Local Lemma of_flush_text_at : forall `{P : PosPolicy} `{C : InlineCursor} txt o,
  of_ostate (@flush_text_at P C txt o) = flush_text txt (of_ostate o).
Proof.
  intros P C txt o. unfold flush_text; unfold flush_text_at.
  destruct (nonempty_str txt); [|reflexivity].
  rewrite of_oemit, of_imk. reflexivity.
Qed.

Local Lemma of_flush_text_to_at :
  forall `{P : PosPolicy} `{C : InlineCursor} stop txt o,
  of_ostate (@flush_text_to_at P C stop txt o) =
  flush_text txt (of_ostate o).
Proof.
  intros P C stop txt o. unfold flush_text; unfold flush_text_to_at, flush_text_at.
  destruct (nonempty_str txt); [|reflexivity].
  rewrite !of_oemit, !of_imk. reflexivity.
Qed.

Local Lemma of_opush_at : forall k m cm open o,
  of_ostate (opush_at k m cm open o) =
  opush_at k m cm null_span (of_ostate o).
Proof. intros k m cm open [out stk word]; reflexivity. Qed.

Local Lemma of_opush : forall `{P : PosPolicy} `{C : InlineCursor} k m o,
  of_ostate (@opush T P C k m o) =
  @opush T semantic_pos semantic_inline_cursor k m (of_ostate o).
Proof.
  intros P C k m o. unfold opush, dtoken_span, pspan.
  rewrite of_opush_at. destruct (@pos_records P); reflexivity.
Qed.

Local Lemma of_bpush : forall `{P : PosPolicy} `{C : InlineCursor} image o,
  of_ostate (@bpush P C image o) =
  @bpush semantic_pos semantic_inline_cursor image (of_ostate o).
Proof.
  intros P C image [out stk word]. unfold bpush, pspan.
  destruct (@pos_records P); reflexivity.
Qed.

Local Lemma of_dpush : forall image open o,
  of_ostate (dpush image open o) =
  dpush image null_span (of_ostate o).
Proof. intros image open [out stk word]; reflexivity. Qed.

Local Lemma of_isnoc : forall n l,
  Erase.of_inlines (isnoc n l) = isnoc (Erase.inode n) (Erase.of_inlines l).
Proof.
  intros n [|m l]; [reflexivity|].
  destruct m as [q [|lv b'] u]; try reflexivity;
    destruct u; try reflexivity;
    destruct n as [p [|kv a'] v]; try reflexivity;
    destruct v; reflexivity.
Qed.

Local Lemma of_fr_src : forall f, fr_src (of_frame f) = fr_src f.
Proof. intros [k m open out]; destruct k; reflexivity. Qed.

Local Lemma of_fr_lit : forall `{P : PosPolicy} f,
  @fr_lit T semantic_pos (of_frame f) = Erase.inode (@fr_lit T P f).
Proof.
  intros P f. unfold fr_lit. rewrite of_imk, of_fr_src. reflexivity.
Qed.

Local Lemma of_nonempty : forall l, nonempty (of_oitems l) = nonempty l.
Proof. intros [|i l]; reflexivity. Qed.

Local Lemma of_dmatch : forall k m f, dmatch k m (of_frame f) = dmatch k m f.
Proof. intros k m [[?|?|?] ? ? ?]; reflexivity. Qed.

Local Lemma of_fr_barrier : forall f, fr_barrier (of_frame f) = fr_barrier f.
Proof. intros [[?|?|?] ? ? ?]; reflexivity. Qed.

Local Lemma of_istarts_str : forall l,
  istarts_str (Erase.of_inlines l) = istarts_str l.
Proof.
  intros [|[p [|kv a] v] l]; try reflexivity; destruct v; reflexivity.
Qed.

Local Lemma of_oattach_list : forall `{P : PosPolicy} a spec w out,
  Erase.of_inlines (@oattach_list P a spec w out) =
  @oattach_list semantic_pos a null_span None (Erase.of_inlines out).
Proof.
  intros P a spec w [|[p a' v] out]; [reflexivity|].
  destruct v;
    try (destruct a' as [|kv a'];
         cbn [Erase.of_inlines Erase.inode oattach_list];
         rewrite ?of_add_inline_role; reflexivity).
  destruct a' as [|kv a'];
    [|cbn [Erase.of_inlines Erase.inode oattach_list];
      rewrite of_add_inline_role; reflexivity].
  cbn [Erase.of_inlines Erase.inode Erase.of_inline oattach_list].
  destruct (last_ws_split s) as [pre w0].
  destruct (nonempty_str w0); [|reflexivity].
  destruct a as [|kv a]; [reflexivity|].
  destruct (split_text_pos p w) as [pp wp]. cbn [split_text_pos].
  rewrite of_isnoc, of_add_inline_role. cbn [Erase.inode].
  destruct (nonempty_str pre); [rewrite of_isnoc|]; reflexivity.
Qed.

(* Erasure commutes with resolution for the same reason it commutes with
   `oattach_list`: the pass moves attributes and a spec's range, and the
   range is what erasure drops. *)
Local Lemma of_oresolve_go : forall `{P : PosPolicy} l,
  @oresolve_go semantic_pos (of_oitems l) =
  (Erase.of_inlines (fst (@oresolve_go P l)), snd (@oresolve_go P l)).
Proof.
  intros P. induction l as [|[n|a spec w] l IH]; [reflexivity| |];
    cbn [of_oitems of_oitem oresolve_go];
    rewrite IH; destruct (@oresolve_go P l) as [out m]; cbn [fst snd].
  - destruct m; [rewrite of_isnoc|]; reflexivity.
  - rewrite <- (of_istarts_str (@oattach_list P a spec w out)).
    rewrite of_oattach_list. reflexivity.
Qed.

Local Lemma of_oresolve : forall `{P : PosPolicy} l,
  Erase.of_inlines (@oresolve P l) = @oresolve semantic_pos (of_oitems l).
Proof.
  intros P l. unfold oresolve. rewrite of_oresolve_go. reflexivity.
Qed.

Local Lemma of_oclose_go : forall `{P : PosPolicy} k m pend stk,
  @oclose_go T semantic_pos k m (of_oitems pend) (map of_frame stk) =
  match @oclose_go T P k m pend stk with
  | None => None
  | Some (content, open, rest) =>
      Some (of_oitems content, null_span, map of_frame rest)
  end.
Proof.
  intros P k m pend stk. revert pend.
  induction stk as [|f stk IH]; intros pend; [reflexivity|].
  cbn [map oclose_go]. rewrite of_dmatch, of_fr_barrier.
  change (fr_out (of_frame f)) with (of_oitems (fr_out f)).
  rewrite <- of_oapp.
  destruct (dmatch k m f).
  - rewrite of_nonempty.
    destruct (nonempty (oapp pend (fr_out f)));
      cbn [of_frame fr_open]; reflexivity.
  - destruct (fr_barrier f); [reflexivity|].
    rewrite (of_fr_lit f).
    specialize (IH (oapp (oapp pend (fr_out f)) [OIn (@fr_lit T P f)])).
    rewrite !of_oapp in IH. cbn [of_oitems of_oitem] in IH.
    rewrite <- of_oapp in IH. exact IH.
Qed.

Local Lemma of_dnode : forall k ns,
  Erase.of_inline (dnode k ns) = dnode k (Erase.of_inlines ns).
Proof.
  intros k ns. destruct k; cbn [dnode Erase.of_inline];
    rewrite Erase.inline_children; reflexivity.
Qed.

Local Lemma of_bnode : forall image ns tgt,
  Erase.of_inline (bnode image ns tgt) = bnode image (Erase.of_inlines ns) tgt.
Proof.
  intros image ns tgt. destruct image; cbn [bnode Erase.of_inline];
    rewrite Erase.inline_children; reflexivity.
Qed.

Local Lemma span_node : forall ns,
  Erase.of_inline (Span ns) = Span (Erase.of_inlines ns).
Proof.
  intros ns. cbn [Erase.of_inline]. rewrite Erase.inline_children. reflexivity.
Qed.

(* An empty reference's label is the string content of its first
   bracket, which is payload and so survives erasure. *)
Local Lemma of_reference_text : forall i,
  reference_text (Erase.of_inline i) = reference_text i.
Proof.
  refine (inline_ind2
    (fun i => reference_text (Erase.of_inline i) = reference_text i)
    (fun ils => reference_text (Emph (Erase.of_inlines ils)) =
                reference_text (Emph ils))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
    intros;
    cbn [Erase.of_inline Erase.of_inlines Erase.inode reference_text
      node_contents] in *;
    rewrite ?Erase.inline_children in *; congruence.
Qed.

Local Lemma of_reference_inlines_text : forall ns,
  reference_inlines_text (Erase.of_inlines ns) = reference_inlines_text ns.
Proof.
  intros ns. unfold reference_inlines_text. f_equal.
  rewrite Erase.inlines_map, map_map. apply map_ext.
  intros [p a x]; cbn [node_contents Erase.inode]. apply of_reference_text.
Qed.

Local Lemma of_auto_node : forall s, Erase.of_inline (auto_node s) = auto_node s.
Proof. intros s. unfold auto_node. destruct (auto_email s); reflexivity. Qed.

Local Lemma of_vnode : forall vk s, Erase.of_inline (vnode vk s) = vnode vk s.
Proof. intros [|st] s; reflexivity. Qed.

Local Lemma of_oclose : forall `{P : PosPolicy} k m stop o,
  sclose k m (of_ostate o) =
  option_map of_ostate (@oclose T P k m stop o).
Proof.
  intros P k m stop o. unfold sclose, oclose.
  change (os_stk (of_ostate o)) with (map of_frame (os_stk o)).
  change (@nil oitem) with (of_oitems []) at 1.
  rewrite of_oclose_go.
  destruct (@oclose_go T P k m [] (os_stk o)) as [[[content open] rest]|];
    [|reflexivity].
  cbn [option_map].
  rewrite of_oemit, of_imk, of_dnode, Erase.inlines_rev,
    of_oresolve.
  destruct o as [out stk word]; reflexivity.
Qed.

Local Lemma of_bclose_go : forall `{P : PosPolicy} pend stk,
  @bclose_go T semantic_pos (of_oitems pend) (map of_frame stk) =
  match @bclose_go T P pend stk with
  | None => None
  | Some (content, image, open, rest) =>
      Some (of_oitems content, image, null_span, map of_frame rest)
  end.
Proof.
  intros P pend stk. revert pend.
  induction stk as [|f stk IH]; intros pend; [reflexivity|].
  cbn [map bclose_go].
  change (fr_kind (of_frame f)) with (fr_kind f).
  change (fr_out (of_frame f)) with (of_oitems (fr_out f)).
  rewrite <- of_oapp.
  destruct (fr_kind f) eqn:Ek; [| |reflexivity].
  - rewrite (of_fr_lit f).
    specialize (IH (oapp (oapp pend (fr_out f)) [OIn (@fr_lit T P f)])).
    rewrite !of_oapp in IH. cbn [of_oitems of_oitem] in IH.
    rewrite <- of_oapp in IH. exact IH.
  - cbn [of_frame fr_open]. reflexivity.
Qed.

Local Lemma of_bclose : forall `{P : PosPolicy} o,
  @bclose T semantic_pos (of_ostate o) =
  match @bclose T P o with
  | None => None
  | Some (kids, image, open, o') =>
      Some (Erase.of_inlines kids, image, null_span, of_ostate o')
  end.
Proof.
  intros P o. unfold bclose.
  change (os_stk (of_ostate o)) with (map of_frame (os_stk o)).
  change (@nil oitem) with (of_oitems []) at 1.
  rewrite of_bclose_go.
  destruct (@bclose_go T P [] (os_stk o)) as [[[[content image] open] rest]|];
    [|reflexivity].
  rewrite <- of_oresolve, <- Erase.inlines_rev.
  destruct o as [out stk word]; reflexivity.
Qed.

Local Lemma of_bunpush : forall o,
  bunpush (of_ostate o) =
  match bunpush o with
  | None => None
  | Some (image, open, o') => Some (image, null_span, of_ostate o')
  end.
Proof.
  intros [out [|[[image| |] marked open [|i l]] stk] word]; reflexivity.
Qed.

Local Lemma of_opop_str : forall o,
  opop_str (of_ostate o) =
  (fst (opop_str o), of_ostate (snd (opop_str o))).
Proof.
  intros [out [|f stk] word].
  - destruct out as [|[[p a v]|b sp w] out]; try reflexivity.
    destruct a as [|kv a]; [destruct v; reflexivity|reflexivity].
  - destruct f as [k marked open [|[[p a v]|b sp w] l]]; try reflexivity.
    destruct a as [|kv a]; [destruct v; reflexivity|reflexivity].
Qed.

Local Lemma of_bflat : forall `{P : PosPolicy} `{C : InlineCursor} kids txt o,
  @bflat semantic_pos semantic_inline_cursor (Erase.of_inlines kids) txt
    (of_ostate o)
  = (fst (@bflat P C kids txt o), of_ostate (snd (@bflat P C kids txt o))).
Proof.
  intros P C kids. induction kids as [|[p a x] kids IH]; intros txt o;
    [reflexivity|].
  rewrite Erase.inlines_cons. unfold Erase.inode at 1.
  destruct a as [|kv a];
    [destruct x; try (cbn [Erase.of_inline bflat]; apply IH)|];
    cbn [bflat]; sem_flush;
    rewrite <- of_flush_text_at, (oemit_node p); apply IH.
Qed.

Local Lemma of_bsplit_nl : forall `{P : PosPolicy} `{C : InlineCursor} s txt o,
  @bsplit_nl semantic_pos semantic_inline_cursor s txt (of_ostate o)
  = (fst (@bsplit_nl P C s txt o),
     of_ostate (snd (@bsplit_nl P C s txt o))).
Proof.
  intros P C s. induction s as [|c s IH]; intros txt o; [reflexivity|].
  cbn [bsplit_nl]. destruct (Ascii.eqb c nl_char); [|apply IH].
  sem_flush. rewrite <- of_flush_text_at.
  change (@imk_here semantic_pos semantic_inline_cursor SoftBreak)
    with (@imk_here semantic_pos semantic_inline_cursor
            (Erase.of_inline SoftBreak)).
  rewrite <- of_imk_here, <- of_oemit. apply IH.
Qed.

Local Lemma of_oclose_barred : forall k m o,
  oclose_barred k m (of_ostate o) = oclose_barred k m o.
Proof.
  intros k m o. unfold oclose_barred.
  change (os_stk (of_ostate o)) with (map of_frame (os_stk o)).
  generalize false. generalize (os_stk o) as stk.
  induction stk as [|f stk IH]; intros past; [reflexivity|].
  cbn [map oclose_barred_go]. rewrite of_dmatch, of_fr_barrier.
  destruct (dmatch k m f); [reflexivity|apply IH].
Qed.

Local Lemma of_bclosed_lit : forall `{P : PosPolicy} `{C : InlineCursor}
  kids image o,
  @bclosed_lit semantic_pos semantic_inline_cursor (Erase.of_inlines kids) image
    (of_ostate o)
  = (fst (@bclosed_lit P C kids image o),
     of_ostate (snd (@bclosed_lit P C kids image o))).
Proof.
  intros P C kids image o. unfold bclosed_lit.
  rewrite of_opop_str.
  destruct (opop_str o) as [pre o1]; cbn [fst snd].
  rewrite of_bflat.
  destruct (@bflat P C kids (pre ++ bracket_open image) o1) as [txt o2];
    reflexivity.
Qed.

Local Lemma of_bspan_lit : forall `{P : PosPolicy} `{C : InlineCursor}
  kids image src o,
  @bspan_lit semantic_pos semantic_inline_cursor (Erase.of_inlines kids) image
    src (of_ostate o)
  = (fst (@bspan_lit P C kids image src o),
     of_ostate (snd (@bspan_lit P C kids image src o))).
Proof.
  intros P C kids image src o. unfold bspan_lit.
  rewrite of_bclosed_lit.
  destruct (@bclosed_lit P C kids image o) as [txt o']; cbn [fst snd].
  apply of_bsplit_nl.
Qed.

Local Lemma of_battr_lit : forall `{P : PosPolicy} `{C : InlineCursor} src txt o,
  @battr_lit semantic_pos semantic_inline_cursor src txt (of_ostate o)
  = (fst (@battr_lit P C src txt o),
     of_ostate (snd (@battr_lit P C src txt o))).
Proof. intros P C src txt o. apply of_bsplit_nl. Qed.

Local Lemma of_bref_lit : forall `{P : PosPolicy} `{C : InlineCursor}
  kids image label o,
  @bref_lit semantic_pos semantic_inline_cursor (Erase.of_inlines kids) image
    label (of_ostate o)
  = (fst (@bref_lit P C kids image label o),
     of_ostate (snd (@bref_lit P C kids image label o))).
Proof.
  intros P C kids image label o. unfold bref_lit.
  rewrite of_bclosed_lit.
  destruct (@bclosed_lit P C kids image o) as [txt o']; reflexivity.
Qed.

Local Lemma of_bnote_lit : forall `{P : PosPolicy} `{C : InlineCursor}
  esc image label o,
  @bnote_lit semantic_pos semantic_inline_cursor esc image label
    (of_ostate o)
  = (fst (@bnote_lit P C esc image label o),
     of_ostate (snd (@bnote_lit P C esc image label o))).
Proof.
  intros P C esc image label o. unfold bnote_lit.
  rewrite of_opop_str.
  destruct (opop_str o) as [pre o1]; reflexivity.
Qed.

Local Lemma of_ospan_bang : forall `{P : PosPolicy} `{C : InlineCursor} image o,
  of_ostate (@ospan_bang P C image o) =
  @ospan_bang semantic_pos semantic_inline_cursor image (of_ostate o).
Proof.
  intros P C image o. unfold ospan_bang. destruct image; [|reflexivity].
  rewrite of_opop_str. destruct (opop_str o) as [pre o1]; cbn [fst snd].
  apply of_flush_text_at.
Qed.

Local Lemma of_ilead : forall `{P : PosPolicy} `{C : InlineCursor} c txt prev o,
  of_iscan (@ilead T P C c txt prev o) =
  @ilead T semantic_pos semantic_inline_cursor c txt prev (of_ostate o).
Proof.
  intros P C c txt prev o. unfold ilead.
  destruct (is_bslash c); [reflexivity|].
  destruct (is_tick c);
    [cbn [of_iscan]; rewrite of_flush_text_at; reflexivity|].
  destruct (Ascii.eqb c dollar); [reflexivity|].
  destruct (Ascii.eqb c period); [reflexivity|].
  destruct (Ascii.eqb c hyphen); [reflexivity|].
  destruct (Ascii.eqb c lbrace); [reflexivity|].
  destruct (Ascii.eqb c bang); [reflexivity|].
  destruct (Ascii.eqb c lt); [reflexivity|].
  destruct (Ascii.eqb c ":"%char);
    [cbn [of_iscan]; rewrite of_remember_word_start; reflexivity|].
  destruct (Ascii.eqb c lbrack).
  { destruct (note_pos txt prev && wikilinks_enabled)%bool;
      [rewrite of_bunpush; destruct (bunpush o) as [[[image open] o']|];
        [reflexivity|]|];
      cbn [of_iscan]; rewrite of_bpush, of_flush_text_at; reflexivity. }
  destruct (Ascii.eqb c rbrack); [reflexivity|].
  destruct (Ascii.eqb c hat && note_pos txt prev && notes_enabled)%bool;
    [rewrite of_bunpush; destruct (bunpush o) as [[[image open] o']|];
      [reflexivity|]|];
    destruct (dstyle_of c); cbn [of_iscan];
    rewrite ?of_remember_word_start; reflexivity.
Qed.

Local Lemma of_idest_open : forall `{P : PosPolicy} `{C : InlineCursor}
  kids image open o,
  of_iscan (@idest_open P C kids image open o) =
  @idest_open semantic_pos semantic_inline_cursor (Erase.of_inlines kids) image
    null_span (of_ostate o).
Proof.
  intros P C kids image open o. unfold idest_open.
  rewrite <- (of_dpush image open), of_bflat.
  destruct (@bflat P C kids EmptyString (dpush image open o)) as [txt o'];
    reflexivity.
Qed.

Local Lemma of_oopen_marked : forall `{P : PosPolicy} `{C : InlineCursor}
  k cm txt o,
  of_ostate (@oopen_marked T P C k cm txt o) =
  @oopen_marked T semantic_pos semantic_inline_cursor k cm txt (of_ostate o).
Proof.
  intros P C k cm txt o. unfold oopen_marked.
  rewrite of_opush_at, of_flush_text_to_at.
  unfold dtoken_span, pspan. destruct (@pos_records P); reflexivity.
Qed.

Local Lemma of_idelim_open_marked : forall `{P : PosPolicy} `{C : InlineCursor}
  k cm txt o,
  of_iscan (@idelim_open_marked T P C k cm txt o) =
  @idelim_open_marked T semantic_pos semantic_inline_cursor k cm txt
    (of_ostate o).
Proof.
  intros P C k cm txt o. unfold idelim_open_marked.
  cbn [of_iscan]. rewrite of_oopen_marked. reflexivity.
Qed.

Local Lemma of_islice_end : forall st,
  of_iscan (islice_end st) = islice_end (of_iscan st).
Proof.
  induction st; cbn [of_iscan islice_end];
    try reflexivity; try (destruct esc; reflexivity).
  exact IHst.
Qed.

Local Lemma of_iattr_mark : forall `{P : PosPolicy} `{C : InlineCursor}
  src a txt o,
  of_iscan (@iattr_mark P C src a txt o) =
  @iattr_mark semantic_pos semantic_inline_cursor src a txt (of_ostate o).
Proof.
  intros P C src a txt o. unfold iattr_mark.
  cbn [of_iscan]. rewrite of_omark,
    (of_flush_text_to_at (spot_before cursor_start (String lbrace src))).
  unfold pspan. destruct (@pos_records P); reflexivity.
Qed.

Local Lemma of_iattr_feed : forall `{P : PosPolicy} `{C : InlineCursor}
  c p src txt prev sh o,
  of_iscan (@iattr_feed T P C c p src txt prev sh o) =
  @iattr_feed T semantic_pos semantic_inline_cursor c p src txt prev
    (of_iscan sh) (of_ostate o).
Proof.
  intros P C c p src txt prev sh o. unfold iattr_feed.
  destruct (ap_failed (astep p c)); [reflexivity|].
  destruct (ap_done (astep p c)); [apply of_iattr_mark|].
  cbn [of_iscan]. rewrite of_islice_end. reflexivity.
Qed.

Local Lemma of_ibrace_step_at : forall `{P : PosPolicy} `{C : InlineCursor}
  allow c txt prev o,
  of_iscan (@ibrace_step_at T P C allow c txt prev o) =
  @ibrace_step_at T semantic_pos semantic_inline_cursor allow c txt prev
    (of_ostate o).
Proof.
  intros P C allow c txt prev o. unfold ibrace_step_at.
  destruct (dstyle_of c) as [k|]; [reflexivity|].
  destruct allow.
  - rewrite of_iattr_feed, of_ilead. reflexivity.
  - rewrite of_battr_lit.
    destruct (@battr_lit P C EmptyString txt o) as [t o']; cbn [fst snd].
    apply of_ilead.
Qed.

Local Lemma of_ibang_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c txt prev o,
  of_iscan (@ibang_step T P C c txt prev o) =
  @ibang_step T semantic_pos semantic_inline_cursor c txt prev (of_ostate o).
Proof.
  intros P C c txt prev o. unfold ibang_step.
  destruct (Ascii.eqb c lbrack); [|apply of_ilead].
  cbn [of_iscan]. rewrite of_bpush, of_flush_text_to_at. reflexivity.
Qed.

Local Lemma of_idelim_done : forall `{P : PosPolicy} `{C : InlineCursor}
  k txt before marker next o,
  of_iscan (@idelim_done T P C k txt before marker next o) =
  @idelim_done T semantic_pos semantic_inline_cursor k txt before marker next
    (of_ostate o).
Proof.
  intros P C k txt before marker next o. unfold idelim_done.
  destruct (dbare k before && negb marker && nonspace_at next)%bool;
    [|reflexivity].
  cbn [of_iscan]. rewrite of_opush, of_flush_text_to_at. reflexivity.
Qed.

Local Lemma of_idelim_resolve : forall `{P : PosPolicy} `{C : InlineCursor}
  k txt before marker next o,
  of_iscan (@idelim_resolve T P C k txt before marker next o) =
  @idelim_resolve T semantic_pos semantic_inline_cursor k txt before marker next
    (of_ostate o).
Proof.
  intros P C k txt before marker next o. unfold idelim_resolve.
  destruct (nonspace_at before || marker)%bool; [|apply of_idelim_done].
  sem_flush.
  rewrite <- (of_flush_text_to_at
                (span_start (@dtoken_span T P C k false)) txt o).
  rewrite (of_oclose k marker
             (if marker then cursor_stop else cursor_start)).
  destruct (@oclose T P k marker _ _) as [o'|]; cbn [option_map].
  - reflexivity.
  - rewrite of_oclose_barred. destruct (oclose_barred k marker o);
      [reflexivity|apply of_idelim_done].
Qed.

Local Lemma of_idollar_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c two txt prev o,
  of_iscan (@idollar_step T P C c two txt prev o) =
  @idollar_step T semantic_pos semantic_inline_cursor c two txt prev
    (of_ostate o).
Proof.
  intros P C c two txt prev o. unfold idollar_step.
  destruct (Ascii.eqb c dollar); [destruct two; reflexivity|].
  destruct (is_tick c && math_enabled)%bool; [|apply of_ilead].
  cbn [of_iscan]. rewrite of_flush_text_to_at. reflexivity.
Qed.

Local Lemma of_iperiod_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c two txt prev o,
  of_iscan (@iperiod_step T P C c two txt prev o) =
  @iperiod_step T semantic_pos semantic_inline_cursor c two txt prev
    (of_ostate o).
Proof.
  intros P C c two txt prev o. unfold iperiod_step.
  destruct (Ascii.eqb c period); [destruct two; reflexivity|apply of_ilead].
Qed.

Local Lemma of_idash_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c n txt prev o,
  of_iscan (@idash_step T P C c n txt prev o) =
  @idash_step T semantic_pos semantic_inline_cursor c n txt prev
    (of_ostate o).
Proof.
  intros P C c n txt prev o. unfold idash_step.
  destruct (Ascii.eqb c hyphen); [reflexivity|].
  destruct (Ascii.eqb c rbrace); [|apply of_ilead].
  destruct (dstyle_of hyphen) as [k|]; [|reflexivity].
  destruct (Nat.leb (dwidth k) n); [apply of_idelim_resolve|reflexivity].
Qed.

Local Lemma of_iresolve : forall `{P : PosPolicy} `{C : InlineCursor} st,
  of_iscan (@iresolve T P C st) =
  @iresolve T semantic_pos semantic_inline_cursor (of_iscan st).
Proof.
  intros P C [| | |k extra txt before marked o| | | | | | | | | | | | | | | |];
    try reflexivity.
  cbn [of_iscan iresolve].
  destruct (Nat.ltb (S extra) (dwidth k)); [reflexivity|].
  destruct marked;
    [apply of_idelim_open_marked|apply of_idelim_resolve].
Qed.

Local Lemma of_iescws_resolve : forall `{P : PosPolicy} `{C : InlineCursor}
  ws txt prev o,
  let '(t, pv, o') := @iescws_resolve P C ws txt prev o in
  @iescws_resolve semantic_pos semantic_inline_cursor ws txt prev
    (of_ostate o) = (t, pv, of_ostate o').
Proof.
  intros P C [|c rest] txt prev o; [reflexivity|].
  cbn [iescws_resolve]. destruct (Ascii.eqb c " "%char); [|reflexivity].
  rewrite of_oemit, of_imk, of_flush_text_to_at. reflexivity.
Qed.

Local Lemma of_iesc_hard : forall `{P : PosPolicy} `{C : InlineCursor} ws txt o,
  of_ostate (@iesc_hard P C ws txt o) =
  @iesc_hard semantic_pos semantic_inline_cursor ws txt (of_ostate o).
Proof.
  intros P C ws txt o. unfold iesc_hard.
  rewrite of_oemit, of_flush_text_to_at, of_imk_here. reflexivity.
Qed.

Local Lemma of_ispan_feed : forall `{P : PosPolicy} `{C : InlineCursor}
  c kids image open p src o,
  of_iscan (@ispan_feed T P C c kids image open p src o) =
  @ispan_feed T semantic_pos semantic_inline_cursor c (Erase.of_inlines kids) image
    null_span p src (of_ostate o).
Proof.
  intros P C c kids image open p src o. unfold ispan_feed.
  destruct (ap_failed (astep p c)).
  - rewrite of_bspan_lit.
    destruct (@bspan_lit P C kids image src o) as [txt o']; cbn [fst snd].
    apply of_ilead.
  - destruct (ap_done (astep p c)); [|reflexivity].
    cbn [of_iscan]. rewrite of_oemit, of_add_inline_role,
      of_ospan_bang.
    cbn [Erase.inode]. rewrite span_node. reflexivity.
Qed.

Local Lemma of_inote_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c esc image label open o,
  of_iscan (@inote_step P C c esc image label open o) =
  @inote_step semantic_pos semantic_inline_cursor c esc image label null_span
    (of_ostate o).
Proof.
  intros P C c esc image label open o. unfold inote_step.
  destruct esc; [reflexivity|].
  destruct (is_bslash c); [reflexivity|].
  destruct (Ascii.eqb c rbrack); [|reflexivity].
  cbn [of_iscan]. rewrite of_oemit, of_imk, of_ospan_bang.
  reflexivity.
Qed.

Local Lemma of_bwiki_lit : forall esc rb image region o,
  bwiki_lit esc rb image region (of_ostate o) =
  (fst (bwiki_lit esc rb image region o),
   of_ostate (snd (bwiki_lit esc rb image region o))).
Proof.
  intros esc rb image region o. unfold bwiki_lit.
  rewrite of_opop_str. destruct (opop_str o) as [pre o1]; reflexivity.
Qed.

Local Lemma of_iwiki_close : forall `{P : PosPolicy} `{C : InlineCursor}
  image region open o,
  of_iscan (@iwiki_close P C image region open o) =
  @iwiki_close semantic_pos semantic_inline_cursor image region null_span
    (of_ostate o).
Proof.
  intros P C image region open o. unfold iwiki_close.
  destruct (wiki_split region) as [[|x t] al].
  - rewrite of_bwiki_lit.
    destruct (bwiki_lit false true image region o) as [txt o']; reflexivity.
  - cbn [of_iscan]. rewrite of_oemit, of_imk. reflexivity.
Qed.

Local Lemma of_iwiki_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c esc rb image region open o,
  of_iscan (@iwiki_step P C c esc rb image region open o) =
  @iwiki_step semantic_pos semantic_inline_cursor c esc rb image region
    null_span (of_ostate o).
Proof.
  intros P C c esc rb image region open o. unfold iwiki_step.
  destruct esc; [reflexivity|].
  destruct (rb && Ascii.eqb c rbrack)%bool; [apply of_iwiki_close|].
  destruct (is_bslash c); [reflexivity|].
  destruct (Ascii.eqb c rbrack); reflexivity.
Qed.

Local Lemma of_iauto_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c src txt o,
  of_iscan (@iauto_step T P C c src txt o) =
  @iauto_step T semantic_pos semantic_inline_cursor c src txt (of_ostate o).
Proof.
  intros P C c src txt o. unfold iauto_step.
  destruct (Ascii.eqb c gt && auto_body_ok src && auto_kind_ok src)%bool.
  - cbn [of_iscan]. rewrite of_oemit, of_imk, of_auto_node,
      of_flush_text_to_at. reflexivity.
  - destruct (Ascii.eqb c gt || is_ws c || Ascii.eqb c lt)%bool;
      [apply of_ilead|reflexivity].
Qed.

Local Lemma of_iraw_step_at : forall `{P : PosPolicy} `{C : InlineCursor}
  allow c spec txt o,
  of_iscan (@iraw_step_at T P C allow c spec txt o) =
  @iraw_step_at T semantic_pos semantic_inline_cursor allow c spec txt
    (of_ostate o).
Proof.
  intros P C allow c spec txt o. unfold iraw_step_at.
  destruct (Ascii.eqb c rbrace && raw_spec_ok spec)%bool.
  - destruct raw_inline_enabled.
    + cbn [of_iscan]. rewrite of_oemit, of_imk. reflexivity.
    + rewrite of_ilead, of_oemit, of_imk. reflexivity.
  - destruct (match spec with
              | EmptyString => negb (Ascii.eqb c eqchar)
              | _ => (Ascii.eqb c rbrace || raw_stop c)%bool
              end);
      [|reflexivity].
    destruct spec as [|d spec];
      [rewrite of_ibrace_step_at|rewrite of_ilead];
      rewrite of_oemit, of_imk; reflexivity.
Qed.

Local Lemma of_isymbol_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c alias txt o sh,
  of_iscan (@isymbol_step P C c alias txt o sh) =
  @isymbol_step semantic_pos semantic_inline_cursor c alias txt
    (of_ostate o) (of_iscan sh).
Proof.
  intros P C c alias txt o sh. unfold isymbol_step.
  destruct (symbol_char c); [reflexivity|].
  destruct (Ascii.eqb c ":"%char && nonempty_str alias)%bool;
    [|reflexivity].
  cbn [of_iscan]. rewrite of_oemit, of_imk,
    of_flush_text_to_at. reflexivity.
Qed.

Local Lemma iscan_attr : forall ap src txt prev sh o,
  of_iscan (IAttr ap src txt prev sh o) =
  IAttr ap src txt prev (of_iscan sh) (of_ostate o).
Proof. reflexivity. Qed.

Local Lemma iscan_dest : forall kids image open esc depth dst sh o,
  of_iscan (IDest kids image open esc depth dst sh o) =
  IDest (Erase.of_inlines kids) image null_span esc depth dst
    (of_iscan sh) (of_ostate o).
Proof. reflexivity. Qed.

(*
The transition erases
---------------------

Uniform in the policy: at `located_pos` it says the spans the scan
records are all that distinguish it from the semantic reading, and at
`semantic_pos` it says the semantic reading is position-free.  No branch
reads a coordinate, so every case closes by rewriting erasure through the
state the branch builds.
*)
Theorem of_istep_at :
  forall `{P : PosPolicy} `{C : InlineCursor} allow c st,
  of_iscan (@istep_at T P C allow c st) =
  @istep_at T semantic_pos semantic_inline_cursor allow c (of_iscan st).
Proof.
  intros P C allow c st. revert allow c.
  induction st as
    [esc txt prev o | ws txt prev o | txt prev o
    | k extra txt before marked o | n vk o | n run txt vk o
    | two txt prev o | two txt prev o | n txt prev o | txt prev o
    | txt o | kids image open ap src o | ap src txt prev sh IHsh o
    | kids image open label o | esc image label open o
    | esc rb image region open o
    | kids image open esc depth dst sh IHsh o | src txt o
    | alias txt sh IHsh o | spec txt o ];
    intros allow c.
  - (* IText *)
    destruct esc; cbn [of_iscan istep_at].
    + destruct (is_ws c); reflexivity.
    + apply of_ilead.
  - (* IEscWs *)
    cbn [of_iscan istep_at]. destruct (is_ws c); [reflexivity|].
    pose proof (of_iescws_resolve (P:=P) (C:=C) ws txt prev o) as H.
    destruct (@iescws_resolve P C ws txt prev o) as [[t pv] o'].
    rewrite H. apply of_ilead.
  - (* IBrace *) apply of_ibrace_step_at.
  - (* IDelim *)
    cbn [of_iscan istep_at].
    destruct (Nat.ltb (S extra) (dwidth k)).
    { destruct (Ascii.eqb c (dchar k));
        [destruct marked; reflexivity|apply of_ilead]. }
    destruct marked.
    { rewrite of_ilead, of_oopen_marked. reflexivity. }
    pose proof (of_idelim_resolve (P:=P) (C:=C) k txt before
                  (Ascii.eqb c rbrace) (Some c) o) as Hr.
    destruct (Ascii.eqb c rbrace); [exact Hr|].
    rewrite <- Hr.
    destruct (@idelim_resolve T P C k txt before false (Some c) o)
      as [esc' txt' prev' o'| | | | | | | | | | | | | | | | | | |];
      try reflexivity.
    destruct esc'; [reflexivity|apply of_ilead].
  - (* IOpen *)
    cbn [of_iscan istep_at]. destruct (is_tick c); reflexivity.
  - (* IVerb *)
    cbn [of_iscan istep_at]. destruct (is_tick c); [reflexivity|].
    destruct (Nat.eqb run n); [|reflexivity].
    destruct (Ascii.eqb c lbrace && vkind_verb vk)%bool; [reflexivity|].
    rewrite of_ilead, of_oemit, of_imk, of_vnode. reflexivity.
  - (* IDollar *) apply of_idollar_step.
  - (* IPeriod *) apply of_iperiod_step.
  - (* IDash *) apply of_idash_step.
  - (* IBang *) apply of_ibang_step.
  - (* IClosed *)
    cbn [of_iscan istep_at].
    destruct (Ascii.eqb c lparen || Ascii.eqb c lbrack
              || (Ascii.eqb c lbrace && allow))%bool;
      [|apply of_ilead].
    sem_flush.
    rewrite <- (of_flush_text_to_at (previous_spot cursor_start) txt o).
    rewrite of_bclose.
    destruct (@bclose T P (@flush_text_to_at P C
                (previous_spot cursor_start) txt o))
      as [[[[kids image] open] o']|]; [|apply of_ilead].
    destruct (Ascii.eqb c lparen);
      [cbn [of_iscan]; rewrite of_idest_open; reflexivity|].
    destruct (Ascii.eqb c lbrack); reflexivity.
  - (* ISpan *) apply of_ispan_feed.
  - (* IAttr *)
    rewrite iscan_attr. cbn [istep_at].
    destruct (ap_failed (astep ap c)); [apply IHsh|].
    rewrite of_iattr_feed, IHsh. reflexivity.
  - (* IReference *)
    cbn [of_iscan istep_at]. destruct (Ascii.eqb c rbrack); [|reflexivity].
    cbn [of_iscan]. rewrite of_oemit, of_imk, of_bnode.
    destruct label; [rewrite of_reference_inlines_text|]; reflexivity.
  - (* INote *) apply of_inote_step.
  - (* IWiki *) apply of_iwiki_step.
  - (* IDest *)
    rewrite iscan_dest. destruct esc; cbn [istep_at].
    + rewrite iscan_dest, IHsh. reflexivity.
    + destruct (is_bslash c);
        [rewrite iscan_dest, IHsh; reflexivity|].
      destruct (Ascii.eqb c lparen);
        [rewrite iscan_dest, IHsh; reflexivity|].
      destruct (Ascii.eqb c rparen);
        [|rewrite iscan_dest, IHsh; reflexivity].
      destruct depth as [|d];
        [|rewrite iscan_dest, IHsh; reflexivity].
      cbn [of_iscan]. rewrite of_oemit, of_imk, of_bnode.
      reflexivity.
  - (* IAuto *) apply of_iauto_step.
  - (* ISymbol *)
    cbn [istep_at]. rewrite of_isymbol_step, IHsh. reflexivity.
  - (* IRaw *) apply of_iraw_step_at.
Qed.

Local Lemma of_ifinish_ostate_flat : forall `{P : PosPolicy} `{C : InlineCursor} st,
  of_ostate (@ifinish_ostate_flat P C st) =
  @ifinish_ostate_flat semantic_pos semantic_inline_cursor (of_iscan st).
Proof.
  intros P C
    [esc txt prev o | ws txt prev o | txt prev o
    | k extra txt before marked o | n vk o | n run txt vk o
    | two txt prev o | two txt prev o | n txt prev o | txt prev o
    | txt o | kids image open ap src o | ap src txt prev sh o
    | kids image open label o | esc image label open o
    | esc rb image region open o
    | kids image open esc depth dst sh o | src txt o
    | alias txt sh o | spec txt o ];
    cbn [of_iscan ifinish_ostate_flat];
    try reflexivity.
  - destruct esc; [apply of_iesc_hard|apply of_flush_text_at].
  - apply of_iesc_hard.
  - rewrite of_oemit, of_imk, of_vnode. reflexivity.
  - rewrite of_oemit, of_imk, of_vnode. reflexivity.
  - rewrite of_bspan_lit.
    destruct (@bspan_lit P C kids image src o) as [t o']; cbn [fst snd].
    apply of_flush_text_at.
  - rewrite of_battr_lit.
    destruct (@battr_lit P C src txt o) as [t o']; cbn [fst snd].
    apply of_flush_text_at.
  - rewrite of_bref_lit.
    destruct (@bref_lit P C kids image label o) as [t o']; cbn [fst snd].
    apply of_flush_text_at.
  - rewrite of_bnote_lit.
    destruct (@bnote_lit P C esc image label o) as [t o']; cbn [fst snd].
    apply of_flush_text_at.
  - rewrite of_bwiki_lit.
    destruct (bwiki_lit esc rb image region o) as [t o']; cbn [fst snd].
    apply of_flush_text_at.
  - apply of_flush_text_at.
  - rewrite of_flush_text_at, of_oemit, of_imk. reflexivity.
Qed.

Local Lemma of_ifinish_ostate : forall `{P : PosPolicy} `{C : InlineCursor} st,
  of_ostate (@ifinish_ostate T P C st) =
  @ifinish_ostate T semantic_pos semantic_inline_cursor (of_iscan st).
Proof.
  intros P C st. induction st;
    try (cbn [ifinish_ostate];
         rewrite of_ifinish_ostate_flat, of_iresolve; reflexivity).
  - rewrite iscan_attr. cbn [ifinish_ostate]. assumption.
  - rewrite iscan_dest. cbn [ifinish_ostate]. assumption.
  - cbn [of_iscan ifinish_ostate]. assumption.
Qed.

Local Lemma of_oflatten : forall `{P : PosPolicy} pend stk bottom,
  of_oitems (@oflatten T P pend stk bottom) =
  @oflatten T semantic_pos (of_oitems pend) (map of_frame stk)
    (of_oitems bottom).
Proof.
  intros P pend stk. revert pend.
  induction stk as [|f stk IH]; intros pend bottom; [apply of_oapp|].
  cbn [map oflatten].
  change (fr_out (of_frame f)) with (of_oitems (fr_out f)).
  rewrite (of_fr_lit f), <- of_oapp.
  specialize (IH (oapp (oapp pend (fr_out f)) [OIn (@fr_lit T P f)]) bottom).
  rewrite !of_oapp in IH. cbn [of_oitems of_oitem] in IH.
  rewrite <- of_oapp in IH. exact IH.
Qed.

Local Lemma of_oitems_of : forall `{P : PosPolicy} o,
  of_oitems (@oitems_of T P o) =
  @oitems_of T semantic_pos (of_ostate o).
Proof.
  intros P o. unfold oitems_of.
  change (os_stk (of_ostate o)) with (map of_frame (os_stk o)).
  change (os_out (of_ostate o)) with (of_oitems (os_out o)).
  change (@nil oitem) with (of_oitems []) at 1.
  apply of_oflatten.
Qed.

Local Lemma of_ofinish : forall `{P : PosPolicy} o,
  Erase.of_inlines (@ofinish T P o) = @ofinish T semantic_pos (of_ostate o).
Proof.
  intros P o. unfold ofinish.
  rewrite of_oresolve, of_oitems_of. reflexivity.
Qed.

Local Lemma of_ifinish : forall `{P : PosPolicy} `{C : InlineCursor} st,
  Erase.of_inlines (@ifinish T P C st) =
  @ifinish T semantic_pos semantic_inline_cursor (of_iscan st).
Proof.
  intros P C st. unfold ifinish, ifinish_rev.
  rewrite Erase.inlines_rev, of_ofinish, of_ifinish_ostate. reflexivity.
Qed.

Local Lemma of_ibreak_flat : forall `{P : PosPolicy} `{C : InlineCursor} st,
  of_iscan (@ibreak_flat T P C st) =
  @ibreak_flat T semantic_pos semantic_inline_cursor (of_iscan st).
Proof.
  intros P C. induction st as
    [esc txt prev o | ws txt prev o | txt prev o
    | k extra txt before marked o | n vk o | n run txt vk o
    | two txt prev o | two txt prev o | n txt prev o | txt prev o
    | txt o | kids image open ap src o | ap src txt prev sh o
    | kids image open label o | esc image label open o
    | esc rb image region open o
    | kids image open esc depth dst sh IHdest o | src txt o
    | alias txt sh IHsh o | spec txt o ];
    cbn [of_iscan ibreak_flat];
    try reflexivity.
  - destruct esc; cbn [of_iscan];
      rewrite of_oword_reset;
      [rewrite of_iesc_hard; reflexivity|].
    rewrite of_oemit, of_imk_here, of_flush_text_at. reflexivity.
  - cbn [of_iscan]. rewrite of_oword_reset, of_iesc_hard. reflexivity.
  - destruct (Nat.eqb run n); [|reflexivity].
    cbn [of_iscan]. rewrite of_oword_reset, of_oemit, of_imk_here,
      of_oemit, of_imk, of_vnode. reflexivity.
  - apply of_ispan_feed.
  - rewrite of_iattr_feed. reflexivity.
  - rewrite of_bwiki_lit.
    destruct (bwiki_lit esc rb image region o) as [t o']; cbn [fst snd of_iscan].
    rewrite of_oword_reset, of_oemit, of_imk_here,
      of_flush_text_at. reflexivity.
  - cbn [of_iscan]. rewrite of_oword_reset, of_oemit, of_imk_here,
      of_flush_text_at. reflexivity.
  - exact IHsh.
  - cbn [of_iscan]. rewrite of_oword_reset, of_oemit, of_imk_here,
      of_flush_text_at, of_oemit, of_imk. reflexivity.
Qed.

Local Lemma of_ibreak_at : forall `{P : PosPolicy} `{C : InlineCursor} allow st,
  of_iscan (@ibreak_at T P C allow st) =
  @ibreak_at T semantic_pos semantic_inline_cursor allow (of_iscan st).
Proof.
  intros P C allow st. revert allow. induction st; intros allow;
    try (cbn [ibreak_at];
         rewrite of_ibreak_flat, of_iresolve; reflexivity).
  - rewrite iscan_attr. cbn [ibreak_at].
    rewrite of_iattr_feed, IHst. reflexivity.
  - rewrite iscan_dest. cbn [ibreak_at].
    rewrite iscan_dest, IHst. reflexivity.
  - cbn [ibreak_at]. apply IHst.
Qed.

End WithTable.
End ScanErase.

Section WithTable.
Context {T : dtable}.
Ltac sem_flush :=
  try change (@flush_text_at semantic_pos semantic_inline_cursor)
    with flush_text;
  repeat match goal with
  | |- context [@flush_text_to_at semantic_pos semantic_inline_cursor
                  ?stop ?txt ?o] =>
      change (@flush_text_to_at semantic_pos semantic_inline_cursor
                stop txt o)
        with (flush_text txt o)
  end;
  (* the same for a close, whose node the semantic policy builds without
     reading the span it is handed *)
  repeat match goal with
  | |- context [@oclose T semantic_pos ?k ?m ?stop ?o] =>
      change (@oclose T semantic_pos k m stop o) with (sclose k m o)
  end.

(* The semantic driver the located one erases to.  `iscan_str` and
   `iscan_str_off` are its two instances; it exists so that one statement
   covers a paragraph whose leading lines a failed block spec handed
   back. *)
Local Fixpoint iscan_str_at (allow : bool) (s : string) (st : iscan) : iscan :=
  match s with
  | EmptyString => st
  | String c rest =>
      iscan_str_at allow rest
        (@istep_at T semantic_pos semantic_inline_cursor allow c st)
  end.

Local Lemma iscan_str_at_on : forall s st,
  iscan_str_at inline_attrs_enabled s st = iscan_str s st.
Proof. induction s as [|c s IH]; intros st; [reflexivity|apply IH]. Qed.

Local Lemma iscan_str_at_off : forall s st,
  iscan_str_at false s st = iscan_str_off s st.
Proof. induction s as [|c s IH]; intros st; [reflexivity|apply IH]. Qed.

Local Lemma erase_iscan_str_located :
  forall `{P : PosPolicy} allow k origin rem s st,
  ScanErase.of_iscan (@iscan_str_located T P allow k origin rem s st) =
  iscan_str_at allow s (ScanErase.of_iscan st).
Proof.
  intros P allow k origin rem s. revert rem.
  induction s as [|c s IH]; intros rem st; [reflexivity|].
  cbn [iscan_str_located iscan_str_at]. rewrite IH, ScanErase.of_istep_at.
  reflexivity.
Qed.

(* The driver's two step equations, so that a proof over a paragraph's
   lines rewrites rather than reduces: `cbn` unfolds the recursive call
   as well and loses the name. *)
Local Lemma iscan_lines_located_one : forall `{P : PosPolicy} off org k x st,
  @iscan_lines_located T P off org [(k, x)] st =
  @iscan_str_located T P (allow_attrs off) k org
    (String.length x) (strip_trailing_ws x) st.
Proof. reflexivity. Qed.

Local Lemma iscan_lines_located_cons :
  forall `{P : PosPolicy} off org k x y rest st,
  @iscan_lines_located T P off org ((k, x) :: y :: rest)%list st =
  @iscan_lines_located T P (pred off) org (y :: rest)%list
    (@ibreak_at T P
       (CursorAt (Spot k 0) (lines_start (y :: rest)%list)
          (Spot k (String.length x)))
       (allow_attrs off)
       (@iscan_str_located T P (allow_attrs off) k org
          (String.length x) x st)).
Proof. reflexivity. Qed.

Local Lemma erase_iscan_lines_located : forall `{P : PosPolicy} off org l st,
  ScanErase.of_iscan (@iscan_lines_located T P off org l st) =
  iscan_lines_off off (map snd l) (ScanErase.of_iscan st).
Proof.
  intros P off org l. revert off.
  induction l as [|[k x] l IH]; intros off st.
  - destruct off; reflexivity.
  - destruct l as [|kx l'].
    + rewrite iscan_lines_located_one, erase_iscan_str_located.
      destruct off as [|off'];
        [cbn [iscan_lines_off iscan_lines map snd]; apply iscan_str_at_on
        |cbn [iscan_lines_off map snd]; apply iscan_str_at_off].
    + rewrite iscan_lines_located_cons, IH, ScanErase.of_ibreak_at,
        erase_iscan_str_located.
      destruct off as [|off'];
        [cbn [allow_attrs iscan_lines_off iscan_lines map snd];
         rewrite iscan_str_at_on; reflexivity
        |cbn [allow_attrs iscan_lines_off map snd];
         rewrite iscan_str_at_off; reflexivity].
Qed.

(* The same at the ambient instance, which the statement above reads as
   the semantic scan being position-free. *)
Local Lemma erase_iscan_str_at : forall allow s st,
  ScanErase.of_iscan (iscan_str_at allow s st) = iscan_str_at allow s (ScanErase.of_iscan st).
Proof.
  intros allow s. induction s as [|c s IH]; intros st; [reflexivity|].
  cbn [iscan_str_at]. rewrite IH, ScanErase.of_istep_at. reflexivity.
Qed.

(* The ambient driver's step equations, for the same reason. *)
Local Lemma iscan_lines_off_O : forall l st, iscan_lines_off 0 l st = iscan_lines l st.
Proof. reflexivity. Qed.

Local Lemma iscan_lines_last : forall x st,
  iscan_lines [x] st = iscan_str (strip_trailing_ws x) st.
Proof. reflexivity. Qed.

Local Lemma iscan_lines_step : forall x y rest st,
  iscan_lines (x :: y :: rest)%list st =
  iscan_lines (y :: rest)%list
    (@ibreak T semantic_pos semantic_inline_cursor (iscan_str x st)).
Proof. reflexivity. Qed.

Local Lemma iscan_lines_off_last : forall k x st,
  iscan_lines_off (S k) [x] st = iscan_str_off (strip_trailing_ws x) st.
Proof. reflexivity. Qed.

Local Lemma iscan_lines_off_step : forall k x y rest st,
  iscan_lines_off (S k) (x :: y :: rest)%list st =
  iscan_lines_off k (y :: rest)%list
    (@ibreak_at T semantic_pos semantic_inline_cursor false (iscan_str_off x st)).
Proof. reflexivity. Qed.

Local Lemma erase_iscan_lines_off : forall off l st,
  ScanErase.of_iscan (iscan_lines_off off l st) =
  iscan_lines_off off l (ScanErase.of_iscan st).
Proof.
  intros off l. revert off.
  induction l as [|x l IH]; intros off st.
  - destruct off; reflexivity.
  - destruct l as [|y l'].
    + destruct off as [|off'].
      * rewrite !iscan_lines_off_O, !iscan_lines_last, <- !iscan_str_at_on.
        apply erase_iscan_str_at.
      * rewrite !iscan_lines_off_last, <- !iscan_str_at_off.
        apply erase_iscan_str_at.
    + destruct off as [|off'].
      * rewrite !iscan_lines_off_O, !iscan_lines_step, <- !iscan_lines_off_O,
          IH. unfold ibreak.
        rewrite ScanErase.of_ibreak_at, <- !iscan_str_at_on, erase_iscan_str_at.
        reflexivity.
      * rewrite !iscan_lines_off_step, IH, ScanErase.of_ibreak_at,
          <- !iscan_str_at_off, erase_iscan_str_at. reflexivity.
Qed.

Local Lemma erase_ifinish_located : forall `{P : PosPolicy} l st,
  Erase.of_inlines (@ifinish_located T P l st) =
  @ifinish T semantic_pos semantic_inline_cursor (ScanErase.of_iscan st).
Proof. intros P l st. apply ScanErase.of_ifinish. Qed.

(* A paragraph's lines with their source line indices, scanned so that
   every node records where it came from.  `off` is `para_inlines_off`'s:
   how many leading lines are read with attributes off. *)
Local Definition para_inlines_located `{PosPolicy} (off : nat)
  (l : list (nat * string)) : inlines :=
  ifinish_located l (iscan_lines_located off (lines_start l) l istart).

(* The one entry the block layer calls.  It asks the policy before it
   looks at the lines, so at `semantic_pos` it is `para_inlines_off` of
   their texts by conversion: a paragraph the located parse builds and
   one the semantic parse builds differ in what the nodes carry and in
   nothing else, and no statement about the latter has to mention
   this. *)
Definition para_inlines_at `{PosPolicy} (off : nat)
  (l : list (nat * string)) : inlines :=
  if pos_records
  then para_inlines_located off l
  else para_inlines_off off (map snd l).

(* A table cell is a trimmed infix, rather than a suffix of its source
   line.  Its starting distance from the line end comes from the row
   scanner, so the same located byte scan can read it without treating
   its trimmed text as a whole source line. *)
Definition parse_inline_line_located `{PosPolicy}
  (k rem : nat) (s : string) : inlines :=
  let stop := Spot k (rem - String.length s) in
  @ifinish T _ (CursorAt stop stop (Spot k rem))
    (iscan_str_located inline_attrs_enabled k (Spot k rem) rem s istart).

Lemma erase_parse_inline_line_located : forall `{P : PosPolicy} k rem s,
  Erase.of_inlines (@parse_inline_line_located P k rem s) = parse_inline_line s.
Proof.
  intros P k rem s. unfold parse_inline_line_located, parse_inline_line.
  rewrite ScanErase.of_ifinish, erase_iscan_str_located,
    iscan_str_at_on. reflexivity.
Qed.

Lemma erase_parse_inline_line : forall s,
  Erase.of_inlines (parse_inline_line s) = parse_inline_line s.
Proof.
  intros s. unfold parse_inline_line.
  rewrite ScanErase.of_ifinish, <- iscan_str_at_on, erase_iscan_str_at.
  reflexivity.
Qed.

Lemma para_inlines_at_semantic : forall off l,
  @para_inlines_at semantic_pos off l = para_inlines_off off (map snd l).
Proof. reflexivity. Qed.

Local Lemma erase_istart : ScanErase.of_iscan istart = istart.
Proof. reflexivity. Qed.

Local Lemma erase_para_inlines_located : forall `{P : PosPolicy} off l,
  Erase.of_inlines (@para_inlines_located P off l) =
  para_inlines_off off (map snd l).
Proof.
  intros P off l. unfold para_inlines_located, para_inlines_off.
  rewrite erase_ifinish_located, erase_iscan_lines_located, erase_istart.
  reflexivity.
Qed.

(* The same statement at the ambient instance, which is what a block
   built by it needs: a paragraph the semantic scan produced is already
   position-free. *)
Local Lemma erase_inlines_para_inlines_off : forall off l,
  Erase.of_inlines (para_inlines_off off l) = para_inlines_off off l.
Proof.
  intros off l. unfold para_inlines_off.
  rewrite ScanErase.of_ifinish, erase_iscan_lines_off, erase_istart. reflexivity.
Qed.

Lemma erase_inlines_para_inlines : forall l,
  Erase.of_inlines (para_inlines l) = para_inlines l.
Proof. intros l. apply (erase_inlines_para_inlines_off 0). Qed.

(* Uniform in the policy: at `located_pos` it says the spans the scan
   records are all that distinguish it from the semantic reading; at
   `semantic_pos` it says the semantic reading is position-free, which
   is what the block erasure needs wherever a paragraph is built by the
   ambient instance. *)
Theorem para_inlines_at_erase : forall `{P : PosPolicy} off l,
  Erase.of_inlines (@para_inlines_at P off l) =
  para_inlines_off off (map snd l).
Proof.
  intros P off l. unfold para_inlines_at.
  destruct (@pos_records P);
    [apply erase_para_inlines_located|apply erase_inlines_para_inlines_off].
Qed.

End WithTable.
