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

Coordinates are counted, never measured.  Extracted `String.length`
allocates a unary `nat` per byte, so calling it per byte would make a
line quadratic; `rem` starts at one length per line and a predecessor
carries it down.  That count is the distance to the end of the *source*
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

Local Definition erase_oitem (i : oitem) : oitem :=
  match i with
  | OIn n => OIn (Erase.inode n)
  | OMark a _ _ => OMark a null_span None
  end.

Local Fixpoint erase_oitems (l : oitems) : oitems :=
  match l with
  | [] => []
  | i :: rest => erase_oitem i :: erase_oitems rest
  end.

Local Lemma erase_oitems_map : forall l, erase_oitems l = map erase_oitem l.
Proof. induction l as [|i l IH]; cbn [erase_oitems map]; congruence. Qed.

Local Definition erase_frame (f : frame) : frame :=
  Frame (fr_kind f) (fr_marked f) null_span (erase_oitems (fr_out f)).

Local Definition erase_ostate (o : ostate) : ostate :=
  OState (erase_oitems (os_out o)) (map erase_frame (os_stk o)) None.

Fixpoint erase_iscan (st : iscan) : iscan :=
  match st with
  | IText esc txt prev o => IText esc txt prev (erase_ostate o)
  | IEscWs ws txt prev o => IEscWs ws txt prev (erase_ostate o)
  | IBrace txt prev o => IBrace txt prev (erase_ostate o)
  | IDelim k extra txt before marked o =>
      IDelim k extra txt before marked (erase_ostate o)
  | IOpen n vk o => IOpen n vk (erase_ostate o)
  | IVerb n run txt vk o => IVerb n run txt vk (erase_ostate o)
  | IDollar two txt prev o => IDollar two txt prev (erase_ostate o)
  | IPeriod two txt prev o => IPeriod two txt prev (erase_ostate o)
  | IDash n txt prev o => IDash n txt prev (erase_ostate o)
  | IBang txt prev o => IBang txt prev (erase_ostate o)
  | IClosed txt o => IClosed txt (erase_ostate o)
  | ISpan kids image _ p src o =>
      ISpan (Erase.of_inlines kids) image null_span p src (erase_ostate o)
  | IAttr p src txt prev sh o =>
      IAttr p src txt prev (erase_iscan sh) (erase_ostate o)
  | IReference kids image _ label o =>
      IReference (Erase.of_inlines kids) image null_span label (erase_ostate o)
  | INote esc image label _ o =>
      INote esc image label null_span (erase_ostate o)
  | IWiki esc rb image region _ o =>
      IWiki esc rb image region null_span (erase_ostate o)
  | IDest kids image _ esc depth dst sh o =>
      IDest (Erase.of_inlines kids) image null_span esc depth dst
        (erase_iscan sh) (erase_ostate o)
  | IAuto src txt o => IAuto src txt (erase_ostate o)
  | ISymbol alias txt sh o =>
      ISymbol alias txt (erase_iscan sh) (erase_ostate o)
  | IRaw spec txt o => IRaw spec txt (erase_ostate o)
  end.

(* A node the policy built: its payload survives, its provenance does
   not, and the roles a spec attached to it are provenance. *)
Local Lemma erase_imk : forall `{P : PosPolicy} start stop x,
  Erase.inode (@imk P start stop x) = mk (Erase.of_inline x).
Proof.
  intros P start stop x. unfold imk, posnode, mk, Erase.inode.
  destruct pos_records; reflexivity.
Qed.

Local Lemma erase_add_inline_role : forall `{P : PosPolicy} role r n,
  Erase.inode (@add_inline_role P role r n) = Erase.inode n.
Proof.
  intros P role r [p a x]. unfold add_inline_role, add_roles.
  destruct pos_records; [destruct p|]; reflexivity.
Qed.

Local Lemma erase_osnoc : forall n l,
  erase_oitems (osnoc n l) = osnoc (erase_oitem n) (erase_oitems l).
Proof.
  intros [n|a sp w] [|[m|b sq w'] l]; try reflexivity;
    destruct m as [q [|lv b'] u]; try reflexivity;
    destruct u; try reflexivity;
    destruct n as [p [|kv a'] v]; try reflexivity;
    destruct v; reflexivity.
Qed.

Local Lemma erase_oapp : forall cur out,
  erase_oitems (oapp cur out) = oapp (erase_oitems cur) (erase_oitems out).
Proof.
  induction cur as [|n cur IH]; intros out; [reflexivity|].
  destruct cur as [|n' cur']; cbn [oapp].
  - apply erase_osnoc.
  - change (erase_oitems (n :: n' :: cur')%list)
      with (erase_oitem n :: erase_oitems (n' :: cur')%list)%list.
    cbn [oapp]. rewrite <- IH. reflexivity.
Qed.

Local Lemma erase_oemit : forall n o,
  erase_ostate (oemit n o) = oemit (Erase.inode n) (erase_ostate o).
Proof. intros n [out [|f stk] word]; [reflexivity|destruct f; reflexivity]. Qed.

Local Lemma erase_oemit_node : forall p a x o,
  oemit (Node NoPos a (Erase.of_inline x)) (erase_ostate o) =
  erase_ostate (oemit (Node p a x) o).
Proof. intros p a x o. rewrite erase_oemit. reflexivity. Qed.

Local Lemma erase_imk_here : forall `{P : PosPolicy} `{C : InlineCursor} x,
  Erase.inode (@imk_here P C x) =
  @imk_here semantic_pos semantic_inline_cursor (Erase.of_inline x).
Proof. intros P C x. unfold imk_here. rewrite erase_imk. reflexivity. Qed.

Local Lemma erase_oemit_merge : forall n o,
  erase_ostate (oemit_merge n o) =
  oemit_merge (Erase.inode n) (erase_ostate o).
Proof.
  intros n [out [|f stk] word]; [|destruct f as [fk fm fo fout]];
    unfold oemit_merge, erase_ostate, erase_frame;
    cbn [os_stk os_out os_word_start fr_kind fr_marked fr_out map];
    rewrite (erase_osnoc (OIn n)); reflexivity.
Qed.

Local Lemma erase_omark : forall a spec o,
  erase_ostate (omark a spec o) = omark a null_span (erase_ostate o).
Proof. intros a spec [out [|f stk] word]; [reflexivity|destruct f; reflexivity]. Qed.

Local Lemma erase_oemit_all : forall ns o,
  erase_ostate (oemit_all ns o) = oemit_all (Erase.of_inlines ns) (erase_ostate o).
Proof.
  induction ns as [|n ns IH]; intros o; [reflexivity|].
  cbn [oemit_all]. rewrite IH, erase_oemit. reflexivity.
Qed.

Local Lemma erase_oemit_all_merge : forall ns o,
  erase_ostate (oemit_all_merge ns o) =
  oemit_all_merge (Erase.of_inlines ns) (erase_ostate o).
Proof.
  induction ns as [|n ns IH]; intros o; [reflexivity|].
  cbn [oemit_all_merge]. rewrite IH, erase_oemit_merge. reflexivity.
Qed.

Local Lemma erase_oset_cur : forall l o,
  erase_ostate (oset_cur l o) = oset_cur (erase_oitems l) (erase_ostate o).
Proof. intros l [out [|f stk] word]; [reflexivity|destruct f; reflexivity]. Qed.

Local Lemma erase_oword_reset : forall o,
  erase_ostate (oword_reset o) = oword_reset (erase_ostate o).
Proof. intros [out stk word]; reflexivity. Qed.

Local Lemma erase_remember_word_start : forall `{P : PosPolicy} `{C : InlineCursor} c o,
  erase_ostate (@remember_word_start P C c o) = erase_ostate o.
Proof.
  intros P C c [out stk word]. unfold remember_word_start.
  destruct (pos_records && is_ws c)%bool; reflexivity.
Qed.

Local Lemma erase_flush_text_at : forall `{P : PosPolicy} `{C : InlineCursor} txt o,
  erase_ostate (@flush_text_at P C txt o) = flush_text txt (erase_ostate o).
Proof.
  intros P C txt o. unfold flush_text; unfold flush_text_at.
  destruct (nonempty_str txt); [|reflexivity].
  rewrite erase_oemit, erase_imk. reflexivity.
Qed.

Local Lemma erase_flush_text_to_at :
  forall `{P : PosPolicy} `{C : InlineCursor} stop txt o,
  erase_ostate (@flush_text_to_at P C stop txt o) =
  flush_text txt (erase_ostate o).
Proof.
  intros P C stop txt o. unfold flush_text; unfold flush_text_to_at, flush_text_at.
  destruct (nonempty_str txt); [|reflexivity].
  rewrite !erase_oemit, !erase_imk. reflexivity.
Qed.

Local Lemma erase_opush_at : forall k m cm open o,
  erase_ostate (opush_at k m cm open o) =
  opush_at k m cm null_span (erase_ostate o).
Proof. intros k m cm open [out stk word]; reflexivity. Qed.

Local Lemma erase_opush : forall `{P : PosPolicy} `{C : InlineCursor} k m o,
  erase_ostate (@opush T P C k m o) =
  @opush T semantic_pos semantic_inline_cursor k m (erase_ostate o).
Proof.
  intros P C k m o. unfold opush, dtoken_span, pspan.
  rewrite erase_opush_at. destruct (@pos_records P); reflexivity.
Qed.

Local Lemma erase_bpush : forall `{P : PosPolicy} `{C : InlineCursor} image o,
  erase_ostate (@bpush P C image o) =
  @bpush semantic_pos semantic_inline_cursor image (erase_ostate o).
Proof.
  intros P C image [out stk word]. unfold bpush, pspan.
  destruct (@pos_records P); reflexivity.
Qed.

Local Lemma erase_dpush : forall image open o,
  erase_ostate (dpush image open o) =
  dpush image null_span (erase_ostate o).
Proof. intros image open [out stk word]; reflexivity. Qed.

Local Lemma erase_isnoc : forall n l,
  Erase.of_inlines (isnoc n l) = isnoc (Erase.inode n) (Erase.of_inlines l).
Proof.
  intros n [|m l]; [reflexivity|].
  destruct m as [q [|lv b'] u]; try reflexivity;
    destruct u; try reflexivity;
    destruct n as [p [|kv a'] v]; try reflexivity;
    destruct v; reflexivity.
Qed.

Local Lemma erase_fr_src : forall f, fr_src (erase_frame f) = fr_src f.
Proof. intros [k m open out]; destruct k; reflexivity. Qed.

Local Lemma erase_fr_lit : forall `{P : PosPolicy} f,
  @fr_lit T semantic_pos (erase_frame f) = Erase.inode (@fr_lit T P f).
Proof.
  intros P f. unfold fr_lit. rewrite erase_imk, erase_fr_src. reflexivity.
Qed.

Local Lemma erase_nonempty : forall l, nonempty (erase_oitems l) = nonempty l.
Proof. intros [|i l]; reflexivity. Qed.

Local Lemma erase_dmatch : forall k m f, dmatch k m (erase_frame f) = dmatch k m f.
Proof. intros k m [[?|?|?] ? ? ?]; reflexivity. Qed.

Local Lemma erase_fr_barrier : forall f, fr_barrier (erase_frame f) = fr_barrier f.
Proof. intros [[?|?|?] ? ? ?]; reflexivity. Qed.

Local Lemma erase_istarts_str : forall l,
  istarts_str (Erase.of_inlines l) = istarts_str l.
Proof.
  intros [|[p [|kv a] v] l]; try reflexivity; destruct v; reflexivity.
Qed.

Local Lemma erase_oattach_list : forall `{P : PosPolicy} a spec w out,
  Erase.of_inlines (@oattach_list P a spec w out) =
  @oattach_list semantic_pos a null_span None (Erase.of_inlines out).
Proof.
  intros P a spec w [|[p a' v] out]; [reflexivity|].
  destruct v;
    try (destruct a' as [|kv a'];
         cbn [Erase.of_inlines Erase.inode oattach_list];
         rewrite ?erase_add_inline_role; reflexivity).
  destruct a' as [|kv a'];
    [|cbn [Erase.of_inlines Erase.inode oattach_list];
      rewrite erase_add_inline_role; reflexivity].
  cbn [Erase.of_inlines Erase.inode Erase.of_inline oattach_list].
  destruct (last_ws_split s) as [pre w0].
  destruct (nonempty_str w0); [|reflexivity].
  destruct a as [|kv a]; [reflexivity|].
  destruct (split_text_pos p w) as [pp wp]. cbn [split_text_pos].
  rewrite erase_isnoc, erase_add_inline_role. cbn [Erase.inode].
  destruct (nonempty_str pre); [rewrite erase_isnoc|]; reflexivity.
Qed.

(* Erasure commutes with resolution for the same reason it commutes with
   `oattach_list`: the pass moves attributes and a spec's range, and the
   range is what erasure drops. *)
Local Lemma erase_oresolve_go : forall `{P : PosPolicy} l,
  @oresolve_go semantic_pos (erase_oitems l) =
  (Erase.of_inlines (fst (@oresolve_go P l)), snd (@oresolve_go P l)).
Proof.
  intros P. induction l as [|[n|a spec w] l IH]; [reflexivity| |];
    cbn [erase_oitems erase_oitem oresolve_go];
    rewrite IH; destruct (@oresolve_go P l) as [out m]; cbn [fst snd].
  - destruct m; [rewrite erase_isnoc|]; reflexivity.
  - rewrite <- (erase_istarts_str (@oattach_list P a spec w out)).
    rewrite erase_oattach_list. reflexivity.
Qed.

Local Lemma erase_oresolve : forall `{P : PosPolicy} l,
  Erase.of_inlines (@oresolve P l) = @oresolve semantic_pos (erase_oitems l).
Proof.
  intros P l. unfold oresolve. rewrite erase_oresolve_go. reflexivity.
Qed.

Local Lemma erase_oclose_go : forall `{P : PosPolicy} k m pend stk,
  @oclose_go T semantic_pos k m (erase_oitems pend) (map erase_frame stk) =
  match @oclose_go T P k m pend stk with
  | None => None
  | Some (content, open, rest) =>
      Some (erase_oitems content, null_span, map erase_frame rest)
  end.
Proof.
  intros P k m pend stk. revert pend.
  induction stk as [|f stk IH]; intros pend; [reflexivity|].
  cbn [map oclose_go]. rewrite erase_dmatch, erase_fr_barrier.
  change (fr_out (erase_frame f)) with (erase_oitems (fr_out f)).
  rewrite <- erase_oapp.
  destruct (dmatch k m f).
  - rewrite erase_nonempty.
    destruct (nonempty (oapp pend (fr_out f)));
      cbn [erase_frame fr_open]; reflexivity.
  - destruct (fr_barrier f); [reflexivity|].
    rewrite (erase_fr_lit f).
    specialize (IH (oapp (oapp pend (fr_out f)) [OIn (@fr_lit T P f)])).
    rewrite !erase_oapp in IH. cbn [erase_oitems erase_oitem] in IH.
    rewrite <- erase_oapp in IH. exact IH.
Qed.

Local Lemma erase_dnode : forall k ns,
  Erase.of_inline (dnode k ns) = dnode k (Erase.of_inlines ns).
Proof.
  intros k ns. destruct k; cbn [dnode Erase.of_inline];
    rewrite Erase.inline_children; reflexivity.
Qed.

Local Lemma erase_bnode : forall image ns tgt,
  Erase.of_inline (bnode image ns tgt) = bnode image (Erase.of_inlines ns) tgt.
Proof.
  intros image ns tgt. destruct image; cbn [bnode Erase.of_inline];
    rewrite Erase.inline_children; reflexivity.
Qed.

Local Lemma erase_span_node : forall ns,
  Erase.of_inline (Span ns) = Span (Erase.of_inlines ns).
Proof.
  intros ns. cbn [Erase.of_inline]. rewrite Erase.inline_children. reflexivity.
Qed.

(* An empty reference's label is the string content of its first
   bracket, which is payload and so survives erasure. *)
Local Lemma erase_reference_text : forall i,
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

Local Lemma erase_reference_inlines_text : forall ns,
  reference_inlines_text (Erase.of_inlines ns) = reference_inlines_text ns.
Proof.
  intros ns. unfold reference_inlines_text. f_equal.
  rewrite Erase.inlines_map, map_map. apply map_ext.
  intros [p a x]; cbn [node_contents Erase.inode]. apply erase_reference_text.
Qed.

Local Lemma erase_auto_node : forall s, Erase.of_inline (auto_node s) = auto_node s.
Proof. intros s. unfold auto_node. destruct (auto_email s); reflexivity. Qed.

Local Lemma erase_vnode : forall vk s, Erase.of_inline (vnode vk s) = vnode vk s.
Proof. intros [|st] s; reflexivity. Qed.

Local Lemma erase_oclose : forall `{P : PosPolicy} k m stop o,
  sclose k m (erase_ostate o) =
  option_map erase_ostate (@oclose T P k m stop o).
Proof.
  intros P k m stop o. unfold sclose, oclose.
  change (os_stk (erase_ostate o)) with (map erase_frame (os_stk o)).
  change (@nil oitem) with (erase_oitems []) at 1.
  rewrite erase_oclose_go.
  destruct (@oclose_go T P k m [] (os_stk o)) as [[[content open] rest]|];
    [|reflexivity].
  cbn [option_map].
  rewrite erase_oemit, erase_imk, erase_dnode, Erase.inlines_rev,
    erase_oresolve.
  destruct o as [out stk word]; reflexivity.
Qed.

Local Lemma erase_bclose_go : forall `{P : PosPolicy} pend stk,
  @bclose_go T semantic_pos (erase_oitems pend) (map erase_frame stk) =
  match @bclose_go T P pend stk with
  | None => None
  | Some (content, image, open, rest) =>
      Some (erase_oitems content, image, null_span, map erase_frame rest)
  end.
Proof.
  intros P pend stk. revert pend.
  induction stk as [|f stk IH]; intros pend; [reflexivity|].
  cbn [map bclose_go].
  change (fr_kind (erase_frame f)) with (fr_kind f).
  change (fr_out (erase_frame f)) with (erase_oitems (fr_out f)).
  rewrite <- erase_oapp.
  destruct (fr_kind f) eqn:Ek; [| |reflexivity].
  - rewrite (erase_fr_lit f).
    specialize (IH (oapp (oapp pend (fr_out f)) [OIn (@fr_lit T P f)])).
    rewrite !erase_oapp in IH. cbn [erase_oitems erase_oitem] in IH.
    rewrite <- erase_oapp in IH. exact IH.
  - cbn [erase_frame fr_open]. reflexivity.
Qed.

Local Lemma erase_bclose : forall `{P : PosPolicy} o,
  @bclose T semantic_pos (erase_ostate o) =
  match @bclose T P o with
  | None => None
  | Some (kids, image, open, o') =>
      Some (Erase.of_inlines kids, image, null_span, erase_ostate o')
  end.
Proof.
  intros P o. unfold bclose.
  change (os_stk (erase_ostate o)) with (map erase_frame (os_stk o)).
  change (@nil oitem) with (erase_oitems []) at 1.
  rewrite erase_bclose_go.
  destruct (@bclose_go T P [] (os_stk o)) as [[[[content image] open] rest]|];
    [|reflexivity].
  rewrite <- erase_oresolve, <- Erase.inlines_rev.
  destruct o as [out stk word]; reflexivity.
Qed.

Local Lemma erase_bunpush : forall o,
  bunpush (erase_ostate o) =
  match bunpush o with
  | None => None
  | Some (image, open, o') => Some (image, null_span, erase_ostate o')
  end.
Proof.
  intros [out [|[[image| |] marked open [|i l]] stk] word]; reflexivity.
Qed.

Local Lemma erase_opop_str : forall o,
  opop_str (erase_ostate o) =
  (fst (opop_str o), erase_ostate (snd (opop_str o))).
Proof.
  intros [out [|f stk] word].
  - destruct out as [|[[p a v]|b sp w] out]; try reflexivity.
    destruct a as [|kv a]; [destruct v; reflexivity|reflexivity].
  - destruct f as [k marked open [|[[p a v]|b sp w] l]]; try reflexivity.
    destruct a as [|kv a]; [destruct v; reflexivity|reflexivity].
Qed.

Local Lemma erase_bflat : forall `{P : PosPolicy} `{C : InlineCursor} kids txt o,
  @bflat semantic_pos semantic_inline_cursor (Erase.of_inlines kids) txt
    (erase_ostate o)
  = (fst (@bflat P C kids txt o), erase_ostate (snd (@bflat P C kids txt o))).
Proof.
  intros P C kids. induction kids as [|[p a x] kids IH]; intros txt o;
    [reflexivity|].
  rewrite Erase.inlines_cons. unfold Erase.inode at 1.
  destruct a as [|kv a];
    [destruct x; try (cbn [Erase.of_inline bflat]; apply IH)|];
    cbn [bflat]; sem_flush;
    rewrite <- erase_flush_text_at, (erase_oemit_node p); apply IH.
Qed.

Local Lemma erase_bsplit_nl : forall `{P : PosPolicy} `{C : InlineCursor} s txt o,
  @bsplit_nl semantic_pos semantic_inline_cursor s txt (erase_ostate o)
  = (fst (@bsplit_nl P C s txt o),
     erase_ostate (snd (@bsplit_nl P C s txt o))).
Proof.
  intros P C s. induction s as [|c s IH]; intros txt o; [reflexivity|].
  cbn [bsplit_nl]. destruct (Ascii.eqb c nl_char); [|apply IH].
  sem_flush. rewrite <- erase_flush_text_at.
  change (@imk_here semantic_pos semantic_inline_cursor SoftBreak)
    with (@imk_here semantic_pos semantic_inline_cursor
            (Erase.of_inline SoftBreak)).
  rewrite <- erase_imk_here, <- erase_oemit. apply IH.
Qed.

Local Lemma erase_oclose_barred : forall k m o,
  oclose_barred k m (erase_ostate o) = oclose_barred k m o.
Proof.
  intros k m o. unfold oclose_barred.
  change (os_stk (erase_ostate o)) with (map erase_frame (os_stk o)).
  generalize false. generalize (os_stk o) as stk.
  induction stk as [|f stk IH]; intros past; [reflexivity|].
  cbn [map oclose_barred_go]. rewrite erase_dmatch, erase_fr_barrier.
  destruct (dmatch k m f); [reflexivity|apply IH].
Qed.

Local Lemma erase_bclosed_lit : forall `{P : PosPolicy} `{C : InlineCursor}
  kids image o,
  @bclosed_lit semantic_pos semantic_inline_cursor (Erase.of_inlines kids) image
    (erase_ostate o)
  = (fst (@bclosed_lit P C kids image o),
     erase_ostate (snd (@bclosed_lit P C kids image o))).
Proof.
  intros P C kids image o. unfold bclosed_lit.
  rewrite erase_opop_str.
  destruct (opop_str o) as [pre o1]; cbn [fst snd].
  rewrite erase_bflat.
  destruct (@bflat P C kids (pre ++ bracket_open image) o1) as [txt o2];
    reflexivity.
Qed.

Local Lemma erase_bspan_lit : forall `{P : PosPolicy} `{C : InlineCursor}
  kids image src o,
  @bspan_lit semantic_pos semantic_inline_cursor (Erase.of_inlines kids) image
    src (erase_ostate o)
  = (fst (@bspan_lit P C kids image src o),
     erase_ostate (snd (@bspan_lit P C kids image src o))).
Proof.
  intros P C kids image src o. unfold bspan_lit.
  rewrite erase_bclosed_lit.
  destruct (@bclosed_lit P C kids image o) as [txt o']; cbn [fst snd].
  apply erase_bsplit_nl.
Qed.

Local Lemma erase_battr_lit : forall `{P : PosPolicy} `{C : InlineCursor} src txt o,
  @battr_lit semantic_pos semantic_inline_cursor src txt (erase_ostate o)
  = (fst (@battr_lit P C src txt o),
     erase_ostate (snd (@battr_lit P C src txt o))).
Proof. intros P C src txt o. apply erase_bsplit_nl. Qed.

Local Lemma erase_bref_lit : forall `{P : PosPolicy} `{C : InlineCursor}
  kids image label o,
  @bref_lit semantic_pos semantic_inline_cursor (Erase.of_inlines kids) image
    label (erase_ostate o)
  = (fst (@bref_lit P C kids image label o),
     erase_ostate (snd (@bref_lit P C kids image label o))).
Proof.
  intros P C kids image label o. unfold bref_lit.
  rewrite erase_bclosed_lit.
  destruct (@bclosed_lit P C kids image o) as [txt o']; reflexivity.
Qed.

Local Lemma erase_bnote_lit : forall `{P : PosPolicy} `{C : InlineCursor}
  esc image label o,
  @bnote_lit semantic_pos semantic_inline_cursor esc image label
    (erase_ostate o)
  = (fst (@bnote_lit P C esc image label o),
     erase_ostate (snd (@bnote_lit P C esc image label o))).
Proof.
  intros P C esc image label o. unfold bnote_lit.
  rewrite erase_opop_str.
  destruct (opop_str o) as [pre o1]; reflexivity.
Qed.

Local Lemma erase_ospan_bang : forall `{P : PosPolicy} `{C : InlineCursor} image o,
  erase_ostate (@ospan_bang P C image o) =
  @ospan_bang semantic_pos semantic_inline_cursor image (erase_ostate o).
Proof.
  intros P C image o. unfold ospan_bang. destruct image; [|reflexivity].
  rewrite erase_opop_str. destruct (opop_str o) as [pre o1]; cbn [fst snd].
  apply erase_flush_text_at.
Qed.

Local Lemma erase_ilead : forall `{P : PosPolicy} `{C : InlineCursor} c txt prev o,
  erase_iscan (@ilead T P C c txt prev o) =
  @ilead T semantic_pos semantic_inline_cursor c txt prev (erase_ostate o).
Proof.
  intros P C c txt prev o. unfold ilead.
  destruct (is_bslash c); [reflexivity|].
  destruct (is_tick c);
    [cbn [erase_iscan]; rewrite erase_flush_text_at; reflexivity|].
  destruct (Ascii.eqb c dollar); [reflexivity|].
  destruct (Ascii.eqb c period); [reflexivity|].
  destruct (Ascii.eqb c hyphen); [reflexivity|].
  destruct (Ascii.eqb c lbrace); [reflexivity|].
  destruct (Ascii.eqb c bang); [reflexivity|].
  destruct (Ascii.eqb c lt); [reflexivity|].
  destruct (Ascii.eqb c ":"%char);
    [cbn [erase_iscan]; rewrite erase_remember_word_start; reflexivity|].
  destruct (Ascii.eqb c lbrack).
  { destruct (note_pos txt prev && wikilinks_enabled)%bool;
      [rewrite erase_bunpush; destruct (bunpush o) as [[[image open] o']|];
        [reflexivity|]|];
      cbn [erase_iscan]; rewrite erase_bpush, erase_flush_text_at; reflexivity. }
  destruct (Ascii.eqb c rbrack); [reflexivity|].
  destruct (Ascii.eqb c hat && note_pos txt prev && notes_enabled)%bool;
    [rewrite erase_bunpush; destruct (bunpush o) as [[[image open] o']|];
      [reflexivity|]|];
    destruct (dstyle_of c); cbn [erase_iscan];
    rewrite ?erase_remember_word_start; reflexivity.
Qed.

Local Lemma erase_idest_open : forall `{P : PosPolicy} `{C : InlineCursor}
  kids image open o,
  erase_iscan (@idest_open P C kids image open o) =
  @idest_open semantic_pos semantic_inline_cursor (Erase.of_inlines kids) image
    null_span (erase_ostate o).
Proof.
  intros P C kids image open o. unfold idest_open.
  rewrite <- (erase_dpush image open), erase_bflat.
  destruct (@bflat P C kids EmptyString (dpush image open o)) as [txt o'];
    reflexivity.
Qed.

Local Lemma erase_oopen_marked : forall `{P : PosPolicy} `{C : InlineCursor}
  k cm txt o,
  erase_ostate (@oopen_marked T P C k cm txt o) =
  @oopen_marked T semantic_pos semantic_inline_cursor k cm txt (erase_ostate o).
Proof.
  intros P C k cm txt o. unfold oopen_marked.
  rewrite erase_opush_at, erase_flush_text_to_at.
  unfold dtoken_span, pspan. destruct (@pos_records P); reflexivity.
Qed.

Local Lemma erase_idelim_open_marked : forall `{P : PosPolicy} `{C : InlineCursor}
  k cm txt o,
  erase_iscan (@idelim_open_marked T P C k cm txt o) =
  @idelim_open_marked T semantic_pos semantic_inline_cursor k cm txt
    (erase_ostate o).
Proof.
  intros P C k cm txt o. unfold idelim_open_marked.
  cbn [erase_iscan]. rewrite erase_oopen_marked. reflexivity.
Qed.

Local Lemma erase_islice_end : forall st,
  erase_iscan (islice_end st) = islice_end (erase_iscan st).
Proof.
  induction st; cbn [erase_iscan islice_end];
    try reflexivity; try (destruct esc; reflexivity).
  exact IHst.
Qed.

Local Lemma erase_iattr_mark : forall `{P : PosPolicy} `{C : InlineCursor}
  src a txt o,
  erase_iscan (@iattr_mark P C src a txt o) =
  @iattr_mark semantic_pos semantic_inline_cursor src a txt (erase_ostate o).
Proof.
  intros P C src a txt o. unfold iattr_mark.
  cbn [erase_iscan]. rewrite erase_omark,
    (erase_flush_text_to_at (spot_before cursor_start (String lbrace src))).
  unfold pspan. destruct (@pos_records P); reflexivity.
Qed.

Local Lemma erase_iattr_feed : forall `{P : PosPolicy} `{C : InlineCursor}
  c p src txt prev sh o,
  erase_iscan (@iattr_feed T P C c p src txt prev sh o) =
  @iattr_feed T semantic_pos semantic_inline_cursor c p src txt prev
    (erase_iscan sh) (erase_ostate o).
Proof.
  intros P C c p src txt prev sh o. unfold iattr_feed.
  destruct (ap_failed (astep p c)); [reflexivity|].
  destruct (ap_done (astep p c)); [apply erase_iattr_mark|].
  cbn [erase_iscan]. rewrite erase_islice_end. reflexivity.
Qed.

Local Lemma erase_ibrace_step_at : forall `{P : PosPolicy} `{C : InlineCursor}
  allow c txt prev o,
  erase_iscan (@ibrace_step_at T P C allow c txt prev o) =
  @ibrace_step_at T semantic_pos semantic_inline_cursor allow c txt prev
    (erase_ostate o).
Proof.
  intros P C allow c txt prev o. unfold ibrace_step_at.
  destruct (dstyle_of c) as [k|]; [reflexivity|].
  destruct allow.
  - rewrite erase_iattr_feed, erase_ilead. reflexivity.
  - rewrite erase_battr_lit.
    destruct (@battr_lit P C EmptyString txt o) as [t o']; cbn [fst snd].
    apply erase_ilead.
Qed.

Local Lemma erase_ibang_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c txt prev o,
  erase_iscan (@ibang_step T P C c txt prev o) =
  @ibang_step T semantic_pos semantic_inline_cursor c txt prev (erase_ostate o).
Proof.
  intros P C c txt prev o. unfold ibang_step.
  destruct (Ascii.eqb c lbrack); [|apply erase_ilead].
  cbn [erase_iscan]. rewrite erase_bpush, erase_flush_text_to_at. reflexivity.
Qed.

Local Lemma erase_idelim_done : forall `{P : PosPolicy} `{C : InlineCursor}
  k txt before marker next o,
  erase_iscan (@idelim_done T P C k txt before marker next o) =
  @idelim_done T semantic_pos semantic_inline_cursor k txt before marker next
    (erase_ostate o).
Proof.
  intros P C k txt before marker next o. unfold idelim_done.
  destruct (dbare k before && negb marker && nonspace_at next)%bool;
    [|reflexivity].
  cbn [erase_iscan]. rewrite erase_opush, erase_flush_text_to_at. reflexivity.
Qed.

Local Lemma erase_idelim_resolve : forall `{P : PosPolicy} `{C : InlineCursor}
  k txt before marker next o,
  erase_iscan (@idelim_resolve T P C k txt before marker next o) =
  @idelim_resolve T semantic_pos semantic_inline_cursor k txt before marker next
    (erase_ostate o).
Proof.
  intros P C k txt before marker next o. unfold idelim_resolve.
  destruct (nonspace_at before || marker)%bool; [|apply erase_idelim_done].
  sem_flush.
  rewrite <- (erase_flush_text_to_at
                (span_start (@dtoken_span T P C k false)) txt o).
  rewrite (erase_oclose k marker
             (if marker then cursor_stop else cursor_start)).
  destruct (@oclose T P k marker _ _) as [o'|]; cbn [option_map].
  - reflexivity.
  - rewrite erase_oclose_barred. destruct (oclose_barred k marker o);
      [reflexivity|apply erase_idelim_done].
Qed.

Local Lemma erase_idollar_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c two txt prev o,
  erase_iscan (@idollar_step T P C c two txt prev o) =
  @idollar_step T semantic_pos semantic_inline_cursor c two txt prev
    (erase_ostate o).
Proof.
  intros P C c two txt prev o. unfold idollar_step.
  destruct (Ascii.eqb c dollar); [destruct two; reflexivity|].
  destruct (is_tick c && math_enabled)%bool; [|apply erase_ilead].
  cbn [erase_iscan]. rewrite erase_flush_text_to_at. reflexivity.
Qed.

Local Lemma erase_iperiod_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c two txt prev o,
  erase_iscan (@iperiod_step T P C c two txt prev o) =
  @iperiod_step T semantic_pos semantic_inline_cursor c two txt prev
    (erase_ostate o).
Proof.
  intros P C c two txt prev o. unfold iperiod_step.
  destruct (Ascii.eqb c period); [destruct two; reflexivity|apply erase_ilead].
Qed.

Local Lemma erase_idash_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c n txt prev o,
  erase_iscan (@idash_step T P C c n txt prev o) =
  @idash_step T semantic_pos semantic_inline_cursor c n txt prev
    (erase_ostate o).
Proof.
  intros P C c n txt prev o. unfold idash_step.
  destruct (Ascii.eqb c hyphen); [reflexivity|].
  destruct (Ascii.eqb c rbrace); [|apply erase_ilead].
  destruct (dstyle_of hyphen) as [k|]; [|reflexivity].
  destruct (Nat.leb (dwidth k) n); [apply erase_idelim_resolve|reflexivity].
Qed.

Local Lemma erase_iresolve : forall `{P : PosPolicy} `{C : InlineCursor} st,
  erase_iscan (@iresolve T P C st) =
  @iresolve T semantic_pos semantic_inline_cursor (erase_iscan st).
Proof.
  intros P C [| | |k extra txt before marked o| | | | | | | | | | | | | | | |];
    try reflexivity.
  cbn [erase_iscan iresolve].
  destruct (Nat.ltb (S extra) (dwidth k)); [reflexivity|].
  destruct marked;
    [apply erase_idelim_open_marked|apply erase_idelim_resolve].
Qed.

Local Lemma erase_iescws_resolve : forall `{P : PosPolicy} `{C : InlineCursor}
  ws txt prev o,
  let '(t, pv, o') := @iescws_resolve P C ws txt prev o in
  @iescws_resolve semantic_pos semantic_inline_cursor ws txt prev
    (erase_ostate o) = (t, pv, erase_ostate o').
Proof.
  intros P C [|c rest] txt prev o; [reflexivity|].
  cbn [iescws_resolve]. destruct (Ascii.eqb c " "%char); [|reflexivity].
  rewrite erase_oemit, erase_imk, erase_flush_text_to_at. reflexivity.
Qed.

Local Lemma erase_iesc_hard : forall `{P : PosPolicy} `{C : InlineCursor} ws txt o,
  erase_ostate (@iesc_hard P C ws txt o) =
  @iesc_hard semantic_pos semantic_inline_cursor ws txt (erase_ostate o).
Proof.
  intros P C ws txt o. unfold iesc_hard.
  rewrite erase_oemit, erase_flush_text_to_at, erase_imk_here. reflexivity.
Qed.

Local Lemma erase_ispan_feed : forall `{P : PosPolicy} `{C : InlineCursor}
  c kids image open p src o,
  erase_iscan (@ispan_feed T P C c kids image open p src o) =
  @ispan_feed T semantic_pos semantic_inline_cursor c (Erase.of_inlines kids) image
    null_span p src (erase_ostate o).
Proof.
  intros P C c kids image open p src o. unfold ispan_feed.
  destruct (ap_failed (astep p c)).
  - rewrite erase_bspan_lit.
    destruct (@bspan_lit P C kids image src o) as [txt o']; cbn [fst snd].
    apply erase_ilead.
  - destruct (ap_done (astep p c)); [|reflexivity].
    cbn [erase_iscan]. rewrite erase_oemit, erase_add_inline_role,
      erase_ospan_bang.
    cbn [Erase.inode]. rewrite erase_span_node. reflexivity.
Qed.

Local Lemma erase_inote_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c esc image label open o,
  erase_iscan (@inote_step P C c esc image label open o) =
  @inote_step semantic_pos semantic_inline_cursor c esc image label null_span
    (erase_ostate o).
Proof.
  intros P C c esc image label open o. unfold inote_step.
  destruct esc; [reflexivity|].
  destruct (is_bslash c); [reflexivity|].
  destruct (Ascii.eqb c rbrack); [|reflexivity].
  cbn [erase_iscan]. rewrite erase_oemit, erase_imk, erase_ospan_bang.
  reflexivity.
Qed.

Local Lemma erase_bwiki_lit : forall esc rb image region o,
  bwiki_lit esc rb image region (erase_ostate o) =
  (fst (bwiki_lit esc rb image region o),
   erase_ostate (snd (bwiki_lit esc rb image region o))).
Proof.
  intros esc rb image region o. unfold bwiki_lit.
  rewrite erase_opop_str. destruct (opop_str o) as [pre o1]; reflexivity.
Qed.

Local Lemma erase_iwiki_close : forall `{P : PosPolicy} `{C : InlineCursor}
  image region open o,
  erase_iscan (@iwiki_close P C image region open o) =
  @iwiki_close semantic_pos semantic_inline_cursor image region null_span
    (erase_ostate o).
Proof.
  intros P C image region open o. unfold iwiki_close.
  destruct (wiki_split region) as [[|x t] al].
  - rewrite erase_bwiki_lit.
    destruct (bwiki_lit false true image region o) as [txt o']; reflexivity.
  - cbn [erase_iscan]. rewrite erase_oemit, erase_imk. reflexivity.
Qed.

Local Lemma erase_iwiki_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c esc rb image region open o,
  erase_iscan (@iwiki_step P C c esc rb image region open o) =
  @iwiki_step semantic_pos semantic_inline_cursor c esc rb image region
    null_span (erase_ostate o).
Proof.
  intros P C c esc rb image region open o. unfold iwiki_step.
  destruct esc; [reflexivity|].
  destruct (rb && Ascii.eqb c rbrack)%bool; [apply erase_iwiki_close|].
  destruct (is_bslash c); [reflexivity|].
  destruct (Ascii.eqb c rbrack); reflexivity.
Qed.

Local Lemma erase_iauto_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c src txt o,
  erase_iscan (@iauto_step T P C c src txt o) =
  @iauto_step T semantic_pos semantic_inline_cursor c src txt (erase_ostate o).
Proof.
  intros P C c src txt o. unfold iauto_step.
  destruct (Ascii.eqb c gt && auto_body_ok src && auto_kind_ok src)%bool.
  - cbn [erase_iscan]. rewrite erase_oemit, erase_imk, erase_auto_node,
      erase_flush_text_to_at. reflexivity.
  - destruct (Ascii.eqb c gt || is_ws c || Ascii.eqb c lt)%bool;
      [apply erase_ilead|reflexivity].
Qed.

Local Lemma erase_iraw_step_at : forall `{P : PosPolicy} `{C : InlineCursor}
  allow c spec txt o,
  erase_iscan (@iraw_step_at T P C allow c spec txt o) =
  @iraw_step_at T semantic_pos semantic_inline_cursor allow c spec txt
    (erase_ostate o).
Proof.
  intros P C allow c spec txt o. unfold iraw_step_at.
  destruct (Ascii.eqb c rbrace && raw_spec_ok spec)%bool.
  - destruct raw_inline_enabled.
    + cbn [erase_iscan]. rewrite erase_oemit, erase_imk. reflexivity.
    + rewrite erase_ilead, erase_oemit, erase_imk. reflexivity.
  - destruct (match spec with
              | EmptyString => negb (Ascii.eqb c eqchar)
              | _ => (Ascii.eqb c rbrace || raw_stop c)%bool
              end);
      [|reflexivity].
    destruct spec as [|d spec];
      [rewrite erase_ibrace_step_at|rewrite erase_ilead];
      rewrite erase_oemit, erase_imk; reflexivity.
Qed.

Local Lemma erase_isymbol_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c alias txt o sh,
  erase_iscan (@isymbol_step P C c alias txt o sh) =
  @isymbol_step semantic_pos semantic_inline_cursor c alias txt
    (erase_ostate o) (erase_iscan sh).
Proof.
  intros P C c alias txt o sh. unfold isymbol_step.
  destruct (symbol_char c); [reflexivity|].
  destruct (Ascii.eqb c ":"%char && nonempty_str alias)%bool;
    [|reflexivity].
  cbn [erase_iscan]. rewrite erase_oemit, erase_imk,
    erase_flush_text_to_at. reflexivity.
Qed.

Local Lemma erase_iscan_attr : forall ap src txt prev sh o,
  erase_iscan (IAttr ap src txt prev sh o) =
  IAttr ap src txt prev (erase_iscan sh) (erase_ostate o).
Proof. reflexivity. Qed.

Local Lemma erase_iscan_dest : forall kids image open esc depth dst sh o,
  erase_iscan (IDest kids image open esc depth dst sh o) =
  IDest (Erase.of_inlines kids) image null_span esc depth dst
    (erase_iscan sh) (erase_ostate o).
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
Theorem erase_istep_at :
  forall `{P : PosPolicy} `{C : InlineCursor} allow c st,
  erase_iscan (@istep_at T P C allow c st) =
  @istep_at T semantic_pos semantic_inline_cursor allow c (erase_iscan st).
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
    destruct esc; cbn [erase_iscan istep_at].
    + destruct (is_ws c); reflexivity.
    + apply erase_ilead.
  - (* IEscWs *)
    cbn [erase_iscan istep_at]. destruct (is_ws c); [reflexivity|].
    pose proof (erase_iescws_resolve (P:=P) (C:=C) ws txt prev o) as H.
    destruct (@iescws_resolve P C ws txt prev o) as [[t pv] o'].
    rewrite H. apply erase_ilead.
  - (* IBrace *) apply erase_ibrace_step_at.
  - (* IDelim *)
    cbn [erase_iscan istep_at].
    destruct (Nat.ltb (S extra) (dwidth k)).
    { destruct (Ascii.eqb c (dchar k));
        [destruct marked; reflexivity|apply erase_ilead]. }
    destruct marked.
    { rewrite erase_ilead, erase_oopen_marked. reflexivity. }
    pose proof (erase_idelim_resolve (P:=P) (C:=C) k txt before
                  (Ascii.eqb c rbrace) (Some c) o) as Hr.
    destruct (Ascii.eqb c rbrace); [exact Hr|].
    rewrite <- Hr.
    destruct (@idelim_resolve T P C k txt before false (Some c) o)
      as [esc' txt' prev' o'| | | | | | | | | | | | | | | | | | |];
      try reflexivity.
    destruct esc'; [reflexivity|apply erase_ilead].
  - (* IOpen *)
    cbn [erase_iscan istep_at]. destruct (is_tick c); reflexivity.
  - (* IVerb *)
    cbn [erase_iscan istep_at]. destruct (is_tick c); [reflexivity|].
    destruct (Nat.eqb run n); [|reflexivity].
    destruct (Ascii.eqb c lbrace && vkind_verb vk)%bool; [reflexivity|].
    rewrite erase_ilead, erase_oemit, erase_imk, erase_vnode. reflexivity.
  - (* IDollar *) apply erase_idollar_step.
  - (* IPeriod *) apply erase_iperiod_step.
  - (* IDash *) apply erase_idash_step.
  - (* IBang *) apply erase_ibang_step.
  - (* IClosed *)
    cbn [erase_iscan istep_at].
    destruct (Ascii.eqb c lparen || Ascii.eqb c lbrack
              || (Ascii.eqb c lbrace && allow))%bool;
      [|apply erase_ilead].
    sem_flush.
    rewrite <- (erase_flush_text_to_at (previous_spot cursor_start) txt o).
    rewrite erase_bclose.
    destruct (@bclose T P (@flush_text_to_at P C
                (previous_spot cursor_start) txt o))
      as [[[[kids image] open] o']|]; [|apply erase_ilead].
    destruct (Ascii.eqb c lparen);
      [cbn [erase_iscan]; rewrite erase_idest_open; reflexivity|].
    destruct (Ascii.eqb c lbrack); reflexivity.
  - (* ISpan *) apply erase_ispan_feed.
  - (* IAttr *)
    rewrite erase_iscan_attr. cbn [istep_at].
    destruct (ap_failed (astep ap c)); [apply IHsh|].
    rewrite erase_iattr_feed, IHsh. reflexivity.
  - (* IReference *)
    cbn [erase_iscan istep_at]. destruct (Ascii.eqb c rbrack); [|reflexivity].
    cbn [erase_iscan]. rewrite erase_oemit, erase_imk, erase_bnode.
    destruct label; [rewrite erase_reference_inlines_text|]; reflexivity.
  - (* INote *) apply erase_inote_step.
  - (* IWiki *) apply erase_iwiki_step.
  - (* IDest *)
    rewrite erase_iscan_dest. destruct esc; cbn [istep_at].
    + rewrite erase_iscan_dest, IHsh. reflexivity.
    + destruct (is_bslash c);
        [rewrite erase_iscan_dest, IHsh; reflexivity|].
      destruct (Ascii.eqb c lparen);
        [rewrite erase_iscan_dest, IHsh; reflexivity|].
      destruct (Ascii.eqb c rparen);
        [|rewrite erase_iscan_dest, IHsh; reflexivity].
      destruct depth as [|d];
        [|rewrite erase_iscan_dest, IHsh; reflexivity].
      cbn [erase_iscan]. rewrite erase_oemit, erase_imk, erase_bnode.
      reflexivity.
  - (* IAuto *) apply erase_iauto_step.
  - (* ISymbol *)
    cbn [istep_at]. rewrite erase_isymbol_step, IHsh. reflexivity.
  - (* IRaw *) apply erase_iraw_step_at.
Qed.

Local Lemma erase_ifinish_ostate_flat : forall `{P : PosPolicy} `{C : InlineCursor} st,
  erase_ostate (@ifinish_ostate_flat P C st) =
  @ifinish_ostate_flat semantic_pos semantic_inline_cursor (erase_iscan st).
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
    cbn [erase_iscan ifinish_ostate_flat];
    try reflexivity.
  - destruct esc; [apply erase_iesc_hard|apply erase_flush_text_at].
  - apply erase_iesc_hard.
  - rewrite erase_oemit, erase_imk, erase_vnode. reflexivity.
  - rewrite erase_oemit, erase_imk, erase_vnode. reflexivity.
  - rewrite erase_bspan_lit.
    destruct (@bspan_lit P C kids image src o) as [t o']; cbn [fst snd].
    apply erase_flush_text_at.
  - rewrite erase_battr_lit.
    destruct (@battr_lit P C src txt o) as [t o']; cbn [fst snd].
    apply erase_flush_text_at.
  - rewrite erase_bref_lit.
    destruct (@bref_lit P C kids image label o) as [t o']; cbn [fst snd].
    apply erase_flush_text_at.
  - rewrite erase_bnote_lit.
    destruct (@bnote_lit P C esc image label o) as [t o']; cbn [fst snd].
    apply erase_flush_text_at.
  - rewrite erase_bwiki_lit.
    destruct (bwiki_lit esc rb image region o) as [t o']; cbn [fst snd].
    apply erase_flush_text_at.
  - apply erase_flush_text_at.
  - rewrite erase_flush_text_at, erase_oemit, erase_imk. reflexivity.
Qed.

Local Lemma erase_ifinish_ostate : forall `{P : PosPolicy} `{C : InlineCursor} st,
  erase_ostate (@ifinish_ostate T P C st) =
  @ifinish_ostate T semantic_pos semantic_inline_cursor (erase_iscan st).
Proof.
  intros P C st. induction st;
    try (cbn [ifinish_ostate];
         rewrite erase_ifinish_ostate_flat, erase_iresolve; reflexivity).
  - rewrite erase_iscan_attr. cbn [ifinish_ostate]. assumption.
  - rewrite erase_iscan_dest. cbn [ifinish_ostate]. assumption.
  - cbn [erase_iscan ifinish_ostate]. assumption.
Qed.

Local Lemma erase_oflatten : forall `{P : PosPolicy} pend stk bottom,
  erase_oitems (@oflatten T P pend stk bottom) =
  @oflatten T semantic_pos (erase_oitems pend) (map erase_frame stk)
    (erase_oitems bottom).
Proof.
  intros P pend stk. revert pend.
  induction stk as [|f stk IH]; intros pend bottom; [apply erase_oapp|].
  cbn [map oflatten].
  change (fr_out (erase_frame f)) with (erase_oitems (fr_out f)).
  rewrite (erase_fr_lit f), <- erase_oapp.
  specialize (IH (oapp (oapp pend (fr_out f)) [OIn (@fr_lit T P f)]) bottom).
  rewrite !erase_oapp in IH. cbn [erase_oitems erase_oitem] in IH.
  rewrite <- erase_oapp in IH. exact IH.
Qed.

Local Lemma erase_oitems_of : forall `{P : PosPolicy} o,
  erase_oitems (@oitems_of T P o) =
  @oitems_of T semantic_pos (erase_ostate o).
Proof.
  intros P o. unfold oitems_of.
  change (os_stk (erase_ostate o)) with (map erase_frame (os_stk o)).
  change (os_out (erase_ostate o)) with (erase_oitems (os_out o)).
  change (@nil oitem) with (erase_oitems []) at 1.
  apply erase_oflatten.
Qed.

Local Lemma erase_ofinish : forall `{P : PosPolicy} o,
  Erase.of_inlines (@ofinish T P o) = @ofinish T semantic_pos (erase_ostate o).
Proof.
  intros P o. unfold ofinish.
  rewrite erase_oresolve, erase_oitems_of. reflexivity.
Qed.

Local Lemma erase_ifinish : forall `{P : PosPolicy} `{C : InlineCursor} st,
  Erase.of_inlines (@ifinish T P C st) =
  @ifinish T semantic_pos semantic_inline_cursor (erase_iscan st).
Proof.
  intros P C st. unfold ifinish, ifinish_rev.
  rewrite Erase.inlines_rev, erase_ofinish, erase_ifinish_ostate. reflexivity.
Qed.

Local Lemma erase_ibreak_flat : forall `{P : PosPolicy} `{C : InlineCursor} st,
  erase_iscan (@ibreak_flat T P C st) =
  @ibreak_flat T semantic_pos semantic_inline_cursor (erase_iscan st).
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
    cbn [erase_iscan ibreak_flat];
    try reflexivity.
  - destruct esc; cbn [erase_iscan];
      rewrite erase_oword_reset;
      [rewrite erase_iesc_hard; reflexivity|].
    rewrite erase_oemit, erase_imk_here, erase_flush_text_at. reflexivity.
  - cbn [erase_iscan]. rewrite erase_oword_reset, erase_iesc_hard. reflexivity.
  - destruct (Nat.eqb run n); [|reflexivity].
    cbn [erase_iscan]. rewrite erase_oword_reset, erase_oemit, erase_imk_here,
      erase_oemit, erase_imk, erase_vnode. reflexivity.
  - apply erase_ispan_feed.
  - rewrite erase_iattr_feed. reflexivity.
  - rewrite erase_bwiki_lit.
    destruct (bwiki_lit esc rb image region o) as [t o']; cbn [fst snd erase_iscan].
    rewrite erase_oword_reset, erase_oemit, erase_imk_here,
      erase_flush_text_at. reflexivity.
  - cbn [erase_iscan]. rewrite erase_oword_reset, erase_oemit, erase_imk_here,
      erase_flush_text_at. reflexivity.
  - exact IHsh.
  - cbn [erase_iscan]. rewrite erase_oword_reset, erase_oemit, erase_imk_here,
      erase_flush_text_at, erase_oemit, erase_imk. reflexivity.
Qed.

Local Lemma erase_ibreak_at : forall `{P : PosPolicy} `{C : InlineCursor} allow st,
  erase_iscan (@ibreak_at T P C allow st) =
  @ibreak_at T semantic_pos semantic_inline_cursor allow (erase_iscan st).
Proof.
  intros P C allow st. revert allow. induction st; intros allow;
    try (cbn [ibreak_at];
         rewrite erase_ibreak_flat, erase_iresolve; reflexivity).
  - rewrite erase_iscan_attr. cbn [ibreak_at].
    rewrite erase_iattr_feed, IHst. reflexivity.
  - rewrite erase_iscan_dest. cbn [ibreak_at].
    rewrite erase_iscan_dest, IHst. reflexivity.
  - cbn [ibreak_at]. apply IHst.
Qed.

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
  erase_iscan (@iscan_str_located P allow k origin rem s st) =
  iscan_str_at allow s (erase_iscan st).
Proof.
  intros P allow k origin rem s. revert rem.
  induction s as [|c s IH]; intros rem st; [reflexivity|].
  cbn [iscan_str_located iscan_str_at]. rewrite IH, erase_istep_at.
  reflexivity.
Qed.

(* The driver's two step equations, so that a proof over a paragraph's
   lines rewrites rather than reduces: `cbn` unfolds the recursive call
   as well and loses the name. *)
Local Lemma iscan_lines_located_one : forall `{P : PosPolicy} off org k x st,
  @iscan_lines_located P off org [(k, x)] st =
  @iscan_str_located P (allow_attrs off) k org
    (String.length x) (strip_trailing_ws x) st.
Proof. reflexivity. Qed.

Local Lemma iscan_lines_located_cons :
  forall `{P : PosPolicy} off org k x y rest st,
  @iscan_lines_located P off org ((k, x) :: y :: rest)%list st =
  @iscan_lines_located P (pred off) org (y :: rest)%list
    (@ibreak_at T P
       (CursorAt (Spot k 0) (lines_start (y :: rest)%list)
          (Spot k (String.length x)))
       (allow_attrs off)
       (@iscan_str_located P (allow_attrs off) k org
          (String.length x) x st)).
Proof. reflexivity. Qed.

Local Lemma erase_iscan_lines_located : forall `{P : PosPolicy} off org l st,
  erase_iscan (@iscan_lines_located P off org l st) =
  iscan_lines_off off (map snd l) (erase_iscan st).
Proof.
  intros P off org l. revert off.
  induction l as [|[k x] l IH]; intros off st.
  - destruct off; reflexivity.
  - destruct l as [|kx l'].
    + rewrite iscan_lines_located_one, erase_iscan_str_located.
      destruct off as [|off'];
        [cbn [iscan_lines_off iscan_lines map snd]; apply iscan_str_at_on
        |cbn [iscan_lines_off map snd]; apply iscan_str_at_off].
    + rewrite iscan_lines_located_cons, IH, erase_ibreak_at,
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
  erase_iscan (iscan_str_at allow s st) = iscan_str_at allow s (erase_iscan st).
Proof.
  intros allow s. induction s as [|c s IH]; intros st; [reflexivity|].
  cbn [iscan_str_at]. rewrite IH, erase_istep_at. reflexivity.
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
  erase_iscan (iscan_lines_off off l st) =
  iscan_lines_off off l (erase_iscan st).
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
        rewrite erase_ibreak_at, <- !iscan_str_at_on, erase_iscan_str_at.
        reflexivity.
      * rewrite !iscan_lines_off_step, IH, erase_ibreak_at,
          <- !iscan_str_at_off, erase_iscan_str_at. reflexivity.
Qed.

Local Lemma erase_ifinish_located : forall `{P : PosPolicy} l st,
  Erase.of_inlines (@ifinish_located P l st) =
  @ifinish T semantic_pos semantic_inline_cursor (erase_iscan st).
Proof. intros P l st. apply erase_ifinish. Qed.

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
  rewrite erase_ifinish, erase_iscan_str_located,
    iscan_str_at_on. reflexivity.
Qed.

Lemma erase_parse_inline_line : forall s,
  Erase.of_inlines (parse_inline_line s) = parse_inline_line s.
Proof.
  intros s. unfold parse_inline_line.
  rewrite erase_ifinish, <- iscan_str_at_on, erase_iscan_str_at.
  reflexivity.
Qed.

Lemma para_inlines_at_semantic : forall off l,
  @para_inlines_at semantic_pos off l = para_inlines_off off (map snd l).
Proof. reflexivity. Qed.

Local Lemma erase_istart : erase_iscan istart = istart.
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
  rewrite erase_ifinish, erase_iscan_lines_off, erase_istart. reflexivity.
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
