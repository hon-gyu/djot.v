(* ai-disclosure: ai-generated *)

(* The scanner run on a buffer computes what the specification scanner
   computes: `chunks` obeys the string laws, and reading pending text
   through `map_text` commutes with every step, line break, and finish. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Strings Ast Attributes InlineTable InlineView InlineScan
  InlineLocated.
Import ListNotations.

Local Open Scope string_scope.

(* What the simulation needs of an instance: its operations are the
   string ones, read through `tval`. *)
Class TextLaws (Buf : Type) `{TextOps Buf} : Prop := {
  tval_nil : tval tnil = EmptyString;
  tval_push : forall b s, tval (tpush b s) = (tval b ++ s)%string;
  tval_of : forall s, tval (tof s) = s;
  tnonempty_val : forall b, tnonempty b = nonempty_str (tval b)
}.

Lemma concat_empty_snoc : forall l s,
  String.concat EmptyString (l ++ [s]) = (String.concat EmptyString l ++ s)%string.
Proof.
  induction l as [|x l IH]; intros s; [reflexivity|].
  cbn [app]. destruct l as [|y l].
  - reflexivity.
  - change (String.concat EmptyString (x :: (y :: l) ++ [s]))
      with (x ++ String.concat EmptyString ((y :: l) ++ [s]))%string.
    change (String.concat EmptyString (x :: y :: l))
      with (x ++ String.concat EmptyString (y :: l))%string.
    rewrite IH, append_assoc. reflexivity.
Qed.

Lemma nonempty_str_app : forall a b,
  nonempty_str (a ++ b) = (nonempty_str a || nonempty_str b)%bool.
Proof. intros [|c a] b; reflexivity. Qed.

Lemma nonempty_str_concat_empty : forall l,
  nonempty_str (String.concat EmptyString l) = existsb nonempty_str l.
Proof.
  induction l as [|x l IH]; [reflexivity|].
  destruct l as [|y l].
  - cbn. rewrite Bool.orb_false_r. reflexivity.
  - change (String.concat EmptyString (x :: y :: l))
      with (x ++ String.concat EmptyString (y :: l))%string.
    rewrite nonempty_str_app, IH. reflexivity.
Qed.

#[export] Instance chunks_laws : TextLaws chunks.
Proof.
  split.
  - reflexivity.
  - intros b s. cbn [tval tpush chunks_text]. unfold chunks_push, chunks_value.
    destruct s as [|c s]; cbn [nonempty_str].
    + rewrite append_empty_r. reflexivity.
    + cbn [List.rev]. apply concat_empty_snoc.
  - intros [|c s]; reflexivity.
  - intros b. cbn [tval tnonempty chunks_text]. unfold chunks_value.
    rewrite nonempty_str_concat_empty. apply Bool.eq_iff_eq_true.
    rewrite !existsb_exists.
    split; intros [x [Hx Hp]]; exists x; split; auto;
      [apply -> in_rev|apply <- in_rev]; exact Hx.
Qed.

(*
Simulation
==========

Any lawful buffer runs the specification: reading every pending-text
field through `tval` commutes with each step of the scan.
*)
Section WithTable.
Context {T : dtable}.

Section Lawful.
Context {Buf : Type} {X : TextOps Buf} {L : TextLaws Buf}.

Lemma map_text_lift : forall st, map_text (lift st) = st.
Proof.
  induction st; cbn [map_text lift]; rewrite ?tval_of; congruence.
Qed.

(* A pair of pending text and scope state, read the same way. *)
Definition map_fst (r : Buf * ostate) : string * ostate := (tval (fst r), snd r).

Context `{PosPolicy} `{InlineCursor}.

Ltac laws := rewrite ?tval_push, ?tval_nil, ?tval_of, ?tnonempty_val.

Lemma bflat_map : forall kids t o,
  map_fst (bflat kids t o) = bflat kids (tval t) o.
Proof.
  induction kids as [|[p a v] kids IH]; intros t o; [reflexivity|].
  cbn [bflat]. tred.
  destruct a; [destruct v|]; rewrite IH; laws; reflexivity.
Qed.

Lemma bsplit_nl_map : forall s t o,
  map_fst (bsplit_nl s t o) = bsplit_nl s (tval t) o.
Proof.
  induction s as [|c s IH]; intros t o; [reflexivity|].
  cbn [bsplit_nl]. tred.
  destruct (Ascii.eqb c nl_char); rewrite IH; laws; reflexivity.
Qed.

Lemma bclosed_lit_map : forall kids image o,
  map_fst (bclosed_lit kids image o) = bclosed_lit kids image o.
Proof.
  intros kids image o. unfold bclosed_lit.
  destruct (opop_str o) as [pre o1]. tred.
  rewrite <- (tval_of (pre ++ bracket_open image)) at 2.
  rewrite <- bflat_map. destruct (bflat kids _ o1) as [t o2].
  unfold map_fst; cbn [fst snd]. laws. reflexivity.
Qed.

Lemma bspan_lit_map : forall kids image src o,
  map_fst (bspan_lit kids image src o) = bspan_lit kids image src o.
Proof.
  intros kids image src o. unfold bspan_lit. tred.
  rewrite <- bclosed_lit_map. destruct (bclosed_lit kids image o) as [t o'].
  unfold map_fst; cbn [fst snd]. rewrite <- tval_push. apply bsplit_nl_map.
Qed.

Lemma battr_lit_map : forall src t o,
  map_fst (battr_lit src t o) = battr_lit src (tval t) o.
Proof.
  intros src t o. unfold battr_lit. tred.
  rewrite <- tval_push. apply bsplit_nl_map.
Qed.

Lemma bref_lit_map : forall kids image label o,
  map_fst (bref_lit kids image label o) = bref_lit kids image label o.
Proof.
  intros kids image label o. unfold bref_lit. tred.
  rewrite <- bclosed_lit_map. destruct (bclosed_lit kids image o) as [t o'].
  unfold map_fst; cbn [fst snd]. laws. reflexivity.
Qed.

Lemma note_pos_map : forall t prev, note_pos t prev = note_pos (tval t) prev.
Proof. intros t prev. unfold note_pos. tred. laws. reflexivity. Qed.

Lemma ilead_map : forall c t prev o,
  map_text (ilead c t prev o) = ilead c (tval t) prev o.
Proof.
  intros c t prev o. unfold ilead. tred. rewrite note_pos_map.
  repeat match goal with
  | |- context [if ?b then _ else _] => destruct b
  | |- context [match ?x with Some _ => _ | None => _ end] => destruct x as [[[? ?] ?]|]
  | |- context [match dstyle_of ?c with Some _ => _ | None => _ end] => destruct (dstyle_of c)
  end; cbn [map_text]; laws; reflexivity.
Qed.

Lemma idest_open_map : forall kids image open o,
  map_text (idest_open kids image open o) = idest_open kids image open o.
Proof.
  intros kids image open o. unfold idest_open. tred.
  rewrite <- tval_nil at 2. rewrite <- bflat_map.
  destruct (bflat kids tnil _) as [t o']. unfold map_fst; cbn [fst snd map_text].
  laws. reflexivity.
Qed.

Hint Rewrite ilead_map idest_open_map : map_text.

(* Split both sides on the conditions they share, then read the text
   fields through the laws and the lemmas proved so far. *)
Ltac crush :=
  tred; laws; autorewrite with map_text;
  repeat (match goal with
          | |- context [if ?b then _ else _] => destruct b
          | |- context [match ?x with Some _ => _ | None => _ end] => destruct x
          | |- context [match ?x with pair _ _ => _ end] => destruct x
          | |- context [match ?n with O => _ | S _ => _ end] => destruct n
          end; tred; laws; autorewrite with map_text);
  cbn [map_text]; laws; autorewrite with map_text; try reflexivity.

Lemma auto_lit_map : forall src t,
  tval (InlineScan.auto_lit src t) = InlineScan.auto_lit src (tval t).
Proof. intros src t. unfold InlineScan.auto_lit. tred. laws. reflexivity. Qed.

Lemma islice_end_map : forall st,
  map_text (islice_end st) = islice_end (map_text st).
Proof.
  induction st; cbn [islice_end map_text]; try destruct esc; crush;
    rewrite ?auto_lit_map; try reflexivity; assumption.
Qed.

Lemma iattr_mark_map : forall src a t o,
  map_text (iattr_mark src a t o) = iattr_mark src a (tval t) o.
Proof. intros. unfold iattr_mark. crush. Qed.

Hint Rewrite islice_end_map iattr_mark_map : map_text.

Lemma iattr_feed_map : forall c p src t prev sh o,
  map_text (iattr_feed c p src t prev sh o)
  = iattr_feed c p src (tval t) prev (map_text sh) o.
Proof. intros. unfold iattr_feed. crush. Qed.

Lemma oopen_marked_map : forall k cm t o,
  oopen_marked k cm t o = oopen_marked k cm (tval t) o.
Proof. intros. unfold oopen_marked. crush. Qed.

Lemma idelim_open_marked_map : forall k cm t o,
  map_text (idelim_open_marked k cm t o) = idelim_open_marked k cm (tval t) o.
Proof. intros. unfold idelim_open_marked. crush. Qed.

Hint Rewrite iattr_feed_map idelim_open_marked_map : map_text.

Lemma ibrace_step_at_map : forall attrs c t prev o,
  map_text (ibrace_step_at attrs c t prev o) = ibrace_step_at attrs c (tval t) prev o.
Proof.
  intros. unfold ibrace_step_at. destruct (dstyle_of c); [unfold idelim_marked; crush|].
  destruct attrs; [crush|].
  rewrite <- battr_lit_map. destruct (battr_lit EmptyString t o) as [t' o'].
  unfold map_fst; cbn [fst snd]. crush.
Qed.

Lemma ispan_feed_map : forall c kids image open p src o,
  map_text (ispan_feed c kids image open p src o) = ispan_feed c kids image open p src o.
Proof.
  intros. unfold ispan_feed.
  destruct (ap_failed (astep p c)); [|crush].
  rewrite <- bspan_lit_map. destruct (bspan_lit kids image src o) as [t o'].
  unfold map_fst; cbn [fst snd]. crush.
Qed.

Lemma inote_step_map : forall c esc image label open o,
  map_text (inote_step c esc image label open o) = inote_step c esc image label open o.
Proof. intros. unfold inote_step. crush. Qed.

Lemma iauto_step_map : forall c src t o,
  map_text (iauto_step c src t o) = iauto_step c src (tval t) o.
Proof. intros. unfold iauto_step. crush; rewrite ?auto_lit_map; crush. Qed.

Lemma isymbol_step_map : forall c alias t o sh,
  map_text (isymbol_step c alias t o sh) = isymbol_step c alias (tval t) o (map_text sh).
Proof. intros. unfold isymbol_step. crush. Qed.

Hint Rewrite ibrace_step_at_map : map_text.

Lemma iraw_step_at_map : forall attrs c spec v o,
  map_text (iraw_step_at attrs c spec v o) = iraw_step_at attrs c spec v o.
Proof. intros. unfold iraw_step_at. destruct spec; crush. Qed.

Lemma iwiki_close_map : forall image region open o,
  map_text (iwiki_close image region open o) = iwiki_close image region open o.
Proof.
  intros. unfold iwiki_close. destruct (wiki_split region) as [[|c t] al]; [|crush].
  destruct (bwiki_lit false true image region o). crush.
Qed.

Hint Rewrite iwiki_close_map : map_text.

Lemma iwiki_step_map : forall c esc rb image region open o,
  map_text (iwiki_step c esc rb image region open o) = iwiki_step c esc rb image region open o.
Proof. intros. unfold iwiki_step. crush. Qed.

Lemma ibang_step_map : forall c t prev o,
  map_text (ibang_step c t prev o) = ibang_step c (tval t) prev o.
Proof. intros. unfold ibang_step. crush. Qed.

Lemma idelim_done_map : forall k t before marker next o,
  map_text (idelim_done k t before marker next o) = idelim_done k (tval t) before marker next o.
Proof. intros. unfold idelim_done, InlineScan.idelim_lit. crush. Qed.

Hint Rewrite idelim_done_map : map_text.

Lemma idelim_resolve_map : forall k t before marker next o,
  map_text (idelim_resolve k t before marker next o)
  = idelim_resolve k (tval t) before marker next o.
Proof. intros. unfold idelim_resolve, InlineScan.idelim_lit. crush. Qed.

Hint Rewrite idelim_resolve_map : map_text.

Lemma idollar_step_map : forall c two t prev o,
  map_text (idollar_step c two t prev o) = idollar_step c two (tval t) prev o.
Proof. intros. unfold idollar_step. crush. Qed.

Lemma iperiod_step_map : forall c two t prev o,
  map_text (iperiod_step c two t prev o) = iperiod_step c two (tval t) prev o.
Proof. intros. unfold iperiod_step. crush. Qed.

Lemma idash_step_map : forall c n t prev o,
  map_text (idash_step c n t prev o) = idash_step c n (tval t) prev o.
Proof. intros. unfold idash_step. crush. Qed.

Lemma iresolve_map : forall st, map_text (iresolve st) = iresolve (map_text st).
Proof. intros []; cbn [iresolve map_text]; crush. Qed.

Lemma iescws_resolve_map : forall ws t prev o,
  let '(t', p', o') := iescws_resolve ws t prev o in
  (tval t', p', o') = iescws_resolve ws (tval t) prev o.
Proof. intros. unfold iescws_resolve. destruct ws; crush. Qed.

Lemma iesc_hard_map : forall ws t o, iesc_hard ws t o = iesc_hard ws (tval t) o.
Proof. intros. unfold iesc_hard. crush. Qed.

Hint Rewrite ispan_feed_map inote_step_map iauto_step_map isymbol_step_map
  iraw_step_at_map iwiki_step_map ibang_step_map idollar_step_map
  iperiod_step_map idash_step_map : map_text.

Theorem istep_at_map : forall attrs c st,
  map_text (istep_at attrs c st) = istep_at attrs c (map_text st).
Proof.
  intros attrs c st. revert attrs.
  induction st; intros attrs; cbn [istep_at map_text].
  - (* IText *) destruct esc; crush.
  - (* IEscWs *)
    destruct (is_ws c); [crush|].
    pose proof (iescws_resolve_map ws txt prev o) as M.
    destruct (iescws_resolve ws txt prev o) as [[t' p'] o'].
    rewrite <- M. crush.
  - crush.
  - (* IDelim *)
    destruct (Nat.ltb (S extra) (dwidth k)); [crush|].
    destruct marked; [crush; rewrite oopen_marked_map; reflexivity|].
    destruct (Ascii.eqb c rbrace); [crush|].
    rewrite <- idelim_resolve_map.
    destruct (idelim_resolve k txt before false (Some c) o) as [[] | | | | | | | | | | | | | | | | | | |];
      cbn [map_text]; crush.
  - crush.
  - crush.
  - crush.
  - crush.
  - crush.
  - crush.
  - crush.
  - crush.
  - (* IAttr *) rewrite <- !IHst. crush.
  - crush.
  - crush.
  - crush.
  - (* IDest *) destruct esc; rewrite <- ?IHst; crush.
  - crush.
  - (* ISymbol *) rewrite <- IHst. crush.
  - crush.
Qed.

(* Run a text-rebuilding helper on the buffer side: its string-side call
   becomes the buffer call read through `map_fst`. *)
Ltac through lem :=
  rewrite <- lem;
  match goal with
  | |- context [map_fst ?r] => destruct r; unfold map_fst; cbn [fst snd]
  end.

Lemma ifinish_ostate_flat_map : forall st,
  ifinish_ostate_flat st = ifinish_ostate_flat (map_text st).
Proof.
  intros []; cbn [ifinish_ostate_flat map_text]; try destruct esc;
    try solve [crush; rewrite ?iesc_hard_map, ?auto_lit_map; reflexivity];
    first [through bref_lit_map | through bspan_lit_map | through battr_lit_map];
    crush.
Qed.

Lemma ifinish_ostate_map : forall st, ifinish_ostate st = ifinish_ostate (map_text st).
Proof.
  induction st; cbn [ifinish_ostate map_text]; try assumption;
    rewrite ifinish_ostate_flat_map, iresolve_map; reflexivity.
Qed.

Theorem ifinish_map : forall st, ifinish st = ifinish (map_text st).
Proof. intros st. unfold ifinish, ifinish_rev. rewrite ifinish_ostate_map. reflexivity. Qed.

Lemma ibreak_flat_map : forall st,
  map_text (ibreak_flat st) = ibreak_flat (map_text st).
Proof.
  induction st; cbn [ibreak_flat map_text]; try destruct esc;
    try solve [crush; rewrite ?iesc_hard_map, ?auto_lit_map; reflexivity];
    try assumption;
    first [ apply ispan_feed_map | apply iattr_feed_map
          | destruct (bwiki_lit _ _ _ _ _); crush ].
Qed.

Theorem ibreak_at_map : forall attrs st,
  map_text (ibreak_at attrs st) = ibreak_at attrs (map_text st).
Proof.
  intros attrs st. revert attrs.
  induction st; intros attrs; cbn [ibreak_at map_text];
    try solve [rewrite ibreak_flat_map, iresolve_map; reflexivity].
  - rewrite iattr_feed_map, IHst. reflexivity.
  - rewrite IHst. crush.
  - apply IHst.
Qed.

End Lawful.

(*
Drivers
=======

The three line drivers the parser runs, over a buffer.  Each is its
specification read through `map_text`, which is what licenses a native
realization of the buffer driver to stand in for the specification one.
*)
Section Drivers.
Context {Buf : Type} {X : TextOps Buf} {L : TextLaws Buf}.

Fixpoint iscan_str_buf (s : string) (st : iscan_g (Buf:=Buf)) : iscan_g :=
  match s with
  | EmptyString => st
  | String c rest =>
      iscan_str_buf rest (@istep _ _ _ semantic_pos semantic_inline_cursor c st)
  end.

Fixpoint iscan_str_off_buf (s : string) (st : iscan_g (Buf:=Buf)) : iscan_g :=
  match s with
  | EmptyString => st
  | String c rest =>
      iscan_str_off_buf rest
        (@istep_at _ _ _ semantic_pos semantic_inline_cursor false c st)
  end.

Fixpoint iscan_str_located_buf `{PosPolicy} (allow : bool) (k : nat)
  (origin : spot) (rem : nat) (s : string) (st : iscan_g (Buf:=Buf)) : iscan_g :=
  match s with
  | EmptyString => st
  | String c rest =>
      iscan_str_located_buf allow k origin (pred rem) rest
        (@istep_at _ _ _ _ (InlineLocated.cursor_in k rem origin) allow c st)
  end.

Theorem iscan_str_buf_spec : forall s st,
  map_text (iscan_str_buf s st) = iscan_str s (map_text st).
Proof.
  induction s as [|c s IH]; intros st; [reflexivity|].
  cbn [iscan_str_buf iscan_str]. rewrite IH. unfold istep. rewrite istep_at_map.
  reflexivity.
Qed.

Theorem iscan_str_off_buf_spec : forall s st,
  map_text (iscan_str_off_buf s st) = iscan_str_off s (map_text st).
Proof.
  induction s as [|c s IH]; intros st; [reflexivity|].
  cbn [iscan_str_off_buf iscan_str_off]. rewrite IH, istep_at_map. reflexivity.
Qed.

Theorem iscan_str_located_buf_spec :
  forall `{PosPolicy} allow k origin rem s st,
    map_text (iscan_str_located_buf allow k origin rem s st)
    = InlineLocated.iscan_str_located allow k origin rem s (map_text st).
Proof.
  intros P allow k origin rem s. revert rem.
  induction s as [|c s IH]; intros rem st; [reflexivity|].
  cbn [iscan_str_located_buf InlineLocated.iscan_str_located].
  rewrite IH, istep_at_map. reflexivity.
Qed.

End Drivers.
End WithTable.
