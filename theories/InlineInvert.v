(* ai-disclosure: autonomous *)

(* The scan inverts the canonical view: scanning a canonical line reaches
   the state that emitting its nodes reaches, and a canonical paragraph
   parses back to its inlines. *)

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

Local Lemma iscan_open_ticks_more :
  forall k n vk out,
    iscan_str (ticks k) (IOpen n vk out) = IOpen (n + k) vk out.
Proof.
  induction k as [|k IH]; intros n vk out.
  - cbn [ticks iscan_str]. f_equal. lia.
  - cbn [ticks iscan_str istep istep_at]. change
      (iscan_str (ticks k) (IOpen (S n) vk out) = IOpen (n + S k) vk out).
    rewrite IH. f_equal. lia.
Qed.

Local Lemma iscan_open_ticks :
  forall k txt prev o,
    iscan_str (ticks (S k)) (IText false txt prev o)
    = IOpen (S k) VVerb (flush_text txt o).
Proof.
  intros k txt prev o. cbn [ticks iscan_str istep istep_at ilead]. change
    (iscan_str (ticks k) (IOpen 1 VVerb (flush_text txt o))
     = IOpen (S k) VVerb (flush_text txt o)).
  rewrite iscan_open_ticks_more. f_equal.
Qed.

Local Lemma iscan_verb_ticks_more :
  forall k n run txt vk out,
    iscan_str (ticks k) (IVerb n run txt vk out) = IVerb n (run + k) txt vk out.
Proof.
  induction k as [|k IH]; intros n run txt vk out.
  - cbn [ticks iscan_str]. f_equal. lia.
  - cbn [ticks iscan_str istep istep_at]. change
      (iscan_str (ticks k) (IVerb n (S run) txt vk out)
       = IVerb n (run + S k) txt vk out).
    rewrite IH. f_equal. lia.
Qed.

Local Lemma iscan_open_body :
  forall s n vk out,
    nonempty_str s = true -> starts_tick s = false -> n <> 0 ->
    iscan_str s (IOpen n vk out) = iscan_str s (IVerb n 0 EmptyString vk out).
Proof.
  intros [|c s] n vk out Hne Hstart Hn; [discriminate|].
  cbn [starts_tick] in Hstart. cbn [iscan_str istep istep_at]. rewrite Hstart.
  replace (Nat.eqb 0 n) with false.
  - reflexivity.
  - destruct n; [contradiction|reflexivity].
Qed.

Local Lemma iscan_verb_safe_nonempty :
  forall s n run txt vk out,
    nonempty_str s = true -> ends_tick s = false ->
    verb_safe_from n run s = true ->
    iscan_str s (IVerb n run txt vk out)
    = IVerb n 0 (txt ++ ticks run ++ s) vk out.
Proof.
  induction s as [|c rest IH]; intros n run txt vk out Hne Hend Hsafe;
    [discriminate|].
  cbn [iscan_str verb_safe_from] in Hsafe |- *. tred.
  destruct (is_tick c) eqn:Hc.
  - cbn [istep istep_at]. rewrite Hc. destruct rest as [|d rest'].
    + unfold ends_tick, starts_tick, rev_string in Hend.
      cbn [rev_string_aux] in Hend. rewrite Hc in Hend. discriminate.
    + rewrite ends_tick_cons_nonempty in Hend.
      rewrite (IH n (S run) txt vk out eq_refl Hend Hsafe).
      apply Ascii.eqb_eq in Hc. subst c. f_equal.
      rewrite ticks_succ_r, !append_assoc. reflexivity.
  - apply andb_true_iff in Hsafe as [Hrun Hsafe].
    apply negb_true_iff in Hrun. cbn [istep istep_at]. tred. rewrite Hc, Hrun.
    destruct rest as [|d rest'].
    + cbn [iscan_str]. f_equal.
    + rewrite ends_tick_cons_nonempty in Hend.
      rewrite (IH n 0 (txt ++ ticks run ++ one c) vk out eq_refl Hend Hsafe).
      f_equal. cbn [ticks one]. rewrite !append_assoc. reflexivity.
Qed.

Local Lemma iscan_verb_text_nonempty :
  forall s txt prev o,
    nonempty_str s = true ->
    verb_safe (verb_ticks s) (pad_verb s) = true ->
    iscan_str (verb_text s) (IText false txt prev o)
    = IVerb (verb_ticks s) (verb_ticks s) (pad_verb s) VVerb (flush_text txt o).
Proof.
  intros s txt prev o Hne Hsafe. unfold verb_text.
  rewrite !iscan_str_app.
  destruct (verb_ticks s) as [|k] eqn:Hn;
    [exfalso; apply (verb_ticks_nonzero s); exact Hn|].
  rewrite iscan_open_ticks.
  unfold verb_safe in Hsafe.
  rewrite (iscan_open_body (pad_verb s) (S k) VVerb (flush_text txt o)
             (pad_verb_nonempty s Hne) (pad_verb_starts_nontick s Hne))
    by discriminate.
  rewrite (iscan_verb_safe_nonempty (pad_verb s) (S k) 0 EmptyString VVerb
             (flush_text txt o) (pad_verb_nonempty s Hne)
             (pad_verb_ends_nontick s Hne) Hsafe).
  change (iscan_str (ticks (S k))
            (IVerb (S k) 0 (pad_verb s) VVerb (flush_text txt o))
          = IVerb (S k) (S k) (pad_verb s) VVerb (flush_text txt o)).
  rewrite iscan_verb_ticks_more. f_equal.
Qed.

(*
The output frame
----------------

Every state carries the inlines emitted so far, in reverse, and every
transition only ever conses onto them.  So a fixed suffix rides through
the whole scan untouched, and `ifinish` reverses it out at the front.
This is what lets a paragraph be assembled one line at a time from a
scan that does not restart: the lines after the first run against a
suffix holding the lines before it. *)


(* Appending at the *bottom* -- `os_out`, the outermost scope -- is what
   makes this commute with every transition: pushing and popping scopes
   only ever touch `os_stk`, so the suffix is out of their reach. *)
Local Definition oout_app (base : oitems) (o : ostate) : ostate :=
  OState (os_out o ++ base)%list (os_stk o) (os_word_start o).

(* What a suffix always is: empty, or a previous line, whose most recent
   node is the `SoftBreak` that ended it.  The `_app` lemmas below ask
   this of their suffix.

   `starts_str base = false` would do for the seam merge in
   `osnoc_nonstr`, but not for attachment: a scope that has emitted
   nothing sees the suffix's head, so the head has to be one
   `oattach_list` declines, as it declines an empty scope. *)
Local Definition base_ok (base : oitems) : bool :=
  match base with
  | [] => true
  | OIn (Node _ _ SoftBreak) :: _ => true
  | _ => false
  end.

Local Lemma base_ok_starts_str :
  forall base, base_ok base = true -> starts_str base = false.
Proof.
  intros [|[[p [|kv a'] v]|ma] base] H; try reflexivity.
  destruct v; try reflexivity. discriminate.
Qed.

Local Fixpoint iout_app (base : oitems) (st : iscan) : iscan :=
  match st with
  | IText esc txt prev o => IText esc txt prev (oout_app base o)
  | IEscWs ws txt prev o => IEscWs ws txt prev (oout_app base o)
  | IBrace txt prev o => IBrace txt prev (oout_app base o)
  | IDelim k seen txt cc m o => IDelim k seen txt cc m (oout_app base o)
  | IOpen n vk o => IOpen n vk (oout_app base o)
  | IVerb n run txt vk o => IVerb n run txt vk (oout_app base o)
  | IDollar two txt prev o => IDollar two txt prev (oout_app base o)
  | IDollarMath two escaped src txt last sh o =>
      IDollarMath two escaped src txt last (iout_app base sh) (oout_app base o)
  | IDollarMathClose two src txt last sh o =>
      IDollarMathClose two src txt last (iout_app base sh) (oout_app base o)
  | IBang txt prev o => IBang txt prev (oout_app base o)
  | IPeriod two txt prev o => IPeriod two txt prev (oout_app base o)
  | IDash n txt prev o => IDash n txt prev (oout_app base o)
  | IClosed txt o => IClosed txt (oout_app base o)
  | ISpan kids image open p src o =>
      ISpan kids image open p src (oout_app base o)
  | IAttr p src txt prev sh o =>
      IAttr p src txt prev (iout_app base sh) (oout_app base o)
  | INote esc image label open o =>
      INote esc image label open (oout_app base o)
  | IWiki esc rb image region open o =>
      IWiki esc rb image region open (oout_app base o)
  | IReference kids image open label o =>
      IReference kids image open label (oout_app base o)
  | IDest kids image open esc depth dst sh o =>
      IDest kids image open esc depth dst
        (iout_app base sh) (oout_app base o)
  | IAuto src txt o => IAuto src txt (oout_app base o)
  | ISymbol alias txt sh o =>
      ISymbol alias txt (iout_app base sh) (oout_app base o)
  | IRaw spec txt o => IRaw spec txt (oout_app base o)
  end.

Local Lemma oemit_app :
  forall n o base,
    oemit n (oout_app base o) = oout_app base (oemit n o).
Proof.
  intros n [out [|f stk] word] base; reflexivity.
Qed.

Local Lemma flush_text_app :
  forall txt o base,
    flush_text txt (oout_app base o) = oout_app base (flush_text txt o).
Proof.
  intros txt o base. unfold flush_text, flush_text_at.
  destruct (nonempty_str txt); [apply oemit_app | reflexivity].
Qed.


Local Lemma opush_at_app :
  forall k m cm open o base,
    opush_at k m cm open (oout_app base o)
    = oout_app base (opush_at k m cm open o).
Proof. intros k m cm open o base. reflexivity. Qed.

Local Lemma opush_app :
  forall k m o base,
    opush k m (oout_app base o) = oout_app base (opush k m o).
Proof. intros k m o base. reflexivity. Qed.

Local Lemma oclose_app :
  forall `{P : PosPolicy} k m stop o base,
    oclose k m stop (oout_app base o)
    = option_map (oout_app base) (oclose k m stop o).
Proof.
  intros P k m stop o base. unfold oclose. cbn [oout_app os_stk os_out].
  destruct (oclose_go k m [] (os_stk o)) as [[[content open] rest]|];
    [|reflexivity].
  cbn [option_map].
  rewrite <- (oemit_app
                (imk (span_start open) stop
                   (dnode k (List.rev (oresolve content))))
                (OState (os_out o) rest (os_word_start o)) base).
  reflexivity.
Qed.

Local Lemma sclose_app :
  forall k m o base,
    sclose k m (oout_app base o) = option_map (oout_app base) (sclose k m o).
Proof. intros k m o base. apply oclose_app. Qed.

Local Lemma bpush_app :
  forall image o base,
    bpush image (oout_app base o) = oout_app base (bpush image o).
Proof. intros image o base. reflexivity. Qed.

(* Taking a bracket back reads only the stack, which the suffix never
   touches. *)
Local Lemma bunpush_app :
  forall o base,
    bunpush (oout_app base o)
    = option_map
        (fun p => let '(image, open, o') := p in
                  (image, open, oout_app base o'))
        (bunpush o).
Proof.
  intros [out [|f stk] word] base; [reflexivity|].
  destruct f as [[k|im|im|nm] m open [|n l]]; reflexivity.
Qed.

Local Lemma bclose_app :
  forall o base,
    bclose (oout_app base o)
    = option_map
        (fun p => let '(kids, image, open, o') := p in
                  (kids, image, open, oout_app base o'))
        (bclose o).
Proof.
  intros o base. unfold bclose. cbn [oout_app os_stk os_out].
  destruct (bclose_go [] (os_stk o))
    as [[[[content image] open] rest]|]; reflexivity.
Qed.

Local Lemma tag_push_app :
  forall name start o base,
    tag_push name start (oout_app base o) = oout_app base (tag_push name start o).
Proof. intros name start o base. reflexivity. Qed.

Local Lemma tag_close_app :
  forall o base,
    tag_close (oout_app base o)
    = option_map
        (fun p => let '(kids, name, open, o') := p in
                  (kids, name, open, oout_app base o'))
        (tag_close o).
Proof.
  intros o base. unfold tag_close. cbn [oout_app os_stk os_out].
  destruct (tag_close_go [] (os_stk o))
    as [[[[content name] open] rest]|]; reflexivity.
Qed.

(* The bracket reconstruction reads the suffix too: `opop_str` reads the
   most recent node, which, with nothing emitted yet, is the suffix's
   head.  Hence the hypothesis `ofinish_out_app` carries. *)
Local Lemma opop_str_app :
  forall o base,
    base_ok base = true ->
    opop_str (oout_app base o)
    = (fst (opop_str o), oout_app base (snd (opop_str o))).
Proof.
  intros [out stk] base Hb. unfold opop_str, oout_app; cbn [os_out os_stk].
  destruct stk as [|f fs].
  - destruct out as [|n rest]; cbn [app].
    + destruct base as [|[[a [|p ps] i]|ma] base']; try reflexivity.
      destruct i; try reflexivity. discriminate.
    + destruct n as [[a [|p ps] i]|ma]; try reflexivity.
      destruct i; reflexivity.
  - destruct (fr_out f) as [|n rest]; [reflexivity|].
    destruct n as [[a [|p ps] i]|ma]; try reflexivity.
    destruct i; reflexivity.
Qed.

Local Lemma bflat_app :
  forall kids txt o base,
    bflat kids txt (oout_app base o)
    = (fst (bflat kids txt o), oout_app base (snd (bflat kids txt o))).
Proof.
  induction kids as [|[a attrs i] kids IH]; intros txt o base; cbn [bflat].
  - reflexivity.
  - destruct attrs as [|p ps];
      [destruct i; try (rewrite flush_text_app, oemit_app; apply IH); apply IH
      |rewrite flush_text_app, oemit_app; apply IH].
Qed.

Local Lemma bsplit_nl_app :
  forall s txt o base,
    bsplit_nl s txt (oout_app base o)
    = (fst (bsplit_nl s txt o), oout_app base (snd (bsplit_nl s txt o))).
Proof.
  induction s as [|c s IH]; intros txt o base; cbn [bsplit_nl];
    [reflexivity|].
  destruct (Ascii.eqb c nl_char);
    [rewrite flush_text_app, oemit_app|]; apply IH.
Qed.

Local Lemma dpush_app :
  forall image open o base,
    dpush image open (oout_app base o) =
    oout_app base (dpush image open o).
Proof. intros image open o base. reflexivity. Qed.

Local Lemma idest_open_app :
  forall kids image open o base,
    idest_open kids image open (oout_app base o)
    = iout_app base (idest_open kids image open o).
Proof.
  intros kids image open o base. unfold idest_open; tred.
  rewrite dpush_app, bflat_app.
  destruct (bflat kids EmptyString (dpush image open o)) as [txt o1].
  reflexivity.
Qed.

Local Lemma bclosed_lit_app :
  forall kids image o base,
    base_ok base = true ->
    bclosed_lit kids image (oout_app base o)
    = (fst (bclosed_lit kids image o),
       oout_app base (snd (bclosed_lit kids image o))).
Proof.
  intros kids image o base Hb. unfold bclosed_lit.
  rewrite (opop_str_app o base Hb).
  destruct (opop_str o) as [pre o1]; cbn [fst snd]; tred.
  rewrite bflat_app.
  destruct (bflat kids (pre ++ bracket_open image)%string o1) as [txt o2].
  reflexivity.
Qed.

Local Lemma bref_lit_app :
  forall kids image label o base,
    base_ok base = true ->
    bref_lit kids image label (oout_app base o) =
    let '(txt, o') := bref_lit kids image label o in
    (txt, oout_app base o').
Proof.
  intros kids image label o base Hb. unfold bref_lit.
  rewrite (bclosed_lit_app kids image o base Hb).
  destruct (bclosed_lit kids image o). reflexivity.
Qed.

Local Lemma bnote_lit_app :
  forall esc image label o base,
    base_ok base = true ->
    bnote_lit esc image label (oout_app base o) =
    let '(txt, o') := bnote_lit esc image label o in
    (txt, oout_app base o').
Proof.
  intros esc image label o base Hb. unfold bnote_lit.
  rewrite (opop_str_app o base Hb).
  destruct (opop_str o) as [pre o1]; cbn [fst snd]. reflexivity.
Qed.

Local Lemma bwiki_lit_app :
  forall esc rb image region o base,
    base_ok base = true ->
    bwiki_lit esc rb image region (oout_app base o) =
    let '(txt, o') := bwiki_lit esc rb image region o in
    (txt, oout_app base o').
Proof.
  intros esc rb image region o base Hb. unfold bwiki_lit.
  rewrite (opop_str_app o base Hb).
  destruct (opop_str o) as [pre o1]; cbn [fst snd]. reflexivity.
Qed.

Local Lemma bspan_lit_app :
  forall kids image src o base,
    base_ok base = true ->
    bspan_lit kids image src (oout_app base o) =
    let '(txt, o') := bspan_lit kids image src o in
    (txt, oout_app base o').
Proof.
  intros kids image src o base Hb. unfold bspan_lit.
  rewrite (bclosed_lit_app kids image o base Hb).
  destruct (bclosed_lit kids image o) as [txt o']; cbn [fst snd]; tred.
  rewrite bsplit_nl_app.
  destruct (bsplit_nl src (txt ++ one lbrace)%string o'). reflexivity.
Qed.

Local Lemma battr_lit_app :
  forall src txt o base,
    battr_lit src txt (oout_app base o) =
    let '(t, o') := battr_lit src txt o in (t, oout_app base o').
Proof.
  intros src txt o base. unfold battr_lit; tred. rewrite bsplit_nl_app.
  destruct (bsplit_nl src (txt ++ one lbrace)%string o). reflexivity.
Qed.

Local Lemma iescws_resolve_app :
  forall ws txt prev o base,
    base_ok base = true ->
    iescws_resolve ws txt prev (oout_app base o)
    = let '(t, p, o') := iescws_resolve ws txt prev o in (t, p, oout_app base o').
Proof.
  intros [|c ws] txt prev o base Hb; cbn [iescws_resolve tval]; [reflexivity|].
  destruct (Ascii.eqb c " "%char); [|reflexivity].
  rewrite flush_text_app, oemit_app. reflexivity.
Qed.

Local Lemma ilead_app :
  forall c txt prev o base,
    ilead c txt prev (oout_app base o) = iout_app base (ilead c txt prev o).
Proof.
  intros c txt prev o base. unfold ilead.
  destruct (is_bslash c); [reflexivity|].
  destruct (is_tick c); [cbn [iout_app]; rewrite flush_text_app; reflexivity|].
  destruct (Ascii.eqb c dollar); [reflexivity|].
  destruct (Ascii.eqb c period); [reflexivity|].
  destruct (Ascii.eqb c hyphen); [reflexivity|].
  destruct (Ascii.eqb c lbrace); [reflexivity|].
  destruct (Ascii.eqb c bang); [reflexivity|].
  destruct (Ascii.eqb c lt); [reflexivity|].
  destruct (Ascii.eqb c ":"%char); [reflexivity|].
  destruct (Ascii.eqb c lbrack).
  { destruct (note_pos txt prev && wikilinks_enabled)%bool;
      [rewrite bunpush_app; destruct (bunpush o) as [[[image open] o']|];
        [reflexivity|]|];
      cbn [iout_app]; rewrite flush_text_app, bpush_app; reflexivity. }
  destruct (Ascii.eqb c rbrack).
  { destruct tags_enabled; [|reflexivity]. tred. sem_flush.
    rewrite flush_text_app, tag_close_app.
    destruct (tag_close (flush_text txt o)) as [[[[kids name] open] o']|];
      [|reflexivity].
    cbn [option_map iout_app]. rewrite oemit_app. reflexivity. }
  destruct (Ascii.eqb c hat && note_pos txt prev && notes_enabled)%bool;
    [rewrite bunpush_app;
     destruct (bunpush o) as [[[image open] o']|]; [reflexivity|]|];
    destruct (dstyle_of c); reflexivity.
Qed.

Local Lemma ospan_bang_app :
  forall image o base,
    base_ok base = true ->
    ospan_bang image (oout_app base o) = oout_app base (ospan_bang image o).
Proof.
  intros image o base Hb. unfold ospan_bang. destruct image; [|reflexivity].
  rewrite (opop_str_app o base Hb).
  destruct (opop_str o) as [pre o1]; cbn [fst snd].
  apply flush_text_app.
Qed.

Local Lemma omark_app :
  forall a spec o base,
    omark a spec (oout_app base o) = oout_app base (omark a spec o).
Proof.
  intros a spec [out [|f stk] word] base; reflexivity.
Qed.

Local Lemma iattr_mark_app :
  forall src a txt o base,
    iattr_mark src a txt (oout_app base o) =
    iout_app base (iattr_mark src a txt o).
Proof.
  intros src a txt o base. unfold iattr_mark.
  cbn [iout_app]. rewrite flush_text_app, omark_app. reflexivity.
Qed.

Local Lemma islice_end_app :
  forall base st,
    islice_end (iout_app base st) = iout_app base (islice_end st).
Proof.
  intros base st. induction st as [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|mt me ms mx ml msh IHmsh mo|mct mcs mcx mcl mcsh IHmcsh mco|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|cltxt clob|kids img open sp ssrc sob|ap asrc atxt aprev ash aob|kids img open label ob|nesc nimg nlab open nob|wesc wrb wimg wreg wopen wob|kids img open esc depth dst sh ob|asrc atxt aob|salias stxt sob IHsob o|rspec rtxt rob];
    try reflexivity.
  exact IHsob.
Qed.

Local Lemma iattr_feed_app :
  forall c p src txt prev sh o base,
    base_ok base = true ->
    iattr_feed c p src txt prev (iout_app base sh) (oout_app base o)
    = iout_app base (iattr_feed c p src txt prev sh o).
Proof.
  intros c p src txt prev sh o base Hb. unfold iattr_feed.
  rewrite islice_end_app.
  destruct (ap_failed (astep p c)); [reflexivity|].
  destruct (ap_done (astep p c)); [apply iattr_mark_app|reflexivity].
Qed.

Local Lemma ispan_feed_app :
  forall c kids image open p src o base,
    base_ok base = true ->
    ispan_feed c kids image open p src (oout_app base o)
    = iout_app base (ispan_feed c kids image open p src o).
Proof.
  intros c kids image open p src o base Hb. unfold ispan_feed. tred.
  destruct (ap_failed (astep p c)).
  - rewrite (bspan_lit_app kids image src o base Hb).
    destruct (bspan_lit kids image src o) as [txt o']. apply ilead_app.
  - destruct (ap_done (astep p c)); [|reflexivity].
    cbn [iout_app]. rewrite ospan_bang_app by exact Hb.
    rewrite oemit_app. reflexivity.
Qed.

Local Lemma idelim_resolve_app :
  forall k txt bef marker next o base,
    @idelim_resolve T _ _ semantic_pos semantic_inline_cursor
      k txt bef marker next (oout_app base o)
    = iout_app base
        (@idelim_resolve T _ _ semantic_pos semantic_inline_cursor
          k txt bef marker next o).
Proof.
  intros k txt bef marker next o base.
  assert (Hdone : forall o',
    @idelim_done T _ _ semantic_pos semantic_inline_cursor
      k txt bef marker next (oout_app base o')
    = iout_app base
        (@idelim_done T _ _ semantic_pos semantic_inline_cursor
          k txt bef marker next o')).
  { intros o'. unfold idelim_done.
    destruct (dbare k bef && negb marker && nonspace_at next)%bool;
      [cbn [iout_app]; rewrite flush_text_app, opush_app|]; reflexivity. }
  unfold idelim_resolve; rewrite !oclose_guard; tred.
  destruct (nonspace_at bef || marker)%bool; [|apply Hdone].
  sem_flush. rewrite flush_text_app, sclose_app.
  destruct (sclose k marker (flush_text txt o)); [reflexivity|].
  unfold oclose_barred, oout_app; cbn [os_stk].
  destruct (oclose_barred_go k marker false (os_stk o)); [reflexivity|].
  apply Hdone.
Qed.

Local Lemma idelim_open_marked_out_app :
  forall k cm txt base o,
    idelim_open_marked k cm txt (oout_app base o)
    = iout_app base (idelim_open_marked k cm txt o).
Proof.
  intros k cm txt base o.
  unfold idelim_open_marked, oopen_marked. cbn [iout_app].
  sem_flush. rewrite flush_text_app, opush_at_app. reflexivity.
Qed.

Local Lemma iresolve_app :
  forall base st,
    base_ok base = true ->
    iresolve (iout_app base st) = iout_app base (iresolve st).
Proof.
  intros base [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|mt me ms mx ml msh mo|mct mcs mcx mcl mcsh mco|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|cltxt clob|kids img open sp ssrc sob|ap asrc atxt aprev ash aob|kids img open label ob|nesc nimg nlab open nob|wesc wrb wimg wreg wopen wob|kids img open esc depth dst sh ob|asrc atxt aob|salias stxt sob|rspec rtxt rob] Hb;
    try reflexivity.
  - cbn [iresolve iout_app]. destruct (Nat.ltb (S seen) (dwidth k));
      [reflexivity|].
    destruct mrk; [apply idelim_open_marked_out_app | apply idelim_resolve_app].
Qed.

Local Lemma idelim_marked_out_app :
  forall k extra txt base o,
    idelim_marked k extra txt (oout_app base o)
    = iout_app base (idelim_marked k extra txt o).
Proof. intros. reflexivity. Qed.

Local Lemma istep_at_out_app :
  forall attrs_enabled c base st,
    base_ok base = true ->
    istep_at attrs_enabled c (iout_app base st)
    = iout_app base (istep_at attrs_enabled c st).
Proof.
  intros attrs_enabled c base st. revert attrs_enabled c base.
  induction st as [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|mt me ms mx ml msh IHmsh mo|mct mcs mcx mcl mcsh IHmcsh mco|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|cltxt clob|kids img open sp ssrc sob|ap asrc atxt aprev ash IHash aob|kids img open label ob|nesc nimg nlab open nob|wesc wrb wimg wreg wopen wob|kids img open esc depth dst sh IHsh ob|asrc atxt aob|salias stxt sob|rspec rtxt rob];
    intros attrs_enabled c base Hb; cbn [iout_app istep_at]; tred.
  - destruct (is_ws c); reflexivity.
  - apply ilead_app.
  - destruct (is_ws c); [reflexivity|].
    rewrite iescws_resolve_app by exact Hb.
    destruct (iescws_resolve ews etxt eprev eob) as [[t p] o']; cbn [fst snd].
    apply ilead_app.
  - unfold ibrace_step, ibrace_step_at. destruct (dstyle_of c);
      [apply idelim_marked_out_app|].
    destruct attrs_enabled; [rewrite ilead_app; apply iattr_feed_app, Hb|].
    rewrite battr_lit_app. destruct (battr_lit EmptyString txt o) as [t o'].
    apply ilead_app.
  - destruct (Nat.ltb (S seen) (dwidth k)).
    { destruct (Ascii.eqb c (dchar k)); [|apply ilead_app].
      destruct mrk; [apply idelim_marked_out_app|reflexivity]. }
    destruct mrk.
    { unfold oopen_marked. cbn [iout_app].
      rewrite flush_text_app, opush_at_app. apply ilead_app. }
    rewrite idelim_resolve_app. destruct (Ascii.eqb c rbrace); [reflexivity|].
    destruct (idelim_resolve k txt cc false (Some c) o)
      as [[] txt' prev' o'|? ? ? ?|? ? ?|? ? ? ? ? ?|? ? ?|? ? ? ? ?|? ? ? ?|? ? ? ? ? ? ?|? ? ? ? ? ?|? ? ? ?|? ? ? ?|? ? ?|? ?|? ? ? ? ?|? ? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ? ? ?|? ? ? ? ? ?|? ? ?|? ? ?|? ? ?]; cbn [iout_app];
      try reflexivity.
    apply ilead_app.
  - destruct (is_tick c); reflexivity.
  - destruct (is_tick c); [reflexivity|].
    destruct (Nat.eqb run n); [|reflexivity].
    destruct vk as [|sty|prefix]; cbn [vkind_verb vnode].
    + destruct (Ascii.eqb c lbrace); [reflexivity|].
      rewrite ?imk_semantic, oemit_app. apply ilead_app.
    + destruct sty.
      * rewrite andb_false_r, ?imk_semantic, oemit_app.
        apply ilead_app.
      * destruct (Ascii.eqb c dollar && dollar_math_enabled)%bool;
          rewrite ?imk_semantic, oemit_app;
          [reflexivity|apply ilead_app].
    + destruct (Ascii.eqb c dollar).
      * rewrite (opop_str_app o base Hb).
        destruct (opop_str o) as [pre o']; cbn [fst snd iout_app].
        rewrite flush_text_app, oemit_app. reflexivity.
      * destruct (Ascii.eqb c lbrace); [reflexivity|].
        rewrite ?imk_semantic, oemit_app. apply ilead_app.
  - (* a pending `$` either grows, opens a math span, or is text *)
    unfold idollar_step. destruct (Ascii.eqb c dollar);
      [destruct dtwo; reflexivity|].
    destruct (is_tick c && math_enabled)%bool;
      [cbn [iout_app]; rewrite flush_text_app; reflexivity|].
    destruct (is_tick c && dollar_math_enabled && negb dtwo)%bool;
      [cbn [iout_app]; rewrite flush_text_app; reflexivity|].
    destruct (dollar_math_enabled &&
      (negb dtwo ||
       negb (match dprev with Some p => Ascii.eqb p dollar | None => false end))
      && (dtwo || (negb (is_ws_nl c) && negb (is_tick c))))%bool;
      [cbn [iout_app]; rewrite ilead_app; reflexivity|apply ilead_app].
  - (* live dollar candidate *)
    cbn [istep_at iout_app]. rewrite IHmsh by exact Hb. destruct me;
      [reflexivity|]. destruct (Ascii.eqb c dollar); reflexivity.
  - (* possible closer *)
    cbn [istep_at iout_app]. rewrite IHmcsh by exact Hb.
    destruct mct; [destruct mcl as [p|];
      [destruct (Ascii.eqb p nl_char); destruct (Ascii.eqb c dollar)
      |destruct (Ascii.eqb c dollar)]|
      destruct (match mcl with Some p => negb (is_ws_nl p) | None => false end
        && negb ((Nat.leb 48 (nat_of_ascii c))
                 && Nat.leb (nat_of_ascii c) 57))%bool];
      cbn [iout_app]; try reflexivity.
    all: rewrite ?flush_text_app, ?oemit_app; try apply ilead_app; reflexivity.
  - (* a pending `.` either grows, completes an ellipsis, or is text *)
    unfold iperiod_step. destruct (Ascii.eqb c period);
      [destruct ptwo; reflexivity|].
    apply ilead_app.
  - (* a hyphen run either grows, gives its last back to a close marker,
       or is cut into dashes *)
    unfold idash_step. destruct (Ascii.eqb c hyphen); [reflexivity|].
    destruct (Ascii.eqb c rbrace); [|apply ilead_app].
    destruct (dstyle_of hyphen) as [k|]; [|reflexivity].
    destruct (Nat.leb (dwidth k) dn); [apply idelim_resolve_app|reflexivity].
  - unfold ibang_step. destruct (Ascii.eqb c lbrack);
      [cbn [iout_app]; rewrite flush_text_app, bpush_app; reflexivity
      |apply ilead_app].
  - destruct ((Ascii.eqb c lparen || Ascii.eqb c lbrack
               || (Ascii.eqb c lbrace && attrs_enabled))%bool);
      [|apply ilead_app].
    sem_flush. rewrite flush_text_app, bclose_app.
    destruct (bclose (flush_text cltxt clob))
      as [[[[kids image] open] o']|];
      [|apply ilead_app].
    cbn [option_map].
    destruct (Ascii.eqb c lparen);
      [rewrite idest_open_app; reflexivity|].
    destruct (Ascii.eqb c lbrack); reflexivity.
  - apply ispan_feed_app, Hb.
  - destruct (ap_failed (astep ap c)).
    + apply IHash, Hb.
    + rewrite (IHash false c base Hb). apply iattr_feed_app, Hb.
  - destruct (Ascii.eqb c rbrack); [cbn [iout_app]; rewrite oemit_app|];
      reflexivity.
  - unfold inote_step. destruct nesc; [reflexivity|].
    destruct (is_bslash c); [reflexivity|].
    destruct (Ascii.eqb c rbrack); [|reflexivity].
    cbn [iout_app]. rewrite ospan_bang_app by exact Hb.
    rewrite oemit_app. reflexivity.
  - unfold iwiki_step. tred. destruct wesc; [reflexivity|].
    destruct (wrb && Ascii.eqb c rbrack)%bool.
    + unfold iwiki_close. tred. destruct (wiki_split wreg) as [[|x t] al].
      * rewrite (bwiki_lit_app false true wimg wreg wob base Hb).
        destruct (bwiki_lit false true wimg wreg wob) as [t' o']. reflexivity.
      * cbn [iout_app]. rewrite oemit_app. reflexivity.
    + destruct (is_bslash c); [reflexivity|].
      destruct (Ascii.eqb c rbrack); reflexivity.
  - (* both readings advance, and only the balanced close names one *)
    destruct esc; [cbn [iout_app]; rewrite IHsh by exact Hb; reflexivity|].
    destruct (is_bslash c); [cbn [iout_app]; rewrite IHsh by exact Hb; reflexivity|].
    destruct (Ascii.eqb c lparen); [cbn [iout_app]; rewrite IHsh by exact Hb; reflexivity|].
    destruct (Ascii.eqb c rparen);
      [|cbn [iout_app]; rewrite IHsh by exact Hb; reflexivity].
    destruct depth;
      [cbn [iout_app]; rewrite oemit_app; reflexivity
      |cbn [iout_app]; rewrite IHsh by exact Hb; reflexivity].
  - unfold iauto_step. tred.
    destruct (Ascii.eqb c gt && auto_body_ok asrc && auto_kind_ok asrc)%bool;
      [cbn [iout_app]; rewrite flush_text_app, oemit_app; reflexivity|].
    destruct (Ascii.eqb c gt || is_ws c || Ascii.eqb c lt)%bool;
      [apply ilead_app | reflexivity].
  - unfold isymbol_step. tred.
    rewrite IHsob by exact Hb.
    destruct (symbol_char c); [reflexivity|].
    destruct (Ascii.eqb c ":"%char && nonempty_str salias)%bool.
    + cbn [iout_app]. rewrite flush_text_app, oemit_app. reflexivity.
    + destruct (Ascii.eqb c lbrack && nonempty_str salias && tags_enabled
                && tag_may_follow stxt)%bool;
        [|reflexivity].
      cbn [iout_app]. rewrite flush_text_app, tag_push_app. reflexivity.
  - unfold iraw_step_at. tred. rewrite ?imk_semantic.
    destruct (Ascii.eqb c rbrace && raw_spec_ok rspec)%bool.
    + destruct raw_inline_enabled.
      * cbn [iout_app]. rewrite oemit_app. reflexivity.
      * rewrite (oemit_app (mk (Verbatim rtxt)) rob base). apply ilead_app.
    + destruct rspec as [|x rspec']; cbn [tnonempty nonempty_str].
      * destruct (negb (Ascii.eqb c eqchar)); [|reflexivity].
        rewrite (oemit_app (mk (Verbatim rtxt)) rob base).
        unfold ibrace_step_at; destruct (dstyle_of c);
          [apply idelim_marked_out_app|].
        destruct attrs_enabled;
          [rewrite ilead_app; apply iattr_feed_app, Hb|].
        rewrite battr_lit_app. destruct (battr_lit EmptyString "") as [t o'].
        apply ilead_app.
      * destruct (Ascii.eqb c rbrace || raw_stop c)%bool; [|reflexivity].
        rewrite (oemit_app (mk (Verbatim rtxt)) rob base). apply ilead_app.
Qed.

Local Lemma istep_out_app :
  forall c base st,
    base_ok base = true ->
    istep c (iout_app base st) = iout_app base (istep c st).
Proof.
  intros c base st Hb. unfold istep. apply istep_at_out_app, Hb.
Qed.

Local Lemma iscan_str_out_app :
  forall s base st,
    base_ok base = true ->
    iscan_str s (iout_app base st) = iout_app base (iscan_str s st).
Proof.
  induction s as [|c s IH]; intros base st Hb; cbn [iscan_str]; [reflexivity|].
  rewrite istep_out_app by exact Hb. apply IH, Hb.
Qed.

Local Lemma ibreak_flat_app :
  forall base st,
    base_ok base = true ->
    ibreak_flat (iout_app base st) = iout_app base (ibreak_flat st).
Proof.
  intros base st. induction st as [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|mt me ms mx ml msh IHmsh mo|mct mcs mcx mcl mcsh IHmcsh mco|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|cltxt clob|kids img open sp ssrc sob|ap asrc atxt aprev ash aob|kids img open label ob|nesc nimg nlab nob|wesc wrb wimg wreg wopen wob|kids img open esc depth dst sh ob|asrc atxt aob|salias stxt sob IHsob o|rspec rtxt rob]; intro Hb;
    cbn [iout_app ibreak_flat]; try reflexivity.
  all: try (try unfold iesc_hard;
            rewrite flush_text_app, oemit_app; reflexivity).
  - destruct (Nat.eqb run n); [|reflexivity].
    rewrite !oemit_app. reflexivity.
  - apply ispan_feed_app, Hb.
  - apply iattr_feed_app, Hb.
  - tred.
    rewrite (bwiki_lit_app wesc wrb wimg wreg wob base Hb).
    destruct (bwiki_lit wesc wrb wimg wreg wob) as [t o'].
    cbn [iout_app]. rewrite flush_text_app, oemit_app. reflexivity.
  - apply IHsob, Hb.
  - rewrite oemit_app, flush_text_app, oemit_app. reflexivity.
Qed.

Local Lemma ibreak_flat_state_app :
  forall base st,
    base_ok base = true -> is_compound st = false ->
    ibreak (iout_app base st) = iout_app base (ibreak st).
Proof.
  intros base st Hb Hd.
  assert (Hd' : is_compound (iout_app base st) = false)
    by (destruct st; cbn [is_compound iout_app] in *;
        try reflexivity; try exact Hd; discriminate Hd).
  rewrite (ibreak_flat_state _ Hd'), (ibreak_flat_state _ Hd).
  rewrite iresolve_app by exact Hb. apply ibreak_flat_app, Hb.
Qed.

Local Lemma ibreak_at_out_app :
  forall attrs_enabled base st,
    base_ok base = true ->
    ibreak_at attrs_enabled (iout_app base st)
    = iout_app base (ibreak_at attrs_enabled st).
Proof.
  intros attrs_enabled base st. revert attrs_enabled base.
  induction st as [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|mt me ms mx ml msh IHmsh mo|mct mcs mcx mcl mcsh IHmcsh mco|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|cltxt clob|kids img open sp ssrc sob|ap asrc atxt aprev ash IHash aob|kids img open label ob|nesc nimg nlab open nob|wesc wrb wimg wreg wopen wob|kids img open esc depth dst sh IHsh ob|asrc atxt aob|salias stxt sob IHsob o|rspec rtxt rob];
    intros attrs_enabled base Hb;
    try (rewrite (ibreak_at_flat_state attrs_enabled) by reflexivity;
         rewrite (ibreak_at_flat_state attrs_enabled) by reflexivity;
         apply ibreak_flat_state_app; [exact Hb|reflexivity]).
  - cbn [ibreak_at iout_app].
    destruct (dtwo && dollar_math_enabled &&
      negb (match dprev with Some p => Ascii.eqb p dollar
            | None => false end))%bool.
    + cbn [iout_app]. rewrite <- ibreak_flat_app by exact Hb.
      reflexivity.
    + cbn [iresolve]. rewrite <- ibreak_flat_app by exact Hb.
      reflexivity.
  - cbn [ibreak_at iout_app]. rewrite IHmsh by exact Hb. reflexivity.
  - cbn [ibreak_at iout_app]. rewrite IHmcsh by exact Hb.
    destruct mct; [destruct mcl as [p|];
      [reflexivity|rewrite <- ibreak_flat_app by exact Hb;
       rewrite flush_text_app, oemit_app; reflexivity]|].
    destruct (match mcl with Some p => negb (is_ws_nl p)
              | None => false end); [|reflexivity].
    rewrite <- ibreak_flat_app by exact Hb.
    rewrite flush_text_app, oemit_app. reflexivity.
  - cbn [ibreak_at iout_app]. rewrite IHash by exact Hb.
    apply iattr_feed_app, Hb.
  - cbn [ibreak_at iout_app]. rewrite IHsh by exact Hb. reflexivity.
  - cbn [ibreak_at iout_app]. rewrite IHsob by exact Hb. reflexivity.
Qed.

Local Lemma ibreak_out_app :
  forall base st,
    base_ok base = true ->
    ibreak (iout_app base st) = iout_app base (ibreak st).
Proof.
  intros base st Hb. unfold ibreak. apply ibreak_at_out_app, Hb.
Qed.

Local Lemma iscan_lines_cons2 :
  forall x y rest st,
    iscan_lines (x :: y :: rest) st
    = iscan_lines (y :: rest) (ibreak (iscan_str x st)).
Proof. reflexivity. Qed.

Local Lemma iscan_lines_out_app :
  forall l base st,
    base_ok base = true ->
    iscan_lines l (iout_app base st) = iout_app base (iscan_lines l st).
Proof.
  induction l as [|x [|y rest] IH]; intros base st Hb; cbn [iscan_lines].
  - reflexivity.
  - apply iscan_str_out_app, Hb.
  - rewrite iscan_str_out_app, ibreak_out_app by exact Hb. apply IH, Hb.
Qed.

(* Flattening an abandoned scope merges a `Str` seam, which would reach
   into a suffix beginning with a `Str`.  This is the weakest form of
   `base_ok`, and the one consumer that needs no more. *)
Local Lemma osnoc_nonstr :
  forall n out, starts_str out = false -> osnoc n out = (n :: out)%list.
Proof.
  intros n [|[[a [|x xs] i]|ma] out'] H; try reflexivity.
  cbn [starts_str] in H. destruct i; try reflexivity.
  destruct n as [[c [|y ys] j]|na]; try reflexivity.
  destruct j; try reflexivity. discriminate.
Qed.

Lemma oapp_one : forall n out, oapp [n] out = osnoc n out.
Proof. reflexivity. Qed.

Lemma oapp_cons2 :
  forall n m rest out, oapp (n :: m :: rest) out = (n :: oapp (m :: rest) out)%list.
Proof. reflexivity. Qed.

Local Lemma oapp_app :
  forall cur out base,
    base_ok base = true ->
    oapp cur (out ++ base)%list = (oapp cur out ++ base)%list.
Proof.
  induction cur as [|n cur IH]; intros out base Hb; [reflexivity|].
  destruct cur as [|m cur'].
  - rewrite !oapp_one. destruct out as [|x out']; cbn [app].
    + rewrite (osnoc_nonstr n base (base_ok_starts_str base Hb)). reflexivity.
    + destruct x as [[a [|p ps] i]|xa]; [|reflexivity|reflexivity].
      destruct i; try reflexivity.
      destruct n as [[c [|q qs] j]|na]; [|reflexivity|reflexivity].
      destruct j; reflexivity.
  - rewrite !oapp_cons2. cbn [app]. f_equal. apply (IH out base Hb).
Qed.

Local Lemma oflatten_app :
  forall stk pend bottom base,
    base_ok base = true ->
    oflatten pend stk (bottom ++ base)%list
    = (oflatten pend stk bottom ++ base)%list.
Proof.
  induction stk as [|f stk IH]; intros pend bottom base Hb;
    cbn [oflatten]; [apply oapp_app, Hb | apply IH, Hb].
Qed.

(* A previous line resolves to something headed by the `SoftBreak` that
   ended it, which is what makes the splice invisible to both the seam
   merge and a waiting spec. *)
Local Lemma oresolve_base_head :
  forall base,
    base_ok base = true -> ibase_ok (oresolve base) = true.
Proof.
  intros [|[[p a v]|ma] base'] H; try discriminate; [reflexivity|].
  destruct v; try discriminate.
  unfold oresolve; cbn [oresolve_go].
  destruct (oresolve_go base') as [out m]; cbn [fst].
  destruct m; [|destruct a; reflexivity].
  destruct a as [|kv a']; rewrite isnoc_nonplain by reflexivity; reflexivity.
Qed.

(* Resolution distributes over the splice: the suffix is already settled
   and nothing in the prefix can reach into it. *)
Local Lemma oresolve_go_base :
  forall base, base_ok base = true -> snd (oresolve_go base) = false.
Proof.
  intros [|[[p a v]|ma] base'] H; try discriminate; [reflexivity|].
  cbn [oresolve_go]. destruct (oresolve_go base'); reflexivity.
Qed.


(* A waiting spec reads only the head of what is below it, and `base_ok`
   makes that head a `SoftBreak` -- which it declines exactly as it
   declines an empty scope.  So the splice is invisible to it. *)
Local Lemma oattach_list_app :
  forall a spec word out base,
    base_ok base = true ->
    oattach_list a spec word (out ++ oresolve base)%list
    = (oattach_list a spec word out ++ oresolve base)%list.
Proof.
  intros a spec word out base Hb.
  pose proof (oresolve_base_head base Hb) as Hbi.
  pose proof (ibase_ok_starts_str _ Hbi) as Hh.
  destruct out as [|[p a' v] out]; cbn [app]; unfold oattach_list.
  - destruct (oresolve base) as [|[q b w] bl] eqn:Eb; [reflexivity|].
    cbn [ibase_ok] in Hbi. destruct w; try discriminate Hbi.
    destruct b; reflexivity.
  - destruct a' as [|kv a'']; destruct v;
      try reflexivity; try (apply isnoc_app, Hh).
    (* the one case left: a plain `Str` head, which the spec splits *)
    destruct (last_ws_split s) as [pre w].
    destruct (nonempty_str w); [|reflexivity].
    destruct a as [|ka a2]; [reflexivity|].
    destruct (split_text_pos p word) as [pp wp].
    destruct (nonempty_str pre);
      [rewrite (isnoc_app (Node pp [] (Str pre)) out (oresolve base))
         by exact Hh|];
      apply isnoc_app, Hh.
Qed.

Local Lemma oresolve_go_app :
  forall l base,
    base_ok base = true ->
    oresolve_go (l ++ base)%list
    = ((fst (oresolve_go l) ++ oresolve base)%list, snd (oresolve_go l)).
Proof.
  intros l base Hb.
  pose proof (oresolve_base_head base Hb) as Hbi.
  pose proof (ibase_ok_starts_str _ Hbi) as Hh.
  induction l as [|i l IH]; cbn [app oresolve_go].
  - unfold oresolve. rewrite <- (oresolve_go_base base Hb).
    destruct (oresolve_go base); reflexivity.
  - rewrite IH. destruct (oresolve_go l) as [out m]; cbn [fst snd].
    destruct i as [n|a spec word].
    + destruct m; [rewrite isnoc_app by exact Hh|]; reflexivity.
    + rewrite (oattach_list_app a spec word out base Hb). f_equal.
      destruct (oattach_list a spec word out) as [|x xs] eqn:E;
        [exact Hh|reflexivity].
Qed.

Local Lemma oresolve_app :
  forall l base,
    base_ok base = true ->
    oresolve (l ++ base)%list = (oresolve l ++ oresolve base)%list.
Proof.
  intros l base Hb. unfold oresolve. rewrite (oresolve_go_app l base Hb).
  reflexivity.
Qed.

Local Lemma ofinish_out_app :
  forall base o,
    base_ok base = true ->
    ofinish (oout_app base o) = (ofinish o ++ oresolve base)%list.
Proof.
  intros base o Hb. unfold ofinish. rewrite !oitems_of_spec.
  unfold oout_app;
    cbn [os_out os_stk].
  rewrite oflatten_app by exact Hb. apply oresolve_app, Hb.
Qed.

Local Lemma ifinish_ostate_flat_app :
  forall base st,
    base_ok base = true ->
    ifinish_ostate_flat (iout_app base st)
    = oout_app base (ifinish_ostate_flat st).
Proof.
  intros base [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|mt me ms mx ml msh mo|mct mcs mcx mcl mcsh mco|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|cltxt clob|kids img open sp ssrc sob|ap asrc atxt aprev ash aob|kids img open label ob|nesc nimg nlab open nob|wesc wrb wimg wreg wopen wob|kids img open esc depth dst sh ob|asrc atxt aob|salias stxt sob|rspec rtxt rob] Hb;
    cbn [iout_app ifinish_ostate_flat]. tred.
  1,3: unfold iesc_hard; rewrite flush_text_app, oemit_app; reflexivity.
  1: rewrite flush_text_app; reflexivity.
  1,2: reflexivity.
  1,2: rewrite oemit_app; reflexivity.
  all: try reflexivity.
  - rewrite (bspan_lit_app kids img (tval ssrc) sob base Hb).
    destruct (bspan_lit kids img (tval ssrc) sob) as [t o']; cbn [fst snd].
    rewrite flush_text_app. reflexivity.
  - rewrite battr_lit_app.
    destruct (battr_lit (tval asrc) atxt aob) as [t o']; cbn [fst snd].
    rewrite flush_text_app. reflexivity.
  - rewrite (bref_lit_app kids img (tval label) ob base Hb).
    destruct (bref_lit kids img (tval label) ob) as [t o']; cbn [fst snd].
    rewrite flush_text_app. reflexivity.
  - rewrite (bnote_lit_app nesc nimg (tval nlab) nob base Hb).
    destruct (bnote_lit nesc nimg (tval nlab) nob) as [t o']; cbn [fst snd].
    rewrite flush_text_app. reflexivity.
  - rewrite (bwiki_lit_app wesc wrb wimg (tval wreg) wob base Hb).
    destruct (bwiki_lit wesc wrb wimg (tval wreg) wob) as [t o']; cbn [fst snd].
    rewrite flush_text_app. reflexivity.
  - rewrite flush_text_app. reflexivity.
  - rewrite oemit_app, flush_text_app. reflexivity.
Qed.

Local Lemma ifinish_ostate_flat_state_app :
  forall base st,
    base_ok base = true -> is_compound st = false ->
    ifinish_ostate (iout_app base st) = oout_app base (ifinish_ostate st).
Proof.
  intros base st Hb Hd.
  assert (Hd' : is_compound (iout_app base st) = false)
    by (destruct st; cbn [is_compound iout_app] in *;
        try reflexivity; try exact Hd; discriminate Hd).
  rewrite (ifinish_ostate_flat_state _ Hd'),
          (ifinish_ostate_flat_state _ Hd).
  rewrite iresolve_app by exact Hb. apply ifinish_ostate_flat_app, Hb.
Qed.

Local Lemma ifinish_ostate_out_app :
  forall base st,
    base_ok base = true ->
    ifinish_ostate (iout_app base st) = oout_app base (ifinish_ostate st).
Proof.
  intros base st Hb.
  induction st;
    try (apply ifinish_ostate_flat_state_app; [exact Hb|reflexivity]).
  all: try (cbn [iout_app ifinish_ostate iresolve ifinish_ostate_flat];
            apply flush_text_app).
  all: try (cbn [ifinish_ostate iout_app]; exact IHst).
  cbn [ifinish_ostate iout_app]. destruct two;
    [destruct last as [p|];
     [exact IHst|rewrite flush_text_app, oemit_app; reflexivity]|].
  destruct (match last with Some p => negb (is_ws_nl p)
            | None => false end); [|exact IHst].
  rewrite flush_text_app, oemit_app. reflexivity.
Qed.

Local Lemma ifinish_rev_out_app :
  forall base st,
    base_ok base = true ->
    ifinish_rev (iout_app base st)
    = (ifinish_rev st ++ oresolve base)%list.
Proof.
  intros base st Hb. unfold ifinish_rev.
  rewrite ifinish_ostate_out_app by exact Hb.
  apply ofinish_out_app, Hb.
Qed.

Local Lemma ifinish_out_app :
  forall base st,
    base_ok base = true ->
    ifinish (iout_app base st)
    = (List.rev (oresolve base) ++ ifinish st)%list.
Proof.
  intros base st Hb. unfold ifinish.
  rewrite ifinish_rev_out_app by exact Hb.
  rewrite List.rev_app_distr. reflexivity.
Qed.

Local Definition text_sep_ok (txt : string) (cis : list cinline) : bool :=
  match txt with
  | EmptyString => true
  | String _ _ =>
      match cis with
      | CIStr _ :: _ => false
      | CITag _ _ :: _ => tag_may_follow txt
      | _ => true
      end
  end.

Local Lemma text_sep_nil : forall txt, text_sep_ok txt [] = true.
Proof. intros [|c t]; reflexivity. Qed.

Local Lemma text_sep_tag :
  forall txt name kids rest,
    text_sep_ok txt (CITag name kids :: rest) = true -> tag_may_follow txt = true.
Proof. intros [|c t] name kids rest H; [reflexivity|exact H]. Qed.

Local Lemma ifinish_text :
  forall txt prev out,
    ifinish (IText false txt prev (OState out [] None))
    = List.rev (oresolve (os_out (flush_text txt (OState out [] None)))).
Proof.
  intros txt prev out.
  unfold ifinish, ifinish_rev, ofinish. rewrite oitems_of_spec.
  cbn [ifinish_ostate ifinish_ostate_flat iresolve].
  unfold flush_text, flush_text_at, oemit; cbn [os_stk os_out oflatten oapp]; tred.
  destruct (nonempty_str txt); reflexivity.
Qed.

(* Canonical text never opens a verbatim: `needs_escape` claims the
   backtick, so `escape_str` emits none bare, and the scanner stays in
   `IText` throughout. *)
Local Lemma ilead_plain :
  forall c txt prev o,
    needs_escape c = false ->
    ilead c txt prev o = IText false (txt ++ one c)%string (Some c) o.
Proof.
  intros c txt prev o Hc. unfold needs_escape in Hc.
  apply orb_false_iff in Hc as [Hc Hcolon].
  apply orb_false_iff in Hc as [Hc Hhyp].
  apply orb_false_iff in Hc as [Hc Hhat].
  apply orb_false_iff in Hc as [Hres Hdl].
  destruct (dreserved_false c Hres)
    as [Hbs [Htk [Hlb [Hrb [Hlk [Hrk [Hbg [Hdol [Hpd Hlt]]]]]]]]].
  unfold ilead.
  rewrite Hbs, Htk, Hdol, Hpd, Hhyp, Hlb, Hbg, Hlt, Hcolon, Hlk, Hrk, Hhat.
  cbn [andb].
  destruct (dstyle_of c) eqn:Hd; [|reflexivity].
  unfold is_delim in Hdl. rewrite Hd in Hdl. discriminate.
Qed.

(* An escaped character is that character pushed as text. *)
Local Lemma iscan_escaped :
  forall c t txt prev o, needs_escape c = true ->
    iscan_str (String "\"%char (String c t)) (IText false txt prev o)
    = iscan_str t (IText false (txt ++ one c)%string (Some c) o).
Proof.
  intros c t txt prev o Hc.
  cbn [iscan_str istep istep_at]. unfold ilead.
  change (is_bslash "\"%char) with true. cbn [iscan_str istep istep_at].
  rewrite (is_punct_not_ws c (needs_escape_punct c Hc)),
          (needs_escape_punct c Hc).
  reflexivity.
Qed.

(* A character left bare by `bare_ok` waits on the byte after it, and
   that byte never completes a construct with it, so the two bytes read
   as the character pushed as text and then the next one. *)
Local Lemma bare_step :
  forall b c pre d r txt prev o,
    needs_escape c = true -> bare_ok b pre c (String d r) = true ->
    iscan_str (escape_from b (String c pre) (String d r)) (ilead c txt prev o)
    = iscan_str (escape_from b (String c pre) (String d r))
        (IText false (txt ++ one c)%string (Some c) o).
Proof.
  intros b c pre d r txt prev o Hc Hb.
  destruct pre as [|p pre']; [discriminate Hb|].
  cbn [bare_ok] in Hb.
  assert (Hd1 : typography_dashes 1 = one hyphen)
    by (unfold typography_dashes; destruct smart_typography; reflexivity).
  cbn [escape_from].
  destruct (needs_escape d && negb (bare_ok b (String c (String p pre')) d r))%bool
    eqn:Hd; cbn [iscan_str]; f_equal.
  - (* the next byte is a backslash, which claims nothing the waiting
       state could complete *)
    f_equal.
    apply orb_true_iff in Hb as [Hb|Hh]; [apply orb_true_iff in Hb as [Hp|Hbang]|].
    + apply andb_true_iff in Hp as [Hp _]. apply andb_true_iff in Hp as [Hp _].
      apply Ascii.eqb_eq in Hp. subst c.
      unfold istep. cbn [istep_at]. unfold ilead at 1. cbn. reflexivity.
    + apply Ascii.eqb_eq in Hbang. subst c.
      unfold istep. cbn [istep_at]. unfold ilead at 1. cbn. reflexivity.
    + apply andb_true_iff in Hh as [Hh _].
      apply Ascii.eqb_eq in Hh. subst c.
      unfold istep. cbn [istep_at]. unfold ilead at 1. cbn. rewrite Hd1. reflexivity.
  - (* the next byte is bare, so it is not a bracket or a brace, which
       are never bare *)
    assert (Hlb : Ascii.eqb d lbrack = false).
    { destruct (Ascii.eqb d lbrack) eqn:E; [|reflexivity].
      apply Ascii.eqb_eq in E. subst d.
      destruct r, b; cbn in Hd; discriminate Hd. }
    assert (Hrb : Ascii.eqb d rbrace = false).
    { destruct (Ascii.eqb d rbrace) eqn:E; [|reflexivity].
      apply Ascii.eqb_eq in E. subst d.
      destruct r, b; cbn in Hd; discriminate Hd. }
    apply orb_true_iff in Hb as [Hb|Hh]; [apply orb_true_iff in Hb as [Hp|Hbang]|].
    + apply andb_true_iff in Hp as [Hp _]. apply andb_true_iff in Hp as [Hp Hdp].
      apply negb_true_iff in Hdp.
      apply Ascii.eqb_eq in Hp. subst c.
      unfold istep. cbn [istep_at]. unfold ilead at 1. cbn - [ilead].
      unfold iperiod_step. rewrite Hdp. reflexivity.
    + apply Ascii.eqb_eq in Hbang. subst c.
      unfold istep. cbn [istep_at]. unfold ilead at 1. cbn - [ilead].
      unfold ibang_step. rewrite Hlb. reflexivity.
    + apply andb_true_iff in Hh as [Hh Hdh]. apply negb_true_iff in Hdh.
      apply Ascii.eqb_eq in Hh. subst c.
      unfold istep. cbn [istep_at]. unfold ilead at 1. cbn - [ilead typography_dashes].
      unfold idash_step. rewrite Hdh, Hrb, Hd1. reflexivity.
Qed.

(* Canonical text never leaves `IText` for long: `needs_escape` claims
   every character the scanner dispatches on, and `escape_from` leaves one
   bare only where the next byte hands it back as text.  So adding a
   table row costs an escape, not a proof. *)
Local Lemma iscan_escape_from :
  forall s pre txt prev o,
    iscan_str (escape_from false pre s) (IText false txt prev o)
    = IText false (txt ++ s)%string (str_last s prev) o.
Proof.
  induction s as [|c rest IH]; intros pre txt prev o.
  - cbn [escape_from iscan_str]. rewrite append_empty_r. reflexivity.
  - cbn [escape_from].
    destruct (needs_escape c && negb (bare_ok false pre c rest))%bool eqn:Hesc.
    + apply andb_true_iff in Hesc as [Hc _].
      cbn [iscan_str istep istep_at]. unfold ilead.
      change (is_bslash "\"%char) with true. cbn [iscan_str istep istep_at].
      rewrite (is_punct_not_ws c (needs_escape_punct c Hc)),
              (needs_escape_punct c Hc).
      rewrite IH, append_assoc. reflexivity.
    + destruct (needs_escape c) eqn:Hc.
      * cbn [andb negb] in Hesc. apply negb_false_iff in Hesc.
        destruct rest as [|d r]; [destruct pre; discriminate Hesc|].
        cbn [iscan_str istep istep_at].
        rewrite (bare_step false c pre d r txt prev o Hc Hesc).
        rewrite IH, append_assoc. reflexivity.
      * cbn [iscan_str istep istep_at]. rewrite (ilead_plain c txt prev o Hc).
        rewrite IH, append_assoc. reflexivity.
Qed.

(* A run that ends its line may leave its last character bare, and then
   the scan ends waiting on it; the end of the line settles it as text,
   which is where the escaped spelling ends already. *)
Local Lemma escape_end_state :
  forall s pre txt prev o,
    let st := iscan_str (escape_from true pre s) (IText false txt prev o) in
    st = IText false (txt ++ s)%string (str_last s prev) o
    \/ ((exists t p, st = IPeriod false t p o \/ st = IBang t p o \/ st = IDash 1 t p o)
        /\ iresolve st = IText false (txt ++ s)%string (str_last s prev) o).
Proof.
  induction s as [|c rest IH]; intros pre txt prev o; cbn zeta.
  - left. cbn [escape_from iscan_str]. rewrite append_empty_r. reflexivity.
  - cbn [escape_from].
    specialize (IH (String c pre) (txt ++ one c)%string (Some c) o). cbn zeta in IH.
    rewrite append_assoc in IH. cbn [append one] in IH.
    change (str_last (String c rest) prev) with (str_last rest (Some c)).
    destruct (needs_escape c && negb (bare_ok true pre c rest))%bool eqn:Hesc.
    + apply andb_true_iff in Hesc as [Hc _].
      rewrite (iscan_escaped c _ txt prev o Hc). exact IH.
    + destruct (needs_escape c) eqn:Hc.
      * cbn [andb negb] in Hesc. apply negb_false_iff in Hesc.
        destruct rest as [|d r].
        -- (* the bare last character: the scan ends waiting on it *)
           clear IH. destruct pre as [|p pre']; [discriminate Hesc|].
           cbn [bare_ok andb] in Hesc.
           cbn [escape_from iscan_str istep istep_at str_last].
           right.
           assert (Hd1 : typography_dashes 1 = one hyphen)
             by (unfold typography_dashes; destruct smart_typography; reflexivity).
           apply orb_true_iff in Hesc as [Hesc|Hh];
             [apply orb_true_iff in Hesc as [Hp|Hb]|].
           ++ apply andb_true_iff in Hp as [Hp _]. apply Ascii.eqb_eq in Hp. subst c.
              unfold ilead. cbn - [tpush]. split; [eauto|reflexivity].
           ++ apply Ascii.eqb_eq in Hb. subst c.
              unfold ilead. cbn - [tpush]. split; [eauto|reflexivity].
           ++ apply Ascii.eqb_eq in Hh. subst c.
              unfold ilead. cbn - [tpush typography_dashes]. split; [eauto|].
              rewrite Hd1. reflexivity.
        -- cbn [iscan_str istep istep_at].
           rewrite (bare_step true c pre d r txt prev o Hc Hesc). exact IH.
      * cbn [iscan_str istep istep_at]. rewrite (ilead_plain c txt prev o Hc). exact IH.
Qed.

Local Lemma ifinish_escape_end :
  forall s pre txt prev o,
    ifinish (iscan_str (escape_from true pre s) (IText false txt prev o))
    = ifinish (IText false (txt ++ s)%string (str_last s prev) o).
Proof.
  intros s pre txt prev o.
  destruct (escape_end_state s pre txt prev o)
    as [E | [[t [p [E|[E|E]]]] Hr]]; rewrite E; [reflexivity| | |];
    rewrite E in Hr; unfold ifinish, ifinish_rev; cbn [ifinish_ostate];
    rewrite Hr; reflexivity.
Qed.

Local Lemma iscan_closed_escape_end :
  forall s pre txt prev o,
    iscan_closed (iscan_str (escape_from true pre s) (IText false txt prev o))
    = iscan_closed (IText false (txt ++ s)%string (str_last s prev) o).
Proof.
  intros s pre txt prev o.
  destruct (escape_end_state s pre txt prev o)
    as [E | [[t [p [E|[E|E]]]] Hr]]; rewrite E; [reflexivity| | |];
    rewrite E in Hr; unfold iscan_closed; rewrite Hr; reflexivity.
Qed.

Local Lemma iscan_escape :
  forall s txt prev o,
    iscan_str (escape_str s) (IText false txt prev o)
    = IText false (txt ++ s)%string (str_last s prev) o.
Proof. intros s. apply iscan_escape_from. Qed.

Local Lemma iscan_escape_after_verb :
  forall s n body vk o,
    nonempty_str s = true ->
    iscan_str (escape_str s) (IVerb n n body vk o)
    = IText false s (str_last s (Some tick))
        (oemit (mk (vnode vk (trim_verb body))) o).
Proof.
  intros [|c rest] n body vk o Hne; [discriminate|].
  destruct vk as [|sty|prefix]; [|destruct sty|].
  all: unfold escape_str; cbn [escape_from bare_ok negb]; rewrite andb_true_r;
       destruct (needs_escape c) eqn:Hc.
  all: first [
    cbn [iscan_str istep istep_at];
    change (is_tick "\"%char) with false;
    rewrite nat_eqb_refl;
    try change (Ascii.eqb "\"%char dollar) with false;
    try change (Ascii.eqb "\"%char lbrace) with false;
    cbn [andb]; unfold ilead at 1;
    change (is_bslash "\"%char) with true;
    cbn [iscan_str istep istep_at];
    try change (Ascii.eqb "\"%char lbrace) with false;
    cbn [istep_at];
    rewrite (is_punct_not_ws c (needs_escape_punct c Hc)),
            (needs_escape_punct c Hc), iscan_escape_from;
    cbn [append one]; reflexivity
  | cbn [iscan_str istep istep_at];
    replace (is_tick c) with false
      by (destruct (is_tick c) eqn:Ht;
          [rewrite (needs_escape_tick c Ht) in Hc; discriminate|reflexivity]);
    try replace (Ascii.eqb c dollar) with false
      by (destruct (Ascii.eqb c dollar) eqn:Hd;
          [apply Ascii.eqb_eq in Hd; subst c;
           cbn [needs_escape] in Hc; discriminate|reflexivity]);
    try replace (Ascii.eqb c lbrace) with false
      by (destruct (Ascii.eqb c lbrace) eqn:Hb;
          [apply Ascii.eqb_eq in Hb; subst c;
           rewrite needs_escape_lbrace in Hc; discriminate|reflexivity]);
    cbn [andb];
    rewrite nat_eqb_refl, (ilead_plain c EmptyString (Some tick) _ Hc);
    rewrite iscan_escape_from; cbn [one append]; reflexivity
  ].
Qed.

Local Lemma cis_ok_tail :
  forall c rest, cis_ok (c :: rest) = true -> cis_ok rest = true.
Proof.
  intros c rest H. unfold cis_ok in *. apply andb_true_iff in H as [Ha Hs].
  apply andb_true_iff. split.
  - cbn [forallb] in Ha. apply andb_true_iff in Ha as [_ Ha]. exact Ha.
  - destruct rest as [|r rest']; [reflexivity|].
    cbn [ci_sep_ok] in Hs. apply andb_true_iff in Hs as [_ Hs]. exact Hs.
Qed.

Local Lemma cis_ok_head :
  forall c rest, cis_ok (c :: rest) = true -> ci_ok c = true.
Proof.
  intros c rest H. unfold cis_ok in H. apply andb_true_iff in H as [H _].
  cbn [forallb] in H. apply andb_true_iff in H as [H _]. exact H.
Qed.

Local Lemma ci_str_tail_sep :
  forall s rest,
    cis_ok (CIStr s :: rest) = true -> nonempty_str s = true ->
    text_sep_ok s rest = true.
Proof.
  intros s [|r rest] H Hs; [unfold text_sep_ok; destruct s; reflexivity|].
  destruct r as [t|v|k kids|img kids dst|rimg rkids rlabel|label|a|rf rv|we wt wal|tn tkids];
    [|unfold text_sep_ok; destruct s; reflexivity ..|].
  - unfold cis_ok in H. cbn [ci_sep_ok ci_pair_ok] in H.
    repeat rewrite andb_false_r in H. discriminate.
  - unfold cis_ok in H. cbn [ci_sep_ok ci_pair_ok] in H.
    apply andb_true_iff in H as [_ H]. apply andb_true_iff in H as [H _].
    destruct s; [discriminate Hs|exact H].
Qed.

Local Lemma ci_verb_nonempty :
  forall v rest, cis_ok (CIVerb v :: rest) = true -> nonempty_str v = true.
Proof.
  intros v rest H. pose proof (cis_ok_head (CIVerb v) rest H) as Hv.
  cbn [ci_ok] in Hv. apply andb_true_iff in Hv as [Hv _]. exact Hv.
Qed.

Local Lemma ci_verb_content_ok :
  forall v rest, cis_ok (CIVerb v :: rest) = true -> verb_content_ok v = true.
Proof.
  intros v rest H. pose proof (cis_ok_head (CIVerb v) rest H) as Hv.
  cbn [ci_ok] in Hv. apply andb_true_iff in Hv as [_ Hv]. exact Hv.
Qed.

Local Lemma verb_content_safe :
  forall v, verb_content_ok v = true -> verb_safe (verb_ticks v) (pad_verb v) = true.
Proof.
  intros v H. unfold verb_content_ok in H.
  repeat rewrite andb_true_iff in H. destruct H as [[[_ _] _] H]. exact H.
Qed.

(* `ilead` dispatches the reserved characters first, so a row is reached
   at all only because its character is free of them, and it finds
   itself again because the table is unambiguous.  Both come from
   `dconfig_ok`. *)
(* The hypothesis the hyphen adds.  `ilead` claims that character before
   it consults the table, so a row spelled with it is reached from `{` or
   from `}` instead -- see `iscan_marked_close_step`, which is where this
   hypothesis stops travelling. *)
Lemma ilead_dchar :
  forall k txt prev o,
    denabled_of k = true ->
    Ascii.eqb (dchar k) hyphen = false ->
    bunpush o = None ->
    ilead (dchar k) txt prev o
    = IDelim k 0 txt prev false o.
Proof.
  intros k txt prev o Hen Hhy Hup.
  destruct (dreserved_false (dchar k) (dchar_free k))
    as [Hb [Ht [Hlb [Hrb [Hlk [Hrk [Hbg [Hdol [Hpd Hlt]]]]]]]]].
  unfold ilead.
  rewrite Hb, Ht, Hdol, Hpd, Hhy, Hlb, Hlt, Hlk, Hrk, Hbg, Hup.
  assert (Hcolon : Ascii.eqb (dchar k) ":"%char = false).
  { destruct (Ascii.eqb (dchar k) ":"%char) eqn:E; [|reflexivity].
    apply Ascii.eqb_eq in E. subst.
    pose proof (dchar_free k) as Hfree.
    rewrite E in Hfree. discriminate. }
  rewrite Hcolon.
  rewrite (dstyle_of_dchar k Hen). destruct (_ && _)%bool; reflexivity.
Qed.

(* What the hyphen condition promises, with no hypothesis left over: a
   row that says it is bare is reached from the source in its bare
   spelling.  `ilead_dchar` keeps the hypothesis because
   `iscan_marked_close_step` calls it for a braced row too. *)
Local Lemma ilead_dchar_bare :
  forall k txt prev o,
    denabled_of k = true ->
    dsyntax_bare (dsyntax_of k) = true ->
    bunpush o = None ->
    ilead (dchar k) txt prev o = IDelim k 0 txt prev false o.
Proof.
  intros k txt prev o Hen Hb Hup.
  exact (ilead_dchar k txt prev o Hen (dchar_bare_free k Hb) Hup).
Qed.

(* Spelling a token, one character at a time: each of the row's
   characters after the first advances the count, and the token is still
   incomplete throughout because the arithmetic says so. *)
Lemma iscan_chars_delim :
  forall n k extra txt bef o,
    S extra + n <= dwidth k ->
    iscan_str (chars (dchar k) n) (IDelim k extra txt bef false o)
    = IDelim k (extra + n) txt bef false o.
Proof.
  induction n as [|n IH]; intros k extra txt bef o Hn.
  - cbn [chars iscan_str]. replace (extra + 0) with extra by lia. reflexivity.
  - cbn [chars iscan_str istep istep_at].
    replace (Nat.ltb (S extra) (dwidth k)) with true
      by (symmetry; apply Nat.ltb_lt; lia).
    rewrite Ascii.eqb_refl.
    rewrite (IH k (S extra) txt bef o) by lia.
    f_equal. lia.
Qed.

(* A row's whole token, scanned from text: it leaves the token complete
   and its role undecided, which is the state the next byte resolves. *)
Lemma iscan_dtoken :
  forall k txt prev o,
    denabled_of k = true ->
    Ascii.eqb (dchar k) hyphen = false ->
    bunpush o = None ->
    iscan_str (dtoken k) (IText false txt prev o)
    = IDelim k (pred (dwidth k)) txt prev false o.
Proof.
  intros k txt prev o Hen Hhy Hup. unfold dtoken.
  destruct (dwidth k) as [|w] eqn:Ew; [destruct (dwidth_nonzero k Ew)|].
  cbn [chars iscan_str istep istep_at]. rewrite (ilead_dchar k _ _ _ Hen Hhy Hup).
  rewrite (iscan_chars_delim w k 0 txt _ o) by lia.
  cbn [pred]. reflexivity.
Qed.

(* A run of hyphens, scanned from text: `ilead` claims the first and the
   state counts the rest.  This is `iscan_dtoken`'s counterpart for the
   one character the table does not get to dispatch. *)
Local Lemma iscan_dash_run :
  forall n m txt prev o,
    iscan_str (chars hyphen n) (IDash m txt prev o) = IDash (m + n) txt prev o.
Proof.
  induction n as [|n IH]; intros m txt prev o.
  - cbn [chars iscan_str]. rewrite Nat.add_0_r. reflexivity.
  - cbn [chars iscan_str istep istep_at]. unfold idash_step.
    rewrite Ascii.eqb_refl, (IH (S m) txt prev o). f_equal. lia.
Qed.

Local Lemma ilead_hyphen :
  forall txt prev o, ilead hyphen txt prev o = IDash 1 txt prev o.
Proof.
  intros txt prev o. unfold ilead.
  change (is_bslash hyphen) with false.
  change (is_tick hyphen) with false.
  change (Ascii.eqb hyphen dollar) with false.
  change (Ascii.eqb hyphen period) with false.
  rewrite Ascii.eqb_refl. reflexivity.
Qed.

Local Lemma iscan_chars_dash :
  forall n txt prev o,
    iscan_str (chars hyphen (S n)) (IText false txt prev o)
    = IDash (S n) txt prev o.
Proof.
  intros n txt prev o. cbn [chars iscan_str istep istep_at].
  rewrite ilead_hyphen, (iscan_dash_run n 1 txt prev o).
  reflexivity.
Qed.

(* The token then `}`: a marked span closes.  The only hypothesis is that
   the row has a token. *)
Local Lemma iscan_marked_close_step :
  forall k txt prev o o',
    denabled_of k = true ->
    bunpush o = None ->
    sclose k true (flush_text txt o) = Some o' ->
    iscan_str (dtoken k ++ one rbrace) (IText false txt prev o)
    = IText false EmptyString (Some rbrace) o'.
Proof.
  intros k txt prev o o' Hen Hup H.
  pose proof (dwidth_nonzero k) as Hw.
  destruct (Ascii.eqb (dchar k) hyphen) eqn:Hhy.
  { (* the hyphen row: the token was scanned as a run rather than as a
       delimiter, and the `}` gives the whole run back.  Both routes end
       in the same `idelim_resolve`, which is why the hypothesis
       `iscan_dtoken` needed does not travel past this lemma. *)
    apply Ascii.eqb_eq in Hhy.
    destruct (dwidth k) as [|w] eqn:Ew; [lia|].
    unfold dtoken. rewrite Ew, Hhy.
    rewrite iscan_str_app, (iscan_chars_dash w txt prev o).
    unfold one. cbn [iscan_str istep istep_at]. unfold idash_step.
    change (Ascii.eqb rbrace hyphen) with false.
    rewrite Ascii.eqb_refl, <- Hhy, (dstyle_of_dchar k Hen), Ew.
    rewrite Nat.leb_refl, Nat.sub_diag. tred.
    assert (Ezero : typography_dashes 0 = EmptyString).
    { unfold typography_dashes. destruct smart_typography; reflexivity. }
    rewrite Ezero, (append_empty_r txt).
    unfold idelim_resolve. rewrite !oclose_guard. tred. sem_flush.
    rewrite Bool.orb_true_r, H. reflexivity. }
  rewrite iscan_str_app, (iscan_dtoken k txt prev o Hen Hhy Hup).
  unfold one. cbn [iscan_str istep istep_at].
  replace (Nat.ltb (S (pred (dwidth k))) (dwidth k)) with false
    by (symmetry; apply Nat.ltb_ge; lia).
  rewrite Ascii.eqb_refl. unfold idelim_resolve. rewrite !oclose_guard. tred. sem_flush.
  rewrite Bool.orb_true_r, H. reflexivity.
Qed.

(* Where the token lemmas get their hypothesis: a marked close runs with
   the delimiter's own frame on top, which is not a bracket, and nothing
   the close does before the token can turn it into one. *)
Local Lemma bunpush_oemit_all_opush :
  forall ns k m cm open o,
    bunpush (oemit_all ns (opush_at k m cm open o)) = None.
Proof.
  intros ns k m cm open [out stk word]. unfold opush_at; cbn [os_out os_stk].
  rewrite oemit_all_frame. reflexivity.
Qed.

Local Lemma bunpush_flush :
  forall txt o, bunpush o = None -> bunpush (flush_text txt o) = None.
Proof.
  intros txt [out [|[[k|im|im|nm] m open [|n l]] stk] word] H;
    unfold flush_text, flush_text_at;
    destruct (nonempty_str txt); solve [exact H | reflexivity | discriminate H].
Qed.

Local Lemma iscan_marked_flush :
  forall k cm tail txt prev before open base,
    denabled_of k = true ->
    (nonempty before || nonempty_str txt)%bool = true ->
    exists p,
      iscan_str (marked_close k tail)
        (IText false txt prev
           (oemit_all before (opush_at k true cm open base)))
      = iscan_str (marked_close k tail)
          (IText false EmptyString p
            (flush_text txt
               (oemit_all before (opush_at k true cm open base)))).
Proof.
  intros k cm tail txt prev before open base Hen Hne.
  assert (Hclose : exists o',
    sclose k true
      (flush_text txt (oemit_all before (opush_at k true cm open base)))
    = Some o').
  { destruct (nonempty_str txt) eqn:Htxt.
    - exists (oemit (mk (dnode k (before ++ [mk (Str txt)])%list)) base).
      unfold flush_text, flush_text_at. rewrite Htxt.
      change (sclose k true
                (oemit_all [mk (Str txt)]
                  (oemit_all before (opush_at k true cm open base)))
              = Some
                  (oemit (mk (dnode k (before ++ [mk (Str txt)])%list))
                    base)).
      rewrite <- (oemit_all_app before [mk (Str txt)]
                    (opush_at k true cm open base)).
      cbn [oemit_all]. unfold sclose.
      apply (@oclose_oemit_all_marked T semantic_pos k cm _ open (Spot 0 0) base).
      destruct before; reflexivity.
    - apply orb_true_iff in Hne as [Hbefore|Htxt']; [|discriminate].
      exists (oemit (mk (dnode k before)) base).
      unfold flush_text, flush_text_at. rewrite Htxt. unfold sclose.
      apply (@oclose_oemit_all_marked T semantic_pos k cm before open
               (Spot 0 0) base), Hbefore. }
  destruct Hclose as [o' Hclose]. exists prev.
  unfold marked_close. rewrite <- append_assoc.
  rewrite !(iscan_str_app (dtoken k ++ one rbrace) tail).
  pose proof (bunpush_oemit_all_opush before k true cm open base) as Hup.
  rewrite (iscan_marked_close_step k txt prev
             (oemit_all before (opush_at k true cm open base)) o' Hen Hup Hclose).
  rewrite (iscan_marked_close_step k EmptyString prev
             (flush_text txt (oemit_all before (opush_at k true cm open base))) o' Hen
             (bunpush_flush txt _ Hup)
             ltac:(cbn [flush_text flush_text_at]; exact Hclose)).
  reflexivity.
Qed.

(* The rest of a marked open's token.  The counterpart of
   `iscan_chars_delim`, and it stops one byte earlier than the push does:
   a marked opener's role is settled but the side its decay takes is
   not. *)
Lemma iscan_chars_marked :
  forall n k extra txt o,
    S extra + n <= dwidth k ->
    iscan_str (chars (dchar k) n) (idelim_marked k extra txt o)
    = idelim_marked k (extra + n) txt o.
Proof.
  induction n as [|n IH]; intros k extra txt o Hn.
  - cbn [chars iscan_str]. rewrite Nat.add_0_r. reflexivity.
  - unfold idelim_marked at 1.
    cbn [chars iscan_str istep istep_at].
    replace (Nat.ltb (S extra) (dwidth k)) with true
      by (symmetry; apply Nat.ltb_lt; lia).
    rewrite Ascii.eqb_refl.
    rewrite (IH k (S extra) txt o) by lia.
    f_equal. lia.
Qed.

Lemma iscan_marked_open :
  forall d txt prev o,
    denabled_of d = true ->
    iscan_str (marked_open d) (IText false txt prev o)
    = idelim_marked d (pred (dwidth d)) txt o.
Proof.
  intros d txt prev o Hen. unfold marked_open, dtoken.
  destruct (dwidth d) as [|w] eqn:Ew;
    [destruct (dwidth_nonzero d Ew)|].
  unfold one. cbn [chars append iscan_str istep istep_at].
  change (ilead lbrace txt prev o) with (IBrace txt prev o).
  cbn [istep istep_at]. unfold ibrace_step, ibrace_step_at.
  rewrite (dstyle_of_dchar d Hen).
  rewrite (iscan_chars_marked w d 0 txt o) by lia.
  cbn [pred]. reflexivity.
Qed.

(* And the byte that follows it, which is where the push happens: it
   chooses the side the scope's decay would take, and then is dispatched
   into the scope as any byte would be.  A caller whose scope closes never
   learns which side it was, so the bit is existential here -- the only
   thing the chain below needs is that the scope is open. *)
Local Lemma iscan_marked_open_app :
  forall d s txt prev o,
    denabled_of d = true -> nonempty_str s = true ->
    exists cm open,
      iscan_str (marked_open d ++ s) (IText false txt prev o)
      = iscan_str s
          (IText false EmptyString (Some (dchar d))
            (opush_at d true cm open (flush_text txt o))).
Proof.
  intros d [|c s] txt prev o Hen Hne; [discriminate|].
  exists (Ascii.eqb c rbrace). eexists.
  rewrite iscan_str_app, (iscan_marked_open d txt prev o Hen).
  destruct (dwidth d) as [|w] eqn:Ew; [destruct (dwidth_nonzero d Ew)|].
  unfold idelim_marked. cbn [pred iscan_str istep istep_at].
  rewrite Ew, Nat.ltb_irrefl. unfold oopen_marked. reflexivity.
Qed.

Local Lemma iscan_marked_close_emit :
  forall d cm tail ns open base p,
    denabled_of d = true ->
    nonempty ns = true ->
    iscan_str (marked_close d tail)
      (IText false EmptyString p
         (oemit_all ns (opush_at d true cm open base)))
    = iscan_str tail
        (IText false EmptyString (Some rbrace)
          (oemit (mk (dnode d ns)) base)).
Proof.
  intros d cm tail ns open base p Hen Hne. unfold marked_close.
  rewrite <- append_assoc, iscan_str_app.
  rewrite (iscan_marked_close_step d EmptyString p
             (oemit_all ns (opush_at d true cm open base))
             (oemit (mk (dnode d ns)) base)
             Hen
             (bunpush_oemit_all_opush ns d true cm open base)
             ltac:(cbn [flush_text flush_text_at];
                   apply (@oclose_oemit_all_marked T semantic_pos d cm ns open
                            (Spot 0 0) base), Hne)).
  reflexivity.
Qed.

Local Lemma iscan_after_verb_nontick :
  forall s n body o,
    nonempty_str s = true -> starts_tick s = false ->
    after_verb_next s = true ->
    iscan_str s (IVerb n n body VVerb o)
    = iscan_str s
        (IText false EmptyString (Some tick)
          (oemit (mk (Verbatim (trim_verb body))) o)).
Proof.
  intros [|c s] n body o Hne Htick Hnext; [discriminate|].
  cbn [starts_tick] in Htick. cbn [iscan_str istep istep_at]. rewrite Htick.
  rewrite nat_eqb_refl.
  cbn [after_verb_next] in Hnext.
  destruct (Ascii.eqb c lbrace) eqn:Hb; [|reflexivity].
  (* the raw mode and the brace it stands in for agree from the next byte
     on: the mode's own failure path is `ibrace_step`, which is that
     byte's ordinary dispatch *)
  destruct s as [|d s]; [discriminate|].
  cbn [iscan_str istep istep_at].
  apply Ascii.eqb_eq in Hb; subst c.
  cbn [vkind_verb andb].
  unfold istep at 1; cbn [istep_at]; unfold iraw_step_at.
  rewrite Hnext, andb_false_r. unfold ilead; cbn. reflexivity.
Qed.

Local Lemma escape_str_starts_nontick :
  forall s, nonempty_str s = true -> starts_tick (escape_str s) = false.
Proof.
  intros [|c s] H; [discriminate|]. unfold escape_str; cbn [escape_from bare_ok negb]; rewrite andb_true_r.
  destruct (needs_escape c) eqn:Hc; [reflexivity|].
  cbn [starts_tick]. destruct (is_tick c) eqn:Ht; [|reflexivity].
  rewrite (needs_escape_tick c Ht) in Hc. discriminate.
Qed.

(* `after_verb_next` asks about the brace and nothing else, so anything
   that cannot start with one satisfies it outright.  That is every
   canonical constituent but a delimiter, whose brace is its opener. *)
Local Definition starts_brace (s : string) : bool :=
  match s with String c _ => Ascii.eqb c lbrace | EmptyString => false end.

Local Lemma after_verb_next_nonbrace :
  forall s, starts_brace s = false -> after_verb_next s = true.
Proof.
  intros [|c s] H; [reflexivity|].
  cbn [after_verb_next starts_brace] in H |- *. rewrite H. reflexivity.
Qed.

Local Lemma nonempty_str_app_l :
  forall a b, nonempty_str b = true -> nonempty_str (a ++ b)%string = true.
Proof. intros [|x a] b H; [exact H | reflexivity]. Qed.

Local Lemma nonempty_str_app_r :
  forall a b, nonempty_str a = true -> nonempty_str (a ++ b)%string = true.
Proof. intros [|x a] b H; [discriminate | reflexivity]. Qed.

Local Lemma starts_brace_app_l :
  forall a b, nonempty_str a = true -> starts_brace (a ++ b) = starts_brace a.
Proof. intros [|c a] b H; [discriminate|reflexivity]. Qed.

Local Lemma escape_str_starts_nonbrace :
  forall s, starts_brace (escape_str s) = false.
Proof.
  intros [|c s]; [reflexivity|]. unfold escape_str; cbn [escape_from bare_ok negb]; rewrite andb_true_r.
  destruct (needs_escape c) eqn:Hc; [reflexivity|].
  cbn [starts_brace]. destruct (Ascii.eqb c lbrace) eqn:Hb; [|reflexivity].
  apply Ascii.eqb_eq in Hb; subst c.
  rewrite needs_escape_lbrace in Hc. discriminate.
Qed.

Local Lemma escape_str_nonempty :
  forall s, nonempty_str s = true -> nonempty_str (escape_str s) = true.
Proof.
  intros [|c s] H; [discriminate|]. unfold escape_str; cbn [escape_from bare_ok negb]; rewrite andb_true_r.
  destruct (needs_escape c); reflexivity.
Qed.

(* The two things a closer has to be for the scope machinery: nonempty,
   which is the row having a token, and not starting with a backtick,
   which is its character being free of the ones the scanner claims. *)
Local Lemma marked_close_nonempty :
  forall k tail, nonempty_str (marked_close k tail) = true.
Proof.
  intros k tail. pose proof (dtoken_nonempty k) as H.
  unfold marked_close. destruct (dtoken k); [discriminate|reflexivity].
Qed.

Local Lemma marked_close_starts_nontick :
  forall k tail, starts_tick (marked_close k tail) = false.
Proof.
  intros k tail.
  destruct (dreserved_false (dchar k) (dchar_free k)) as [_ [Ht _]].
  unfold marked_close, dtoken.
  destruct (dwidth k) as [|w] eqn:E; [destruct (dwidth_nonzero k E)|].
  cbn [chars append starts_tick]. exact Ht.
Qed.

(* ...and it is not a brace either, since a row's character is not
   reserved -- which is what a verbatim before the closer needs. *)
Local Lemma marked_close_after_verb :
  forall k tail, after_verb_next (marked_close k tail) = true.
Proof.
  intros k tail. apply after_verb_next_nonbrace.
  unfold marked_close, dtoken.
  destruct (dwidth k) as [|w] eqn:Ew;
    [pose proof (dtoken_nonempty k) as Hn; unfold dtoken in Hn;
     rewrite Ew in Hn; discriminate|].
  cbn [chars append starts_brace].
  destruct (dreserved_false (dchar k) (dchar_free k))
    as [_ [_ [Hlb _]]].
  exact Hlb.
Qed.

(* What a verbatim needs of whatever follows it: a nonempty continuation
   that does not start with a backtick, or its closing run would grow.
   Stated over an arbitrary closer, since a marked delimiter and a
   bracket both supply one. *)
(*
Scanning a link
---------------

The bracket analogues of `iscan_marked_open` and
`iscan_marked_close_emit`.  The close is longer than a delimiter's
because it spans three dispatches -- the `]`, the `(` and the balanced
`)` -- with the destination scanned as escaped text in between. *)

(* One lemma for both openers: the `!` is a separate dispatch, but it
   only decides which frame is pushed. *)
(* Whether a `[` read in text mode from this state is the second bracket
   of a wikilink: `ilead`'s guard, as a predicate on the state. *)
Local Definition wiki_opens (txt : string) (prev : option ascii) (o : ostate) : bool :=
  (note_pos txt prev && wikilinks_enabled
   && match bunpush o with Some _ => true | None => false end)%bool.

Local Lemma iscan_bracket_open :
  forall image txt prev o,
    (image || negb (wiki_opens txt prev o))%bool = true ->
    iscan_str (bracket_open image) (IText false txt prev o)
    = IText false EmptyString (Some lbrack) (bpush image (flush_text txt o)).
Proof.
  intros [] txt prev o H; [reflexivity|].
  cbn [orb] in H. apply negb_true_iff in H. unfold wiki_opens in H.
  cbn [bracket_open one iscan_str istep istep_at]. unfold ilead.
  change (is_bslash lbrack) with false.
  change (is_tick lbrack) with false.
  change (Ascii.eqb lbrack dollar) with false.
  change (Ascii.eqb lbrack period) with false.
  change (Ascii.eqb lbrack hyphen) with false.
  change (Ascii.eqb lbrack lbrace) with false.
  change (Ascii.eqb lbrack bang) with false.
  change (Ascii.eqb lbrack lt) with false.
  change (Ascii.eqb lbrack lbrack) with true.
  cbn iota beta.
  destruct (note_pos txt prev && wikilinks_enabled)%bool; [|reflexivity].
  destruct (bunpush o); [discriminate H|reflexivity].
Qed.

(* Once anything has been emitted into the scope, no bracket can be
   taken back, so no `[` there opens a wikilink. *)
Local Lemma wiki_opens_oemit_all :
  forall txt prev before O,
    nonempty before = true ->
    wiki_opens txt prev (oemit_all before O) = false.
Proof.
  intros txt prev [|n ns] O H; [discriminate H|].
  assert (Hem : forall m o, bunpush (oemit m o) = None).
  { intros m [out [|[[k|im|im|nm] mk op fo] stk] word]; reflexivity. }
  assert (Hall : forall ms o,
    bunpush o = None -> bunpush (oemit_all ms o) = None).
  { induction ms as [|m ms IH]; intros o Ho; [exact Ho|].
    cbn [oemit_all]. apply IH, Hem. }
  unfold wiki_opens. cbn [oemit_all]. rewrite (Hall ns _ (Hem n O)).
  apply andb_false_r.
Qed.

Local Lemma wiki_opens_text :
  forall txt prev o, nonempty_str txt = true -> wiki_opens txt prev o = false.
Proof. intros txt prev o H. unfold wiki_opens, note_pos; tred. rewrite H. reflexivity. Qed.

Local Lemma wiki_opens_top :
  forall txt prev out w, wiki_opens txt prev (OState out [] w) = false.
Proof. intros txt prev out w. unfold wiki_opens. cbn [bunpush os_stk]. apply andb_false_r. Qed.

Local Lemma wiki_opens_opush :
  forall txt prev ns k m cm open o,
    wiki_opens txt prev (oemit_all ns (opush_at k m cm open o)) = false.
Proof.
  intros txt prev ns k m cm open o. unfold wiki_opens.
  rewrite bunpush_oemit_all_opush. apply andb_false_r.
Qed.

(* What a link's `bracket_kids_ok` is for: its text never begins where a
   `[` would open a wikilink. *)
Local Lemma wiki_opens_bracket_kids :
  forall kids txt prev o,
    bracket_kids_ok kids = true -> cis_lbrack_head kids = true ->
    wiki_opens txt prev o = false.
Proof.
  intros kids txt prev o Hk Hh. unfold bracket_kids_ok in Hk.
  rewrite Hh, andb_true_r in Hk. apply negb_true_iff in Hk.
  unfold wiki_opens. rewrite Hk, andb_false_r. reflexivity.
Qed.

Local Lemma bclose_flush_bpush :
  forall txt image before base,
    bclose (flush_text txt (oemit_all before (bpush image base)))
    = Some (if nonempty_str txt
            then (before ++ [mk (Str txt)])%list else before, image,
            null_span, base).
Proof.
  intros txt image before base. unfold flush_text, flush_text_at.
  destruct (nonempty_str txt).
  - replace (oemit (mk (Str txt)) (oemit_all before (bpush image base)))
      with (oemit_all [mk (Str txt)] (oemit_all before (bpush image base)))
      by reflexivity.
    rewrite <- (oemit_all_app before [mk (Str txt)] (bpush image base)).
    apply bclose_oemit_all.
  - apply bclose_oemit_all.
Qed.

Local Lemma drop_nl_no_nl : forall s, no_nl s = true -> drop_nl s = s.
Proof.
  induction s as [|c s IH]; intros H; [reflexivity|].
  cbn [no_nl] in H. apply andb_true_iff in H as [Hc H].
  apply negb_true_iff in Hc. cbn [drop_nl].
  change nl_char with "010"%char. rewrite Hc, (IH H). reflexivity.
Qed.

(* The destination is escaped text, and reads back the way escaped text
   does: `needs_escape_dest` claims every byte the mode dispatches on,
   and its escapes decode because each such byte is punctuation. *)
Local Lemma iscan_dest_escape :
  forall s kids image open depth dst sh o,
    iscan_str (escape_dest s) (IDest kids image open false depth dst sh o)
    = IDest kids image open false depth (dst ++ s)%string
        (iscan_str (escape_dest s) sh) o.
Proof.
  induction s as [|c s IH]; intros kids image open depth dst sh o;
    cbn [escape_dest]; [rewrite append_empty_r; reflexivity|].
  assert (Hsplit : forall t, (dst ++ String c t)%string
                             = ((dst ++ one c) ++ t)%string).
  { intro t. rewrite (append_assoc dst (one c) t). reflexivity. }
  destruct (needs_escape_dest c) eqn:Hc.
  - pose proof (needs_escape_dest_punct c Hc) as Hp.
    cbn [iscan_str istep istep_at]. change (is_bslash "\"%char) with true.
    cbn [istep istep_at]. rewrite Hp, IH, Hsplit. reflexivity.
  - assert (Hbs : is_bslash c = false).
    { destruct (is_bslash c) eqn:E; [|reflexivity].
      unfold needs_escape_dest, needs_escape in Hc.
      apply Ascii.eqb_eq in E. subst c. discriminate. }
    assert (Hlp : Ascii.eqb c lparen = false).
    { destruct (Ascii.eqb c lparen) eqn:E; [|reflexivity].
      unfold needs_escape_dest in Hc. rewrite E in Hc.
      rewrite orb_true_r in Hc. discriminate. }
    assert (Hrp : Ascii.eqb c rparen = false).
    { destruct (Ascii.eqb c rparen) eqn:E; [|reflexivity].
      unfold needs_escape_dest in Hc. rewrite E in Hc.
      rewrite orb_true_r in Hc. discriminate. }
    cbn [iscan_str istep istep_at]. rewrite Hbs, Hlp, Hrp, IH, Hsplit. reflexivity.
Qed.

Local Lemma istep_rbrack_close :
  forall txt prev o,
    tag_close (flush_text txt o) = None ->
    istep rbrack (IText false txt prev o) = IClosed txt o.
Proof.
  intros txt prev o H. cbn [istep istep_at]. unfold ilead.
  change (is_bslash rbrack) with false.
  change (is_tick rbrack) with false.
  change (Ascii.eqb rbrack lbrace) with false.
  change (Ascii.eqb rbrack bang) with false.
  change (Ascii.eqb rbrack lbrack) with false.
  change (Ascii.eqb rbrack rbrack) with true.
  cbn iota beta. tred. sem_flush. rewrite H.
  destruct tags_enabled; reflexivity.
Qed.

(* Inside a plain bracket no `]` closes a named one. *)
Local Lemma tag_close_bpush :
  forall txt before image base,
    tag_close (flush_text txt (oemit_all before (bpush image base))) = None.
Proof.
  intros txt before image [out stk word]. apply tag_close_flush.
  unfold bpush. rewrite oemit_all_frame. reflexivity.
Qed.

(* ...and the byte after it is what closes the bracket. *)
Local Lemma istep_lbrack_ref :
  forall txt o kids image open o',
    bclose (flush_text txt o) = Some (kids, image, open, o') ->
    istep lbrack (IClosed txt o) =
      IReference kids image open EmptyString o'.
Proof.
  intros txt o kids image open o' H. cbn [istep istep_at].
  change (Ascii.eqb lbrack lparen) with false.
  change (Ascii.eqb lbrack lbrack) with true. cbn [orb]; tred.
  sem_flush. rewrite H. reflexivity.
Qed.

Local Lemma istep_lparen_dest :
  forall txt o kids image open o',
    bclose (flush_text txt o) = Some (kids, image, open, o') ->
    istep lparen (IClosed txt o)
    = IDest kids image open false 0 EmptyString
        (idest_open kids image open o') o'.
Proof.
  intros txt o kids image open o' H. cbn [istep istep_at].
  change (Ascii.eqb lparen lparen) with true. cbn [orb]; tred.
  sem_flush. rewrite H. reflexivity.
Qed.

Local Lemma iscan_link_close :
  forall dst tail ns image base p,
    no_nl dst = true ->
    iscan_str (link_close dst tail)
      (IText false EmptyString p (oemit_all ns (bpush image base)))
    = iscan_str tail
        (IText false EmptyString (Some rparen)
          (oemit (mk (bnode image ns (Direct dst))) base)).
Proof.
  intros dst tail ns image base p Hnl. unfold link_close.
  cbn [iscan_str]. rewrite (istep_rbrack_close EmptyString p _ (tag_close_bpush _ _ _ _)).
  rewrite (istep_lparen_dest EmptyString _ ns image
             (null_span) base
             (bclose_flush_bpush EmptyString image ns base)).
  rewrite iscan_str_app, iscan_dest_escape.
  change ((EmptyString ++ dst)%string) with dst.
  cbn [iscan_str istep istep_at].
  change (is_bslash rparen) with false.
  change (Ascii.eqb rparen lparen) with false.
  change (Ascii.eqb rparen rparen) with true.
  tred.
  rewrite (drop_nl_no_nl dst Hnl). reflexivity.
Qed.

(* The bracket's flush law, and it needs no precondition: a `]` closes an
   empty label as happily as a full one, which is what `empty_ok` below
   records and what makes `[](u)` representable. *)
Local Lemma iscan_bracket_flush :
  forall dst tail txt prev image before base,
    exists p,
      iscan_str (link_close dst tail)
        (IText false txt prev (oemit_all before (bpush image base)))
      = iscan_str (link_close dst tail)
          (IText false EmptyString p
            (flush_text txt (oemit_all before (bpush image base)))).
Proof.
  intros dst tail txt prev image before base. exists (Some lbrack).
  pose (ns := if nonempty_str txt
              then (before ++ [mk (Str txt)])%list else before).
  unfold link_close. cbn [iscan_str].
  rewrite (istep_rbrack_close txt prev _ (tag_close_bpush _ _ _ _)).
  rewrite (istep_rbrack_close EmptyString _ _);
    [|apply tag_close_flush, tag_close_bpush].
  cbn [iscan_str].
  rewrite (istep_lparen_dest txt _ ns image
             (null_span) base
             (bclose_flush_bpush txt image before base)).
  rewrite (istep_lparen_dest EmptyString _ ns image
             (null_span) base);
    [reflexivity|].
  cbn [flush_text flush_text_at nonempty_str]. rewrite ?imk_semantic.
  apply (bclose_flush_bpush txt image before base).
Qed.

Local Lemma link_close_app :
  forall dst t, (link_close dst EmptyString ++ t)%string = link_close dst t.
Proof.
  intros dst t. unfold link_close. cbn [append].
  rewrite append_assoc. cbn [append]. reflexivity.
Qed.

(*
Scanning a named bracket
------------------------

The opener is the symbol state's alias, which a `[` turns into a frame;
the closer is the `]` alone, which closes that frame at once.
*)

(* The semantic frame does not record where the opener started. *)
Local Lemma tag_push_start :
  forall name s1 s2 o, tag_push name s1 o = tag_push name s2 o.
Proof. reflexivity. Qed.

Local Lemma iscan_symbol_alias :
  forall name alias txt sh o,
    Line.str_forallb symbol_char name = true ->
    iscan_str name (ISymbol alias txt sh o)
    = ISymbol (alias ++ name) txt (iscan_str name sh) o.
Proof.
  induction name as [|c name IH]; intros alias txt sh o H.
  - cbn [iscan_str]. rewrite append_empty_r. reflexivity.
  - cbn [Line.str_forallb] in H. apply andb_true_iff in H as [Hc H].
    cbn [iscan_str istep istep_at]. unfold isymbol_step. rewrite Hc. tred.
    change (istep_at inline_attrs_enabled c sh) with (istep c sh).
    rewrite IH by exact H. rewrite append_assoc. reflexivity.
Qed.

Local Lemma iscan_tag_open :
  forall name txt prev o,
    tags_enabled = true -> tag_name_ok name = true ->
    tag_may_follow txt = true ->
    iscan_str (tag_open name) (IText false txt prev o)
    = IText false EmptyString (Some lbrack)
        (tag_push name (Spot 0 0) (flush_text txt o)).
Proof.
  intros [|c name] txt prev o Ht Hn Hf; [discriminate|].
  unfold tag_name_ok in Hn. apply andb_true_iff in Hn as [_ Hs].
  unfold tag_open. cbn [iscan_str istep istep_at]. unfold ilead.
  change (is_bslash ":"%char) with false. change (is_tick ":"%char) with false.
  change (Ascii.eqb ":" dollar) with false. change (Ascii.eqb ":" period) with false.
  change (Ascii.eqb ":" hyphen) with false. change (Ascii.eqb ":" lbrace) with false.
  change (Ascii.eqb ":" bang) with false. change (Ascii.eqb ":" lt) with false.
  change (Ascii.eqb ":" ":") with true. cbn iota beta.
  rewrite iscan_str_app, (iscan_symbol_alias (String c name) _ _ _ _ Hs).
  cbn [append one iscan_str istep istep_at]. unfold isymbol_step.
  change (symbol_char lbrack) with false. change (Ascii.eqb lbrack ":") with false.
  change (Ascii.eqb lbrack lbrack) with true. tred. rewrite Ht, Hf. cbn [andb nonempty_str].
  sem_flush. reflexivity.
Qed.

Local Lemma iscan_tag_close :
  forall name tail ns base p,
    tags_enabled = true ->
    iscan_str (String rbrack tail)
      (IText false EmptyString p (oemit_all ns (tag_push name (Spot 0 0) base)))
    = iscan_str tail
        (IText false EmptyString (Some rbrack) (oemit (mk (Span name ns)) base)).
Proof.
  intros name tail ns base p Ht. cbn [iscan_str istep istep_at]. unfold ilead.
  change (is_bslash rbrack) with false. change (is_tick rbrack) with false.
  change (Ascii.eqb rbrack dollar) with false. change (Ascii.eqb rbrack period) with false.
  change (Ascii.eqb rbrack hyphen) with false. change (Ascii.eqb rbrack lbrace) with false.
  change (Ascii.eqb rbrack bang) with false. change (Ascii.eqb rbrack lt) with false.
  change (Ascii.eqb rbrack ":") with false.
  change (Ascii.eqb rbrack lbrack) with false. change (Ascii.eqb rbrack rbrack) with true.
  cbn iota beta. tred. rewrite Ht. sem_flush. cbn [flush_text flush_text_at nonempty_str].
  rewrite tag_close_oemit_all. rewrite ?imk_semantic. reflexivity.
Qed.

Local Lemma iscan_tag_flush :
  forall name tail txt prev before base,
    tags_enabled = true ->
    exists p,
      iscan_str (String rbrack tail)
        (IText false txt prev (oemit_all before (tag_push name (Spot 0 0) base)))
      = iscan_str (String rbrack tail)
          (IText false EmptyString p
            (flush_text txt (oemit_all before (tag_push name (Spot 0 0) base)))).
Proof.
  intros name tail txt prev before base Ht. exists (Some lbrack).
  set (Y := oemit_all before (tag_push name (Spot 0 0) base)).
  assert (Hs : exists r, tag_close (flush_text txt Y) = Some r).
  { unfold Y, flush_text, flush_text_at. destruct (nonempty_str txt).
    - change (oemit ?n (oemit_all ?l ?z)) with (oemit_all [n] (oemit_all l z)).
      rewrite <- oemit_all_app, tag_close_oemit_all. eexists. reflexivity.
    - rewrite tag_close_oemit_all. eexists. reflexivity. }
  destruct Hs as [r Er].
  cbn [iscan_str istep istep_at]. unfold ilead.
  change (is_bslash rbrack) with false. change (is_tick rbrack) with false.
  change (Ascii.eqb rbrack dollar) with false. change (Ascii.eqb rbrack period) with false.
  change (Ascii.eqb rbrack hyphen) with false. change (Ascii.eqb rbrack lbrace) with false.
  change (Ascii.eqb rbrack bang) with false. change (Ascii.eqb rbrack lt) with false.
  change (Ascii.eqb rbrack ":") with false.
  change (Ascii.eqb rbrack lbrack) with false. change (Ascii.eqb rbrack rbrack) with true.
  cbn iota beta. tred. rewrite Ht. sem_flush.
  change (flush_text "" (flush_text txt Y)) with (flush_text txt Y).
  rewrite Er. reflexivity.
Qed.

(* A named bracket is never taken back, so no `[` right inside one opens
   a wikilink. *)
Local Lemma wiki_opens_tag_push :
  forall txt prev name start o, wiki_opens txt prev (tag_push name start o) = false.
Proof. intros txt prev name start [out stk word]. unfold wiki_opens. apply andb_false_r. Qed.

(*
Scanning a reference link
-------------------------

The same three dispatches as a direct link's closer, with `[`, the label
and `]` in place of `(`, the destination and `)`.  The label is easier:
the mode escapes nothing and dispatches on nothing but `]`, so the whole
of it goes in one induction.
*)

Local Lemma iscan_ref_label :
  forall label kids image open acc o,
    no_char rbrack label = true ->
    iscan_str label (IReference kids image open acc o)
    = IReference kids image open (acc ++ label)%string o.
Proof.
  induction label as [|c label IH]; intros kids image open acc o H;
    [rewrite append_empty_r; reflexivity|].
  cbn [no_char] in H. apply andb_true_iff in H as [Hc H].
  apply negb_true_iff in Hc.
  cbn [iscan_str istep istep_at]. rewrite Hc, (IH _ _ _ _ _ H).
  rewrite append_assoc. reflexivity.
Qed.

Local Lemma iscan_ref_close :
  forall label tail ns image base p,
    nonempty_str label = true ->
    no_char rbrack label = true ->
    iscan_str (ref_close label tail)
      (IText false EmptyString p (oemit_all ns (bpush image base)))
    = iscan_str tail
        (IText false EmptyString (Some rbrack)
          (oemit (mk (bnode image ns (Reference (normalize_label label)))) base)).
Proof.
  intros label tail ns image base p Hne Hbr. unfold ref_close.
  cbn [iscan_str]. rewrite (istep_rbrack_close EmptyString p _ (tag_close_bpush _ _ _ _)).
  rewrite (istep_lbrack_ref EmptyString _ ns image
             (null_span) base
             (bclose_flush_bpush EmptyString image ns base)).
  rewrite iscan_str_app,
    (iscan_ref_label label ns image
      (null_span)
      EmptyString _ Hbr).
  change ((EmptyString ++ label)%string) with label.
  cbn [iscan_str istep istep_at]. change (Ascii.eqb rbrack rbrack) with true.
  destruct label as [|c label']; [discriminate Hne|reflexivity].
Qed.

(* The flush law, as for a direct link and by the same `]` dispatch. *)
Local Lemma iscan_ref_flush :
  forall label tail txt prev image before base,
    exists p,
      iscan_str (ref_close label tail)
        (IText false txt prev (oemit_all before (bpush image base)))
      = iscan_str (ref_close label tail)
          (IText false EmptyString p
            (flush_text txt (oemit_all before (bpush image base)))).
Proof.
  intros label tail txt prev image before base. exists (Some lbrack).
  pose (ns := if nonempty_str txt
              then (before ++ [mk (Str txt)])%list else before).
  unfold ref_close. cbn [iscan_str].
  rewrite (istep_rbrack_close txt prev _ (tag_close_bpush _ _ _ _)).
  rewrite (istep_rbrack_close EmptyString _ _);
    [|apply tag_close_flush, tag_close_bpush].
  cbn [iscan_str].
  rewrite (istep_lbrack_ref txt _ ns image
             (null_span) base
             (bclose_flush_bpush txt image before base)).
  rewrite (istep_lbrack_ref EmptyString _ ns image
             (null_span) base);
    [reflexivity|].
  cbn [flush_text flush_text_at nonempty_str]. rewrite ?imk_semantic.
  apply (bclose_flush_bpush txt image before base).
Qed.

(* A canonical note label reaches its closing bracket without leaving an
   escape pending.  Backslashes are consumed in pairs with the following
   byte, and both bytes remain in the label. *)
Local Lemma iscan_note_label :
  forall label tail esc image acc open o,
    note_label_safe_from esc label = true ->
    iscan_str (label ++ one rbrack ++ tail)
      (INote esc image acc open o)
    = iscan_str tail
        (IText false EmptyString (Some rbrack)
          (oemit (mk (FootnoteReference
            (normalize_label
              (acc ++ (if esc then one bslash else EmptyString) ++ label))))
            (ospan_bang image o))).
Proof.
  induction label as [|c label IH]; intros tail esc image acc open o Hsafe.
  - cbn [note_label_safe_from] in Hsafe. destruct esc; [discriminate|].
    cbn [append iscan_str istep istep_at inote_step]. tred.
    change (is_bslash rbrack) with false.
    change (Ascii.eqb rbrack rbrack) with true.
    rewrite !append_empty_r. reflexivity.
  - cbn [note_label_safe_from] in Hsafe.
    cbn [append iscan_str istep istep_at inote_step]. tred.
    destruct esc.
    + cbn [inote_step]. tred.
      rewrite (IH tail false image (acc ++ one bslash ++ one c)%string open o
                 Hsafe).
      rewrite !append_assoc. reflexivity.
    + destruct (Ascii.eqb c rbrack) eqn:Hclose; [discriminate|].
      destruct (is_bslash c) eqn:Hslash.
      * unfold is_bslash in Hslash. apply Ascii.eqb_eq in Hslash. subst c.
        cbn [inote_step]. tred.
        rewrite is_bslash_bslash.
        rewrite (IH tail true image acc open o Hsafe).
        cbn [append]. reflexivity.
      * cbn [inote_step]. tred. rewrite Hslash, Hclose.
        rewrite (IH tail false image (acc ++ one c)%string open o Hsafe).
        rewrite !append_assoc. reflexivity.
Qed.

Local Lemma iscan_note_text :
  forall label tail txt prev o,
    notes_enabled = true ->
    note_label_safe label = true ->
    wiki_opens txt prev o = false ->
    iscan_str (note_text label ++ tail)
      (IText false txt prev o)
    = iscan_str tail
        (IText false EmptyString (Some rbrack)
          (oemit (mk (FootnoteReference (normalize_label label)))
            (flush_text txt o))).
Proof.
  intros label tail txt prev o Hnotes Hsafe Hw.
  replace (note_text label ++ tail)%string with
    (bracket_open false ++ (one hat ++ (label ++ one rbrack ++ tail)))%string
    by (unfold note_text, bracket_open; cbn [append];
        rewrite append_assoc; reflexivity).
  rewrite iscan_str_app, iscan_bracket_open by (rewrite Hw; reflexivity).
  rewrite iscan_str_app. cbn [one iscan_str istep istep_at].
  unfold ilead.
  change (is_bslash hat) with false.
  change (is_tick hat) with false.
  change (Ascii.eqb hat dollar) with false.
  change (Ascii.eqb hat period) with false.
  change (Ascii.eqb hat hyphen) with false.
  change (Ascii.eqb hat lbrace) with false.
  change (Ascii.eqb hat bang) with false.
  change (Ascii.eqb hat lt) with false.
  change (Ascii.eqb hat ":"%char) with false.
  change (Ascii.eqb hat lbrack) with false.
  change (Ascii.eqb hat rbrack) with false.
  change (Ascii.eqb hat hat && note_pos EmptyString (Some lbrack))%bool
    with true.
  rewrite Hnotes. cbn [andb].
  rewrite bunpush_bpush.
  tred.
  rewrite (iscan_note_label label tail false false EmptyString
             null_span (flush_text txt o) Hsafe).
  reflexivity.
Qed.

(* A canonical target splits off exactly: it has no bar and no
   backslash, and what follows the first bar is the alias whatever it
   holds. *)
Local Lemma wiki_split_canonical :
  forall t al,
    no_char vbar t = true -> no_char bslash t = true ->
    wiki_split (t ++ match al with Some a => String vbar a | None => EmptyString end)
    = (t, al).
Proof.
  induction t as [|c t IH]; intros al Hv Hb.
  - destruct al as [a|]; reflexivity.
  - cbn [no_char] in Hv, Hb.
    apply andb_true_iff in Hv as [Hvc Hv]. apply andb_true_iff in Hb as [Hbc Hb].
    apply negb_true_iff in Hvc. apply negb_true_iff in Hbc.
    cbn [append wiki_split]. unfold is_bslash. rewrite Hbc, Hvc, (IH al Hv Hb).
    reflexivity.
Qed.

(* A canonical region has nothing the region scan gives a role. *)
Local Lemma iscan_wiki_region :
  forall r image acc open o,
    no_char rbrack r = true -> no_char bslash r = true ->
    iscan_str r (IWiki false false image acc open o)
    = IWiki false false image (acc ++ r) open o.
Proof.
  induction r as [|c r IH]; intros image acc open o Hr Hb.
  - rewrite append_empty_r. reflexivity.
  - cbn [no_char] in Hr, Hb.
    apply andb_true_iff in Hr as [Hrc Hr]. apply andb_true_iff in Hb as [Hbc Hb].
    apply negb_true_iff in Hrc. apply negb_true_iff in Hbc.
    cbn [iscan_str istep istep_at iwiki_step andb]. unfold is_bslash.
    rewrite Hbc, Hrc, (IH image _ open o Hr Hb), append_assoc. reflexivity.
Qed.

Local Lemma iscan_wiki_text :
  forall embed t al tail txt prev o,
    ci_ok (CIWiki embed t al) = true ->
    (embed || negb (wiki_opens txt prev o))%bool = true ->
    iscan_str (wiki_text embed t al ++ tail) (IText false txt prev o)
    = iscan_str tail
        (IText false EmptyString (Some rbrack)
          (oemit (mk (Ext_wikilink embed t al)) (flush_text txt o))).
Proof.
  intros embed t al tail txt prev o Hok Hw.
  rewrite ci_ok_wiki in Hok.
  apply andb_true_iff in Hok as [Hok Hal]. apply andb_true_iff in Hok as [Hok Ht].
  apply andb_true_iff in Hok as [Hen Hne].
  unfold wiki_part_ok in Ht.
  apply andb_true_iff in Ht as [Ht _]. apply andb_true_iff in Ht as [Ht Htb].
  apply andb_true_iff in Ht as [Htr Htv].
  set (apart := match al with Some a => String vbar a | None => EmptyString end).
  replace (wiki_text embed t al ++ tail)%string with
    (bracket_open embed
       ++ (one lbrack ++ (t ++ (apart ++ (one rbrack ++ (one rbrack ++ tail))))))%string
    by (unfold wiki_text, apart; rewrite !append_assoc; reflexivity).
  (* the second `[` takes back the bracket the first one pushed *)
  rewrite iscan_str_app, (iscan_bracket_open embed txt prev o Hw).
  rewrite iscan_str_app. cbn [one iscan_str istep istep_at]. unfold ilead.
  change (is_bslash lbrack) with false.
  change (is_tick lbrack) with false.
  change (Ascii.eqb lbrack dollar) with false.
  change (Ascii.eqb lbrack period) with false.
  change (Ascii.eqb lbrack hyphen) with false.
  change (Ascii.eqb lbrack lbrace) with false.
  change (Ascii.eqb lbrack bang) with false.
  change (Ascii.eqb lbrack lt) with false.
  change (Ascii.eqb lbrack ":"%char) with false.
  change (Ascii.eqb lbrack lbrack) with true.
  change (note_pos EmptyString (Some lbrack)) with true.
  rewrite Hen, bunpush_bpush. cbn [andb]. cbn iota beta.
  (* the region: the target, then the bar and the alias *)
  rewrite iscan_str_app, (iscan_wiki_region t embed EmptyString _ _ Htr Htb).
  change (EmptyString ++ t)%string with t.
  assert (Hreg :
    iscan_str apart (IWiki false false embed t null_span (flush_text txt o))
    = IWiki false false embed (t ++ apart) null_span (flush_text txt o)).
  { unfold apart. destruct al as [a|]; [|rewrite append_empty_r; reflexivity].
    unfold wiki_part_ok in Hal.
    apply andb_true_iff in Hal as [Ha _]. apply andb_true_iff in Ha as [Ha Hab].
    apply andb_true_iff in Ha as [Har _].
    cbn [iscan_str istep istep_at iwiki_step andb].
    change (is_bslash vbar) with false. change (Ascii.eqb vbar rbrack) with false.
    cbn iota beta.
    rewrite (iscan_wiki_region a embed _ _ _ Har Hab), append_assoc. reflexivity. }
  rewrite iscan_str_app, Hreg.
  (* and the closer, whose split is the target and the alias *)
  cbn [one append iscan_str istep istep_at iwiki_step andb].
  change (is_bslash rbrack) with false. change (Ascii.eqb rbrack rbrack) with true.
  cbn iota beta.
  cbn [istep_at iwiki_step andb]. change (Ascii.eqb rbrack rbrack) with true.
  cbn iota beta.
  unfold iwiki_close, apart. tred. rewrite (wiki_split_canonical t al Htv Htb).
  destruct t as [|c t']; [discriminate Hne|]. rewrite imk_semantic. reflexivity.
Qed.

(* The region is accumulated and nothing in it is dispatched, which is
   the whole of why a successful autolink's content is literal. *)
Local Lemma iscan_auto_region :
  forall s acc txt o,
    auto_region s = true ->
    iscan_str s (IAuto acc txt o) = IAuto (acc ++ s)%string txt o.
Proof.
  induction s as [|c s IH]; intros acc txt o Hr.
  - rewrite append_empty_r. reflexivity.
  - unfold auto_region in Hr.
    apply andb_true_iff in Hr as [Hr Hgt].
    apply andb_true_iff in Hr as [Hws Hlt].
    cbn [no_ws no_char] in Hws, Hlt, Hgt.
    apply andb_true_iff in Hws as [Hwsc Hws].
    apply andb_true_iff in Hlt as [Hltc Hlt].
    apply andb_true_iff in Hgt as [Hgtc Hgt].
    apply negb_true_iff in Hwsc, Hltc, Hgtc.
    cbn [iscan_str istep istep_at]. unfold iauto_step. tred.
    rewrite Hgtc. cbn [andb orb].
    unfold is_ws_nl in Hwsc. apply orb_false_iff in Hwsc as [Hwsc _].
    rewrite Hwsc, Hltc. cbn [orb].
    rewrite (IH (acc ++ one c)%string txt o)
      by (unfold auto_region; rewrite Hws, Hlt, Hgt; reflexivity).
    rewrite append_assoc. reflexivity.
Qed.

(* A raw spec accumulates the same way an autolink's region does, and
   under the same kind of condition: the format's own exclusions. *)
Local Lemma iscan_raw_format :
  forall fmt acc txt o,
    (no_ws fmt && no_char lbrace fmt && no_char rbrace fmt
     && no_char tick fmt)%bool = true ->
    nonempty_str acc = true ->
    iscan_str fmt (IRaw acc txt o) = IRaw (acc ++ fmt)%string txt o.
Proof.
  induction fmt as [|c fmt IH]; intros acc txt o Hf Hacc.
  - rewrite append_empty_r. reflexivity.
  - apply andb_true_iff in Hf as [Hf Htk].
    apply andb_true_iff in Hf as [Hf Hrb].
    apply andb_true_iff in Hf as [Hws Hlb].
    cbn [no_ws no_char] in Hws, Hlb, Hrb, Htk.
    apply andb_true_iff in Hws as [Hwsc Hws].
    apply andb_true_iff in Hlb as [Hlbc Hlb].
    apply andb_true_iff in Hrb as [Hrbc Hrb].
    apply andb_true_iff in Htk as [Htkc Htk].
    apply negb_true_iff in Hwsc. apply negb_true_iff in Hlbc.
    apply negb_true_iff in Hrbc. apply negb_true_iff in Htkc.
    cbn [iscan_str istep istep_at]. unfold iraw_step_at. tred.
    rewrite Hrbc. cbn [andb].
    destruct acc as [|x acc']; [discriminate|]. cbn [tnonempty nonempty_str].
    unfold raw_stop. rewrite Hlbc.
    replace (is_ws c) with false
      by (unfold is_ws_nl in Hwsc; apply orb_false_iff in Hwsc as [H1 _];
          rewrite H1; reflexivity).
    unfold is_tick. rewrite Htkc. cbn [orb].
    rewrite (IH (String x acc' ++ one c)%string txt o)
      by (first [rewrite Hws, Hlb, Hrb, Htk; reflexivity | reflexivity]).
    rewrite append_assoc. reflexivity.
Qed.

(* ...and the `>` that resolves it, which is the only byte the mode
   treats as anything but region. *)
Local Lemma iscan_auto_text :
  forall s tail txt prev o,
    auto_body_ok s = true -> auto_kind_ok s = true ->
    iscan_str (auto_text s ++ tail) (IText false txt prev o)
    = iscan_str tail
        (IText false EmptyString (Some gt)
           (oemit (mk (auto_node s)) (flush_text txt o))).
Proof.
  intros s tail txt prev o Hbody Hkind.
  pose proof Hbody as Hregion. unfold auto_body_ok in Hregion.
  apply andb_true_iff in Hregion as [_ Hregion].
  unfold auto_text. cbn [append iscan_str istep istep_at].
  unfold ilead.
  change (is_bslash lt) with false.
  change (is_tick lt) with false.
  change (Ascii.eqb lt dollar) with false.
  change (Ascii.eqb lt period) with false.
  change (Ascii.eqb lt hyphen) with false.
  change (Ascii.eqb lt lbrace) with false.
  change (Ascii.eqb lt bang) with false.
  change (Ascii.eqb lt lt) with true.
  tred.
  rewrite append_assoc, iscan_str_app.
  rewrite (iscan_auto_region s EmptyString txt o Hregion).
  replace ((EmptyString ++ s)%string) with s by reflexivity.
  cbn [one append iscan_str istep istep_at]. unfold iauto_step. tred.
  change (Ascii.eqb gt gt) with true.
  rewrite Hbody, Hkind. reflexivity.
Qed.

(* The raw span, end to end: the verbatim's own source reaches the
   closing run, the `{` enters the mode, the format accumulates and the
   `}` decides the node.  `verb_content_ok` is what the verbatim half
   needs and `raw_fmt_ok` the spec half; the `=` is where they meet. *)
Local Lemma iscan_raw_text :
  forall fmt v tail txt prev o,
    raw_inline_enabled = true ->
    nonempty_str v = true -> verb_content_ok v = true ->
    raw_fmt_ok fmt = true ->
    iscan_str (raw_text fmt v ++ tail) (IText false txt prev o)
    = iscan_str tail
        (IText false EmptyString (Some rbrace)
           (oemit (mk (RawInline fmt v)) (flush_text txt o))).
Proof.
  intros fmt v tail txt prev o Hraw Hne Hvok Hfmt.
  unfold raw_fmt_ok in Hfmt.
  apply andb_true_iff in Hfmt as [Hfmt Htk].
  apply andb_true_iff in Hfmt as [Hfmt Hrb].
  apply andb_true_iff in Hfmt as [Hfmt Hlb].
  apply andb_true_iff in Hfmt as [Hfne Hws].
  unfold raw_text. rewrite append_assoc, iscan_str_app.
  rewrite iscan_verb_text_nonempty by auto using verb_content_safe.
  (* the `{` after the closing run enters the mode... *)
  cbn [append iscan_str istep istep_at].
  rewrite nat_eqb_refl. cbn [vkind_verb andb].
  change (Ascii.eqb lbrace lbrace) with true. cbn [andb].
  change (is_tick lbrace) with false. cbn [andb].
  tred.
  rewrite trim_verb_pad by exact Hvok.
  (* ...the `=` makes it a candidate, the format accumulates... *)
  unfold istep_at at 1. unfold iraw_step_at. tred.
  change (Ascii.eqb "="%char rbrace) with false. cbn [andb].
  change (negb (Ascii.eqb "="%char eqchar)) with false.
  cbn [nonempty_str].
  rewrite append_assoc, iscan_str_app.
  change ((EmptyString ++ one "="%char)%string) with (one eqchar).
  rewrite (iscan_raw_format fmt (one eqchar) v (flush_text txt o))
    by (first [rewrite Hws, Hlb, Hrb, Htk; reflexivity | reflexivity]).
  (* ...and the `}` decides the node. *)
  cbn [one iscan_str istep istep_at append]. unfold iraw_step_at. tred.
  change (Ascii.eqb rbrace rbrace) with true.
  unfold raw_spec_ok. cbn [append].
  rewrite Ascii.eqb_refl, Hfne. cbn [andb].
  rewrite Hraw. unfold raw_format. reflexivity.
Qed.

Local Lemma ref_close_app :
  forall label t, (ref_close label EmptyString ++ t)%string = ref_close label t.
Proof.
  intros label t. unfold ref_close. cbn [append].
  rewrite append_assoc. cbn [append]. reflexivity.
Qed.

Local Lemma ref_close_nonempty :
  forall label tail, nonempty_str (ref_close label tail) = true.
Proof. intros label tail. reflexivity. Qed.

Local Lemma ref_close_starts_nontick :
  forall label tail, starts_tick (ref_close label tail) = false.
Proof. intros label tail. reflexivity. Qed.

Local Lemma link_close_nonempty :
  forall dst tail, nonempty_str (link_close dst tail) = true.
Proof. intros dst tail. reflexivity. Qed.

Local Lemma link_close_starts_nontick :
  forall dst tail, starts_tick (link_close dst tail) = false.
Proof. intros dst tail. reflexivity. Qed.

Local Lemma after_verb_source_nontick :
  forall v rest cl,
    cis_ok (CIVerb v :: rest) = true ->
    nonempty_str cl = true -> starts_tick cl = false ->
    after_verb_next cl = true ->
    nonempty_str (ci_text rest ++ cl) = true /\
    starts_tick (ci_text rest ++ cl) = false /\
    after_verb_next (ci_text rest ++ cl) = true.
Proof.
  intros v [|c rest] cl Hok Hcl Hct Hnx.
  - cbn [ci_text append]. split; [assumption|split; assumption].
  - destruct c as [s|w|d kids|img kids dst|rimg rkids rlabel|label|a|rf rv|we wt wal|tn tkids].
    + pose proof (cis_ok_head (CIStr s) rest (cis_ok_tail _ _ Hok)) as Hs.
      cbn [ci_ok] in Hs. apply andb_true_iff in Hs as [Hs _].
      cbn [ci_text ci_src]. split; [|split].
      * destruct (escape_str s) eqn:E;
          [pose proof (escape_str_nonempty s Hs); rewrite E in H; discriminate
          |reflexivity].
      * rewrite starts_tick_app_l.
        -- rewrite starts_tick_app_l.
           ++ apply escape_str_starts_nontick, Hs.
           ++ apply escape_str_nonempty, Hs.
        -- destruct (escape_str s) eqn:E; [|reflexivity].
           pose proof (escape_str_nonempty s Hs). rewrite E in H.
           discriminate.
      * apply after_verb_next_nonbrace.
        rewrite starts_brace_app_l.
        -- rewrite starts_brace_app_l;
             [apply escape_str_starts_nonbrace | apply escape_str_nonempty, Hs].
        -- apply nonempty_str_app_r, escape_str_nonempty, Hs.
    + unfold cis_ok in Hok. cbn [ci_sep_ok ci_pair_ok] in Hok.
      repeat rewrite andb_false_r in Hok. discriminate.
    + (* the one constituent whose source *is* a brace: what may follow it
         is the pair rule, and this is the only place that reads it *)
      unfold cis_ok in Hok. cbn [ci_sep_ok ci_pair_ok] in Hok.
      apply andb_true_iff in Hok as [_ Hok].
      apply andb_true_iff in Hok as [Hpair _].
      cbn [ci_text]. rewrite ci_src_delim.
      cbn [append starts_tick]. split; [reflexivity|split; [reflexivity|]].
      (* the row's token is nonempty, so the byte after the brace is its
         character and the pair rule is exactly the question asked *)
      unfold marked_open, dtoken.
      destruct (dwidth d) as [|w] eqn:Ew;
        [pose proof (dtoken_nonempty d) as Hn; unfold dtoken in Hn;
         rewrite Ew in Hn; discriminate|].
      cbn [chars append one after_verb_next].
      rewrite Ascii.eqb_refl. exact Hpair.
    + cbn [ci_text]. rewrite ci_src_link. unfold bracket_open.
      destruct img; cbn [append starts_tick after_verb_next];
        split; [reflexivity|split; reflexivity|reflexivity|split; reflexivity].
    + cbn [ci_text]. rewrite ci_src_ref. unfold bracket_open.
      destruct rimg; cbn [append starts_tick after_verb_next];
        split; [reflexivity|split; reflexivity|reflexivity|split; reflexivity].
    + cbn [ci_text ci_src note_text append starts_tick after_verb_next].
      split; [reflexivity|split; reflexivity].
    + cbn [ci_text ci_src auto_text append starts_tick after_verb_next].
      split; [reflexivity|split; reflexivity].
    + (* raw content opens with a backtick run, and the pair rule is what
         keeps it away from a verbatim *)
      unfold cis_ok in Hok. cbn [ci_sep_ok ci_pair_ok] in Hok.
      repeat rewrite andb_false_r in Hok. discriminate.
    + cbn [ci_text ci_src wiki_text]. unfold bracket_open.
      destruct we; cbn [append starts_tick after_verb_next];
        split; [reflexivity|split; reflexivity|reflexivity|split; reflexivity].
    + cbn [ci_text]. rewrite ci_src_tag. unfold tag_open.
      destruct tn; cbn [append starts_tick after_verb_next];
        split; [reflexivity|split; reflexivity|reflexivity|split; reflexivity].
Qed.

Local Lemma after_verb_rest_nontick :
  forall v c rest,
    cis_ok (CIVerb v :: c :: rest) = true ->
    nonempty_str (ci_text (c :: rest)) = true /\
    starts_tick (ci_text (c :: rest)) = false /\
    after_verb_next (ci_text (c :: rest)) = true.
Proof.
  intros v c rest Hok.
  (* any nonempty closer that is not a backtick and not a brace will do,
     and taking one off the table keeps this independent of which rows
     exist *)
  destruct (after_verb_source_nontick v (c :: rest) (one rbrace) Hok
              eq_refl eq_refl eq_refl)
    as [Hne [Htick Hnx]].
  destruct c as [s|w|d kids|img kids dst|rimg rkids rlabel|label|a|rf rv|we wt wal|tn tkids].
  - pose proof (cis_ok_head (CIStr s) rest (cis_ok_tail _ _ Hok)) as Hs.
    cbn [ci_ok] in Hs. apply andb_true_iff in Hs as [Hs _].
    cbn [ci_text ci_src]. split; [|split].
    + destruct (escape_str s) eqn:E;
        [pose proof (escape_str_nonempty s Hs); rewrite E in H; discriminate
        |reflexivity].
    + rewrite starts_tick_app_l;
        [apply escape_str_starts_nontick, Hs|apply escape_str_nonempty, Hs].
    + apply after_verb_next_nonbrace.
      rewrite starts_brace_app_l;
        [apply escape_str_starts_nonbrace | apply escape_str_nonempty, Hs].
  - unfold cis_ok in Hok. cbn [ci_sep_ok ci_pair_ok] in Hok.
    repeat rewrite andb_false_r in Hok. discriminate.
  - unfold cis_ok in Hok. cbn [ci_sep_ok ci_pair_ok] in Hok.
    apply andb_true_iff in Hok as [_ Hok].
    apply andb_true_iff in Hok as [Hpair _].
    cbn [ci_text]. rewrite ci_src_delim. cbn [starts_tick nonempty_str].
    split; [reflexivity|split; [reflexivity|]].
    unfold marked_open, dtoken.
    destruct (dwidth d) as [|w] eqn:Ew;
      [pose proof (dtoken_nonempty d) as Hn; unfold dtoken in Hn;
       rewrite Ew in Hn; discriminate|].
    cbn [chars append one after_verb_next].
    rewrite Ascii.eqb_refl. exact Hpair.
  - cbn [ci_text]. rewrite ci_src_link. unfold bracket_open.
    destruct img;
      cbn [append starts_tick nonempty_str after_verb_next];
      split; [reflexivity|split; reflexivity|reflexivity|split; reflexivity].
  - cbn [ci_text]. rewrite ci_src_ref. unfold bracket_open.
    destruct rimg;
      cbn [append starts_tick nonempty_str after_verb_next];
      split; [reflexivity|split; reflexivity|reflexivity|split; reflexivity].
  - cbn [ci_text ci_src note_text append starts_tick nonempty_str
         after_verb_next].
    split; [reflexivity|split; reflexivity].
  - cbn [ci_text ci_src auto_text append starts_tick nonempty_str
         after_verb_next].
    split; [reflexivity|split; reflexivity].
  - unfold cis_ok in Hok. cbn [ci_sep_ok ci_pair_ok] in Hok.
    repeat rewrite andb_false_r in Hok. discriminate.
  - cbn [ci_text ci_src wiki_text]. unfold bracket_open.
    destruct we;
      cbn [append starts_tick nonempty_str after_verb_next];
      split; [reflexivity|split; reflexivity|reflexivity|split; reflexivity].
  - cbn [ci_text]. rewrite ci_src_tag. unfold tag_open.
    destruct tn;
      cbn [append starts_tick nonempty_str after_verb_next];
      split; [reflexivity|split; reflexivity|reflexivity|split; reflexivity].
Qed.

Local Lemma orb_false_r_true : forall b, (b || false)%bool = true -> b = true.
Proof. intros [] H; [reflexivity | exact H]. Qed.

(* The scanner inversion, one scope deep.

   Scanning a canonical run of inlines from inside an open scope reaches
   the same state as emitting their nodes.  The scope's *closer* is a
   parameter, because two constructs supply one -- a marked delimiter and
   a bracket -- and the proof needs exactly three things of it: that it
   is nonempty and does not start with a backtick (so a verbatim before
   it resolves), and that scanning it flushes the pending text.  That
   last is the `Hflush` hypothesis, and `empty_ok` is where the two
   differ: `oclose` refuses an empty scope, `bclose` does not, which is
   what makes `[](u)` representable and `{__}` not. *)
Local Lemma iscan_cis_scope :
  forall cis cl O empty_ok txt prev before,
    nonempty_str cl = true -> starts_tick cl = false ->
    after_verb_next cl = true ->
    (forall txt' prev' before',
       (nonempty before' || nonempty_str txt' || empty_ok)%bool = true ->
       exists p,
         iscan_str cl (IText false txt' prev' (oemit_all before' O))
         = iscan_str cl
             (IText false EmptyString p
               (flush_text txt' (oemit_all before' O)))) ->
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    (cis_lbrack_head cis = true ->
       wiki_opens txt prev (oemit_all before O) = false) ->
    (nonempty before || nonempty_str txt || nonempty cis || empty_ok)%bool
      = true ->
    exists p,
      iscan_str (ci_text cis ++ cl)
        (IText false txt prev (oemit_all before O))
      = iscan_str cl
          (IText false EmptyString p
            (oemit_all (ci_inlines cis)
              (flush_text txt (oemit_all before O)))).
Proof.
  intro cis. pattern cis.
  apply (well_founded_induction (well_founded_ltof _ cis_size)).
  clear cis.
  intros cis IH cl O empty_ok txt prev before Hcl Hct Hnx Hflush Hok Hsep Hw Hne.
  destruct cis as [|c rest].
  - cbn [ci_text ci_inlines map append nonempty] in Hne |- *.
    apply Hflush. rewrite <- Hne. destruct (nonempty before), (nonempty_str txt);
      reflexivity.
  - destruct c as [s|v|d kids|img kids dst|rimg rkids rlabel|label|a|rf rv|we wt wal|tn tkids].
    + destruct txt as [|x txt']; [|discriminate].
      pose proof (cis_ok_head (CIStr s) rest Hok) as Hsok.
      cbn [ci_ok] in Hsok. apply andb_true_iff in Hsok as [Hs _].
      assert (Hlt : ltof (list cinline) cis_size rest (CIStr s :: rest)).
      { unfold ltof. cbn [cis_size ci_size]. lia. }
      pose proof (IH rest Hlt cl O empty_ok s (str_last s prev) before
        Hcl Hct Hnx Hflush
        (cis_ok_tail _ _ Hok) (ci_str_tail_sep s rest Hok Hs)
        (fun _ => wiki_opens_text _ _ _ Hs)) as IHr.
      assert (Hnr : nonempty before || nonempty_str s || nonempty rest
                    || empty_ok = true).
      { rewrite Hs, orb_true_r. reflexivity. }
      destruct (IHr Hnr) as [p Ep]. exists p.
      cbn [ci_text ci_src ci_inlines map append].
      rewrite append_assoc, iscan_str_app, iscan_escape.
      change (EmptyString ++ s)%string with s. rewrite Ep.
      unfold flush_text at 1 2. unfold flush_text_at.
      cbn [nonempty_str ci_ast mk oemit_all].
      rewrite Hs. reflexivity.
    + pose proof (ci_verb_nonempty v rest Hok) as Hvne.
      pose proof (ci_verb_content_ok v rest Hok) as Hvok.
      destruct (after_verb_source_nontick v rest cl Hok Hcl Hct Hnx)
        as [Hsrcne [Hsrctick Hsrcnx]].
      assert (Hlt : ltof (list cinline) cis_size rest (CIVerb v :: rest)).
      { unfold ltof. cbn [cis_size ci_size]. lia. }
      assert (Hstep : forall pre,
        nonempty pre = true ->
        exists p,
          iscan_str (ci_text rest ++ cl)
            (IText false EmptyString (Some tick) (oemit_all pre O))
          = iscan_str cl
              (IText false EmptyString p
                (oemit_all (ci_inlines rest)
                  (flush_text EmptyString (oemit_all pre O))))).
      { intros pre Hpre.
        apply (IH rest Hlt cl O empty_ok EmptyString (Some tick) pre
                 Hcl Hct Hnx Hflush (cis_ok_tail _ _ Hok) eq_refl
                 (fun _ => wiki_opens_oemit_all _ _ _ _ Hpre)).
        rewrite Hpre. reflexivity. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [mk (Verbatim v)])%list
                    ltac:(destruct before; reflexivity)) as [p Ep].
        exists p.
        cbn [ci_text ci_src ci_inlines map]. rewrite append_assoc, iscan_str_app.
        rewrite iscan_verb_text_nonempty by auto using verb_content_safe.
        cbn [flush_text flush_text_at nonempty_str]. rewrite ?imk_semantic.
        rewrite (iscan_after_verb_nontick _ _ _ _ Hsrcne Hsrctick Hsrcnx),
          trim_verb_pad by exact Hvok. cbn [vnode].
        rewrite oemit_all_app in Ep.
        cbn [oemit_all flush_text flush_text_at nonempty_str] in Ep.
        rewrite Ep. cbn [oemit_all ci_ast]. reflexivity.
      * destruct (Hstep (before ++ [mk (Str (String x txt')); mk (Verbatim v)])%list
                    ltac:(destruct before; reflexivity)) as [p Ep].
        exists p.
        cbn [ci_text ci_src ci_inlines map]. rewrite append_assoc, iscan_str_app.
        rewrite iscan_verb_text_nonempty by auto using verb_content_safe.
        cbn [flush_text flush_text_at nonempty_str]. rewrite ?imk_semantic.
        rewrite (iscan_after_verb_nontick _ _ _ _ Hsrcne Hsrctick Hsrcnx),
          trim_verb_pad by exact Hvok. cbn [vnode].
        rewrite oemit_all_app in Ep.
        cbn [oemit_all flush_text flush_text_at nonempty_str] in Ep.
        rewrite Ep. cbn [oemit_all ci_ast]. reflexivity.
    + pose proof (cis_ok_head (CIDelim d kids) rest Hok) as Hdk.
      rewrite ci_ok_delim in Hdk. apply andb_true_iff in Hdk as [Hdk Hkidsok].
      apply andb_true_iff in Hdk as [Hden Hkidsne].
      assert (Hkidslt :
        ltof (list cinline) cis_size kids (CIDelim d kids :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_delim. lia. }
      destruct (iscan_marked_open_app d
                  (ci_text kids ++ marked_close d (ci_text rest ++ cl))
                  txt prev (oemit_all before O) Hden
                  (nonempty_str_app_l _ _ (marked_close_nonempty _ _)))
        as [cm [op Eopen]].
      pose proof (IH kids Hkidslt (marked_close d (ci_text rest ++ cl))
        (opush_at d true cm op (flush_text txt (oemit_all before O))) false
        EmptyString (Some (dchar d)) []
        (marked_close_nonempty _ _) (marked_close_starts_nontick _ _)
        (marked_close_after_verb _ _)
        (fun txt' prev' before' e =>
           iscan_marked_flush d cm (ci_text rest ++ cl) txt' prev' before' op
             (flush_text txt (oemit_all before O)) Hden (orb_false_r_true _ e)))
        as IHkids.
      assert (Hkn :
        nonempty (@nil (node inline)) || nonempty_str EmptyString ||
        nonempty kids || false = true).
      { cbn. rewrite orb_false_r. exact Hkidsne. }
      destruct (IHkids Hkidsok eq_refl (fun _ => wiki_opens_opush _ _ _ _ _ _ _ _) Hkn)
        as [pk Ekids].
      assert (Hrestlt :
        ltof (list cinline) cis_size rest (CIDelim d kids :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_delim. lia. }
      assert (Hstep : forall pre,
        nonempty pre = true ->
        exists p,
          iscan_str (ci_text rest ++ cl)
            (IText false EmptyString (Some rbrace) (oemit_all pre O))
          = iscan_str cl
              (IText false EmptyString p
                (oemit_all (ci_inlines rest)
                  (flush_text EmptyString (oemit_all pre O))))).
      { intros pre Hpre.
        apply (IH rest Hrestlt cl O empty_ok EmptyString (Some rbrace) pre
                 Hcl Hct Hnx Hflush (cis_ok_tail _ _ Hok) eq_refl
                 (fun _ => wiki_opens_oemit_all _ _ _ _ Hpre)).
        rewrite Hpre. reflexivity. }
      assert (Hsrc : forall t,
        ((marked_open d ++ (ci_text kids ++ marked_close d EmptyString))
           ++ t)%string
        = (marked_open d ++ (ci_text kids ++ marked_close d t))%string).
      { intro t. rewrite !append_assoc, marked_close_app. reflexivity. }
      assert (Hkins : nonempty (ci_inlines kids) = true).
      { destruct kids; [discriminate|reflexivity]. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [ci_ast (CIDelim d kids)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_delim.
        rewrite append_assoc, Hsrc, Eopen.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids |- *.
        rewrite ?imk_semantic in Ekids; rewrite ?imk_semantic. rewrite Ekids.
        rewrite (iscan_marked_close_emit d cm _ (ci_inlines kids) op _ pk Hden
                   Hkins).
        rewrite <- ci_ast_delim. rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text flush_text_at nonempty_str oemit_all].
        rewrite ?imk_semantic. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CIDelim d kids)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_delim.
        rewrite append_assoc, Hsrc, Eopen.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids |- *.
        rewrite ?imk_semantic in Ekids; rewrite ?imk_semantic. rewrite Ekids.
        rewrite (iscan_marked_close_emit d cm _ (ci_inlines kids) op _ pk Hden
                   Hkins).
        rewrite <- ci_ast_delim. rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text flush_text_at nonempty_str oemit_all].
        rewrite ?imk_semantic. reflexivity.
    + pose proof (cis_ok_head (CILink img kids dst) rest Hok) as Hdk.
      rewrite ci_ok_link in Hdk. apply andb_true_iff in Hdk as [Hdk Hbk].
      apply andb_true_iff in Hdk as [Hnl Hkidsok].
      assert (Hkidslt :
        ltof (list cinline) cis_size kids (CILink img kids dst :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_link. lia. }
      pose proof (IH kids Hkidslt (link_close dst (ci_text rest ++ cl))
        (bpush img (flush_text txt (oemit_all before O))) true
        EmptyString (Some lbrack) []
        (link_close_nonempty _ _) (link_close_starts_nontick _ _) eq_refl
        (fun txt' prev' before' _ =>
           iscan_bracket_flush dst (ci_text rest ++ cl) txt' prev' img before'
             (flush_text txt (oemit_all before O)))) as IHkids.
      destruct (IHkids Hkidsok eq_refl
                 (wiki_opens_bracket_kids _ _ _ _ Hbk) (orb_true_r _))
        as [pk Ekids].
      assert (Hrestlt :
        ltof (list cinline) cis_size rest (CILink img kids dst :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_link. lia. }
      assert (Hstep : forall pre,
        nonempty pre = true ->
        exists p,
          iscan_str (ci_text rest ++ cl)
            (IText false EmptyString (Some rparen) (oemit_all pre O))
          = iscan_str cl
              (IText false EmptyString p
                (oemit_all (ci_inlines rest)
                  (flush_text EmptyString (oemit_all pre O))))).
      { intros pre Hpre.
        apply (IH rest Hrestlt cl O empty_ok EmptyString (Some rparen) pre
                 Hcl Hct Hnx Hflush (cis_ok_tail _ _ Hok) eq_refl
                 (fun _ => wiki_opens_oemit_all _ _ _ _ Hpre)).
        rewrite Hpre. reflexivity. }
      assert (Hsrc : forall t,
        (((bracket_open img ++ (ci_text kids ++ link_close dst EmptyString))
          ++ t))%string
        = (bracket_open img ++ (ci_text kids ++ link_close dst t))%string).
      { intro t. rewrite append_assoc, append_assoc, link_close_app.
        reflexivity. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [ci_ast (CILink img kids dst)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_link.
        rewrite append_assoc, Hsrc, iscan_str_app, iscan_bracket_open
          by (first [destruct img | destruct rimg];
              [reflexivity|rewrite (Hw eq_refl); reflexivity]).
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids |- *.
        rewrite ?imk_semantic in Ekids; rewrite ?imk_semantic. rewrite Ekids.
        rewrite (iscan_link_close dst _ (ci_inlines kids) img _ pk Hnl).
        rewrite <- ci_ast_link. rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text flush_text_at nonempty_str oemit_all].
        rewrite ?imk_semantic. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CILink img kids dst)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_link.
        rewrite append_assoc, Hsrc, iscan_str_app, iscan_bracket_open
          by (first [destruct img | destruct rimg];
              [reflexivity|rewrite (Hw eq_refl); reflexivity]).
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids |- *.
        rewrite ?imk_semantic in Ekids; rewrite ?imk_semantic. rewrite Ekids.
        rewrite (iscan_link_close dst _ (ci_inlines kids) img _ pk Hnl).
        rewrite <- ci_ast_link. rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text flush_text_at nonempty_str oemit_all].
        rewrite ?imk_semantic. reflexivity.
    + (* a reference link: the direct link's case with the other closer *)
      pose proof (cis_ok_head (CIRef rimg rkids rlabel) rest Hok) as Hdk.
      rewrite ci_ok_ref in Hdk. apply andb_true_iff in Hdk as [Hdk Hbk].
      apply andb_true_iff in Hdk as [Hlab Hkidsok].
      apply andb_true_iff in Hlab as [Hlab Hnorm].
      apply andb_true_iff in Hlab as [Hne' Hbr].
      apply String.eqb_eq in Hnorm.
      assert (Hkidslt :
        ltof (list cinline) cis_size rkids (CIRef rimg rkids rlabel :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_ref. lia. }
      pose proof (IH rkids Hkidslt (ref_close rlabel (ci_text rest ++ cl))
        (bpush rimg (flush_text txt (oemit_all before O))) true
        EmptyString (Some lbrack) []
        (ref_close_nonempty _ _) (ref_close_starts_nontick _ _) eq_refl
        (fun txt' prev' before' _ =>
           iscan_ref_flush rlabel (ci_text rest ++ cl) txt' prev' rimg before'
             (flush_text txt (oemit_all before O)))) as IHkids.
      destruct (IHkids Hkidsok eq_refl
                 (wiki_opens_bracket_kids _ _ _ _ Hbk) (orb_true_r _))
        as [pk Ekids].
      assert (Hrestlt :
        ltof (list cinline) cis_size rest (CIRef rimg rkids rlabel :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_ref. lia. }
      assert (Hstep : forall pre,
        nonempty pre = true ->
        exists p,
          iscan_str (ci_text rest ++ cl)
            (IText false EmptyString (Some rbrack) (oemit_all pre O))
          = iscan_str cl
              (IText false EmptyString p
                (oemit_all (ci_inlines rest)
                  (flush_text EmptyString (oemit_all pre O))))).
      { intros pre Hpre.
        apply (IH rest Hrestlt cl O empty_ok EmptyString (Some rbrack) pre
                 Hcl Hct Hnx Hflush (cis_ok_tail _ _ Hok) eq_refl
                 (fun _ => wiki_opens_oemit_all _ _ _ _ Hpre)).
        rewrite Hpre. reflexivity. }
      assert (Hsrc : forall t,
        (((bracket_open rimg ++ (ci_text rkids ++ ref_close rlabel EmptyString))
          ++ t))%string
        = (bracket_open rimg ++ (ci_text rkids ++ ref_close rlabel t))%string).
      { intro t. rewrite append_assoc, append_assoc, ref_close_app.
        reflexivity. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [ci_ast (CIRef rimg rkids rlabel)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_ref.
        rewrite append_assoc, Hsrc, iscan_str_app, iscan_bracket_open
          by (first [destruct img | destruct rimg];
              [reflexivity|rewrite (Hw eq_refl); reflexivity]).
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids |- *.
        rewrite ?imk_semantic in Ekids; rewrite ?imk_semantic. rewrite Ekids.
        rewrite (iscan_ref_close rlabel _ (ci_inlines rkids) rimg _ pk Hne' Hbr),
                Hnorm.
        rewrite <- ci_ast_ref. rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text flush_text_at nonempty_str oemit_all].
        rewrite ?imk_semantic. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CIRef rimg rkids rlabel)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_ref.
        rewrite append_assoc, Hsrc, iscan_str_app, iscan_bracket_open
          by (first [destruct img | destruct rimg];
              [reflexivity|rewrite (Hw eq_refl); reflexivity]).
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids |- *.
        rewrite ?imk_semantic in Ekids; rewrite ?imk_semantic. rewrite Ekids.
        rewrite (iscan_ref_close rlabel _ (ci_inlines rkids) rimg _ pk Hne' Hbr),
                Hnorm.
        rewrite <- ci_ast_ref. rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text flush_text_at nonempty_str oemit_all].
        rewrite ?imk_semantic. reflexivity.
    + pose proof (cis_ok_head (CINote label) rest Hok) as Hnote.
      rewrite ci_ok_note in Hnote.
      apply andb_true_iff in Hnote as [Hnote Hnorm].
      apply andb_true_iff in Hnote as [Hnotes Hsafe].
      apply String.eqb_eq in Hnorm.
      assert (Hrestlt : ltof (list cinline) cis_size rest (CINote label :: rest)).
      { unfold ltof. cbn [cis_size ci_size]. lia. }
      assert (Hstep : forall pre,
        nonempty pre = true ->
        exists p,
          iscan_str (ci_text rest ++ cl)
            (IText false EmptyString (Some rbrack) (oemit_all pre O))
          = iscan_str cl
              (IText false EmptyString p
                (oemit_all (ci_inlines rest)
                  (flush_text EmptyString (oemit_all pre O))))).
      { intros pre Hpre. apply (IH rest Hrestlt cl O empty_ok EmptyString
          (Some rbrack) pre Hcl Hct Hnx Hflush (cis_ok_tail _ _ Hok) eq_refl
                 (fun _ => wiki_opens_oemit_all _ _ _ _ Hpre)).
        rewrite Hpre. reflexivity. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [ci_ast (CINote label)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p. cbn [ci_text ci_inlines map].
        change (ci_src (CINote label)) with (note_text label).
        rewrite append_assoc, iscan_note_text
          by first [assumption | exact (Hw eq_refl)].
        rewrite Hnorm. rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all ci_ast] in Erest |- *.
        rewrite ?imk_semantic in Erest; rewrite ?imk_semantic.
        rewrite Erest. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CINote label)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p. cbn [ci_text ci_inlines map].
        change (ci_src (CINote label)) with (note_text label).
        rewrite append_assoc, iscan_note_text
          by first [assumption | exact (Hw eq_refl)].
        rewrite Hnorm. rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all ci_ast] in Erest |- *.
        rewrite ?imk_semantic in Erest; rewrite ?imk_semantic.
        rewrite Erest. reflexivity.
    + (* an autolink: the footnote reference's case with the other leaf,
         and no normalization to rewrite through *)
      pose proof (cis_ok_head (CIAuto a) rest Hok) as Hauto.
      rewrite ci_ok_auto in Hauto.
      apply andb_true_iff in Hauto as [Hbody Hkind].
      assert (Hrestlt : ltof (list cinline) cis_size rest (CIAuto a :: rest)).
      { unfold ltof. cbn [cis_size ci_size]. lia. }
      assert (Hstep : forall pre,
        nonempty pre = true ->
        exists p,
          iscan_str (ci_text rest ++ cl)
            (IText false EmptyString (Some gt) (oemit_all pre O))
          = iscan_str cl
              (IText false EmptyString p
                (oemit_all (ci_inlines rest)
                  (flush_text EmptyString (oemit_all pre O))))).
      { intros pre Hpre. apply (IH rest Hrestlt cl O empty_ok EmptyString
          (Some gt) pre Hcl Hct Hnx Hflush (cis_ok_tail _ _ Hok) eq_refl
                 (fun _ => wiki_opens_oemit_all _ _ _ _ Hpre)).
        rewrite Hpre. reflexivity. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [ci_ast (CIAuto a)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p. cbn [ci_text ci_inlines map].
        change (ci_src (CIAuto a)) with (auto_text a).
        rewrite append_assoc, iscan_auto_text by assumption.
        rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all ci_ast] in Erest |- *.
        rewrite ?imk_semantic in Erest; rewrite ?imk_semantic.
        rewrite Erest. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CIAuto a)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p. cbn [ci_text ci_inlines map].
        change (ci_src (CIAuto a)) with (auto_text a).
        rewrite append_assoc, iscan_auto_text by assumption.
        rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all ci_ast] in Erest |- *.
        rewrite ?imk_semantic in Erest; rewrite ?imk_semantic.
        rewrite Erest. reflexivity.
    + (* raw content: the same leaf shape again, with the verbatim's own
         conditions in front of the spec's *)
      pose proof (cis_ok_head (CIRaw rf rv) rest Hok) as Hraw.
      rewrite ci_ok_raw in Hraw.
      apply andb_true_iff in Hraw as [Hraw Hfmt].
      apply andb_true_iff in Hraw as [Hraw Hrok].
      apply andb_true_iff in Hraw as [Hcap Hrne].
      assert (Hrestlt :
        ltof (list cinline) cis_size rest (CIRaw rf rv :: rest)).
      { unfold ltof. cbn [cis_size ci_size]. lia. }
      assert (Hstep : forall pre,
        nonempty pre = true ->
        exists p,
          iscan_str (ci_text rest ++ cl)
            (IText false EmptyString (Some rbrace) (oemit_all pre O))
          = iscan_str cl
              (IText false EmptyString p
                (oemit_all (ci_inlines rest)
                  (flush_text EmptyString (oemit_all pre O))))).
      { intros pre Hpre. apply (IH rest Hrestlt cl O empty_ok EmptyString
          (Some rbrace) pre Hcl Hct Hnx Hflush (cis_ok_tail _ _ Hok) eq_refl
                 (fun _ => wiki_opens_oemit_all _ _ _ _ Hpre)).
        rewrite Hpre. reflexivity. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [ci_ast (CIRaw rf rv)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p. cbn [ci_text ci_inlines map].
        change (ci_src (CIRaw rf rv)) with (raw_text rf rv).
        rewrite append_assoc, iscan_raw_text by assumption.
        rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all ci_ast] in Erest |- *.
        rewrite ?imk_semantic in Erest; rewrite ?imk_semantic.
        rewrite Erest. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CIRaw rf rv)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p. cbn [ci_text ci_inlines map].
        change (ci_src (CIRaw rf rv)) with (raw_text rf rv).
        rewrite append_assoc, iscan_raw_text by assumption.
        rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all ci_ast] in Erest |- *.
        rewrite ?imk_semantic in Erest; rewrite ?imk_semantic.
        rewrite Erest. reflexivity.
    + (* a wikilink: the footnote reference's leaf shape, whose first `[`
         `Hw` keeps from being read as the second bracket of another *)
      pose proof (cis_ok_head (CIWiki we wt wal) rest Hok) as Hwk.
      assert (Hrestlt :
        ltof (list cinline) cis_size rest (CIWiki we wt wal :: rest)).
      { unfold ltof. cbn [cis_size ci_size]. lia. }
      assert (Hstep : forall pre,
        nonempty pre = true ->
        exists p,
          iscan_str (ci_text rest ++ cl)
            (IText false EmptyString (Some rbrack) (oemit_all pre O))
          = iscan_str cl
              (IText false EmptyString p
                (oemit_all (ci_inlines rest)
                  (flush_text EmptyString (oemit_all pre O))))).
      { intros pre Hpre. apply (IH rest Hrestlt cl O empty_ok EmptyString
          (Some rbrack) pre Hcl Hct Hnx Hflush (cis_ok_tail _ _ Hok) eq_refl
                 (fun _ => wiki_opens_oemit_all _ _ _ _ Hpre)).
        rewrite Hpre. reflexivity. }
      assert (Hopen :
        (we || negb (wiki_opens txt prev (oemit_all before O)))%bool = true)
        by (destruct we; [reflexivity|rewrite (Hw eq_refl); reflexivity]).
      destruct txt as [|x txt'].
      * destruct (Hstep
                    (before ++ [ci_ast (CIWiki we wt wal)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p. cbn [ci_text ci_inlines map].
        change (ci_src (CIWiki we wt wal)) with (wiki_text we wt wal).
        rewrite append_assoc, (iscan_wiki_text we wt wal _ _ _ _ Hwk Hopen).
        rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all ci_ast] in Erest |- *.
        rewrite ?imk_semantic in Erest; rewrite ?imk_semantic.
        rewrite Erest. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CIWiki we wt wal)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p. cbn [ci_text ci_inlines map].
        change (ci_src (CIWiki we wt wal)) with (wiki_text we wt wal).
        rewrite append_assoc, (iscan_wiki_text we wt wal _ _ _ _ Hwk Hopen).
        rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all ci_ast] in Erest |- *.
        rewrite ?imk_semantic in Erest; rewrite ?imk_semantic.
        rewrite Erest. reflexivity.
    + (* a named span: the link's shape, opened through the symbol state
         and closed by its `]` alone *)
      pose proof (cis_ok_head (CITag tn tkids) rest Hok) as Htk.
      rewrite ci_ok_tag in Htk. apply andb_true_iff in Htk as [Htk Hkidsok].
      apply andb_true_iff in Htk as [Hten Hname].
      assert (Hkidslt :
        ltof (list cinline) cis_size tkids (CITag tn tkids :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_tag. lia. }
      pose proof (IH tkids Hkidslt (String rbrack (ci_text rest ++ cl))
        (tag_push tn (Spot 0 0) (flush_text txt (oemit_all before O))) true
        EmptyString (Some lbrack) []
        eq_refl eq_refl eq_refl
        (fun txt' prev' before' _ =>
           iscan_tag_flush tn (ci_text rest ++ cl) txt' prev' before'
             (flush_text txt (oemit_all before O)) Hten)) as IHkids.
      destruct (IHkids Hkidsok eq_refl
                 (fun _ => wiki_opens_tag_push _ _ _ _ _) (orb_true_r _))
        as [pk Ekids].
      cbn [oemit_all] in Ekids.
      assert (Hrestlt :
        ltof (list cinline) cis_size rest (CITag tn tkids :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_tag. lia. }
      assert (Hstep : forall pre,
        nonempty pre = true ->
        exists p,
          iscan_str (ci_text rest ++ cl)
            (IText false EmptyString (Some rbrack) (oemit_all pre O))
          = iscan_str cl
              (IText false EmptyString p
                (oemit_all (ci_inlines rest)
                  (flush_text EmptyString (oemit_all pre O))))).
      { intros pre Hpre.
        apply (IH rest Hrestlt cl O empty_ok EmptyString (Some rbrack) pre
                 Hcl Hct Hnx Hflush (cis_ok_tail _ _ Hok) eq_refl
                 (fun _ => wiki_opens_oemit_all _ _ _ _ Hpre)).
        rewrite Hpre. reflexivity. }
      assert (Hsrc : forall t,
        ((tag_open tn ++ (ci_text tkids ++ one rbrack)) ++ t)%string
        = (tag_open tn ++ (ci_text tkids ++ String rbrack t))%string).
      { intro t. rewrite !append_assoc. reflexivity. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [ci_ast (CITag tn tkids)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_tag.
        rewrite append_assoc, Hsrc, iscan_str_app, iscan_tag_open by assumption.
        rewrite Ekids. cbn [flush_text flush_text_at nonempty_str].
        rewrite (iscan_tag_close tn _ (ci_inlines tkids) _ pk Hten).
        rewrite <- ci_ast_tag. rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Erest |- *.
        rewrite ?imk_semantic in Erest; rewrite ?imk_semantic.
        rewrite Erest. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CITag tn tkids)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_tag.
        rewrite append_assoc, Hsrc, iscan_str_app, iscan_tag_open by assumption.
        rewrite Ekids. cbn [flush_text flush_text_at nonempty_str].
        rewrite (iscan_tag_close tn _ (ci_inlines tkids) _ pk Hten).
        rewrite <- ci_ast_tag. rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Erest |- *.
        rewrite ?imk_semantic in Erest; rewrite ?imk_semantic.
        rewrite Erest. reflexivity.
Qed.

(* The delimiter instance, which is what the two callers below use. *)
Local Lemma iscan_cis_marked :
  forall cis k cm tail txt prev before open base,
    denabled_of k = true ->
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    (nonempty before || nonempty_str txt || nonempty cis)%bool = true ->
    exists p,
      iscan_str (ci_text cis ++ marked_close k tail)
        (IText false txt prev
           (oemit_all before (opush_at k true cm open base)))
      = iscan_str (marked_close k tail)
          (IText false EmptyString p
            (oemit_all (ci_inlines cis)
              (flush_text txt
                 (oemit_all before (opush_at k true cm open base))))).
Proof.
  intros cis k cm tail txt prev before open base Hden Hok Hsep Hne.
  apply (iscan_cis_scope cis (marked_close k tail)
           (opush_at k true cm open base) false
           txt prev before
           (marked_close_nonempty _ _) (marked_close_starts_nontick _ _)
           (marked_close_after_verb _ _)
           (fun txt' prev' before' e =>
              iscan_marked_flush k cm tail txt' prev' before' open base Hden
                (orb_false_r_true _ e))
           Hok Hsep (fun _ => wiki_opens_opush _ _ _ _ _ _ _ _)).
  rewrite orb_false_r. exact Hne.
Qed.

(* And the bracket instance, for a label scanned inside its own scope. *)
Local Lemma iscan_cis_bracket :
  forall cis dst tail txt prev image before base,
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    bracket_kids_ok cis = true ->
    exists p,
      iscan_str (ci_text cis ++ link_close dst tail)
        (IText false txt prev (oemit_all before (bpush image base)))
      = iscan_str (link_close dst tail)
          (IText false EmptyString p
            (oemit_all (ci_inlines cis)
              (flush_text txt (oemit_all before (bpush image base))))).
Proof.
  intros cis dst tail txt prev image before base Hok Hsep Hbk.
  apply (iscan_cis_scope cis (link_close dst tail) (bpush image base) true
           txt prev before
           (link_close_nonempty _ _) (link_close_starts_nontick _ _)
           eq_refl
           (fun txt' prev' before' _ =>
              iscan_bracket_flush dst tail txt' prev' image before' base)
           Hok Hsep (wiki_opens_bracket_kids _ _ _ _ Hbk)).
  apply orb_true_r.
Qed.

(* And the reference instance, which differs only in the closer. *)
Local Lemma iscan_cis_ref :
  forall cis label tail txt prev image before base,
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    bracket_kids_ok cis = true ->
    exists p,
      iscan_str (ci_text cis ++ ref_close label tail)
        (IText false txt prev (oemit_all before (bpush image base)))
      = iscan_str (ref_close label tail)
          (IText false EmptyString p
            (oemit_all (ci_inlines cis)
              (flush_text txt (oemit_all before (bpush image base))))).
Proof.
  intros cis label tail txt prev image before base Hok Hsep Hbk.
  apply (iscan_cis_scope cis (ref_close label tail) (bpush image base) true
           txt prev before
           (ref_close_nonempty _ _) (ref_close_starts_nontick _ _)
           eq_refl
           (fun txt' prev' before' _ =>
              iscan_ref_flush label tail txt' prev' image before' base)
           Hok Hsep (wiki_opens_bracket_kids _ _ _ _ Hbk)).
  apply orb_true_r.
Qed.

(* And the named instance, whose closer is the `]` alone. *)
Local Lemma iscan_cis_tag :
  forall cis name tail txt prev before base,
    tags_enabled = true ->
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    exists p,
      iscan_str (ci_text cis ++ String rbrack tail)
        (IText false txt prev (oemit_all before (tag_push name (Spot 0 0) base)))
      = iscan_str (String rbrack tail)
          (IText false EmptyString p
            (oemit_all (ci_inlines cis)
              (flush_text txt (oemit_all before (tag_push name (Spot 0 0) base))))).
Proof.
  intros cis name tail txt prev before base Ht Hok Hsep.
  apply (iscan_cis_scope cis (String rbrack tail) (tag_push name (Spot 0 0) base) true
           txt prev before eq_refl eq_refl eq_refl
           (fun txt' prev' before' _ =>
              iscan_tag_flush name tail txt' prev' before' base Ht)
           Hok Hsep).
  - intros _. destruct before; [apply wiki_opens_tag_push|apply wiki_opens_oemit_all; reflexivity].
  - apply orb_true_r.
Qed.

(* Once a canonical scan has closed every nested delimiter, the output
   state again has an empty scope stack. *)
Local Definition flush_out (txt : string) (out : inlines) : inlines :=
  if nonempty_str txt then mk (Str txt) :: out else out.

(* The canonical scan never leaves a spec waiting -- `needs_escape`
   claims `{` -- so every state it reaches holds nodes only, and is
   written that way. *)
Local Lemma flush_text_flat :
  forall txt out,
    flush_text txt (OState (List.map OIn out) [] None)
    = OState (List.map OIn (flush_out txt out)) [] None.
Proof.
  intros txt out. unfold flush_text, flush_text_at, flush_out, oemit; cbn [os_stk].
  destruct (nonempty_str txt); reflexivity.
Qed.

(*
A line's text
-------------

`ci_line` is `ci_text_at true`: the same text as `ci_text` except that a
run ending the line may leave its last character bare.  The lemmas that
read a whole line are stated at either flag.
*)

Local Lemma ci_text_at_cons_nonstr :
  forall b c rest, match c with CIStr _ => False | _ => True end ->
    ci_text_at b (c :: rest) = (ci_src c ++ ci_text_at b rest)%string.
Proof.
  intros b c [|c' rest] H; [|apply ci_text_at_cons2].
  rewrite ci_text_at_last. cbn [ci_text_at]. rewrite append_empty_r.
  destruct c; [contradiction|..]; reflexivity.
Qed.

(* What the byte after a verbatim is asked about: the two texts start
   alike, since a run's first character is escaped at either flag. *)
Local Lemma ci_text_at_head :
  forall b cis,
    nonempty_str (ci_text_at b cis) = nonempty_str (ci_text cis)
    /\ starts_tick (ci_text_at b cis) = starts_tick (ci_text cis)
    /\ after_verb_next (ci_text_at b cis) = after_verb_next (ci_text cis).
Proof.
  intros b cis. induction cis as [|c rest IH]; [repeat split; reflexivity|].
  rewrite <- !ci_text_at_false in *.
  destruct rest as [|c' rest'].
  - rewrite !ci_text_at_last. destruct c; try (repeat split; reflexivity).
    destruct s as [|x s']; [repeat split; reflexivity|].
    cbn [escape_from bare_ok negb]. rewrite !andb_true_r.
    destruct (needs_escape x) eqn:Hx; [repeat split; reflexivity|].
    cbn [nonempty_str starts_tick after_verb_next].
    destruct (Ascii.eqb x lbrace) eqn:Hb; [|repeat split; reflexivity].
    apply Ascii.eqb_eq in Hb. subst x. rewrite needs_escape_lbrace in Hx. discriminate.
  - (* a shared head decides all three, unless it is a lone brace, which
       no constituent's source is *)
    rewrite !ci_text_at_cons2.
    destruct (ci_src c) as [|x y] eqn:Ec; [exact IH|].
    cbn [append nonempty_str starts_tick after_verb_next].
    split; [reflexivity|split; [reflexivity|]].
    destruct (Ascii.eqb x lbrace) eqn:Hb; [|reflexivity].
    destruct y as [|d y']; [exfalso|reflexivity].
    apply Ascii.eqb_eq in Hb. subst x.
    destruct c; cbn [ci_src] in Ec; try discriminate Ec.
    + destruct s as [|x s']; [discriminate Ec|].
      unfold escape_str in Ec. cbn [escape_from bare_ok negb] in Ec.
      rewrite andb_true_r in Ec.
      destruct (needs_escape x) eqn:Hx; injection Ec as Ex Es; [discriminate Ex|].
      subst x. rewrite needs_escape_lbrace in Hx. discriminate.
    + unfold verb_text in Ec. pose proof (verb_ticks_nonzero s) as Hn.
      destruct (verb_ticks s) as [|k]; [contradiction|]. cbn in Ec. discriminate Ec.
    + unfold marked_open in Ec. pose proof (dtoken_nonempty k) as Hk.
      destruct (dtoken k) as [|t tk]; [discriminate Hk|].
      cbn in Ec. injection Ec as Ec. discriminate Ec.
    + unfold bracket_open in Ec. destruct img; cbn in Ec; discriminate Ec.
    + unfold bracket_open in Ec. destruct img; cbn in Ec; discriminate Ec.
    + unfold raw_text, verb_text in Ec. pose proof (verb_ticks_nonzero s) as Hn.
      destruct (verb_ticks s) as [|k]; [contradiction|]. cbn in Ec. discriminate Ec.
    + unfold wiki_text, bracket_open in Ec. destruct embed; cbn in Ec; discriminate Ec.
    + unfold tag_open in Ec. destruct name; cbn in Ec; discriminate Ec.
Qed.

Local Lemma iscan_cis :
  forall b cis prev' txt out,
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    ifinish (iscan_str (ci_text_at b cis)
               (IText false txt prev' (OState (List.map OIn out) [] None)))
    = (List.rev (flush_out txt out) ++ ci_inlines cis)%list.
Proof.
  intros b cis. pattern cis.
  apply (well_founded_induction (well_founded_ltof _ cis_size)).
  clear cis. intros cis IH prev' txt out Hok Hsep.
  destruct cis as [|c rest].
  - cbn [ci_text_at ci_inlines iscan_str]. rewrite app_nil_r.
    rewrite ifinish_text, flush_text_flat; cbn [os_out].
    rewrite oresolve_map. reflexivity.
  - assert (Hrestlt : ltof (list cinline) cis_size rest (c :: rest)).
    { unfold ltof. cbn [cis_size]. pose proof (ci_size_pos c). lia. }
    destruct c as [s|v|d kids|img kids dst|rimg rkids rlabel|label|a|rf rv|we wt wal|tn tkids].
    + destruct txt as [|x txt']; [|discriminate].
      pose proof (cis_ok_head (CIStr s) rest Hok) as Hsok.
      cbn [ci_ok] in Hsok. apply andb_true_iff in Hsok as [Hs _].
      assert (Hstr :
        iscan_str (ci_text_at b (CIStr s :: rest))
          (IText false EmptyString prev' (OState (List.map OIn out) [] None))
        = iscan_str (ci_text_at b rest)
            (IText false s (str_last s prev') (OState (List.map OIn out) [] None))
        \/ rest = [] /\ b = true).
      { destruct rest as [|r rest'].
        - destruct b; [right; split; reflexivity|left].
          rewrite ci_text_at_last. apply iscan_escape.
        - left. rewrite ci_text_at_cons2. cbn [ci_src].
          rewrite iscan_str_app, iscan_escape. reflexivity. }
      destruct Hstr as [Hstr|[-> ->]].
      2:{ rewrite ci_text_at_last, ifinish_escape_end. cbn [append].
          change (IText false s (str_last s prev') (OState (List.map OIn out) [] None))
            with (iscan_str (ci_text_at true [])
                    (IText false s (str_last s prev') (OState (List.map OIn out) [] None))).
          cbn [ci_inlines map].
          rewrite <- ?List.map_cons;
          rewrite (IH [] ltac:(unfold ltof; cbn [cis_size ci_size]; lia)
                     (str_last s prev') s out).
          - unfold flush_out at 1. rewrite Hs.
            cbn [List.rev nonempty_str ci_ast map].
            rewrite <- List.app_assoc. reflexivity.
          - reflexivity.
          - destruct s; [discriminate Hs|reflexivity]. }
      rewrite Hstr.
      cbn [ci_inlines map append].
      rewrite <- ?List.map_cons;
      rewrite (IH rest Hrestlt (str_last s prev') s out).
      * unfold flush_out at 1. rewrite Hs.
        cbn [List.rev nonempty_str ci_ast map].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * apply ci_str_tail_sep; assumption.
    + pose proof (ci_verb_nonempty v rest Hok) as Hvne.
      pose proof (ci_verb_content_ok v rest Hok) as Hvok.
      rewrite ci_text_at_cons_nonstr by exact I. cbn [ci_src]. rewrite iscan_str_app.
      rewrite iscan_verb_text_nonempty by auto using verb_content_safe.
      rewrite flush_text_flat.
      destruct rest as [|r rest'].
      * cbn [ci_text_at ci_inlines map append].
        cbn [iscan_str].
        unfold ifinish, ifinish_rev;
        cbn [ifinish_ostate ifinish_ostate_flat iresolve].
        tred.
        rewrite nat_eqb_refl, trim_verb_pad by exact Hvok. cbn [vnode].
        unfold oemit, ofinish. rewrite oitems_of_spec.
        cbn [os_stk os_out oflatten oapp].
        rewrite <- ?List.map_cons, oresolve_map. cbn [List.rev ci_ast]. reflexivity.
      * destruct (after_verb_rest_nontick v r rest' Hok) as [Hne [Htick Hnx]].
        destruct (ci_text_at_head b (r :: rest')) as (E1 & E2 & E3).
        rewrite <- E1 in Hne. rewrite <- E2 in Htick. rewrite <- E3 in Hnx.
        rewrite (iscan_after_verb_nontick _ _ _ _ Hne Htick Hnx).
        rewrite trim_verb_pad by exact Hvok. cbn [vnode].
        cbn [oemit os_stk os_out os_word_start].
        rewrite <- ?List.map_cons.
        rewrite (IH (r :: rest') Hrestlt (Some tick) EmptyString
          (mk (Verbatim v) :: flush_out txt out)).
        -- cbn [flush_out nonempty_str ci_inlines map ci_ast List.rev].
           rewrite <- List.app_assoc. reflexivity.
        -- exact (cis_ok_tail _ _ Hok).
        -- reflexivity.
    + pose proof (cis_ok_head (CIDelim d kids) rest Hok) as Hdk.
      rewrite ci_ok_delim in Hdk. apply andb_true_iff in Hdk as [Hdk Hkidsok].
      apply andb_true_iff in Hdk as [Hden Hkidsne].
      destruct (iscan_marked_open_app d
                  (ci_text kids ++ marked_close d (ci_text_at b rest))
                  txt prev' (OState (List.map OIn out) [] None) Hden
                  (nonempty_str_app_l _ _ (marked_close_nonempty _ _)))
        as [cm [op Eopen]].
      pose proof (iscan_cis_marked kids d cm (ci_text_at b rest) EmptyString
        (Some (dchar d)) [] op
        (flush_text txt (OState (List.map OIn out) [] None))
        Hden Hkidsok eq_refl) as IHkids.
      assert (Hkn :
        nonempty (@nil (node inline)) || nonempty_str EmptyString ||
        nonempty kids = true).
      { cbn. exact Hkidsne. }
      destruct (IHkids Hkn) as [pk Ekids].
      rewrite ci_text_at_cons_nonstr by exact I. cbn [ci_inlines map]. rewrite ci_src_delim.
      assert (Hsrc :
        ((marked_open d ++ (ci_text kids ++ marked_close d EmptyString))
           ++ ci_text_at b rest)%string
        = (marked_open d ++
            (ci_text kids ++ marked_close d (ci_text_at b rest)))%string).
      { rewrite !append_assoc, marked_close_app. reflexivity. }
      rewrite Hsrc, Eopen.
      cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids. rewrite Ekids.
      assert (Hkins : nonempty (ci_inlines kids) = true).
      { destruct kids; [discriminate|reflexivity]. }
      rewrite (iscan_marked_close_emit d cm _ (ci_inlines kids) op _ pk Hden
                 Hkins).
      rewrite <- ci_ast_delim.
      destruct (flush_text txt (OState (List.map OIn out) [] None))
        as [out' stk' word'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk Eword. subst out' stk' word'.
      cbn [oemit os_out os_stk os_word_start].
      rewrite <- ?List.map_cons;
      rewrite (IH rest Hrestlt (Some rbrace) EmptyString
        (ci_ast (CIDelim d kids) :: flush_out txt out)).
      * cbn [flush_out nonempty_str ci_inlines map List.rev].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * reflexivity.
    + pose proof (cis_ok_head (CILink img kids dst) rest Hok) as Hdk.
      rewrite ci_ok_link in Hdk. apply andb_true_iff in Hdk as [Hdk Hbk].
    apply andb_true_iff in Hdk as [Hnl Hkidsok].
      destruct (iscan_cis_bracket kids dst (ci_text_at b rest) EmptyString
        (Some lbrack) img [] (flush_text txt (OState (List.map OIn out) [] None))
        Hkidsok eq_refl Hbk) as [pk Ekids].
      rewrite ci_text_at_cons_nonstr by exact I. cbn [ci_inlines map]. rewrite ci_src_link.
      assert (Hsrc :
        ((bracket_open img ++ (ci_text kids ++ link_close dst EmptyString)) ++
          ci_text_at b rest)%string
        = (bracket_open img ++
            (ci_text kids ++ link_close dst (ci_text_at b rest)))%string).
      { rewrite append_assoc, append_assoc, link_close_app. reflexivity. }
      rewrite Hsrc, iscan_str_app, iscan_bracket_open
        by (rewrite wiki_opens_top; apply orb_true_r).
      cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids. rewrite Ekids.
      rewrite (iscan_link_close dst _ (ci_inlines kids) img _ pk Hnl).
      rewrite <- ci_ast_link.
      destruct (flush_text txt (OState (List.map OIn out) [] None))
        as [out' stk' word'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk Eword. subst out' stk' word'.
      cbn [oemit os_out os_stk os_word_start].
      rewrite <- ?List.map_cons;
      rewrite (IH rest Hrestlt (Some rparen) EmptyString
        (ci_ast (CILink img kids dst) :: flush_out txt out)).
      * cbn [flush_out nonempty_str ci_inlines map List.rev].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * reflexivity.
    + pose proof (cis_ok_head (CIRef rimg rkids rlabel) rest Hok) as Hdk.
      rewrite ci_ok_ref in Hdk. apply andb_true_iff in Hdk as [Hdk Hbk].
      apply andb_true_iff in Hdk as [Hlab Hkidsok].
      apply andb_true_iff in Hlab as [Hlab Hnorm].
      apply andb_true_iff in Hlab as [Hne' Hbr].
      apply String.eqb_eq in Hnorm.
      destruct (iscan_cis_ref rkids rlabel (ci_text_at b rest) EmptyString
        (Some lbrack) rimg [] (flush_text txt (OState (List.map OIn out) [] None))
        Hkidsok eq_refl Hbk) as [pk Ekids].
      rewrite ci_text_at_cons_nonstr by exact I. cbn [ci_inlines map]. rewrite ci_src_ref.
      assert (Hsrc :
        ((bracket_open rimg ++ (ci_text rkids ++ ref_close rlabel EmptyString)) ++
          ci_text_at b rest)%string
        = (bracket_open rimg ++
            (ci_text rkids ++ ref_close rlabel (ci_text_at b rest)))%string).
      { rewrite append_assoc, append_assoc, ref_close_app. reflexivity. }
      rewrite Hsrc, iscan_str_app, iscan_bracket_open
        by (rewrite wiki_opens_top; apply orb_true_r).
      cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids. rewrite Ekids.
      rewrite (iscan_ref_close rlabel _ (ci_inlines rkids) rimg _ pk Hne' Hbr),
              Hnorm.
      rewrite <- ci_ast_ref.
      destruct (flush_text txt (OState (List.map OIn out) [] None))
        as [out' stk' word'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk Eword. subst out' stk' word'.
      cbn [oemit os_out os_stk os_word_start].
      rewrite <- ?List.map_cons;
      rewrite (IH rest Hrestlt (Some rbrack) EmptyString
        (ci_ast (CIRef rimg rkids rlabel) :: flush_out txt out)).
      * cbn [flush_out nonempty_str ci_inlines map List.rev].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * reflexivity.
    + pose proof (cis_ok_head (CINote label) rest Hok) as Hnote.
      rewrite ci_ok_note in Hnote.
      apply andb_true_iff in Hnote as [Hnote Hnorm].
      apply andb_true_iff in Hnote as [Hnotes Hsafe].
      apply String.eqb_eq in Hnorm.
      rewrite ci_text_at_cons_nonstr by exact I. cbn [ci_inlines map].
      change (ci_src (CINote label)) with (note_text label).
      rewrite (iscan_note_text label (ci_text_at b rest) txt prev'
                 (OState (List.map OIn out) [] None) Hnotes Hsafe
                 (wiki_opens_top _ _ _ _)), Hnorm.
      destruct (flush_text txt (OState (List.map OIn out) [] None))
        as [out' stk' word'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk Eword. subst out' stk' word'.
      cbn [oemit os_out os_stk os_word_start].
      change (mk (FootnoteReference label)) with (ci_ast (CINote label)).
      rewrite <- ?List.map_cons;
      rewrite (IH rest Hrestlt (Some rbrack) EmptyString
        (ci_ast (CINote label) :: flush_out txt out)).
      * cbn [flush_out nonempty_str ci_ast List.rev].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * reflexivity.
    + pose proof (cis_ok_head (CIAuto a) rest Hok) as Hauto.
      rewrite ci_ok_auto in Hauto.
      apply andb_true_iff in Hauto as [Hbody Hkind].
      rewrite ci_text_at_cons_nonstr by exact I. cbn [ci_inlines map].
      change (ci_src (CIAuto a)) with (auto_text a).
      rewrite (iscan_auto_text a (ci_text_at b rest) txt prev'
                 (OState (List.map OIn out) [] None) Hbody Hkind).
      destruct (flush_text txt (OState (List.map OIn out) [] None))
        as [out' stk' word'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk Eword. subst out' stk' word'.
      cbn [oemit os_out os_stk os_word_start].
      change (mk (auto_node a)) with (ci_ast (CIAuto a)).
      rewrite <- ?List.map_cons;
      rewrite (IH rest Hrestlt (Some gt) EmptyString
        (ci_ast (CIAuto a) :: flush_out txt out)).
      * cbn [flush_out nonempty_str ci_ast List.rev].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * reflexivity.
    + pose proof (cis_ok_head (CIRaw rf rv) rest Hok) as Hraw.
      rewrite ci_ok_raw in Hraw.
      apply andb_true_iff in Hraw as [Hraw Hfmt].
      apply andb_true_iff in Hraw as [Hraw Hrok].
      apply andb_true_iff in Hraw as [Hcap Hrne].
      rewrite ci_text_at_cons_nonstr by exact I. cbn [ci_inlines map].
      change (ci_src (CIRaw rf rv)) with (raw_text rf rv).
      rewrite (iscan_raw_text rf rv (ci_text_at b rest) txt prev'
                 (OState (List.map OIn out) [] None) Hcap Hrne Hrok Hfmt).
      destruct (flush_text txt (OState (List.map OIn out) [] None))
        as [out' stk' word'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk Eword. subst out' stk' word'.
      cbn [oemit os_out os_stk os_word_start].
      change (mk (RawInline rf rv)) with (ci_ast (CIRaw rf rv)).
      rewrite <- ?List.map_cons;
      rewrite (IH rest Hrestlt (Some rbrace) EmptyString
        (ci_ast (CIRaw rf rv) :: flush_out txt out)).
      * cbn [flush_out nonempty_str ci_ast List.rev].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * reflexivity.
    + pose proof (cis_ok_head (CIWiki we wt wal) rest Hok) as Hwk.
      rewrite ci_text_at_cons_nonstr by exact I. cbn [ci_inlines map].
      change (ci_src (CIWiki we wt wal)) with (wiki_text we wt wal).
      rewrite (iscan_wiki_text we wt wal (ci_text_at b rest) txt prev'
                 (OState (List.map OIn out) [] None) Hwk)
        by (rewrite wiki_opens_top; apply orb_true_r).
      destruct (flush_text txt (OState (List.map OIn out) [] None))
        as [out' stk' word'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk Eword. subst out' stk' word'.
      cbn [oemit os_out os_stk os_word_start].
      change (mk (Ext_wikilink we wt wal)) with (ci_ast (CIWiki we wt wal)).
      rewrite <- ?List.map_cons;
      rewrite (IH rest Hrestlt (Some rbrack) EmptyString
        (ci_ast (CIWiki we wt wal) :: flush_out txt out)).
      * cbn [flush_out nonempty_str ci_ast List.rev].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * reflexivity.
    + pose proof (cis_ok_head (CITag tn tkids) rest Hok) as Htk.
      rewrite ci_ok_tag in Htk. apply andb_true_iff in Htk as [Htk Hkidsok].
      apply andb_true_iff in Htk as [Hten Hname].
      destruct (iscan_cis_tag tkids tn (ci_text_at b rest) EmptyString
        (Some lbrack) [] (flush_text txt (OState (List.map OIn out) [] None))
        Hten Hkidsok eq_refl) as [pk Ekids].
      rewrite ci_text_at_cons_nonstr by exact I. cbn [ci_inlines map]. rewrite ci_src_tag.
      assert (Hsrc :
        ((tag_open tn ++ (ci_text tkids ++ one rbrack)) ++ ci_text_at b rest)%string
        = (tag_open tn ++ (ci_text tkids ++ String rbrack (ci_text_at b rest)))%string).
      { rewrite !append_assoc. reflexivity. }
      rewrite Hsrc, iscan_str_app, iscan_tag_open
        by first [assumption | exact (text_sep_tag _ _ _ _ Hsep)].
      cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids. rewrite Ekids.
      rewrite (iscan_tag_close tn _ (ci_inlines tkids) _ pk Hten).
      rewrite <- ci_ast_tag.
      destruct (flush_text txt (OState (List.map OIn out) [] None))
        as [out' stk' word'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk Eword. subst out' stk' word'.
      cbn [oemit os_out os_stk os_word_start].
      rewrite <- ?List.map_cons;
      rewrite (IH rest Hrestlt (Some rbrack) EmptyString
        (ci_ast (CITag tn tkids) :: flush_out txt out)).
      * cbn [flush_out nonempty_str ci_inlines map List.rev].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * reflexivity.
Qed.

(* The other half of what a canonical line owes the paragraph: it leaves
   the scan owing nothing to the next line.  Every canonical constituent
   either stays in `IText` (a string) or resolves its closing run before
   the line ends (a verbatim).  An empty verbatim would not: two adjacent
   runs leave `IOpen`, which is why `ci_ok` excludes it. *)
Local Lemma iscan_cis_closed :
  forall b cis prev' txt out,
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    iscan_closed (iscan_str (ci_text_at b cis)
                    (IText false txt prev' (OState (List.map OIn out) [] None)))
    = true.
Proof.
  intros b cis. pattern cis.
  apply (well_founded_induction (well_founded_ltof _ cis_size)).
  clear cis. intros cis IH prev' txt out Hok Hsep.
  destruct cis as [|c rest]; [reflexivity|].
  assert (Hrestlt : ltof (list cinline) cis_size rest (c :: rest)).
  { unfold ltof. cbn [cis_size]. pose proof (ci_size_pos c). lia. }
  destruct c as [s|v|d kids|img kids dst|rimg rkids rlabel|label|a|rf rv|we wt wal|tn tkids].
  - destruct txt as [|x txt']; [|discriminate Hsep].
    pose proof (cis_ok_head (CIStr s) rest Hok) as Hsok.
    cbn [ci_ok] in Hsok. apply andb_true_iff in Hsok as [Hs _].
    destruct rest as [|r rest'].
    + rewrite ci_text_at_last. destruct b.
      * rewrite iscan_closed_escape_end.
        exact (IH [] Hrestlt _ _ out (cis_ok_tail _ _ Hok) (text_sep_nil _)).
      * change (escape_from false EmptyString s) with (escape_str s).
        rewrite iscan_escape.
        exact (IH [] Hrestlt _ _ out (cis_ok_tail _ _ Hok) (text_sep_nil _)).
    + rewrite ci_text_at_cons2. cbn [ci_src]. rewrite iscan_str_app, iscan_escape.
      exact (IH (r :: rest') Hrestlt _ _ _ (cis_ok_tail _ _ Hok)
               (ci_str_tail_sep s _ Hok Hs)).
  - pose proof (ci_verb_nonempty v rest Hok) as Hvne.
    pose proof (ci_verb_content_ok v rest Hok) as Hvok.
    rewrite ci_text_at_cons_nonstr by exact I. cbn [ci_src]. rewrite iscan_str_app.
    rewrite iscan_verb_text_nonempty by auto using verb_content_safe.
    rewrite flush_text_flat.
    destruct rest as [|r rest'].
    + cbn [ci_text_at iscan_str iscan_closed iclosed_at iresolve os_stk null].
      rewrite nat_eqb_refl. reflexivity.
    + destruct (after_verb_rest_nontick v r rest' Hok) as [Hne [Htick Hnx]].
      destruct (ci_text_at_head b (r :: rest')) as (E1 & E2 & E3).
      rewrite <- E1 in Hne. rewrite <- E2 in Htick. rewrite <- E3 in Hnx.
      rewrite (iscan_after_verb_nontick _ _ _ _ Hne Htick Hnx).
      rewrite trim_verb_pad by exact Hvok. cbn [vnode].
      cbn [oemit os_out os_stk os_word_start].
      rewrite <- ?List.map_cons.
      apply (IH (r :: rest') Hrestlt); [exact (cis_ok_tail _ _ Hok)|reflexivity].
  - pose proof (cis_ok_head (CIDelim d kids) rest Hok) as Hdk.
    rewrite ci_ok_delim in Hdk. apply andb_true_iff in Hdk as [Hdk Hkidsok].
    apply andb_true_iff in Hdk as [Hden Hkidsne].
    destruct (iscan_marked_open_app d
                (ci_text kids ++ marked_close d (ci_text_at b rest))
                txt prev' (OState (List.map OIn out) [] None) Hden
                (nonempty_str_app_l _ _ (marked_close_nonempty _ _)))
      as [cm [op Eopen]].
    pose proof (iscan_cis_marked kids d cm (ci_text_at b rest) EmptyString
      (Some (dchar d)) [] op
      (flush_text txt (OState (List.map OIn out) [] None))
      Hden Hkidsok eq_refl) as IHkids.
    assert (Hkn :
      nonempty (@nil (node inline)) || nonempty_str EmptyString ||
      nonempty kids = true).
    { cbn. exact Hkidsne. }
    destruct (IHkids Hkn) as [pk Ekids].
    rewrite ci_text_at_cons_nonstr by exact I. rewrite ci_src_delim.
    assert (Hsrc :
      ((marked_open d ++ (ci_text kids ++ marked_close d EmptyString))
         ++ ci_text_at b rest)%string
      = (marked_open d ++
          (ci_text kids ++ marked_close d (ci_text_at b rest)))%string).
    { rewrite !append_assoc, marked_close_app. reflexivity. }
    rewrite Hsrc, Eopen.
    cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids. rewrite Ekids.
    assert (Hkins : nonempty (ci_inlines kids) = true).
    { destruct kids; [discriminate|reflexivity]. }
    rewrite (iscan_marked_close_emit d cm _ (ci_inlines kids) op _ pk Hden Hkins).
    destruct (flush_text txt (OState (List.map OIn out) [] None))
      as [out' stk' word'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk Eword. subst out' stk' word'.
    cbn [oemit os_out os_stk os_word_start]. rewrite <- ?List.map_cons.
    apply (IH rest Hrestlt); [exact (cis_ok_tail _ _ Hok)|reflexivity].
  - pose proof (cis_ok_head (CILink img kids dst) rest Hok) as Hdk.
    rewrite ci_ok_link in Hdk. apply andb_true_iff in Hdk as [Hdk Hbk].
    apply andb_true_iff in Hdk as [Hnl Hkidsok].
    destruct (iscan_cis_bracket kids dst (ci_text_at b rest) EmptyString
      (Some lbrack) img [] (flush_text txt (OState (List.map OIn out) [] None))
      Hkidsok eq_refl Hbk) as [pk Ekids].
    rewrite ci_text_at_cons_nonstr by exact I. rewrite ci_src_link.
    assert (Hsrc :
      ((bracket_open img ++ (ci_text kids ++ link_close dst EmptyString)) ++
        ci_text_at b rest)%string
      = (bracket_open img ++
          (ci_text kids ++ link_close dst (ci_text_at b rest)))%string).
    { rewrite append_assoc, append_assoc, link_close_app. reflexivity. }
    rewrite Hsrc, iscan_str_app, iscan_bracket_open
        by (rewrite wiki_opens_top; apply orb_true_r).
    cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids. rewrite Ekids.
    rewrite (iscan_link_close dst _ (ci_inlines kids) img _ pk Hnl).
    destruct (flush_text txt (OState (List.map OIn out) [] None))
      as [out' stk' word'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk Eword. subst out' stk' word'.
    cbn [oemit os_out os_stk os_word_start]. rewrite <- ?List.map_cons.
    apply (IH rest Hrestlt); [exact (cis_ok_tail _ _ Hok)|reflexivity].
  - pose proof (cis_ok_head (CIRef rimg rkids rlabel) rest Hok) as Hdk.
    rewrite ci_ok_ref in Hdk. apply andb_true_iff in Hdk as [Hdk Hbk].
    apply andb_true_iff in Hdk as [Hlab Hkidsok].
    apply andb_true_iff in Hlab as [Hlab Hnorm].
    apply andb_true_iff in Hlab as [Hne' Hbr].
    destruct (iscan_cis_ref rkids rlabel (ci_text_at b rest) EmptyString
      (Some lbrack) rimg [] (flush_text txt (OState (List.map OIn out) [] None))
      Hkidsok eq_refl Hbk) as [pk Ekids].
    rewrite ci_text_at_cons_nonstr by exact I. rewrite ci_src_ref.
    assert (Hsrc :
      ((bracket_open rimg ++ (ci_text rkids ++ ref_close rlabel EmptyString)) ++
        ci_text_at b rest)%string
      = (bracket_open rimg ++
          (ci_text rkids ++ ref_close rlabel (ci_text_at b rest)))%string).
    { rewrite append_assoc, append_assoc, ref_close_app. reflexivity. }
    rewrite Hsrc, iscan_str_app, iscan_bracket_open
        by (rewrite wiki_opens_top; apply orb_true_r).
    cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids. rewrite Ekids.
    rewrite (iscan_ref_close rlabel _ (ci_inlines rkids) rimg _ pk Hne' Hbr).
    destruct (flush_text txt (OState (List.map OIn out) [] None))
      as [out' stk' word'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk Eword. subst out' stk' word'.
    cbn [oemit os_out os_stk os_word_start]. rewrite <- ?List.map_cons.
    apply (IH rest Hrestlt); [exact (cis_ok_tail _ _ Hok)|reflexivity].
  - pose proof (cis_ok_head (CINote label) rest Hok) as Hnote.
    rewrite ci_ok_note in Hnote.
    apply andb_true_iff in Hnote as [Hnote Hnorm].
    apply andb_true_iff in Hnote as [Hnotes Hsafe].
    rewrite ci_text_at_cons_nonstr by exact I. change (ci_src (CINote label)) with (note_text label).
    rewrite (iscan_note_text label (ci_text_at b rest) txt prev'
               (OState (List.map OIn out) [] None) Hnotes Hsafe
                 (wiki_opens_top _ _ _ _)).
    destruct (flush_text txt (OState (List.map OIn out) [] None))
      as [out' stk' word'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk Eword. subst out' stk' word'.
    cbn [oemit os_out os_stk os_word_start]. rewrite <- ?List.map_cons.
    apply (IH rest Hrestlt); [exact (cis_ok_tail _ _ Hok)|reflexivity].
  - pose proof (cis_ok_head (CIAuto a) rest Hok) as Hauto.
    rewrite ci_ok_auto in Hauto.
    apply andb_true_iff in Hauto as [Hbody Hkind].
    rewrite ci_text_at_cons_nonstr by exact I. change (ci_src (CIAuto a)) with (auto_text a).
    rewrite (iscan_auto_text a (ci_text_at b rest) txt prev'
               (OState (List.map OIn out) [] None) Hbody Hkind).
    destruct (flush_text txt (OState (List.map OIn out) [] None))
      as [out' stk' word'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk Eword. subst out' stk' word'.
    cbn [oemit os_out os_stk os_word_start]. rewrite <- ?List.map_cons.
    apply (IH rest Hrestlt); [exact (cis_ok_tail _ _ Hok)|reflexivity].
  - pose proof (cis_ok_head (CIRaw rf rv) rest Hok) as Hraw.
    rewrite ci_ok_raw in Hraw.
    apply andb_true_iff in Hraw as [Hraw Hfmt].
    apply andb_true_iff in Hraw as [Hraw Hrok].
    apply andb_true_iff in Hraw as [Hcap Hrne].
    rewrite ci_text_at_cons_nonstr by exact I. change (ci_src (CIRaw rf rv)) with (raw_text rf rv).
    rewrite (iscan_raw_text rf rv (ci_text_at b rest) txt prev'
               (OState (List.map OIn out) [] None) Hcap Hrne Hrok Hfmt).
    destruct (flush_text txt (OState (List.map OIn out) [] None))
      as [out' stk' word'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk Eword. subst out' stk' word'.
    cbn [oemit os_out os_stk os_word_start]. rewrite <- ?List.map_cons.
    apply (IH rest Hrestlt); [exact (cis_ok_tail _ _ Hok)|reflexivity].
  - pose proof (cis_ok_head (CIWiki we wt wal) rest Hok) as Hwk.
    rewrite ci_text_at_cons_nonstr by exact I. change (ci_src (CIWiki we wt wal)) with (wiki_text we wt wal).
    rewrite (iscan_wiki_text we wt wal (ci_text_at b rest) txt prev'
               (OState (List.map OIn out) [] None) Hwk)
      by (rewrite wiki_opens_top; apply orb_true_r).
    destruct (flush_text txt (OState (List.map OIn out) [] None))
      as [out' stk' word'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk Eword. subst out' stk' word'.
    cbn [oemit os_out os_stk os_word_start]. rewrite <- ?List.map_cons.
    apply (IH rest Hrestlt); [exact (cis_ok_tail _ _ Hok)|reflexivity].
  - pose proof (cis_ok_head (CITag tn tkids) rest Hok) as Htk.
    rewrite ci_ok_tag in Htk. apply andb_true_iff in Htk as [Htk Hkidsok].
    apply andb_true_iff in Htk as [Hten Hname].
    destruct (iscan_cis_tag tkids tn (ci_text_at b rest) EmptyString
      (Some lbrack) [] (flush_text txt (OState (List.map OIn out) [] None))
      Hten Hkidsok eq_refl) as [pk Ekids].
    rewrite ci_text_at_cons_nonstr by exact I. rewrite ci_src_tag.
    assert (Hsrc :
      ((tag_open tn ++ (ci_text tkids ++ one rbrack)) ++ ci_text_at b rest)%string
      = (tag_open tn ++ (ci_text tkids ++ String rbrack (ci_text_at b rest)))%string).
    { rewrite !append_assoc. reflexivity. }
    rewrite Hsrc, iscan_str_app, iscan_tag_open
      by first [assumption | exact (text_sep_tag _ _ _ _ Hsep)].
    cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids. rewrite Ekids.
    rewrite (iscan_tag_close tn _ (ci_inlines tkids) _ pk Hten).
    destruct (flush_text txt (OState (List.map OIn out) [] None))
      as [out' stk' word'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk Eword. subst out' stk' word'.
    cbn [oemit os_out os_stk os_word_start]. rewrite <- ?List.map_cons.
    apply (IH rest Hrestlt); [exact (cis_ok_tail _ _ Hok)|reflexivity].
Qed.

(* Every way a pending delimiter can resolve lands back in text mode:
   closing, opening and decaying to literal text all do.  So after
   `iresolve` no state waiting on a next byte is left, and the catch-all
   arms of `ibreak` and `ifinish_ostate` are dead. *)
Local Lemma idelim_done_text :
  forall k txt bef marker next o,
    exists txt' prev' o',
      idelim_done k txt bef marker next o = IText false txt' prev' o'.
Proof.
  intros k txt bef marker next o. unfold idelim_done.
  destruct (dbare k bef && negb marker && nonspace_at next)%bool; eauto.
Qed.

Lemma idelim_resolve_text :
  forall k txt bef marker next o,
    exists txt' prev' o',
      idelim_resolve k txt bef marker next o = IText false txt' prev' o'.
Proof.
  intros k txt bef marker next o.
  unfold idelim_resolve; rewrite !oclose_guard; tred.
  destruct (nonspace_at bef || marker)%bool; [|apply idelim_done_text].
  sem_flush. destruct (sclose k marker (flush_text txt o)); [eauto|].
  destruct (oclose_barred k marker o); [eauto | apply idelim_done_text].
Qed.

Lemma iresolve_resolved :
  forall st,
    match iresolve st with
    | IBrace _ _ _ | IBang _ _ _ | IDollar _ _ _ _
    | IPeriod _ _ _ _ | IDash _ _ _ _
    | IDelim _ _ _ _ _ _ | IClosed _ _ => False
    | _ => True
    end.
Proof.
  intros [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|mt me ms mx ml msh mo|mct mcs mcx mcl mcsh mco|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|cltxt clob|kids img sp ssrc sob|ap asrc atxt aprev ash aob|kids img label ob|nesc nimg nlab nob|wesc wrb wimg wreg wob|kids img esc depth dst sh ob|asrc atxt aob|salias stxt sob|rspec rtxt rob];
    cbn [iresolve]; try exact I.
  - destruct (Nat.ltb (S seen) (dwidth k)); [exact I|].
    destruct mrk; [exact I|].
    destruct (idelim_resolve_text k txt cc false None o) as [txt' [prev' [o' E]]].
    rewrite E. exact I.
Qed.

Local Lemma parse_inline_line_escape :
  forall s, nonempty_str s = true ->
  parse_inline_line (escape_str s) = [mk (Str s)].
Proof.
  intros s H. unfold parse_inline_line, istart. rewrite iscan_escape.
  change (EmptyString ++ s)%string with s.
  unfold ifinish, ifinish_rev.
  cbn [ifinish_ostate ifinish_ostate_flat iresolve]. unfold flush_text, flush_text_at; tred.
  rewrite H. reflexivity.
Qed.

(* The per-line equation, which holds when the line leaves the scan
   closed.  A line that leaves it mid-span does not contribute a
   separable run of inlines, because a later line finishes the span. *)
Local Lemma para_inlines_cons2_closed :
  forall x y rest,
    iscan_closed (iscan_str x istart) = true ->
    para_inlines (x :: y :: rest) =
    (parse_inline_line x ++ mk SoftBreak :: para_inlines (y :: rest))%list.
Proof.
  intros x y rest Hcl. unfold para_inlines, parse_inline_line.
  rewrite iscan_lines_cons2, (ibreak_closed _ Hcl), ?imk_here_semantic.
  change (IText false EmptyString None
            (OState (OIn (mk SoftBreak) :: ifinish_items (iscan_str x istart))
               [] None))
    with (iout_app (OIn (mk SoftBreak) :: ifinish_items (iscan_str x istart))
            istart).
  rewrite iscan_lines_out_app, ifinish_out_app by reflexivity.
  rewrite oresolve_cons_nonplain by reflexivity.
  rewrite <- (ifinish_rev_items (iscan_str x istart)).
  cbn [List.rev]. rewrite <- List.app_assoc. reflexivity.
Qed.

(*
The pass inverts the view
=========================
*)

(** Parsing a canonical line's text gives back its inlines.  Nothing is
    asked of the list but `cis_ok`: the empty line is the empty scan, which
    is what lets a table cell be empty. *)
Lemma parse_inline_line_ci :
  forall cis, cis_ok cis = true ->
  parse_inline_line (ci_line cis) = ci_inlines cis.
Proof.
  intros cis Hok.
  unfold parse_inline_line, istart, ostart, ci_line.
  change (@nil oitem) with (List.map OIn (@nil (node inline))).
  rewrite (iscan_cis true cis None EmptyString []).
  - reflexivity.
  - exact Hok.
  - reflexivity.
Qed.

(** The same for text that does not end its line, such as a key's label,
    which the colon follows. *)
Lemma parse_inline_text_ci :
  forall cis, cis_ok cis = true ->
  parse_inline_line (ci_text cis) = ci_inlines cis.
Proof.
  intros cis Hok.
  unfold parse_inline_line, istart, ostart. rewrite <- ci_text_at_false.
  change (@nil oitem) with (List.map OIn (@nil (node inline))).
  rewrite (iscan_cis false cis None EmptyString []).
  - reflexivity.
  - exact Hok.
  - reflexivity.
Qed.

(** The same, a paragraph at a time.  The last hypothesis is `para_ok`'s
    trailing-whitespace conjunct: `para_inlines` strips the final line,
    so the two agree exactly when there is nothing to strip. *)
Lemma para_inlines_ci_para :
  forall lss,
    forallb cis_ok lss = true ->
    forallb nonempty lss = true ->
    strip_trailing_ws (last (map ci_line lss) EmptyString)
      = last (map ci_line lss) EmptyString ->
    para_inlines (map ci_line lss) = ci_para lss.
Proof.
  induction lss as [|cis rest IH]; intros Hok Hne Hlast; [reflexivity|].
  cbn [forallb] in Hok, Hne.
  apply andb_true_iff in Hok as [Hc Hr].
  apply andb_true_iff in Hne as [Hn Hnr].
  destruct rest as [|cis2 rest'].
  - cbn [map last] in Hlast |- *.
    rewrite para_inlines_one, Hlast.
    change (parse_inline_line (ci_line cis) = ci_para [cis]).
    rewrite ci_para_one. apply parse_inline_line_ci; assumption.
  - cbn [map] in *.
    rewrite para_inlines_cons2_closed
      by (unfold ci_line, istart, ostart;
          change (@nil oitem) with (List.map OIn (@nil (node inline)));
          apply (iscan_cis_closed true); [exact Hc|reflexivity]).
    rewrite ci_para_cons2, (parse_inline_line_ci cis Hc).
    f_equal. f_equal.
    apply IH; [exact Hr | exact Hnr |].
    rewrite last_cons_nonnil in Hlast by discriminate. exact Hlast.
Qed.

End WithTable.
