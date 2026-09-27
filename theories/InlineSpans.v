(* ai-disclosure: autonomous *)

(** * Where the located scan puts delimiter nodes

   The syntax reference on emphasis: a delimiter "can open emphasis only
   if it is not directly followed by whitespace.  It can close ... only
   if it is not directly preceded by whitespace" (M2), and it closes
   "only if there are some characters besides the delimiter character
   between the opener and the closer" (M3).

   Both rules are about bytes around the delimiters, which the semantic
   tree does not keep.  The located scan does: a delimiter node's span
   runs from its opener's first byte to its closer's last, braces
   included, as djot.js's does.  So the rules are stated on that span,
   read against the text the scanner was given (its windows), for every
   row of the table: `para_inlines_spans` for a paragraph's lines and
   `cell_inlines_spans` for a table cell.

   The statement is about the inline content the block layer hands over.
   `StoredLines.parse_blocks_located_spans` carries it to the document. *)

From Stdlib Require Import String Ascii List Bool Lia Arith Sorted.
From DjotV Require Import Config Strings Ast Attributes InlineTable InlineView
  InlineScan InlineLocated.
Import ListNotations.

Local Open Scope string_scope.

Section WithTable.
Context {T : dtable}.

(*
The text the scanner reads
==========================

A window is one line's scanned text with where it starts, as a spot's
`rem` counts: a paragraph line is its whole stored text, the last one
stripped of trailing whitespace; a table cell is a trimmed infix of its
row.  A spot inside a window names the text from there to the window's
end.
*)

Definition window : Type := (nat * nat * string)%type.

Fixpoint wfind (W : list window) (k : nat) : option (nat * string) :=
  match W with
  | [] => None
  | (j, r0, w) :: rest => if Nat.eqb j k then Some (r0, w) else wfind rest k
  end.

Fixpoint sdrop (n : nat) (s : string) : string :=
  match n, s with
  | O, _ => s
  | S n', String _ s' => sdrop n' s'
  | S _, EmptyString => EmptyString
  end.

(* The window's text from `p` on, when `p` is inside the window. *)
Definition sfx (W : list window) (p : spot) : option string :=
  match wfind W (spot_line p) with
  | Some (r0, w) =>
      if (Nat.leb (String.length w) r0 && Nat.leb (spot_rem p) r0
          && Nat.leb (r0 - String.length w) (spot_rem p))%bool
      then Some (sdrop (r0 - spot_rem p) w) else None
  | None => None
  end.

Definition byte_at (W : list window) (p : spot) : option ascii :=
  match sfx W p with Some (String c _) => Some c | _ => None end.

(* [n] bytes to the right and to the left on the same line. *)
Definition sright (n : nat) (p : spot) : spot := Spot (spot_line p) (spot_rem p - n).
Definition sleft (n : nat) (p : spot) : spot := Spot (spot_line p) (spot_rem p + n).

(* Source order: later lines, and further along a line. *)
Definition spot_le (a b : spot) : Prop :=
  spot_line a < spot_line b \/
  (spot_line a = spot_line b /\ spot_rem b <= spot_rem a).

Definition spot_lt (a b : spot) : Prop :=
  spot_line a < spot_line b \/
  (spot_line a = spot_line b /\ spot_rem b < spot_rem a).

(*
The statement
=============

An opener is the row's token, with a `{` in front when it is marked; a
closer is the token, with a `}` after it when it is marked.  A bare
opener is followed by a byte of its window that is not whitespace, and a
bare closer preceded by one (M2).  Between the opener's end and the
closer's start lies at least one byte or line break (M3).
*)

Definition otok (k : dstyle) (m : bool) : string :=
  ((if m then one lbrace else EmptyString) ++ dtoken k)%string.

Definition ctok (k : dstyle) (m : bool) : string :=
  (dtoken k ++ (if m then one rbrace else EmptyString))%string.

Definition opener_at (W : list window) (k : dstyle) (m : bool) (a : spot) : Prop :=
  exists rest, sfx W a = Some (otok k m ++ rest)%string /\
    (m = false -> exists c, byte_at W (sright (String.length (otok k m)) a) = Some c /\
                            nonspace_at (Some c) = true).

Definition closer_at (W : list window) (k : dstyle) (m : bool) (b : spot) : Prop :=
  let s := sleft (String.length (ctok k m)) b in
  exists rest, sfx W s = Some (ctok k m ++ rest)%string /\
    (m = false -> exists c, byte_at W (sleft 1 s) = Some c /\
                            nonspace_at (Some c) = true).

Definition dspan_ok (W : list window) (k : dstyle) (r : span) : Prop :=
  exists m, opener_at W k m (span_start r) /\ closer_at W k m (span_stop r) /\
    spot_lt (sright (String.length (otok k m)) (span_start r))
            (sleft (String.length (ctok k m)) (span_stop r)).

(* The row a delimiter node was built for: `dnode` read backwards. *)
Definition dkind (x : inline) : option dstyle :=
  match x with
  | Emph _ => Some DEmph | Strong _ => Some DStrong
  | Superscript _ => Some DSuper | Subscript _ => Some DSub
  | Highlight _ => Some DMark | Insert _ => Some DInsert
  | Delete _ => Some DDelete
  | Quoted SingleQuotes _ => Some DSQuote
  | Quoted DoubleQuotes _ => Some DDQuote
  | _ => None
  end.

Definition dpos_ok (W : list window) (p : pos) (x : inline) : Prop :=
  match dkind x with
  | Some k => exists pr, p = SomePos pr /\ dspan_ok W k (node_span pr)
  | None => True
  end.

(* Every delimiter node in a tree, at any depth. *)
Fixpoint dn_inline (W : list window) (p : pos) (x : inline) : Prop :=
  let go :=
    fix go (ils : inlines) : Prop :=
      match ils with
      | [] => True
      | Node q _ y :: rest => dn_inline W q y /\ go rest
      end in
  dpos_ok W p x /\
  match x with
  | Emph ils | Strong ils | Highlight ils | Insert ils | Delete ils
  | Superscript ils | Subscript ils | Span ils | Quoted _ ils
  | Link ils _ | Image ils _ => go ils
  | _ => True
  end.

Definition dn_node (W : list window) (n : node inline) : Prop :=
  match n with Node p _ x => dn_inline W p x end.

Lemma dn_children : forall W ils,
  (fix go (ils : inlines) : Prop :=
     match ils with
     | [] => True
     | Node q _ y :: rest => dn_inline W q y /\ go rest
     end) ils <-> Forall (dn_node W) ils.
Proof.
  intros W ils. induction ils as [|[q a y] ils IH].
  - split; [constructor|tauto].
  - split.
    + intros [H1 H2]. constructor; [exact H1|apply IH, H2].
    + intros H. inversion H as [|? ? H1 H2]; subst. split; [exact H1|apply IH, H2].
Qed.

(*
Arithmetic of spots
===================
*)

Lemma spot_le_refl : forall p, spot_le p p.
Proof. intros p. right. lia. Qed.

Lemma spot_le_trans : forall a b c, spot_le a b -> spot_le b c -> spot_le a c.
Proof. unfold spot_le. intros a b c H1 H2. lia. Qed.

Lemma spot_lt_le : forall a b, spot_lt a b -> spot_le a b.
Proof. unfold spot_le, spot_lt. intros a b H. lia. Qed.

Lemma spot_lt_le_trans : forall a b c, spot_lt a b -> spot_le b c -> spot_lt a c.
Proof. unfold spot_le, spot_lt. intros a b c H1 H2. lia. Qed.

Lemma spot_le_lt_trans : forall a b c, spot_le a b -> spot_lt b c -> spot_lt a c.
Proof. unfold spot_le, spot_lt. intros a b c H1 H2. lia. Qed.

Lemma spot_lt_trans : forall a b c, spot_lt a b -> spot_lt b c -> spot_lt a c.
Proof. unfold spot_lt. intros a b c H1 H2. lia. Qed.

Lemma spot_lt_sright : forall n p, 0 < n -> n <= spot_rem p -> spot_lt p (sright n p).
Proof. intros n [k r] H1 H2. unfold spot_lt, sright. cbn in *. lia. Qed.

Lemma spot_le_sright : forall n p, spot_le p (sright n p).
Proof. intros n [k r]. unfold spot_le, sright. cbn. lia. Qed.

Lemma spot_lt_sleft : forall n p, 0 < n -> spot_lt (sleft n p) p.
Proof. intros n [k r] H. unfold spot_lt, sleft. cbn. lia. Qed.

Lemma spot_le_sleft : forall n p, spot_le (sleft n p) p.
Proof. intros n [k r]. unfold spot_le, sleft. cbn. lia. Qed.

Lemma sleft_sright : forall n p, n <= spot_rem p -> sleft n (sright n p) = p.
Proof. intros n [k r] H. unfold sleft, sright. cbn in *. f_equal. lia. Qed.

Lemma sright_sleft : forall n p, sright n (sleft n p) = p.
Proof. intros n [k r]. unfold sleft, sright. cbn. f_equal. lia. Qed.

(*
Reading the windows
-------------------
*)

(* `s` is the text immediately before `p`, on its line. *)
Definition ends_at (W : list window) (s : string) (p : spot) : Prop :=
  exists rest, sfx W (sleft (String.length s) p) = Some (s ++ rest)%string.

Lemma sdrop_length : forall n s, String.length (sdrop n s) = String.length s - n.
Proof.
  induction n as [|n IH]; intros [|c s]; cbn; try reflexivity. apply IH.
Qed.

Lemma sdrop_sdrop : forall a b s, sdrop a (sdrop b s) = sdrop (b + a) s.
Proof.
  intros a b. revert a. induction b as [|b IH]; intros a [|c s]; cbn.
  - reflexivity.
  - reflexivity.
  - destruct a; reflexivity.
  - apply IH.
Qed.

Lemma sdrop_app : forall a b, sdrop (String.length a) (a ++ b) = b.
Proof. induction a as [|c a IH]; intros b; [reflexivity|apply IH]. Qed.

Lemma sfx_some : forall W p s,
  sfx W p = Some s ->
  exists r0 w, wfind W (spot_line p) = Some (r0, w) /\
    String.length w <= r0 /\ spot_rem p <= r0 /\ r0 - String.length w <= spot_rem p /\
    s = sdrop (r0 - spot_rem p) w.
Proof.
  intros W p s H. unfold sfx in H.
  destruct (wfind W (spot_line p)) as [[r0 w]|]; [|discriminate].
  destruct (Nat.leb (String.length w) r0) eqn:E0; [|discriminate].
  destruct (Nat.leb (spot_rem p) r0) eqn:E1; [|discriminate].
  destruct (Nat.leb (r0 - String.length w) (spot_rem p)) eqn:E2; [|discriminate].
  apply Nat.leb_le in E0, E1, E2. injection H as <-. eauto 7.
Qed.

(* How much of its window lies after a spot. *)
Lemma sfx_rem : forall W p s, sfx W p = Some s -> String.length s <= spot_rem p.
Proof.
  intros W p s H. destruct (sfx_some _ _ _ H) as (r0 & w & _ & H0 & H1 & H2 & ->).
  rewrite sdrop_length. lia.
Qed.

Lemma sfx_sright : forall W p s n,
  sfx W p = Some s -> n <= String.length s -> sfx W (sright n p) = Some (sdrop n s).
Proof.
  intros W p s n H Hn. destruct (sfx_some _ _ _ H) as (r0 & w & Hw & H0 & H1 & H2 & ->).
  rewrite sdrop_length in Hn. unfold sfx, sright. cbn [spot_line spot_rem].
  rewrite Hw.
  replace (Nat.leb (String.length w) r0) with true by (symmetry; apply Nat.leb_le; lia).
  replace (Nat.leb (spot_rem p - n) r0) with true by (symmetry; apply Nat.leb_le; lia).
  replace (Nat.leb (r0 - String.length w) (spot_rem p - n)) with true
    by (symmetry; apply Nat.leb_le; lia).
  rewrite sdrop_sdrop. cbn [andb]. do 2 f_equal. lia.
Qed.

Lemma sfx_app : forall W p a b,
  sfx W p = Some (a ++ b)%string -> sfx W (sright (String.length a) p) = Some b.
Proof.
  intros W p a b H. rewrite (sfx_sright _ _ _ _ H), sdrop_app; [reflexivity|].
  rewrite length_append. lia.
Qed.

Lemma sfx_cons : forall W p c s,
  sfx W p = Some (String c s) -> sfx W (sright 1 p) = Some s.
Proof. intros W p c s H. exact (sfx_app W p (one c) s H). Qed.

Lemma byte_at_sfx : forall W p c s, sfx W p = Some (String c s) -> byte_at W p = Some c.
Proof. intros W p c s H. unfold byte_at. rewrite H. reflexivity. Qed.

Lemma ends_at_sfx : forall W s p rest,
  ends_at W s p -> sfx W p = Some rest -> sfx W (sleft (String.length s) p) = Some (s ++ rest)%string.
Proof.
  intros W s p rest [r Hr] Hp.
  pose proof (sfx_app _ _ _ _ Hr) as H.
  pose proof (sfx_rem _ _ _ Hr) as Hlen. rewrite length_append in Hlen.
  rewrite sright_sleft in H. rewrite Hp in H. injection H as ->. exact Hr.
Qed.

(* Reading one more byte extends what lies before the cursor. *)
Lemma ends_at_snoc : forall W s p c rest,
  ends_at W s p -> sfx W p = Some (String c rest) ->
  ends_at W (s ++ one c) (sright 1 p).
Proof.
  intros W s p c rest He Hp. exists rest.
  pose proof (ends_at_sfx _ _ _ _ He Hp) as H.
  pose proof (sfx_rem _ _ _ Hp) as Hl. cbn [String.length] in Hl.
  rewrite length_append. cbn [String.length one].
  replace (sleft (String.length s + 1) (sright 1 p)) with (sleft (String.length s) p).
  - rewrite append_assoc. exact H.
  - unfold sleft, sright. destruct p as [k r]. cbn in *. f_equal. lia.
Qed.

Lemma ends_at_one : forall W p c rest,
  sfx W p = Some (String c rest) -> ends_at W (one c) (sright 1 p).
Proof.
  intros W p c rest H. exists rest. cbn [String.length one].
  rewrite sleft_sright; [exact H|].
  pose proof (sfx_rem _ _ _ H). cbn in H0. lia.
Qed.

(* The last byte of what lies before the cursor is the byte to its left. *)
Lemma ends_at_last : forall W s c p,
  ends_at W (s ++ one c) p -> byte_at W (sleft 1 p) = Some c.
Proof.
  intros W s c p [rest H].
  rewrite append_assoc in H. pose proof (sfx_app _ _ _ _ H) as H1.
  rewrite length_append in H1. cbn [String.length one] in H1.
  unfold byte_at.
  replace (sleft 1 p) with (sright (String.length s) (sleft (String.length s + 1) p)).
  - rewrite H1. reflexivity.
  - destruct p as [k r]. unfold sleft, sright. cbn. f_equal. lia.
Qed.

(*
The scanner's invariant
=======================

What a scan state owes the statement.  Every delimiter node it holds is
already where the statement wants it (`item_ok`), and every delimiter
frame records an opener the statement would accept (`frame_ok`).

M3 needs one more fact, about order.  `h` is where the bytes the state
has not yet put into text or items begin: the cursor, or the first byte
of a construct still waiting for its role.  An open frame's opener ends
at or before `h`, strictly before once the frame holds anything, and a
frame below another ends before that one starts (`stack_ok`).  `t` says
whether text is pending, which counts as holding something.
*)

Definition item_ok (W : list window) (i : oitem) : Prop :=
  match i with OIn n => dn_node W n | OMark _ _ _ => True end.

Definition frame_ok (W : list window) (f : frame) : Prop :=
  match fr_kind f with
  | FKDelim k _ =>
      opener_at W k (fr_marked f) (span_start (fr_open f)) /\
      span_stop (fr_open f) =
        sright (String.length (otok k (fr_marked f))) (span_start (fr_open f))
  | FKBracket _ | FKDest _ => True
  end /\
  spot_lt (span_start (fr_open f)) (span_stop (fr_open f)) /\
  Forall (item_ok W) (fr_out f).

Fixpoint stack_ok (stk : list frame) (t : bool) (h : spot) : Prop :=
  match stk with
  | [] => True
  | f :: rest =>
      spot_le (span_stop (fr_open f)) h /\
      ((fr_out f <> [] \/ t = true) -> spot_lt (span_stop (fr_open f)) h) /\
      stack_ok rest false (span_start (fr_open f))
  end.

Definition oinv (W : list window) (o : ostate) (t : bool) (h : spot) : Prop :=
  Forall (item_ok W) (os_out o) /\ Forall (frame_ok W) (os_stk o) /\
  stack_ok (os_stk o) t h.

(* The state was settled at some point before `cur`. *)
Definition held (W : list window) (o : ostate) (t : bool) (cur : spot) : Prop :=
  exists h, spot_lt h cur /\ oinv W o t h.

(* The byte the scanner believes is to the left of `p`: the window's, or
   none (or the newline a fallback ends on) at the window's start. *)
Definition prev_ok (W : list window) (prev : option ascii) (p : spot) : Prop :=
  match byte_at W (sleft 1 p) with
  | Some b => prev = Some b
  | None => prev = None \/ prev = Some nl_char
  end.


Definition delim_run (k : dstyle) (extra : nat) (marked : bool) : string :=
  ((if marked then one lbrace else EmptyString) ++ chars (dchar k) (S extra))%string.

Fixpoint st_inv (W : list window) (cur : spot) (st : iscan) : Prop :=
  match st with
  | IText esc txt prev o =>
      oinv W o (esc || nonempty_str txt) cur /\ prev_ok W prev cur /\
      (esc = true -> byte_at W (sleft 1 cur) = Some bslash)
  | IEscWs ws txt _ o =>
      held W o (nonempty_str txt) cur /\ ends_at W ws cur /\ ws <> EmptyString
  | IBrace txt _ o =>
      oinv W o (nonempty_str txt) (sleft 1 cur) /\
      byte_at W (sleft 1 cur) = Some lbrace
  | IDelim k extra txt before marked o =>
      S extra <= dwidth k /\ ends_at W (delim_run k extra marked) cur /\
      oinv W o (nonempty_str txt)
        (sleft (String.length (delim_run k extra marked)) cur) /\
      (marked = false ->
         prev_ok W before (sleft (String.length (delim_run k extra marked)) cur))
  | IOpen n _ o => held W o false cur /\ 1 <= n
  | IVerb n run _ _ o =>
      held W o false cur /\ 1 <= n /\
      (0 < run -> byte_at W (sleft 1 cur) = Some tick)
  | IDollar _ txt _ o =>
      held W o (nonempty_str txt) cur /\ byte_at W (sleft 1 cur) = Some dollar
  | IDollarMath _ _ _ txt _ sh o =>
      held W o (nonempty_str txt) cur /\ st_inv W cur sh
  | IDollarMathClose _ _ txt _ sh o =>
      held W o (nonempty_str txt) cur /\ byte_at W (sleft 1 cur) = Some dollar /\
      st_inv W cur sh
  | IPeriod _ txt _ o =>
      held W o (nonempty_str txt) cur /\ byte_at W (sleft 1 cur) = Some period
  | IDash n txt _ o =>
      ends_at W (chars hyphen n) cur /\ 1 <= n /\
      oinv W o (nonempty_str txt) (sleft n cur)
  | IBang txt _ o =>
      oinv W o (nonempty_str txt) (sleft 1 cur) /\
      byte_at W (sleft 1 cur) = Some bang
  | IClosed txt o =>
      oinv W o (nonempty_str txt) (sleft 1 cur) /\
      byte_at W (sleft 1 cur) = Some rbrack
  | ISpan kids _ _ p src o =>
      Forall (dn_node W) kids /\ held W o false cur /\
      prev_ok W (InlineScan.blit_prev (String lbrace src)) cur /\
      ap_done p = false
  | IAttr p _ txt _ sh o =>
      held W o (nonempty_str txt) cur /\ ap_done p = false /\ st_inv W cur sh
  | IReference kids _ _ _ o => Forall (dn_node W) kids /\ held W o false cur
  | INote _ _ _ _ o => held W o false cur
  | IWiki _ _ _ _ _ o => held W o false cur
  | IDest kids _ _ _ _ _ sh o =>
      Forall (dn_node W) kids /\ held W o false cur /\ st_inv W cur sh
  | IAuto src txt o =>
      held W o (nonempty_str txt) cur /\ ends_at W (String lt src) cur
  | ISymbol _ txt sh o => held W o (nonempty_str txt) cur /\ st_inv W cur sh
  | IRaw spec _ o =>
      ends_at W (String lbrace spec) cur /\
      held W o false (sleft (String.length (String lbrace spec)) cur)
  end.

(*
Nodes
=====

Every lemma from here on is about the located scan.
*)

#[local] Existing Instance located_pos | 0.

Definition children (x : inline) : inlines :=
  match x with
  | Emph ils | Strong ils | Highlight ils | Insert ils | Delete ils
  | Superscript ils | Subscript ils | Span ils | Quoted _ ils
  | Link ils _ | Image ils _ => ils
  | _ => []
  end.

Lemma dn_inline_eq : forall W p x,
  dn_inline W p x <-> dpos_ok W p x /\ Forall (dn_node W) (children x).
Proof.
  intros W p x. destruct x; cbn [dn_inline children];
    rewrite ?dn_children; (split; [intros [H1 H2]; split; auto|intros [H1 H2]; split; auto]).
Qed.

Lemma dn_node_eq : forall W p a x,
  dn_node W (Node p a x) <-> dpos_ok W p x /\ Forall (dn_node W) (children x).
Proof. intros W p a x. apply dn_inline_eq. Qed.

(* A node that is not a delimiter's is fine when its children are. *)
Lemma dn_node_plain : forall W p a x,
  dkind x = None -> Forall (dn_node W) (children x) -> dn_node W (Node p a x).
Proof.
  intros W p a x Hk Hc. apply dn_node_eq. split; [|exact Hc].
  unfold dpos_ok. rewrite Hk. exact I.
Qed.

Lemma dn_node_str : forall W p a s, dn_node W (Node p a (Str s)).
Proof. intros. apply dn_node_plain; [reflexivity|constructor]. Qed.

Lemma dn_add_roles : forall W rs n,
  dn_node W n -> dn_node W (add_roles rs n).
Proof.
  intros W rs [[|pr] a x] H; cbn [add_roles pos_records located_pos]; [exact H|].
  apply dn_node_eq in H as [Hp Hc]. apply dn_node_eq. split; [|exact Hc].
  unfold dpos_ok in *. destruct (dkind x); [|exact I].
  destruct Hp as (pr' & Heq & Hs). injection Heq as <-.
  eexists. split; [reflexivity|exact Hs].
Qed.

Lemma dn_add_inline_role : forall W role r n,
  dn_node W n -> dn_node W (add_inline_role role r n).
Proof. intros W role r n H. apply dn_add_roles, H. Qed.

Lemma dn_imk_plain : forall W start stop x,
  dkind x = None -> Forall (dn_node W) (children x) ->
  dn_node W (imk start stop x).
Proof. intros W start stop x Hk Hc. apply dn_node_plain; assumption. Qed.

Lemma dkind_dnode : forall k ns, dkind (dnode k ns) = Some k.
Proof. intros [] ns; reflexivity. Qed.

Lemma children_dnode : forall k ns, children (dnode k ns) = ns.
Proof. intros [] ns; reflexivity. Qed.

Lemma dn_imk_dnode : forall W k start stop ns,
  dspan_ok W k (SrcSpan start stop) -> Forall (dn_node W) ns ->
  dn_node W (imk start stop (dnode k ns)).
Proof.
  intros W k start stop ns Hs Hc. unfold imk. cbn [pos_records located_pos].
  unfold posnode. cbn [mkpos]. apply dn_node_eq. split.
  - unfold dpos_ok. rewrite dkind_dnode. eexists. split; [reflexivity|exact Hs].
  - rewrite children_dnode. exact Hc.
Qed.

(*
Items
-----
*)

Lemma osnoc_ok : forall W n out,
  item_ok W n -> Forall (item_ok W) out -> Forall (item_ok W) (osnoc n out).
Proof.
  intros W n out Hn Hout. unfold osnoc.
  destruct out as [|[[p [|kv a] x]|a sp w] rest]; try (constructor; assumption).
  destruct x; try (constructor; assumption).
  destruct n as [[q [|kv' b] y]|b sp w]; try (constructor; assumption).
  destruct y; try (constructor; assumption).
  inversion Hout; subst. constructor; [apply dn_node_str|assumption].
Qed.

Lemma oapp_ok : forall W cur out,
  Forall (item_ok W) cur -> Forall (item_ok W) out -> Forall (item_ok W) (oapp cur out).
Proof.
  intros W cur. induction cur as [|n cur IH]; intros out Hc Ho; [exact Ho|].
  inversion Hc as [|? ? Hn Hrest]; subst.
  destruct cur as [|n' cur']; cbn [oapp].
  - apply osnoc_ok; assumption.
  - constructor; [exact Hn|apply IH; assumption].
Qed.

Lemma isnoc_ok : forall W n out,
  dn_node W n -> Forall (dn_node W) out -> Forall (dn_node W) (isnoc n out).
Proof.
  intros W n out Hn Hout. unfold isnoc.
  destruct out as [|[p [|kv a] x] rest]; try (constructor; assumption).
  destruct x; try (constructor; assumption).
  destruct n as [q [|kv' b] y]; try (constructor; assumption).
  destruct y; try (constructor; assumption).
  inversion Hout; subst. constructor; [apply dn_node_str|assumption].
Qed.

Lemma oattach_list_ok : forall W a spec w out,
  Forall (dn_node W) out -> Forall (dn_node W) (oattach_list a spec w out).
Proof.
  intros W a spec w out Hout. unfold oattach_list.
  destruct out as [|[p a' x] rest]; [constructor|].
  inversion Hout as [|? ? Hn Hrest]; subst.
  destruct x;
    try (destruct a'; constructor; first [apply dn_add_inline_role; exact Hn|exact Hrest]).
  - destruct a' as [|kv a'];
      [|constructor; [apply dn_add_inline_role; exact Hn|exact Hrest]].
    destruct (last_ws_split s) as [pre w0].
    destruct (nonempty_str w0); [|exact Hout].
    destruct a as [|kv a]; [exact Hout|].
    destruct (split_text_pos p w) as [pp wp].
    apply isnoc_ok; [apply dn_add_inline_role, dn_node_str|].
    destruct (nonempty_str pre); [apply isnoc_ok; [apply dn_node_str|]|]; exact Hrest.
  - destruct a'; exact Hout.
Qed.

Lemma oresolve_go_ok : forall W l,
  Forall (item_ok W) l -> Forall (dn_node W) (fst (oresolve_go l)).
Proof.
  intros W l. induction l as [|[n|a spec w] l IH]; intros Hl; [constructor| |];
    inversion Hl as [|? ? Hi Hrest]; subst; cbn [oresolve_go];
    specialize (IH Hrest); destruct (oresolve_go l) as [out m]; cbn [fst] in *.
  - destruct m; [apply isnoc_ok|constructor]; assumption.
  - apply oattach_list_ok, IH.
Qed.

Lemma oresolve_ok : forall W l,
  Forall (item_ok W) l -> Forall (dn_node W) (oresolve l).
Proof. intros W l H. apply oresolve_go_ok, H. Qed.

(*
Scan states
===========

Moving `h` forward keeps a state settled, and moving it strictly forward
makes every open frame count as holding something.
*)

Lemma stack_ok_mono : forall stk t h h',
  spot_le h h' -> stack_ok stk t h -> stack_ok stk t h'.
Proof.
  intros [|f rest] t h h' Hle H; [exact I|].
  destruct H as (H1 & H2 & H3). split; [|split; [|exact H3]].
  - eapply spot_le_trans; eassumption.
  - intros Ht. eapply spot_lt_le_trans; [apply H2, Ht|exact Hle].
Qed.

Lemma stack_ok_strict : forall stk t h h',
  spot_lt h h' -> stack_ok stk t h -> stack_ok stk true h'.
Proof.
  intros [|f rest] t h h' Hlt H; [exact I|].
  destruct H as (H1 & H2 & H3). split; [|split; [|exact H3]].
  - apply spot_lt_le. eapply spot_le_lt_trans; eassumption.
  - intros _. eapply spot_le_lt_trans; eassumption.
Qed.

Lemma stack_ok_untouch : forall stk t h, stack_ok stk true h -> stack_ok stk t h.
Proof.
  intros [|f rest] t h H; [exact I|].
  destruct H as (H1 & H2 & H3). split; [exact H1|split; [|exact H3]].
  intros _. apply H2. right. reflexivity.
Qed.

Lemma oinv_mono : forall W o t h h',
  spot_le h h' -> oinv W o t h -> oinv W o t h'.
Proof.
  intros W o t h h' Hle (H1 & H2 & H3). split; [exact H1|split; [exact H2|]].
  eapply stack_ok_mono; eassumption.
Qed.

Lemma oinv_strict : forall W o t h h',
  spot_lt h h' -> oinv W o t h -> oinv W o true h'.
Proof.
  intros W o t h h' Hlt (H1 & H2 & H3). split; [exact H1|split; [exact H2|]].
  eapply stack_ok_strict; eassumption.
Qed.

Lemma oinv_untouch : forall W o t h, oinv W o true h -> oinv W o t h.
Proof.
  intros W o t h (H1 & H2 & H3). split; [exact H1|split; [exact H2|]].
  apply stack_ok_untouch, H3.
Qed.

Lemma held_intro : forall W o t h cur,
  spot_lt h cur -> oinv W o t h -> held W o t cur.
Proof. intros. eexists. split; eassumption. Qed.

Lemma held_oinv : forall W o t cur, held W o t cur -> oinv W o true cur.
Proof. intros W o t cur (h & Hlt & H). eapply oinv_strict; eassumption. Qed.

Lemma held_mono : forall W o t cur cur',
  spot_le cur cur' -> held W o t cur -> held W o t cur'.
Proof.
  intros W o t cur cur' Hle (h & Hlt & H). exists h.
  split; [eapply spot_lt_le_trans; eassumption|exact H].
Qed.

(*
Emission
--------
*)

Lemma oemit_ok : forall W n o h,
  dn_node W n -> oinv W o true h -> oinv W (oemit n o) true h.
Proof.
  intros W n [out stk word] h Hn (H1 & H2 & H3). unfold oemit. cbn [os_stk os_out os_word_start] in *.
  destruct stk as [|f rest].
  - split; [constructor; assumption|split; constructor].
  - inversion H2 as [|? ? Hf Hrest]; subst.
    destruct H3 as (A & B & C).
    split; [exact H1|split].
    + constructor; [|exact Hrest].
      destruct Hf as (F1 & F2 & F3). split; [exact F1|split; [exact F2|]].
      cbn [fr_out]. constructor; assumption.
    + cbn [fr_open fr_out stack_ok]. split; [exact A|split; [|exact C]].
      intros _. apply B. right. reflexivity.
Qed.

Lemma omark_ok : forall W a spec o h,
  oinv W o true h -> oinv W (omark a spec o) true h.
Proof.
  intros W a spec [out stk word] h (H1 & H2 & H3). unfold omark. cbn [os_stk os_out os_word_start] in *.
  destruct stk as [|f rest].
  - split; [constructor; [exact I|assumption]|split; constructor].
  - inversion H2 as [|? ? Hf Hrest]; subst.
    destruct H3 as (A & B & C).
    split; [exact H1|split].
    + constructor; [|exact Hrest].
      destruct Hf as (F1 & F2 & F3). split; [exact F1|split; [exact F2|]].
      cbn [fr_out]. constructor; [exact I|assumption].
    + cbn [fr_open fr_out stack_ok]. split; [exact A|split; [|exact C]].
      intros _. apply B. right. reflexivity.
Qed.

Lemma remember_word_start_ok : forall W (CU : InlineCursor) c o t h,
  oinv W o t h -> oinv W (remember_word_start c o) t h.
Proof.
  intros W CU c [out stk word] t h H. unfold remember_word_start.
  destruct (pos_records && is_ws c)%bool; exact H.
Qed.

Lemma oword_reset_ok : forall W o t h, oinv W o t h -> oinv W (oword_reset o) t h.
Proof. intros W [out stk word] t h H. exact H. Qed.

(* Flushing pending text: whatever was pending is now held. *)
Lemma flush_text_to_at_ok : forall W (CU : InlineCursor) stop txt o h,
  oinv W o (nonempty_str txt) h -> oinv W (flush_text_to_at stop txt o) false h.
Proof.
  intros W CU stop txt o h H. unfold flush_text_to_at.
  destruct (nonempty_str txt) eqn:E.
  - apply oinv_untouch, oemit_ok; [apply dn_node_str|exact H].
  - exact H.
Qed.

Lemma flush_text_at_ok : forall W (CU : InlineCursor) txt o h,
  oinv W o (nonempty_str txt) h -> oinv W (flush_text_at txt o) false h.
Proof.
  intros W CU txt o h H. unfold flush_text_at.
  destruct (nonempty_str txt) eqn:E.
  - apply oinv_untouch, oemit_ok; [apply dn_node_str|exact H].
  - exact H.
Qed.

Lemma flush_text_to_at_touched : forall W (CU : InlineCursor) stop txt o h,
  oinv W o true h -> oinv W (flush_text_to_at stop txt o) true h.
Proof.
  intros W CU stop txt o h H. unfold flush_text_to_at.
  destruct (nonempty_str txt); [apply oemit_ok; [apply dn_node_str|]|]; exact H.
Qed.

Lemma flush_text_at_touched : forall W (CU : InlineCursor) txt o h,
  oinv W o true h -> oinv W (flush_text_at txt o) true h.
Proof.
  intros W CU txt o h H. unfold flush_text_at.
  destruct (nonempty_str txt); [apply oemit_ok; [apply dn_node_str|]|]; exact H.
Qed.

(*
Tokens
------
*)

Lemma spot_before_no_nl : forall p s,
  no_char nl_char s = true -> spot_before p s = sleft (String.length s) p.
Proof.
  intros p s H. unfold spot_before.
  assert (Hs : forall s, no_char nl_char s = true ->
            InlineScan.source_shape s = (0, String.length s, String.length s)).
  { induction s0 as [|c s0 IH]; intros Hn; [reflexivity|].
    cbn [no_char] in Hn. apply andb_true_iff in Hn as [Hc Hn].
    cbn [InlineScan.source_shape String.length]. rewrite (IH Hn).
    apply negb_true_iff in Hc. rewrite Hc. reflexivity. }
  rewrite (Hs s H). reflexivity.
Qed.

Lemma dchar_not_nl : forall k, Ascii.eqb (dchar k) nl_char = false.
Proof.
  intros k. destruct (Ascii.eqb (dchar k) nl_char) eqn:E; [|reflexivity].
  apply Ascii.eqb_eq in E. pose proof (dchar_punct k) as H. rewrite E in H. discriminate.
Qed.

Lemma chars_no_nl : forall c n, Ascii.eqb c nl_char = false -> no_char nl_char (chars c n) = true.
Proof. intros c n H. induction n as [|n IH]; [reflexivity|]. cbn. rewrite H, IH. reflexivity. Qed.

Lemma dtoken_no_nl : forall k, no_char nl_char (dtoken k) = true.
Proof. intros k. apply chars_no_nl, dchar_not_nl. Qed.

Lemma no_char_app : forall c a b,
  no_char c (a ++ b) = (no_char c a && no_char c b)%bool.
Proof.
  intros c a b. induction a as [|x a IH]; [reflexivity|]. cbn. rewrite IH, andb_assoc. reflexivity.
Qed.

Lemma otok_no_nl : forall k m, no_char nl_char (otok k m) = true.
Proof. intros k [|]; unfold otok; rewrite no_char_app, dtoken_no_nl; reflexivity. Qed.

Lemma dtoken_length : forall k, String.length (dtoken k) = dwidth k.
Proof.
  intros k. unfold dtoken. generalize (dwidth k). induction n as [|n IH]; [reflexivity|].
  cbn. rewrite IH. reflexivity.
Qed.

Lemma otok_length : forall k m,
  String.length (otok k m) = (if m then 1 else 0) + dwidth k.
Proof. intros k [|]; unfold otok; rewrite length_append, dtoken_length; reflexivity. Qed.

Lemma ctok_length : forall k m,
  String.length (ctok k m) = dwidth k + (if m then 1 else 0).
Proof. intros k [|]; unfold ctok; rewrite length_append, dtoken_length; reflexivity. Qed.

Lemma delim_run_full : forall k extra m,
  S extra = dwidth k -> delim_run k extra m = otok k m.
Proof. intros k extra m H. unfold delim_run, otok, dtoken. rewrite H. reflexivity. Qed.

(*
Pushing a scope
---------------
*)

Lemma opush_at_ok : forall W k m cm open o,
  oinv W o false (span_start open) ->
  opener_at W k m (span_start open) ->
  span_stop open = sright (String.length (otok k m)) (span_start open) ->
  spot_lt (span_start open) (span_stop open) ->
  oinv W (opush_at k m cm open o) false (span_stop open).
Proof.
  intros W k m cm open [out stk word] (H1 & H2 & H3) Ho Hs Hlt.
  unfold opush_at. cbn [os_stk os_out] in *.
  split; [exact H1|split].
  - constructor; [|exact H2].
    split; [split; assumption|split; [exact Hlt|constructor]].
  - cbn [stack_ok fr_open fr_out]. split; [apply spot_le_refl|split; [|exact H3]].
    intros [H|H]; [contradiction|discriminate].
Qed.

(* The bracket and destination scopes are not delimiters: only their
   place in the order is owed. *)
Lemma frame_push_ok : forall W kind m open o,
  (match kind with FKDelim _ _ => False | _ => True end) ->
  oinv W o false (span_start open) ->
  spot_lt (span_start open) (span_stop open) ->
  oinv W (OState (os_out o) (Frame kind m open [] :: os_stk o) (os_word_start o))
    false (span_stop open).
Proof.
  intros W kind m open [out stk word] Hk (H1 & H2 & H3) Hlt.
  cbn [os_stk os_out os_word_start] in *.
  split; [exact H1|split].
  - constructor; [|exact H2].
    split; [destruct kind; [contradiction|exact I|exact I]|split; [exact Hlt|constructor]].
  - cbn [stack_ok fr_open fr_out]. split; [apply spot_le_refl|split; [|exact H3]].
    intros [H|H]; [contradiction|discriminate].
Qed.

(*
Closing a scope
---------------

The walk out through the open scopes.  `hp` is where the scope being
looked at must have closed its opener by: the cursor for the innermost,
then each scope's opener for the one below it.  What the walk carries
down (`pend`) is nonempty past the first scope, so every scope below the
first holds something.
*)

Lemma dmatch_true : forall k m f,
  dmatch k m f = true -> exists cm, fr_kind f = FKDelim k cm /\ fr_marked f = m.
Proof.
  intros k m [kind fm fo fout] H. unfold dmatch in H. cbn [fr_kind fr_marked] in *.
  destruct kind as [k' cm| |]; try discriminate.
  apply andb_true_iff in H as [Hk Hm].
  exists cm. split.
  - destruct k, k'; try discriminate; reflexivity.
  - apply Bool.eqb_prop in Hm. symmetry. exact Hm.
Qed.

Lemma fr_lit_ok : forall W f, item_ok W (OIn (fr_lit f)).
Proof. intros W f. apply dn_imk_plain; [reflexivity|constructor]. Qed.

Lemma oclose_go_ok : forall W k m stk pend hp cs content open rest,
  Forall (item_ok W) pend -> Forall (frame_ok W) stk ->
  (match stk with
   | [] => True
   | f :: rest =>
       spot_le (span_stop (fr_open f)) hp /\
       ((fr_out f <> [] \/ pend <> []) -> spot_lt (span_stop (fr_open f)) hp) /\
       stack_ok rest false (span_start (fr_open f))
   end) ->
  spot_le hp cs ->
  oclose_go k m pend stk = Some (content, open, rest) ->
  Forall (item_ok W) content /\ Forall (frame_ok W) rest /\
  stack_ok rest false (span_start open) /\
  opener_at W k m (span_start open) /\
  spot_lt (sright (String.length (otok k m)) (span_start open)) cs /\
  spot_lt (span_start open) cs.
Proof.
  intros W k m stk. induction stk as [|f stk IH];
    intros pend hp cs content open rest Hp Hf Hs Hcs Hgo; [discriminate|].
  inversion Hf as [|? ? Hfo Hfs]; subst.
  destruct Hs as (S1 & S2 & S3).
  cbn [oclose_go] in Hgo.
  pose proof (oapp_ok W pend (fr_out f) Hp (proj2 (proj2 Hfo))) as Hc.
  destruct (dmatch k m f) eqn:Ed.
  - destruct (nonempty (oapp pend (fr_out f))) eqn:Hne; [|discriminate].
    injection Hgo as <- <- <-.
    destruct (dmatch_true _ _ _ Ed) as (cm & Hk & Hm).
    destruct Hfo as (F1 & F2 & F3). rewrite Hk, Hm in F1. destruct F1 as [Fo Fs].
    assert (Hlt : spot_lt (span_stop (fr_open f)) hp).
    { apply S2. destruct pend as [|x pend']; [left|right; discriminate].
      destruct (fr_out f); [discriminate|discriminate]. }
    split; [exact Hc|split; [exact Hfs|split; [exact S3|split; [exact Fo|]]]].
    rewrite <- Fs. split; [eapply spot_lt_le_trans; eassumption|].
    eapply spot_lt_trans; [exact F2|]. eapply spot_lt_le_trans; eassumption.
  - destruct (fr_barrier f); [discriminate|].
    eapply (IH (oapp (oapp pend (fr_out f)) [OIn (fr_lit f)]) (span_stop (fr_open f)));
      try eassumption.
    + apply oapp_ok; [exact Hc|constructor; [apply fr_lit_ok|constructor]].
    + destruct stk as [|g stk']; [exact I|].
      destruct S3 as (T1 & T2 & T3). split; [|split; [|exact T3]].
      * eapply spot_le_trans; [exact T1|apply spot_lt_le, (proj1 (proj2 Hfo))].
      * intros _. eapply spot_le_lt_trans; [exact T1|exact (proj1 (proj2 Hfo))].
    + eapply spot_le_trans; eassumption.
Qed.

Lemma oclose_ok : forall W k m stop o h o',
  oinv W o false h ->
  closer_at W k m stop ->
  spot_le h (sleft (String.length (ctok k m)) stop) ->
  oclose k m stop o = Some o' ->
  oinv W o' true stop.
Proof.
  intros W k m stop [out stk word] h o' (H1 & H2 & H3) Hcl Hh Hc.
  unfold oclose in Hc. cbn [os_stk os_out os_word_start] in *.
  destruct (oclose_go k m [] stk) as [[[content open] rest]|] eqn:Hgo; [|discriminate].
  injection Hc as <-.
  assert (Hst : match stk with
               | [] => True
               | f :: rest =>
                   spot_le (span_stop (fr_open f)) h /\
                   ((fr_out f <> [] \/ ([] : oitems) <> []) ->
                    spot_lt (span_stop (fr_open f)) h) /\
                   stack_ok rest false (span_start (fr_open f))
               end).
  { destruct stk as [|f rest']; [exact I|]. destruct H3 as (A & B & C).
    split; [exact A|split; [|exact C]]. intros [X|X]; [apply B; left; exact X|contradiction]. }
  destruct (oclose_go_ok W k m stk [] h _ content open rest (Forall_nil _) H2 Hst Hh Hgo)
    as (C1 & C2 & C3 & C4 & C5 & C6).
  pose proof (spot_le_sleft (String.length (ctok k m)) stop) as Hcs.
  apply oemit_ok.
  - apply dn_imk_dnode.
    + exists m. cbn [span_start span_stop]. split; [exact C4|split; [exact Hcl|exact C5]].
    + apply Forall_rev, oresolve_ok, C1.
  - split; [exact H1|split; [exact C2|]].
    eapply stack_ok_strict; [|exact C3].
    eapply spot_lt_le_trans; [exact C6|exact Hcs].
Qed.

(*
Brackets
--------
*)

Lemma bclose_go_ok : forall W stk pend hp content image open rest,
  Forall (item_ok W) pend -> Forall (frame_ok W) stk ->
  (match stk with
   | [] => True
   | f :: rest =>
       spot_le (span_stop (fr_open f)) hp /\ stack_ok rest false (span_start (fr_open f))
   end) ->
  bclose_go pend stk = Some (content, image, open, rest) ->
  Forall (item_ok W) content /\ Forall (frame_ok W) rest /\
  stack_ok rest false (span_start open) /\
  spot_lt (span_start open) (span_stop open) /\ spot_le (span_stop open) hp.
Proof.
  intros W stk. induction stk as [|f stk IH];
    intros pend hp content image open rest Hp Hf Hs Hgo; [discriminate|].
  inversion Hf as [|? ? Hfo Hfs]; subst. destruct Hs as (S1 & S3).
  cbn [bclose_go] in Hgo.
  pose proof (oapp_ok W pend (fr_out f) Hp (proj2 (proj2 Hfo))) as Hc.
  destruct (fr_kind f) as [k cm|im|im] eqn:Hk; try discriminate.
  - destruct (IH (oapp (oapp pend (fr_out f)) [OIn (fr_lit f)]) (span_start (fr_open f))
                content image open rest) as (A & B & C & D & E).
    + apply oapp_ok; [exact Hc|constructor; [apply fr_lit_ok|constructor]].
    + exact Hfs.
    + destruct stk as [|g stk']; [exact I|]. destruct S3 as (T1 & T2 & T3).
      split; assumption.
    + exact Hgo.
    + split; [exact A|split; [exact B|split; [exact C|split; [exact D|]]]].
      eapply spot_le_trans; [exact E|].
      eapply spot_le_trans; [apply spot_lt_le, (proj1 (proj2 Hfo))|exact S1].
  - injection Hgo as <- <- <- <-.
    split; [exact Hc|split; [exact Hfs|split; [exact S3|split; [exact (proj1 (proj2 Hfo))|exact S1]]]].
Qed.

Lemma bclose_ok : forall W o h kids image open o',
  oinv W o false h ->
  bclose o = Some (kids, image, open, o') ->
  Forall (dn_node W) kids /\ oinv W o' false (span_start open) /\
  spot_lt (span_start open) (span_stop open) /\ spot_le (span_stop open) h.
Proof.
  intros W [out stk word] h kids image open o' (H1 & H2 & H3) Hb.
  unfold bclose in Hb. cbn [os_stk os_out os_word_start] in *.
  destruct (bclose_go [] stk) as [[[[content im] op] rest]|] eqn:Hgo; [|discriminate].
  injection Hb as <- <- <- <-.
  destruct (bclose_go_ok W stk [] h content im op rest (Forall_nil _) H2) as (A & B & C & D & E).
  - destruct stk as [|f rest']; [exact I|]. destruct H3 as (X & _ & Z). split; assumption.
  - exact Hgo.
  - split; [apply Forall_rev, oresolve_ok, A|].
    split; [split; [exact H1|split; [exact B|exact C]]|split; [exact D|exact E]].
Qed.

Lemma bunpush_ok : forall W o h image open o',
  oinv W o false h ->
  bunpush o = Some (image, open, o') ->
  oinv W o' false (span_start open) /\
  spot_lt (span_start open) (span_stop open) /\ spot_le (span_stop open) h.
Proof.
  intros W [out stk word] h image open o' (H1 & H2 & H3) Hb.
  unfold bunpush in Hb. cbn [os_stk os_out os_word_start] in *.
  destruct stk as [|[kind fm fo fout] rest]; [discriminate|].
  destruct kind as [|im|]; try discriminate. destruct fout; [|discriminate].
  injection Hb as <- <- <-.
  inversion H2 as [|? ? Hf Hrest]; subst. destruct H3 as (A & _ & C).
  split; [split; [exact H1|split; [exact Hrest|exact C]]|split; [exact (proj1 (proj2 Hf))|exact A]].
Qed.

(*
Text put back
-------------

The fallbacks rebuild source from what a construct ate.  They only take
the text before a bracket back out of the scope and emit nodes into it,
so a state that already counts as holding something keeps its
invariant.
*)

Lemma opop_str_ok : forall W o h,
  oinv W o true h -> oinv W (snd (opop_str o)) true h.
Proof.
  intros W [out stk word] h (H1 & H2 & H3). unfold opop_str. cbn [os_stk os_out os_word_start] in *.
  destruct stk as [|f fs].
  - destruct out as [|[[p [|kv a] x]|a sp w] rest]; try (split; [exact H1|split; assumption]).
    destruct x; try (split; [exact H1|split; assumption]).
    inversion H1; subst. split; [assumption|split; constructor].
  - destruct (fr_out f) as [|[[p [|kv a] x]|a sp w] rest] eqn:Ho;
      try (split; [exact H1|split; assumption]).
    destruct x; try (split; [exact H1|split; assumption]).
    inversion H2 as [|? ? Hf Hfs]; subst. destruct H3 as (A & B & C).
    destruct Hf as (F1 & F2 & F3). rewrite Ho in F3. inversion F3; subst.
    split; [exact H1|split].
    + constructor; [|exact Hfs]. split; [exact F1|split; [exact F2|assumption]].
    + cbn [stack_ok fr_open fr_out]. split; [exact A|split; [|exact C]].
      intros _. apply B. right. reflexivity.
Qed.

Lemma bflat_ok : forall W (CU : InlineCursor) kids txt o h,
  Forall (dn_node W) kids -> oinv W o true h -> oinv W (snd (bflat kids txt o)) true h.
Proof.
  intros W CU kids. induction kids as [|[p a x] kids IH]; intros txt o h Hk Ho; [exact Ho|].
  inversion Hk; subst. cbn [bflat].
  destruct a as [|kv a]; [destruct x|];
    try (apply IH; [assumption|apply oemit_ok; [assumption|apply flush_text_at_touched, Ho]]).
  apply IH; assumption.
Qed.

Lemma bsplit_nl_ok : forall W (CU : InlineCursor) src txt o h,
  oinv W o true h -> oinv W (snd (bsplit_nl src txt o)) true h.
Proof.
  intros W CU src. induction src as [|c src IH]; intros txt o h Ho; [exact Ho|].
  cbn [bsplit_nl]. destruct (Ascii.eqb c nl_char); apply IH; [|exact Ho].
  apply oemit_ok; [apply dn_imk_plain; [reflexivity|constructor]|apply flush_text_at_touched, Ho].
Qed.

Lemma bclosed_lit_ok : forall W (CU : InlineCursor) kids image o h,
  Forall (dn_node W) kids -> oinv W o true h -> oinv W (snd (bclosed_lit kids image o)) true h.
Proof.
  intros W CU kids image o h Hk Ho. unfold bclosed_lit.
  pose proof (opop_str_ok W o h Ho) as H1.
  destruct (opop_str o) as [pre o1]. cbn [snd] in H1.
  pose proof (bflat_ok W CU kids (tof (pre ++ bracket_open image)) o1 h Hk H1) as H2.
  destruct (bflat kids _ o1) as [t o2]. exact H2.
Qed.

Lemma bspan_lit_ok : forall W (CU : InlineCursor) kids image src o h,
  Forall (dn_node W) kids -> oinv W o true h -> oinv W (snd (bspan_lit kids image src o)) true h.
Proof.
  intros W CU kids image src o h Hk Ho. unfold bspan_lit.
  pose proof (bclosed_lit_ok W CU kids image o h Hk Ho) as H1.
  destruct (bclosed_lit kids image o) as [t o1]. apply bsplit_nl_ok, H1.
Qed.

Lemma bref_lit_ok : forall W (CU : InlineCursor) kids image label o h,
  Forall (dn_node W) kids -> oinv W o true h -> oinv W (snd (bref_lit kids image label o)) true h.
Proof.
  intros W CU kids image label o h Hk Ho. unfold bref_lit.
  pose proof (bclosed_lit_ok W CU kids image o h Hk Ho) as H1.
  destruct (bclosed_lit kids image o) as [t o1]. exact H1.
Qed.

Lemma bnote_lit_ok : forall W (CU : InlineCursor) esc image label o h,
  oinv W o true h -> oinv W (snd (bnote_lit esc image label o)) true h.
Proof.
  intros W CU esc image label o h Ho. unfold bnote_lit.
  pose proof (opop_str_ok W o h Ho) as H1. destruct (opop_str o) as [pre o1]. exact H1.
Qed.

Lemma bwiki_lit_ok : forall W esc rb image region o h,
  oinv W o true h -> oinv W (snd (bwiki_lit esc rb image region o)) true h.
Proof.
  intros W esc rb image region o h Ho. unfold bwiki_lit.
  pose proof (opop_str_ok W o h Ho) as H1. destruct (opop_str o) as [pre o1]. exact H1.
Qed.

Lemma ospan_bang_ok : forall W (CU : InlineCursor) image o h,
  oinv W o true h -> oinv W (ospan_bang image o) true h.
Proof.
  intros W CU image o h Ho. unfold ospan_bang. destruct image; [|exact Ho].
  pose proof (opop_str_ok W o h Ho) as H1. destruct (opop_str o) as [pre o1].
  apply flush_text_at_touched, H1.
Qed.

Lemma iesc_hard_ok : forall W (CU : InlineCursor) ws txt o h,
  oinv W o true h -> oinv W (iesc_hard ws txt o) true h.
Proof.
  intros W CU ws txt o h Ho. unfold iesc_hard.
  apply oemit_ok; [apply dn_imk_plain; [reflexivity|constructor]|].
  apply flush_text_to_at_touched, Ho.
Qed.


(*
The cursor
----------

A step reads the byte at `cur`, and the next byte is one to the right.
*)

Section Cursor.
Variable W : list window.
Variable cur : spot.
Variable c : ascii.
Variable rest : string.
Hypothesis Hcur : sfx W cur = Some (String c rest).

Lemma cur_rem : 1 <= spot_rem cur.
Proof. pose proof (sfx_rem _ _ _ Hcur) as H. cbn in H. lia. Qed.

Lemma cur_next : spot_lt cur (sright 1 cur).
Proof. apply spot_lt_sright; [lia|apply cur_rem]. Qed.

Lemma cur_back : sleft 1 (sright 1 cur) = cur.
Proof. apply sleft_sright, cur_rem. Qed.

Lemma byte_back : byte_at W (sleft 1 (sright 1 cur)) = Some c.
Proof. rewrite cur_back. eapply byte_at_sfx. exact Hcur. Qed.

Lemma prev_here : prev_ok W (Some c) (sright 1 cur).
Proof. unfold prev_ok. rewrite byte_back. reflexivity. Qed.

Lemma ends_here : ends_at W (one c) (sright 1 cur).
Proof. eapply ends_at_one. exact Hcur. Qed.

Lemma oinv_next : forall o t, oinv W o t cur -> oinv W o true (sright 1 cur).
Proof. intros o t H. eapply oinv_strict; [apply cur_next|exact H]. Qed.

Lemma held_next : forall o t, oinv W o t cur -> held W o t (sright 1 cur).
Proof. intros o t H. eapply held_intro; [apply cur_next|exact H]. Qed.

End Cursor.

Lemma oinv_false : forall W o t h, oinv W o t h -> oinv W o false h.
Proof.
  intros W o t h (H1 & H2 & H3). split; [exact H1|split; [exact H2|]].
  destruct (os_stk o) as [|f rest]; [exact I|]. destruct H3 as (A & B & C).
  split; [exact A|split; [|exact C]]. intros [X|X]; [apply B; left; exact X|discriminate].
Qed.

Lemma oinv_any : forall W o t h, oinv W o true h -> oinv W o t h.
Proof. intros. apply oinv_untouch. assumption. Qed.

(* The bracket's scope, pushed at the cursor. *)
Lemma bpush_ok : forall W (CU : InlineCursor) (image : bool) o (start : spot),
  oinv W o false start ->
  start = (if image then previous_spot cursor_start else cursor_start) ->
  spot_lt start cursor_stop ->
  oinv W (bpush image o) false cursor_stop.
Proof.
  intros W CU image o start Ho Hs Hlt. unfold bpush, pspan. cbn [pos_records located_pos].
  rewrite <- Hs.
  exact (frame_push_ok W (FKBracket image) false (SrcSpan start cursor_stop) o I Ho Hlt).
Qed.

Lemma ilead_ok : forall W (CU : InlineCursor) cur c rest txt prev o,
  cursor_start = cur -> cursor_stop = sright 1 cur ->
  sfx W cur = Some (String c rest) ->
  oinv W o (nonempty_str txt) cur -> prev_ok W prev cur ->
  st_inv W (sright 1 cur) (ilead c txt prev o).
Proof.
  intros W CU cur c rest txt prev o Hs Hn Hcur Ho Hp.
  pose proof (oinv_next _ _ _ _ Hcur _ _ Ho) as Hon.
  pose proof (held_next _ _ _ _ Hcur _ _ Ho) as Hheld.
  pose proof (prev_here _ _ _ _ Hcur) as Hph.
  pose proof (byte_back _ _ _ _ Hcur) as Hb.
  pose proof (cur_back _ _ _ _ Hcur) as Hback.
  unfold ilead.
  destruct (is_bslash c) eqn:E1.
  { cbn [st_inv].
    split; [exact Hon|split; [exact Hph|]].
    intros _. unfold is_bslash in E1. apply Ascii.eqb_eq in E1. subst c. exact Hb. }
  destruct (is_tick c) eqn:E2.
  { cbn [st_inv]. split; [|lia]. eapply held_intro; [apply (cur_next _ _ _ _ Hcur)|].
    apply flush_text_at_ok, Ho. }
  destruct (Ascii.eqb c dollar) eqn:E3.
  { apply Ascii.eqb_eq in E3; subst c. cbn [st_inv]. split; [exact Hheld|exact Hb]. }
  destruct (Ascii.eqb c period) eqn:E4.
  { apply Ascii.eqb_eq in E4; subst c. cbn [st_inv]. split; [exact Hheld|exact Hb]. }
  destruct (Ascii.eqb c hyphen) eqn:E5.
  { apply Ascii.eqb_eq in E5; subst c. cbn [st_inv].
    split; [exact (ends_here _ _ _ _ Hcur)|split; [lia|]].
    rewrite Hback. exact Ho. }
  destruct (Ascii.eqb c lbrace) eqn:E6.
  { apply Ascii.eqb_eq in E6; subst c. cbn [st_inv]. rewrite Hback.
    split; [exact Ho|]. rewrite <- Hback. exact Hb. }
  destruct (Ascii.eqb c bang) eqn:E7.
  { apply Ascii.eqb_eq in E7; subst c. cbn [st_inv]. rewrite Hback.
    split; [exact Ho|]. rewrite <- Hback. exact Hb. }
  destruct (Ascii.eqb c lt) eqn:E8.
  { apply Ascii.eqb_eq in E8; subst c. cbn [st_inv].
    split; [exact Hheld|exact (ends_here _ _ _ _ Hcur)]. }
  destruct (Ascii.eqb c ":"%char) eqn:E9.
  { cbn [st_inv]. split; [exact Hheld|].
    split; [|split; [exact Hph|discriminate]]. apply remember_word_start_ok, oinv_any, Hon. }
  destruct (Ascii.eqb c lbrack) eqn:E10.
  { destruct (if (note_pos txt prev && wikilinks_enabled)%bool then bunpush o else None)
      as [[[image open] o']|] eqn:Ew.
    - destruct (note_pos txt prev && wikilinks_enabled)%bool; [|discriminate].
      destruct (bunpush_ok W o cur image open o' (oinv_false _ _ _ _ Ho) Ew) as (A & B & C).
      cbn [st_inv]. eapply held_intro; [|exact A].
      eapply spot_lt_trans; [exact B|].
      eapply spot_le_lt_trans; [exact C|apply (cur_next _ _ _ _ Hcur)].
    - apply Ascii.eqb_eq in E10; subst c. cbn [st_inv]. split; [|split; [exact Hph|discriminate]].
      rewrite <- Hn. apply bpush_ok with (start := cur).
      + apply flush_text_at_ok. exact Ho.
      + symmetry. exact Hs.
      + rewrite Hn. apply (cur_next _ _ _ _ Hcur). }
  destruct (Ascii.eqb c rbrack) eqn:E11.
  { apply Ascii.eqb_eq in E11; subst c. cbn [st_inv]. rewrite Hback.
    split; [exact Ho|]. rewrite <- Hback. exact Hb. }
  destruct (if (Ascii.eqb c hat && note_pos txt prev && notes_enabled)%bool
            then bunpush o else None) as [[[image open] o']|] eqn:Ew.
  { destruct (Ascii.eqb c hat && note_pos txt prev && notes_enabled)%bool; [|discriminate].
    destruct (bunpush_ok W o cur image open o' (oinv_false _ _ _ _ Ho) Ew) as (A & B & C).
    cbn [st_inv]. eapply held_intro; [|exact A].
    eapply spot_lt_trans; [exact B|].
    eapply spot_le_lt_trans; [exact C|apply (cur_next _ _ _ _ Hcur)]. }
  destruct (dstyle_of c) as [k|] eqn:Ek.
  - apply dstyle_of_char in Ek. cbn [st_inv].
    assert (Hr : delim_run k 0 false = one c) by (unfold delim_run; rewrite Ek; reflexivity).
    rewrite Hr. cbn [String.length one]. rewrite Hback.
    split; [pose proof (dwidth_nonzero k); lia|].
    split; [exact (ends_here _ _ _ _ Hcur)|split; [exact Ho|intros _; exact Hp]].
  - cbn [st_inv]. split; [|split; [exact Hph|discriminate]].
    apply remember_word_start_ok, oinv_any, Hon.
Qed.

(*
Delimiters
----------

The two rules are the scanner's two tests.  A bare token opens only if
the byte after it is nonspace (`idelim_done`), and closes only if the
byte before it is (`idelim_resolve`); the opener's frame and the
closer's position are where the window says.
*)

Lemma chars_snoc : forall c n, chars c (S n) = (chars c n ++ one c)%string.
Proof.
  intros c n. induction n as [|n IH]; [reflexivity|].
  cbn [chars] in *. cbn [append]. f_equal. exact IH.
Qed.

Lemma dtoken_snoc : forall k, exists s, dtoken k = (s ++ one (dchar k))%string.
Proof.
  intros k. unfold dtoken. destruct (dwidth k) as [|w] eqn:E.
  - destruct (dwidth_nonzero k E).
  - exists (chars (dchar k) w). apply chars_snoc.
Qed.

Lemma nonempty_app_r : forall a b, nonempty_str b = true -> nonempty_str (a ++ b) = true.
Proof. intros [|c a] b H; [exact H|reflexivity]. Qed.

Lemma delim_run_snoc : forall k extra m,
  delim_run k (S extra) m = (delim_run k extra m ++ one (dchar k))%string.
Proof. intros k extra m. unfold delim_run. rewrite chars_snoc, append_assoc. reflexivity. Qed.

Lemma delim_run_last : forall k extra m,
  exists s, delim_run k extra m = (s ++ one (dchar k))%string.
Proof.
  intros k extra m. unfold delim_run. rewrite chars_snoc, <- append_assoc. eexists. reflexivity.
Qed.

Lemma delim_run_length : forall k extra m,
  String.length (delim_run k extra m) = (if m then 1 else 0) + S extra.
Proof.
  intros k extra m. unfold delim_run. rewrite length_append.
  assert (H : forall c n, String.length (chars c n) = n)
    by (induction n as [|n IH]; [reflexivity|cbn; rewrite IH; reflexivity]).
  rewrite H. destruct m; reflexivity.
Qed.

(* The byte before the cursor, read off what lies before it. *)
Lemma prev_of_ends : forall W s c p, ends_at W (s ++ one c) p -> prev_ok W (Some c) p.
Proof. intros W s c p H. unfold prev_ok. rewrite (ends_at_last _ _ _ _ H). reflexivity. Qed.

Lemma prev_nonspace : forall W prev p,
  prev_ok W prev p -> nonspace_at prev = true ->
  exists b, byte_at W (sleft 1 p) = Some b /\ nonspace_at (Some b) = true /\ prev = Some b.
Proof.
  intros W prev p Hp Hn. unfold prev_ok in Hp.
  destruct (byte_at W (sleft 1 p)) as [b|].
  - subst prev. eauto.
  - destruct Hp as [->| ->]; discriminate.
Qed.

Section Delim.
Variable W : list window.
Context (CU : InlineCursor).
Variable cur : spot.
Hypothesis Hs : cursor_start = cur.
Variable k : dstyle.
Hypothesis Htok : ends_at W (dtoken k) cur.

Let ts := sleft (dwidth k) cur.

Lemma ts_lt : spot_lt ts cur.
Proof. apply spot_lt_sleft. pose proof (dwidth_nonzero k). lia. Qed.

Lemma ts_eq : sleft (String.length (dtoken k)) cur = ts.
Proof. unfold ts. rewrite dtoken_length. reflexivity. Qed.

Lemma prev_dchar : prev_ok W (Some (dchar k)) cur.
Proof. destruct (dtoken_snoc k) as [s Hs']. rewrite Hs' in Htok. eapply prev_of_ends, Htok. Qed.

Lemma otok_after : sright (String.length (otok k false)) ts = cur.
Proof. unfold otok. cbn [append]. rewrite dtoken_length. unfold ts. apply sright_sleft. Qed.

Lemma dtoken_span_eq : dtoken_span k false = SrcSpan ts cur.
Proof.
  unfold dtoken_span, pspan. cbn [pos_records located_pos]. rewrite Hs.
  rewrite spot_before_no_nl; [|apply dtoken_no_nl]. cbn [append]. rewrite ts_eq. reflexivity.
Qed.

(* Where the scan is after resolving the token: past a `}` it consumed,
   or at the byte after the token otherwise. *)
Definition dafter (marker : bool) : spot := if marker then sright 1 cur else cur.

Lemma delim_lit_ok : forall txt marker o,
  oinv W o (nonempty_str txt) ts ->
  (marker = true -> byte_at W cur = Some rbrace) ->
  oinv W o (nonempty_str (InlineScan.idelim_lit k txt marker)) (dafter marker) /\
  prev_ok W (InlineScan.idelim_lit_prev k marker) (dafter marker).
Proof.
  intros txt marker o Ho Hm. split.
  - apply oinv_any. eapply oinv_strict; [|exact Ho].
    eapply spot_lt_le_trans; [apply ts_lt|]. unfold dafter.
    destruct marker; [apply spot_le_sright|apply spot_le_refl].
  - unfold dafter, InlineScan.idelim_lit_prev. destruct marker.
    + specialize (Hm eq_refl). unfold byte_at in Hm.
      destruct (sfx W cur) as [[|b r]|] eqn:E; try discriminate. injection Hm as ->.
      exact (prev_here _ _ _ _ E).
    + exact prev_dchar.
Qed.

Lemma idelim_done_ok : forall txt before marker next o,
  oinv W o (nonempty_str txt) ts ->
  (marker = true -> byte_at W cur = Some rbrace) ->
  match next with Some x => byte_at W cur = Some x | None => True end ->
  exists txt' prev' o',
    idelim_done k txt before marker next o = IText false txt' prev' o' /\
    oinv W o' (nonempty_str txt') (dafter marker) /\ prev_ok W prev' (dafter marker).
Proof.
  intros txt before marker next o Ho Hm Hx. unfold idelim_done.
  destruct (dbare k before && negb marker && nonspace_at next)%bool eqn:E.
  - apply andb_true_iff in E as [E Enx]. apply andb_true_iff in E as [_ Em].
    apply negb_true_iff in Em. subst marker.
    destruct next as [x|]; [|discriminate].
    do 3 eexists. split; [reflexivity|]. split; [|exact prev_dchar].
    unfold opush. rewrite dtoken_span_eq. cbn [nonempty_str].
    change cur with (span_stop (SrcSpan ts cur)).
    apply opush_at_ok; cbn [span_start span_stop].
    + apply flush_text_to_at_ok, Ho.
    + destruct Htok as [r Hr]. rewrite ts_eq in Hr. exists r.
      split; [exact Hr|].
      intros _. exists x. split; [|exact Enx]. rewrite otok_after. exact Hx.
    + symmetry. apply otok_after.
    + apply ts_lt.
  - destruct (delim_lit_ok txt marker o Ho Hm) as [A B].
    do 3 eexists. split; [reflexivity|]. split; eassumption.
Qed.

Lemma idelim_resolve_ok : forall txt before marker next o,
  oinv W o (nonempty_str txt) ts ->
  (marker = false -> prev_ok W before ts) ->
  (marker = true -> byte_at W cur = Some rbrace) ->
  (marker = true -> cursor_stop = sright 1 cur) ->
  match next with Some x => byte_at W cur = Some x | None => True end ->
  exists txt' prev' o',
    idelim_resolve k txt before marker next o = IText false txt' prev' o' /\
    oinv W o' (nonempty_str txt') (dafter marker) /\ prev_ok W prev' (dafter marker).
Proof.
  intros txt before marker next o Ho Hb Hm Hn Hx. unfold idelim_resolve.
  rewrite oclose_guard. tred.
  destruct (nonspace_at before || marker)%bool eqn:Ecl;
    [|apply idelim_done_ok; assumption].
  rewrite dtoken_span_eq. cbn [span_start].
  destruct (oclose k marker (if marker then cursor_stop else cursor_start)
              (flush_text_to_at ts txt o)) as [o'|] eqn:Eo.
  - do 3 eexists. split; [reflexivity|].
    assert (Hcl : closer_at W k marker (dafter marker)).
    { unfold closer_at, dafter, ctok. destruct marker.
      - specialize (Hm eq_refl). unfold byte_at in Hm.
        destruct (sfx W cur) as [[|b r]|] eqn:E; try discriminate. injection Hm as ->.
        exists r. rewrite length_append, dtoken_length. cbn [String.length one].
        replace (sleft (dwidth k + 1) (sright 1 cur)) with ts.
        + split; [|intros H; discriminate].
          pose proof (ends_at_sfx _ _ _ _ Htok E) as H. rewrite ts_eq in H.
          rewrite append_assoc. exact H.
        + unfold ts. pose proof (cur_rem _ _ _ _ E). destruct cur as [kk rr].
          unfold sleft, sright. cbn in *. f_equal. lia.
      - rewrite append_empty_r. destruct Htok as [r Hr]. exists r.
        rewrite ts_eq in Hr |- *. split; [exact Hr|]. intros _.
        rewrite orb_false_r in Ecl.
        destruct (prev_nonspace _ _ _ (Hb eq_refl) Ecl) as (b & B1 & B2 & _).
        exists b. split; assumption. }
    assert (Hstop : (if marker then cursor_stop else cursor_start) = dafter marker)
      by (unfold dafter; destruct marker; [exact (Hn eq_refl)|exact Hs]).
    rewrite Hstop in Eo.
    assert (Hts : sleft (String.length (ctok k marker)) (dafter marker) = ts).
    { unfold dafter, ts. rewrite ctok_length. destruct marker.
      - specialize (Hm eq_refl). unfold byte_at in Hm.
        destruct (sfx W cur) as [[|b r]|] eqn:E; try discriminate.
        pose proof (cur_rem _ _ _ _ E). destruct cur as [kk rr].
        unfold sleft, sright. cbn in *. f_equal. lia.
      - destruct cur as [kk rr]. unfold sleft. cbn. f_equal. lia. }
    pose proof (oclose_ok W k marker (dafter marker) _ ts o'
                  (flush_text_to_at_ok W CU ts txt o ts Ho) Hcl
                  (eq_ind_r (fun x => spot_le ts x) (spot_le_refl ts) Hts) Eo) as Hc.
    split; [apply oinv_any, Hc|].
    exact (proj2 (delim_lit_ok txt marker o Ho Hm)).
  - destruct (oclose_barred k marker o).
    + destruct (delim_lit_ok txt marker o Ho Hm) as [A B].
      do 3 eexists. split; [reflexivity|]. split; eassumption.
    + apply idelim_done_ok; assumption.
Qed.

End Delim.

(*
Braces and specs
----------------
*)

(* A spec is done only on the `}` that closes it. *)
Lemma astep_done : forall p c,
  ap_done p = false -> ap_done (astep p c) = true -> c = "}"%char.
Proof.
  intros [st tok key at'] c H1 H2. unfold astep in H2. cbn [ap_st] in *.
  destruct st; unfold ap_done in H1; cbn in H1; try discriminate;
    unfold ap_done in H2; cbn in H2;
    repeat match type of H2 with
           | context [if ?b then _ else _] => let E := fresh "E" in destruct b eqn:E
           end; cbn in H2; try discriminate;
    apply Ascii.eqb_eq; assumption.
Qed.

Lemma snoc_decomp : forall s, s <> EmptyString -> exists s' c, s = (s' ++ one c)%string.
Proof.
  induction s as [|x s IH]; intros H; [contradiction|].
  destruct s as [|y s'].
  - exists EmptyString, x. reflexivity.
  - destruct (IH ltac:(discriminate)) as (s0 & c & ->).
    exists (String x s0), c. reflexivity.
Qed.

Lemma str_last_snoc : forall s c d, str_last (s ++ one c) d = Some c.
Proof. induction s as [|x s IH]; intros c d; [reflexivity|apply IH]. Qed.

Lemma prev_blit : forall W s p,
  ends_at W s p -> s <> EmptyString -> prev_ok W (InlineScan.blit_prev s) p.
Proof.
  intros W s p He Hne. destruct (snoc_decomp s Hne) as (s' & c & ->).
  unfold InlineScan.blit_prev. rewrite str_last_snoc. eapply prev_of_ends, He.
Qed.

Lemma byte_left : forall W p b s,
  byte_at W (sleft 1 p) = Some b -> sfx W p = Some s ->
  sfx W (sleft 1 p) = Some (String b s).
Proof.
  intros W p b s Hb Hp. unfold byte_at in Hb.
  destruct (sfx W (sleft 1 p)) as [[|b' s']|] eqn:E; try discriminate.
  injection Hb as ->. pose proof (sfx_cons _ _ _ _ E) as H.
  rewrite sright_sleft, Hp in H. injection H as ->. reflexivity.
Qed.

Lemma islice_end_ok : forall W cur st, st_inv W cur st -> st_inv W cur (islice_end st).
Proof.
  intros W cur st. induction st; intros H; cbn [islice_end]; try exact H; cbn [st_inv] in *; tred; cbn [orb] in *.
  - (* IText *) destruct esc; [|exact H].
    destruct H as (A & B & C). split; [|split; [|discriminate]].
    + rewrite (nonempty_app_r txt (one bslash) eq_refl). exact A.
    + unfold prev_ok. rewrite (C eq_refl). reflexivity.
  - (* IBrace *) destruct H as (A & B). 
    split; [|split; [unfold prev_ok; rewrite B; reflexivity|discriminate]].
    rewrite (nonempty_app_r txt (one lbrace) eq_refl).
    eapply oinv_strict; [|exact A]; apply spot_lt_sleft; lia.
  - (* IPeriod *) destruct H as (A & B). 
    split; [|split; [unfold prev_ok; rewrite B; reflexivity|discriminate]].
    apply oinv_any; exact (held_oinv _ _ _ _ A).
  - (* IDash *) destruct H as (A & B & C). 
    split; [|split; [|discriminate]].
    + apply oinv_any. eapply oinv_strict; [|exact C]; apply spot_lt_sleft; lia.
    + destruct n as [|n]; [lia|]. rewrite chars_snoc in A. eapply prev_of_ends, A.
  - (* IClosed *) destruct H as (A & B). 
    split; [|split; [unfold prev_ok; rewrite B; reflexivity|discriminate]].
    rewrite (nonempty_app_r txt (one rbrack) eq_refl).
    eapply oinv_strict; [|exact A]; apply spot_lt_sleft; lia.
  - (* IAuto *) destruct H as (A & B). 
    split; [|split; [apply prev_blit; [exact B|discriminate]|discriminate]].
    apply oinv_any; exact (held_oinv _ _ _ _ A).
  - (* ISymbol *) destruct H as (A & B). apply IHst, B.
Qed.

Lemma iattr_feed_ok : forall W (CU : InlineCursor) cur next c p src txt prev sh o,
  spot_le cur next ->
  (c = "}"%char -> prev_ok W (Some c) next) ->
  held W o (nonempty_str txt) cur -> ap_done p = false -> st_inv W next sh ->
  st_inv W next (iattr_feed c p src txt prev sh o).
Proof.
  intros W CU cur next c p src txt prev sh o Hle Hc Ho Hd Hsh. unfold iattr_feed.
  destruct (ap_failed (astep p c)); [exact Hsh|].
  destruct (ap_done (astep p c)) eqn:Ed.
  - pose proof (astep_done p c Hd Ed) as ->. unfold iattr_mark. cbn [st_inv]. tred. cbn [orb].
    split; [|split; [exact (Hc eq_refl)|discriminate]].
    apply oinv_any, omark_ok, flush_text_to_at_touched.
    eapply oinv_mono; [exact Hle|]. exact (held_oinv _ _ _ _ Ho).
  - cbn [st_inv]. split; [eapply held_mono; eassumption|].
    split; [exact Ed|apply islice_end_ok, Hsh].
Qed.

Lemma oopen_marked_ok : forall W (CU : InlineCursor) cur k cm txt o,
  cursor_start = cur ->
  ends_at W (otok k true) cur ->
  oinv W o (nonempty_str txt) (sleft (String.length (otok k true)) cur) ->
  oinv W (oopen_marked k cm txt o) false cur.
Proof.
  intros W CU cur k cm txt o Hs He Ho. unfold oopen_marked.
  assert (Hsp : dtoken_span k true = SrcSpan (sleft (String.length (otok k true)) cur) cur).
  { unfold dtoken_span, pspan. cbn [pos_records located_pos]. rewrite Hs.
    rewrite spot_before_no_nl; [reflexivity|]. apply (otok_no_nl k true). }
  rewrite Hsp. change cur with (span_stop (SrcSpan (sleft (String.length (otok k true)) cur) cur)) at 2.
  apply opush_at_ok; cbn [span_start span_stop].
  - tred. apply flush_text_to_at_ok, Ho.
  - destruct He as [r Hr]. exists r. split; [exact Hr|discriminate].
  - rewrite sright_sleft. reflexivity.
  - apply spot_lt_sleft. rewrite otok_length. pose proof (dwidth_nonzero k). lia.
Qed.

Lemma ibrace_ok : forall W (CU : InlineCursor) cur c rest allow txt prev o,
  cursor_start = cur -> cursor_stop = sright 1 cur ->
  sfx W cur = Some (String c rest) ->
  oinv W o (nonempty_str txt) (sleft 1 cur) ->
  byte_at W (sleft 1 cur) = Some lbrace ->
  st_inv W (sright 1 cur) (ibrace_step_at allow c txt prev o).
Proof.
  intros W CU cur c rest allow txt prev o Hs Hn Hcur Ho Hb.
  pose proof (cur_back _ _ _ _ Hcur) as Hback.
  assert (Hcur1 : oinv W o true cur)
    by (eapply oinv_strict; [|exact Ho]; apply spot_lt_sleft; lia).
  assert (Hprev : prev_ok W (Some lbrace) cur) by (unfold prev_ok; rewrite Hb; reflexivity).
  unfold ibrace_step_at.
  destruct (dstyle_of c) as [k|] eqn:Ek.
  - apply dstyle_of_char in Ek. unfold idelim_marked. cbn [st_inv].
    rewrite delim_run_length. cbn [Nat.add].
    replace (sleft 2 (sright 1 cur)) with (sleft 1 cur)
      by (pose proof (cur_rem _ _ _ _ Hcur); destruct cur as [kk rr];
          unfold sleft, sright; cbn in *; f_equal; lia).
    split; [pose proof (dwidth_nonzero k); lia|].
    split; [|split; [exact Ho|discriminate]].
    exists rest. unfold delim_run. cbn [String.length chars one append].
    replace (sleft 2 (sright 1 cur)) with (sleft 1 cur)
      by (pose proof (cur_rem _ _ _ _ Hcur); destruct cur as [kk rr];
          unfold sleft, sright; cbn in *; f_equal; lia).
    rewrite Ek. exact (byte_left _ _ _ _ Hb Hcur).
  - destruct allow.
    + apply iattr_feed_ok with (cur := cur).
      * apply spot_lt_le, (cur_next _ _ _ _ Hcur).
      * intros ->. exact (prev_here _ _ _ _ Hcur).
      * eapply held_intro; [|exact Ho]; apply spot_lt_sleft; lia.
      * reflexivity.
      * apply (ilead_ok W CU cur c rest); try assumption. tred.
        rewrite (nonempty_app_r txt (one lbrace) eq_refl). exact Hcur1.
    + unfold battr_lit. cbn [bsplit_nl]. tred.
      apply (ilead_ok W CU cur c rest); try assumption.
      * rewrite (nonempty_app_r txt (one lbrace) eq_refl). exact Hcur1.
Qed.


(*
One byte, state by state
------------------------
*)

Lemma held_step : forall W o t t' cur next,
  held W o t cur -> spot_lt cur next -> held W o t' next.
Proof.
  intros W o t t' cur next H Hlt. eapply held_intro; [exact Hlt|].
  apply oinv_any. exact (held_oinv _ _ _ _ H).
Qed.

Lemma previous_spot_eq : forall p, previous_spot p = sleft 1 p.
Proof. intros [k r]. unfold previous_spot, sleft. cbn. f_equal. lia. Qed.

Lemma typography_dashes_0 : typography_dashes 0 = EmptyString.
Proof. unfold typography_dashes. destruct smart_typography; reflexivity. Qed.

Lemma chars_add : forall c a b, chars c (a + b) = (chars c a ++ chars c b)%string.
Proof. intros c a b. induction a as [|a IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma ends_at_suffix : forall W a b p, ends_at W (a ++ b) p -> ends_at W b p.
Proof.
  intros W a b p [r H]. rewrite append_assoc in H.
  pose proof (sfx_app _ _ _ _ H) as H1. exists r.
  replace (sleft (String.length b) p)
    with (sright (String.length a) (sleft (String.length (a ++ b)) p)); [exact H1|].
  rewrite length_append. destruct p as [k rr]. unfold sleft, sright. cbn. f_equal. lia.
Qed.

Lemma ends_at_nonempty_prev : forall W s p,
  ends_at W s p -> s <> EmptyString -> forall d, prev_ok W (str_last s d) p.
Proof.
  intros W s p He Hne d. destruct (snoc_decomp s Hne) as (s' & c & ->).
  rewrite str_last_snoc. eapply prev_of_ends, He.
Qed.

Lemma ilead_nl : forall W (CU : InlineCursor) cur next txt prev o,
  spot_lt cur next -> byte_at W (sleft 1 next) = None ->
  oinv W o (nonempty_str txt) cur ->
  st_inv W next (ilead nl_char txt prev o).
Proof.
  intros W CU cur next txt prev o Hlt Hb Ho.
  assert (Hk : dstyle_of nl_char = None).
  { destruct (dstyle_of nl_char) as [k|] eqn:E; [|reflexivity].
    apply dstyle_of_char in E. pose proof (dchar_not_nl k) as H. rewrite E in H. discriminate. }
  unfold ilead. cbn -[dstyle_of remember_word_start note_pos bunpush oinv prev_ok byte_at].
  rewrite Hk. cbn [st_inv]. tred. cbn [orb].
  split; [|split; [unfold prev_ok; rewrite Hb; right; reflexivity|discriminate]].
  apply remember_word_start_ok. apply oinv_any. eapply oinv_strict; eassumption.
Qed.

Lemma dn_imk_leaf : forall W start stop x,
  dkind x = None -> children x = [] -> dn_node W (imk start stop x).
Proof. intros W start stop x Hk Hc. apply dn_imk_plain; [exact Hk|rewrite Hc; constructor]. Qed.

Lemma dn_auto : forall W start stop s, dn_node W (imk start stop (auto_node s)).
Proof. intros. unfold auto_node. destruct (auto_email s); apply dn_imk_leaf; reflexivity. Qed.

Lemma dn_vnode : forall W start stop vk s, dn_node W (imk start stop (vnode vk s)).
Proof. intros. destruct vk; apply dn_imk_leaf; reflexivity. Qed.

Lemma dn_bnode : forall W start stop image kids tgt,
  Forall (dn_node W) kids -> dn_node W (imk start stop (bnode image kids tgt)).
Proof. intros. destruct image; apply dn_imk_plain; (reflexivity || assumption). Qed.

(* Where a byte took the scan: one byte along the window, or across a
   line break, which the scanner reads as a newline with nothing before
   it on the new line. *)
Definition stepped (W : list window) (CU : InlineCursor) (cur next : spot) (c : ascii) : Prop :=
  (exists rest, sfx W cur = Some (String c rest) /\ next = sright 1 cur /\
                cursor_start = cur /\ cursor_stop = next) \/
  (c = nl_char /\ spot_lt cur next /\ byte_at W (sleft 1 next) = None).

Lemma stepped_lt : forall W CU cur next c, stepped W CU cur next c -> spot_lt cur next.
Proof.
  intros W CU cur next c [(r & H1 & -> & _)|(_ & H & _)]; [exact (cur_next _ _ _ _ H1)|exact H].
Qed.

Lemma stepped_prev : forall W CU cur next c, stepped W CU cur next c -> prev_ok W (Some c) next.
Proof.
  intros W CU cur next c [(r & H1 & -> & _)|(-> & _ & H)];
    [exact (prev_here _ _ _ _ H1)|unfold prev_ok; rewrite H; right; reflexivity].
Qed.

Lemma stepped_ilead : forall W CU cur next c txt prev o,
  stepped W CU cur next c -> oinv W o (nonempty_str txt) cur -> prev_ok W prev cur ->
  st_inv W next (ilead c txt prev o).
Proof.
  intros W CU cur next c txt prev o [(r & H1 & -> & Hs & Hn)|(-> & Hlt & Hb)] Ho Hp.
  - eapply ilead_ok; eassumption.
  - eapply ilead_nl; eassumption.
Qed.

Lemma ispan_feed_ok : forall W (CU : InlineCursor) cur next c kids image open p src o,
  stepped W CU cur next c ->
  Forall (dn_node W) kids -> held W o false cur ->
  prev_ok W (InlineScan.blit_prev (String lbrace src)) cur -> ap_done p = false ->
  st_inv W next (ispan_feed c kids image open p src o).
Proof.
  intros W CU cur next c kids image open p src o Hst Hk Ho Hp Hd.
  pose proof (held_oinv _ _ _ _ Ho) as Ht. pose proof (stepped_lt _ _ _ _ _ Hst) as Hlt.
  unfold ispan_feed.
  destruct (ap_failed (astep p c)).
  - pose proof (bspan_lit_ok W CU kids image (tval src) o cur Hk Ht) as H.
    destruct (bspan_lit kids image (tval src) o) as [txt o'].
    eapply stepped_ilead; [exact Hst|apply oinv_any, H|exact Hp].
  - destruct (ap_done (astep p c)) eqn:Ed.
    + pose proof (astep_done p c Hd Ed) as Hc. cbn [st_inv orb].
      split; [|split; [|discriminate]].
      2: { replace (Some rbrace) with (Some c) by (rewrite Hc; reflexivity).
           exact (stepped_prev _ _ _ _ _ Hst). }
      apply oinv_any, oemit_ok.
      * apply dn_add_inline_role, dn_node_plain; [reflexivity|exact Hk].
      * apply ospan_bang_ok. eapply oinv_mono; [apply spot_lt_le, Hlt|exact Ht].
    + cbn [st_inv]. tred. split; [exact Hk|split; [eapply held_mono; [apply spot_lt_le, Hlt|exact Ho]|]].
      split; [|exact Ed].
      change (String lbrace (src ++ one c)) with ((String lbrace src) ++ one c)%string.
      unfold InlineScan.blit_prev. rewrite str_last_snoc. exact (stepped_prev _ _ _ _ _ Hst).
Qed.

Section Step.
Local Set Default Proof Using "All".
Variable W : list window.
Context (CU : InlineCursor).
Variable cur : spot.
Variable c : ascii.
Variable rest : string.
Hypothesis Hs : cursor_start = cur.
Hypothesis Hn : cursor_stop = sright 1 cur.
Hypothesis Hcur : sfx W cur = Some (String c rest).

Let next := sright 1 cur.

Lemma nx_lt : spot_lt cur next.
Proof. exact (cur_next _ _ _ _ Hcur). Qed.

Lemma nx_prev : prev_ok W (Some c) next.
Proof. exact (prev_here _ _ _ _ Hcur). Qed.

Lemma nx_back : sleft 1 next = cur.
Proof. exact (cur_back _ _ _ _ Hcur). Qed.

(* `ilead` from a state that has already consumed something. *)
Lemma ilead_held : forall txt prev o,
  oinv W o true cur -> prev_ok W prev cur -> st_inv W next (ilead c txt prev o).
Proof.
  intros txt prev o Ho Hp. apply (ilead_ok W CU cur c rest); try assumption.
  apply oinv_any, Ho.
Qed.

Lemma text_next : forall txt o,
  oinv W o true cur -> st_inv W next (IText false txt (Some c) o).
Proof.
  intros txt o Ho. cbn [st_inv orb]. split; [|split; [exact nx_prev|discriminate]].
  apply oinv_any. eapply oinv_strict; [exact nx_lt|exact Ho].
Qed.

Lemma iescws_ok : forall ws txt prev o,
  held W o (nonempty_str txt) cur -> ends_at W ws cur -> ws <> EmptyString ->
  let '(txt', prev', o') := iescws_resolve ws txt prev o in
  oinv W o' (nonempty_str txt') cur /\ prev_ok W prev' cur.
Proof.
  intros ws txt prev o Ho He Hne. pose proof (held_oinv _ _ _ _ Ho) as Ht.
  unfold iescws_resolve. tred.
  destruct ws as [|c0 r]; [contradiction|].
  destruct (Ascii.eqb c0 " "%char).
  - split.
    + apply oinv_any, oemit_ok; [apply dn_imk_plain; [reflexivity|constructor]|].
      apply flush_text_to_at_touched, Ht.
    + exact (ends_at_nonempty_prev _ _ _ He Hne None).
  - split; [apply oinv_any, Ht|exact (ends_at_nonempty_prev _ _ _ He Hne prev)].
Qed.

Lemma idollar_ok : forall two txt prev o,
  held W o (nonempty_str txt) cur -> byte_at W (sleft 1 cur) = Some dollar ->
  st_inv W next (idollar_step c two txt prev o).
Proof.
  intros two txt prev o Ho Hb. pose proof (held_oinv _ _ _ _ Ho) as Ht.
  pose proof nx_back as Hback. unfold idollar_step.
  destruct (Ascii.eqb c dollar) eqn:E.
  - apply Ascii.eqb_eq in E.
    destruct two; cbn [st_inv]; (split; [eapply held_step; [exact Ho|exact nx_lt]|]);
      rewrite Hback, <- E; exact (byte_at_sfx _ _ _ _ Hcur).
  - assert (Hl : forall t, st_inv W next (ilead c t (Some dollar) o))
      by (intros t; apply ilead_held; [exact Ht|unfold prev_ok; rewrite Hb; reflexivity]).
    destruct (is_tick c && math_enabled)%bool.
    + cbn [st_inv]. split; [|lia]. destruct Ho as (h & Hlt & Hh).
      eapply held_intro; [eapply spot_lt_trans; [exact Hlt|exact nx_lt]|].
      tred. apply flush_text_to_at_ok, Hh.
    + destruct (is_tick c && dollar_math_enabled && negb two)%bool.
      { cbn [st_inv]. split; [|lia]. eapply held_intro; [exact nx_lt|].
        tred. apply flush_text_to_at_ok, oinv_any, Ht. }
      destruct (dollar_math_enabled && _ && _)%bool; [|apply Hl].
      cbn [st_inv]. split; [eapply held_step; [exact Ho|exact nx_lt]|apply Hl].
Qed.

Lemma iperiod_ok : forall two txt prev o,
  held W o (nonempty_str txt) cur -> byte_at W (sleft 1 cur) = Some period ->
  st_inv W next (iperiod_step c two txt prev o).
Proof.
  intros two txt prev o Ho Hb. pose proof (held_oinv _ _ _ _ Ho) as Ht.
  pose proof nx_back as Hback. unfold iperiod_step.
  destruct (Ascii.eqb c period) eqn:E.
  - destruct two.
    + apply text_next, Ht.
    + apply Ascii.eqb_eq in E. cbn [st_inv].
      split; [eapply held_step; [exact Ho|exact nx_lt]|].
      rewrite Hback, <- E; exact (byte_at_sfx _ _ _ _ Hcur).
  - apply ilead_held; [exact Ht|unfold prev_ok; rewrite Hb; reflexivity].
Qed.

Lemma idash_ok : forall n txt prev o,
  ends_at W (chars hyphen n) cur -> 1 <= n -> oinv W o (nonempty_str txt) (sleft n cur) ->
  st_inv W next (idash_step c n txt prev o).
Proof.
  intros n txt prev o He Hn1 Ho.
  assert (Ht : oinv W o true cur)
    by (eapply oinv_strict; [|exact Ho]; apply spot_lt_sleft; lia).
  assert (Hph : prev_ok W (Some hyphen) cur).
  { destruct n as [|n]; [lia|]. rewrite chars_snoc in He. eapply prev_of_ends, He. }
  unfold idash_step.
  destruct (Ascii.eqb c hyphen) eqn:E1.
  - apply Ascii.eqb_eq in E1. pose proof Hcur as Hc'. rewrite E1 in Hc'. cbn [st_inv].
    split; [rewrite chars_snoc; eapply ends_at_snoc; [exact He|exact Hc']|split; [lia|]].
    replace (sleft (S n) next) with (sleft n cur); [exact Ho|].
    unfold next. pose proof (cur_rem _ _ _ _ Hcur). destruct cur as [kk rr].
    unfold sleft, sright. cbn in *. f_equal. lia.
  - destruct (Ascii.eqb c rbrace) eqn:E2.
    + apply Ascii.eqb_eq in E2. pose proof Hcur as Hc'. rewrite E2 in Hc'.
      assert (Hlit : st_inv W next
                (IText false (txt ++ typography_dashes n ++ one rbrace) (Some rbrace) o))
        by (rewrite <- E2; apply text_next, Ht).
      destruct (dstyle_of hyphen) as [k|] eqn:Ek; [|exact Hlit].
      destruct (Nat.leb (dwidth k) n) eqn:Ew; [|exact Hlit].
      apply Nat.leb_le in Ew. apply dstyle_of_char in Ek.
      assert (Htok : ends_at W (dtoken k) cur).
      { unfold dtoken. rewrite Ek.
        replace n with ((n - dwidth k) + dwidth k) in He by lia.
        rewrite chars_add in He. eapply ends_at_suffix, He. }
      assert (Hts : oinv W o (nonempty_str (txt ++ typography_dashes (n - dwidth k)))
                      (sleft (dwidth k) cur)).
      { destruct (n - dwidth k) as [|d] eqn:Ed.
        - rewrite typography_dashes_0, append_empty_r.
          replace (dwidth k) with n by lia. exact Ho.
        - apply oinv_any. eapply oinv_strict; [|exact Ho].
          destruct cur as [kk rr]. unfold spot_lt, sleft. cbn. lia. }
      destruct (idelim_resolve_ok W CU cur Hs k Htok _ None true (Some rbrace) o Hts
                  ltac:(discriminate) (fun _ => byte_at_sfx _ _ _ _ Hc') (fun _ => Hn)
                  (byte_at_sfx _ _ _ _ Hc'))
        as (txt' & prev' & o' & Eq & A & B).
      tred. rewrite E2, Eq. cbn [st_inv orb]. split; [exact A|split; [exact B|discriminate]].
    + apply ilead_held; [exact Ht|exact Hph].
Qed.

Lemma ibang_ok : forall txt prev o,
  oinv W o (nonempty_str txt) (sleft 1 cur) -> byte_at W (sleft 1 cur) = Some bang ->
  st_inv W next (ibang_step c txt prev o).
Proof.
  intros txt prev o Ho Hb.
  assert (Ht : oinv W o true cur)
    by (eapply oinv_strict; [|exact Ho]; apply spot_lt_sleft; lia).
  unfold ibang_step.
  destruct (Ascii.eqb c lbrack) eqn:E.
  - apply Ascii.eqb_eq in E. cbn [st_inv orb].
    split; [|split; [rewrite <- E; exact nx_prev|discriminate]].
    unfold next. rewrite <- Hn. apply bpush_ok with (start := sleft 1 cur).
    + tred. rewrite Hs, previous_spot_eq. apply flush_text_to_at_ok, Ho.
    + rewrite Hs, previous_spot_eq. reflexivity.
    + rewrite Hn. eapply spot_lt_trans; [apply spot_lt_sleft; lia|exact nx_lt].
  - apply ilead_held; [exact Ht|unfold prev_ok; rewrite Hb; reflexivity].
Qed.

Lemma stepped_here : stepped W CU cur next c.
Proof. left. exists rest. split; [exact Hcur|split; [reflexivity|split; [exact Hs|exact Hn]]]. Qed.

Lemma iclosed_ok : forall allow txt o,
  oinv W o (nonempty_str txt) (sleft 1 cur) -> byte_at W (sleft 1 cur) = Some rbrack ->
  st_inv W next (istep_at allow c (IClosed txt o)).
Proof.
  intros allow txt o Ho Hb.
  assert (Ht : oinv W o true cur)
    by (eapply oinv_strict; [|exact Ho]; apply spot_lt_sleft; lia).
  cbn [istep_at].
  destruct (Ascii.eqb c lparen || Ascii.eqb c lbrack || (Ascii.eqb c lbrace && allow))%bool
    eqn:Econd;
    [|tred; apply ilead_held; [exact Ht|unfold prev_ok; rewrite Hb; reflexivity]].
  destruct (bclose (flush_text_to_at (previous_spot cursor_start) (tval txt) o))
    as [[[[kids image] open] o']|] eqn:Eb;
    [|tred; apply ilead_held; [exact Ht|unfold prev_ok; rewrite Hb; reflexivity]].
  rewrite Hs, previous_spot_eq in Eb. tred.
  destruct (bclose_ok W _ (sleft 1 cur) kids image open o'
              (flush_text_to_at_ok W CU (sleft 1 cur) txt o _ Ho) Eb) as (K & A & B & C).
  assert (Hlt : spot_lt (span_stop open) next).
  { eapply spot_le_lt_trans; [exact C|].
    eapply spot_lt_trans; [apply spot_lt_sleft; lia|exact nx_lt]. }
  assert (Hh : held W o' false next)
    by (eapply held_intro; [eapply spot_lt_trans; [exact B|exact Hlt]|exact A]).
  destruct (Ascii.eqb c lparen) eqn:E1.
  - apply Ascii.eqb_eq in E1. cbn [st_inv]. split; [exact K|split; [exact Hh|]].
    unfold idest_open.
    assert (Hd : oinv W (dpush image open o') true next).
    { eapply oinv_strict; [exact Hlt|]. apply frame_push_ok; [exact I|exact A|exact B]. }
    pose proof (bflat_ok W CU kids tnil (dpush image open o') next K Hd) as Hf.
    destruct (bflat kids tnil (dpush image open o')) as [t o''].
    cbn [st_inv orb]. split; [apply oinv_any, Hf|split; [|discriminate]].
    rewrite <- E1. exact nx_prev.
  - destruct (Ascii.eqb c lbrack) eqn:E2.
    + cbn [st_inv]. split; [exact K|exact Hh].
    + cbn [orb] in Econd. apply andb_true_iff in Econd as [E3 _]. apply Ascii.eqb_eq in E3.
      cbn [st_inv]. split; [exact K|split; [exact Hh|split; [|reflexivity]]].
      rewrite <- E3. exact nx_prev.
Qed.

Lemma eqb_rewrite : forall x, Ascii.eqb c x = true -> prev_ok W (Some x) next.
Proof. intros x E. apply Ascii.eqb_eq in E. rewrite <- E. exact nx_prev. Qed.

Lemma inote_ok : forall esc image label open o,
  held W o false cur -> st_inv W next (inote_step c esc image label open o).
Proof.
  intros esc image label open o Ho. pose proof (held_oinv _ _ _ _ Ho) as Ht.
  pose proof (held_step _ _ false false _ _ Ho nx_lt) as Hh.
  unfold inote_step.
  destruct esc; [exact Hh|]. destruct (is_bslash c); [exact Hh|].
  destruct (Ascii.eqb c rbrack) eqn:E; [|exact Hh].
  cbn [st_inv orb]. split; [|split; [apply eqb_rewrite, E|discriminate]].
  apply oinv_any, oemit_ok; [apply dn_imk_leaf; reflexivity|].
  apply ospan_bang_ok. eapply oinv_strict; [exact nx_lt|exact Ht].
Qed.

Lemma iwiki_ok : forall esc rb image region open o,
  held W o false cur -> st_inv W next (iwiki_step c esc rb image region open o).
Proof.
  intros esc rb image region open o Ho. pose proof (held_oinv _ _ _ _ Ho) as Ht.
  pose proof (held_step _ _ false false _ _ Ho nx_lt) as Hh.
  assert (Htn : oinv W o true next) by (eapply oinv_strict; [exact nx_lt|exact Ht]).
  unfold iwiki_step.
  destruct esc; [exact Hh|].
  destruct (rb && Ascii.eqb c rbrack)%bool eqn:E.
  - apply andb_true_iff in E as [_ E]. unfold iwiki_close. tred.
    destruct (wiki_split region) as [[|x t] al].
    + pose proof (bwiki_lit_ok W false true image region o next Htn) as H.
      destruct (bwiki_lit false true image region o) as [t' o']. cbn [st_inv orb].
      split; [apply oinv_any, H|split; [apply eqb_rewrite, E|discriminate]].
    + cbn [st_inv orb]. split; [|split; [apply eqb_rewrite, E|discriminate]].
      apply oinv_any, oemit_ok; [apply dn_imk_leaf; reflexivity|exact Htn].
  - destruct (is_bslash c); [exact Hh|]. destruct (Ascii.eqb c rbrack); exact Hh.
Qed.

Lemma iauto_ok : forall src txt o,
  held W o (nonempty_str txt) cur -> ends_at W (String lt src) cur ->
  st_inv W next (iauto_step c src txt o).
Proof.
  intros src txt o Ho He. pose proof (held_oinv _ _ _ _ Ho) as Ht.
  unfold iauto_step. tred.
  destruct (Ascii.eqb c gt && auto_body_ok src && auto_kind_ok src)%bool eqn:E.
  - apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E _].
    cbn [st_inv orb]. split; [|split; [apply eqb_rewrite, E|discriminate]].
    apply oinv_any, oemit_ok; [apply dn_auto|].
    apply flush_text_to_at_touched. eapply oinv_strict; [exact nx_lt|exact Ht].
  - destruct (Ascii.eqb c gt || is_ws c || Ascii.eqb c lt)%bool.
    + apply ilead_held; [exact Ht|apply prev_blit; [exact He|discriminate]].
    + cbn [st_inv]. tred. split; [eapply held_step; [exact Ho|exact nx_lt]|].
      change (String lt (src ++ one c)) with ((String lt src) ++ one c)%string.
      eapply ends_at_snoc; [exact He|exact Hcur].
Qed.

Lemma isymbol_ok : forall alias txt o sh',
  held W o (nonempty_str txt) cur -> st_inv W next sh' ->
  st_inv W next (isymbol_step c alias txt o sh').
Proof.
  intros alias txt o sh' Ho Hsh. pose proof (held_oinv _ _ _ _ Ho) as Ht.
  unfold isymbol_step. tred.
  destruct (symbol_char c).
  - cbn [st_inv]. split; [eapply held_step; [exact Ho|exact nx_lt]|exact Hsh].
  - destruct (Ascii.eqb c ":"%char && nonempty_str alias)%bool; [|exact Hsh].
    cbn [st_inv orb]. split; [|split; [exact nx_prev|discriminate]].
    apply oinv_any, oemit_ok; [apply dn_imk_leaf; reflexivity|].
    apply flush_text_to_at_touched. eapply oinv_strict; [exact nx_lt|exact Ht].
Qed.

Lemma iraw_ok : forall allow spec txt o,
  ends_at W (String lbrace spec) cur ->
  held W o false (sleft (String.length (String lbrace spec)) cur) ->
  st_inv W next (iraw_step_at allow c spec txt o).
Proof.
  intros allow spec txt o He Ho.
  pose proof (held_oinv _ _ _ _ Ho) as Ht0.
  assert (Ht : oinv W o true cur) by (eapply oinv_mono; [apply spot_le_sleft|exact Ht0]).
  assert (Hv : forall x, oinv W (oemit (imk (text_start o) x (Verbatim txt)) o) true
                           (sleft (String.length (String lbrace spec)) cur))
    by (intros x; apply oemit_ok; [apply dn_imk_leaf; reflexivity|exact Ht0]).
  assert (Hv' : forall x, oinv W (oemit (imk (text_start o) x (Verbatim txt)) o) true cur)
    by (intros x; eapply oinv_mono; [apply spot_le_sleft|apply Hv]).
  assert (Hp : prev_ok W (InlineScan.blit_prev (String lbrace spec)) cur)
    by (apply prev_blit; [exact He|discriminate]).
  unfold iraw_step_at. tred.
  destruct (Ascii.eqb c rbrace && raw_spec_ok spec)%bool eqn:E.
  - apply andb_true_iff in E as [E _].
    destruct raw_inline_enabled.
    + cbn [st_inv orb]. split; [|split; [apply eqb_rewrite, E|discriminate]].
      apply oinv_any, oemit_ok; [apply dn_imk_leaf; reflexivity|].
      eapply oinv_strict; [exact nx_lt|exact Ht].
    + apply ilead_held; [apply Hv'|exact Hp].
  - destruct (if nonempty_str spec then (Ascii.eqb c rbrace || raw_stop c)%bool
              else negb (Ascii.eqb c eqchar)).
    + destruct (nonempty_str spec) eqn:Ens.
      * apply ilead_held; [apply Hv'|exact Hp].
      * destruct spec as [|x sp]; [|discriminate].
        apply (ibrace_ok W CU cur c rest); try assumption.
        -- cbn [nonempty_str]. apply oinv_any. apply Hv.
        -- destruct He as [r Hr]. cbn [String.length one] in Hr. unfold byte_at. rewrite Hr. reflexivity.
    + cbn [st_inv]. split.
      * change (String lbrace (spec ++ one c)) with ((String lbrace spec) ++ one c)%string.
        eapply ends_at_snoc; [exact He|exact Hcur].
      * replace (sleft (String.length (String lbrace (spec ++ one c))) next)
          with (sleft (String.length (String lbrace spec)) cur); [exact Ho|].
        cbn [String.length]. rewrite length_append. cbn [String.length one].
        unfold next. pose proof (cur_rem _ _ _ _ Hcur). destruct cur as [kk rr].
        unfold sleft, sright. cbn in *. f_equal. lia.
Qed.

Lemma idelim_step_ok : forall allow k extra txt before marked o,
  st_inv W cur (IDelim k extra txt before marked o) ->
  st_inv W next (istep_at allow c (IDelim k extra txt before marked o)).
Proof.
  intros allow k extra txt before marked o (Hw & He & Ho & Hb).
  assert (Ht : oinv W o true cur).
  { eapply oinv_strict; [|exact Ho]. apply spot_lt_sleft. rewrite delim_run_length. lia. }
  assert (Hlast : prev_ok W (Some (dchar k)) cur).
  { destruct (delim_run_last k extra marked) as [s' Hs']. rewrite Hs' in He.
    eapply prev_of_ends, He. }
  cbn [istep_at].
  destruct (Nat.ltb (S extra) (dwidth k)) eqn:Elt.
  - apply Nat.ltb_lt in Elt.
    destruct (Ascii.eqb c (dchar k)) eqn:Ec.
    + apply Ascii.eqb_eq in Ec. pose proof Hcur as Hc'. rewrite Ec in Hc'.
      assert (Hrun : ends_at W (delim_run k (S extra) marked) next)
        by (rewrite delim_run_snoc; eapply ends_at_snoc; [exact He|exact Hc']).
      assert (Hpos : sleft (String.length (delim_run k (S extra) marked)) next =
                     sleft (String.length (delim_run k extra marked)) cur).
      { rewrite !delim_run_length. unfold next. pose proof (cur_rem _ _ _ _ Hcur).
        destruct cur as [kk rr]. unfold sleft, sright. cbn in *. f_equal. lia. }
      destruct marked; [unfold idelim_marked|]; cbn [st_inv]; rewrite Hpos.
      * split; [lia|split; [exact Hrun|split; [exact Ho|discriminate]]].
      * split; [lia|split; [exact Hrun|split; [exact Ho|intros _; exact (Hb eq_refl)]]].
    + tred. apply ilead_held; [exact Ht|exact Hlast].
  - apply Nat.ltb_ge in Elt. assert (Hfull : S extra = dwidth k) by lia.
    rewrite (delim_run_full _ _ _ Hfull) in He, Ho, Hb.
    destruct marked.
    + apply (ilead_ok W CU cur c rest); try assumption.
      apply (oopen_marked_ok W CU cur); assumption.
    + assert (Htok : ends_at W (dtoken k) cur) by exact He.
      assert (Hts : sleft (String.length (otok k false)) cur = sleft (dwidth k) cur)
        by (unfold otok; cbn [append]; rewrite dtoken_length; reflexivity).
      rewrite Hts in Ho, Hb.
      destruct (idelim_resolve_ok W CU cur Hs k Htok txt before (Ascii.eqb c rbrace)
                  (Some c) o Ho (fun _ => Hb eq_refl)
                  (fun E => eq_trans (byte_at_sfx _ _ _ _ Hcur)
                              (f_equal Some (proj1 (Ascii.eqb_eq _ _) E)))
                  (fun _ => Hn) (byte_at_sfx _ _ _ _ Hcur))
        as (txt' & prev' & o' & Eq & A & B).
      rewrite Eq. destruct (Ascii.eqb c rbrace).
      * cbn [st_inv orb]. split; [exact A|split; [exact B|discriminate]].
      * apply (ilead_ok W CU cur c rest); assumption.
Qed.

Lemma istep_ok : forall st allow,
  st_inv W cur st -> st_inv W next (istep_at allow c st).
Proof.
  induction st; intros allow H.
  - (* IText *) destruct H as (Ho & Hp & He). destruct esc.
    + cbn [istep_at]. destruct (is_ws c).
      * cbn [st_inv]. tred. split; [eapply held_intro; [exact nx_lt|apply oinv_any, Ho]|].
        split; [exact (ends_here _ _ _ _ Hcur)|discriminate].
      * apply text_next, Ho.
    + cbn [istep_at]. apply (ilead_ok W CU cur c rest); assumption.
  - (* IEscWs *) destruct H as (Ho & He & Hne). cbn [istep_at].
    destruct (is_ws c).
    + cbn [st_inv]. tred. split; [eapply held_step; [exact Ho|exact nx_lt]|].
      split; [eapply ends_at_snoc; [exact He|exact Hcur]|destruct ws; discriminate].
    + pose proof (iescws_ok ws txt prev o Ho He Hne) as Hr.
      destruct (iescws_resolve ws txt prev o) as [[t' p'] o'].
      destruct Hr as [A B]. apply (ilead_ok W CU cur c rest); assumption.
  - (* IBrace *) destruct H as (Ho & Hb). cbn [istep_at].
    apply (ibrace_ok W CU cur c rest); assumption.
  - (* IDelim *) apply idelim_step_ok, H.
  - (* IOpen *) destruct H as (Ho & Hn1). cbn [istep_at].
    destruct (is_tick c); cbn [st_inv].
    + split; [eapply held_step; [exact Ho|exact nx_lt]|lia].
    + split; [eapply held_step; [exact Ho|exact nx_lt]|split; [exact Hn1|lia]].
  - (* IVerb *) destruct H as (Ho & Hn1 & Hr). cbn [istep_at].
    destruct (is_tick c) eqn:Et.
    + cbn [st_inv]. split; [eapply held_step; [exact Ho|exact nx_lt]|split; [exact Hn1|]].
      intros _. unfold is_tick in Et. apply Ascii.eqb_eq in Et. rewrite <- Et. exact (byte_back _ _ _ _ Hcur).
    + destruct (Nat.eqb run n) eqn:Er.
      * apply Nat.eqb_eq in Er.
        assert (Hraw : Ascii.eqb c lbrace = true ->
                       st_inv W next (IRaw EmptyString (trim_verb txt) o)).
        { intros Eb. apply Ascii.eqb_eq in Eb.
          cbn [st_inv]. tred. split.
          - rewrite <- Eb. exact (ends_here _ _ _ _ Hcur).
          - cbn [String.length]. rewrite nx_back. exact Ho. }
        assert (Hlead : forall x, dkind x = None -> children x = [] ->
                  st_inv W next (ilead c EmptyString (Some tick)
                    (oemit (imk (text_start o) cur x) o))).
        { intros x Hk Hc. apply ilead_held.
          - apply oemit_ok; [apply dn_imk_plain; [exact Hk|rewrite Hc; constructor]|].
            exact (held_oinv _ _ _ _ Ho).
          - unfold prev_ok. rewrite (Hr ltac:(lia)). reflexivity. }
        (* math closed by the `$` just read: text follows it *)
        assert (Hmath : forall start x o',
                  oinv W o' true cur -> dkind x = None -> children x = [] ->
                  Ascii.eqb c dollar = true ->
                  st_inv W next (IText false EmptyString (Some dollar)
                    (oemit (imk start next x) o'))).
        { intros start x o' Ho' Hk Hc Ed. apply Ascii.eqb_eq in Ed.
          cbn [st_inv orb nonempty_str].
          split; [|split; [rewrite <- Ed; exact nx_prev|discriminate]].
          apply oinv_any, oemit_ok; [apply dn_imk_plain; [exact Hk|rewrite Hc; constructor]|].
          eapply oinv_strict; [exact nx_lt|exact Ho']. }
        rewrite Hs, Hn.
        destruct vk as [|[]|prefix]; cbn [vkind_verb vnode tval tnil];
          rewrite ?andb_true_r, ?andb_false_r.
        all: try (destruct (Ascii.eqb c lbrace) eqn:Eb;
                  [apply Hraw; reflexivity|apply Hlead; reflexivity]).
        all: try (apply Hlead; reflexivity).
        -- destruct (Ascii.eqb c dollar && _)%bool eqn:Ed.
           ++ apply andb_true_iff in Ed as [Ed _].
              apply Hmath; [exact (held_oinv _ _ _ _ Ho)|reflexivity|reflexivity|exact Ed].
           ++ apply Hlead; reflexivity.
        -- destruct (Ascii.eqb c dollar) eqn:Ed.
           ++ pose proof (opop_str_ok W o cur (held_oinv _ _ _ _ Ho)) as Hp.
              destruct (opop_str o) as [pre o']. cbn [snd] in Hp.
              apply Hmath; [|reflexivity|reflexivity|reflexivity].
              apply flush_text_to_at_touched, Hp.
           ++ destruct (Ascii.eqb c lbrace) eqn:Eb;
                [apply Hraw; reflexivity|apply Hlead; reflexivity].
      * cbn [st_inv]. split; [eapply held_step; [exact Ho|exact nx_lt]|split; [exact Hn1|lia]].
  - (* IDollar *) destruct H as (Ho & Hb). cbn [istep_at]. apply idollar_ok; assumption.
  - (* IDollarMath *) destruct H as (Ho & Hsh). cbn [istep_at].
    pose proof (IHst allow Hsh) as Hsh'.
    pose proof (held_step W o _ (nonempty_str txt) cur next Ho nx_lt) as Ho'.
    destruct escaped; [cbn [st_inv]; split; assumption|].
    destruct (Ascii.eqb c dollar) eqn:Ed; cbn [st_inv]; [|split; assumption].
    apply Ascii.eqb_eq in Ed. split; [exact Ho'|split; [|exact Hsh']].
    rewrite nx_back, <- Ed. exact (byte_at_sfx _ _ _ _ Hcur).
  - (* IDollarMathClose *) destruct H as (Ho & Hb & Hsh). cbn [istep_at].
    pose proof (IHst allow Hsh) as Hsh'.
    pose proof (held_step W o _ (nonempty_str txt) cur next Ho nx_lt) as Ho'.
    assert (Hd : Ascii.eqb c dollar = true -> byte_at W (sleft 1 next) = Some dollar).
    { intros Ed. apply Ascii.eqb_eq in Ed. rewrite nx_back, <- Ed.
      exact (byte_at_sfx _ _ _ _ Hcur). }
    (* the candidate closes: the math node, then the byte read as usual *)
    assert (Hclose : forall start x, dkind x = None -> children x = [] ->
              st_inv W next (ilead c EmptyString (Some dollar)
                (oemit (imk start cursor_start x) (flush_text_to_at start txt o)))).
    { intros start x Hk Hc. apply ilead_held; [|unfold prev_ok; rewrite Hb; reflexivity].
      apply oemit_ok; [apply dn_imk_plain; [exact Hk|rewrite Hc; constructor]|].
      apply flush_text_to_at_touched, (held_oinv _ _ _ _ Ho). }
    destruct two.
    + destruct last as [p|].
      * destruct (Ascii.eqb p nl_char);
          (destruct (Ascii.eqb c dollar) eqn:Ed; cbn [st_inv];
           [split; [exact Ho'|split; [apply Hd; first [exact Ed|reflexivity]|exact Hsh']]|split; assumption]).
      * destruct (Ascii.eqb c dollar) eqn:Ed.
        -- cbn [st_inv]. split; [exact Ho'|split; [apply Hd; first [exact Ed|reflexivity]|exact Hsh']].
        -- apply Hclose; reflexivity.
    + destruct (_ && _)%bool; [apply Hclose; reflexivity|exact Hsh'].
  - (* IPeriod *) destruct H as (Ho & Hb). cbn [istep_at]. apply iperiod_ok; assumption.
  - (* IDash *) destruct H as (He & Hn1 & Ho). cbn [istep_at]. apply idash_ok; assumption.
  - (* IBang *) destruct H as (Ho & Hb). cbn [istep_at]. apply ibang_ok; assumption.
  - (* IClosed *) destruct H as (Ho & Hb). apply iclosed_ok; assumption.
  - (* ISpan *) destruct H as (Hk & Ho & Hp & Hd). cbn [istep_at].
    eapply ispan_feed_ok; [exact stepped_here|exact Hk|exact Ho|exact Hp|exact Hd].
  - (* IAttr *) destruct H as (Ho & Hd & Hsh). cbn [istep_at].
    destruct (ap_failed (astep p c)); [apply IHst, Hsh|].
    eapply iattr_feed_ok; [apply spot_lt_le, nx_lt|intros _; exact nx_prev|exact Ho|exact Hd|].
    apply IHst, Hsh.
  - (* IReference *) destruct H as (Hk & Ho). cbn [istep_at].
    destruct (Ascii.eqb c rbrack) eqn:E.
    + cbn [st_inv orb]. split; [|split; [apply eqb_rewrite, E|discriminate]].
      apply oinv_any, oemit_ok; [apply dn_bnode, Hk|].
      eapply oinv_strict; [exact nx_lt|exact (held_oinv _ _ _ _ Ho)].
    + cbn [st_inv]. split; [exact Hk|eapply held_step; [exact Ho|exact nx_lt]].
  - (* INote *) cbn [istep_at]. apply inote_ok, H.
  - (* IWiki *) cbn [istep_at]. apply iwiki_ok, H.
  - (* IDest *) destruct H as (Hk & Ho & Hsh).
    assert (Hd : forall esc' depth' dst',
               st_inv W next (IDest kids image open esc' depth' dst' (istep_at allow c st) o))
      by (intros; cbn [st_inv]; split; [exact Hk|split;
            [eapply held_step; [exact Ho|exact nx_lt]|apply IHst, Hsh]]).
    destruct esc; cbn [istep_at]; [apply Hd|].
    destruct (is_bslash c); [apply Hd|].
    destruct (Ascii.eqb c lparen); [apply Hd|].
    destruct (Ascii.eqb c rparen) eqn:E; [|apply Hd].
    destruct depth as [|d]; [|apply Hd].
    cbn [st_inv orb]. split; [|split; [apply eqb_rewrite, E|discriminate]].
    apply oinv_any, oemit_ok; [apply dn_bnode, Hk|].
    eapply oinv_strict; [exact nx_lt|exact (held_oinv _ _ _ _ Ho)].
  - (* IAuto *) destruct H as (Ho & He). cbn [istep_at]. apply iauto_ok; assumption.
  - (* ISymbol *) destruct H as (Ho & Hsh). cbn [istep_at].
    apply isymbol_ok; [exact Ho|apply IHst, Hsh].
  - (* IRaw *) destruct H as (He & Ho). cbn [istep_at]. apply iraw_ok; assumption.
Qed.

End Step.

(*
Line ends
---------

At the end of a line nothing follows, so every state waiting on a next
byte settles (`iresolve`).  A break then moves the scan to the start of
the next window, where nothing lies to the left.
*)

Lemma iresolve_ok : forall W (CU : InlineCursor) cur st,
  cursor_start = cur -> st_inv W cur st -> st_inv W cur (iresolve st).
Proof.
  intros W CU cur st Hs H. destruct st; cbn [iresolve]; try exact H; cbn [st_inv orb]; tred.
  - (* IBrace *) destruct H as (Ho & Hb).
    split; [|split; [unfold prev_ok; rewrite Hb; reflexivity|discriminate]].
    apply oinv_any. eapply oinv_strict; [|exact Ho]. apply spot_lt_sleft; lia.
  - (* IDelim *) destruct H as (Hw & He & Ho & Hb).
    assert (Hlast : prev_ok W (Some (dchar k)) cur).
    { destruct (delim_run_last k extra marked) as [s' Hs']. rewrite Hs' in He.
      eapply prev_of_ends, He. }
    destruct (Nat.ltb (S extra) (dwidth k)) eqn:Elt.
    + cbn [st_inv orb]. split; [|split; [exact Hlast|discriminate]].
      apply oinv_any. eapply oinv_strict; [|exact Ho].
      apply spot_lt_sleft. rewrite delim_run_length. lia.
    + apply Nat.ltb_ge in Elt. assert (Hfull : S extra = dwidth k) by lia.
      rewrite (delim_run_full _ _ _ Hfull) in He, Ho, Hb.
      destruct marked.
      * unfold idelim_open_marked. cbn [st_inv orb].
        split; [apply (oopen_marked_ok W CU cur); assumption|split; [exact Hlast|discriminate]].
      * assert (Hts : sleft (String.length (otok k false)) cur = sleft (dwidth k) cur)
          by (unfold otok; cbn [append]; rewrite dtoken_length; reflexivity).
        rewrite Hts in Ho, Hb.
        destruct (idelim_resolve_ok W CU cur Hs k He txt before false None o Ho
                    (fun _ => Hb eq_refl) ltac:(discriminate) ltac:(discriminate) I)
          as (txt' & prev' & o' & Eq & A & B).
        rewrite Eq. cbn [st_inv orb]. split; [exact A|split; [exact B|discriminate]].
  - (* IDollar *) destruct H as (Ho & Hb).
    split; [|split; [unfold prev_ok; rewrite Hb; reflexivity|discriminate]].
    apply oinv_any; exact (held_oinv _ _ _ _ Ho).
  - (* IPeriod *) destruct H as (Ho & Hb).
    split; [|split; [unfold prev_ok; rewrite Hb; reflexivity|discriminate]].
    apply oinv_any; exact (held_oinv _ _ _ _ Ho).
  - (* IDash *) destruct H as (He & Hn1 & Ho).
    split; [|split; [|discriminate]].
    + apply oinv_any. eapply oinv_strict; [|exact Ho]. apply spot_lt_sleft; lia.
    + destruct n as [|n]; [lia|]. rewrite chars_snoc in He. eapply prev_of_ends, He.
  - (* IBang *) destruct H as (Ho & Hb).
    split; [|split; [unfold prev_ok; rewrite Hb; reflexivity|discriminate]].
    apply oinv_any. eapply oinv_strict; [|exact Ho]. apply spot_lt_sleft; lia.
  - (* IClosed *) destruct H as (Ho & Hb).
    split; [|split; [unfold prev_ok; rewrite Hb; reflexivity|discriminate]].
    apply oinv_any. eapply oinv_strict; [|exact Ho]. apply spot_lt_sleft; lia.
Qed.

(* A state with no byte owed: what `iresolve` leaves, and not a state
   carrying a second reading. *)
Definition settled (st : iscan) : Prop :=
  match st with
  | IBrace _ _ _ | IDollar _ _ _ _ | IPeriod _ _ _ _ | IDash _ _ _ _
  | IBang _ _ _ | IDelim _ _ _ _ _ _ | IClosed _ _
  | IDollarMath _ _ _ _ _ _ _ | IDollarMathClose _ _ _ _ _ _
  | IAttr _ _ _ _ _ _ | IDest _ _ _ _ _ _ _ _ | ISymbol _ _ _ _ => False
  | _ => True
  end.

Lemma idelim_resolve_text : forall (CU : InlineCursor) k txt before marker next o,
  exists t p o', idelim_resolve k txt before marker next o = IText false t p o'.
Proof.
  intros CU k txt before marker next o. unfold idelim_resolve, idelim_done.
  repeat match goal with
         | |- context [match ?x with Some _ => _ | None => _ end] => destruct x
         | |- context [if ?b then _ else _] => destruct b
         end; eauto.
Qed.

Lemma iresolve_settled : forall (CU : InlineCursor) st,
  is_compound st = false -> settled (iresolve st).
Proof.
  intros CU st Hc.
  destruct st; cbn [is_compound] in Hc; try discriminate; cbn [iresolve settled]; try exact I.
  destruct (Nat.ltb (S extra) (dwidth k)); [exact I|].
  destruct marked; [exact I|].
  destruct (idelim_resolve_text CU k txt before false None o) as (t & p & o' & ->). exact I.
Qed.

Section Break.
Local Set Default Proof Using "All".
Variable W : list window.
Context (CU : InlineCursor).
Variables cur next : spot.
Hypothesis Hs : cursor_start = cur.
Hypothesis Hlt : spot_lt cur next.
Hypothesis Hfresh : byte_at W (sleft 1 next) = None.

Lemma brk_stepped : stepped W CU cur next nl_char.
Proof. right. split; [reflexivity|split; assumption]. Qed.

Lemma brk_prev_none : prev_ok W None next.
Proof. unfold prev_ok. rewrite Hfresh. left. reflexivity. Qed.

(* The soft break and what it settles: text flushed, a break emitted. *)
Lemma brk_text : forall o,
  oinv W o true next ->
  st_inv W next (IText false EmptyString None (oword_reset o)).
Proof.
  intros o Ho. cbn [st_inv orb nonempty_str].
  split; [apply oword_reset_ok, oinv_any, Ho|split; [exact brk_prev_none|discriminate]].
Qed.

Lemma brk_soft : forall t o,
  oinv W o true next ->
  oinv W (oemit (imk_here SoftBreak) (flush_text_at t o)) true next.
Proof.
  intros t o Ho. apply oemit_ok; [apply dn_imk_leaf; reflexivity|].
  apply flush_text_at_touched, Ho.
Qed.

Lemma brk_strict : forall o t, oinv W o t cur -> oinv W o true next.
Proof. intros o t H. eapply oinv_strict; [exact Hlt|exact H]. Qed.

Lemma brk_held : forall o t t', held W o t cur -> oinv W o t' next.
Proof. intros o t t' H. apply oinv_any. eapply oinv_mono; [apply spot_lt_le, Hlt|exact (held_oinv _ _ _ _ H)]. Qed.

Lemma ibreak_flat_ok : forall st,
  settled st -> st_inv W cur st -> st_inv W next (ibreak_flat st).
Proof.
  intros st Hset H. destruct st; cbn [settled] in Hset; try contradiction;
    cbn [ibreak_flat]; tred.
  - (* IText *) destruct H as (Ho & Hp & He). destruct esc.
    + apply brk_text, iesc_hard_ok, (brk_strict _ _ Ho).
    + apply brk_text, brk_soft, (brk_strict _ _ Ho).
  - (* IEscWs *) destruct H as (Ho & He & Hne).
    apply brk_text, iesc_hard_ok, (brk_held _ _ _ Ho).
  - (* IOpen *) destruct H as (Ho & Hn1). cbn [st_inv].
    split; [eapply held_step; [exact Ho|exact Hlt]|split; [exact Hn1|lia]].
  - (* IVerb *) destruct H as (Ho & Hn1 & Hr).
    destruct (Nat.eqb run n).
    + apply brk_text, oemit_ok; [apply dn_imk_leaf; reflexivity|].
      apply oemit_ok; [apply dn_vnode|exact (brk_held _ _ _ Ho)].
    + cbn [st_inv]. split; [eapply held_step; [exact Ho|exact Hlt]|split; [exact Hn1|lia]].
  - (* ISpan *) destruct H as (Hk & Ho & Hp & Hd).
    eapply ispan_feed_ok; [exact brk_stepped|exact Hk|exact Ho|exact Hp|exact Hd].
  - (* IReference *) destruct H as (Hk & Ho). cbn [st_inv].
    split; [exact Hk|eapply held_step; [exact Ho|exact Hlt]].
  - (* INote *) cbn [st_inv]. eapply held_step; [exact H|exact Hlt].
  - (* IWiki *)
    pose proof (bwiki_lit_ok W esc rb image region o next (brk_held _ _ _ H)) as Hw.
    destruct (bwiki_lit esc rb image region o) as [t o']. apply brk_text, brk_soft, Hw.
  - (* IAuto *) destruct H as (Ho & He). apply brk_text, brk_soft, (brk_held _ _ _ Ho).
  - (* IRaw *) destruct H as (He & Ho).
    apply brk_text, brk_soft, oemit_ok; [apply dn_imk_leaf; reflexivity|].
    apply oinv_any. eapply oinv_mono; [|exact (held_oinv _ _ _ _ Ho)].
    eapply spot_le_trans; [apply spot_le_sleft|apply spot_lt_le, Hlt].
Qed.

Lemma ibreak_at_ok : forall st allow,
  st_inv W cur st -> st_inv W next (ibreak_at allow st).
Proof.
  induction st; intros allow H; cbn [ibreak_at];
    try (apply ibreak_flat_ok;
         [apply iresolve_settled; reflexivity|apply (iresolve_ok W CU cur); assumption]).
  - (* IDollar *)
    destruct (two && dollar_math_enabled && _)%bool eqn:Ec.
    + destruct H as (Ho & Hb). cbn [st_inv].
      split; [eapply held_step; [exact Ho|exact Hlt]|].
      apply ibreak_flat_ok; [exact I|]. cbn [st_inv orb].
      split; [apply oinv_any, (held_oinv _ _ _ _ Ho)|].
      split; [unfold prev_ok; rewrite Hb; reflexivity|discriminate].
    + apply ibreak_flat_ok;
        [apply iresolve_settled; exact Ec|apply (iresolve_ok W CU cur); assumption].
  - (* IDollarMath *) destruct H as (Ho & Hsh). cbn [st_inv].
    split; [eapply held_step; [exact Ho|exact Hlt]|apply IHst, Hsh].
  - (* IDollarMathClose *) destruct H as (Ho & Hb & Hsh).
    (* the candidate closes at the line's end *)
    assert (Hclose : forall start x, dkind x = None -> children x = [] ->
              st_inv W next (ibreak_flat (IText false EmptyString (Some dollar)
                (oemit (imk start cursor_start x) (flush_text_to_at start txt o))))).
    { intros start x Hk Hc. apply ibreak_flat_ok; [exact I|]. cbn [st_inv orb nonempty_str].
      split; [|split; [unfold prev_ok; rewrite Hb; reflexivity|discriminate]].
      apply oinv_any, oemit_ok; [apply dn_imk_plain; [exact Hk|rewrite Hc; constructor]|].
      apply flush_text_to_at_touched, (held_oinv _ _ _ _ Ho). }
    destruct two.
    + destruct last as [p|]; [|apply Hclose; reflexivity].
      cbn [st_inv]. split; [eapply held_step; [exact Ho|exact Hlt]|apply IHst, Hsh].
    + destruct (match last with Some p => _ | None => false end);
        [apply Hclose; reflexivity|apply IHst, Hsh].
  - (* IAttr *) destruct H as (Ho & Hd & Hsh).
    eapply iattr_feed_ok; [apply spot_lt_le, Hlt|discriminate|exact Ho|exact Hd|].
    apply IHst, Hsh.
  - (* IDest *) destruct H as (Hk & Ho & Hsh). cbn [st_inv].
    split; [exact Hk|split; [eapply held_step; [exact Ho|exact Hlt]|apply IHst, Hsh]].
  - (* ISymbol *) destruct H as (Ho & Hsh). apply IHst, Hsh.
Qed.

End Break.

(*
The end of the paragraph
------------------------

What is still open becomes text, so only the nodes and frames matter
here, not the order.
*)

Definition held_any (W : list window) (o : ostate) : Prop :=
  Forall (item_ok W) (os_out o) /\ Forall (frame_ok W) (os_stk o).

Lemma held_any_of : forall W o t h, oinv W o t h -> held_any W o.
Proof. intros W o t h (A & B & _). split; assumption. Qed.

(* A spot past everything the scan has read: every operation below that
   wants a touched state gets it there. *)
Definition far (cur : spot) : spot := Spot (S (spot_line cur)) 0.

Lemma far_lt : forall p cur, spot_le p cur -> spot_lt p (far cur).
Proof. intros [k r] [kc rc] H. unfold spot_le, spot_lt, far in *. cbn in *. lia. Qed.

Lemma held_far : forall W o t cur, held W o t cur -> oinv W o true (far cur).
Proof.
  intros W o t cur (h & Hh & H). eapply oinv_strict; [|exact H].
  apply far_lt, spot_lt_le, Hh.
Qed.

Lemma oinv_far : forall W o t h cur, spot_le h cur -> oinv W o t h -> oinv W o true (far cur).
Proof. intros W o t h cur Hle H. eapply oinv_strict; [apply far_lt, Hle|exact H]. Qed.

Lemma finish_flat_ok : forall W (CU : InlineCursor) cur st,
  settled st -> st_inv W cur st -> held_any W (ifinish_ostate_flat st).
Proof.
  intros W CU cur st Hset H.
  destruct st; cbn [settled] in Hset; try contradiction; cbn [ifinish_ostate_flat]; tred.
  - destruct H as (Ho & Hp & He). pose proof (oinv_far _ _ _ _ cur (spot_le_refl cur) Ho) as Hf.
    destruct esc.
    + eapply held_any_of, iesc_hard_ok, Hf.
    + eapply held_any_of, flush_text_at_touched, Hf.
  - destruct H as (Ho & He & Hne). eapply held_any_of, iesc_hard_ok; exact (held_far _ _ _ _ Ho).
  - destruct H as (Ho & Hn1). eapply held_any_of, oemit_ok; [apply dn_vnode|exact (held_far _ _ _ _ Ho)].
  - destruct H as (Ho & Hn1 & Hr). eapply held_any_of, oemit_ok; [apply dn_vnode|exact (held_far _ _ _ _ Ho)].
  - destruct H as (Hk & Ho & Hp & Hd).
    pose proof (bspan_lit_ok W CU kids image src o _ Hk (held_far _ _ _ _ Ho)) as Hb.
    destruct (bspan_lit kids image src o) as [t o']. eapply held_any_of, flush_text_at_touched, Hb.
  - destruct H as (Hk & Ho).
    pose proof (bref_lit_ok W CU kids image label o _ Hk (held_far _ _ _ _ Ho)) as Hb.
    destruct (bref_lit kids image label o) as [t o']. eapply held_any_of, flush_text_at_touched, Hb.
  - pose proof (bnote_lit_ok W CU esc image label o _ (held_far _ _ _ _ H)) as Hb.
    destruct (bnote_lit esc image label o) as [t o']. eapply held_any_of, flush_text_at_touched, Hb.
  - pose proof (bwiki_lit_ok W esc rb image region o _ (held_far _ _ _ _ H)) as Hb.
    destruct (bwiki_lit esc rb image region o) as [t o']. eapply held_any_of, flush_text_at_touched, Hb.
  - destruct H as (Ho & He). eapply held_any_of, flush_text_at_touched; exact (held_far _ _ _ _ Ho).
  - destruct H as (He & Ho). eapply held_any_of, flush_text_at_touched, oemit_ok;
      [apply dn_imk_leaf; reflexivity|].
    exact (held_far _ _ _ _ Ho).
Qed.

Lemma ifinish_ostate_ok : forall W (CU : InlineCursor) cur st,
  cursor_start = cur -> st_inv W cur st -> held_any W (ifinish_ostate st).
Proof.
  intros W CU cur st Hs. induction st; intros H; cbn [ifinish_ostate];
    try (eapply finish_flat_ok;
         [apply iresolve_settled; reflexivity|apply (iresolve_ok W CU cur); assumption]).
  - (* IDollar *)
    eapply finish_flat_ok; [exact I|apply (iresolve_ok W CU cur); assumption].
  - (* IDollarMath *) destruct H as (_ & Hsh). apply IHst, Hsh.
  - (* IDollarMathClose *) destruct H as (Ho & _ & Hsh).
    assert (Hclose : forall start x, dkind x = None -> children x = [] ->
              held_any W (oemit (imk start cursor_start x) (flush_text_to_at start txt o))).
    { intros start x Hk Hc. eapply held_any_of, oemit_ok;
        [apply dn_imk_plain; [exact Hk|rewrite Hc; constructor]|].
      apply flush_text_to_at_touched, (held_far _ _ _ _ Ho). }
    destruct two.
    + destruct last; [apply IHst, Hsh|apply Hclose; reflexivity].
    + destruct (match last with Some p => _ | None => false end);
        [apply Hclose; reflexivity|apply IHst, Hsh].
  - destruct H as (_ & _ & Hsh). apply IHst, Hsh.
  - destruct H as (_ & _ & Hsh). apply IHst, Hsh.
  - destruct H as (_ & Hsh). apply IHst, Hsh.
Qed.

Lemma oflatten_ok : forall W pend stk bottom,
  Forall (item_ok W) pend -> Forall (frame_ok W) stk -> Forall (item_ok W) bottom ->
  Forall (item_ok W) (oflatten pend stk bottom).
Proof.
  intros W pend stk. revert pend. induction stk as [|f stk IH]; intros pend bottom Hp Hs Hb.
  - apply oapp_ok; assumption.
  - inversion Hs as [|? ? Hf Hrest]; subst. cbn [oflatten]. apply IH; [|exact Hrest|exact Hb].
    apply oapp_ok; [apply oapp_ok; [exact Hp|exact (proj2 (proj2 Hf))]|].
    constructor; [apply fr_lit_ok|constructor].
Qed.

Lemma ofinish_ok : forall W o, held_any W o -> Forall (dn_node W) (ofinish o).
Proof.
  intros W o [A B]. unfold ofinish. rewrite oitems_of_spec.
  apply oresolve_ok, oflatten_ok; [constructor|exact B|exact A].
Qed.

Lemma ifinish_ok : forall W (CU : InlineCursor) cur st,
  cursor_start = cur -> st_inv W cur st -> Forall (dn_node W) (ifinish st).
Proof.
  intros W CU cur st Hs H. unfold ifinish, ifinish_rev.
  apply Forall_rev, ofinish_ok. eapply ifinish_ostate_ok; eassumption.
Qed.

(*
Driving the scan
================
*)

Lemma iscan_str_ok : forall W allow k origin s rem st,
  sfx W (Spot k rem) = Some s -> st_inv W (Spot k rem) st ->
  st_inv W (Spot k (rem - String.length s))
    (@InlineLocated.iscan_str_located T located_pos allow k origin rem s st).
Proof.
  intros W allow k origin s. induction s as [|c s IH]; intros rem st Hs Hst.
  - cbn. rewrite Nat.sub_0_r. exact Hst.
  - cbn [InlineLocated.iscan_str_located String.length].
    assert (Hr : sright 1 (Spot k rem) = Spot k (pred rem))
      by (unfold sright; cbn; f_equal; lia).
    replace (rem - S (String.length s)) with (pred rem - String.length s) by lia.
    apply IH.
    + rewrite <- Hr. exact (sfx_cons _ _ _ _ Hs).
    + rewrite <- Hr.
      apply (istep_ok W (InlineLocated.cursor_in k rem origin) (Spot k rem) c s);
        [reflexivity|exact (eq_sym Hr)|exact Hs|exact Hst].
Qed.

(* The windows of a paragraph's lines: each stored line whole, the last
   stripped of trailing whitespace, as the scan reads them. *)
Fixpoint para_windows (l : list (nat * string)) : list window :=
  match l with
  | [] => []
  | [(k, x)] => [(k, String.length x, strip_trailing_ws x)]
  | (k, x) :: rest => (k, String.length x, x) :: para_windows rest
  end.

Lemma strip_length : forall x, String.length (strip_trailing_ws x) <= String.length x.
Proof.
  intros x. destruct (strip_trailing_split x) as (w & _ & E).
  rewrite E at 2. rewrite length_append. lia.
Qed.

Lemma sfx_window : forall W k r w,
  wfind W k = Some (r, w) -> String.length w <= r ->
  sfx W (Spot k r) = Some w.
Proof.
  intros W k r w Hw Hl. unfold sfx. cbn [spot_line spot_rem]. rewrite Hw.
  replace (Nat.leb (String.length w) r) with true by (symmetry; apply Nat.leb_le; lia).
  rewrite Nat.leb_refl.
  replace (Nat.leb (r - String.length w) r) with true by (symmetry; apply Nat.leb_le; lia).
  rewrite Nat.sub_diag. reflexivity.
Qed.

(* Nothing of a window lies to the left of its start. *)
Lemma byte_before_window : forall W k r w,
  wfind W k = Some (r, w) -> byte_at W (sleft 1 (Spot k r)) = None.
Proof.
  intros W k r w Hw. unfold byte_at, sfx, sleft. cbn [spot_line spot_rem]. rewrite Hw.
  replace (Nat.leb (r + 1) r) with false by (symmetry; apply Nat.leb_gt; lia).
  rewrite andb_false_r. reflexivity.
Qed.

Lemma iscan_lines_ok : forall W l off origin st,
  l <> [] -> StronglySorted Nat.lt (map fst l) ->
  (forall k r w, In (k, r, w) (para_windows l) -> wfind W k = Some (r, w)) ->
  st_inv W (InlineLocated.lines_start l) st ->
  st_inv W (InlineLocated.lines_stop l)
    (@InlineLocated.iscan_lines_located T located_pos off origin l st).
Proof.
  intros W l. induction l as [|[k x] rest IH]; intros off origin st Hne Hsort Hw Hst;
    [contradiction|].
  destruct rest as [|[k' x'] rest'].
  - cbn [InlineLocated.iscan_lines_located InlineLocated.lines_stop].
    cbn [InlineLocated.lines_start] in Hst.
    apply (iscan_str_ok W _ k origin (strip_trailing_ws x) (String.length x) st); [|exact Hst].
    apply sfx_window; [apply (Hw k); left; reflexivity|apply strip_length].
  - cbn [InlineLocated.iscan_lines_located].
    change (InlineLocated.lines_stop ((k, x) :: (k', x') :: rest'))
      with (InlineLocated.lines_stop ((k', x') :: rest')).
    inversion Hsort as [|? ? Hsort' Hhead]; subst.
    inversion Hhead as [|? ? Hkk' _]; subst.
    assert (Hw' : forall j r w, In (j, r, w) (para_windows ((k', x') :: rest')) ->
                    wfind W j = Some (r, w))
      by (intros j r w Hin; apply Hw; right; exact Hin).
    assert (Hk' : wfind W k' = Some (String.length x',
                    match rest' with [] => strip_trailing_ws x' | _ => x' end)).
    { apply Hw'. destruct rest' as [|y rest'']; left; reflexivity. }
    apply IH; [discriminate|exact Hsort'|exact Hw'|].
    cbn [InlineLocated.lines_start].
    apply (ibreak_at_ok W _ (Spot k 0)).
    + reflexivity.
    + left. cbn. exact Hkk'.
    + eapply byte_before_window, Hk'.
    + replace (Spot k 0) with (Spot k (String.length x - String.length x))
        by (f_equal; lia).
      apply iscan_str_ok; [|exact Hst].
      apply sfx_window; [apply (Hw k); left; reflexivity|lia].
Qed.

Lemma para_windows_keys : forall l,
  map (fun w => fst (fst w)) (para_windows l) = map fst l.
Proof.
  induction l as [|[k x] rest IH]; [reflexivity|].
  destruct rest as [|y rest']; [reflexivity|].
  change (para_windows ((k, x) :: y :: rest'))
    with ((k, String.length x, x) :: para_windows (y :: rest')).
  cbn [map]. rewrite IH. reflexivity.
Qed.

Lemma wfind_in : forall W k r w,
  StronglySorted Nat.lt (map (fun w => fst (fst w)) W) -> In (k, r, w) W ->
  wfind W k = Some (r, w).
Proof.
  induction W as [|[[j r0] w0] W IH]; intros k r w Hs Hin; [destruct Hin|].
  inversion Hs as [|? ? Hs' Hh]; subst. cbn [wfind].
  destruct Hin as [E|Hin].
  - injection E as -> -> ->. rewrite Nat.eqb_refl. reflexivity.
  - destruct (Nat.eqb j k) eqn:E.
    + apply Nat.eqb_eq in E. subst j. exfalso.
      rewrite Forall_forall in Hh.
      specialize (Hh k (in_map (fun w => fst (fst w)) W (k, r, w) Hin)). lia.
    + apply IH; assumption.
Qed.

Lemma st_inv_start : forall W p,
  byte_at W (sleft 1 p) = None -> st_inv W p istart.
Proof.
  intros W p H. unfold istart. cbn [st_inv orb nonempty_str].
  split; [split; [constructor|split; [constructor|exact I]]|].
  split; [unfold prev_ok; rewrite H; left; reflexivity|discriminate].
Qed.

(*
The statement
=============
*)

(** Every delimiter node of a paragraph's located inlines, at any depth,
    has a span that starts with the row's opener and ends with its
    closer, both marked or both bare, as the paragraph's text reads
    them; a bare opener is followed by a nonspace byte and a bare closer
    preceded by one (M2); and at least one byte or line break lies
    between the two (M3).  The lines are the block layer's: stored text
    with its source line, in increasing line order. *)
Theorem para_inlines_spans : forall off l,
  StronglySorted Nat.lt (map fst l) ->
  Forall (dn_node (para_windows l)) (@para_inlines_at T located_pos off l).
Proof.
  intros off l Hs. unfold para_inlines_at. cbn [pos_records located_pos].
  unfold InlineLocated.para_inlines_located, InlineLocated.ifinish_located.
  set (W := para_windows l).
  assert (Hw : forall k r w, In (k, r, w) (para_windows l) -> wfind W k = Some (r, w)).
  { intros k r w Hin. apply wfind_in; [|exact Hin].
    unfold W. rewrite para_windows_keys. exact Hs. }
  eapply (ifinish_ok W _ (InlineLocated.lines_stop l)); [reflexivity|].
  destruct l as [|[k x] rest].
  - apply st_inv_start. reflexivity.
  - apply iscan_lines_ok; [discriminate|exact Hs|exact Hw|].
    apply st_inv_start. cbn [InlineLocated.lines_start].
    destruct rest as [|y rest'];
      (eapply byte_before_window; apply Hw; left; reflexivity).
Qed.

(** The same for a table cell: one window, the cell's trimmed text, at
    the distance from its line's end the row scanner found. *)
Theorem cell_inlines_spans : forall k rem s,
  String.length s <= rem ->
  Forall (dn_node [(k, rem, s)]) (@parse_inline_line_located T located_pos k rem s).
Proof.
  intros k rem s Hl. unfold parse_inline_line_located.
  set (W := [(k, rem, s)]).
  assert (Hw : wfind W k = Some (rem, s)) by (cbn; rewrite Nat.eqb_refl; reflexivity).
  eapply (ifinish_ok W _ (Spot k (rem - String.length s))); [reflexivity|].
  apply iscan_str_ok; [exact (sfx_window W k rem s Hw Hl)|].
  apply st_inv_start. eapply byte_before_window, Hw.
Qed.

End WithTable.
