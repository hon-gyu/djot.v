(* ai-disclosure: autonomous *)

(* Attribute specs, `{#id .class key=value}`, as a character state machine.

   Transcribed from djot.js `src/attributes.ts`, which is already an
   explicit state machine, so the transcription is close to line by line.
   Two deliberate departures, neither of them observable:

   - djot.js records *positions* into the whole document and recovers a
     token's text with `substring`, so a token spanning a line break
     silently picks up the newline and the next line's indentation.  Here
     a token is accumulated character by character and the newline is fed
     explicitly at the end of every line, which yields the same text
     because value collapsing turns any whitespace run into one space.

   - `SCANNING_QUOTED_VALUE_CONTINUATION` and
     `SCANNING_ESCAPED_IN_CONTINUATION` exist only to restart that
     position bookkeeping after a newline.  With an accumulator there is
     nothing to restart, so they are merged into `AQuot` and `AEsc`.

   The machine survives between lines, which is what lets a spec continue
   over an indented line break; `Step.v` carries it in `PAttr`. *)

From Stdlib Require Import String Ascii Bool List.
From DjotV Require Import Strings Ast.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope char_scope.

(*
Character classes
=================
*)

Definition bslash : ascii := "092".
Local Definition dquote : ascii := """".

(* `reKeyChar`: keys, bare values and class names. *)
Local Definition is_key_char (c : ascii) : bool :=
  let n := Ascii.nat_of_ascii c in
  (Nat.leb 97 n && Nat.leb n 122)          (* a-z *)
  || (Nat.leb 65 n && Nat.leb n 90)        (* A-Z *)
  || (Nat.leb 48 n && Nat.leb n 57)        (* 0-9 *)
  || Ascii.eqb c "_" || Ascii.eqb c ":" || Ascii.eqb c "-".

(* Whitespace as the attribute machine sees it: JavaScript's `\s`.  Unlike
   `Strings.is_ws` it includes the line feed, which the machine is fed at
   the end of every line. *)
Definition attr_ws (c : ascii) : bool :=
  is_ws c || Ascii.eqb c "010" || Ascii.eqb c "012" || Ascii.eqb c "011".

(* Identifiers take anything that is neither whitespace nor one of the
   punctuation characters below.  This is djot.js's class, wider than the
   rule the prose spec gives; `{#a<b}` fails because of `<`. *)
Definition is_id_char (c : ascii) : bool :=
  negb (attr_ws c) &&
  negb (List.existsb (Ascii.eqb c)
    ["]"; "["; "~"; "!"; "@"; "#"; "$"; "%"; "^"; "&"; "*"; "("; ")";
     "{"; "}"; "`"; ","; "."; "<"; ">"; bslash; "|"; "="; "+"; "/"; "?"]).

(* Class names are narrower: `\w` plus `:` and `-`, which is exactly the
   key-character class. *)
Local Definition is_attr_class_char (c : ascii) : bool := is_key_char c.

(*
Value normalization
===================

Two rewrites of a value's text before it is stored: whitespace runs
collapse to one space, then backslash escapes of punctuation resolve.
Collapsing first makes a value spanning several indented lines come out
as one line. *)

Local Definition collapse_char (c : ascii) : bool :=
  Ascii.eqb c " " || Ascii.eqb c "013" || Ascii.eqb c "010".

(* `skip` is "the previous character was part of a run already emitted". *)
Local Fixpoint collapse_from (skip : bool) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
      if collapse_char c
      then if skip then collapse_from true s' else String " " (collapse_from true s')
      else String c (collapse_from false s')
  end.

Local Definition collapse_ws (s : string) : string := collapse_from false s.

(* The punctuation a backslash may escape inside a value. *)
Local Definition is_escapable (c : ascii) : bool :=
  List.existsb (Ascii.eqb c)
    ["."; ","; bslash; "/"; "#"; "!"; "$"; "%"; "^"; "&"; "*"; ";"; ":";
     "{"; "}"; "="; "-"; "_"; "`"; "~"; "+"; "["; "]"; "("; ")"; "'";
     dquote; "?"; "|"].

Local Fixpoint unescape (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
      if Ascii.eqb c bslash
      then match s' with
           | EmptyString => String c EmptyString
           | String d s'' =>
               if is_escapable d
               then String d (unescape s'')
               else String c (unescape s')
           end
      else String c (unescape s')
  end.

Local Definition norm_value (s : string) : string := unescape (collapse_ws s).

(*
The machine
===========
*)

Inductive astate : Type :=
  | AScan                (* between attributes *)
  | AId                  (* after '#' *)
  | AClass               (* after '.' *)
  | AKey                 (* accumulating a key, '=' not yet seen *)
  | AVal                 (* just past '=' *)
  | ABare                (* unquoted value *)
  | AQuot                (* inside a double-quoted value *)
  | AEsc                 (* backslash inside a quoted value *)
  | AComment             (* inside %...% *)
  | AFail
  | ADone.

(* `ap_tok` accumulates the current token in reverse; `ap_key` holds the
   key whose value is being scanned; `ap_attrs` is what has been
   committed, in source order. *)
Record aparser : Type := AP
  { ap_st : astate
  ; ap_tok : list ascii
  ; ap_key : string
  ; ap_attrs : attr }.

Definition ap_init : aparser := AP AScan [] EmptyString [].

Definition ap_token (p : aparser) : string := rev_chars (ap_tok p).

Definition ap_push (c : ascii) (p : aparser) : aparser :=
  AP (ap_st p) (c :: ap_tok p) (ap_key p) (ap_attrs p).

Local Definition ap_goto (s : astate) (p : aparser) : aparser :=
  AP s (ap_tok p) (ap_key p) (ap_attrs p).

(* Enter s with a fresh token. *)
Definition ap_begin (s : astate) (p : aparser) : aparser :=
  AP s [] (ap_key p) (ap_attrs p).

(* Commit the accumulated token as an identifier and go to s.  An empty
   token commits nothing, so `{# }` is attribute-free rather than an
   error.  Same for classes. *)
Definition ap_commit_id (s : astate) (p : aparser) : aparser :=
  let t := ap_token p in
  AP s [] (ap_key p)
     (if String.eqb t EmptyString then ap_attrs p else Attr.set "id" t (ap_attrs p)).

Local Definition ap_commit_class (s : astate) (p : aparser) : aparser :=
  let t := ap_token p in
  AP s [] (ap_key p)
     (if String.eqb t EmptyString then ap_attrs p else Attr.add_class t (ap_attrs p)).

(* A value always commits, empty included, so `{a=""}` carries an `a`. *)
Local Definition ap_commit_value (s : astate) (p : aparser) : aparser :=
  AP s [] (ap_key p)
     (Attr.set (ap_key p) (norm_value (ap_token p)) (ap_attrs p)).

Definition astep (p : aparser) (c : ascii) : aparser :=
  match ap_st p with
  | ADone | AFail => p
  | AScan =>
      if attr_ws c then p
      else if Ascii.eqb c "}" then ap_goto ADone p
      else if Ascii.eqb c "#" then ap_begin AId p
      else if Ascii.eqb c "%" then ap_begin AComment p
      else if Ascii.eqb c "." then ap_begin AClass p
      else if is_key_char c then ap_push c (ap_begin AKey p)
      else ap_goto AFail p
  | AId =>
      if is_id_char c then ap_push c p
      else if Ascii.eqb c "}" then ap_commit_id ADone p
      else if attr_ws c then ap_commit_id AScan p
      else ap_goto AFail p
  | AClass =>
      if is_attr_class_char c then ap_push c p
      else if Ascii.eqb c "}" then ap_commit_class ADone p
      else if attr_ws c then ap_commit_class AScan p
      else ap_goto AFail p
  | AKey =>
      if Ascii.eqb c "=" then AP AVal [] (ap_token p) (ap_attrs p)
      else if is_key_char c then ap_push c p
      else ap_goto AFail p
  | AVal =>
      if Ascii.eqb c dquote then ap_begin AQuot p
      else if is_key_char c then ap_push c (ap_begin ABare p)
      else ap_goto AFail p
  | ABare =>
      if is_key_char c then ap_push c p
      else if Ascii.eqb c "}" then ap_commit_value ADone p
      else if attr_ws c then ap_commit_value AScan p
      else ap_goto AFail p
  | AQuot =>
      if Ascii.eqb c dquote then ap_commit_value AScan p
      else if Ascii.eqb c bslash then ap_goto AEsc (ap_push c p)
      else ap_push c p
  | AEsc => ap_goto AQuot (ap_push c p)
  | AComment =>
      if Ascii.eqb c "%" then ap_begin AScan p
      else if Ascii.eqb c "}" then ap_goto ADone p
      else p
  end.

(* Feed a string, stopping at the first terminal state; the second result
   is what was left unread, which is how "the spec ended before the line
   did" is detected. *)
Fixpoint afeed (s : string) (p : aparser) : aparser * string :=
  match s with
  | EmptyString => (p, EmptyString)
  | String c s' =>
      match ap_st p with
      | ADone | AFail => (p, s)
      | _ => afeed s' (astep p c)
      end
  end.

Definition ap_done (p : aparser) : bool :=
  match ap_st p with ADone => true | _ => false end.

Definition ap_failed (p : aparser) : bool :=
  match ap_st p with AFail => true | _ => false end.

(*
The line interface
==================

Both entry points feed the line's content with its indentation dropped,
followed by the newline that ended it.  The newline closes an identifier
or a bare value at end of line, and separates the pieces of a value that
spans lines. *)

Definition attr_nl : string := String "010" EmptyString.

(* Nothing but whitespace, newline included. *)
Fixpoint blank_to_eol (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => attr_ws c && blank_to_eol s'
  end.

(* Whether this line opens a block attribute spec, and in what state.
   `None` when the machine fails or the spec closes with content still on
   the line; either way the line is paragraph text. *)
Definition attr_open (l : string) : option aparser :=
  match drop_leading_ws l with
  | String "{" body =>
      let (p, rest) := afeed (body ++ attr_nl) ap_init in
      if ap_failed p then None
      else if ap_done p && negb (blank_to_eol rest) then None
      else Some p
  | _ => None
  end.

(* A continuation line, already known to be indented past the opener. *)
Definition attr_feed (l : string) (p : aparser) : aparser :=
  fst (afeed (drop_leading_ws l ++ attr_nl) p).

(* Leading whitespace is invisible here, as it is to every other
   recognizer: `attr_open` starts at the first nonblank character. *)
Lemma attr_open_ws_prefix :
  forall p l, is_blank p = true -> attr_open (p ++ l) = attr_open l.
Proof.
  intros p l Hp. unfold attr_open. rewrite (drop_leading_ws_ws_prefix p l Hp).
  reflexivity.
Qed.

(*
Line breaks
===========

A spec continued over indented lines is fed each line with a newline
after it.  The machine treats a newline as it treats a space: every test
it makes agrees on the two, and a quoted value that keeps one is
collapsed before it is stored.  So a spec run line by line ends where the
same spec joined onto one line does, with the same attributes
(`joined_spec_runs`).
*)

(* A newline, read as a space. *)
Local Definition nl_space (c : ascii) : ascii := if Ascii.eqb c "010" then " " else c.

Local Fixpoint smap (f : ascii -> ascii) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (f c) (smap f s')
  end.

Local Lemma nl_space_cases : forall c d, nl_space c = nl_space d ->
  c = d \/ ((c = "010" \/ c = " ") /\ (d = "010" \/ d = " ")).
Proof.
  intros c d H. unfold nl_space in H.
  destruct (Ascii.eqb c "010") eqn:Ec, (Ascii.eqb d "010") eqn:Ed;
    apply Ascii.eqb_eq in Ec || apply Ascii.eqb_neq in Ec;
    apply Ascii.eqb_eq in Ed || apply Ascii.eqb_neq in Ed; subst; auto.
Qed.

Local Lemma collapse_nl_space : forall b s,
  collapse_from b s = collapse_from b (smap nl_space s).
Proof.
  intros b s. revert b. induction s as [|c s IH]; intros b; [reflexivity|].
  cbn [smap collapse_from]. unfold nl_space.
  destruct (Ascii.eqb c "010") eqn:E.
  - apply Ascii.eqb_eq in E. subst c. cbn. rewrite <- !IH. reflexivity.
  - destruct (collapse_char c); rewrite <- !IH; reflexivity.
Qed.

Local Lemma smap_rev_chars : forall l,
  smap nl_space (rev_chars l) = rev_chars (map nl_space l).
Proof.
  induction l as [|c l IH]; [reflexivity|].
  cbn [rev_chars map]. rewrite <- IH.
  generalize (rev_chars l). intros s. induction s as [|d s IHs]; [reflexivity|].
  cbn [append smap]. rewrite IHs. reflexivity.
Qed.

(* Two machine states that differ only in how a quoted value spelled its
   line breaks. *)
Local Definition ap_sim (p q : aparser) : Prop :=
  ap_st p = ap_st q /\ ap_key p = ap_key q /\ ap_attrs p = ap_attrs q /\
  (ap_tok p = ap_tok q \/
   ((ap_st p = AQuot \/ ap_st p = AEsc) /\
    map nl_space (ap_tok p) = map nl_space (ap_tok q))).

Local Lemma norm_sim : forall t u, map nl_space t = map nl_space u ->
  norm_value (rev_chars t) = norm_value (rev_chars u).
Proof.
  intros t u H. unfold norm_value, collapse_ws.
  rewrite (collapse_nl_space false (rev_chars t)), (collapse_nl_space false (rev_chars u)).
  rewrite !smap_rev_chars, H. reflexivity.
Qed.

Local Lemma ap_sim_eq : forall p q, ap_sim p q ->
  ap_st p <> AQuot -> ap_st p <> AEsc -> p = q.
Proof.
  intros [s t k a] [s' t' k' a'] (Hs & Hk & Ha & Ht) Hq He; cbn in *.
  destruct Ht as [Ht|[[H|H] _]]; [subst; reflexivity|contradiction|contradiction].
Qed.

Local Lemma astep_ws : forall p,
  ap_st p <> AQuot -> ap_st p <> AEsc -> astep p "010" = astep p " ".
Proof.
  intros [s t k a] Hq He; cbn in Hq, He.
  destruct s; try contradiction; reflexivity.
Qed.

Local Lemma eqb_sim : forall c d x, nl_space c = nl_space d ->
  x <> "010" -> x <> " " -> Ascii.eqb c x = Ascii.eqb d x.
Proof.
  intros c d x H Hn Hs.
  assert (A : Ascii.eqb "010" x = false) by (apply Ascii.eqb_neq; congruence).
  assert (B : Ascii.eqb " " x = false) by (apply Ascii.eqb_neq; congruence).
  destruct (nl_space_cases c d H) as [<-|[[-> | ->] [-> | ->]]];
    rewrite ?A, ?B; reflexivity.
Qed.

Local Lemma tok_sim : forall p q, ap_sim p q ->
  map nl_space (ap_tok p) = map nl_space (ap_tok q).
Proof. intros p q (_ & _ & _ & [->|[_ H]]); [reflexivity|exact H]. Qed.

Local Lemma astep_sim : forall p q c d,
  ap_sim p q -> nl_space c = nl_space d -> ap_sim (astep p c) (astep q d).
Proof.
  intros p q c d Hpq Hcd.
  assert (Hrefl : forall r, ap_sim r r) by (intros r; repeat split; left; reflexivity).
  destruct (ap_st p) eqn:Es;
    try (assert (p = q) as <- by (apply ap_sim_eq; [exact Hpq| |]; rewrite Es; discriminate);
         destruct (nl_space_cases c d Hcd) as [<-|[[-> | ->] [-> | ->]]];
         first [ apply Hrefl
               | rewrite (astep_ws p) by (rewrite Es; discriminate); apply Hrefl
               | rewrite <- (astep_ws p) by (rewrite Es; discriminate); apply Hrefl ]).
  - (* AQuot *)
    destruct p as [s t k a], q as [s' t' k' a'].
    pose proof (tok_sim _ _ Hpq) as Ht. destruct Hpq as (Hs & Hk & Ha & _).
    cbn in Es, Hs, Hk, Ha, Ht. subst s s' k' a'. unfold astep. cbn [ap_st].
    rewrite (eqb_sim c d dquote Hcd ltac:(discriminate) ltac:(discriminate)).
    rewrite (eqb_sim c d bslash Hcd ltac:(discriminate) ltac:(discriminate)).
    destruct (Ascii.eqb d dquote); [|destruct (Ascii.eqb d bslash)].
    + unfold ap_commit_value, ap_token. cbn [ap_tok ap_key ap_attrs].
      rewrite (norm_sim t t' Ht). apply Hrefl.
    + repeat split; right; split; [right; reflexivity|cbn; rewrite Hcd, Ht; reflexivity].
    + repeat split; right; split; [left; reflexivity|cbn; rewrite Hcd, Ht; reflexivity].
  - (* AEsc *)
    destruct p as [s t k a], q as [s' t' k' a'].
    pose proof (tok_sim _ _ Hpq) as Ht. destruct Hpq as (Hs & Hk & Ha & _).
    cbn in Es, Hs, Hk, Ha, Ht. subst s s' k' a'. unfold astep. cbn [ap_st].
    repeat split; right; split; [left; reflexivity|cbn; rewrite Hcd, Ht; reflexivity].
Qed.

Local Lemma afeed_sim : forall s t p q,
  smap nl_space s = smap nl_space t -> ap_sim p q ->
  ap_sim (fst (afeed s p)) (fst (afeed t q)) /\
  smap nl_space (snd (afeed s p)) = smap nl_space (snd (afeed t q)).
Proof.
  induction s as [|c s IH]; intros [|d t] p q Hst Hpq; try discriminate.
  - split; [exact Hpq|reflexivity].
  - cbn [smap] in Hst. injection Hst as Hcd Hst.
    cbn [afeed]. rewrite <- (proj1 Hpq).
    destruct (ap_st p);
      first [ split; [exact Hpq|cbn [snd smap]; rewrite Hcd, Hst; reflexivity]
            | apply IH; [exact Hst|apply astep_sim; assumption] ].
Qed.

Local Lemma blank_to_eol_nl_space : forall s,
  blank_to_eol (smap nl_space s) = blank_to_eol s.
Proof.
  induction s as [|c s IH]; [reflexivity|]. cbn [smap blank_to_eol]. rewrite IH.
  unfold nl_space. destruct (Ascii.eqb c "010") eqn:E; [|reflexivity].
  apply Ascii.eqb_eq in E. subst c. reflexivity.
Qed.

Local Lemma blank_to_eol_app : forall a b,
  blank_to_eol (a ++ b) = (blank_to_eol a && blank_to_eol b)%bool.
Proof.
  induction a as [|c a IH]; intros b; [reflexivity|].
  cbn [append blank_to_eol]. rewrite IH, andb_assoc. reflexivity.
Qed.

Local Lemma smap_app : forall f a b, smap f (a ++ b) = smap f a ++ smap f b.
Proof. intros f a b. induction a as [|c a IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Local Definition ap_live (p : aparser) : bool :=
  match ap_st p with ADone | AFail => false | _ => true end.

(* Feeding stops at the first terminal state and hands back the rest. *)
Local Lemma afeed_app : forall a b p,
  afeed (a ++ b) p =
  if ap_live (fst (afeed a p)) then afeed b (fst (afeed a p))
  else (fst (afeed a p), snd (afeed a p) ++ b).
Proof.
  induction a as [|c a IH]; intros b p.
  - cbn [append afeed fst snd]. unfold ap_live.
    destruct b as [|d b]; destruct (ap_st p) eqn:E; cbn [afeed]; rewrite ?E; reflexivity.
  - cbn [append afeed]. unfold ap_live.
    destruct (ap_st p) eqn:E; try apply IH; cbn [fst snd append]; rewrite E; reflexivity.
Qed.

Local Lemma fst_afeed_app : forall a b p,
  fst (afeed (a ++ b) p) = fst (afeed b (fst (afeed a p))).
Proof.
  intros a b p. rewrite afeed_app. unfold ap_live.
  destruct (ap_st (fst (afeed a p))) eqn:E; try reflexivity;
    destruct b; cbn [afeed]; rewrite ?E; reflexivity.
Qed.

Local Lemma afeed_stopped : forall s p, ap_live p = false -> afeed s p = (p, s).
Proof.
  intros [|c s] p H; [reflexivity|]. cbn [afeed]. unfold ap_live in H.
  destruct (ap_st p); try discriminate; reflexivity.
Qed.

(* What a run of continuation lines feeds the machine. *)
Local Fixpoint lines_text (ls : list string) : string :=
  match ls with
  | [] => EmptyString
  | l :: ls' => (drop_leading_ws l ++ attr_nl) ++ lines_text ls'
  end.

(* The same lines joined onto the opener's, a space for each line
   break. *)
Fixpoint join_tail (ls : list string) : string :=
  match ls with
  | [] => EmptyString
  | l :: ls' => " " ++ drop_leading_ws l ++ join_tail ls'
  end.

(* The machine after a run of continuation lines. *)
Definition feed_lines (ls : list string) (p : aparser) : aparser :=
  fold_left (fun q l => attr_feed l q) ls p.

(* Whether a spec stays open and unfailed through every line of a run
   but the last, and is done after it: the run `PAttr` takes whole. *)
Fixpoint spec_runs (p : aparser) (ls : list string) : bool :=
  match ls with
  | [] => ap_done p
  | l :: ls' =>
      negb (ap_done p) && negb (ap_failed (attr_feed l p))
      && spec_runs (attr_feed l p) ls'
  end.

Local Lemma feed_lines_afeed : forall ls p,
  feed_lines ls p = fst (afeed (lines_text ls) p).
Proof.
  induction ls as [|l ls IH]; intros p; [reflexivity|].
  cbn [feed_lines fold_left lines_text]. fold (feed_lines ls (attr_feed l p)).
  rewrite IH, fst_afeed_app. reflexivity.
Qed.

Local Lemma join_tail_nl_space : forall ls,
  smap nl_space (join_tail ls ++ attr_nl) = smap nl_space (attr_nl ++ lines_text ls).
Proof.
  induction ls as [|l ls IH]; [reflexivity|].
  cbn [join_tail lines_text]. rewrite !append_assoc, !smap_app.
  rewrite <- (smap_app _ (join_tail ls) attr_nl), IH, smap_app. reflexivity.
Qed.

Local Lemma spec_runs_of_afeed : forall ls p,
  Forall (fun l => blank_to_eol (drop_leading_ws l) = false) ls ->
  ap_done (fst (afeed (lines_text ls) p)) = true ->
  blank_to_eol (snd (afeed (lines_text ls) p)) = true ->
  spec_runs p ls = true.
Proof.
  induction ls as [|l ls IH]; intros p Hls Hd Hb; [exact Hd|].
  inversion Hls as [|? ? Hl Hls']; subst.
  cbn [spec_runs lines_text] in *.
  destruct (ap_live p) eqn:Hp.
  2: { exfalso. rewrite (afeed_stopped _ _ Hp) in Hb. cbn [snd] in Hb.
       rewrite !blank_to_eol_app, Hl in Hb. discriminate. }
  assert (Hnd : ap_done p = false)
    by (unfold ap_live in Hp; unfold ap_done; destruct (ap_st p); congruence).
  rewrite Hnd. cbn [negb andb].
  rewrite afeed_app in Hd, Hb. fold (attr_feed l p) in Hd, Hb |- *.
  destruct (ap_live (attr_feed l p)) eqn:Hp1.
  - assert (Hnf : ap_failed (attr_feed l p) = false)
      by (unfold ap_live in Hp1; unfold ap_failed; destruct (ap_st (attr_feed l p)); congruence).
    rewrite Hnf. apply IH; assumption.
  - cbn [fst snd] in Hd, Hb.
    assert (Hnf : ap_failed (attr_feed l p) = false)
      by (unfold ap_done in Hd; unfold ap_failed; destruct (ap_st (attr_feed l p)); congruence).
    rewrite Hnf. apply IH; [exact Hls'| |];
      rewrite (afeed_stopped _ _ Hp1); cbn [fst snd]; [exact Hd|].
    rewrite blank_to_eol_app in Hb. apply andb_true_iff in Hb as [_ Hb]. exact Hb.
Qed.

Local Lemma ap_sim_refl : forall p, ap_sim p p.
Proof. intros p. repeat split. left. reflexivity. Qed.

(* A spec split over lines runs as the joined spec does: it is live until
   its last line, done at the end of it, with the same attributes. *)
Lemma joined_spec_runs : forall b1 ls ap1 r1 apJ rJ,
  Forall (fun l => blank_to_eol (drop_leading_ws l) = false) ls ->
  afeed (b1 ++ attr_nl) ap_init = (ap1, r1) -> ap_failed ap1 = false ->
  afeed ((b1 ++ join_tail ls) ++ attr_nl) ap_init = (apJ, rJ) ->
  ap_done apJ = true -> blank_to_eol rJ = true ->
  spec_runs ap1 ls = true /\ ap_attrs (feed_lines ls ap1) = ap_attrs apJ.
Proof.
  intros b1 ls ap1 r1 apJ rJ Hls H1 Hf1 HJ HdJ HbJ.
  assert (Hsm : smap nl_space ((b1 ++ attr_nl) ++ lines_text ls) =
                smap nl_space ((b1 ++ join_tail ls) ++ attr_nl)).
  { rewrite (append_assoc b1 attr_nl), (append_assoc b1 (join_tail ls)).
    rewrite (smap_app _ b1), (smap_app _ b1), join_tail_nl_space. reflexivity. }
  destruct (afeed_sim _ _ _ _ Hsm (ap_sim_refl ap_init)) as [Hs Hr].
  rewrite HJ in Hs, Hr. cbn [fst snd] in Hs, Hr.
  rewrite fst_afeed_app, H1 in Hs. cbn [fst] in Hs.
  rewrite feed_lines_afeed. split; [|exact (proj1 (proj2 (proj2 Hs)))].
  apply spec_runs_of_afeed; [exact Hls| |].
  - unfold ap_done. rewrite (proj1 Hs). exact HdJ.
  - rewrite afeed_app, H1 in Hr. cbn [fst snd] in Hr.
    destruct (ap_live ap1) eqn:Hl;
      rewrite <- blank_to_eol_nl_space, <- Hr, blank_to_eol_nl_space in HbJ;
      [exact HbJ|].
    rewrite (afeed_stopped _ _ Hl). cbn [snd].
    cbn [snd] in HbJ. rewrite blank_to_eol_app in HbJ. apply andb_true_iff in HbJ as [_ H]. exact H.
Qed.

(* What `attr_open` fed the machine, and what it checked. *)
Lemma attr_open_inv : forall l ap, attr_open l = Some ap ->
  exists b r, drop_leading_ws l = String "{" b /\
    afeed (b ++ attr_nl) ap_init = (ap, r) /\ ap_failed ap = false /\
    (ap_done ap = true -> blank_to_eol r = true).
Proof.
  intros l ap H. unfold attr_open in H.
  destruct (drop_leading_ws l) as [|c b] eqn:E; [discriminate|].
  destruct (Ascii.eqb c "{") eqn:Ec.
  2: { destruct c as [[] [] [] [] [] [] [] []]; discriminate. }
  apply Ascii.eqb_eq in Ec. subst c.
  destruct (afeed (b ++ attr_nl) ap_init) as [p r] eqn:Ef.
  destruct (ap_failed p) eqn:Hf; [discriminate|].
  destruct (ap_done p && negb (blank_to_eol r))%bool eqn:Hd; [discriminate|].
  injection H as <-. exists b, r. repeat split; try assumption.
  intros Hdone. rewrite Hdone in Hd. destruct (blank_to_eol r); [reflexivity|discriminate].
Qed.

(*
Printing
========

A spec that reads back to the attributes it was printed from: `#id` and
`.class` where the characters allow, `key="value"` otherwise.  A value
cannot keep a whitespace run or a line break, which `norm_value`
collapses, so an attribute holding one reads back collapsed. *)

Fixpoint id_chars_ok (id : string) : bool :=
  match id with
  | EmptyString => true
  | String c rest => is_id_char c && id_chars_ok rest
  end.

Definition explicit_id_ok (id : string) : bool :=
  nonempty_str id && id_chars_ok id.

(* A class entry spelled as `.a .b`: words of class characters, one space
   apart. *)
Local Fixpoint class_words_ok (after_space : bool) (s : string) : bool :=
  match s with
  | EmptyString => negb after_space
  | String c rest =>
      if Ascii.eqb c " " then negb after_space && class_words_ok true rest
      else is_attr_class_char c && class_words_ok false rest
  end.

Definition classes_ok (s : string) : bool := nonempty_str s && class_words_ok true s.

(* One class word, which a div fence can carry. *)
Local Fixpoint class_chars_ok (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c rest => is_attr_class_char c && class_chars_ok rest
  end.

Definition class_word_ok (s : string) : bool := nonempty_str s && class_chars_ok s.

Local Fixpoint dot_words (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if Ascii.eqb c " " then String c (String "." (dot_words rest))
      else String c (dot_words rest)
  end.

Local Fixpoint escape_value (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if Ascii.eqb c dquote || Ascii.eqb c bslash
      then String bslash (String c (escape_value rest))
      else String c (escape_value rest)
  end.

Definition attr_part (kv : string * string) : string :=
  let (k, v) := kv in
  if String.eqb k "id" && explicit_id_ok v then String "#" v
  else if String.eqb k "class" && classes_ok v then String "." (dot_words v)
  else (k ++ "=" ++ String dquote (escape_value v ++ String dquote EmptyString))%string.

(* The spec for a nonempty attribute set; the empty set has none. *)
Definition attr_spec (a : attr) : string :=
  match a with
  | [] => EmptyString
  | _ => ("{" ++ String.concat " " (map attr_part a) ++ "}")%string
  end.
