(* Line classification: the prefix-determinism seam.

   Block structure in djot is a function of what each line looks like
   (spec: "blocks can be parsed line by line ... the contribution a line
   makes to block-level structure never depends on a future line").  This
   module gives each line its kind; the parser consumes kinds, and the
   classifier is the single place a new block construct's start syntax is
   added.  Renderability (Render.v) is phrased as "each rendered line
   classifies as intended", which is what makes roundtrip proofs local. *)

From Stdlib Require Import String Ascii Bool PeanoNat Lia.
From DjotV Require Import Strings.

Local Open Scope string_scope.
Local Open Scope char_scope.

(* An opened code fence: its character (` or ~), length, and info string
   (language, or =FORMAT for raw blocks). *)
Record fence : Type := Fence
  { f_ch : ascii; f_len : nat; f_info : string }.

Inductive line_kind : Type :=
  | KBlank                 (* only whitespace *)
  | KThematic              (* thematic break: 3+ of - or * (mixed ok), ws between *)
  | KFence (f : fence)     (* code fence opener *)
  | KQuote (rest : string) (* block-quote prefix, with the line it encloses *)
  | KHeading (level : nat) (rest : string)   (* #+ then ws, with its text *)
  | KList (m : ascii) (rest : string)  (* bullet marker, with its content *)
  | KText.                 (* anything else: paragraph text *)

(*
Recognizers
===========
*)

(* A thematic-break marker character. *)
Definition is_marker (c : ascii) : bool :=
  Ascii.eqb c "-" || Ascii.eqb c "*".

(* djot.js pattThematicBreak: markers and whitespace only, >= 3 markers.
   (Indentation is allowed; leading ws goes through the ws branch.) *)

Fixpoint thematic_count (s : string) (count : nat) : bool :=
  match s with
  | EmptyString => Nat.leb 3 count
  | String c s' =>
      if is_marker c then thematic_count s' (S count)
      else if is_ws c then thematic_count s' count
      else false
  end.

Definition is_thematic (l : string) : bool := thematic_count l 0.

(* Marker and whitespace are disjoint character classes, so a thematic
   count run through an all-whitespace prefix never touches the marker
   branch: it just keeps the count. *)
Lemma is_ws_not_marker : forall c, is_ws c = true -> is_marker c = false.
Proof.
  intros c H. unfold is_marker.
  destruct (Ascii.eqb c "-") eqn:E1.
  - apply Ascii.eqb_eq in E1. subst c. discriminate H.
  - destruct (Ascii.eqb c "*") eqn:E2; [|reflexivity].
    apply Ascii.eqb_eq in E2. subst c. discriminate H.
Qed.

Lemma thematic_count_ws_prefix :
  forall p l n, is_blank p = true -> thematic_count (p ++ l) n = thematic_count l n.
Proof.
  induction p as [|c p IH]; intros l n H; [reflexivity|].
  cbn [is_blank] in H. apply andb_true_iff in H as [Hc Hp].
  change (String c p ++ l) with (String c (p ++ l)).
  cbn [thematic_count]. rewrite (is_ws_not_marker c Hc), Hc. apply IH, Hp.
Qed.

Lemma is_thematic_ws_prefix :
  forall p l, is_blank p = true -> is_thematic (p ++ l) = is_thematic l.
Proof. intros p l H. unfold is_thematic. apply thematic_count_ws_prefix, H. Qed.

(* Code fences, per djot.js pattCodeFence:
   3+ of a uniform fence char (` or ~), optional ws, one info token
   containing neither whitespace nor backticks, optional trailing ws.
   The fence may be indented.  A close line is the same char, at least
   the open length, and nothing else but whitespace. *)

(* Length of the leading run of c, and the rest of the string. *)
Fixpoint count_run (c : ascii) (s : string) : nat * string :=
  match s with
  | String c' s' =>
      if Ascii.eqb c c'
      then let (n, r) := count_run c s' in (S n, r)
      else (O, s)
  | EmptyString => (O, s)
  end.

(* Characters admissible in a fence info string. *)
Definition is_info_char (c : ascii) : bool :=
  negb (is_ws c || Ascii.eqb c "`" || Ascii.eqb c "010").

(* Split off the leading info token from the rest of the line. *)
Fixpoint take_info (s : string) : string * string :=
  match s with
  | String c s' =>
      if is_info_char c
      then let (info, r) := take_info s' in (String c info, r)
      else (EmptyString, s)
  | EmptyString => (EmptyString, s)
  end.

(* Does this line open a fence, and if so which one? *)
Definition fence_open (l : string) : option fence :=
  match drop_leading_ws l with
  | String c _ as l' =>
      if Ascii.eqb c "`" || Ascii.eqb c "~"
      then
        let (n, r) := count_run c l' in
        if Nat.leb 3 n
        then
          let (info, r') := take_info (drop_leading_ws r) in
          if is_blank r' then Some (Fence c n info) else None
        else None
      else None
  | EmptyString => None
  end.

(* Does this line close the given open fence?  Note this is the *only*
   test applied to a line inside a fence — content is never classified. *)
Definition fence_close (f : fence) (l : string) : bool :=
  let (n, r) := count_run (f_ch f) (drop_leading_ws l) in
  Nat.leb (f_len f) n && is_blank r.

(* Block quotes, per djot.js pattBlockquotePrefix (`[>][ \t\r\n]`): a
   '>' that is followed by whitespace or ends the line.  The prefix is
   the '>' plus at most one whitespace character; what remains is the
   enclosed line, which the parser classifies again (so nesting and
   uniformity both come from re-entering `classify`).

   `>x` is *not* a quote — the whitespace is required.  Indentation
   before the '>' is allowed. *)
Definition quote_prefix (l : string) : option string :=
  match drop_leading_ws l with
  | String c rest =>
      if Ascii.eqb c ">"
      then match rest with
           | EmptyString => Some EmptyString
           | String c' rest' => if is_ws c' then Some rest' else None
           end
      else None
  | EmptyString => None
  end.

(* The enclosed line is strictly shorter, which is what makes the
   parser's descent into nested quotes terminate. *)
Lemma quote_prefix_length :
  forall l rest,
    quote_prefix l = Some rest -> String.length rest < String.length l.
Proof.
  intros l rest H. unfold quote_prefix in H.
  pose proof (drop_leading_ws_length l) as Hle.
  destruct (drop_leading_ws l) as [|c r] eqn:E; [discriminate|].
  destruct (Ascii.eqb c ">"); [|discriminate].
  simpl in Hle.
  destruct r as [|c' r'].
  - injection H as <-. simpl. lia.
  - destruct (is_ws c'); [|discriminate].
    injection H as <-. simpl in *. lia.
Qed.

(* Headings, per djot.js's `pattBangs` plus a whitespace test: one or
   more '#' followed by whitespace or end of line.  Shaped exactly like
   quote_prefix — marker, then at most one whitespace character — but the
   text that follows is *not* reclassified: a heading's content is
   inline, so `# > q` is a heading containing "> q", not a quote. *)
Definition heading_open (l : string) : option (nat * string) :=
  let (n, r) := count_run "#" (drop_leading_ws l) in
  if Nat.leb 1 n
  then match r with
       | EmptyString => Some (n, EmptyString)
       | String c r' => if is_ws c then Some (n, r') else None
       end
  else None.

(* Bullet-list markers, per djot.js pattListMarker restricted to the
   bullet styles (`[-*+]` followed by whitespace or end of line) — same
   marker-then-at-most-one-space shape as quotes and headings.  The
   marker character is the list's *style*: djot.js starts a new list
   when the style changes, so `- a` then `* b` is two lists.

   Ordered markers (`1.`, `(a)`, roman numerals) are deliberately not
   here: their styles are ambiguous until a sibling disambiguates, which
   the plan files under Phase 3's small combinatorial specs.

   `-x` is not a marker, and `* * *` is a thematic break — `classify`
   tests thematic first, matching djot.js's spec order. *)
Definition is_bullet (c : ascii) : bool :=
  (Ascii.eqb c "-" || Ascii.eqb c "*" || Ascii.eqb c "+")%char%bool.

Definition list_marker (l : string) : option (ascii * string) :=
  match drop_leading_ws l with
  | String c rest =>
      if is_bullet c
      then match rest with
           | EmptyString => Some (c, EmptyString)
           | String c' rest' => if is_ws c' then Some (c, rest') else None
           end
      else None
  | EmptyString => None
  end.

(* Like quote_prefix_length: the content after a bullet marker is
   strictly shorter than the line, which is what makes the parser's
   descent into a list item terminate. *)
Lemma list_marker_length :
  forall l m rest,
    list_marker l = Some (m, rest) -> String.length rest < String.length l.
Proof.
  intros l m rest H. unfold list_marker in H.
  pose proof (drop_leading_ws_length l) as Hle.
  destruct (drop_leading_ws l) as [|c r] eqn:E; [discriminate|].
  destruct (is_bullet c); [|discriminate].
  simpl in Hle.
  destruct r as [|c' r'].
  - injection H as _ <-. simpl. lia.
  - destruct (is_ws c'); [|discriminate].
    injection H as _ <-. simpl in *. lia.
Qed.

(* The classifier: one line in, one kind out, no lookahead.  Blank first,
   then block quotes, headings, fences, thematic breaks, list markers;
   anything unrecognized falls through to paragraph text, so KText is the
   catch-all.  Adding a block construct starts by adding a case here. *)
Definition classify (l : string) : line_kind :=
  if is_blank l then KBlank
  else match quote_prefix l with
       | Some rest => KQuote rest
       | None =>
           match heading_open l with
           | Some (lvl, rest) => KHeading lvl rest
           | None =>
               match fence_open l with
               | Some f => KFence f
               | None =>
                   if is_thematic l then KThematic
                   else match list_marker l with
                        | Some (m, rest) => KList m rest
                        | None => KText
                        end
               end
           end
       end.

(* Headings always have a level, which is what wf_block requires of the
   `Heading` it builds. *)
Lemma classify_heading_level :
  forall l lvl rest, classify l = KHeading lvl rest -> Nat.leb 1 lvl = true.
Proof.
  intros l lvl rest H. unfold classify in H.
  destruct (is_blank l); [discriminate|].
  destruct (quote_prefix l); [discriminate|].
  unfold heading_open in H.
  destruct (count_run "#" (drop_leading_ws l)) as [n r].
  destruct (Nat.leb 1 n) eqn:E.
  - destruct r as [|c r']; [injection H as <- <-; exact E|].
    destruct (is_ws c); [injection H as <- <-; exact E|].
    destruct (fence_open l); [discriminate|].
    destruct (is_thematic l); [discriminate|].
    destruct (list_marker l) as [[m r0]|]; discriminate.
  - destruct (fence_open l); [discriminate|].
    destruct (is_thematic l); [discriminate|].
    destruct (list_marker l) as [[m r0]|]; discriminate.
Qed.

(*
Classification facts
====================
*)

Lemma classify_blank :
  forall l, is_blank l = true -> classify l = KBlank.
Proof. intros l H. unfold classify. rewrite H. reflexivity. Qed.

Lemma classify_kblank_blank :
  forall l, classify l = KBlank -> is_blank l = true.
Proof.
  intros l H. unfold classify in H.
  destruct (is_blank l); [reflexivity|].
  destruct (quote_prefix l); [discriminate|].
  destruct (heading_open l) as [[lvl rest]|]; [discriminate|].
  destruct (fence_open l); [discriminate|].
  destruct (is_thematic l); [discriminate|].
  destruct (list_marker l) as [[m r0]|]; discriminate.
Qed.

(* The measure fact, restated at the classifier: the parser only ever
   sees KQuote, never quote_prefix directly. *)
Lemma classify_quote_length :
  forall l rest,
    classify l = KQuote rest -> String.length rest < String.length l.
Proof.
  intros l rest H. apply quote_prefix_length.
  unfold classify in H.
  destruct (is_blank l); [discriminate|].
  destruct (quote_prefix l) as [r|].
  - injection H as <-. reflexivity.
  - destruct (heading_open l) as [[lvl r2]|]; [discriminate|].
    destruct (fence_open l); [discriminate|].
    destruct (is_thematic l); [discriminate|].
    destruct (list_marker l) as [[m r0]|]; discriminate.
Qed.

Lemma classify_list_length :
  forall l m rest,
    classify l = KList m rest -> String.length rest < String.length l.
Proof.
  intros l m rest H. apply (list_marker_length l m).
  unfold classify in H.
  destruct (is_blank l); [discriminate|].
  destruct (quote_prefix l); [discriminate|].
  destruct (heading_open l) as [[lvl r2]|]; [discriminate|].
  destruct (fence_open l); [discriminate|].
  destruct (is_thematic l); [discriminate|].
  destruct (list_marker l) as [[m' r']|]; [|discriminate].
  injection H as <- <-. reflexivity.
Qed.

Lemma classify_not_kblank_nonblank :
  forall l, classify l <> KBlank -> is_blank l = false.
Proof.
  intros l H. destruct (is_blank l) eqn:E; [|reflexivity].
  exfalso. apply H, classify_blank, E.
Qed.

Lemma classify_ktext :
  forall l,
    is_blank l = false -> quote_prefix l = None -> heading_open l = None ->
    fence_open l = None -> is_thematic l = false -> list_marker l = None ->
    classify l = KText.
Proof.
  intros l Hb Hq Hh Hf Ht Hm. unfold classify.
  rewrite Hb, Hq, Hh, Hf, Ht, Hm. reflexivity.
Qed.

(* The canonical thematic-break rendering classifies as one. *)
Lemma classify_canonical_thematic : classify "* * * *" = KThematic.
Proof. reflexivity. Qed.

(* An all-whitespace prefix is invisible to the classifier: every
   recognizer either routes through drop_leading_ws (quote/heading/fence/
   list markers) or, for is_thematic, treats whitespace as skippable
   throughout, not just leading (Strings.drop_leading_ws_ws_prefix,
   is_thematic_ws_prefix).  This is what lets a list item's "  "
   continuation indent be pushed straight through: the enclosed line
   reclassifies exactly as it would unindented. *)
Lemma classify_ws_prefix :
  forall p l, is_blank p = true -> classify (p ++ l) = classify l.
Proof.
  intros p l Hp. unfold classify.
  rewrite (is_blank_ws_prefix p l Hp).
  destruct (is_blank l) eqn:Eb; [reflexivity|].
  unfold quote_prefix, heading_open, fence_open, list_marker.
  rewrite (drop_leading_ws_ws_prefix p l Hp).
  fold (is_thematic l). rewrite <- (is_thematic_ws_prefix p l Hp).
  unfold is_thematic. reflexivity.
Qed.

(* Boolean form of `classify l = KText`, so it can sit inside cb_ok. *)
Definition is_text (l : string) : bool :=
  match classify l with KText => true | _ => false end.

Lemma is_text_classify :
  forall l, is_text l = true -> classify l = KText.
Proof.
  intros l H. unfold is_text in H.
  destruct (classify l); (discriminate || reflexivity).
Qed.

(*
Canonical code fences
=====================

The renderer emits backtick fences of length 3; these lemmas say such
lines classify as intended. *)

(* An info string the renderer can emit verbatim and get back. *)
Fixpoint all_info_chars (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => is_info_char c && all_info_chars s'
  end.

(* Decompose the all_info_chars head fact into its three components. *)
Lemma info_char_parts :
  forall c, is_info_char c = true ->
  is_ws c = false /\ Ascii.eqb c "`" = false /\ Ascii.eqb c "010" = false.
Proof.
  intros c H. unfold is_info_char in H. apply negb_true_iff in H.
  apply orb_false_iff in H as [H Hn]. apply orb_false_iff in H as [Hw Hb].
  auto.
Qed.

Lemma count_run_info :
  forall info, all_info_chars info = true ->
  count_run "`" info = (O, info).
Proof.
  intros info H. destruct info as [|c info']; [reflexivity|].
  simpl in H. apply andb_true_iff in H as [Hc _].
  apply info_char_parts in Hc as (_ & Hb & _).
  cbn [count_run].
  destruct (Ascii.eqb "`" c) eqn:E; [|reflexivity].
  apply Ascii.eqb_eq in E. subst c.
  rewrite Ascii.eqb_refl in Hb. discriminate.
Qed.

Lemma drop_leading_ws_info :
  forall info, all_info_chars info = true ->
  drop_leading_ws info = info.
Proof.
  intros info H. destruct info as [|c info']; [reflexivity|].
  simpl in H. apply andb_true_iff in H as [Hc _].
  apply info_char_parts in Hc as (Hw & _ & _).
  cbn [drop_leading_ws]. rewrite Hw. reflexivity.
Qed.

Lemma take_info_all :
  forall info, all_info_chars info = true ->
  take_info info = (info, EmptyString).
Proof.
  induction info as [|c info IH]; intros H; [reflexivity|].
  simpl in H. apply andb_true_iff in H as [Hc Hinfo].
  cbn [take_info]. rewrite Hc, (IH Hinfo). reflexivity.
Qed.

Lemma drop_head_nonws :
  forall c s, is_ws c = false -> drop_leading_ws (String c s) = String c s.
Proof. intros c s H. cbn [drop_leading_ws]. rewrite H. reflexivity. Qed.

(* The two facts the roundtrip proof actually consumes: the renderer's
   "```INFO" opener and "```" closer behave as intended. *)
Lemma fence_open_backtick :
  forall info, all_info_chars info = true ->
  fence_open ("```" ++ info) = Some (Fence "`" 3 info).
Proof.
  intros info H.
  assert (E3 : count_run "`"
                 (String "`" (String "`" (String "`" info))) = (3, info)).
  { cbn [count_run Ascii.eqb]. rewrite (count_run_info info H). reflexivity. }
  unfold fence_open.
  change ("```" ++ info) with (String "`" (String "`" (String "`" info))).
  rewrite drop_head_nonws by reflexivity.
  cbn [Ascii.eqb orb].
  rewrite E3.
  cbn [Nat.leb].
  rewrite (drop_leading_ws_info info H), (take_info_all info H).
  reflexivity.
Qed.

Lemma classify_backtick_fence :
  forall info, all_info_chars info = true ->
  classify ("```" ++ info) = KFence (Fence "`" 3 info).
Proof.
  intros info H. unfold classify.
  change (is_blank ("```" ++ info)) with false.
  change (quote_prefix ("```" ++ info)) with (@None string).
  change (heading_open ("```" ++ info)) with (@None (nat * string)).
  rewrite (fence_open_backtick info H). reflexivity.
Qed.

(* Canonical block-quote prefixing, the renderer's spelling: "> " in
   front of every line, including blank ones. *)
Lemma quote_prefix_canonical :
  forall l, quote_prefix ("> " ++ l) = Some l.
Proof. reflexivity. Qed.

Lemma classify_canonical_quote :
  forall l, classify ("> " ++ l) = KQuote l.
Proof.
  intros l. unfold classify.
  change (is_blank ("> " ++ l)) with false.
  rewrite quote_prefix_canonical. reflexivity.
Qed.

(* Same, seen through an all-whitespace pad: a quote's own prefix is
   detected identically regardless of what ambient indentation precedes
   it, and the extracted content is exactly `l` with no pad residue —
   this is what lets a quote nested inside a list item ignore the
   item's indent entirely, unlike a nested list (Render.list_content_safe). *)
Lemma classify_canonical_quote_pad :
  forall pad l, is_blank pad = true -> classify (pad ++ "> " ++ l) = KQuote l.
Proof.
  intros pad l Hpad. rewrite classify_ws_prefix by exact Hpad.
  apply classify_canonical_quote.
Qed.

(*
Canonical headings
==================

The renderer prefixes every line of a heading with its hashes and one
space, so a multi-line heading reparses line by line as continuations of
itself — the same trick as block quotes, without the reclassification. *)

Fixpoint hashes (n : nat) : string :=
  match n with O => EmptyString | S n' => "#" ++ hashes n' end.

Definition heading_line (lvl : nat) (l : string) : string :=
  hashes lvl ++ " " ++ l.

(* The hashes are consumed exactly: the renderer's space stops the run,
   so the level comes back out unchanged however long the text is. *)
Lemma count_run_hashes_space :
  forall n l, count_run "#" (hashes n ++ " " ++ l) = (n, " " ++ l).
Proof.
  induction n as [|n IH]; intros l; [reflexivity|].
  cbn [hashes]. rewrite append_assoc.
  change ("#" ++ (hashes n ++ " " ++ l))%string
    with (String "#" (hashes n ++ " " ++ l))%string.
  cbn [count_run]. rewrite IH. reflexivity.
Qed.

Lemma drop_leading_ws_hashes :
  forall n l, 1 <= n -> drop_leading_ws (hashes n ++ " " ++ l) = (hashes n ++ " " ++ l).
Proof.
  intros n l H. destruct n as [|n']; [lia|].
  cbn [hashes]. rewrite append_assoc.
  change ("#" ++ (hashes n' ++ " " ++ l))%string
    with (String "#" (hashes n' ++ " " ++ l))%string.
  apply drop_head_nonws. reflexivity.
Qed.

Lemma no_nl_hashes : forall n, no_nl (hashes n) = true.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [hashes]. change ("#" ++ hashes n)%string with (String "#" (hashes n)).
  cbn [no_nl]. exact IH.
Qed.

Lemma heading_line_no_nl :
  forall lvl l, no_nl (heading_line lvl l) = no_nl l.
Proof.
  intros lvl l. unfold heading_line.
  rewrite !no_nl_append, no_nl_hashes. reflexivity.
Qed.

Lemma heading_line_nonempty :
  forall lvl l, 1 <= lvl -> heading_line lvl l <> EmptyString.
Proof.
  intros lvl l H. unfold heading_line.
  destruct lvl as [|n]; [lia|].
  cbn [hashes]. rewrite append_assoc. discriminate.
Qed.

Lemma classify_canonical_heading :
  forall lvl l, 1 <= lvl -> classify (heading_line lvl l) = KHeading lvl l.
Proof.
  intros lvl l H. unfold classify, heading_line.
  assert (Hb : is_blank (hashes lvl ++ " " ++ l) = false).
  { destruct lvl as [|n]; [lia|]. reflexivity. }
  assert (Hq : quote_prefix (hashes lvl ++ " " ++ l) = None).
  { unfold quote_prefix. rewrite drop_leading_ws_hashes by exact H.
    destruct lvl as [|n]; [lia | reflexivity]. }
  rewrite Hb, Hq.
  unfold heading_open. rewrite drop_leading_ws_hashes by exact H.
  rewrite count_run_hashes_space.
  destruct lvl as [|n]; [lia|]. reflexivity.
Qed.

Lemma fence_close_canonical :
  forall info, fence_close (Fence "`" 3 info) "```" = true.
Proof. reflexivity. Qed.

(* classify_canonical_heading, seen through an all-whitespace pad — same
   free ride as classify_canonical_quote_pad. *)
Lemma classify_canonical_heading_pad :
  forall pad lvl l, is_blank pad = true -> 1 <= lvl ->
  classify (pad ++ heading_line lvl l) = KHeading lvl l.
Proof.
  intros pad lvl l Hpad Hlvl. rewrite classify_ws_prefix by exact Hpad.
  apply classify_canonical_heading, Hlvl.
Qed.

(*
Canonical bullet lists
=======================

The renderer marks an item's first line with "- " and every later line
(whether a continuation of that first block or the start of a later one)
with two spaces of plain indent — the same shape djot.js's own
`this.indent > container.extra.indent` test expects, since `bullet_open`
puts the marker at column 0 and everything after it at column 2.  Unlike
quote_line, the marker is not repeated on every line: `bullet_cont` is
whitespace, so `classify_ws_prefix` carries every recognizer through it
for free — a nested construct starting on a continuation line reclassifies
exactly as it would unindented. *)

Definition bullet_open : string := "- ".
Definition bullet_cont : string := "  ".

Lemma bullet_cont_blank : is_blank bullet_cont = true.
Proof. reflexivity. Qed.

Lemma classify_bullet_cont :
  forall l, classify (bullet_cont ++ l) = classify l.
Proof. intros l. apply classify_ws_prefix, bullet_cont_blank. Qed.

Lemma indent_of_bullet_cont :
  forall l, indent_of (bullet_cont ++ l) = 2 + indent_of l.
Proof. intros l. apply indent_of_ws_prefix, bullet_cont_blank. Qed.

(* The marker line's classification needs one extra hypothesis quotes and
   headings don't: "- " plus the item's own first line must not itself
   look like a thematic break ("- - -"), since `classify` tests thematic
   breaks before list markers.  A canonical item's cb_ok carries this. *)
Lemma classify_bullet_open :
  forall l, is_thematic (bullet_open ++ l) = false ->
  classify (bullet_open ++ l) = KList "-"%char l.
Proof.
  intros l Hth. unfold classify, bullet_open.
  change (is_blank ("- " ++ l)) with false.
  change (quote_prefix ("- " ++ l)) with (@None string).
  change (heading_open ("- " ++ l)) with (@None (nat * string)).
  change (fence_open ("- " ++ l)) with (@None fence).
  change (is_thematic ("- " ++ l)) with (is_thematic (bullet_open ++ l)).
  rewrite Hth.
  change (list_marker ("- " ++ l)) with (Some ("-"%char, l)).
  reflexivity.
Qed.

Lemma indent_of_bullet_open : forall l, indent_of (bullet_open ++ l) = 0.
Proof. reflexivity. Qed.
