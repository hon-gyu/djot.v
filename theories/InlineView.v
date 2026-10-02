(* ai-disclosure: autonomous *)

(* The table in force, the escape encoding, the canonical inline view
   `cinline` with its source (`ci_src`), AST (`ci_ast`) and conditions
   (`ci_ok`), the canonical paragraph (`ci_para`), and the renderer. *)

From Stdlib Require Import String Ascii List Bool Lia Wf_nat Arith.
From DjotV Require Import Config Strings Ast Attributes InlineTable Line.
Import ListNotations.

Local Open Scope string_scope.

Section WithTable.
Context {T : dtable}.

Definition dchar (k : dstyle) : ascii := dc_char cfg k.

Definition dsyntax_of (k : dstyle) : dsyntax := dc_syntax cfg k.

Definition dwidth (k : dstyle) : nat := dc_width cfg k.

Definition smart_typography : bool := dc_smart_typography cfg.

Definition raw_inline_enabled : bool := dc_raw_inline cfg.

Definition math_enabled : bool := dc_math cfg.

Definition dollar_math_enabled : bool := dc_dollar_math cfg.

Definition inline_attrs_enabled : bool := dc_attrs cfg.

Definition notes_enabled : bool := dc_footnotes cfg.

Definition wikilinks_enabled : bool := dc_wikilinks cfg.

(* Whether the row exists at all in the table in force. *)
Definition denabled_of (k : dstyle) : bool := denabled cfg k.

Definition dstyle_of (c : ascii) : option dstyle := dstyle_at_fast cfg c.

(* A row's delimiter as written: `dwidth` copies of its character.  The
   scanner cuts a run of the character into these and leaves any
   remainder as text.  The character belongs to one row, so a width is
   enough. *)
Definition dtoken (k : dstyle) : string := chars (dchar k) (dwidth k).

(* Whitespace as the delimiter rules see it.  `can_open` and `can_close`
   each test one neighbouring byte against this. *)
Local Definition is_space (c : ascii) : bool :=
  (Ascii.eqb c " "%char || Ascii.eqb c "009"%char
   || Ascii.eqb c "013"%char || Ascii.eqb c "010"%char)%bool.

Definition nonspace_at (p : option ascii) : bool :=
  match p with None => false | Some c => negb (is_space c) end.

(* The bytes after which the single quote may open: the start of the
   line, whitespace, either quote, a hyphen, or an opening paren or
   bracket.  After anything else an apostrophe could be meant. *)
Local Definition dopens_after (c : option ascii) : bool :=
  match c with
  | None => true
  | Some ch =>
      (is_space ch || Ascii.eqb ch sqchar || Ascii.eqb ch dqchar
       || Ascii.eqb ch hyphen || Ascii.eqb ch lparen || Ascii.eqb ch lbrack)%bool
  end.

(* What an unmatched token leaves behind.  The two markers are the braces
   that forced it open or closed, and they decide two things.

   How far the token reaches.  An ordinary row leaves its own source,
   with the brace it consumed.  A token with an open marker does not
   consume the `}` after it, so `*}` is two characters of text and `{*}`
   is `{*` with the `}` still to come.

   Which side a smart quote takes.  An open marker can only turn a right
   default into a left one and a close marker only the reverse, so on a
   token with both, the row's default decides.  The double quote defaults
   left, so a braced open double quote with a `}` after it takes the
   right form; the single quote defaults right, so `{'` with a `}` after
   it takes the left. *)
Definition ddecay_str (k : dstyle) (openmark closemark : bool) : string :=
  match dc_decay cfg k with
  | DDSelf =>
      ((if openmark then one lbrace else EmptyString)
       ++ dtoken k
       ++ (if (closemark && negb openmark)%bool
           then one rbrace else EmptyString))%string
  | DDPair dfl l r =>
      if dfl then (if closemark then r else l)
      else (if openmark then l else r)
  end.

(* Whether an unbraced delimiter may open a span here.  Closing never
   asks this, so a quote may close wherever its neighbour is nonspace. *)
Definition dbare (k : dstyle) (before : option ascii) : bool :=
  match dsyntax_of k with
  | DBare => true
  | DBareAfterBreak => dopens_after before
  | _ => false
  end.

Definition is_delim (c : ascii) : bool :=
  match dstyle_of c with Some _ => true | None => false end.


(* Everything the scanner and the renderer assume about the table is
   derived from the instance's own side condition, so an instance is
   admissible or it does not exist. *)
Local Lemma drow_ok_of : forall k, drow_ok cfg k = true.
Proof. intros k. exact (dconfig_ok_row cfg k cfg_ok). Qed.

(* An enabled row has a token to write.  A width of zero would spell a
   delimiter as the empty string, which nothing could scan and nothing
   could close. *)
Lemma dwidth_nonzero : forall k, dwidth k <> 0.
Proof.
  intros k. pose proof (drow_ok_of k) as H.
  unfold drow_ok in H. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _]. apply negb_true_iff in H.
  unfold dwidth. destruct (dc_width cfg k); [discriminate|]. discriminate.
Qed.

(* Hence a row's token is a nonempty string: what a delimiter decays to
   always has something in it. *)
Lemma dtoken_nonempty : forall k, nonempty_str (dtoken k) = true.
Proof.
  intros k. unfold dtoken.
  destruct (dwidth k) as [|w] eqn:E; [destruct (dwidth_nonzero k E)|reflexivity].
Qed.

(* Its character is punctuation, so a backslash escapes it... *)
Lemma dchar_punct : forall k, is_punct (dchar k) = true.
Proof.
  intros k. pose proof (drow_ok_of k) as H.
  unfold drow_ok in H. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [_ H]. exact H.
Qed.

(* ...and it is not one the scanner claims, so `ilead` reaches the
   lookup at all. *)
Lemma dchar_free : forall k, dreserved (dchar k) = false.
Proof.
  intros k. pose proof (drow_ok_of k) as H.
  unfold drow_ok in H. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [_ H]. apply negb_true_iff in H. exact H.
Qed.

(* And a bare row's character is not the hyphen.  `ilead` claims that
   character before the lookup, so a row declaring itself bare and
   spelled with it would be read in its braced spelling and in no other.
   A braced row may be spelled with it, which is where djot's delete row
   lives. *)
Lemma dchar_bare_free :
  forall k,
    dsyntax_bare (dsyntax_of k) = true ->
    Ascii.eqb (dchar k) hyphen = false.
Proof.
  intros k H. pose proof (drow_ok_of k) as Hr.
  unfold drow_ok in Hr. apply andb_true_iff in Hr as [_ Hr].
  apply negb_true_iff, andb_false_iff in Hr as [Hr|Hr];
    [unfold dsyntax_of in H; rewrite H in Hr; discriminate|exact Hr].
Qed.

(* What the decay condition buys, in the form the scanner uses. *)
Lemma ddecay_str_nonempty :
  forall k om cm, nonempty_str (ddecay_str k om cm) = true.
Proof.
  intros k om cm. pose proof (drow_ok_of k) as H.
  unfold drow_ok in H. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [_ H].
  unfold ddecay_str. destruct (dc_decay cfg k) as [|dfl l r] eqn:E.
  - pose proof (dtoken_nonempty k) as Ht.
    destruct om; [reflexivity|].
    destruct (dtoken k); [discriminate|reflexivity].
  - cbn [ddecay_ok] in H. apply andb_true_iff in H as [Hl Hr].
    destruct dfl; [destruct cm; [exact Hr|exact Hl]|].
    destruct om; [exact Hl|exact Hr].
Qed.

Lemma dreserved_false :
  forall c,
    dreserved c = false ->
    is_bslash c = false /\ is_tick c = false
    /\ Ascii.eqb c lbrace = false /\ Ascii.eqb c rbrace = false
    /\ Ascii.eqb c lbrack = false /\ Ascii.eqb c rbrack = false
    /\ Ascii.eqb c bang = false /\ Ascii.eqb c dollar = false
    /\ Ascii.eqb c period = false /\ Ascii.eqb c lt = false.
Proof.
  intros c H. unfold dreserved in H.
  repeat (apply orb_false_iff in H as [H ?]). tauto.
Qed.

(* The lookup is by character, so a row it finds is spelled with the
   character that found it. *)
Lemma dstyle_of_char :
  forall c k, dstyle_of c = Some k -> dchar k = c.
Proof.
  intros c k H. unfold dstyle_of in H. rewrite dstyle_at_fast_eq in H.
  unfold dstyle_at in H.
  apply find_some in H as [_ H]. apply andb_true_iff in H as [_ H].
  apply Ascii.eqb_eq in H. exact H.
Qed.

(* And it only ever finds a row that is switched on. *)
Lemma dstyle_of_enabled :
  forall c k, dstyle_of c = Some k -> denabled_of k = true.
Proof.
  intros c k H. unfold dstyle_of in H. rewrite dstyle_at_fast_eq in H.
  unfold dstyle_at in H.
  apply find_some in H as [_ H]. apply andb_true_iff in H as [H _]. exact H.
Qed.

Lemma dstyle_of_dchar :
  forall k, denabled_of k = true -> dstyle_of (dchar k) = Some k.
Proof.
  intros k H. unfold dstyle_of. rewrite dstyle_at_fast_eq.
  exact (dstyle_at_dchar cfg k cfg_ok H).
Qed.


Local Lemma nl_one_char : nl = one nl_char.
Proof. reflexivity. Qed.

(* The braced spelling of a delimiter, which is the canonical one: it
   opens and closes on sight, so it needs no neighbouring byte to be read
   as a delimiter.  Both the renderer and the scanner inversion speak of
   it, and both go through `dtoken`, so a row wider than one character is
   written the way it is read. *)
Definition marked_open (k : dstyle) : string := (one lbrace ++ dtoken k)%string.

Definition marked_close (k : dstyle) (tail : string) : string :=
  (dtoken k ++ one rbrace ++ tail)%string.

(* The tail is what follows the close, so a close with nothing after it
   absorbs whatever text comes next.  This is the join the roundtrip
   rewrites with: `ci_src` closes on `EmptyString` and the scan wants the
   rest of the line in its place. *)
Lemma marked_close_app :
  forall k tail, (marked_close k EmptyString ++ tail)%string = marked_close k tail.
Proof.
  intros k tail. unfold marked_close.
  rewrite !append_assoc. reflexivity.
Qed.

(* The characters a `CIStr` must escape to survive reparsing: the
   reserved ones, the table's, and three claimed independently.

   `^` marks a footnote after `[`, but it is also the superscript row's
   character, so it cannot be reserved: no row may claim a reserved
   character.  The hyphen is djot's delete row character, so it cannot be
   reserved either, but the scanner dispatches on it for smart dashes
   under every table.  `:` can become a key connective.  Escaping one of
   these under a table that gives it no role costs an escape of
   punctuation, which decodes back to itself. *)
Definition needs_escape (c : ascii) : bool :=
  (dreserved c || is_delim c || Ascii.eqb c hat || Ascii.eqb c hyphen
   || Ascii.eqb c ":"%char)%bool.

(* Obligation 1: an escaped character must be one the decoder accepts.
   The fixed characters are punctuation by computation; the table's
   characters satisfy the obligation because an admissible row is
   spelled with punctuation. *)
Local Lemma dreserved_punct : forall c, dreserved c = true -> is_punct c = true.
Proof.
  intros [b0 b1 b2 b3 b4 b5 b6 b7] H.
  destruct b0, b1, b2, b3, b4, b5, b6, b7;
    vm_compute in H |- *; first [reflexivity | discriminate].
Qed.

Lemma needs_escape_punct : forall c, needs_escape c = true -> is_punct c = true.
Proof.
  intros c H. apply orb_true_iff in H as [H|H];
    [|apply Ascii.eqb_eq in H; subst c; reflexivity].
  apply orb_true_iff in H as [H|H];
    [|apply Ascii.eqb_eq in H; subst c; reflexivity].
  apply orb_true_iff in H as [H|H];
    [|apply Ascii.eqb_eq in H; subst c; reflexivity].
  apply orb_true_iff in H as [H|H]; [apply dreserved_punct, H|].
  unfold is_delim in H. destruct (dstyle_of c) as [k|] eqn:E; [|discriminate].
  rewrite <- (dstyle_of_char c k E). apply dchar_punct.
Qed.

(* Obligation 2: the escape character escapes itself, or a text ending in
   a backslash would decode as an escape of whatever followed. *)
Local Lemma needs_escape_backslash : needs_escape "\"%char = true.
Proof. reflexivity. Qed.

(* Obligation 3: a backtick in a `Str` must not reach the scanner bare,
   or it would open a verbatim span. *)
Lemma needs_escape_tick : forall c, is_tick c = true -> needs_escape c = true.
Proof.
  intros c H. unfold needs_escape, dreserved. rewrite H.
  rewrite orb_true_r, !orb_true_l. reflexivity.
Qed.

(* Obligation 4, the same for every delimiter the table claims, and for
   the braces that force one open or closed. *)
Local Lemma needs_escape_delim : forall c, is_delim c = true -> needs_escape c = true.
Proof.
  intros c H. unfold needs_escape. rewrite H.
  rewrite orb_true_r, orb_true_l. reflexivity.
Qed.

(* And the hyphen, which no table can decline: `ilead` dispatches it
   before the lookup. *)
Local Lemma needs_escape_hyphen : needs_escape hyphen = true.
Proof. unfold needs_escape. rewrite orb_true_r. reflexivity. Qed.

(* The footnote marker, for the same reason the brackets are here: `[^`
   is a construct, so a `^` after a `[` must not reach the scanner
   bare. *)
Local Lemma needs_escape_hat : needs_escape hat = true.
Proof. unfold needs_escape. rewrite orb_true_r. reflexivity. Qed.

Lemma needs_escape_lbrace : needs_escape lbrace = true.
Proof. reflexivity. Qed.

Local Lemma needs_escape_rbrace : needs_escape rbrace = true.
Proof. reflexivity. Qed.

(* And the same for the brackets, on which the scanner dispatches: a `[`
   in a `Str` would open a scope, and a `]` would close one that a later
   construct opened. *)
Local Lemma needs_escape_lbrack : needs_escape lbrack = true.
Proof. reflexivity. Qed.

Local Lemma needs_escape_rbrack : needs_escape rbrack = true.
Proof. reflexivity. Qed.

(* The `!` an image opens on.  Escaping it unconditionally lets a `Str`
   ending in `!` sit before a link without making it an image. *)
Local Lemma needs_escape_bang : needs_escape bang = true.
Proof. reflexivity. Qed.

(* A literal colon must not become a key connective when its line opens
   a paragraph.  The decoder reads `\:` as `:` with keys on or off, so the
   escape is emitted everywhere and rendering needs no block setting. *)
Local Lemma needs_escape_colon : needs_escape ":"%char = true.
Proof. unfold needs_escape. rewrite orb_true_r. reflexivity. Qed.

(* Inside a destination the scanner dispatches on two more characters,
   the parentheses that move its depth counter, and on none of the
   delimiters -- but escaping those too is harmless (an escape decodes to
   the character in either mode) and keeps one predicate ordered above
   the other. *)
Definition needs_escape_dest (c : ascii) : bool :=
  (needs_escape c || Ascii.eqb c lparen || Ascii.eqb c rparen)%bool.

Lemma needs_escape_dest_punct :
  forall c, needs_escape_dest c = true -> is_punct c = true.
Proof.
  intros c H. unfold needs_escape_dest in H.
  apply orb_true_iff in H as [H|H].
  - apply orb_true_iff in H as [H|H]; [apply needs_escape_punct, H|].
    apply Ascii.eqb_eq in H. subst c. reflexivity.
  - apply Ascii.eqb_eq in H. subst c. reflexivity.
Qed.

(* Could `pre` be an ordered list's number, so that a period after it
   followed by a space opens a list at the start of a line?  Decimal,
   one letter, or roman, as `Marker.v` reads them. *)
Local Definition marker_core (pre : string) : bool :=
  nonempty_str pre
  && (str_forallb is_digit pre
      || Nat.eqb (String.length pre) 1 && str_forallb is_alnum pre
      || str_forallb is_roman_lo pre || str_forallb is_roman_up pre).

(* A character `needs_escape` claims may go bare when the byte after it
   cannot complete a construct with it: a period that starts no ellipsis
   and ends no list number, a `!` whose `[` would be escaped anyway, a
   hyphen that starts no dash.  The line's end completes nothing either,
   so a run that ends its line (`at_end`) may leave its last character
   bare too, unless that period could end a list number.  A run's first
   character is always escaped, since it may start a line, where `- ` is
   a list marker.  `pre` is what the run has written so far, reversed. *)
Definition bare_ok (at_end : bool) (pre : string) (c : ascii) (rest : string)
  : bool :=
  match pre, rest with
  | EmptyString, _ => false
  | _, EmptyString =>
      at_end
      && ((Ascii.eqb c period && negb (marker_core pre))
          || Ascii.eqb c bang || Ascii.eqb c hyphen)
  | _, String d _ =>
      (Ascii.eqb c period && negb (Ascii.eqb d period)
       && negb (marker_core pre && Ascii.eqb d " "%char))
      || Ascii.eqb c bang
      || (Ascii.eqb c hyphen && negb (Ascii.eqb d hyphen))
  end.

Fixpoint escape_from (at_end : bool) (pre s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if needs_escape c && negb (bare_ok at_end pre c rest)
      then String "\"%char (String c (escape_from at_end (String c pre) rest))
      else String c (escape_from at_end (String c pre) rest)
  end.

(* A run followed by more of its line, and one that ends it. *)
Definition escape_str (s : string) : string := escape_from false EmptyString s.
Definition escape_end (s : string) : string := escape_from true EmptyString s.

Fixpoint escape_dest (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if needs_escape_dest c
      then String "\"%char (String c (escape_dest rest))
      else String c (escape_dest rest)
  end.

(* Verbatim delimiters use the least positive backtick-run length that
   does not occur in the content. *)
Local Fixpoint tick_runs_from (run : nat) (s : string) : list nat :=
  match s with
  | EmptyString => if Nat.eqb run 0 then [] else [run]
  | String c rest =>
      if is_tick c then tick_runs_from (S run) rest
      else if Nat.eqb run 0
           then tick_runs_from 0 rest
           else run :: tick_runs_from 0 rest
  end.

Local Definition tick_runs (s : string) : list nat := tick_runs_from 0 s.

Local Fixpoint first_missing (fuel candidate : nat) (runs : list nat) : nat :=
  match fuel with
  | 0 => candidate
  | S fuel' =>
      if existsb (Nat.eqb candidate) runs
      then first_missing fuel' (S candidate) runs
      else candidate
  end.

Definition verb_ticks (s : string) : nat :=
  first_missing (S (String.length s)) 1 (tick_runs s).

Local Lemma first_missing_nonzero :
  forall fuel n runs, n <> 0 -> first_missing fuel n runs <> 0.
Proof.
  induction fuel as [|fuel IH]; intros n runs Hn; cbn [first_missing].
  - exact Hn.
  - destruct (existsb (Nat.eqb n) runs); [apply IH; discriminate|exact Hn].
Qed.

Lemma verb_ticks_nonzero : forall s, verb_ticks s <> 0.
Proof. intros s. unfold verb_ticks. apply first_missing_nonzero. discriminate. Qed.

Definition starts_tick (s : string) : bool :=
  match s with String c _ => is_tick c | _ => false end.

Definition ends_tick (s : string) : bool := starts_tick (rev_string s).

Lemma starts_tick_app_l :
  forall a b, nonempty_str a = true -> starts_tick (a ++ b) = starts_tick a.
Proof. intros [|c a] b H; [discriminate|reflexivity]. Qed.

Lemma rev_nonempty_str :
  forall s, nonempty_str (rev_string s) = nonempty_str s.
Proof.
  intros [|c s]; [reflexivity|].
  rewrite rev_string_cons. destruct (rev_string s); reflexivity.
Qed.

Lemma ends_tick_cons_nonempty :
  forall c d s, ends_tick (String c (String d s)) = ends_tick (String d s).
Proof.
  intros c d s. unfold ends_tick. rewrite rev_string_cons.
  apply starts_tick_app_l. rewrite rev_nonempty_str. reflexivity.
Qed.

Local Lemma ends_tick_app_r :
  forall a b, nonempty_str b = true -> ends_tick (a ++ b) = ends_tick b.
Proof.
  intros a b Hb. unfold ends_tick. rewrite rev_string_app.
  apply starts_tick_app_l. rewrite rev_nonempty_str. exact Hb.
Qed.

Definition pad_verb (s : string) : string :=
  let left := if starts_tick s then " " else EmptyString in
  let right := if ends_tick s then " " else EmptyString in
  (left ++ s ++ right)%string.

Lemma pad_verb_nonempty :
  forall s, nonempty_str s = true -> nonempty_str (pad_verb s) = true.
Proof.
  intros s H. unfold pad_verb. destruct (starts_tick s); cbn [append];
    [reflexivity|]. destruct s; [discriminate|reflexivity].
Qed.

Lemma pad_verb_starts_nontick :
  forall s, nonempty_str s = true -> starts_tick (pad_verb s) = false.
Proof.
  intros s H. unfold pad_verb. destruct (starts_tick s) eqn:Hs;
    destruct (ends_tick s); cbn [append starts_tick]; try reflexivity.
  all: rewrite starts_tick_app_l by exact H; exact Hs.
Qed.

Lemma pad_verb_ends_nontick :
  forall s, nonempty_str s = true -> ends_tick (pad_verb s) = false.
Proof.
  intros s H. unfold pad_verb. destruct (starts_tick s);
    destruct (ends_tick s) eqn:He; cbn [append].
  - change (ends_tick (" " ++ (s ++ " ")) = false).
    rewrite ends_tick_app_r by (destruct s; [discriminate|reflexivity]).
    rewrite ends_tick_app_r by reflexivity. reflexivity.
  - rewrite append_empty_r. change (ends_tick (" " ++ s) = false).
    rewrite ends_tick_app_r by exact H. exact He.
  - rewrite ends_tick_app_r by reflexivity. reflexivity.
  - rewrite append_empty_r. exact He.
Qed.

Fixpoint ticks (n : nat) : string :=
  match n with 0 => EmptyString | S k => String tick (ticks k) end.

Lemma ticks_succ_r :
  forall n, ticks (S n) = (ticks n ++ String tick EmptyString)%string.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [ticks append]. rewrite <- IH. reflexivity.
Qed.

Definition verb_text (s : string) : string :=
  let d := ticks (verb_ticks s) in (d ++ pad_verb s ++ d)%string.

Fixpoint verb_safe_from (n run : nat) (s : string) : bool :=
  match s with
  | EmptyString => negb (Nat.eqb run n)
  | String c rest =>
      if is_tick c then verb_safe_from n (S run) rest
      else (negb (Nat.eqb run n) && verb_safe_from n 0 rest)%bool
  end.

Definition verb_safe (n : nat) (s : string) : bool :=
  verb_safe_from n 0 s.

Definition starts_space_tick (s : string) : bool :=
  match s with
  | String c (String d _) => (Ascii.eqb c " "%char && is_tick d)%bool
  | _ => false
  end.

(* Exactly the strings `trim_verb` can emit. *)
Definition verb_content_ok (s : string) : bool :=
  (no_nl s && negb (starts_space_tick s)
   && negb (starts_space_tick (rev_string s))
   && verb_safe (verb_ticks s) (pad_verb s))%bool.

(*
Canonical inlines
=================
*)

(* A bracket's own source: the `[`, with the `!` of an image.  Both the
   canonical rendering and the literal fallback put it back. *)
Definition bracket_open (image : bool) : string :=
  if image then String bang (one lbrack) else one lbrack.

(* A link's closing half: the `](`, the escaped destination, and the `)`,
   with whatever follows.  Written with a tail for the same reason
   `marked_close` is -- the scanner inversion needs to speak of the
   closer and its continuation as one string. *)
Definition link_close (dst tail : string) : string :=
  String rbrack (String lparen (escape_dest dst ++ String rparen tail)).

(* A reference link's closing half: the `]`, then `[`, the label and `]`.
   The label is not escaped -- the scanner's reference mode accumulates
   bytes literally until a `]` -- so `ci_ok` has to keep `]` out of it
   rather than escape it. *)
Definition ref_close (label tail : string) : string :=
  String rbrack (String lbrack (label ++ String rbrack tail)).

(* A wikilink's source: `[[target]]` or `[[target|alias]]`, with the `!`
   of an embed in front. *)
Definition wiki_text (embed : bool) (t : string) (al : option string)
  : string :=
  (bracket_open embed ++ one lbrack ++ t
   ++ match al with Some a => String vbar a | None => EmptyString end
   ++ one rbrack ++ one rbrack)%string.

(* A footnote reference's source.  A leaf: its label is source rather
   than inline content. *)
Definition note_text (label : string) : string :=
  String lbrack (String hat (label ++ one rbrack)).

(* An unescaped `]` would end the label early, while an odd trailing run
   of backslashes would protect the reference's closing bracket. *)
Fixpoint note_label_safe_from (esc : bool) (label : string) : bool :=
  match label with
  | EmptyString => negb esc
  | String c rest =>
      if esc then note_label_safe_from false rest
      else if Ascii.eqb c rbrack then false
      else note_label_safe_from (is_bslash c) rest
  end.

Definition note_label_safe : string -> bool := note_label_safe_from false.

(*
Autolinks
---------

`<...>` is a link to its own text, and the region decides which kind: an
email test, then a URL test.  Both search the whole region rather than
matching a shape, so an autolink is decided by two predicates, not by a
parser. *)

(* `/[^:]@/`: an `@` with a character before it that is not a colon.  The
   leading position cannot match, so `<@x>` is not an email. *)
Local Fixpoint auto_email_from (prev : option ascii) (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c rest =>
      match prev with
      | Some p =>
          if (Ascii.eqb c "@"%char && negb (Ascii.eqb p ":"%char))%bool
          then true else auto_email_from (Some c) rest
      | None => auto_email_from (Some c) rest
      end
  end.

Definition auto_email (s : string) : bool := auto_email_from None s.

(* `/[a-zA-Z]:/`: a letter immediately followed by a colon, anywhere.
   Not a scheme in the URI sense -- `<a:b>` is a link to `a:b` -- and the
   name says only what it tests. *)
Local Definition is_alpha (c : ascii) : bool :=
  ((Ascii.leb "a"%char c && Ascii.leb c "z"%char)
   || (Ascii.leb "A"%char c && Ascii.leb c "Z"%char))%bool.

(* The bytes a symbol name may contain: `[\w_+-]`. *)
Definition symbol_char (c : ascii) : bool :=
  (is_alpha c || (Ascii.leb "0"%char c && Ascii.leb c "9"%char)
   || Ascii.eqb c "_"%char || Ascii.eqb c "+"%char
   || Ascii.eqb c "-"%char)%bool.

Local Fixpoint auto_scheme (s : string) : bool :=
  match s with
  | String c ((String d _) as rest) =>
      if (is_alpha c && Ascii.eqb d ":"%char)%bool then true
      else auto_scheme rest
  | _ => false
  end.

(* The email test first.  A region failing both is not an autolink, and
   the brackets are literal. *)
Definition auto_node (s : string) : inline :=
  if auto_email s then EmailLink s else UrlLink s.

Definition auto_kind_ok (s : string) : bool :=
  (auto_email s || auto_scheme s)%bool.

(* An autolink is its own source, brackets included. *)
Definition auto_text (s : string) : string :=
  String lt (s ++ one gt).

(* What the region may hold and still come back: the pattern is
   `[^<>\s]+`, so nonempty and free of its own brackets and of
   whitespace.  Nothing inside is escaped -- the scanner accumulates the
   region byte for byte -- so this excludes rather than escapes, as a
   reference label does.

   Split in two because the nonemptiness is a fact about the whole
   region and the exclusions are a fact about every byte: the scan
   inversion consumes the region a byte at a time, and its tail is not
   nonempty. *)
Definition auto_region (s : string) : bool :=
  (no_ws s && no_char lt s && no_char gt s)%bool.

Definition auto_body_ok (s : string) : bool :=
  (nonempty_str s && auto_region s)%bool.

(*
Raw inline
----------

A verbatim span whose closing run is followed immediately by `{=format}`
is raw content in that format rather than code.  A math span is not:
`` $`x`{=html} `` stays math.

The format is nonempty and free of whitespace, braces and backticks.  It
is not attribute syntax: the raw check runs first, and no attribute spec
begins with `=`.  So one mode decides it, and `` `x`{=html=} `` is raw
with format `html=` rather than the highlight row the same bytes would
be anywhere else. *)

(* The source after the `{`, which the mode accumulates.  A format is
   what follows an `=`, so a spec that does not begin with one has
   already failed. *)
Definition eqchar : ascii := "="%char.

Definition raw_spec_ok (spec : string) : bool :=
  match spec with
  | String c rest => (Ascii.eqb c eqchar && nonempty_str rest)%bool
  | EmptyString => false
  end.

(* The same conditions on the format alone, which is what the canonical
   view has in hand.  `raw_spec_ok (String eqchar fmt)` is this, and the
   scan inversion is where the two meet. *)
Definition raw_fmt_ok (fmt : string) : bool :=
  (nonempty_str fmt && no_ws fmt && no_char lbrace fmt
   && no_char rbrace fmt && no_char tick fmt)%bool.

Definition raw_format (spec : string) : string :=
  match spec with String _ rest => rest | EmptyString => EmptyString end.

(* The bytes the pattern's character class excludes.  A `}` is not among
   them: it ends the spec, successfully or not. *)
Definition raw_stop (c : ascii) : bool :=
  (is_ws c || is_tick c || Ascii.eqb c lbrace)%bool.

(* What may follow a verbatim's closing run.  The `{` of a canonical
   delimiter may -- every one of them is spelled brace-first -- but a `{=`
   may not, since that is the raw spec and the verbatim would come back
   as raw content instead.  A `{` at the very end is excluded too: with
   nothing after it the scan is left in the raw mode rather than in the
   brace one, and the two states are equal only from the *next* byte on.
   Canonical source cannot spell one, since `escape_str` claims the
   brace. *)
Definition after_verb_next (s : string) : bool :=
  match s with
  | String c rest =>
      if Ascii.eqb c lbrace
      then match rest with
           | String d _ => negb (Ascii.eqb d eqchar)
           | EmptyString => false
           end
      else true
  | EmptyString => true
  end.

(* A raw span's own source: the verbatim, then the spec. *)
Definition raw_text (fmt s : string) : string :=
  (verb_text s ++ String lbrace (String "="%char (fmt ++ one rbrace)))%string.

(* One line's inline content, described by the source that determines it.
   One constructor per inline construct the roundtrip covers, exactly as
   `cblock` carries one per block construct. *)
Inductive cinline : Type :=
  | CIStr (s : string)
  | CIVerb (s : string)
  | CIDelim (k : dstyle) (kids : list cinline)
  (* a direct link or image: its label, and the destination it resolves
     to.  The label may be empty -- `[](u)` is a link in djot -- which is
     the one way this differs from a delimiter. *)
  | CILink (img : bool) (kids : list cinline) (dst : string)
  (* a reference link or image: its text and the label it resolves
     against.  The explicit spelling `[text][label]` is the canonical one
     because it is context-free: the collapsed `[text][]` reads its label
     off the text, so it cannot express a label the text does not spell. *)
  | CIRef (img : bool) (kids : list cinline) (label : string)
  | CINote (label : string)
  (* an autolink: its region, which is both its source and its target.
     A leaf for the reason a footnote reference is one -- the region is
     raw source rather than inline content -- and the kind is not a field
     because `auto_node` computes it from the region, exactly as the
     scanner does. *)
  | CIAuto (s : string)
  (* raw content in a named format, which is a verbatim plus its spec.
     The format is a field because it is source the scanner reads, not
     something computed from the content -- the one way this differs from
     `CIAuto`. *)
  | CIRaw (fmt s : string)
  (* a wikilink: two raw strings and the embed bit, a leaf for the
     footnote label's reason. *)
  | CIWiki (embed : bool) (target : string) (alias : option string).

Fixpoint ci_size (ci : cinline) : nat :=
  let go :=
    fix go (cis : list cinline) : nat :=
      match cis with
      | [] => 0
      | c :: rest => ci_size c + go rest
      end in
  match ci with
  | CIStr _ | CIVerb _ | CINote _ | CIAuto _ | CIRaw _ _ | CIWiki _ _ _ => 1
  | CIDelim _ kids | CILink _ kids _ | CIRef _ kids _ => S (go kids)
  end.

Fixpoint cis_size (cis : list cinline) : nat :=
  match cis with [] => 0 | c :: rest => ci_size c + cis_size rest end.

Lemma ci_size_delim :
  forall k kids, ci_size (CIDelim k kids) = S (cis_size kids).
Proof.
  intros k kids.
  assert (H : forall xs,
    (fix go (cis : list cinline) : nat :=
       match cis with
       | [] => 0
       | c :: rest => ci_size c + go rest
       end) xs = cis_size xs).
  { induction xs as [|c rest IH]; cbn [cis_size]; [reflexivity|].
    rewrite IH. reflexivity. }
  cbn [ci_size]. rewrite H. reflexivity.
Qed.

Lemma ci_size_link :
  forall img kids dst, ci_size (CILink img kids dst) = S (cis_size kids).
Proof.
  intros img kids dst. exact (ci_size_delim DEmph kids).
Qed.

Lemma ci_size_ref :
  forall img kids label, ci_size (CIRef img kids label) = S (cis_size kids).
Proof.
  intros img kids label. exact (ci_size_delim DEmph kids).
Qed.

Lemma ci_size_pos : forall ci, 0 < ci_size ci.
Proof.
  intros [s|s|k kids|img kids dst|img kids label|label|s|f s|e t al];
    cbn [ci_size]; lia.
Qed.

(* The last byte of `s`, or `prev` when `s` is empty. *)
Fixpoint str_last (s : string) (prev : option ascii) : option ascii :=
  match s with
  | EmptyString => prev
  | String c rest => str_last rest (Some c)
  end.

(* Source text.

   Not `concat (map ...)` of a per-element function: a delimiter's
   spelling depends on its neighbours, so `Emph [CIStr "b"]` renders
   `_b_` at a line start but `{_b_}` inside `a_b_c`.  One byte on each
   side is the whole of the context a delimiter rule consults, since
   `can_open` and `can_close` each test a single neighbouring character,
   and the byte to the right is available from the unconsumed tail. *)
Fixpoint ci_src (ci : cinline) : string :=
  let go :=
    fix go (cis : list cinline) : string :=
      match cis with
      | [] => EmptyString
      | c :: rest => (ci_src c ++ go rest)%string
      end in
  match ci with
  | CIStr s => escape_str s
  | CIVerb s => verb_text s
  | CIDelim k kids =>
      (marked_open k ++ (go kids ++ marked_close k EmptyString))%string
  | CILink img kids dst =>
      (bracket_open img ++ (go kids ++ link_close dst EmptyString))%string
  | CIRef img kids label =>
      (bracket_open img ++ (go kids ++ ref_close label EmptyString))%string
  | CINote label => note_text label
  | CIAuto s => auto_text s
  | CIRaw fmt s => raw_text fmt s
  | CIWiki embed t al => wiki_text embed t al
  end.

Fixpoint ci_text (cis : list cinline) : string :=
  match cis with
  | [] => EmptyString
  | ci :: rest => (ci_src ci ++ ci_text rest)%string
  end.

(* A list's text where the list ends its line or not: a trailing run
   that ends the line may leave its last character bare. *)
Fixpoint ci_text_at (at_end : bool) (cis : list cinline) : string :=
  match cis with
  | [] => EmptyString
  | [CIStr s] => escape_from at_end EmptyString s
  | ci :: rest => (ci_src ci ++ ci_text_at at_end rest)%string
  end.

Definition ci_line (cis : list cinline) : string := ci_text_at true cis.

Lemma ci_text_at_cons2 :
  forall b c c' rest,
    ci_text_at b (c :: c' :: rest) = (ci_src c ++ ci_text_at b (c' :: rest))%string.
Proof. intros b [] c' rest; reflexivity. Qed.

Lemma ci_text_at_last :
  forall b c, ci_text_at b [c]
    = match c with CIStr s => escape_from b EmptyString s | _ => ci_src c end.
Proof. intros b []; cbn [ci_text_at]; try apply append_empty_r; reflexivity. Qed.

Lemma ci_text_at_false : forall cis, ci_text_at false cis = ci_text cis.
Proof.
  induction cis as [|c rest IH]; [reflexivity|].
  destruct rest as [|c' rest'].
  - rewrite ci_text_at_last. cbn [ci_text]. rewrite append_empty_r.
    destruct c; reflexivity.
  - rewrite ci_text_at_cons2, IH. reflexivity.
Qed.

(* The traversal inside [ci_src] is [ci_text]. *)
Local Lemma ci_src_children : forall xs,
  (fix go (cis : list cinline) : string :=
     match cis with
     | [] => EmptyString
     | c :: rest => (ci_src c ++ go rest)%string
     end) xs = ci_text xs.
Proof.
  induction xs as [|c rest IH]; cbn [ci_text]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma ci_src_delim :
  forall k kids,
    ci_src (CIDelim k kids)
    = (marked_open k ++ (ci_text kids ++ marked_close k EmptyString))%string.
Proof.
  intros k kids.
  cbn [ci_src]. rewrite ci_src_children. reflexivity.
Qed.

Lemma ci_src_link :
  forall img kids dst,
    ci_src (CILink img kids dst)
    = (bracket_open img ++ (ci_text kids ++ link_close dst EmptyString))%string.
Proof.
  intros img kids dst.
  cbn [ci_src]. rewrite ci_src_children. reflexivity.
Qed.

Lemma ci_src_ref :
  forall img kids label,
    ci_src (CIRef img kids label)
    = (bracket_open img ++ (ci_text kids ++ ref_close label EmptyString))%string.
Proof.
  intros img kids label.
  cbn [ci_src]. rewrite ci_src_children. reflexivity.
Qed.

(* The AST the parser builds from that text. *)
Fixpoint ci_ast (ci : cinline) : node inline :=
  let go :=
    fix go (cis : list cinline) : inlines :=
      match cis with
      | [] => []
      | c :: rest => ci_ast c :: go rest
      end in
  match ci with
  | CIStr s => mk (Str s)
  | CIVerb s => mk (Verbatim s)
  | CIDelim k kids => mk (dnode k (go kids))
  | CILink img kids dst => mk (bnode img (go kids) (Direct dst))
  | CIRef img kids label => mk (bnode img (go kids) (Reference label))
  | CINote label => mk (FootnoteReference label)
  | CIAuto s => mk (auto_node s)
  | CIRaw fmt s => mk (RawInline fmt s)
  | CIWiki embed t al => mk (Ext_wikilink embed t al)
  end.

Definition ci_inlines (cis : list cinline) : inlines := map ci_ast cis.

(* The traversal inside [ci_ast] is [ci_inlines]. *)
Local Lemma ci_ast_children : forall xs,
  (fix go (cis : list cinline) : inlines :=
     match cis with
     | [] => []
     | c :: rest => ci_ast c :: go rest
     end) xs = ci_inlines xs.
Proof.
  induction xs as [|c rest IH]; cbn [ci_inlines map]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma ci_ast_delim :
  forall k kids, ci_ast (CIDelim k kids) = mk (dnode k (ci_inlines kids)).
Proof.
  intros k kids.
  cbn [ci_ast]. rewrite ci_ast_children. reflexivity.
Qed.

Lemma ci_ast_link :
  forall img kids dst,
    ci_ast (CILink img kids dst)
    = mk (bnode img (ci_inlines kids) (Direct dst)).
Proof.
  intros img kids dst.
  cbn [ci_ast]. rewrite ci_ast_children. reflexivity.
Qed.

Lemma ci_ast_ref :
  forall img kids label,
    ci_ast (CIRef img kids label)
    = mk (bnode img (ci_inlines kids) (Reference label)).
Proof.
  intros img kids label.
  cbn [ci_ast]. rewrite ci_ast_children. reflexivity.
Qed.

Local Lemma ci_line_nil : ci_line [] = EmptyString.
Proof. reflexivity. Qed.

Local Lemma ci_line_str : forall s, ci_line [CIStr s] = escape_end s.
Proof. reflexivity. Qed.

(*
Renderability
-------------
*)

(* Which adjacent pairs have separable source.  Two `Str`s would merge,
   as would two verbatims' delimiter runs, or a verbatim and raw content,
   which opens with a backtick run too.  A verbatim before a delimiter
   spelled with `=` would read as a raw spec: `` `x`{=a=} `` is raw
   content in format `a=`.  That exclusion is on the row's character,
   since the table is a parameter. *)
Definition ci_pair_ok (a b : cinline) : bool :=
  match a, b with
  | CIStr _, CIStr _ => false
  | CIVerb _, CIVerb _ => false
  | CIVerb _, CIDelim k _ => negb (Ascii.eqb (dchar k) eqchar)
  (* raw content opens with a backtick run of its own, so it merges with
     a verbatim before it exactly as a second verbatim would *)
  | CIVerb _, CIRaw _ _ => false
  | _, _ => true
  end.

(* Whether a run's source begins with a `[` that is not an image's.  At
   the start of a link's text such a `[` is the second bracket of a
   wikilink, so with wikilinks on a canonical link or reference may not
   begin with one (wikilink spec, section 6). *)
Local Definition ci_lbrack_head (c : cinline) : bool :=
  match c with
  | CILink false _ _ | CIRef false _ _ | CINote _ | CIWiki false _ _ => true
  | _ => false
  end.

Definition cis_lbrack_head (cis : list cinline) : bool :=
  match cis with c :: _ => ci_lbrack_head c | [] => false end.

Definition bracket_kids_ok (kids : list cinline) : bool :=
  negb (wikilinks_enabled && cis_lbrack_head kids).

(* One half of a canonical wikilink: nothing the region scan gives a
   role, and no line break. *)
Definition wiki_part_ok (s : string) : bool :=
  (no_char rbrack s && no_char vbar s && no_char bslash s && no_nl s)%bool.

(* The canonical view's conditions on one inline.  A `Str` is nonempty and
   newline-free.  An empty verbatim is excluded although the parser can
   build one: its source is two adjacent delimiter runs, closed only by
   what follows, so representing it would take a condition on the whole
   paragraph.  `Verbatim ""` in a one-line paragraph does round-trip; it
   is outside the view. *)
Fixpoint ci_ok (ci : cinline) : bool :=
  let go :=
    fix go (cis : list cinline) : bool :=
      match cis with
      | [] => true
      | c :: rest => (ci_ok c && go rest)%bool
      end in
  let sep :=
    fix sep (cis : list cinline) : bool :=
      match cis with
      | a :: ((b :: _) as rest) => ci_pair_ok a b && sep rest
      | _ => true
      end in
  match ci with
  | CIStr s => nonempty_str s && no_nl s
  | CIVerb s => nonempty_str s && verb_content_ok s
  (* The row has to be one the table in force actually has: `ci_src`
     spells a switched-off row exactly as a switched-on one, and the
     scanner would read it back as text.  This is what makes "which
     containers exist" a setting rather than a fixed list -- turning a
     row off removes it from the canonical view too. *)
  | CIDelim k kids =>
      (denabled_of k && nonempty kids && go kids && sep kids)%bool
  (* A destination holding a line break cannot round-trip: the scanner
     drops the break rather than recording it, so the rendering would
     come back shorter.  Everything else the scanner dispatches on is
     escaped by `escape_dest`. *)
  | CILink _ kids dst =>
      (no_nl dst && go kids && sep kids && bracket_kids_ok kids)%bool
  (* A label reaches the AST normalized, so only an already-normalized one
     round-trips; `]` would end it early, and an empty one is the
     collapsed spelling, whose label comes from the text instead. *)
  | CIRef _ kids label =>
      (nonempty_str label && no_char rbrack label
       && String.eqb (normalize_label label) label
       && go kids && sep kids && bracket_kids_ok kids)%bool
  | CINote label =>
      (notes_enabled && note_label_safe label
       && String.eqb (normalize_label label) label)%bool
  (* The region has to be one the pattern accepts and one of the two
     tests claims: a region that fails them is not an autolink but the
     literal text of its own brackets, which is a `CIStr` instead. *)
  | CIAuto s => (auto_body_ok s && auto_kind_ok s)%bool
  (* The content is a verbatim's, spelled by the same machinery and so
     under the same conditions.  The format is nonempty and free of
     whitespace, braces and backticks, and is read raw, so it cannot be
     escaped. *)
  | CIRaw fmt s =>
      (raw_inline_enabled && nonempty_str s
       && verb_content_ok s && raw_fmt_ok fmt)%bool
  (* An empty target is text (wikilink spec, 3.3), and anything the
     region scan dispatches on would end or split it. *)
  | CIWiki _ t al =>
      (wikilinks_enabled && nonempty_str t && wiki_part_ok t
       && match al with Some a => wiki_part_ok a | None => true end)%bool
  end.

Lemma ci_ok_raw :
  forall fmt s,
    ci_ok (CIRaw fmt s)
    = (raw_inline_enabled && nonempty_str s
       && verb_content_ok s && raw_fmt_ok fmt)%bool.
Proof. reflexivity. Qed.

Lemma ci_ok_auto :
  forall s, ci_ok (CIAuto s) = (auto_body_ok s && auto_kind_ok s)%bool.
Proof. reflexivity. Qed.

Lemma ci_ok_wiki :
  forall embed t al,
    ci_ok (CIWiki embed t al)
    = (wikilinks_enabled && nonempty_str t && wiki_part_ok t
       && match al with Some a => wiki_part_ok a | None => true end)%bool.
Proof. reflexivity. Qed.

Lemma ci_ok_note :
  forall label,
    ci_ok (CINote label)
    = (notes_enabled && note_label_safe label
       && String.eqb (normalize_label label) label)%bool.
Proof. reflexivity. Qed.

(* Pairwise source separation: adjacent strings merge, and adjacent
   verbatim spans merge their delimiter runs. *)
Fixpoint ci_sep_ok (cis : list cinline) : bool :=
  match cis with
  | a :: ((b :: _) as rest) => ci_pair_ok a b && ci_sep_ok rest
  | _ => true
  end.

Definition cis_ok (cis : list cinline) : bool :=
  forallb ci_ok cis && ci_sep_ok cis.

(* The two traversals inside [ci_ok] are [forallb ci_ok] and
   [ci_sep_ok]. *)
Local Lemma ci_ok_children : forall xs,
  (fix go (cis : list cinline) : bool :=
     match cis with
     | [] => true
     | c :: rest => (ci_ok c && go rest)%bool
     end) xs = forallb ci_ok xs.
Proof.
  induction xs as [|c rest IH]; cbn [forallb]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Local Lemma ci_sep_children : forall xs,
  (fix sep (cis : list cinline) : bool :=
     match cis with
     | a :: ((b :: _) as rest) => ci_pair_ok a b && sep rest
     | _ => true
     end) xs = ci_sep_ok xs.
Proof.
  induction xs as [|a [|b rest] IH]; cbn [ci_sep_ok]; [reflexivity..|].
  rewrite IH. reflexivity.
Qed.

Lemma ci_ok_delim :
  forall k kids,
    ci_ok (CIDelim k kids)
    = (denabled_of k && nonempty kids && cis_ok kids)%bool.
Proof.
  intros k kids.
  cbn [ci_ok]. rewrite ci_ok_children, ci_sep_children. unfold cis_ok.
  repeat rewrite andb_assoc. reflexivity.
Qed.

Lemma ci_ok_link :
  forall img kids dst,
    ci_ok (CILink img kids dst)
    = (no_nl dst && cis_ok kids && bracket_kids_ok kids)%bool.
Proof.
  intros img kids dst.
  cbn [ci_ok]. rewrite ci_ok_children, ci_sep_children. unfold cis_ok.
  repeat rewrite andb_assoc. reflexivity.
Qed.

Lemma ci_ok_ref :
  forall img kids label,
    ci_ok (CIRef img kids label)
    = (nonempty_str label && no_char rbrack label
       && String.eqb (normalize_label label) label && cis_ok kids
       && bracket_kids_ok kids)%bool.
Proof.
  intros img kids label.
  cbn [ci_ok]. rewrite ci_ok_children, ci_sep_children. unfold cis_ok.
  repeat rewrite andb_assoc. reflexivity.
Qed.

(* Nonemptiness of a line's content is not a separate obligation: the
   block layer already asks that a paragraph's rendered lines are
   nonblank, and only `[]` renders blank. *)
Local Lemma cis_nonempty_of_line :
  forall cis, nonempty_str (ci_line cis) = true -> nonempty cis = true.
Proof.
  intros [|c rest] H; [rewrite ci_line_nil in H; discriminate | reflexivity].
Qed.

(* The form the block layer supplies it in: `para_ok` and `heading_ok`
   both carry `forallb line_ok` over the rendered lines. *)
Lemma cis_nonempty_of_lines :
  forall lss,
    forallb line_ok (map ci_line lss) = true ->
    forallb nonempty lss = true.
Proof.
  induction lss as [|cis rest IH]; [reflexivity|].
  cbn [map forallb]. intros H. apply andb_true_iff in H as [Hl Hr].
  rewrite (cis_nonempty_of_line cis
             (nonblank_nonempty _ (line_ok_nonblank _ Hl))).
  exact (IH Hr).
Qed.

(* The canonical view's paragraph, laid out the same way. *)
Fixpoint ci_para (lss : list (list cinline)) : inlines :=
  match lss with
  | [] => []
  | [cis] => ci_inlines cis
  | cis :: rest => (ci_inlines cis ++ mk SoftBreak :: ci_para rest)%list
  end.

Lemma ci_para_one : forall cis, ci_para [cis] = ci_inlines cis.
Proof. reflexivity. Qed.

Lemma ci_para_cons2 :
  forall cis cis2 rest,
    ci_para (cis :: cis2 :: rest)
    = (ci_inlines cis ++ mk SoftBreak :: ci_para (cis2 :: rest))%list.
Proof. reflexivity. Qed.

(*
The renderer
============
*)

(* A node's attributes follow it as a spec, which is where the scanner
   reads them from.  Matching the empty set apart keeps an unattributed
   node's text exactly its contents' text. *)
Fixpoint inline_text (il : inline) : string :=
  let go :=
    fix go (ns : inlines) : string :=
      match ns with
      | [] => EmptyString
      | Node _ [] x :: rest => (inline_text x ++ go rest)%string
      | Node _ a x :: rest => (inline_text x ++ attr_spec a ++ go rest)%string
      end in
  let marked (k : dstyle) (ns : inlines) :=
    (marked_open k ++ (go ns ++ marked_close k EmptyString))%string in
  match il with
  | Str s => escape_str s
  | Verbatim s => verb_text s
  | Symbol s => (one ":"%char ++ s ++ one ":"%char)%string
  | Emph ns => marked DEmph ns
  | Strong ns => marked DStrong ns
  | Superscript ns => marked DSuper ns
  | Subscript ns => marked DSub ns
  | Highlight ns => marked DMark ns
  | Insert ns => marked DInsert ns
  | Delete ns => marked DDelete ns
  | Quoted SingleQuotes ns => marked DSQuote ns
  | Quoted DoubleQuotes ns => marked DDQuote ns
  | Link ns (Direct dst) =>
      (bracket_open false ++ (go ns ++ link_close dst EmptyString))%string
  | Image ns (Direct dst) =>
      (bracket_open true ++ (go ns ++ link_close dst EmptyString))%string
  | Link ns (Reference label) =>
      (bracket_open false ++ (go ns ++ ref_close label EmptyString))%string
  | Image ns (Reference label) =>
      (bracket_open true ++ (go ns ++ ref_close label EmptyString))%string
  | FootnoteReference label => note_text label
  (* both kinds render as their own region: which one it is was computed
     from that region and is recovered by computing it again *)
  | UrlLink s | EmailLink s => auto_text s
  (* raw content is its verbatim plus the spec that named its format *)
  | RawInline fmt s => raw_text fmt s
  | Ext_wikilink embed t al => wiki_text embed t al
  | Math InlineMath s => (one "$"%char ++ verb_text s)%string
  | Math DisplayMath s => (one "$"%char ++ one "$"%char ++ verb_text s)%string
  (* a span is its text in brackets; the attributes that make it one are
     the node's, which `go` appends *)
  | Span ns => (one "["%char ++ go ns ++ one "]"%char)%string
  | NonBreakingSpace => String bslash (one " "%char)
  (* a break inside a container: `inline_lines` owns the breaks between
     top-level inlines, and a paragraph splits these off as well *)
  | SoftBreak => one "010"%char
  | HardBreak => String bslash (one "010"%char)
  end.

Lemma ci_ast_attrs : forall ci, node_attrs (ci_ast ci) = [].
Proof. destruct ci; reflexivity. Qed.

Lemma inline_text_ci_ast : forall ci, inline_text (node_contents (ci_ast ci)) = ci_src ci.
Proof.
  fix IH 1. intro ci.
  destruct ci as [s|s|k kids|img kids dst|rimg rkids rlabel|label|a|rf rv|we wt wal];
    [reflexivity|reflexivity| | | |reflexivity
    |cbn [ci_ast ci_src]; unfold auto_node;
     destruct (auto_email a); reflexivity
    |cbn [ci_ast ci_src node_contents mk inline_text]; reflexivity
    |reflexivity].
  - destruct k; cbn [ci_ast ci_src dnode node_contents inline_text].
    all: cbn [inline_text node_contents mk]; f_equal; f_equal; f_equal;
      induction kids as [|c rest IHkids]; [reflexivity|]; cbn;
      destruct (ci_ast c) as [p a x] eqn:E;
      pose proof (ci_ast_attrs c) as Ha; rewrite E in Ha; cbn [node_attrs] in Ha; subst a;
      pose proof (IH c) as Hc; rewrite E in Hc;
      cbn [node_contents] in Hc; rewrite Hc, IHkids; reflexivity.
  - cbn [ci_ast ci_src node_contents inline_text mk bnode].
    destruct img;
      (cbn [bnode inline_text]; f_equal; f_equal;
       induction kids as [|c rest IHkids]; [reflexivity|]; cbn;
       destruct (ci_ast c) as [p a x] eqn:E;
      pose proof (ci_ast_attrs c) as Ha; rewrite E in Ha; cbn [node_attrs] in Ha; subst a;
       pose proof (IH c) as Hc; rewrite E in Hc;
       cbn [node_contents] in Hc; rewrite Hc, IHkids; reflexivity).
  - cbn [ci_ast ci_src node_contents inline_text mk bnode].
    destruct rimg;
      (cbn [bnode inline_text]; f_equal; f_equal;
       induction rkids as [|c rest IHkids]; [reflexivity|]; cbn;
       destruct (ci_ast c) as [p a x] eqn:E;
      pose proof (ci_ast_attrs c) as Ha; rewrite E in Ha; cbn [node_attrs] in Ha; subst a;
       pose proof (IH c) as Hc; rewrite E in Hc;
       cbn [node_contents] in Hc; rewrite Hc, IHkids; reflexivity).
Qed.

(* Does the line end here?  A hard break writes a backslash after the
   text, so it does not count. *)
Definition line_ends (ils : inlines) : bool :=
  match ils with
  | [] => true
  | Node _ _ SoftBreak :: _ => true
  | _ => false
  end.

(* Recover the lines of a paragraph from its inlines: `Str` extends the
   current line, `SoftBreak` ends it, and `HardBreak` ends it with a
   backslash. *)
Fixpoint inline_lines (ils : inlines) (cur : string) : list string :=
  match ils with
  | [] => [cur]
  | Node _ _ SoftBreak :: rest => cur :: inline_lines rest EmptyString
  | Node _ _ HardBreak :: rest =>
      (cur ++ one bslash)%string :: inline_lines rest EmptyString
  | Node _ [] (Str s) :: rest =>
      inline_lines rest (cur ++ escape_from (line_ends rest) EmptyString s)
  | Node _ [] il :: rest => inline_lines rest (cur ++ inline_text il)
  | Node _ a il :: rest => inline_lines rest (cur ++ (inline_text il ++ attr_spec a))
  end.

Local Lemma inline_lines_softbreak :
  forall rest cur,
    inline_lines (mk SoftBreak :: rest) cur = cur :: inline_lines rest EmptyString.
Proof. reflexivity. Qed.

Local Lemma line_ends_ci_ast :
  forall ci rest, line_ends (ci_ast ci :: rest) = false.
Proof.
  intros ci rest.
  destruct ci as [s|s|k kids|img kids dst|rimg rkids rlabel|label|a|rf rv|we wt wal];
    try reflexivity.
  - rewrite ci_ast_delim. destruct k; reflexivity.
  - rewrite ci_ast_link. destruct img; reflexivity.
  - rewrite ci_ast_ref. destruct rimg; reflexivity.
  - cbn [ci_ast]. unfold auto_node. destruct (auto_email a); reflexivity.
Qed.

(* A run's text depends on whether the line ends after it; nothing
   else's does. *)
Local Lemma inline_lines_ci_ast :
  forall ci rest cur,
    match ci with CIStr _ => line_ends rest = false | _ => True end ->
    inline_lines (ci_ast ci :: rest) cur
    = inline_lines rest (cur ++ ci_src ci).
Proof.
  intros ci rest cur Hrest.
  destruct ci as [s|s|k kids|img kids dst|rimg rkids rlabel|label|a|rf rv|we wt wal];
    [cbn [ci_ast ci_src mk inline_lines]; rewrite Hrest; reflexivity
    |reflexivity| | | |reflexivity
    |cbn [ci_ast ci_src]; unfold auto_node;
     destruct (auto_email a); reflexivity
    |cbn [ci_ast ci_src node_contents mk inline_text]; reflexivity
    |reflexivity].
  - rewrite ci_ast_delim, <- inline_text_ci_ast.
    destruct k; reflexivity.
  - rewrite ci_ast_link, <- inline_text_ci_ast, ci_ast_link.
    destruct img; reflexivity.
  - rewrite ci_ast_ref, <- inline_text_ci_ast, ci_ast_ref.
    destruct rimg; reflexivity.
Qed.

(** Rendering a canonical line's inlines appends its text and consumes
    nothing else, which is what makes the paragraph case an induction. *)
Lemma inline_lines_ci_inlines :
  forall cis cur rest,
    line_ends rest = true ->
    inline_lines (ci_inlines cis ++ rest)%list cur
    = inline_lines rest (cur ++ ci_line cis).
Proof.
  intros cis cur rest Hrest.
  induction cis as [|c cs IH] in cur |- *.
  - cbn [ci_inlines ci_line ci_text_at app map].
    rewrite append_empty_r. reflexivity.
  - unfold ci_line in *. destruct cs as [|c' cs'].
    + rewrite ci_text_at_last. cbn [ci_inlines map app].
      destruct c; [cbn [ci_ast mk inline_lines]; rewrite Hrest; reflexivity|..];
        rewrite inline_lines_ci_ast by exact I; reflexivity.
    + rewrite ci_text_at_cons2. cbn [ci_inlines map app].
      rewrite inline_lines_ci_ast
        by (destruct c; try exact I; apply line_ends_ci_ast).
      change (ci_ast c' :: map ci_ast cs' ++ rest)%list
        with (ci_inlines (c' :: cs') ++ rest)%list.
      rewrite IH, append_assoc. reflexivity.
Qed.

Local Lemma inline_lines_ci_para :
  forall rest cis cur,
    forallb cis_ok (cis :: rest) = true ->
    forallb nonempty (cis :: rest) = true ->
    inline_lines (ci_para (cis :: rest)) cur
    = (cur ++ ci_line cis) :: map ci_line rest.
Proof.
  induction rest as [|cis2 rest' IH]; intros cis cur Hok Hne;
    cbn [forallb] in Hok, Hne;
    apply andb_true_iff in Hok as [Hc Hr];
    apply andb_true_iff in Hne as [Hn Hnr].
  - rewrite ci_para_one. cbn [map].
    rewrite <- (app_nil_r (ci_inlines cis)).
    rewrite inline_lines_ci_inlines by reflexivity.
    reflexivity.
  - rewrite ci_para_cons2.
    rewrite inline_lines_ci_inlines by reflexivity.
    rewrite inline_lines_softbreak.
    rewrite IH by assumption.
    reflexivity.
Qed.

(** The renderer emits exactly the canonical lines. *)
Corollary inline_lines_ci :
  forall lss,
    forallb cis_ok lss = true -> forallb nonempty lss = true ->
    nonempty lss = true ->
    inline_lines (ci_para lss) EmptyString = map ci_line lss.
Proof.
  intros [|cis rest] Hok Hne Hlss; [discriminate|].
  rewrite inline_lines_ci_para by assumption. reflexivity.
Qed.

End WithTable.
