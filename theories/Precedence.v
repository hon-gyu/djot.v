(* ai-disclosure: autonomous *)

(* The reference's precedence rules for delimiters and brackets (syntax
   reference, "Precedence"), stated as a reading of a paragraph's bytes
   and independent of the scanner: the tokens, the readings the rules
   allow, the proof that exactly one exists, and the tree it describes.
   `InlinePrecedence.v` proves the scanner builds that tree. *)

From Stdlib Require Import String Ascii List Bool Lia Arith Sorted.
From DjotV Require Import Strings Ast Attributes InlineTable InlineView.
Import ListNotations.

Local Open Scope string_scope.

Section WithTable.
Context {T : dtable}.

(*
Tokens
======

The rows covered here are the ones whose unmatched token is its own
text: `_ * ^ ~`, written bare or in braces, and `= +`, written only in
braces, in djot's table.  The quotes are left out: an unmatched quote is
a curly quote, and whether one may open depends on the byte before it.
The hyphen is left out too: a run of dashes claims it first. *)

Definition self_row (k : dstyle) : bool :=
  match dsyntax_of k, dc_decay cfg k with
  | (DBare | DBraced), DDSelf => true
  | _, _ => false
  end.

(* Whether a row's token may open without braces. *)
Definition bare_opens (k : dstyle) : bool :=
  match dsyntax_of k with DBare => true | _ => false end.

(* The bytes a line is drawn from: the characters of those rows, the
   braces, the brackets, the backtick, `<`, `:` while tags are off, and
   bytes that no row and no other syntax claims, the parens among them.  A paren is not a row's character
   here, since a destination counts parens.  The newline ends the
   line; the `$` is drawn on while dollar math is off, and a hole's `%`
   is not drawn on while holes are on. *)
Definition in_alphabet (c : ascii) : bool :=
  (negb (Ascii.eqb c nl_char)
   && (Ascii.eqb c lbrace || Ascii.eqb c rbrace || Ascii.eqb c lbrack
       || Ascii.eqb c rbrack || is_tick c || Ascii.eqb c lt
       || (Ascii.eqb c ":"%char && negb tags_enabled)
       || (Ascii.eqb c dollar && negb dollar_math_enabled)
       || (negb (dreserved c) && negb (holes_enabled && Ascii.eqb c percent)))
   && negb (Ascii.eqb c hyphen)
   && match dstyle_of c with
      | Some k => self_row k && negb (Ascii.eqb c lparen || Ascii.eqb c rparen)
      | None => true
      end)%bool.

Definition starts_row (s : string) : bool :=
  match s with String d _ => is_delim d | EmptyString => false end.

Definition starts_with (c : ascii) (s : string) : bool :=
  match s with String d _ => Ascii.eqb d c | EmptyString => false end.

(* The format of a raw spec `{=FORMAT}` that `s` begins with (R1): a
   nonempty run of bytes that are not whitespace, a backtick, a brace or
   the newline. *)
Fixpoint fmt_go (s : string) : option string :=
  match s with
  | EmptyString => None
  | String c r =>
      if Ascii.eqb c rbrace then Some EmptyString
      else if (raw_stop c || Ascii.eqb c nl_char)%bool then None
      else option_map (String c) (fmt_go r)
  end.

Definition raw_spec (s : string) : option string :=
  match s with
  | String b (String e r) =>
      if (Ascii.eqb b lbrace && Ascii.eqb e eqchar)%bool
      then match fmt_go r with Some (String c f) => Some (String c f) | _ => None end
      else None
  | _ => None
  end.

(* Whether a byte ends an autolink candidate: the `>`, whitespace, a
   second `<`, or the end of the line (A2). *)
Definition auto_stop (c : ascii) : bool :=
  (Ascii.eqb c gt || is_ws c || Ascii.eqb c lt || Ascii.eqb c nl_char)%bool.

(* The region of an autolink candidate, and the byte that ended it. *)
Fixpoint auto_go (s : string) : string * option ascii :=
  match s with
  | EmptyString => (EmptyString, None)
  | String c r =>
      if auto_stop c then (EmptyString, Some c)
      else let '(src, stop) := auto_go r in (String c src, stop)
  end.

(* Whether a candidate's region holds no backslash: inside it a backslash
   is a byte. *)
Fixpoint auto_clean (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c r => if auto_stop c then true else (negb (is_bslash c) && auto_clean r)%bool
  end.

(* The run of symbol characters a string begins with. *)
Fixpoint symbol_run (s : string) : nat :=
  match s with
  | String c r => if symbol_char c then S (symbol_run r) else 0
  | EmptyString => 0
  end.

(* Whether what follows a `:` decides at once: no symbol character, or a
   run of them closed by a `:` (Y1). *)
Definition colon_ok (s : string) : bool :=
  match symbol_run s with
  | O => true
  | k => starts_with ":"%char (sdrop k s)
  end.

(* Whether a `{` after a backtick begins a raw spec that closes. *)
Definition raw_ahead (s : string) : bool :=
  (raw_inline_enabled && match raw_spec s with Some _ => true | None => false end)%bool.

(* What may follow a byte.  A `{` before anything but a row's character
   begins an attribute spec, and so does one after a `]`; one after a
   backtick is drawn on only as a raw spec that closes; a `[` before a `^`
   begins a footnote reference and before a `[` a wikilink; an autolink
   candidate holds no backslash; and a `:` either begins a symbol or is
   text on the spot. *)
Definition follow_ok (c : ascii) (rest : string) : bool :=
  ((negb (Ascii.eqb c lbrace) || starts_row rest)
   && negb (Ascii.eqb c lbrack && (starts_with lbrack rest || starts_with hat rest))
   && negb (Ascii.eqb c rbrack && starts_with lbrace rest)
   && negb (is_tick c && starts_with lbrace rest && negb (raw_ahead rest))
   && negb (Ascii.eqb c lt && negb (auto_clean rest))
   && negb (Ascii.eqb c ":"%char && negb (colon_ok rest)))%bool.

(* A backslash escapes the byte after it, whatever that byte is but the
   newline, so the escaped byte is not drawn on the alphabet (O2, O3).
   An escaped backtick is followed as a backtick is: inside a verbatim
   the backslash is a byte and the backtick may close it. *)
Fixpoint over_alphabet (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c rest =>
      if is_bslash c
      then match rest with
           | EmptyString => true
           | String d rest' =>
               negb (Ascii.eqb d nl_char)
               && negb (is_tick d && starts_with lbrace rest' && negb (raw_ahead rest'))
               && over_alphabet rest'
           end
      else (in_alphabet c && follow_ok c rest && over_alphabet rest)%bool
  end.

(* A text token is one byte, so that every token is nonempty.  A marked
   token is an opener `{_` or a closer `_}`, never both.  A break is a
   newline: a soft break in the tree, and whitespace to the delimiters on
   either side of it.  `TOpen` is a `[`, and `TClose` a `]` followed by
   `(`, which begins a destination (`dest`), or by `[`, which begins a
   reference label; a `]` before anything else is text.

   A backslash and what follows it are an escape (O2 to O5): before
   whitespace that runs to the end of the line, a hard break (`THard`,
   with that whitespace); before a run of whitespace that does not, the
   run (`TEscWs`), which is a non-breaking space and the rest of the run
   when it begins with a space; before any other byte, that byte as text
   if it is punctuation, and the backslash and the byte otherwise
   (`TEsc`).

   A run of `n` backticks opens a verbatim (V1), which runs to the next
   run of exactly `n` (`closed`) or to the paragraph's end; its body is
   every byte between, backslashes and newlines included (V2, V4).  While
   math is on, a run of `pre` dollars right before it is part of it
   (MA1): one makes inline math, more make display math, and the dollars
   before the last two are text.  Any other run of dollars is text
   (`TDollars`).  A closed verbatim with no dollars before it takes the
   raw spec right after it, while raw inline is on (`raw`, R1).

   A `<` begins an autolink candidate (A1 to A3), which runs to the byte
   that ends it (`auto_stop`).  It is a link when that byte is a `>` and
   the region is an address (`ok`); otherwise the `<` and the region are
   text and the byte that ended it is read on its own.

   A `:`, a nonempty run of symbol characters and a `:` are a symbol
   (`TSymbol`, Y1); any other `:` is text. *)
Inductive token : Type :=
  | TText (c : ascii)
  | TBreak
  | TDelim (k : dstyle) (marked opens closes : bool)
  | TOpen
  | TClose (dest : bool)
  | TEsc (c : ascii)
  | TEscWs (ws : string)
  | THard (ws : string)
  | TVerb (pre n : nat) (body : string) (closed : bool) (raw : option string)
  | TDollars (k : nat)
  | TAuto (src : string) (ok : bool)
  | TSymbol (alias : string).

(* The whitespace a string begins with. *)
Fixpoint ws_run (s : string) : string :=
  match s with
  | String c rest => if is_ws c then String c (ws_run rest) else EmptyString
  | EmptyString => EmptyString
  end.

(* The bytes before the first newline. *)
Fixpoint line_rest (s : string) : string :=
  match s with
  | String c rest => if Ascii.eqb c nl_char then EmptyString else String c (line_rest rest)
  | EmptyString => EmptyString
  end.

Fixpoint tick_run (s : string) : nat :=
  match s with
  | String c r => if is_tick c then S (tick_run r) else 0
  | EmptyString => 0
  end.

(* A verbatim's body, read after its opening run of `n`: its bytes, how
   many bytes it takes with its closing run, and whether it closed.
   `run` counts the backticks pending. *)
Fixpoint verb_go (n run : nat) (s : string) : string * nat * bool :=
  match s with
  | EmptyString => if Nat.eqb run n then (EmptyString, 0, true) else (ticks run, 0, false)
  | String c rest =>
      if is_tick c then let '(b, l, cl) := verb_go n (S run) rest in (b, S l, cl)
      else if Nat.eqb run n then (EmptyString, 0, true)
      else let '(b, l, cl) := verb_go n 0 rest in ((ticks run ++ String c b)%string, S l, cl)
  end.

(* A verbatim that `s` begins with, after `pre` dollars, and its length
   without them. *)
Definition verb_tok (pre : nat) (s : string) : token * nat :=
  let n := tick_run s in
  let '(body, used, closed) := verb_go n 0 (sdrop n s) in
  match (if (closed && Nat.eqb pre 0 && raw_inline_enabled)%bool
         then raw_spec (sdrop (n + used) s) else None) with
  | Some f => (TVerb pre n body closed (Some f), n + used + S (S (S (String.length f))))
  | None => (TVerb pre n body closed None, n + used)
  end.

Fixpoint dollar_run (s : string) : nat :=
  match s with
  | String c r => if Ascii.eqb c dollar then S (dollar_run r) else 0
  | EmptyString => 0
  end.

(* An autolink candidate that `s` begins with, past its `<`. *)
Definition auto_tok (s : string) : token * nat :=
  let '(src, stop) := auto_go s in
  if (match stop with Some c => Ascii.eqb c gt | None => false end
      && auto_body_ok src && auto_kind_ok src)%bool
  then (TAuto src true, S (S (String.length src)))
  else (TAuto src false, S (String.length src)).

(* A symbol that `s` begins with, past its `:`, or the `:` as text. *)
Definition sym_tok (s : string) : token * nat :=
  let k := symbol_run s in
  if (Nat.ltb 0 k && starts_with ":"%char (sdrop k s))%bool
  then (TSymbol (substring 0 k s), S (S k))
  else (TText ":"%char, 1).

(* A run of dollars that `s` begins with: the math it prefixes, or text. *)
Definition dollar_tok (s : string) : token * nat :=
  let k := dollar_run s in
  let rest := sdrop k s in
  if (math_enabled && starts_with tick rest)%bool
  then let '(t, l) := verb_tok k rest in (t, k + l)
  else (TDollars k, k).

Definition at_rbrace (p : option ascii) : bool :=
  match p with Some b => Ascii.eqb b rbrace | None => false end.

(* The token `s` begins with, and its length; `prev` is the byte before
   `s`.  A run of a row's character is cut, left to right, into tokens of
   the row's width, and a remainder shorter than that is text.  A token
   with `{` before it is a marked opener, and one with `}` after it a
   marked closer (P3).  A bare token may open when its row may be written
   bare and the byte after it is not whitespace, and may close when the
   byte before it is not whitespace (M2). *)
Definition next_tok (prev : option ascii) (s : string) : option (token * nat) :=
  match s with
  | EmptyString => None
  | String c rest =>
      Some
        (if Ascii.eqb c nl_char then (TBreak, 1)
         else if is_bslash c then
           if is_blank (line_rest rest)
           then (THard (line_rest rest), S (String.length (line_rest rest)))
           else match rest with
                | String d _ =>
                    if is_ws d then (TEscWs (ws_run rest), S (String.length (ws_run rest)))
                    else (TEsc d, 2)
                | EmptyString => (THard EmptyString, 1)
                end
         else if is_tick c then verb_tok 0 s
         else if Ascii.eqb c dollar then dollar_tok s
         else if Ascii.eqb c lt then auto_tok rest
         else if Ascii.eqb c ":"%char then sym_tok rest
         else if Ascii.eqb c lbrack then (TOpen, 1)
         else if Ascii.eqb c rbrack then
           (if starts_with lparen rest then TClose true
            else if starts_with lbrack rest then TClose false
            else TText c, 1)
         else if Ascii.eqb c lbrace then
           match (match rest with
                  | String d _ => dstyle_of d
                  | EmptyString => None
                  end) with
           | Some k =>
               if prefix (dtoken k) rest
               then (TDelim k true true false, S (dwidth k))
               else (TText c, 1)
           | None => (TText c, 1)
           end
         else match dstyle_of c with
         | Some k =>
             if prefix (dtoken k) s
             then if at_rbrace (get (dwidth k) s)
                  then (TDelim k true false true, S (dwidth k))
                  else (TDelim k false
                          (bare_opens k && nonspace_at (get (dwidth k) s))
                          (nonspace_at prev), dwidth k)
             else (TText c, 1)
         | None => (TText c, 1)
         end)
  end.

Definition before (s : string) (p : nat) : option ascii :=
  match p with O => None | S q => get q s end.

(* The token at byte `p`, and its length. *)
Definition tok_at (s : string) (p : nat) : option (token * nat) :=
  next_tok (before s p) (sdrop p s).

Definition tok_of (s : string) (p : nat) : option token :=
  option_map fst (tok_at s p).

(* A paragraph's lines, a newline between two of them, the last read
   without its trailing whitespace, as the paragraph's inlines are. *)
Fixpoint para_string (ls : list string) : string :=
  match ls with
  | [] => EmptyString
  | [x] => strip_trailing_ws x
  | x :: rest => (x ++ String nl_char (para_string rest))%string
  end.

(*
Readings
========

A reading says which role each token takes: a list of pairs of byte
offsets, `(i, j)` pairing the opener at `i` with the closer at `j`, and
the list of the tokens that act as openers.  An opener and a closer
pair when they have the same key: a delimiter's style and marking
("explicitly marked closers can only match explicitly marked openers",
P4), or the bracket.

A `]` that pairs closes its bracket, and what follows is a region of
the link syntax: a destination runs to the `)` that balances its `(`,
and a reference label to the next `]`.  A region is source, and so is
a label that no `]` ends: the reading's tokens are a chain from the
first byte, each followed by the next or, after a `]` that pairs, by
the byte after its region.  A destination with no balancing `)` is not
a region: the rest of the paragraph is read as usual, except that a
closer there may not reach an opener from before the destination, and
a closer that would reach one but for that is text (djot.js,
`inline.ts:150-158`). *)

Definition matching : Type := list (nat * nat).

Inductive key : Type := KDelim (k : dstyle) (marked : bool) | KBracket.

Definition key_eq (a b : key) : bool :=
  match a, b with
  | KDelim k m, KDelim k' m' => (dstyle_eq k k' && Bool.eqb m m')%bool
  | KBracket, KBracket => true
  | _, _ => false
  end.

(* A delimiter pair encloses something (M3); a bracket pair need not. *)
Definition needs_content (k : key) : bool :=
  match k with KDelim _ _ => true | KBracket => false end.

Definition opens_as (t : token) : option key :=
  match t with
  | TDelim k mr true _ => Some (KDelim k mr)
  | TOpen => Some KBracket
  | _ => None
  end.

Definition closes_as (t : token) : option key :=
  match t with
  | TDelim k mr _ true => Some (KDelim k mr)
  | TClose _ => Some KBracket
  | _ => None
  end.

Definition open_key (s : string) (i : nat) : option key :=
  match tok_of s i with Some t => opens_as t | None => None end.

Definition close_key (s : string) (j : nat) : option key :=
  match tok_of s j with Some t => closes_as t | None => None end.

(* The byte after the token at `p`. *)
Definition tok_end (s : string) (p : nat) : nat :=
  match tok_at s p with Some (_, l) => p + l | None => p end.

(* The `)` that balances an open `(`, `i` being the offset of the first
   byte of `s`.  An escaped byte counts no paren. *)
Fixpoint dest_close (esc : bool) (depth i : nat) (s : string) : option nat :=
  match s with
  | EmptyString => None
  | String c rest =>
      if esc then dest_close false depth (S i) rest
      else if is_bslash c then dest_close true depth (S i) rest
      else if Ascii.eqb c lparen then dest_close false (S depth) (S i) rest
      else if Ascii.eqb c rparen
      then match depth with O => Some i | S d => dest_close false d (S i) rest end
      else dest_close false depth (S i) rest
  end.

(* The first `]` not escaped. *)
Fixpoint label_close (esc : bool) (i : nat) (s : string) : option nat :=
  match s with
  | EmptyString => None
  | String c rest =>
      if esc then label_close false (S i) rest
      else if is_bslash c then label_close true (S i) rest
      else if Ascii.eqb c rbrack then Some i
      else label_close false (S i) rest
  end.

(* Where the region after a closing `]` at `d` ends.  The byte after the
   `]` is the region's `(` or `[`, so its text begins two bytes on. *)
Definition region_end (s : string) (d : nat) (dest : bool) : option nat :=
  if dest then dest_close false 0 (S (S d)) (sdrop (S (S d)) s)
  else label_close false (S (S d)) (sdrop (S (S d)) s).

Definition is_opener (m : matching) (i : nat) : bool :=
  existsb (fun e => Nat.eqb (fst e) i) m.

Definition is_closer (m : matching) (j : nat) : bool :=
  existsb (fun e => Nat.eqb (snd e) j) m.

(* Where a reading goes after a `]` that pairs: past its region; past
   the `]` when a destination does not close; nowhere when a label does
   not. *)
Definition resume (s : string) (d : nat) (dest : bool) : option nat :=
  match region_end s d dest with
  | Some e => Some (S e)
  | None => if dest then Some (S d) else None
  end.

Definition chain_next (s : string) (m : matching) (p : nat) : option nat :=
  match tok_at s p with
  | Some (TClose b, l) => if is_closer m p then resume s p b else Some (p + l)
  | Some (_, l) => Some (p + l)
  | None => None
  end.

(* The tokens a reading reads. *)
Inductive chain (s : string) (m : matching) : nat -> Prop :=
  | chain_start : chain s m 0
  | chain_step : forall p q, chain s m p -> chain_next s m p = Some q -> chain s m q.

Definition closes (m : matching) (j : nat) : Prop := exists i, In (i, j) m.

(* Gone by `j`: closed before it, or inside a pair closed before it.  The
   second is the reference's "any potential openers between the opener
   and the closer get marked as regular text"; reading the pairs in the
   order of their closers is "the first opener that gets closed takes
   precedence". *)
Definition dead (m : matching) (j p : nat) : Prop :=
  (exists j', j' < j /\ In (p, j') m)
  \/ (exists i' j', j' < j /\ In (i', j') m /\ i' < p < j').

(* Before a destination that does not close, seen from after it. *)
Definition behind (s : string) (m : matching) (j q : nat) : Prop :=
  exists p d, In (p, d) m /\ tok_of s d = Some (TClose true)
    /\ region_end s d true = None /\ q < d < j.

Definition reading : Type := (matching * list nat)%type.

(* An opener still open at `j`, the destinations aside. *)
Definition cand (s : string) (m : matching) (os : list nat)
  (j q : nat) (k : key) : Prop :=
  In q os /\ q < j /\ open_key s q = Some k /\ ~ closes m q /\ ~ dead m j q.

Definition live (s : string) (m : matching) (os : list nat)
  (j q : nat) (k : key) : Prop :=
  cand s m os j q k /\ ~ behind s m j q.

(* "When there are multiple openers that might be matched with a given
   closer, the closest one is used." *)
Definition closest_live (s : string) (m : matching) (os : list nat)
  (j : nat) (k : key) (p : nat) : Prop :=
  live s m os j p k /\ forall q, live s m os j q k -> q <= p.

(* A closer that only a destination keeps from its opener. *)
Definition barred (s : string) (m : matching) (os : list nat)
  (j : nat) (k : key) : Prop :=
  (forall q, ~ live s m os j q k) /\ exists q, cand s m os j q k.

(* The readings the rules allow.  A pair is a closer on the chain and the
   closest live opener of its key, with something between them for a
   delimiter.  A closer on the chain left unmatched has no live opener
   of its key but a delimiter right before it, with nothing to enclose:
   `__a` pairs nothing, and the second `_` opens in its turn.  A token
   acts as an opener when it may open, is on the chain, does not close,
   and is not barred. *)
Definition valid (s : string) (r : reading) : Prop :=
  let '(m, os) := r in
  (forall i j, In (i, j) m ->
     exists k, close_key s j = Some k /\ chain s m j
       /\ closest_live s m os j k i /\ (needs_content k = true -> tok_end s i < j))
  /\ (forall j k, close_key s j = Some k -> chain s m j -> ~ closes m j ->
        forall p, closest_live s m os j k p -> needs_content k = true /\ tok_end s p = j)
  /\ (forall q, In q os <->
        (exists k, open_key s q = Some k) /\ chain s m q /\ ~ closes m q
        /\ forall k, close_key s q = Some k -> ~ barred s m os q k).

(*
Uniqueness
----------

At most one reading is valid, so the rules determine it and `valid`, not
`ref_read` below, is the specification.  The roles are settled in the
order of the bytes: whether a token is on the chain, closes or opens
reads only the pairs that closed before it and the openers before it. *)

Lemma key_eq_iff : forall a b, key_eq a b = true <-> a = b.
Proof.
  intros [k m|] [k' m'|]; cbn; split; intros H; try discriminate; try reflexivity.
  - apply andb_true_iff in H as [H1 H2].
    destruct k, k'; try discriminate H1; apply Bool.eqb_prop in H2; subst; reflexivity.
  - injection H as -> ->. destruct k'; cbn; apply Bool.eqb_reflx.
Qed.

Lemma key_eq_refl : forall a, key_eq a a = true.
Proof. intros a. apply key_eq_iff. reflexivity. Qed.

Lemma close_key_fun : forall s j k k',
  close_key s j = Some k -> close_key s j = Some k' -> k = k'.
Proof. intros s j k k' H1 H2. rewrite H1 in H2. injection H2 as E. exact E. Qed.

Lemma closest_live_fun : forall s m os j k p q,
  closest_live s m os j k p -> closest_live s m os j k q -> p = q.
Proof.
  intros s m os j k p q [Hp Mp] [Hq Mq].
  specialize (Mp q Hq). specialize (Mq p Hp). lia.
Qed.

Lemma is_opener_iff : forall m i, is_opener m i = true <-> exists j, In (i, j) m.
Proof.
  intros m i. unfold is_opener. rewrite existsb_exists. split.
  - intros ([a b] & Hin & E). apply Nat.eqb_eq in E. cbn in E. subst a.
    exists b. exact Hin.
  - intros [j Hin]. exists (i, j). split; [exact Hin|apply Nat.eqb_refl].
Qed.

Lemma is_closer_iff : forall m j, is_closer m j = true <-> closes m j.
Proof.
  intros m j. unfold is_closer, closes. rewrite existsb_exists. split.
  - intros ([a b] & Hin & E). apply Nat.eqb_eq in E. cbn in E. subst b.
    exists a. exact Hin.
  - intros [i Hin]. exists (i, j). split; [exact Hin|apply Nat.eqb_refl].
Qed.

Lemma closes_dec : forall m j, {closes m j} + {~ closes m j}.
Proof.
  intros m j. destruct (is_closer m j) eqn:D.
  - left. apply is_closer_iff, D.
  - right. intros H. apply is_closer_iff in H. congruence.
Qed.

(* Two readings that agree before `n`. *)
Definition agree (m1 : matching) (os1 : list nat) (m2 : matching) (os2 : list nat)
  (n : nat) : Prop :=
  (forall i j, j < n -> In (i, j) m1 <-> In (i, j) m2)
  /\ (forall q, q < n -> In q os1 <-> In q os2).

Lemma agree_sym : forall m1 os1 m2 os2 n,
  agree m1 os1 m2 os2 n -> agree m2 os2 m1 os1 n.
Proof.
  intros m1 os1 m2 os2 n [Hm Ho]. split.
  - intros i j Hj. symmetry. apply Hm, Hj.
  - intros q Hq. symmetry. apply Ho, Hq.
Qed.

(*
Bounds
------
*)

Lemma length_chars : forall c n, String.length (chars c n) = n.
Proof. intros c n. induction n as [|n IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma prefix_length : forall a s, prefix a s = true -> String.length a <= String.length s.
Proof.
  induction a as [|x a IH]; intros s H; cbn; [lia|].
  destruct s as [|y s]; [discriminate|]. cbn [prefix] in H.
  destruct (ascii_dec x y); [|discriminate]. cbn. specialize (IH s H). lia.
Qed.

Lemma get_lt : forall n s c, get n s = Some c -> n < String.length s.
Proof.
  induction n as [|n IH]; intros [|d s] c H; cbn in *; try discriminate; [lia|].
  specialize (IH s c H). lia.
Qed.

Lemma ws_run_length : forall s, String.length (ws_run s) <= String.length s.
Proof.
  induction s as [|c s IH]; cbn; [lia|]. destruct (is_ws c); cbn; lia.
Qed.

Lemma line_rest_length : forall s, String.length (line_rest s) <= String.length s.
Proof.
  induction s as [|c s IH]; cbn; [lia|]. destruct (Ascii.eqb c nl_char); cbn; lia.
Qed.

Lemma verb_go_len : forall s n run, snd (fst (verb_go n run s)) <= String.length s.
Proof.
  induction s as [|c s IH]; intros n run; cbn [verb_go String.length].
  - destruct (Nat.eqb run n); cbn; lia.
  - destruct (is_tick c).
    + specialize (IH n (S run)). destruct (verb_go n (S run) s) as [[b l] cl]. cbn in *. lia.
    + destruct (Nat.eqb run n); [cbn; lia|].
      specialize (IH n 0). destruct (verb_go n 0 s) as [[b l] cl]. cbn in *. lia.
Qed.

Lemma tick_run_le : forall s, tick_run s <= String.length s.
Proof. induction s as [|c s IH]; cbn; [lia|]. destruct (is_tick c); cbn; lia. Qed.

Lemma fmt_go_len : forall s f, fmt_go s = Some f -> S (String.length f) <= String.length s.
Proof.
  induction s as [|c s IH]; intros f H; [discriminate|]. cbn [fmt_go] in H.
  destruct (Ascii.eqb c rbrace); [injection H as <-; cbn; lia|].
  destruct (raw_stop c || Ascii.eqb c nl_char)%bool; [discriminate|].
  destruct (fmt_go s) as [f'|] eqn:E; [|discriminate]. injection H as <-.
  specialize (IH f' eq_refl). cbn. lia.
Qed.

Lemma raw_spec_len : forall s f, raw_spec s = Some f -> S (S (S (String.length f))) <= String.length s.
Proof.
  intros [|b [|e r]] f H; try discriminate. cbn [raw_spec] in H.
  destruct (Ascii.eqb b lbrace && Ascii.eqb e eqchar)%bool; [|discriminate].
  destruct (fmt_go r) as [[|c f']|] eqn:E; try discriminate. injection H as <-.
  pose proof (fmt_go_len r _ E). cbn in *. lia.
Qed.

Lemma verb_tok_len : forall pre s t l,
  starts_with tick s = true -> verb_tok pre s = (t, l) -> 0 < l <= String.length s.
Proof.
  intros pre s t l Hc H. unfold verb_tok in H.
  pose proof (verb_go_len (sdrop (tick_run s) s) (tick_run s) 0) as G.
  rewrite sdrop_length in G.
  pose proof (tick_run_le s) as Tr.
  assert (Ht : tick_run s <> 0)
    by (destruct s as [|c rest]; [discriminate|]; cbn in Hc |- *; unfold is_tick; rewrite Hc;
        discriminate).
  destruct (verb_go _ 0 _) as [[b u] cl]. cbn [fst snd] in G.
  destruct (if (cl && Nat.eqb pre 0 && raw_inline_enabled)%bool
            then raw_spec (sdrop (tick_run s + u) s) else None) as [f|] eqn:Er.
  - injection H as <- <-.
    destruct (cl && Nat.eqb pre 0 && raw_inline_enabled)%bool; [|discriminate].
    pose proof (raw_spec_len _ _ Er) as Lr. rewrite sdrop_length in Lr. lia.
  - injection H as <- <-. lia.
Qed.

Lemma verb_tok_shape : forall pre s,
  exists n b cl r l, verb_tok pre s = (TVerb pre n b cl r, l).
Proof.
  intros pre s. unfold verb_tok. destruct (verb_go _ _ _) as [[b u] cl].
  destruct (if (cl && Nat.eqb pre 0 && raw_inline_enabled)%bool
            then raw_spec (sdrop (tick_run s + u) s) else None) as [f|];
    do 5 eexists; reflexivity.
Qed.

Lemma dollar_run_le : forall s, dollar_run s <= String.length s.
Proof. induction s as [|c s IH]; cbn; [lia|]. destruct (Ascii.eqb c dollar); cbn; lia. Qed.

Lemma dollar_tok_len : forall c rest t l,
  Ascii.eqb c dollar = true -> dollar_tok (String c rest) = (t, l) ->
  0 < l <= S (String.length rest).
Proof.
  intros c rest t l Hc H. unfold dollar_tok in H.
  pose proof (dollar_run_le (String c rest)) as Dr.
  pose proof (sdrop_length (dollar_run (String c rest)) (String c rest)) as Ls.
  cbn [dollar_run String.length] in *. rewrite Hc in *.
  destruct (math_enabled && starts_with tick (sdrop (S (dollar_run rest)) (String c rest)))%bool
    eqn:E.
  - apply andb_true_iff in E as [_ E].
    destruct (verb_tok (S (dollar_run rest)) (sdrop (S (dollar_run rest)) (String c rest)))
      as [t0 l0] eqn:Ev.
    pose proof (verb_tok_len _ _ _ _ E Ev) as L0. injection H as <- <-. lia.
  - injection H as <- <-. lia.
Qed.

Lemma auto_go_len : forall r src stop, auto_go r = (src, stop) ->
  String.length src + (match stop with Some _ => 1 | None => 0 end) <= String.length r.
Proof.
  induction r as [|c r IH]; intros src stop H; cbn [auto_go] in H.
  - injection H as <- <-. reflexivity.
  - destruct (auto_stop c); [injection H as <- <-; cbn; lia|].
    destruct (auto_go r) as [src' stop'] eqn:E. injection H as <- <-.
    specialize (IH _ _ eq_refl). cbn. lia.
Qed.

Lemma auto_tok_len : forall r t l, auto_tok r = (t, l) -> 0 < l <= S (String.length r).
Proof.
  intros r t l H. unfold auto_tok in H. destruct (auto_go r) as [src stop] eqn:E.
  pose proof (auto_go_len r src stop E) as L.
  destruct (match stop with Some c => Ascii.eqb c gt | None => false end
            && auto_body_ok src && auto_kind_ok src)%bool eqn:Ok; injection H as <- <-.
  - destruct stop; [|discriminate]. lia.
  - lia.
Qed.

Lemma auto_tok_shape : forall r, exists src ok l, auto_tok r = (TAuto src ok, l).
Proof.
  intros r. unfold auto_tok. destruct (auto_go r) as [src stop].
  destruct (_ && _)%bool; do 3 eexists; reflexivity.
Qed.

Lemma symbol_run_le : forall s, symbol_run s <= String.length s.
Proof. induction s as [|c s IH]; cbn; [lia|]. destruct (symbol_char c); cbn; lia. Qed.

Lemma sym_tok_len : forall r t l, sym_tok r = (t, l) -> 0 < l <= S (String.length r).
Proof.
  intros r t l H. unfold sym_tok in H. pose proof (symbol_run_le r) as Le.
  destruct (Nat.ltb 0 (symbol_run r) && starts_with ":"%char (sdrop (symbol_run r) r))%bool
    eqn:E; injection H as <- <-; [|lia].
  apply andb_true_iff in E as [_ E].
  destruct (sdrop (symbol_run r) r) as [|c r'] eqn:Es; [discriminate|].
  pose proof (sdrop_length (symbol_run r) r) as L. rewrite Es in L. cbn in L. lia.
Qed.

Lemma sym_tok_shape : forall r,
  (exists a l, sym_tok r = (TSymbol a, l)) \/ sym_tok r = (TText ":"%char, 1).
Proof.
  intros r. unfold sym_tok. destruct (_ && _)%bool; [left; eauto|right; reflexivity].
Qed.

Lemma next_tok_len : forall prev s t l,
  next_tok prev s = Some (t, l) -> 0 < l <= String.length s.
Proof.
  intros prev s t l H. destruct s as [|c rest] eqn:Es; [discriminate|].
  pose proof dwidth_nonzero as Wn.
  assert (P1 : forall k, prefix (dtoken k) rest = true -> dwidth k <= String.length rest).
  { intros k Hp. apply prefix_length in Hp. unfold dtoken in Hp. rewrite length_chars in Hp.
    exact Hp. }
  assert (P2 : forall k, prefix (dtoken k) s = true -> dwidth k <= String.length s).
  { intros k Hp. apply prefix_length in Hp. unfold dtoken in Hp. rewrite length_chars in Hp.
    exact Hp. }
  assert (G : forall k, at_rbrace (get (dwidth k) s) = true -> dwidth k < String.length s).
  { intros k Hg. unfold at_rbrace in Hg. destruct (get (dwidth k) s) eqn:E; [|discriminate].
    exact (get_lt _ _ _ E). }
  rewrite <- Es in H. unfold next_tok in H. rewrite Es in H at 1.
  injection H as H. rewrite <- Es. subst s. cbn [String.length] in *.
  pose proof (line_rest_length rest). pose proof (ws_run_length rest).
  repeat match type of H with
  | (if ?b then _ else _) = _ => destruct b eqn:?
  | (match ?x with _ => _ end) = _ => destruct x eqn:?
  end;
    try (injection H as <- <-); try lia.
  all: first
    [ match goal with Hw : is_ws ?a = true |- _ =>
        cbn [ws_run] in H1; rewrite Hw in H1 |- *; cbn [String.length] in *; lia end
    | cbn [String.length]; lia
    | match goal with Hp : prefix (dtoken ?k) _ = true |- _ =>
        specialize (P1 k Hp); specialize (Wn k); lia end
    | match goal with Hg : at_rbrace (get (dwidth ?k) _) = true |- _ =>
        specialize (G k Hg); specialize (Wn k); lia end
    | match goal with Hp : prefix (dtoken ?k) _ = true |- _ =>
        specialize (P2 k Hp); specialize (Wn k); lia end
    | match goal with Ht : is_tick ?x = true |- _ =>
        pose proof (verb_tok_len 0 (String x rest) t l Ht H); cbn [String.length] in *; lia end
    | match goal with Hd : Ascii.eqb ?x dollar = true |- _ =>
        exact (dollar_tok_len _ _ t l Hd H) end
    | match goal with Hd : Ascii.eqb ?x lt = true |- _ =>
        exact (auto_tok_len _ t l H) end
    | match goal with Hd : Ascii.eqb ?x ":"%char = true |- _ =>
        exact (sym_tok_len _ t l H) end ].
Qed.

Lemma tok_at_len : forall s p t l,
  tok_at s p = Some (t, l) -> 0 < l /\ p + l <= String.length s.
Proof.
  intros s p t l H. unfold tok_at in H. pose proof (next_tok_len _ _ _ _ H) as Hl.
  rewrite sdrop_length in Hl. lia.
Qed.

Lemma dest_close_bound : forall s esc depth i e,
  dest_close esc depth i s = Some e -> i <= e < i + String.length s.
Proof.
  induction s as [|c s IH]; intros esc depth i e H; [discriminate|].
  cbn [dest_close] in H. cbn [String.length].
  destruct esc; [apply IH in H; lia|].
  destruct (is_bslash c); [apply IH in H; lia|].
  destruct (Ascii.eqb c lparen); [apply IH in H; lia|].
  destruct (Ascii.eqb c rparen); [|apply IH in H; lia].
  destruct depth; [injection H as <-; lia|apply IH in H; lia].
Qed.

Lemma label_close_bound : forall s esc i e,
  label_close esc i s = Some e -> i <= e < i + String.length s.
Proof.
  induction s as [|c s IH]; intros esc i e H; [discriminate|].
  cbn [label_close] in H. cbn [String.length].
  destruct esc; [apply IH in H; lia|].
  destruct (is_bslash c); [apply IH in H; lia|].
  destruct (Ascii.eqb c rbrack); [injection H as <-; lia|apply IH in H; lia].
Qed.

Lemma region_end_bound : forall s d b e,
  region_end s d b = Some e -> S (S d) <= e < String.length s.
Proof.
  intros s d [|] e H; unfold region_end in H;
    [apply dest_close_bound in H|apply label_close_bound in H];
    rewrite sdrop_length in H; lia.
Qed.

Lemma tok_at_close : forall s p b l, tok_at s p = Some (TClose b, l) -> l = 1.
Proof.
  intros s p b l H. unfold tok_at, next_tok, dollar_tok in H.
  destruct (sdrop p s) as [|c rest]; [discriminate|]. injection H as H.
  repeat match type of H with
  | context [sym_tok ?a] =>
      let E := fresh in destruct (sym_tok_shape a) as [(? & ? & E)|E]; rewrite E in H;
      cbn iota beta in H
  | context [auto_tok ?a] =>
      let E := fresh in destruct (auto_tok_shape a) as (? & ? & ? & E); rewrite E in H;
      cbn iota beta in H
  | context [verb_tok ?a ?b] =>
      let E := fresh in destruct (verb_tok_shape a b) as (? & ? & ? & ? & ? & E); rewrite E in H;
      cbn iota beta in H
  | (if ?b then _ else _) = _ => destruct b
  | (match ?x with _ => _ end) = _ => destruct x
  end; congruence.
Qed.

Lemma tok_at_dollars : forall s p k l, tok_at s p = Some (TDollars k, l) -> l = k.
Proof.
  intros s p k l H. unfold tok_at, next_tok, dollar_tok in H.
  destruct (sdrop p s) as [|c rest]; [discriminate|]. injection H as H.
  repeat match type of H with
  | context [sym_tok ?a] =>
      let E := fresh in destruct (sym_tok_shape a) as [(? & ? & E)|E]; rewrite E in H;
      cbn iota beta in H
  | context [auto_tok ?a] =>
      let E := fresh in destruct (auto_tok_shape a) as (? & ? & ? & E); rewrite E in H;
      cbn iota beta in H
  | context [verb_tok ?a ?b] =>
      let E := fresh in destruct (verb_tok_shape a b) as (? & ? & ? & ? & ? & E); rewrite E in H;
      cbn iota beta in H
  | (if ?b then _ else _) = _ => destruct b
  | (match ?x with _ => _ end) = _ => destruct x
  | context [if ?b then _ else _] => destruct b
  end; congruence.
Qed.

Lemma chain_next_bound : forall s m p q,
  chain_next s m p = Some q -> p < q <= String.length s.
Proof.
  intros s m p q H. unfold chain_next in H.
  destruct (tok_at s p) as [[t l]|] eqn:E; [|discriminate].
  pose proof (tok_at_len s p t l E) as Hl.
  destruct t; try (injection H as <-; lia).
  destruct (is_closer m p); [|injection H as <-; lia].
  unfold resume in H. destruct (region_end s p dest) as [e|] eqn:R.
  - injection H as <-. apply region_end_bound in R. lia.
  - pose proof (tok_at_close s p dest l E) as ->.
    destruct dest; [injection H as <-; lia|discriminate].
Qed.

(* The chain is one sequence: between two of its points, the next point
   after the first. *)
Lemma chain_between : forall s m a p,
  chain s m p -> chain s m a -> p < a ->
  exists q, chain_next s m p = Some q /\ q <= a.
Proof.
  intros s m a. induction a as [a IH] using lt_wf_ind. intros p Hp Ha Hlt.
  inversion Ha as [E|p' a' Hp' Hn E]; [lia|subst a'].
  pose proof (chain_next_bound s m p' a Hn) as Hb.
  destruct (lt_eq_lt_dec p p') as [[Hl|<-]|Hl].
  - destruct (IH p' ltac:(lia) p Hp Hp' Hl) as (q & Hq & Hqa).
    exists q. split; [exact Hq|lia].
  - exists a. split; [exact Hn|lia].
  - destruct (IH p ltac:(lia) p' Hp' Hp Hl) as (q & Hq & Hqa).
    rewrite Hn in Hq. injection Hq as <-. lia.
Qed.

Lemma chain_none : forall s m p a,
  chain s m p -> chain_next s m p = None -> chain s m a -> a <= p.
Proof.
  intros s m p a Hp Hn Ha. destruct (le_lt_dec a p) as [H|H]; [exact H|].
  destruct (chain_between s m a p Hp Ha H) as (q & Hq & _). congruence.
Qed.

Lemma chain_gap : forall s m p q a,
  chain s m p -> chain_next s m p = Some q -> p < a < q -> ~ chain s m a.
Proof.
  intros s m p q a Hp Hn Ha Hc.
  destruct (chain_between s m a p Hp Hc ltac:(lia)) as (q' & Hq & Hle).
  rewrite Hn in Hq. injection Hq as <-. lia.
Qed.

Section Agree.
Variables (s : string) (m1 m2 : matching) (os1 os2 : list nat) (n : nat).
Hypothesis A : agree m1 os1 m2 os2 n.

Lemma dead_agree : forall j p, j <= n -> dead m1 j p -> dead m2 j p.
Proof.
  destruct A as [Hm _]. intros j p Hj [(j' & Hj' & H)|(i' & j' & Hj' & H & Hb)].
  - left. exists j'. split; [exact Hj'|]. apply Hm; [lia|exact H].
  - right. exists i', j'. split; [exact Hj'|]. split; [apply Hm; [lia|exact H]|exact Hb].
Qed.

Lemma behind_agree : forall j q, j <= n -> behind s m1 j q -> behind s m2 j q.
Proof.
  destruct A as [Hm _]. intros j q Hj (p & d & H & Hd & He & Hlt).
  exists p, d. split; [apply Hm; [lia|exact H]|]. split; [exact Hd|].
  split; [exact He|exact Hlt].
Qed.

Lemma closes_agree : forall q, q < n -> closes m1 q -> closes m2 q.
Proof.
  destruct A as [Hm _]. intros q Hq [i H]. exists i. apply Hm; [exact Hq|exact H].
Qed.

End Agree.

Lemma closer_agree : forall m1 os1 m2 os2 n q,
  agree m1 os1 m2 os2 n -> q < n -> is_closer m1 q = is_closer m2 q.
Proof.
  intros m1 os1 m2 os2 n q A Hq. apply Bool.eq_true_iff_eq. rewrite !is_closer_iff.
  split; [apply (closes_agree m1 m2 os1 os2 n A q Hq)|].
  apply (closes_agree m2 m1 os2 os1 n (agree_sym _ _ _ _ _ A) q Hq).
Qed.

Lemma chain_agree : forall s m1 os1 m2 os2 n t,
  agree m1 os1 m2 os2 n -> t <= n -> chain s m1 t -> chain s m2 t.
Proof.
  intros s m1 os1 m2 os2 n t A Ht H. induction H as [|p q Hp IH Hn]; [constructor|].
  pose proof (chain_next_bound s m1 p q Hn) as Hb.
  apply (chain_step s m2 p q); [apply IH; lia|].
  rewrite <- Hn. unfold chain_next.
  rewrite (closer_agree m1 os1 m2 os2 n p A ltac:(lia)). reflexivity.
Qed.

Lemma cand_agree : forall s m1 os1 m2 os2 n j q k,
  agree m1 os1 m2 os2 n -> j <= n ->
  cand s m1 os1 j q k -> cand s m2 os2 j q k.
Proof.
  intros s m1 os1 m2 os2 n j q k A Hj (Hin & Hq & Ho & Hc & Hd).
  pose proof (agree_sym _ _ _ _ _ A) as A'.
  split; [apply (proj2 A); [lia|exact Hin]|]. split; [exact Hq|].
  split; [exact Ho|]. split.
  - intros H. apply Hc. apply (closes_agree m2 m1 os2 os1 n A'); [lia|exact H].
  - intros H. apply Hd. apply (dead_agree m2 m1 os2 os1 n A' j q Hj H).
Qed.

Lemma live_agree : forall s m1 os1 m2 os2 n j q k,
  agree m1 os1 m2 os2 n -> j <= n ->
  live s m1 os1 j q k -> live s m2 os2 j q k.
Proof.
  intros s m1 os1 m2 os2 n j q k A Hj [Hc Hb].
  pose proof (agree_sym _ _ _ _ _ A) as A'.
  split; [exact (cand_agree s m1 os1 m2 os2 n j q k A Hj Hc)|].
  intros H. apply Hb. exact (behind_agree s m2 m1 os2 os1 n A' j q Hj H).
Qed.

Lemma closest_live_agree : forall s m1 os1 m2 os2 n j k p,
  agree m1 os1 m2 os2 n -> j <= n ->
  closest_live s m1 os1 j k p -> closest_live s m2 os2 j k p.
Proof.
  intros s m1 os1 m2 os2 n j k p A Hj [Hp Mp].
  pose proof (agree_sym _ _ _ _ _ A) as A'.
  split; [exact (live_agree s m1 os1 m2 os2 n j p k A Hj Hp)|].
  intros q Hq. apply Mp. exact (live_agree s m2 os2 m1 os1 n j q k A' Hj Hq).
Qed.

Lemma barred_agree : forall s m1 os1 m2 os2 n j k,
  agree m1 os1 m2 os2 n -> j <= n ->
  barred s m1 os1 j k -> barred s m2 os2 j k.
Proof.
  intros s m1 os1 m2 os2 n j k A Hj [Hn (q & Hq)].
  pose proof (agree_sym _ _ _ _ _ A) as A'.
  split.
  - intros q' Hq'. apply (Hn q'). exact (live_agree s m2 os2 m1 os1 n j q' k A' Hj Hq').
  - exists q. exact (cand_agree s m1 os1 m2 os2 n j q k A Hj Hq).
Qed.

Local Lemma valid_pairs_at : forall s m1 os1 m2 os2 n,
  valid s (m1, os1) -> valid s (m2, os2) -> agree m1 os1 m2 os2 n ->
  forall i, In (i, n) m1 -> In (i, n) m2.
Proof.
  intros s m1 os1 m2 os2 n [P1 _] [P2 [U2 _]] A i H.
  destruct (P1 i n H) as (k & Hk & Hch & Hcl & Hne).
  apply (closest_live_agree s m1 os1 m2 os2 n n k i A (le_n n)) in Hcl.
  pose proof (chain_agree s m1 os1 m2 os2 n n A (le_n n) Hch) as Hch2.
  destruct (closes_dec m2 n) as [[i' Hi']|Hn].
  - destruct (P2 i' n Hi') as (k' & Hk' & _ & Hcl' & _).
    rewrite <- (close_key_fun s n k k' Hk Hk') in Hcl'.
    rewrite (closest_live_fun s m2 os2 n k i i' Hcl Hcl'). exact Hi'.
  - destruct (U2 n k Hk Hch2 Hn i Hcl) as [Hc E].
    specialize (Hne Hc). lia.
Qed.

Local Lemma valid_os_at : forall s m1 os1 m2 os2 n,
  valid s (m1, os1) -> valid s (m2, os2) -> agree m1 os1 m2 os2 n ->
  (forall i, In (i, n) m1 <-> In (i, n) m2) ->
  In n os1 -> In n os2.
Proof.
  intros s m1 os1 m2 os2 n [_ [_ O1]] [_ [_ O2]] A Hn H.
  pose proof (agree_sym _ _ _ _ _ A) as A'.
  apply O1 in H as (Ho & Hch & Hc & Hb). apply O2.
  split; [exact Ho|]. split; [|split].
  - exact (chain_agree s m1 os1 m2 os2 n n A (le_n n) Hch).
  - intros [i Hi]. apply Hc. exists i. apply Hn, Hi.
  - intros k Hk Hbar. apply (Hb k Hk).
    exact (barred_agree s m2 os2 m1 os1 n n k A' (le_n n) Hbar).
Qed.

Theorem valid_unique : forall s m1 os1 m2 os2,
  valid s (m1, os1) -> valid s (m2, os2) ->
  (forall i j, In (i, j) m1 <-> In (i, j) m2) /\ (forall q, In q os1 <-> In q os2).
Proof.
  intros s m1 os1 m2 os2 V1 V2.
  assert (Step : forall n, agree m1 os1 m2 os2 n ->
            (forall i, In (i, n) m1 <-> In (i, n) m2) /\ (In n os1 <-> In n os2)).
  { intros n A.
    assert (Hp : forall i, In (i, n) m1 <-> In (i, n) m2).
    { intros i. split.
      - apply (valid_pairs_at s m1 os1 m2 os2 n V1 V2 A).
      - apply (valid_pairs_at s m2 os2 m1 os1 n V2 V1 (agree_sym _ _ _ _ _ A)). }
    split; [exact Hp|]. split.
    - apply (valid_os_at s m1 os1 m2 os2 n V1 V2 A Hp).
    - apply (valid_os_at s m2 os2 m1 os1 n V2 V1 (agree_sym _ _ _ _ _ A)).
      intros i. symmetry. apply Hp. }
  assert (All : forall n, agree m1 os1 m2 os2 n).
  { induction n as [|n IH]; [split; intros; lia|].
    destruct (Step n IH) as [Hp Ho]. split.
    - intros i j Hj. destruct (Nat.eq_dec j n) as [->|Hne]; [apply Hp|].
      apply (proj1 IH). lia.
    - intros q Hq. destruct (Nat.eq_dec q n) as [->|Hne]; [exact Ho|].
      apply (proj2 IH). lia. }
  split.
  - intros i j. apply (proj1 (All (S j))). lia.
  - intros q. apply (proj2 (All (S q))). lia.
Qed.

(* "Containers can't overlap": a pair that opens inside another closes
   inside it. *)
Theorem valid_nested : forall s m os i j i' j',
  valid s (m, os) -> In (i, j) m -> In (i', j') m -> i < i' < j -> j' < j.
Proof.
  intros s m os i j i' j' [P _] H H' Hb.
  destruct (P i j H) as (k & Hk & _ & Hcl & _).
  destruct (P i' j' H') as (k' & Hk' & _ & Hcl' & _).
  destruct (lt_eq_lt_dec j' j) as [[Hlt|Heq]|Hgt]; [exact Hlt| |].
  - subst j'. pose proof (close_key_fun s j k k' Hk Hk') as <-.
    pose proof (closest_live_fun s m os j k i i' Hcl Hcl'). lia.
  - exfalso. destruct Hcl' as [((_ & _ & _ & _ & Hd) & _) _].
    apply Hd. right. exists i, j. split; [exact Hgt|]. split; [exact H|exact Hb].
Qed.

(*
The reading, computed
---------------------

Along the chain, with the openers still open innermost first and a
marker for each destination that does not close.  A closer takes the
closest open opener of its key above every marker; with none there and
one below a marker it is barred. *)

Inductive litem : Type := LOpen (p : nat) (k : key) | LBar (d : nat).

Definition lpos (x : litem) : nat := match x with LOpen p _ => p | LBar d => d end.

Definition ldesc (lv : list litem) : Prop :=
  StronglySorted (fun a b => lpos b < lpos a) lv.

Fixpoint has_key (k : key) (lv : list litem) : bool :=
  match lv with
  | [] => false
  | LOpen _ k' :: rest => (key_eq k k' || has_key k rest)%bool
  | LBar _ :: rest => has_key k rest
  end.

Inductive pick_res : Type := PFound (p : nat) (below : list litem) | PBarred | PNone.

Fixpoint pick (k : key) (lv : list litem) : pick_res :=
  match lv with
  | [] => PNone
  | LBar _ :: rest => if has_key k rest then PBarred else PNone
  | LOpen p k' :: rest => if key_eq k k' then PFound p rest else pick k rest
  end.

Record rstate : Type := RState {
  rs_live : list litem;
  rs_pairs : matching;
  rs_os : list nat
}.

Definition ropen (i : nat) (k : key) (op : bool) (st : rstate) : rstate :=
  if op then RState (LOpen i k :: rs_live st) (rs_pairs st) (i :: rs_os st) else st.

Definition rstep (s : string) (i : nat) (t : token) (st : rstate) : rstate :=
  match t with
  | TText _ | TBreak | TEsc _ | TEscWs _ | THard _ | TVerb _ _ _ _ _ | TDollars _ | TAuto _ _ | TSymbol _ => st
  | TOpen => ropen i KBracket true st
  | TDelim k mr op cl =>
      match (if cl then pick (KDelim k mr) (rs_live st) else PNone) with
      | PFound p below =>
          if Nat.ltb (tok_end s p) i
          then RState below ((p, i) :: rs_pairs st) (rs_os st)
          else ropen i (KDelim k mr) op st
      | PBarred => st
      | PNone => ropen i (KDelim k mr) op st
      end
  | TClose b =>
      match pick KBracket (rs_live st) with
      | PFound p below =>
          let pairs := (p, i) :: rs_pairs st in
          match region_end s i b, b with
          | None, true => RState (LBar i :: below) pairs (rs_os st)
          | _, _ => RState below pairs (rs_os st)
          end
      | _ => st
      end
  end.

Fixpoint rgo (s : string) (fuel p : nat) (st : rstate) : rstate :=
  match fuel with
  | O => st
  | S f =>
      match tok_of s p with
      | None => st
      | Some t =>
          let st' := rstep s p t st in
          match chain_next s (rs_pairs st') p with
          | Some q => rgo s f q st'
          | None => st'
          end
      end
  end.

Definition rstart : rstate := RState [] [] [].

Definition ref_read (s : string) : reading :=
  let st := rgo s (S (String.length s)) 0 rstart in (rs_pairs st, rs_os st).

(*
The computed reading is valid
-----------------------------

At a byte `n` the stack holds exactly the openers still open at `n`
and a marker for each destination that does not close, innermost
first, and every role before `n` obeys the rules.  A token's role reads
only what came before it, so extending the reading past `n` keeps the
rules for the tokens before `n` (`agree`). *)

(* Above every marker. *)
Definition clear (lv : list litem) (q : nat) : Prop :=
  forall d, In (LBar d) lv -> d <= q.

Lemma has_key_spec : forall k lv,
  has_key k lv = true <-> exists q, In (LOpen q k) lv.
Proof.
  intros k lv. induction lv as [|[q k'|d] rest IH]; cbn [has_key In].
  - split; [discriminate|intros [q []]].
  - rewrite orb_true_iff, IH, key_eq_iff. split.
    + intros [->|[q' H]]; [exists q; left; reflexivity|exists q'; right; exact H].
    + intros [q' [E|H]]; [injection E as _ ->; left; reflexivity|right; exists q'; exact H].
  - rewrite IH. split; intros [q0 H]; exists q0;
      [right; exact H|destruct H as [E|H]; [discriminate|exact H]].
Qed.

Lemma pick_found : forall k lv p below,
  ldesc lv -> pick k lv = PFound p below ->
  In (LOpen p k) lv /\ clear lv p
  /\ (forall q, In (LOpen q k) lv -> clear lv q -> q <= p)
  /\ (forall x, In x below <-> In x lv /\ lpos x < p)
  /\ ldesc below
  /\ (forall x, In x lv -> p < lpos x -> exists q k', x = LOpen q k').
Proof.
  intros k lv. induction lv as [|x rest IH]; intros p below D H; [discriminate|].
  apply StronglySorted_inv in D as [D F]. rewrite Forall_forall in F.
  destruct x as [q k'|d]; cbn [pick] in H.
  - destruct (key_eq k k') eqn:E.
    + injection H as <- <-. apply key_eq_iff in E. subst k'.
      split; [left; reflexivity|]. split; [|split; [|split; [|split]]].
      * intros d [Hd|Hd]; [discriminate|]. specialize (F _ Hd). cbn in F. lia.
      * intros q0 [Hq|Hq] _; [injection Hq as ->; lia|]. specialize (F _ Hq).
        cbn in F. lia.
      * intros x. split.
        -- intros Hx. split; [right; exact Hx|]. exact (F x Hx).
        -- intros [[<-|Hx] Hlt]; [cbn in Hlt; lia|exact Hx].
      * exact D.
      * intros x [<-|Hx] Hlt; [cbn in Hlt; lia|]. specialize (F x Hx).
        cbn in F. lia.
    + destruct (IH p below D H) as (Hin & Hc & Hmax & Hb & Db & Ha).
      assert (Hqp : p < q) by (exact (F _ Hin)).
      split; [right; exact Hin|]. split; [|split; [|split; [|split]]].
      * intros d [Hd|Hd]; [discriminate|exact (Hc d Hd)].
      * intros q' [Hq'|Hq'] Hcl.
        -- injection Hq' as <- E'. subst k'. rewrite key_eq_refl in E. discriminate.
        -- apply Hmax; [exact Hq'|]. intros d Hd. apply Hcl. right. exact Hd.
      * intros x. rewrite Hb. split.
        -- intros [Hx Hlt]. split; [right; exact Hx|exact Hlt].
        -- intros [[<-|Hx] Hlt]; [cbn in Hlt; lia|]. split; [exact Hx|exact Hlt].
      * exact Db.
      * intros x [<-|Hx] Hlt; [exists q, k'; reflexivity|]. exact (Ha x Hx Hlt).
  - destruct (has_key k rest); discriminate.
Qed.

Lemma pick_barred : forall k lv,
  ldesc lv -> pick k lv = PBarred ->
  (forall q, In (LOpen q k) lv -> ~ clear lv q) /\ exists q, In (LOpen q k) lv.
Proof.
  intros k lv. induction lv as [|x rest IH]; intros D H; [discriminate|].
  apply StronglySorted_inv in D as [D F]. rewrite Forall_forall in F.
  destruct x as [q k'|d]; cbn [pick] in H.
  - destruct (key_eq k k') eqn:E; [discriminate|].
    destruct (IH D H) as [Hn [q' Hq']]. split; [|exists q'; right; exact Hq'].
    intros q0 [Hq0|Hq0] Hcl.
    + injection Hq0 as <- E'. subst k'. rewrite key_eq_refl in E. discriminate.
    + apply (Hn q0 Hq0). intros d Hd. apply Hcl. right. exact Hd.
  - destruct (has_key k rest) eqn:Hk; [|discriminate].
    apply has_key_spec in Hk as [q Hq]. split; [|exists q; right; exact Hq].
    intros q0 [Hq0|Hq0] Hcl; [discriminate|].
    specialize (Hcl d (or_introl eq_refl)). specialize (F _ Hq0). cbn in F. lia.
Qed.

Lemma pick_none : forall k lv,
  pick k lv = PNone -> forall q, ~ In (LOpen q k) lv.
Proof.
  intros k lv. induction lv as [|x rest IH]; intros H q Hq; [exact Hq|].
  destruct x as [q' k'|d]; cbn [pick] in H.
  - destruct (key_eq k k') eqn:E; [discriminate|].
    destruct Hq as [Hq|Hq]; [|exact (IH H q Hq)].
    injection Hq as <- E'. subst k'. rewrite key_eq_refl in E. discriminate.
  - destruct (has_key k rest) eqn:Hk; [discriminate|].
    destruct Hq as [Hq|Hq]; [discriminate|].
    assert (has_key k rest = true) by (apply has_key_spec; exists q; exact Hq).
    congruence.
Qed.

Definition bar (s : string) (m : matching) (d : nat) : Prop :=
  exists p, In (p, d) m /\ tok_of s d = Some (TClose true) /\ region_end s d true = None.

(* The three rules of `valid`, one token at a time. *)
Definition pair_ok (s : string) (m : matching) (os : list nat) (i j : nat) : Prop :=
  exists k, close_key s j = Some k /\ chain s m j
    /\ closest_live s m os j k i /\ (needs_content k = true -> tok_end s i < j).

Definition unmatched_ok (s : string) (m : matching) (os : list nat) (j : nat) : Prop :=
  forall k, close_key s j = Some k -> chain s m j -> ~ closes m j ->
    forall p, closest_live s m os j k p -> needs_content k = true /\ tok_end s p = j.

Definition opener_ok (s : string) (m : matching) (os : list nat) (q : nat) : Prop :=
  In q os <->
    (exists k, open_key s q = Some k) /\ chain s m q /\ ~ closes m q
    /\ forall k, close_key s q = Some k -> ~ barred s m os q k.

Record rinv (s : string) (n : nat) (st : rstate) : Prop := RInv {
  ri_bound_pairs : forall i j, In (i, j) (rs_pairs st) -> j < n;
  ri_bound_os : forall q, In q (rs_os st) -> q < n;
  ri_cand : forall q k,
    In (LOpen q k) (rs_live st) <-> cand s (rs_pairs st) (rs_os st) n q k;
  ri_bar : forall d, In (LBar d) (rs_live st) <-> bar s (rs_pairs st) d;
  ri_desc : ldesc (rs_live st);
  ri_pairs : forall i j, In (i, j) (rs_pairs st) -> pair_ok s (rs_pairs st) (rs_os st) i j;
  ri_unmatched : forall j, j < n -> unmatched_ok s (rs_pairs st) (rs_os st) j;
  ri_os : forall q, q < n -> opener_ok s (rs_pairs st) (rs_os st) q
}.

(* What a token's rules read is settled before it. *)
Lemma pair_ok_agree : forall s m os m' os' n i j,
  agree m os m' os' n -> j <= n -> pair_ok s m os i j -> pair_ok s m' os' i j.
Proof.
  intros s m os m' os' n i j A Hj (k & Hk & Hc & Hl & Hn).
  exists k. split; [exact Hk|]. split; [|split; [|exact Hn]].
  - exact (chain_agree s m os m' os' n j A Hj Hc).
  - exact (closest_live_agree s m os m' os' n j k i A Hj Hl).
Qed.

Lemma unmatched_ok_agree : forall s m os m' os' n j,
  agree m os m' os' n -> j < n -> unmatched_ok s m os j -> unmatched_ok s m' os' j.
Proof.
  intros s m os m' os' n j A Hj U k Hk Hc Hnc p Hp.
  pose proof (agree_sym _ _ _ _ _ A) as A'.
  apply (U k Hk).
  - exact (chain_agree s m' os' m os n j A' ltac:(lia) Hc).
  - intros H. apply Hnc. exact (closes_agree m m' os os' n A j Hj H).
  - exact (closest_live_agree s m' os' m os n j k p A' ltac:(lia) Hp).
Qed.

Lemma opener_ok_agree : forall s m os m' os' n q,
  agree m os m' os' n -> q < n -> opener_ok s m os q -> opener_ok s m' os' q.
Proof.
  intros s m os m' os' n q A Hq O.
  pose proof (agree_sym _ _ _ _ _ A) as A'.
  unfold opener_ok in *. split.
  - intros H. apply (proj2 A q Hq) in H. apply O in H as (Ho & Hc & Hnc & Hb).
    split; [exact Ho|]. split; [|split].
    + exact (chain_agree s m os m' os' n q A ltac:(lia) Hc).
    + intros H. apply Hnc. exact (closes_agree m' m os' os n A' q Hq H).
    + intros k Hk H. apply (Hb k Hk).
      exact (barred_agree s m' os' m os n q k A' ltac:(lia) H).
  - intros (Ho & Hc & Hnc & Hb). apply (proj2 A q Hq). apply O.
    split; [exact Ho|]. split; [|split].
    + exact (chain_agree s m' os' m os n q A' ltac:(lia) Hc).
    + intros H. apply Hnc. exact (closes_agree m m' os os' n A q Hq H).
    + intros k Hk H. apply (Hb k Hk).
      exact (barred_agree s m os m' os' n q k A ltac:(lia) H).
Qed.

(* Under the invariant, liveness is read off the stack. *)
Lemma live_stack : forall s n st q k,
  rinv s n st ->
  live s (rs_pairs st) (rs_os st) n q k <-> In (LOpen q k) (rs_live st) /\ clear (rs_live st) q.
Proof.
  intros s n st q k I. unfold live. rewrite (ri_cand s n st I). split.
  - intros [Hc Hb]. split; [exact Hc|]. intros d Hd.
    destruct (le_lt_dec d q) as [Hle|Hlt]; [exact Hle|]. exfalso. apply Hb.
    apply (ri_bar s n st I) in Hd as (p & Hp & Ht & He).
    exists p, d. split; [exact Hp|]. split; [exact Ht|]. split; [exact He|].
    split; [exact Hlt|exact (ri_bound_pairs s n st I p d Hp)].
  - intros [Hc Hcl]. split; [exact Hc|]. intros (p & d & Hp & Ht & He & Hq & _).
    assert (In (LBar d) (rs_live st)) as Hd
      by (apply (ri_bar s n st I); exists p; auto).
    specialize (Hcl d Hd). lia.
Qed.

Local Lemma pairs_lt : forall s n st i j,
  rinv s n st -> In (i, j) (rs_pairs st) -> i < j.
Proof.
  intros s n st i j I H. destruct (ri_pairs s n st I i j H) as (_ & _ & _ & [[(_ & Hq & _) _] _] & _).
  exact Hq.
Qed.

Local Lemma dead_succ : forall m n q,
  (forall i j, In (i, j) m -> j < n) -> (dead m (S n) q <-> dead m n q).
Proof.
  intros m n q B. split.
  - intros [(j' & Hj & H)|(i' & j' & Hj & H & Hb)].
    + left. exists j'. split; [exact (B _ _ H)|exact H].
    + right. exists i', j'. split; [exact (B _ _ H)|]. split; assumption.
  - intros [(j' & Hj & H)|(i' & j' & Hj & H & Hb)].
    + left. exists j'. split; [lia|exact H].
    + right. exists i', j'. split; [lia|]. split; assumption.
Qed.

(* No pair closes at `n`. *)
Local Lemma cand_succ : forall s n st os' q k,
  rinv s n st -> (forall q', q' < n -> In q' os' <-> In q' (rs_os st)) ->
  cand s (rs_pairs st) os' (S n) q k
  <-> cand s (rs_pairs st) (rs_os st) n q k
      \/ (q = n /\ In n os' /\ open_key s n = Some k).
Proof.
  intros s n st os' q k I Hos.
  pose proof (ri_bound_pairs s n st I) as B. pose proof (ri_bound_os s n st I) as Bo. split.
  - intros (Hin & Hq & Ho & Hc & Hd). destruct (Nat.eq_dec q n) as [->|Hne].
    + right. split; [reflexivity|]. split; assumption.
    + left. split; [apply Hos; [lia|exact Hin]|]. split; [lia|]. split; [exact Ho|].
      split; [exact Hc|]. intros H. apply Hd. apply dead_succ; assumption.
  - intros [(Hin & Hq & Ho & Hc & Hd)|(-> & Hin & Ho)].
    + split; [apply Hos; [exact Hq|exact Hin]|]. split; [lia|]. split; [exact Ho|].
      split; [exact Hc|]. intros H. apply Hd. apply (dead_succ _ n q B), H.
    + split; [exact Hin|]. split; [lia|]. split; [exact Ho|]. split.
      * intros [i Hi]. specialize (B _ _ Hi). lia.
      * intros [(j' & Hj & H)|(i' & j' & Hj & H & Hb)].
        -- specialize (B _ _ H). pose proof (pairs_lt s n st _ _ I H). lia.
        -- specialize (B _ _ H). lia.
Qed.

(* A pair closes at `n` with its opener `p` live. *)
Local Lemma cand_pair : forall s n st p q k,
  rinv s n st -> p < n ->
  cand s ((p, n) :: rs_pairs st) (rs_os st) (S n) q k
  <-> cand s (rs_pairs st) (rs_os st) n q k /\ q < p.
Proof.
  intros s n st p q k I Hpn.
  pose proof (ri_bound_pairs s n st I) as B. pose proof (ri_bound_os s n st I) as Bo.
  assert (Dead : dead ((p, n) :: rs_pairs st) (S n) q
                 <-> dead (rs_pairs st) n q \/ q = p \/ p < q < n).
  { split.
    - intros [(j' & Hj & [E|H])|(i' & j' & Hj & [E|H] & Hb)].
      + injection E as -> ->. right. left. reflexivity.
      + left. left. exists j'. split; [exact (B _ _ H)|exact H].
      + injection E as -> ->. right. right. exact Hb.
      + left. right. exists i', j'. split; [exact (B _ _ H)|]. split; assumption.
    - intros [[(j' & Hj & H)|(i' & j' & Hj & H & Hb)]|[->|Hb]].
      + left. exists j'. split; [lia|right; exact H].
      + right. exists i', j'. split; [lia|]. split; [right; exact H|exact Hb].
      + left. exists n. split; [lia|left; reflexivity].
      + right. exists p, n. split; [lia|]. split; [left; reflexivity|exact Hb]. }
  split.
  - intros (Hin & Hq & Ho & Hc & Hd).
    assert (Hqn : q < n) by (specialize (Bo q Hin); lia).
    rewrite Dead in Hd.
    split; [|destruct (lt_eq_lt_dec q p) as [[H|H]|H]; [exact H|tauto|]; exfalso; apply Hd; right; right; lia].
    split; [exact Hin|]. split; [exact Hqn|]. split; [exact Ho|]. split.
    + intros [i Hi]. apply Hc. exists i. right. exact Hi.
    + intros H. apply Hd. left. exact H.
  - intros [(Hin & Hq & Ho & Hc & Hd) Hqp].
    split; [exact Hin|]. split; [lia|]. split; [exact Ho|]. split.
    + intros [i [E|Hi]]; [injection E as _ ->; lia|]. apply Hc. exists i. exact Hi.
    + rewrite Dead. intros [H|[H|H]]; [exact (Hd H)|lia|lia].
Qed.

(* A byte off the chain: nothing changes. *)
Local Lemma rinv_skip : forall s n st,
  rinv s n st -> ~ chain s (rs_pairs st) n -> rinv s (S n) st.
Proof.
  intros s n st I Hc.
  assert (Hno : ~ In n (rs_os st)) by (intros H; specialize (ri_bound_os s n st I n H); lia).
  constructor.
  - intros i j H. specialize (ri_bound_pairs s n st I i j H). lia.
  - intros q H. specialize (ri_bound_os s n st I q H). lia.
  - intros q k. rewrite (ri_cand s n st I), (cand_succ s n st (rs_os st) q k I (fun _ _ => iff_refl _)).
    split; [intros H; left; exact H|intros [H|(_ & H & _)]; [exact H|contradiction]].
  - exact (ri_bar s n st I).
  - exact (ri_desc s n st I).
  - exact (ri_pairs s n st I).
  - intros j Hj. destruct (Nat.eq_dec j n) as [->|Hne];
      [|apply (ri_unmatched s n st I); lia].
    intros k _ Hch. contradiction.
  - intros q Hq. destruct (Nat.eq_dec q n) as [->|Hne];
      [|apply (ri_os s n st I); lia].
    split; [contradiction|intros (_ & Hch & _); contradiction].
Qed.

Local Lemma rinv_skip_to : forall s a b st,
  rinv s a st -> a <= b -> (forall j, a <= j < b -> ~ chain s (rs_pairs st) j) ->
  rinv s b st.
Proof.
  intros s a b st I Hab. induction Hab as [|b Hab IH]; intros Hoff; [exact I|].
  apply rinv_skip; [apply IH; intros j Hj; apply Hoff; lia|apply Hoff; lia].
Qed.

(* A token that closes nothing: it opens or it is text. *)
Local Lemma rinv_noclose : forall s n st op K,
  rinv s n st ->
  (op = true -> open_key s n = Some K) ->
  opener_ok s (rs_pairs st) (if op then n :: rs_os st else rs_os st) n ->
  unmatched_ok s (rs_pairs st) (if op then n :: rs_os st else rs_os st) n ->
  rinv s (S n)
    (RState (if op then LOpen n K :: rs_live st else rs_live st) (rs_pairs st)
       (if op then n :: rs_os st else rs_os st)).
Proof.
  intros s n st op K I HK Ho Hu.
  set (os' := if op then n :: rs_os st else rs_os st).
  assert (Hos : forall q, q < n -> In q os' <-> In q (rs_os st)).
  { intros q Hq. unfold os'. destruct op; [|reflexivity]. cbn.
    split; [intros [E|H]; [lia|exact H]|intros H; right; exact H]. }
  assert (A : agree (rs_pairs st) (rs_os st) (rs_pairs st) os' n).
  { split; [intros; reflexivity|]. intros q Hq. symmetry. apply Hos, Hq. }
  constructor; cbn [rs_live rs_pairs rs_os]; fold os'.
  - intros i j H. specialize (ri_bound_pairs s n st I i j H). lia.
  - intros q H. unfold os' in H. destruct op; [destruct H as [<-|H]; [lia|]|];
      specialize (ri_bound_os s n st I q H); lia.
  - intros q k. rewrite (cand_succ s n st os' q k I Hos), <- (ri_cand s n st I).
    unfold os'. destruct op.
    + specialize (HK eq_refl). cbn. split.
      * intros [E|H]; [injection E as <- <-; right; auto|left; exact H].
      * intros [H|(-> & _ & Ho')]; [right; exact H|].
        rewrite HK in Ho'. injection Ho' as <-. left. reflexivity.
    + split; [intros H; left; exact H|].
      intros [H|(-> & Hin & _)]; [exact H|].
      exfalso. specialize (ri_bound_os s n st I n Hin). lia.
  - intros d. destruct op; cbn; [|exact (ri_bar s n st I d)].
    rewrite <- (ri_bar s n st I d). split; [intros [E|H]; [discriminate|exact H]|].
    intros H; right; exact H.
  - destruct op; [|exact (ri_desc s n st I)]. constructor; [exact (ri_desc s n st I)|].
    apply Forall_forall. intros [q k|d] Hx; cbn.
    + apply (ri_cand s n st I) in Hx as (_ & Hq & _). exact Hq.
    + apply (ri_bar s n st I) in Hx as (p & H & _). exact (ri_bound_pairs s n st I p d H).
  - intros i j H. apply (pair_ok_agree s (rs_pairs st) (rs_os st) _ os' n i j A).
    + exact (Nat.lt_le_incl _ _ (ri_bound_pairs s n st I i j H)).
    + exact (ri_pairs s n st I i j H).
  - intros j Hj. destruct (Nat.eq_dec j n) as [->|Hne]; [exact Hu|].
    apply (unmatched_ok_agree s (rs_pairs st) (rs_os st) _ os' n j A); [lia|].
    apply (ri_unmatched s n st I). lia.
  - intros q Hq. destruct (Nat.eq_dec q n) as [->|Hne]; [exact Ho|].
    apply (opener_ok_agree s (rs_pairs st) (rs_os st) _ os' n q A); [lia|].
    apply (ri_os s n st I). lia.
Qed.

(* A token that closes a pair with `p`. *)
Local Lemma rinv_pair : forall s n st p K lv',
  rinv s n st -> chain s (rs_pairs st) n ->
  close_key s n = Some K ->
  closest_live s (rs_pairs st) (rs_os st) n K p ->
  (needs_content K = true -> tok_end s p < n) ->
  (forall q k, In (LOpen q k) lv' <-> In (LOpen q k) (rs_live st) /\ q < p) ->
  (forall d, In (LBar d) lv' <->
     In (LBar d) (rs_live st)
     \/ (d = n /\ tok_of s n = Some (TClose true) /\ region_end s n true = None)) ->
  ldesc lv' ->
  rinv s (S n) (RState lv' ((p, n) :: rs_pairs st) (rs_os st)).
Proof.
  intros s n st p K lv' I Hch HK Hcl Hne Hlv Hbar Hdesc.
  set (m' := (p, n) :: rs_pairs st).
  pose proof (ri_bound_pairs s n st I) as B.
  assert (Hpn : p < n) by (destruct Hcl as [((_ & Hp & _) & _) _]; exact Hp).
  assert (A : agree (rs_pairs st) (rs_os st) m' (rs_os st) n).
  { split; [|intros; reflexivity]. intros i j Hj. unfold m'. cbn. split.
    - intros H. right. exact H.
    - intros [E|H]; [injection E as _ ->; lia|exact H]. }
  constructor; cbn [rs_live rs_pairs rs_os]; fold m'.
  - intros i j [E|H]; [injection E as _ <-; lia|specialize (B i j H); lia].
  - intros q H. specialize (ri_bound_os s n st I q H). lia.
  - intros q k. unfold m'. rewrite Hlv, (cand_pair s n st p q k I Hpn), (ri_cand s n st I).
    reflexivity.
  - intros d. rewrite Hbar, (ri_bar s n st I d). unfold bar. split.
    + intros [(p' & H & Hd & He)|(-> & Hd & He)].
      * exists p'. split; [right; exact H|]. split; assumption.
      * exists p. split; [left; reflexivity|]. split; assumption.
    + intros (p' & [E|H] & Hd & He).
      * injection E as -> ->. right. auto.
      * left. exists p'. auto.
  - exact Hdesc.
  - intros i j [E|H].
    + injection E as <- <-. exists K. split; [exact HK|]. split.
      * exact (chain_agree s (rs_pairs st) (rs_os st) m' (rs_os st) n n A (le_n n) Hch).
      * split; [|exact Hne].
        exact (closest_live_agree s (rs_pairs st) (rs_os st) m' (rs_os st) n n K p A (le_n n) Hcl).
    + apply (pair_ok_agree s (rs_pairs st) (rs_os st) m' (rs_os st) n i j A).
      * exact (Nat.lt_le_incl _ _ (B i j H)).
      * exact (ri_pairs s n st I i j H).
  - intros j Hj. destruct (Nat.eq_dec j n) as [->|Hne'].
    + intros k _ _ Hc. exfalso. apply Hc. exists p. left. reflexivity.
    + apply (unmatched_ok_agree s (rs_pairs st) (rs_os st) m' (rs_os st) n j A); [lia|].
      apply (ri_unmatched s n st I). lia.
  - intros q Hq. destruct (Nat.eq_dec q n) as [->|Hne'].
    + split.
      * intros H. specialize (ri_bound_os s n st I n H). lia.
      * intros (_ & _ & Hc & _). exfalso. apply Hc. exists p. left. reflexivity.
    + apply (opener_ok_agree s (rs_pairs st) (rs_os st) m' (rs_os st) n q A); [lia|].
      apply (ri_os s n st I). lia.
Qed.

Local Lemma ldesc_pos_inj : forall lv x y,
  ldesc lv -> In x lv -> In y lv -> lpos x = lpos y -> x = y.
Proof.
  induction lv as [|z lv IH]; intros x y D Hx Hy E; [destruct Hx|].
  apply StronglySorted_inv in D as [D F]. rewrite Forall_forall in F.
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy]; [reflexivity| | |exact (IH x y D Hx Hy E)].
  - specialize (F y Hy). lia.
  - specialize (F x Hx). lia.
Qed.

(* What a found opener leaves below it. *)
Local Lemma pick_below : forall s n st K p below,
  rinv s n st -> pick K (rs_live st) = PFound p below ->
  closest_live s (rs_pairs st) (rs_os st) n K p
  /\ (forall q k, In (LOpen q k) below <-> In (LOpen q k) (rs_live st) /\ q < p)
  /\ (forall d, In (LBar d) below <-> In (LBar d) (rs_live st))
  /\ ldesc below
  /\ (forall x, In x below -> lpos x < p).
Proof.
  intros s n st K p below I P.
  pose proof (ri_desc s n st I) as D.
  destruct (pick_found K _ p below D P) as (Hin & Hcl & Hmax & Hb & Db & Ha).
  split; [|split; [|split; [|split]]].
  - split; [apply (live_stack s n st p K I); split; assumption|].
    intros q Hq. apply (live_stack s n st q K I) in Hq as [Hq Hc]. exact (Hmax q Hq Hc).
  - intros q k. rewrite Hb. reflexivity.
  - intros d. rewrite Hb. split; [intros [H _]; exact H|]. intros H. split; [exact H|].
    cbn. specialize (Hcl d H).
    destruct (Nat.eq_dec d p) as [->|Hne]; [|lia].
    pose proof (ldesc_pos_inj _ _ _ D H Hin eq_refl). discriminate.
  - exact Db.
  - intros x Hx. apply Hb in Hx as [_ Hx]. exact Hx.
Qed.

Local Lemma pick_not_live : forall s n st K p,
  rinv s n st -> pick K (rs_live st) = PBarred \/ pick K (rs_live st) = PNone ->
  ~ closest_live s (rs_pairs st) (rs_os st) n K p.
Proof.
  intros s n st K p I P [Hp _]. apply (live_stack s n st p K I) in Hp as [Hin Hc].
  destruct P as [P|P].
  - destruct (pick_barred K _ (ri_desc s n st I) P) as [Hn _]. exact (Hn p Hin Hc).
  - exact (pick_none K _ P p Hin).
Qed.

Lemma rinv_step : forall s n st t,
  tok_of s n = Some t -> rinv s n st -> chain s (rs_pairs st) n ->
  rinv s (S n) (rstep s n t st).
Proof.
  intros s n [lv m os] t Hn I Hch.
  assert (Hok : open_key s n = opens_as t) by (unfold open_key; rewrite Hn; reflexivity).
  assert (Hck : close_key s n = closes_as t) by (unfold close_key; rewrite Hn; reflexivity).
  assert (Hnc : ~ closes m n)
    by (intros [i Hi]; specialize (ri_bound_pairs s n _ I i n Hi); cbn in *; lia).
  assert (Hnos : ~ In n os) by (intros H; specialize (ri_bound_os s n _ I n H); cbn in *; lia).
  cbn [rs_pairs] in Hch.
  unfold rstep; cbn [rs_live rs_pairs rs_os].
  pose (st := RState lv m os).
  assert (NC : forall op K,
            (op = true -> open_key s n = Some K) ->
            opener_ok s m (if op then n :: os else os) n ->
            unmatched_ok s m (if op then n :: os else os) n ->
            rinv s (S n) (RState (if op then LOpen n K :: lv else lv) m
                             (if op then n :: os else os)))
    by (intros op K; exact (rinv_noclose s n st op K I)).
  assert (Aos : forall op : bool, agree m os m (if op then n :: os else os) n).
  { intros op. split; [intros; reflexivity|]. intros q Hq. destruct op; [|reflexivity]. cbn.
    split; [intros H; right; exact H|intros [E|H]; [lia|exact H]]. }
  assert (OO : forall (op : bool) (K : key), open_key s n = (if op then Some K else None) ->
            (forall k, close_key s n = Some k -> op = true -> ~ barred s m os n k) ->
            opener_ok s m (if op then n :: os else os) n).
  { intros [|] K Ho Hb.
    - split; [intros _|intros _; left; reflexivity].
      split; [exists K; exact Ho|]. split; [exact Hch|]. split; [exact Hnc|].
      intros k Hk Hbar. apply (Hb k Hk eq_refl).
      exact (barred_agree s m (n :: os) m os n n k (agree_sym _ _ _ _ _ (Aos true))
               (le_n n) Hbar).
    - split; [intros H; contradiction|intros [[k Hk] _]; congruence]. }
  assert (UN : forall (op : bool) K,
            (forall p, ~ closest_live s m os n K p) -> close_key s n = Some K ->
            unmatched_ok s m (if op then n :: os else os) n).
  { intros op K Hn' HK k Hk _ _ p Hp. rewrite HK in Hk. injection Hk as <-.
    exfalso. apply (Hn' p).
    exact (closest_live_agree s m _ m os n n K p (agree_sym _ _ _ _ _ (Aos op)) (le_n n) Hp). }
  assert (Nolive : forall K, pick K lv = PBarred \/ pick K lv = PNone ->
            forall p, ~ closest_live s m os n K p)
    by (intros K P p; exact (pick_not_live s n st K p I P)).
  assert (Text : opens_as t = None -> closes_as t = None -> rinv s (S n) st).
  { intros Ho Hc. apply (NC false KBracket); [discriminate| |].
    - apply (OO false KBracket); [rewrite Hok; exact Ho|intros k Hk; congruence].
    - intros k Hk. congruence. }
  (* text, a break and the escapes neither open nor close *)
  destruct t as [c| |k mr op cl| |b|c|ws|ws|vp vn vb vc vr|dk|asrc aok|sa]; try (apply Text; reflexivity).
  - (* a delimiter *)
    set (K := KDelim k mr).
    assert (Hop : open_key s n = if op then Some K else None)
      by (rewrite Hok; destruct op; reflexivity).
    assert (Ropen : (forall k', close_key s n = Some k' -> ~ barred s m os n k') ->
              (forall op' : bool, unmatched_ok s m (if op' then n :: os else os) n) ->
              rinv s (S n) (ropen n K op st)).
    { intros Hnb Hu. unfold ropen. destruct op; cbn [rs_live rs_pairs rs_os].
      - apply (NC true K); [intros _; exact Hop|apply (OO true K Hop)|apply (Hu true)].
        intros k' Hk' _. exact (Hnb k' Hk').
      - apply (NC false K); [discriminate|apply (OO false K Hop)|apply (Hu false)].
        intros k' _ E. discriminate E. }
    destruct cl.
    2: { cbn. apply Ropen.
         - intros k' Hk'. rewrite Hck in Hk'. discriminate.
         - intros op' k' Hk'. rewrite Hck in Hk'. discriminate. }
    assert (HK : close_key s n = Some K) by (rewrite Hck; reflexivity).
    destruct (pick K lv) as [p below| |] eqn:P.
    + destruct (pick_below s n st K p below I P) as (Hcl & Hlv & Hbar & Db & Hlt).
      unfold st in Hcl, Hlv, Hbar; cbn [rs_live rs_pairs rs_os] in Hcl, Hlv, Hbar.
      destruct (Nat.ltb (tok_end s p) n) eqn:L.
      * apply Nat.ltb_lt in L.
        apply (rinv_pair s n st p K below I Hch HK Hcl (fun _ => L) Hlv).
        -- intros d. rewrite Hbar. split; [intros H; left; exact H|].
           intros [H|(_ & E & _)]; [exact H|congruence].
        -- exact Db.
      * apply Nat.ltb_ge in L. apply Ropen.
        -- intros k' Hk' [Hn' _]. rewrite HK in Hk'. injection Hk' as <-.
           exact (Hn' p (proj1 Hcl)).
        -- intros op' k' Hk' _ _ p' Hp'. rewrite HK in Hk'. injection Hk' as <-.
           pose proof (closest_live_agree s m _ m os n n K p'
                         (agree_sym _ _ _ _ _ (Aos op')) (le_n n) Hp') as Hp''.
           rewrite <- (closest_live_fun s m os n K p p' Hcl Hp'').
           split; [reflexivity|].
           destruct Hcl as [[(Hin & Hpn & Hop' & _) _] _].
           pose proof (proj1 (ri_os s n st I p Hpn) Hin) as (_ & Hchp & _).
           destruct (chain_between s m n p Hchp Hch Hpn) as (q & Hq & Hqn).
           unfold open_key, tok_of in Hop'. unfold tok_end in *. unfold chain_next in Hq.
           destruct (tok_at s p) as [[tp lp]|]; [|discriminate].
           destruct tp; try (injection Hq as <-; lia). discriminate Hop'.
    + (* barred: text *)
      destruct (pick_barred K lv (ri_desc s n st I) P) as [Hnl [q Hq]].
      apply (NC false K); [discriminate| |apply (UN false K (Nolive K (or_introl P)) HK)].
      split; [intros H; contradiction|]. intros ([k' Hk'] & _ & _ & Hb).
      exfalso. apply (Hb K HK). split.
      * intros q' Hq'. apply (live_stack s n st q' K I) in Hq' as [Hin Hc].
        exact (Hnl q' Hin Hc).
      * exists q. apply (ri_cand s n st I). exact Hq.
    + apply Ropen.
      * intros k' Hk' [_ (q & Hq)]. rewrite HK in Hk'. injection Hk' as <-.
        apply (ri_cand s n st I) in Hq. exact (pick_none K lv P q Hq).
      * intros op'. apply (UN op' K (Nolive K (or_intror P)) HK).
  - (* a `[` *)
    apply (NC true KBracket); [intros _; rewrite Hok; reflexivity|apply (OO true KBracket)|].
    + rewrite Hok. reflexivity.
    + intros k Hk. rewrite Hck in Hk. discriminate.
    + intros k Hk. rewrite Hck in Hk. discriminate.
  - (* a `]` that may close *)
    assert (HK : close_key s n = Some KBracket) by (rewrite Hck; reflexivity).
    destruct (pick KBracket lv) as [p below| |] eqn:P.
    2,3: apply (NC false KBracket); [discriminate| |];
         [ split; [intros H; contradiction|intros ([k' Hk'] & _); rewrite Hok in Hk'; discriminate]
         | apply (UN false KBracket (Nolive KBracket ltac:(auto)) HK) ].
    destruct (pick_below s n st KBracket p below I P) as (Hcl & Hlv & Hbar & Db & Hlt).
    unfold st in Hcl, Hlv, Hbar; cbn [rs_live rs_pairs rs_os] in Hcl, Hlv, Hbar.
    destruct (region_end s n b) as [e|] eqn:R; [|destruct b].
    + apply (rinv_pair s n st p KBracket below I Hch HK Hcl
               (fun H => ltac:(discriminate H)) Hlv).
      * intros d. rewrite Hbar. split; [intros H; left; exact H|].
        intros [H|(_ & E1 & E)]; [exact H|]. rewrite Hn in E1. injection E1 as ->. congruence.
      * exact Db.
    + apply (rinv_pair s n st p KBracket (LBar n :: below) I Hch HK Hcl
               (fun H => ltac:(discriminate H))).
      * intros q k. cbn. rewrite <- Hlv. split; [intros [E|H]; [discriminate|exact H]|].
        intros H. right. exact H.
      * intros d. cbn. rewrite Hbar. split.
        -- intros [E|H]; [injection E as <-; right; auto|left; exact H].
        -- intros [H|(-> & _ & _)]; [right; exact H|left; reflexivity].
      * constructor; [exact Db|]. apply Forall_forall. intros x Hx.
        specialize (Hlt x Hx). cbn. destruct Hcl as [[(_ & Hp & _) _] _]. lia.
    + apply (rinv_pair s n st p KBracket below I Hch HK Hcl
               (fun H => ltac:(discriminate H)) Hlv).
      * intros d. rewrite Hbar. split; [intros H; left; exact H|].
        intros [H|(_ & E & _)]; [exact H|congruence].
      * exact Db.
Qed.

(* A step adds at most a pair closing at the token and the token as an
   opener. *)
Lemma rstep_grows : forall s i t st,
  (rs_pairs (rstep s i t st) = rs_pairs st
   \/ exists p, rs_pairs (rstep s i t st) = (p, i) :: rs_pairs st)
  /\ (rs_os (rstep s i t st) = rs_os st \/ rs_os (rstep s i t st) = i :: rs_os st).
Proof.
  intros s i t [lv m os]. unfold rstep. cbn [rs_live rs_pairs rs_os].
  assert (Ro : forall k op st',
            rs_pairs st' = m -> rs_os st' = os ->
            (rs_pairs (ropen i k op st') = m
             \/ exists p, rs_pairs (ropen i k op st') = (p, i) :: m)
            /\ (rs_os (ropen i k op st') = os \/ rs_os (ropen i k op st') = i :: os)).
  { intros k [|] st' E1 E2; unfold ropen; cbn [rs_pairs rs_os]; rewrite E1, E2;
      split; [left|right|left|left]; reflexivity. }
  destruct t as [c| |k mr op cl| |b|c|ws|ws|vp vn vb vc vr|dk|asrc aok|sa]; try (split; left; reflexivity).
  - destruct (if cl then pick (KDelim k mr) lv else PNone) as [p below| |];
      [destruct (Nat.ltb (tok_end s p) i)| |];
      try (apply Ro; reflexivity); try (split; left; reflexivity).
    cbn. split; [right; exists p; reflexivity|left; reflexivity].
  - apply Ro; reflexivity.
  - destruct (pick KBracket lv) as [p below| |]; try (split; left; reflexivity).
    destruct (region_end s i b), b; cbn;
      (split; [right; exists p; reflexivity|left; reflexivity]).
Qed.

(* Past the last token of the chain the invariant is the rules. *)
Local Lemma rinv_valid : forall s n st,
  rinv s n st ->
  (forall j, n <= j -> chain s (rs_pairs st) j -> tok_of s j = None) ->
  valid s (rs_pairs st, rs_os st).
Proof.
  intros s n st I Hend.
  split; [|split].
  - exact (ri_pairs s n st I).
  - intros j k Hk Hc. destruct (Nat.lt_ge_cases j n) as [Hj|Hj].
    + exact (ri_unmatched s n st I j Hj k Hk Hc).
    + unfold close_key in Hk. rewrite (Hend j Hj Hc) in Hk. discriminate.
  - intros q. destruct (Nat.lt_ge_cases q n) as [Hq|Hq].
    + exact (ri_os s n st I q Hq).
    + split.
      * intros H. specialize (ri_bound_os s n st I q H). lia.
      * intros ([k Hk] & Hc & _). unfold open_key in Hk.
        rewrite (Hend q Hq Hc) in Hk. discriminate.
Qed.

(* A step keeps the token on the chain; the invariant then holds at the
   next token, or the rules hold if there is none. *)
Lemma rinv_next : forall s n st t,
  rinv s n st -> chain s (rs_pairs st) n -> tok_of s n = Some t ->
  chain s (rs_pairs (rstep s n t st)) n
  /\ match chain_next s (rs_pairs (rstep s n t st)) n with
     | Some q => rinv s q (rstep s n t st) /\ chain s (rs_pairs (rstep s n t st)) q
     | None => valid s (rs_pairs (rstep s n t st), rs_os (rstep s n t st))
     end.
Proof.
  intros s n st t I Hch Ht.
  set (st' := rstep s n t st).
  pose proof (rinv_step s n st t Ht I Hch) as I'.
  destruct (rstep_grows s n t st) as [Gp Go]; fold st' in Gp, Go.
  assert (A : agree (rs_pairs st) (rs_os st) (rs_pairs st') (rs_os st') n).
  { split.
    - intros i j Hj. destruct Gp as [-> | [p ->]]; [reflexivity|]. cbn.
      split; [intros H0; right; exact H0|intros [E|H0]; [injection E as _ ->; lia|exact H0]].
    - intros q Hq. destruct Go as [-> | ->]; [reflexivity|]. cbn.
      split; [intros H0; right; exact H0|intros [E|H0]; [lia|exact H0]]. }
  assert (Hch' : chain s (rs_pairs st') n) by exact (chain_agree s _ _ _ _ n n A (le_n n) Hch).
  split; [exact Hch'|].
  destruct (chain_next s (rs_pairs st') n) as [q|] eqn:Hq.
  - pose proof (chain_next_bound s _ n q Hq) as Hb. split.
    + apply (rinv_skip_to s (S n) q st' I'); [lia|].
      intros j Hj. exact (chain_gap s _ n q j Hch' Hq ltac:(lia)).
    + exact (chain_step s _ n q Hch' Hq).
  - apply (rinv_valid s (S n) st' I'). intros j Hj Hc.
    pose proof (chain_none s _ n j Hch' Hq Hc). lia.
Qed.

(* Past the end of the paragraph. *)
Lemma rinv_end : forall s n st,
  rinv s n st -> chain s (rs_pairs st) n -> tok_of s n = None ->
  valid s (rs_pairs st, rs_os st).
Proof.
  intros s n st I Hch Ht. apply (rinv_valid s n st I). intros j Hj Hc.
  destruct (Nat.eq_dec j n) as [->|Hne]; [exact Ht|].
  destruct (chain_between s _ j n Hch Hc ltac:(lia)) as (q & Hq & _).
  unfold chain_next, tok_of in Hq, Ht. destruct (tok_at s n); [discriminate|].
  discriminate.
Qed.

Local Lemma rgo_valid : forall s f n st,
  rinv s n st -> chain s (rs_pairs st) n -> String.length s - n < f ->
  valid s (rs_pairs (rgo s f n st), rs_os (rgo s f n st)).
Proof.
  intros s f. induction f as [|f IH]; intros n st I Hch Hf; [lia|].
  cbn [rgo]. destruct (tok_of s n) as [t|] eqn:Ht; [|exact (rinv_end s n st I Hch Ht)].
  destruct (rinv_next s n st t I Hch Ht) as [_ N].
  destruct (chain_next s (rs_pairs (rstep s n t st)) n) as [q|] eqn:Hq; [|exact N].
  pose proof (chain_next_bound s _ n q Hq). destruct N as [I' Hq'].
  apply IH; [exact I'|exact Hq'|lia].
Qed.

Lemma rinv_start : forall s, rinv s 0 rstart.
Proof.
  intros s. constructor; cbn [rs_live rs_pairs rs_os rstart].
  - intros i j [].
  - intros q [].
  - intros q k. split; [intros []|intros ([] & _)].
  - intros d. split; [intros []|intros (p & [] & _)].
  - constructor.
  - intros i j [].
  - intros j H. lia.
  - intros q H. lia.
Qed.

Theorem ref_read_valid : forall s, valid s (ref_read s).
Proof.
  intros s. unfold ref_read.
  apply rgo_valid; [apply rinv_start|constructor|lia].
Qed.

(*
The tree
========

What a matching describes, read along its chain: each pair of
delimiters becomes its row's node around the tokens between, a bracket
pair with a region that ends becomes a link to the region's text, and
every other token is text.  Adjacent text is one `Str`, as the scanner
writes it. *)

Definition str_snoc (s : string) (out : inlines) : inlines :=
  match out with
  | Node p [] (Str t) :: rest => Node p [] (Str (t ++ s)) :: rest
  | _ => mk (Str s) :: out
  end.

(* An escaped byte as text: the byte if it is punctuation (O2), and the
   backslash and the byte otherwise (O3). *)
Definition esc_text (c : ascii) : string :=
  if is_punct c then one c else String bslash (one c).

(* A token as written. *)
Definition raw_text (raw : option string) : string :=
  match raw with
  | Some f => (String lbrace (String eqchar f) ++ one rbrace)%string
  | None => EmptyString
  end.

Definition tok_text (t : token) : string :=
  match t with
  | TText c => one c
  | TBreak => one nl_char
  | TDelim k false _ _ => dtoken k
  | TDelim k true true _ => (one lbrace ++ dtoken k)%string
  | TDelim k true false _ => (dtoken k ++ one rbrace)%string
  | TOpen => one lbrack
  | TClose _ => one rbrack
  | TEsc c => String bslash (one c)
  | TEscWs ws => String bslash ws
  | THard ws => String bslash ws
  | TVerb pre n body closed raw =>
      (chars dollar pre ++ ticks n ++ body ++ (if closed then ticks n else EmptyString)
       ++ raw_text raw)%string
  | TDollars k => chars dollar k
  | TAuto src ok => (String lt src ++ if ok then one gt else EmptyString)%string
  | TSymbol a => (String ":"%char a ++ one ":"%char)%string
  end.

(* A run escaped by a backslash is a non-breaking space and the rest of
   the run when it begins with a space (O5). *)
Definition nbsp_rest (ws : string) : option string :=
  match ws with
  | String c rest => if Ascii.eqb c " "%char then Some rest else None
  | EmptyString => None
  end.

(* "Spaces and tab characters before the backslash are ignored" (O4): a
   hard break trims the text right before it. *)
Definition str_trim (out : inlines) : inlines :=
  match out with
  | Node p [] (Str t) :: rest =>
      match strip_trailing_ws t with
      | EmptyString => rest
      | t' => Node p [] (Str t') :: rest
      end
  | _ => out
  end.

(* A destination is written without its line breaks. *)
Fixpoint no_nl (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => if Ascii.eqb c nl_char then no_nl rest else String c (no_nl rest)
  end.

(* A destination's bytes with their escapes decoded. *)
Fixpoint dest_text (esc : bool) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if esc then (esc_text c ++ dest_text false rest)%string
      else if is_bslash c then dest_text true rest
      else String c (dest_text false rest)
  end.

(* The text of the region after a `]` at `d` that ends at `e`, its `(` or
   `[` aside. *)
Definition region_text (s : string) (d e : nat) (dest : bool) : string :=
  let txt := substring (S (S d)) (e - S (S d)) s in
  if dest then dest_text false txt else txt.

(* The link a bracket pair and its region make: to the destination, or
   to the label, which an empty label takes from the link text. *)
Definition region_node (dest : bool) (kids : inlines) (txt : string) : inline :=
  if dest then Link kids (Direct (no_nl txt))
  else Link kids (Reference (normalize_label
                    (match txt with
                     | EmptyString => reference_inlines_text kids
                     | _ => txt
                     end))).

Inductive tkind : Type := TKDelim (k : dstyle) | TKBracket.

(* The frames of the open pairs, innermost first, each with its kind and
   its content reversed, above the reversed top level. *)
Definition tframes : Type := list (tkind * inlines).

Definition temit (n : node inline) (fs : tframes) (top : inlines)
  : tframes * inlines :=
  match fs with
  | [] => ([], n :: top)
  | (k, acc) :: rest => ((k, n :: acc) :: rest, top)
  end.

Definition temit_str (s : string) (fs : tframes) (top : inlines)
  : tframes * inlines :=
  match fs with
  | [] => ([], str_snoc s top)
  | (k, acc) :: rest => ((k, str_snoc s acc) :: rest, top)
  end.

Definition ttrim (fs : tframes) (top : inlines) : tframes * inlines :=
  match fs with
  | [] => ([], str_trim top)
  | (k, acc) :: rest => ((k, str_trim acc) :: rest, top)
  end.

(* Nodes in order, plain text merging at the seams. *)
Fixpoint temit_all (ns : inlines) (fs : tframes) (top : inlines)
  : tframes * inlines :=
  match ns with
  | [] => (fs, top)
  | Node _ [] (Str s) :: rest =>
      let '(fs', top') := temit_str s fs top in temit_all rest fs' top'
  | n :: rest => let '(fs', top') := temit n fs top in temit_all rest fs' top'
  end.

Definition is_hard (t : token) : bool := match t with THard _ => true | _ => false end.

(* The node of a verbatim with `pre` dollars before it and its raw
   spec. *)
Definition verb_node (pre : nat) (raw : option string) (body : string) : inline :=
  match raw, pre with
  | Some f, _ => RawInline f (trim_verb body)
  | None, 0 => Verbatim (trim_verb body)
  | None, 1 => Math InlineMath (trim_verb body)
  | None, _ => Math DisplayMath (trim_verb body)
  end.

(* One token of the chain; `hard` says the token before it was a hard
   break, which a break right after is part of.  A reference label that
   never ends is text, brackets and all, to the paragraph's end. *)
Definition tstep (s : string) (m : matching) (i : nat) (t : token) (hard : bool)
  (fs : tframes) (top : inlines) : tframes * inlines :=
  match t with
  | TText _ => temit_str (tok_text t) fs top
  | TEsc c => temit_str (esc_text c) fs top
  | TEscWs ws =>
      match nbsp_rest ws with
      | Some rest =>
          let '(fs', top') := temit (mk NonBreakingSpace) fs top in
          if nonempty_str rest then temit_str rest fs' top' else (fs', top')
      | None => temit_str (tok_text t) fs top
      end
  | THard _ => let '(fs', top') := ttrim fs top in temit (mk HardBreak) fs' top'
  | TVerb pre _ body _ raw =>
      let '(fs', top') := if Nat.ltb 2 pre then temit_str (chars dollar (pre - 2)) fs top
                          else (fs, top) in
      temit (mk (verb_node pre raw body)) fs' top'
  | TDollars _ => temit_str (tok_text t) fs top
  | TAuto src ok => if ok then temit (mk (auto_node src)) fs top else temit_str (tok_text t) fs top
  | TSymbol a => temit (mk (Symbol a)) fs top
  | TBreak => if hard then (fs, top) else temit (mk SoftBreak) fs top
  | TDelim k _ _ _ =>
      if is_opener m i then ((TKDelim k, []) :: fs, top)
      else match is_closer m i, fs with
           | true, (TKDelim k', acc) :: fs0 => temit (mk (dnode k' (List.rev acc))) fs0 top
           | _, _ => temit_str (tok_text t) fs top
           end
  | TOpen =>
      if is_opener m i then ((TKBracket, []) :: fs, top)
      else temit_str (tok_text t) fs top
  | TClose b =>
      match is_closer m i, fs with
      | true, (_, acc) :: fs0 =>
          let kids := List.rev acc in
          match region_end s i b with
          | Some e => temit (mk (region_node b kids (region_text s i e b))) fs0 top
          | None =>
              temit_all (mk (Str (one lbrack)) :: kids
                         ++ [mk (Str (one rbrack ++ if b then EmptyString else sdrop (S i) s))])%list
                fs0 top
          end
      | _, _ => temit_str (tok_text t) fs top
      end
  end.

Fixpoint tgo (s : string) (m : matching) (fuel i : nat) (hard : bool)
  (fs : tframes) (top : inlines) : tframes * inlines :=
  match fuel with
  | O => (fs, top)
  | S f =>
      match tok_of s i with
      | None => (fs, top)
      | Some t =>
          let '(fs', top') := tstep s m i t hard fs top in
          match chain_next s m i with
          | Some q => tgo s m f q (is_hard t) fs' top'
          | None => (fs', top')
          end
      end
  end.

(* A valid matching closes every pair it opens, so no frame is left at
   the end. *)
Definition tree_of (s : string) (m : matching) : inlines :=
  List.rev (snd (tgo s m (S (String.length s)) 0 false [] [])).

End WithTable.
