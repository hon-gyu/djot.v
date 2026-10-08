(* ai-disclosure: autonomous *)

(* The reference's precedence rules for delimiters and brackets (syntax
   reference, "Precedence"), stated as a reading of a paragraph's tokens
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
   braces, the brackets, and bytes that no row and no other syntax
   claims, the parens among them.  A paren is not a row's character
   here, since a destination counts parens.  The newline ends the
   line, and a hole's `%` is not drawn on while holes are on. *)
Definition in_alphabet (c : ascii) : bool :=
  (negb (Ascii.eqb c nl_char)
   && (Ascii.eqb c lbrace || Ascii.eqb c rbrace || Ascii.eqb c lbrack
       || Ascii.eqb c rbrack
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

(* What may follow a byte.  A `{` before anything but a row's character
   begins an attribute spec, and so does one after a `]`; a `[` before a
   `^` begins a footnote reference and before a `[` a wikilink. *)
Definition follow_ok (c : ascii) (rest : string) : bool :=
  ((negb (Ascii.eqb c lbrace) || starts_row rest)
   && negb (Ascii.eqb c lbrack && (starts_with lbrack rest || starts_with hat rest))
   && negb (Ascii.eqb c rbrack && starts_with lbrace rest))%bool.

(* A backslash escapes the byte after it, whatever that byte is, so the
   escaped byte is not drawn on the alphabet (O2, O3). *)
Fixpoint over_alphabet (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c rest =>
      if is_bslash c
      then match rest with
           | EmptyString => true
           | String _ rest' => over_alphabet rest'
           end
      else (in_alphabet c && follow_ok c rest && over_alphabet rest)%bool
  end.

(* A text token is one byte, so that every token is nonempty.  A marked
   token is an opener `{_` or a closer `_}`, never both.  A break is the
   end of a paragraph's line: a soft break in the tree, and whitespace to
   the delimiters on either side of it.  `TOpen` is a `[`, and `TClose` a
   `]` followed by `(`, which begins a destination (`dest`), or by `[`,
   which begins a reference label; a `]` before anything else is text.

   A backslash and what follows it are an escape (O2 to O5): before
   whitespace that runs to the end of the line, a hard break (`THard`,
   with that whitespace); before a run of whitespace that does not, the
   run (`TEscWs`), which is a non-breaking space and the rest of the run
   when it begins with a space; before any other byte, that byte as text
   if it is punctuation, and the backslash and the byte otherwise
   (`TEsc`). *)
Inductive token : Type :=
  | TText (c : ascii)
  | TBreak
  | TDelim (k : dstyle) (marked opens closes : bool)
  | TOpen
  | TClose (dest : bool)
  | TEsc (c : ascii)
  | TEscWs (ws : string)
  | THard (ws : string).

(* The whitespace a string begins with. *)
Fixpoint ws_run (s : string) : string :=
  match s with
  | String c rest => if is_ws c then String c (ws_run rest) else EmptyString
  | EmptyString => EmptyString
  end.

Definition at_rbrace (p : option ascii) : bool :=
  match p with Some b => Ascii.eqb b rbrace | None => false end.

(* A run of a row's character is cut, left to right, into tokens of the
   row's width, and a remainder shorter than that is text.  A token with
   `{` before it is a marked opener, and one with `}` after it a marked
   closer (P3).  A bare token may open when its row may be written bare
   and the byte after it is not whitespace, and may close when the byte
   before it is not whitespace (M2).  `prev` is the byte before `s`, and
   `skip` counts the bytes of a token already emitted that are still to
   be read. *)
Fixpoint lex (prev : option ascii) (skip : nat) (s : string) : list token :=
  match s with
  | EmptyString => []
  | String c rest =>
      match skip with
      | S n => lex (Some c) n rest
      | O =>
          if is_bslash c then
            (if is_blank rest then THard rest
             else match rest with
                  | String d _ => if is_ws d then TEscWs (ws_run rest) else TEsc d
                  | EmptyString => THard EmptyString
                  end)
              :: lex (Some c)
                   (if is_blank rest then String.length rest
                    else match rest with
                         | String d _ => if is_ws d then String.length (ws_run rest) else 1
                         | EmptyString => 0
                         end) rest
          else if Ascii.eqb c lbrack then TOpen :: lex (Some c) 0 rest
          else if Ascii.eqb c rbrack then
            (if starts_with lparen rest then TClose true
             else if starts_with lbrack rest then TClose false
             else TText c) :: lex (Some c) 0 rest
          else if Ascii.eqb c lbrace then
            match (match rest with
                   | String d _ => dstyle_of d
                   | EmptyString => None
                   end) with
            | Some k =>
                if prefix (dtoken k) rest
                then TDelim k true true false :: lex (Some c) (dwidth k) rest
                else TText c :: lex (Some c) 0 rest
            | None => TText c :: lex (Some c) 0 rest
            end
          else match dstyle_of c with
          | Some k =>
              if prefix (dtoken k) s
              then if at_rbrace (get (dwidth k) s)
                   then TDelim k true false true :: lex (Some c) (dwidth k) rest
                   else TDelim k false
                          (bare_opens k && nonspace_at (get (dwidth k) s))
                          (nonspace_at prev)
                        :: lex (Some c) (pred (dwidth k)) rest
              else TText c :: lex (Some c) 0 rest
          | None => TText c :: lex (Some c) 0 rest
          end
      end
  end.

Definition tokens (s : string) : list token := lex None 0 s.

(* A paragraph's lines, with a break between two of them.  Each line is
   lexed alone, so a token at a line's end has nothing after it and one
   at a line's start nothing before it; the last line is read without
   its trailing whitespace, as the paragraph's inlines are. *)
Fixpoint para_tokens (ls : list string) : list token :=
  match ls with
  | [] => []
  | [x] => tokens (strip_trailing_ws x)
  | x :: rest => (tokens x ++ TBreak :: para_tokens rest)%list
  end.

(*
Readings
========

A reading says which role each token takes: a list of pairs of token
positions, `(i, j)` pairing the opener at `i` with the closer at `j`,
and the list of the tokens that act as openers.  An opener and a closer
pair when they have the same key: a delimiter's style and marking
("explicitly marked closers can only match explicitly marked openers",
P4), or the bracket.

A `]` that pairs closes its bracket, and what follows is a region of
the link syntax: a destination runs to the `)` that balances its `(`,
and a reference label to the next `]`.  A region is source, so nothing
in it opens or closes, and so is a label that no `]` ends.  A
destination with no balancing `)` is not: the rest of the paragraph is
read as usual, except that a closer there may not reach an opener from
before the destination, and a closer that would reach one but for that
is text (djot.js, `inline.ts:150-158`). *)

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

Definition open_key (ts : list token) (i : nat) : option key :=
  match nth_error ts i with Some t => opens_as t | None => None end.

Definition close_key (ts : list token) (j : nat) : option key :=
  match nth_error ts j with Some t => closes_as t | None => None end.

(* The `)` that balances an open `(`, `i` being the position of the
   first of `ts`. *)
Fixpoint paren_close (depth i : nat) (ts : list token) : option nat :=
  match ts with
  | [] => None
  | TText c :: rest =>
      if Ascii.eqb c lparen then paren_close (S depth) (S i) rest
      else if Ascii.eqb c rparen
      then match depth with O => Some i | S d => paren_close d (S i) rest end
      else paren_close depth (S i) rest
  | _ :: rest => paren_close depth (S i) rest
  end.

Fixpoint rbrack_at (i : nat) (ts : list token) : option nat :=
  match ts with
  | [] => None
  | TText c :: rest => if Ascii.eqb c rbrack then Some i else rbrack_at (S i) rest
  | TClose _ :: _ => Some i
  | _ :: rest => rbrack_at (S i) rest
  end.

(* Where the region after a closing `]` at `d` ends.  The token after the
   `]` is the region's `(` or `[`, so the region's text begins two
   tokens on. *)
Definition region_end (ts : list token) (d : nat) (dest : bool) : option nat :=
  if dest then paren_close 0 (S (S d)) (skipn (S (S d)) ts)
  else rbrack_at (S (S d)) (skipn (S (S d)) ts).

Definition closes (m : matching) (j : nat) : Prop := exists i, In (i, j) m.

(* Gone by `j`: closed before it, or inside a pair closed before it.  The
   second is the reference's "any potential openers between the opener
   and the closer get marked as regular text"; reading the pairs in the
   order of their closers is "the first opener that gets closed takes
   precedence". *)
Definition dead (m : matching) (j p : nat) : Prop :=
  (exists j', j' < j /\ In (p, j') m)
  \/ (exists i' j', j' < j /\ In (i', j') m /\ i' < p < j').

(* Inside a region. *)
Definition inert (ts : list token) (m : matching) (t : nat) : Prop :=
  exists p d b, In (p, d) m /\ nth_error ts d = Some (TClose b) /\ d < t
    /\ match region_end ts d b with Some e => t <= e | None => b = false end.

(* Before a destination that does not close, seen from after it. *)
Definition behind (ts : list token) (m : matching) (j q : nat) : Prop :=
  exists p d, In (p, d) m /\ nth_error ts d = Some (TClose true)
    /\ region_end ts d true = None /\ q < d < j.

Definition reading : Type := (matching * list nat)%type.

(* An opener still open at `j`, the destinations aside. *)
Definition cand (ts : list token) (m : matching) (os : list nat)
  (j q : nat) (k : key) : Prop :=
  In q os /\ q < j /\ open_key ts q = Some k /\ ~ closes m q /\ ~ dead m j q.

Definition live (ts : list token) (m : matching) (os : list nat)
  (j q : nat) (k : key) : Prop :=
  cand ts m os j q k /\ ~ behind ts m j q.

(* "When there are multiple openers that might be matched with a given
   closer, the closest one is used." *)
Definition closest_live (ts : list token) (m : matching) (os : list nat)
  (j : nat) (k : key) (p : nat) : Prop :=
  live ts m os j p k /\ forall q, live ts m os j q k -> q <= p.

(* A closer that only a destination keeps from its opener. *)
Definition barred (ts : list token) (m : matching) (os : list nat)
  (j : nat) (k : key) : Prop :=
  (forall q, ~ live ts m os j q k) /\ exists q, cand ts m os j q k.

(* The readings the rules allow.  A pair is a closer and the closest live
   opener of its key, with something between them for a delimiter.  A
   closer left unmatched has no live opener of its key but a delimiter
   right before it, with nothing to enclose: `__a` pairs nothing, and the
   second `_` opens in its turn.  A token acts as an opener when it may
   open, is not in a region, does not close, and is not barred. *)
Definition valid (ts : list token) (r : reading) : Prop :=
  let '(m, os) := r in
  (forall i j, In (i, j) m ->
     exists k, close_key ts j = Some k /\ ~ inert ts m j
       /\ closest_live ts m os j k i /\ (needs_content k = true -> S i < j))
  /\ (forall j k, close_key ts j = Some k -> ~ inert ts m j -> ~ closes m j ->
        forall p, closest_live ts m os j k p -> needs_content k = true /\ S p = j)
  /\ (forall q, In q os <->
        (exists k, open_key ts q = Some k) /\ ~ inert ts m q /\ ~ closes m q
        /\ forall k, close_key ts q = Some k -> ~ barred ts m os q k).

(*
Uniqueness
----------

At most one reading is valid, so the rules determine it and `valid`, not
`ref_read` below, is the specification.  The roles are settled in the
order of the tokens: whether a token closes or opens reads only the
pairs that closed before it and the openers before it. *)

Lemma key_eq_iff : forall a b, key_eq a b = true <-> a = b.
Proof.
  intros [k m|] [k' m'|]; cbn; split; intros H; try discriminate; try reflexivity.
  - apply andb_true_iff in H as [H1 H2].
    destruct k, k'; try discriminate H1; apply Bool.eqb_prop in H2; subst; reflexivity.
  - injection H as -> ->. destruct k'; cbn; apply Bool.eqb_reflx.
Qed.

Lemma key_eq_refl : forall a, key_eq a a = true.
Proof. intros a. apply key_eq_iff. reflexivity. Qed.

Lemma close_key_fun : forall ts j k k',
  close_key ts j = Some k -> close_key ts j = Some k' -> k = k'.
Proof. intros ts j k k' H1 H2. rewrite H1 in H2. injection H2 as E. exact E. Qed.

Lemma closest_live_fun : forall ts m os j k p q,
  closest_live ts m os j k p -> closest_live ts m os j k q -> p = q.
Proof.
  intros ts m os j k p q [Hp Mp] [Hq Mq].
  specialize (Mp q Hq). specialize (Mq p Hp). lia.
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

Section Agree.
Variables (ts : list token) (m1 m2 : matching) (os1 os2 : list nat) (n : nat).
Hypothesis A : agree m1 os1 m2 os2 n.

Lemma dead_agree : forall j p, j <= n -> dead m1 j p -> dead m2 j p.
Proof.
  destruct A as [Hm _]. intros j p Hj [(j' & Hj' & H)|(i' & j' & Hj' & H & Hb)].
  - left. exists j'. split; [exact Hj'|]. apply Hm; [lia|exact H].
  - right. exists i', j'. split; [exact Hj'|]. split; [apply Hm; [lia|exact H]|exact Hb].
Qed.

Lemma inert_agree : forall t, t <= n -> inert ts m1 t -> inert ts m2 t.
Proof.
  destruct A as [Hm _]. intros t Ht (p & d & b & H & Hd & Hlt & He).
  exists p, d, b. split; [apply Hm; [lia|exact H]|]. split; [exact Hd|].
  split; [exact Hlt|exact He].
Qed.

Lemma behind_agree : forall j q, j <= n -> behind ts m1 j q -> behind ts m2 j q.
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

Lemma cand_agree : forall ts m1 os1 m2 os2 n j q k,
  agree m1 os1 m2 os2 n -> j <= n ->
  cand ts m1 os1 j q k -> cand ts m2 os2 j q k.
Proof.
  intros ts m1 os1 m2 os2 n j q k A Hj (Hin & Hq & Ho & Hc & Hd).
  pose proof (agree_sym _ _ _ _ _ A) as A'.
  split; [apply (proj2 A); [lia|exact Hin]|]. split; [exact Hq|].
  split; [exact Ho|]. split.
  - intros H. apply Hc. apply (closes_agree m2 m1 os2 os1 n A'); [lia|exact H].
  - intros H. apply Hd. apply (dead_agree m2 m1 os2 os1 n A' j q Hj H).
Qed.

Lemma live_agree : forall ts m1 os1 m2 os2 n j q k,
  agree m1 os1 m2 os2 n -> j <= n ->
  live ts m1 os1 j q k -> live ts m2 os2 j q k.
Proof.
  intros ts m1 os1 m2 os2 n j q k A Hj [Hc Hb].
  pose proof (agree_sym _ _ _ _ _ A) as A'.
  split; [exact (cand_agree ts m1 os1 m2 os2 n j q k A Hj Hc)|].
  intros H. apply Hb. exact (behind_agree ts m2 m1 os2 os1 n A' j q Hj H).
Qed.

Lemma closest_live_agree : forall ts m1 os1 m2 os2 n j k p,
  agree m1 os1 m2 os2 n -> j <= n ->
  closest_live ts m1 os1 j k p -> closest_live ts m2 os2 j k p.
Proof.
  intros ts m1 os1 m2 os2 n j k p A Hj [Hp Mp].
  pose proof (agree_sym _ _ _ _ _ A) as A'.
  split; [exact (live_agree ts m1 os1 m2 os2 n j p k A Hj Hp)|].
  intros q Hq. apply Mp. exact (live_agree ts m2 os2 m1 os1 n j q k A' Hj Hq).
Qed.

Lemma barred_agree : forall ts m1 os1 m2 os2 n j k,
  agree m1 os1 m2 os2 n -> j <= n ->
  barred ts m1 os1 j k -> barred ts m2 os2 j k.
Proof.
  intros ts m1 os1 m2 os2 n j k A Hj [Hn (q & Hq)].
  pose proof (agree_sym _ _ _ _ _ A) as A'.
  split.
  - intros q' Hq'. apply (Hn q'). exact (live_agree ts m2 os2 m1 os1 n j q' k A' Hj Hq').
  - exists q. exact (cand_agree ts m1 os1 m2 os2 n j q k A Hj Hq).
Qed.

Lemma closes_dec : forall m j, {closes m j} + {~ closes m j}.
Proof.
  intros m j.
  destruct (existsb (fun e => Nat.eqb (snd e) j) m) eqn:D.
  - left. apply existsb_exists in D as ([i j'] & Hin & Hj).
    apply Nat.eqb_eq in Hj. cbn in Hj. subst j'. exists i. exact Hin.
  - right. intros [i Hin].
    assert (existsb (fun e => Nat.eqb (snd e) j) m = true) as C.
    { apply existsb_exists. exists (i, j). split; [exact Hin|].
      apply Nat.eqb_refl. }
    rewrite D in C. discriminate.
Qed.

Local Lemma valid_pairs_at : forall ts m1 os1 m2 os2 n,
  valid ts (m1, os1) -> valid ts (m2, os2) -> agree m1 os1 m2 os2 n ->
  forall i, In (i, n) m1 -> In (i, n) m2.
Proof.
  intros ts m1 os1 m2 os2 n [P1 _] [P2 [U2 _]] A i H.
  destruct (P1 i n H) as (k & Hk & Hni & Hcl & Hne).
  apply (closest_live_agree ts m1 os1 m2 os2 n n k i A (le_n n)) in Hcl.
  assert (Hni2 : ~ inert ts m2 n).
  { intros Hi. apply Hni.
    exact (inert_agree ts m2 m1 os2 os1 n (agree_sym _ _ _ _ _ A) n (le_n n) Hi). }
  destruct (closes_dec m2 n) as [[i' Hi']|Hn].
  - destruct (P2 i' n Hi') as (k' & Hk' & _ & Hcl' & _).
    rewrite <- (close_key_fun ts n k k' Hk Hk') in Hcl'.
    rewrite (closest_live_fun ts m2 os2 n k i i' Hcl Hcl'). exact Hi'.
  - destruct (U2 n k Hk Hni2 Hn i Hcl) as [Hc E].
    specialize (Hne Hc). lia.
Qed.

Local Lemma valid_os_at : forall ts m1 os1 m2 os2 n,
  valid ts (m1, os1) -> valid ts (m2, os2) -> agree m1 os1 m2 os2 n ->
  (forall i, In (i, n) m1 <-> In (i, n) m2) ->
  In n os1 -> In n os2.
Proof.
  intros ts m1 os1 m2 os2 n [_ [_ O1]] [_ [_ O2]] A Hn H.
  pose proof (agree_sym _ _ _ _ _ A) as A'.
  apply O1 in H as (Ho & Hni & Hc & Hb). apply O2.
  split; [exact Ho|]. split; [|split].
  - intros Hi. apply Hni. exact (inert_agree ts m2 m1 os2 os1 n A' n (le_n n) Hi).
  - intros [i Hi]. apply Hc. exists i. apply Hn, Hi.
  - intros k Hk Hbar. apply (Hb k Hk).
    exact (barred_agree ts m2 os2 m1 os1 n n k A' (le_n n) Hbar).
Qed.

Theorem valid_unique : forall ts m1 os1 m2 os2,
  valid ts (m1, os1) -> valid ts (m2, os2) ->
  (forall i j, In (i, j) m1 <-> In (i, j) m2) /\ (forall q, In q os1 <-> In q os2).
Proof.
  intros ts m1 os1 m2 os2 V1 V2.
  assert (Step : forall n, agree m1 os1 m2 os2 n ->
            (forall i, In (i, n) m1 <-> In (i, n) m2) /\ (In n os1 <-> In n os2)).
  { intros n A.
    assert (Hp : forall i, In (i, n) m1 <-> In (i, n) m2).
    { intros i. split.
      - apply (valid_pairs_at ts m1 os1 m2 os2 n V1 V2 A).
      - apply (valid_pairs_at ts m2 os2 m1 os1 n V2 V1 (agree_sym _ _ _ _ _ A)). }
    split; [exact Hp|]. split.
    - apply (valid_os_at ts m1 os1 m2 os2 n V1 V2 A Hp).
    - apply (valid_os_at ts m2 os2 m1 os1 n V2 V1 (agree_sym _ _ _ _ _ A)).
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
Theorem valid_nested : forall ts m os i j i' j',
  valid ts (m, os) -> In (i, j) m -> In (i', j') m -> i < i' < j -> j' < j.
Proof.
  intros ts m os i j i' j' [P _] H H' Hb.
  destruct (P i j H) as (k & Hk & _ & Hcl & _).
  destruct (P i' j' H') as (k' & Hk' & _ & Hcl' & _).
  destruct (lt_eq_lt_dec j' j) as [[Hlt|Heq]|Hgt]; [exact Hlt| |].
  - subst j'. pose proof (close_key_fun ts j k k' Hk Hk') as <-.
    pose proof (closest_live_fun ts m os j k i i' Hcl Hcl'). lia.
  - exfalso. destruct Hcl' as [((_ & _ & _ & _ & Hd) & _) _].
    apply Hd. right. exists i, j. split; [exact Hgt|]. split; [exact H|exact Hb].
Qed.

(*
The reading, computed
---------------------

Left to right, with the openers still open innermost first and a marker
for each destination that does not close.  A closer takes the closest
open opener of its key above every marker; with none there and one
below a marker it is barred.  After a bracket's closer the region's end
is known from the tokens, and the tokens up to it are skipped. *)

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

(* Whether the tokens from here on are in a region: no, up to and
   including `e`, or to the end. *)
Inductive rmode : Type := RNormal | RInert (e : option nat).

Record rstate : Type := RState {
  rs_live : list litem;
  rs_pairs : matching;
  rs_os : list nat;
  rs_mode : rmode
}.

Definition ropen (i : nat) (k : key) (op : bool) (s : rstate) : rstate :=
  if op then RState (LOpen i k :: rs_live s) (rs_pairs s) (i :: rs_os s) (rs_mode s)
  else s.

Definition rstep (ts : list token) (i : nat) (t : token) (s : rstate) : rstate :=
  match rs_mode s with
  | RInert (Some e) =>
      if Nat.eqb i e then RState (rs_live s) (rs_pairs s) (rs_os s) RNormal else s
  | RInert None => s
  | RNormal =>
      match t with
      | TText _ | TBreak | TEsc _ | TEscWs _ | THard _ => s
      | TOpen => ropen i KBracket true s
      | TDelim k mr op cl =>
          match (if cl then pick (KDelim k mr) (rs_live s) else PNone) with
          | PFound p below =>
              if Nat.ltb (S p) i
              then RState below ((p, i) :: rs_pairs s) (rs_os s) RNormal
              else ropen i (KDelim k mr) op s
          | PBarred => s
          | PNone => ropen i (KDelim k mr) op s
          end
      | TClose b =>
          match pick KBracket (rs_live s) with
          | PFound p below =>
              let pairs := (p, i) :: rs_pairs s in
              match region_end ts i b with
              | Some e => RState below pairs (rs_os s) (RInert (Some e))
              | None =>
                  if b then RState (LBar i :: below) pairs (rs_os s) RNormal
                  else RState below pairs (rs_os s) (RInert None)
              end
          | _ => s
          end
      end
  end.

Fixpoint rrun (ts : list token) (i : nat) (rest : list token) (s : rstate) : rstate :=
  match rest with
  | [] => s
  | t :: more => rrun ts (S i) more (rstep ts i t s)
  end.

Definition rstart : rstate := RState [] [] [] RNormal.

Definition ref_read (ts : list token) : reading :=
  let s := rrun ts 0 ts rstart in (rs_pairs s, rs_os s).

(*
The computed reading is valid
-----------------------------

After the first `n` tokens the stack holds exactly the openers still
open at `n` and a marker for each destination that does not close,
innermost first; the mode says which tokens from `n` on are in a
region; and every role so far obeys the rules.  A token's role reads
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

Definition bar (ts : list token) (m : matching) (d : nat) : Prop :=
  exists p, In (p, d) m /\ nth_error ts d = Some (TClose true)
    /\ region_end ts d true = None.

Definition covers (md : rmode) (t : nat) : Prop :=
  match md with
  | RNormal => False
  | RInert (Some e) => t <= e
  | RInert None => True
  end.

(* The three rules of `valid`, one token at a time. *)
Definition pair_ok (ts : list token) (m : matching) (os : list nat) (i j : nat)
  : Prop :=
  exists k, close_key ts j = Some k /\ ~ inert ts m j
    /\ closest_live ts m os j k i /\ (needs_content k = true -> S i < j).

Definition unmatched_ok (ts : list token) (m : matching) (os : list nat) (j : nat)
  : Prop :=
  forall k, close_key ts j = Some k -> ~ inert ts m j -> ~ closes m j ->
    forall p, closest_live ts m os j k p -> needs_content k = true /\ S p = j.

Definition opener_ok (ts : list token) (m : matching) (os : list nat) (q : nat)
  : Prop :=
  In q os <->
    (exists k, open_key ts q = Some k) /\ ~ inert ts m q /\ ~ closes m q
    /\ forall k, close_key ts q = Some k -> ~ barred ts m os q k.

Record rinv (ts : list token) (n : nat) (s : rstate) : Prop := RInv {
  ri_bound_pairs : forall i j, In (i, j) (rs_pairs s) -> j < n;
  ri_bound_os : forall q, In q (rs_os s) -> q < n;
  ri_cand : forall q k,
    In (LOpen q k) (rs_live s) <-> cand ts (rs_pairs s) (rs_os s) n q k;
  ri_bar : forall d, In (LBar d) (rs_live s) <-> bar ts (rs_pairs s) d;
  ri_desc : ldesc (rs_live s);
  ri_mode : forall t, n <= t -> (inert ts (rs_pairs s) t <-> covers (rs_mode s) t);
  ri_mode_le : forall e, rs_mode s = RInert (Some e) -> n <= e;
  ri_pairs : forall i j, In (i, j) (rs_pairs s) -> pair_ok ts (rs_pairs s) (rs_os s) i j;
  ri_unmatched : forall j, j < n -> unmatched_ok ts (rs_pairs s) (rs_os s) j;
  ri_os : forall q, q < n -> opener_ok ts (rs_pairs s) (rs_os s) q
}.

(* What a token's rules read is settled before it. *)
Lemma pair_ok_agree : forall ts m os m' os' n i j,
  agree m os m' os' n -> j <= n -> pair_ok ts m os i j -> pair_ok ts m' os' i j.
Proof.
  intros ts m os m' os' n i j A Hj (k & Hk & Hi & Hc & Hn).
  exists k. split; [exact Hk|]. split; [|split; [|exact Hn]].
  - intros H. apply Hi.
    exact (inert_agree ts m' m os' os n (agree_sym _ _ _ _ _ A) j Hj H).
  - exact (closest_live_agree ts m os m' os' n j k i A Hj Hc).
Qed.

Lemma unmatched_ok_agree : forall ts m os m' os' n j,
  agree m os m' os' n -> j < n -> unmatched_ok ts m os j -> unmatched_ok ts m' os' j.
Proof.
  intros ts m os m' os' n j A Hj U k Hk Hi Hc p Hp.
  pose proof (agree_sym _ _ _ _ _ A) as A'.
  apply (U k Hk).
  - intros H. apply Hi. exact (inert_agree ts m m' os os' n A j ltac:(lia) H).
  - intros H. apply Hc. exact (closes_agree m m' os os' n A j Hj H).
  - exact (closest_live_agree ts m' os' m os n j k p A' ltac:(lia) Hp).
Qed.

Lemma opener_ok_agree : forall ts m os m' os' n q,
  agree m os m' os' n -> q < n -> opener_ok ts m os q -> opener_ok ts m' os' q.
Proof.
  intros ts m os m' os' n q A Hq O.
  pose proof (agree_sym _ _ _ _ _ A) as A'.
  unfold opener_ok in *. split.
  - intros H. apply (proj2 A q Hq) in H. apply O in H as (Ho & Hi & Hc & Hb).
    split; [exact Ho|]. split; [|split].
    + intros H. apply Hi. exact (inert_agree ts m' m os' os n A' q ltac:(lia) H).
    + intros H. apply Hc. exact (closes_agree m' m os' os n A' q Hq H).
    + intros k Hk H. apply (Hb k Hk).
      exact (barred_agree ts m' os' m os n q k A' ltac:(lia) H).
  - intros (Ho & Hi & Hc & Hb). apply (proj2 A q Hq). apply O.
    split; [exact Ho|]. split; [|split].
    + intros H. apply Hi. exact (inert_agree ts m m' os os' n A q ltac:(lia) H).
    + intros H. apply Hc. exact (closes_agree m m' os os' n A q Hq H).
    + intros k Hk H. apply (Hb k Hk).
      exact (barred_agree ts m os m' os' n q k A ltac:(lia) H).
Qed.

(* Under the invariant, liveness is read off the stack. *)
Lemma live_stack : forall ts n s q k,
  rinv ts n s ->
  live ts (rs_pairs s) (rs_os s) n q k <-> In (LOpen q k) (rs_live s) /\ clear (rs_live s) q.
Proof.
  intros ts n s q k I. unfold live. rewrite (ri_cand ts n s I). split.
  - intros [Hc Hb]. split; [exact Hc|]. intros d Hd.
    destruct (le_lt_dec d q) as [Hle|Hlt]; [exact Hle|]. exfalso. apply Hb.
    apply (ri_bar ts n s I) in Hd as (p & Hp & Ht & He).
    exists p, d. split; [exact Hp|]. split; [exact Ht|]. split; [exact He|].
    split; [exact Hlt|exact (ri_bound_pairs ts n s I p d Hp)].
  - intros [Hc Hcl]. split; [exact Hc|]. intros (p & d & Hp & Ht & He & Hq & _).
    assert (In (LBar d) (rs_live s)) as Hd
      by (apply (ri_bar ts n s I); exists p; auto).
    specialize (Hcl d Hd). lia.
Qed.


Local Lemma pairs_lt : forall ts n s i j,
  rinv ts n s -> In (i, j) (rs_pairs s) -> i < j.
Proof.
  intros ts n s i j I H. destruct (ri_pairs ts n s I i j H) as (_ & _ & _ & [[(_ & Hq & _) _] _] & _).
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
Local Lemma cand_succ : forall ts n s os' q k,
  rinv ts n s -> (forall q', q' < n -> In q' os' <-> In q' (rs_os s)) ->
  cand ts (rs_pairs s) os' (S n) q k
  <-> cand ts (rs_pairs s) (rs_os s) n q k
      \/ (q = n /\ In n os' /\ open_key ts n = Some k).
Proof.
  intros ts n s os' q k I Hos.
  pose proof (ri_bound_pairs ts n s I) as B. pose proof (ri_bound_os ts n s I) as Bo. split.
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
        -- specialize (B _ _ H). pose proof (pairs_lt ts n s _ _ I H). lia.
        -- specialize (B _ _ H). lia.
Qed.

(* A pair closes at `n` with its opener `p` live. *)
Local Lemma cand_pair : forall ts n s p q k,
  rinv ts n s -> p < n ->
  cand ts ((p, n) :: rs_pairs s) (rs_os s) (S n) q k
  <-> cand ts (rs_pairs s) (rs_os s) n q k /\ q < p.
Proof.
  intros ts n s p q k I Hpn.
  pose proof (ri_bound_pairs ts n s I) as B. pose proof (ri_bound_os ts n s I) as Bo.
  assert (Dead : dead ((p, n) :: rs_pairs s) (S n) q
                 <-> dead (rs_pairs s) n q \/ q = p \/ p < q < n).
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

Local Lemma inert_pair : forall ts m p n t,
  (forall i j, In (i, j) m -> j < n) -> n < t ->
  inert ts ((p, n) :: m) t
  <-> inert ts m t
      \/ (exists b, nth_error ts n = Some (TClose b)
           /\ match region_end ts n b with Some e => t <= e | None => b = false end).
Proof.
  intros ts m p n t B Ht. split.
  - intros (p' & d & b & [E|H] & Hd & Hlt & He).
    + injection E as -> ->. right. exists b. split; assumption.
    + left. exists p', d, b. auto.
  - intros [(p' & d & b & H & Hd & Hlt & He)|(b & Hd & He)].
    + exists p', d, b. split; [right; exact H|]. auto.
    + exists p, n, b. split; [left; reflexivity|]. auto.
Qed.

Local Lemma inert_pair_at : forall ts m p n,
  inert ts ((p, n) :: m) n <-> inert ts m n.
Proof.
  intros ts m p n. split.
  - intros (p' & d & b & [E|H] & Hd & Hlt & He); [injection E as _ ->; lia|].
    exists p', d, b. auto.
  - intros (p' & d & b & H & Hd & Hlt & He). exists p', d, b.
    split; [right; exact H|]. auto.
Qed.

(* A token in a region: nothing changes but the mode. *)
Local Lemma rinv_skip : forall ts n s md',
  rinv ts n s -> covers (rs_mode s) n ->
  (forall t, S n <= t -> (covers (rs_mode s) t <-> covers md' t)) ->
  (forall e, md' = RInert (Some e) -> S n <= e) ->
  rinv ts (S n) (RState (rs_live s) (rs_pairs s) (rs_os s) md').
Proof.
  intros ts n s md' I Hc Hmd Hle.
  assert (Hin : inert ts (rs_pairs s) n) by (apply (ri_mode ts n s I n (le_n n)), Hc).
  assert (Hno : ~ In n (rs_os s)) by (intros H; specialize (ri_bound_os ts n s I n H); lia).
  constructor; cbn [rs_live rs_pairs rs_os rs_mode].
  - intros i j H. specialize (ri_bound_pairs ts n s I i j H). lia.
  - intros q H. specialize (ri_bound_os ts n s I q H). lia.
  - intros q k. rewrite (ri_cand ts n s I), (cand_succ ts n s (rs_os s) q k I (fun _ _ => iff_refl _)).
    split; [intros H; left; exact H|intros [H|(_ & H & _)]; [exact H|contradiction]].
  - exact (ri_bar ts n s I).
  - exact (ri_desc ts n s I).
  - intros t Ht. rewrite (ri_mode ts n s I t ltac:(lia)). apply Hmd, Ht.
  - exact Hle.
  - exact (ri_pairs ts n s I).
  - intros j Hj. destruct (Nat.eq_dec j n) as [->|Hne];
      [|apply (ri_unmatched ts n s I); lia].
    intros k _ Hni. contradiction.
  - intros q Hq. destruct (Nat.eq_dec q n) as [->|Hne];
      [|apply (ri_os ts n s I); lia].
    split; [contradiction|intros (_ & Hni & _); contradiction].
Qed.

(* A token that closes nothing: it opens or it is text. *)
Local Lemma rinv_noclose : forall ts n s op K,
  rinv ts n s -> rs_mode s = RNormal ->
  (op = true -> open_key ts n = Some K) ->
  opener_ok ts (rs_pairs s) (if op then n :: rs_os s else rs_os s) n ->
  unmatched_ok ts (rs_pairs s) (if op then n :: rs_os s else rs_os s) n ->
  rinv ts (S n)
    (RState (if op then LOpen n K :: rs_live s else rs_live s) (rs_pairs s)
       (if op then n :: rs_os s else rs_os s) RNormal).
Proof.
  intros ts n s op K I Hmd HK Ho Hu.
  set (os' := if op then n :: rs_os s else rs_os s).
  assert (Hos : forall q, q < n -> In q os' <-> In q (rs_os s)).
  { intros q Hq. unfold os'. destruct op; [|reflexivity]. cbn.
    split; [intros [E|H]; [lia|exact H]|intros H; right; exact H]. }
  assert (A : agree (rs_pairs s) (rs_os s) (rs_pairs s) os' n).
  { split; [intros; reflexivity|]. intros q Hq. symmetry. apply Hos, Hq. }
  assert (Hni : ~ inert ts (rs_pairs s) n).
  { intros H. apply (ri_mode ts n s I n (le_n n)) in H. rewrite Hmd in H. exact H. }
  constructor; cbn [rs_live rs_pairs rs_os rs_mode]; fold os'.
  - intros i j H. specialize (ri_bound_pairs ts n s I i j H). lia.
  - intros q H. unfold os' in H. destruct op; [destruct H as [<-|H]; [lia|]|];
      specialize (ri_bound_os ts n s I q H); lia.
  - intros q k. rewrite (cand_succ ts n s os' q k I Hos), <- (ri_cand ts n s I).
    unfold os'. destruct op.
    + specialize (HK eq_refl). cbn. split.
      * intros [E|H]; [injection E as <- <-; right; auto|left; exact H].
      * intros [H|(-> & _ & Ho')]; [right; exact H|].
        rewrite HK in Ho'. injection Ho' as <-. left. reflexivity.
    + split; [intros H; left; exact H|].
      intros [H|(-> & Hin & _)]; [exact H|].
      exfalso. specialize (ri_bound_os ts n s I n Hin). lia.
  - intros d. destruct op; cbn; [|exact (ri_bar ts n s I d)].
    rewrite <- (ri_bar ts n s I d). split; [intros [E|H]; [discriminate|exact H]|].
    intros H; right; exact H.
  - destruct op; [|exact (ri_desc ts n s I)]. constructor; [exact (ri_desc ts n s I)|].
    apply Forall_forall. intros [q k|d] Hx; cbn.
    + apply (ri_cand ts n s I) in Hx as (_ & Hq & _). exact Hq.
    + apply (ri_bar ts n s I) in Hx as (p & H & _). exact (ri_bound_pairs ts n s I p d H).
  - intros t Ht. rewrite (ri_mode ts n s I t ltac:(lia)), Hmd. reflexivity.
  - intros e E. discriminate E.
  - intros i j H. apply (pair_ok_agree ts (rs_pairs s) (rs_os s) _ os' n i j A).
    + exact (Nat.lt_le_incl _ _ (ri_bound_pairs ts n s I i j H)).
    + exact (ri_pairs ts n s I i j H).
  - intros j Hj. destruct (Nat.eq_dec j n) as [->|Hne]; [exact Hu|].
    apply (unmatched_ok_agree ts (rs_pairs s) (rs_os s) _ os' n j A); [lia|].
    apply (ri_unmatched ts n s I). lia.
  - intros q Hq. destruct (Nat.eq_dec q n) as [->|Hne]; [exact Ho|].
    apply (opener_ok_agree ts (rs_pairs s) (rs_os s) _ os' n q A); [lia|].
    apply (ri_os ts n s I). lia.
Qed.

(* A token that closes a pair with `p`. *)
Local Lemma rinv_pair : forall ts n s p K lv' md',
  rinv ts n s -> rs_mode s = RNormal ->
  close_key ts n = Some K ->
  closest_live ts (rs_pairs s) (rs_os s) n K p ->
  (needs_content K = true -> S p < n) ->
  (forall q k, In (LOpen q k) lv' <-> In (LOpen q k) (rs_live s) /\ q < p) ->
  (forall d, In (LBar d) lv' <->
     In (LBar d) (rs_live s)
     \/ (d = n /\ nth_error ts n = Some (TClose true) /\ region_end ts n true = None)) ->
  ldesc lv' ->
  (forall t, S n <= t ->
     (covers md' t <->
      exists b, nth_error ts n = Some (TClose b)
        /\ match region_end ts n b with Some e => t <= e | None => b = false end)) ->
  (forall e, md' = RInert (Some e) -> S n <= e) ->
  rinv ts (S n) (RState lv' ((p, n) :: rs_pairs s) (rs_os s) md').
Proof.
  intros ts n s p K lv' md' I Hmd HK Hcl Hne Hlv Hbar Hdesc Hmode Hle.
  set (m' := (p, n) :: rs_pairs s).
  pose proof (ri_bound_pairs ts n s I) as B.
  assert (Hpn : p < n) by (destruct Hcl as [((_ & Hp & _) & _) _]; exact Hp).
  assert (A : agree (rs_pairs s) (rs_os s) m' (rs_os s) n).
  { split; [|intros; reflexivity]. intros i j Hj. unfold m'. cbn. split.
    - intros H. right. exact H.
    - intros [E|H]; [injection E as _ ->; lia|exact H]. }
  assert (Hni : ~ inert ts (rs_pairs s) n).
  { intros H. apply (ri_mode ts n s I n (le_n n)) in H. rewrite Hmd in H. exact H. }
  assert (Hcn : closes m' n) by (exists p; left; reflexivity).
  assert (Hnos : ~ In n (rs_os s)) by (intros H; specialize (ri_bound_os ts n s I n H); lia).
  constructor; cbn [rs_live rs_pairs rs_os rs_mode]; fold m'.
  - intros i j [E|H]; [injection E as _ <-; lia|specialize (B i j H); lia].
  - intros q H. specialize (ri_bound_os ts n s I q H). lia.
  - intros q k. unfold m'. rewrite Hlv, (cand_pair ts n s p q k I Hpn), (ri_cand ts n s I).
    reflexivity.
  - intros d. rewrite Hbar, (ri_bar ts n s I d). unfold bar. split.
    + intros [(p' & H & Hd & He)|(-> & Hd & He)].
      * exists p'. split; [right; exact H|]. split; assumption.
      * exists p. split; [left; reflexivity|]. split; assumption.
    + intros (p' & [E|H] & Hd & He).
      * injection E as -> ->. right. auto.
      * left. exists p'. auto.
  - exact Hdesc.
  - intros t Ht. unfold m'.
    rewrite (inert_pair ts (rs_pairs s) p n t B ltac:(lia)), (Hmode t Ht).
    rewrite (ri_mode ts n s I t ltac:(lia)), Hmd. cbn. tauto.
  - exact Hle.
  - intros i j [E|H].
    + injection E as <- <-. exists K. split; [exact HK|]. split.
      * unfold m'. rewrite inert_pair_at. exact Hni.
      * split; [|exact Hne].
        exact (closest_live_agree ts (rs_pairs s) (rs_os s) m' (rs_os s) n n K p A (le_n n) Hcl).
    + apply (pair_ok_agree ts (rs_pairs s) (rs_os s) m' (rs_os s) n i j A).
      * exact (Nat.lt_le_incl _ _ (B i j H)).
      * exact (ri_pairs ts n s I i j H).
  - intros j Hj. destruct (Nat.eq_dec j n) as [->|Hne'].
    + intros k _ _ Hc. contradiction.
    + apply (unmatched_ok_agree ts (rs_pairs s) (rs_os s) m' (rs_os s) n j A); [lia|].
      apply (ri_unmatched ts n s I). lia.
  - intros q Hq. destruct (Nat.eq_dec q n) as [->|Hne'].
    + split; [contradiction|intros (_ & _ & Hc & _); contradiction].
    + apply (opener_ok_agree ts (rs_pairs s) (rs_os s) m' (rs_os s) n q A); [lia|].
      apply (ri_os ts n s I). lia.
Qed.

Local Lemma paren_close_ge : forall ts depth i e, paren_close depth i ts = Some e -> i <= e.
Proof.
  induction ts as [|t ts IH]; intros depth i e H; [discriminate|].
  cbn [paren_close] in H.
  destruct t; try (apply IH in H; lia).
  destruct (Ascii.eqb c lparen); [apply IH in H; lia|].
  destruct (Ascii.eqb c rparen); [|apply IH in H; lia].
  destruct depth; [injection H as <-; lia|apply IH in H; lia].
Qed.

Local Lemma rbrack_at_ge : forall ts i e, rbrack_at i ts = Some e -> i <= e.
Proof.
  induction ts as [|t ts IH]; intros i e H; [discriminate|].
  cbn [rbrack_at] in H.
  destruct t; try (apply IH in H; lia); [|injection H as <-; lia].
  destruct (Ascii.eqb c rbrack); [injection H as <-; lia|apply IH in H; lia].
Qed.

Local Lemma region_end_ge : forall ts d b e, region_end ts d b = Some e -> S (S d) <= e.
Proof.
  intros ts d [|] e H; unfold region_end in H;
    [exact (paren_close_ge _ _ _ _ H)|exact (rbrack_at_ge _ _ _ H)].
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
Local Lemma pick_below : forall ts n s K p below,
  rinv ts n s -> pick K (rs_live s) = PFound p below ->
  closest_live ts (rs_pairs s) (rs_os s) n K p
  /\ (forall q k, In (LOpen q k) below <-> In (LOpen q k) (rs_live s) /\ q < p)
  /\ (forall d, In (LBar d) below <-> In (LBar d) (rs_live s))
  /\ ldesc below
  /\ (forall x, In x below -> lpos x < p).
Proof.
  intros ts n s K p below I P.
  pose proof (ri_desc ts n s I) as D.
  destruct (pick_found K _ p below D P) as (Hin & Hcl & Hmax & Hb & Db & Ha).
  split; [|split; [|split; [|split]]].
  - split; [apply (live_stack ts n s p K I); split; assumption|].
    intros q Hq. apply (live_stack ts n s q K I) in Hq as [Hq Hc]. exact (Hmax q Hq Hc).
  - intros q k. rewrite Hb. reflexivity.
  - intros d. rewrite Hb. split; [intros [H _]; exact H|]. intros H. split; [exact H|].
    cbn. specialize (Hcl d H).
    destruct (Nat.eq_dec d p) as [->|Hne]; [|lia].
    pose proof (ldesc_pos_inj _ _ _ D H Hin eq_refl). discriminate.
  - exact Db.
  - intros x Hx. apply Hb in Hx as [_ Hx]. exact Hx.
Qed.

Local Lemma pick_not_live : forall ts n s K p,
  rinv ts n s -> pick K (rs_live s) = PBarred \/ pick K (rs_live s) = PNone ->
  ~ closest_live ts (rs_pairs s) (rs_os s) n K p.
Proof.
  intros ts n s K p I P [Hp _]. apply (live_stack ts n s p K I) in Hp as [Hin Hc].
  destruct P as [P|P].
  - destruct (pick_barred K _ (ri_desc ts n s I) P) as [Hn _]. exact (Hn p Hin Hc).
  - exact (pick_none K _ P p Hin).
Qed.

Lemma rinv_step : forall ts n s t,
  nth_error ts n = Some t -> rinv ts n s -> rinv ts (S n) (rstep ts n t s).
Proof.
  intros ts n [lv m os md] t Hn I.
  assert (Hok : open_key ts n = opens_as t) by (unfold open_key; rewrite Hn; reflexivity).
  assert (Hck : close_key ts n = closes_as t) by (unfold close_key; rewrite Hn; reflexivity).
  assert (Hnc : ~ closes m n)
    by (intros [i Hi]; specialize (ri_bound_pairs ts n _ I i n Hi); cbn in *; lia).
  assert (Hnos : ~ In n os) by (intros H; specialize (ri_bound_os ts n _ I n H); cbn in *; lia).
  unfold rstep; cbn [rs_mode rs_live rs_pairs rs_os].
  destruct md as [|[e|]].
  2: { pose proof (ri_mode_le ts n _ I e eq_refl) as Hle. cbn in Hle.
       destruct (Nat.eqb n e) eqn:E.
       - apply Nat.eqb_eq in E. subst e.
         apply (rinv_skip ts n (RState lv m os (RInert (Some n))) RNormal I);
           cbn; [lia| |intros e' E'; discriminate].
         intros t' Ht'. split; [lia|intros []].
       - apply Nat.eqb_neq in E.
         apply (rinv_skip ts n (RState lv m os (RInert (Some e))) (RInert (Some e)) I);
           cbn; [lia|tauto|intros e' E'; injection E' as <-; lia]. }
  2: { apply (rinv_skip ts n (RState lv m os (RInert None)) (RInert None) I);
         cbn; [exact Logic.I|tauto|intros e' E'; discriminate]. }
  assert (Hni : ~ inert ts m n).
  { intros H. apply (ri_mode ts n _ I n (le_n n)) in H. exact H. }
  pose (s := RState lv m os RNormal).
  assert (NC : forall op K,
            (op = true -> open_key ts n = Some K) ->
            opener_ok ts m (if op then n :: os else os) n ->
            unmatched_ok ts m (if op then n :: os else os) n ->
            rinv ts (S n) (RState (if op then LOpen n K :: lv else lv) m
                             (if op then n :: os else os) RNormal))
    by (intros op K; exact (rinv_noclose ts n s op K I eq_refl)).
  assert (Aos : forall op : bool, agree m os m (if op then n :: os else os) n).
  { intros op. split; [intros; reflexivity|]. intros q Hq. destruct op; [|reflexivity]. cbn.
    split; [intros H; right; exact H|intros [E|H]; [lia|exact H]]. }
  assert (OO : forall (op : bool) (K : key), open_key ts n = (if op then Some K else None) ->
            (forall k, close_key ts n = Some k -> op = true -> ~ barred ts m os n k) ->
            opener_ok ts m (if op then n :: os else os) n).
  { intros [|] K Ho Hb.
    - split; [intros _|intros _; left; reflexivity].
      split; [exists K; exact Ho|]. split; [exact Hni|]. split; [exact Hnc|].
      intros k Hk Hbar. apply (Hb k Hk eq_refl).
      exact (barred_agree ts m (n :: os) m os n n k (agree_sym _ _ _ _ _ (Aos true))
               (le_n n) Hbar).
    - split; [intros H; contradiction|intros [[k Hk] _]; congruence]. }
  assert (UN : forall (op : bool) K,
            (forall p, ~ closest_live ts m os n K p) -> close_key ts n = Some K ->
            unmatched_ok ts m (if op then n :: os else os) n).
  { intros op K Hn' HK k Hk _ _ p Hp. rewrite HK in Hk. injection Hk as <-.
    exfalso. apply (Hn' p).
    exact (closest_live_agree ts m _ m os n n K p (agree_sym _ _ _ _ _ (Aos op)) (le_n n) Hp). }
  assert (Nolive : forall K, pick K lv = PBarred \/ pick K lv = PNone ->
            forall p, ~ closest_live ts m os n K p)
    by (intros K P p; exact (pick_not_live ts n s K p I P)).
  assert (Text : opens_as t = None -> closes_as t = None -> rinv ts (S n) s).
  { intros Ho Hc. apply (NC false KBracket); [discriminate| |].
    - apply (OO false KBracket); [rewrite Hok; exact Ho|intros k Hk; congruence].
    - intros k Hk. congruence. }
  (* text, a break and the escapes neither open nor close *)
  destruct t as [c| |k mr op cl| |b|c|ws|ws]; try (apply Text; reflexivity).
  - (* a delimiter *)
    set (K := KDelim k mr).
    assert (Hop : open_key ts n = if op then Some K else None)
      by (rewrite Hok; destruct op; reflexivity).
    assert (Ropen : (forall k', close_key ts n = Some k' -> ~ barred ts m os n k') ->
              (forall op' : bool, unmatched_ok ts m (if op' then n :: os else os) n) ->
              rinv ts (S n) (ropen n K op s)).
    { intros Hnb Hu. unfold ropen. destruct op; cbn [rs_live rs_pairs rs_os rs_mode].
      - apply (NC true K); [intros _; exact Hop|apply (OO true K Hop)|apply (Hu true)].
        intros k' Hk' _. exact (Hnb k' Hk').
      - apply (NC false K); [discriminate|apply (OO false K Hop)|apply (Hu false)].
        intros k' _ E. discriminate E. }
    destruct cl.
    2: { cbn. apply Ropen.
         - intros k' Hk'. rewrite Hck in Hk'. discriminate.
         - intros op' k' Hk'. rewrite Hck in Hk'. discriminate. }
    assert (HK : close_key ts n = Some K) by (rewrite Hck; reflexivity).
    destruct (pick K lv) as [p below| |] eqn:P.
    + destruct (pick_below ts n s K p below I P) as (Hcl & Hlv & Hbar & Db & Hlt).
      unfold s in Hcl, Hlv, Hbar; cbn [rs_live rs_pairs rs_os] in Hcl, Hlv, Hbar.
      assert (Hpn : p < n) by (destruct Hcl as [((_ & Hp & _) & _) _]; exact Hp).
      destruct (Nat.ltb (S p) n) eqn:L.
      * apply Nat.ltb_lt in L.
        apply (rinv_pair ts n s p K below RNormal I eq_refl HK Hcl (fun _ => L) Hlv).
        -- intros d. rewrite Hbar. split; [intros H; left; exact H|].
           intros [H|(_ & E & _)]; [exact H|congruence].
        -- exact Db.
        -- intros t Ht. split; [intros []|intros (b & E & _); congruence].
        -- intros e E. discriminate E.
      * apply Nat.ltb_ge in L. apply Ropen.
        -- intros k' Hk' [Hn' _]. rewrite HK in Hk'. injection Hk' as <-.
           exact (Hn' p (proj1 Hcl)).
        -- intros op' k' Hk' _ _ p' Hp'. rewrite HK in Hk'. injection Hk' as <-.
           pose proof (closest_live_agree ts m _ m os n n K p'
                         (agree_sym _ _ _ _ _ (Aos op')) (le_n n) Hp') as Hp''.
           rewrite <- (closest_live_fun ts m os n K p p' Hcl Hp'').
           split; [reflexivity|lia].
    + (* barred: text *)
      destruct (pick_barred K lv (ri_desc ts n s I) P) as [Hnl [q Hq]].
      apply (NC false K); [discriminate| |apply (UN false K (Nolive K (or_introl P)) HK)].
      split; [intros H; contradiction|]. intros ([k' Hk'] & _ & _ & Hb).
      exfalso. apply (Hb K HK). split.
      * intros q' Hq'. apply (live_stack ts n s q' K I) in Hq' as [Hin Hc].
        exact (Hnl q' Hin Hc).
      * exists q. apply (ri_cand ts n s I). exact Hq.
    + apply Ropen.
      * intros k' Hk' [_ (q & Hq)]. rewrite HK in Hk'. injection Hk' as <-.
        apply (ri_cand ts n s I) in Hq. exact (pick_none K lv P q Hq).
      * intros op'. apply (UN op' K (Nolive K (or_intror P)) HK).
  - (* a `[` *)
    apply (NC true KBracket); [intros _; rewrite Hok; reflexivity|apply (OO true KBracket)|].
    + rewrite Hok. reflexivity.
    + intros k Hk. rewrite Hck in Hk. discriminate.
    + intros k Hk. rewrite Hck in Hk. discriminate.
  - (* a `]` that may close *)
    assert (HK : close_key ts n = Some KBracket) by (rewrite Hck; reflexivity).
    destruct (pick KBracket lv) as [p below| |] eqn:P.
    2,3: apply (NC false KBracket); [discriminate| |];
         [ split; [intros H; contradiction|intros ([k' Hk'] & _); rewrite Hok in Hk'; discriminate]
         | apply (UN false KBracket (Nolive KBracket ltac:(auto)) HK) ].
    destruct (pick_below ts n s KBracket p below I P) as (Hcl & Hlv & Hbar & Db & Hlt).
    unfold s in Hcl, Hlv, Hbar; cbn [rs_live rs_pairs rs_os] in Hcl, Hlv, Hbar.
    assert (Hpn : p < n) by (destruct Hcl as [((_ & Hp & _) & _) _]; exact Hp).
    destruct (region_end ts n b) as [e|] eqn:R.
    + apply (rinv_pair ts n s p KBracket below (RInert (Some e)) I eq_refl HK Hcl
               (fun H => ltac:(discriminate H)) Hlv).
      * intros d. rewrite Hbar. split; [intros H; left; exact H|].
        intros [H|(_ & E1 & E2)]; [exact H|]. rewrite Hn in E1.
        injection E1 as ->. congruence.
      * exact Db.
      * intros t Ht. cbn. split.
        -- intros H. exists b. split; [exact Hn|]. rewrite R. exact H.
        -- intros (b' & E & H). rewrite Hn in E. injection E as <-. rewrite R in H. exact H.
      * intros e' E. injection E as <-. pose proof (region_end_ge ts n b e R). lia.
    + destruct b.
      * apply (rinv_pair ts n s p KBracket (LBar n :: below) RNormal I eq_refl HK Hcl
                 (fun H => ltac:(discriminate H))).
        -- intros q k. cbn. rewrite <- Hlv. split; [intros [E|H]; [discriminate|exact H]|].
           intros H. right. exact H.
        -- intros d. cbn. rewrite Hbar. split.
           ++ intros [E|H]; [injection E as <-; right; auto|left; exact H].
           ++ intros [H|(-> & _ & _)]; [right; exact H|left; reflexivity].
        -- constructor; [exact Db|]. apply Forall_forall. intros x Hx.
           specialize (Hlt x Hx). cbn. lia.
        -- intros t Ht. split; [intros []|].
           intros (b' & E & H). rewrite Hn in E. injection E as <-. rewrite R in H.
           discriminate H.
        -- intros e' E. discriminate E.
      * apply (rinv_pair ts n s p KBracket below (RInert None) I eq_refl HK Hcl
                 (fun H => ltac:(discriminate H)) Hlv).
        -- intros d. rewrite Hbar. split; [intros H; left; exact H|].
           intros [H|(_ & E & _)]; [exact H|congruence].
        -- exact Db.
        -- intros t Ht. cbn. split; [intros _; exists false; split; [exact Hn|rewrite R; reflexivity]|].
           intros _. exact Logic.I.
        -- intros e' E. discriminate E.
Qed.

Lemma rinv_run : forall ts pre suf s,
  ts = (pre ++ suf)%list -> rinv ts (length pre) s ->
  rinv ts (length ts) (rrun ts (length pre) suf s).
Proof.
  intros ts pre suf. revert pre.
  induction suf as [|t rest IH]; intros pre s E I; cbn [rrun].
  - rewrite E, app_nil_r. rewrite E, app_nil_r in I. exact I.
  - assert (Hn : nth_error ts (length pre) = Some t).
    { rewrite E, nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
    specialize (IH (pre ++ [t])%list (rstep ts (length pre) t s)).
    rewrite length_app in IH. cbn [length] in IH. rewrite Nat.add_1_r in IH.
    apply IH; [rewrite E, <- app_assoc; reflexivity|].
    apply rinv_step; [exact Hn|exact I].
Qed.

Lemma rinv_start : forall ts, rinv ts 0 rstart.
Proof.
  intros ts. constructor; cbn [rs_live rs_pairs rs_os rs_mode rstart].
  - intros i j [].
  - intros q [].
  - intros q k. split; [intros []|intros ([] & _)].
  - intros d. split; [intros []|intros (p & [] & _)].
  - constructor.
  - intros t _. split; [intros (p & d & b & [] & _)|intros []].
  - intros e E. discriminate E.
  - intros i j [].
  - intros j H. lia.
  - intros q H. lia.
Qed.

Theorem ref_read_valid : forall ts, valid ts (ref_read ts).
Proof.
  intros ts. unfold ref_read.
  pose proof (rinv_run ts [] ts _ eq_refl (rinv_start ts)) as I.
  set (s := rrun ts 0 ts rstart) in *.
  split; [|split].
  - exact (ri_pairs ts _ s I).
  - intros j k Hk. destruct (Nat.lt_ge_cases j (length ts)) as [Hj|Hj].
    + exact (ri_unmatched ts _ s I j Hj k Hk).
    + unfold close_key in Hk. rewrite (proj2 (nth_error_None ts j) Hj) in Hk.
      discriminate.
  - intros q. destruct (Nat.lt_ge_cases q (length ts)) as [Hq|Hq].
    + exact (ri_os ts _ s I q Hq).
    + split.
      * intros H. specialize (ri_bound_os ts _ s I q H). lia.
      * intros ([k Hk] & _). unfold open_key in Hk.
        rewrite (proj2 (nth_error_None ts q) Hq) in Hk. discriminate.
Qed.

(*
The tree
========

What a matching describes: each pair of delimiters becomes its row's
node around the tokens between, a bracket pair with a region that ends
becomes a link to the region's text, and every other token is text.
Adjacent text is one `Str`, as the scanner writes it. *)

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
  end.

(* A run escaped by a backslash is a non-breaking space and the rest of
   the run when it begins with a space (O5). *)
Definition nbsp_rest (ws : string) : option string :=
  match ws with
  | String c rest => if Ascii.eqb c " "%char then Some rest else None
  | EmptyString => None
  end.

(* A token in a destination, which decodes an escape as text does and
   keeps everything else as written. *)
Definition tok_dest (t : token) : string :=
  match t with
  | TEsc c => esc_text c
  | _ => tok_text t
  end.

(* What a token adds to a region's text: a reference label keeps it as
   written. *)
Definition tok_region (dest : bool) (t : token) : string :=
  if dest then tok_dest t else tok_text t.

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

(* A break right after a hard break is that break: no soft one follows. *)
Definition after_hard (ts : list token) (i : nat) : bool :=
  match i with
  | O => false
  | S j => match nth_error ts j with Some (THard _) => true | _ => false end
  end.

(* A destination is written without its line breaks. *)
Fixpoint no_nl (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => if Ascii.eqb c nl_char then no_nl rest else String c (no_nl rest)
  end.

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

Definition is_opener (m : matching) (i : nat) : bool :=
  existsb (fun e => Nat.eqb (fst e) i) m.

Definition is_closer (m : matching) (j : nat) : bool :=
  existsb (fun e => Nat.eqb (snd e) j) m.

(* After a bracket pair, a region's text is gathered up to its end; the
   token that opens the region is not part of it. *)
Inductive tmode : Type :=
  | TMNormal
  | TMRegion (dest : bool) (kids : inlines) (d : nat) (e : option nat) (txt : string).

Definition tstate : Type := (tframes * inlines * tmode)%type.

Definition tnormal (r : tframes * inlines) : tstate := (fst r, snd r, TMNormal).

Definition tstep (ts : list token) (m : matching) (i : nat) (t : token)
  (st : tstate) : tstate :=
  let '(fs, top, md) := st in
  match md with
  | TMRegion b kids d e txt =>
      if match e with Some e' => Nat.eqb i e' | None => false end
      then tnormal (temit (mk (region_node b kids txt)) fs top)
      else (fs, top, TMRegion b kids d e
                       (if Nat.eqb i (S d) then txt else (txt ++ tok_region b t)%string))
  | TMNormal =>
      match t with
      | TText _ => tnormal (temit_str (tok_text t) fs top)
      | TEsc c => tnormal (temit_str (esc_text c) fs top)
      | TEscWs ws =>
          match nbsp_rest ws with
          | Some rest =>
              let '(fs', top') := temit (mk NonBreakingSpace) fs top in
              tnormal (if nonempty_str rest then temit_str rest fs' top' else (fs', top'))
          | None => tnormal (temit_str (tok_text t) fs top)
          end
      | THard _ =>
          let '(fs', top') := ttrim fs top in tnormal (temit (mk HardBreak) fs' top')
      | TBreak =>
          if after_hard ts i then (fs, top, TMNormal)
          else tnormal (temit (mk SoftBreak) fs top)
      | TDelim k _ _ _ =>
          if is_opener m i then ((TKDelim k, []) :: fs, top, TMNormal)
          else match is_closer m i, fs with
               | true, (TKDelim k', acc) :: fs0 =>
                   tnormal (temit (mk (dnode k' (List.rev acc))) fs0 top)
               | _, _ => tnormal (temit_str (tok_text t) fs top)
               end
      | TOpen =>
          if is_opener m i then ((TKBracket, []) :: fs, top, TMNormal)
          else tnormal (temit_str (tok_text t) fs top)
      | TClose b =>
          match is_closer m i, fs with
          | true, (_, acc) :: fs0 =>
              let kids := List.rev acc in
              match region_end ts i b with
              | Some e => (fs0, top, TMRegion b kids i (Some e) EmptyString)
              | None =>
                  if b
                  then tnormal (temit_all (mk (Str (one lbrack)) :: kids
                                           ++ [mk (Str (one rbrack))])%list fs0 top)
                  else (fs0, top, TMRegion false kids i None EmptyString)
              end
          | _, _ => tnormal (temit_str (tok_text t) fs top)
          end
      end
  end.

Fixpoint tree_go (ts : list token) (m : matching) (i : nat) (rest : list token)
  (st : tstate) : tstate :=
  match rest with
  | [] => st
  | t :: more => tree_go ts m (S i) more (tstep ts m i t st)
  end.

(* A valid matching closes every pair it opens, so no frame is left at
   the end; a reference label that never ended is text, brackets and
   all. *)
Definition tree_end (st : tstate) : inlines :=
  let '(fs, top, md) := st in
  match md with
  | TMRegion b kids _ None txt =>
      List.rev (snd (temit_all (mk (Str (one lbrack)) :: kids
                                ++ [mk (Str (one rbrack ++ one lbrack ++ txt))])%list
                       fs top))
  | _ => List.rev top
  end.

Definition tree_of (ts : list token) (m : matching) : inlines :=
  tree_end (tree_go ts m 0 ts ([], [], TMNormal)).

End WithTable.
