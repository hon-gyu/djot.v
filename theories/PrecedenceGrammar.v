(* ai-disclosure: autonomous *)

(* The precedence rules as a grammar over a paragraph's tokens: a third
   statement of them beside `valid` and `ref_read` (`Precedence.v`), and
   the one a reading can be derived by hand from.  Definitions only.
   `PrecedenceGrammarFacts.v` proves that the grammar's parses of a
   paragraph are exactly its valid reading. *)

From Stdlib Require Import String List Bool Arith.
From DjotV Require Import Strings InlineTable Precedence.
Import ListNotations.

Section WithTable.
Context {T : dtable}.

(* A parse of a stretch of the paragraph: its pairs and its openers,
   latest first, and the offset where it stopped. *)
Definition gparse : Type := (matching * list nat * nat)%type.

(* A token that does not act as a closer: it may not close, or it closes
   as a kind with no live opener, or as a delimiter whose only live opener
   is right before it, with nothing to enclose (M3).  Such a token is read
   as an opener when it may open, and is text otherwise. *)
Definition free (L : list key) (pv : option key) (t : token) : Prop :=
  forall k, closes_as t = Some k ->
    (In k L /\ needs_content k = true /\ pv = Some k) \/ ~ In k L.

(* Where a level goes on after a pair closed at `e`: after a delimiter,
   or past the region of a `]`. *)
Definition past (e : nat) (tc : token) (le : nat) : nat :=
  match tc with
  | TClose _ b | TSpan b _ => e + S (S (S (String.length b)))
  | _ => e + le
  end.

(*
The grammar
===========

A level of the paragraph is `seq s L F pv p`, read from offset `p`:

- `L`, the kinds with a live opener: a closer of one must close;
- `F`, the kind of the pair this is the content of, if any: its opener
  may not be left unmatched here, or it would be the closest;
- `pv`, the kind of a live opener right before `p`, if any.

  R0  ε                                    at the paragraph's end, or at a closer of F
  R1  text                                 seq L F -
  R2  close_k                              seq L F -       free, and may not open
  R3  open_k                               seq (k+L) F k   k is not F
  R4  open_k  seq (k+L) k k  close_k       seq L F -       a delimiter encloses something
  R5  [  seq ([+L) [ [  ]  region          seq L F -

Tokens are the specification's (`tok_at`), walked by byte offset as a
reading's chain is.  An opener in R3 to R5 is a token that may open and
is free.  R4 and R5 are one rule (`seq_pair`), the closer's region
skipped (`past`). *)

Inductive seq (s : string)
  : list key -> option key -> option key -> nat -> gparse -> Prop :=
  | seq_end : forall L F pv p,
      tok_at s p = None ->
      seq s L F pv p ([], [], p)
  | seq_stop : forall L pv p t l k,
      tok_at s p = Some (t, l) -> closes_as t = Some k ->
      seq s L (Some k) pv p ([], [], p)
  | seq_text : forall L F pv p t l r,
      tok_at s p = Some (t, l) -> opens_as t = None -> free L pv t ->
      seq s L F None (p + l) r ->
      seq s L F pv p r
  | seq_open : forall L F pv p t l k m os e,
      tok_at s p = Some (t, l) -> opens_as t = Some k -> free L pv t ->
      F <> Some k ->
      seq s (k :: L) F (Some k) (p + l) (m, os, e) ->
      seq s L F pv p (m, os ++ [p], e)
  | seq_pair : forall L F pv p t l k m1 os1 e tc le m2 os2 e2,
      tok_at s p = Some (t, l) -> opens_as t = Some k -> free L pv t ->
      seq s (k :: L) (Some k) (Some k) (p + l) (m1, os1, e) ->
      tok_at s e = Some (tc, le) -> closes_as tc = Some k ->
      (needs_content k = true -> p + l < e) ->
      seq s L F None (past e tc le) (m2, os2, e2) ->
      seq s L F pv p (m2 ++ (p, e) :: m1, os2 ++ os1 ++ [p], e2).

(* A paragraph's parses: a top level read to the paragraph's end. *)
Definition parses (s : string) (r : reading) : Prop :=
  exists e, tok_at s e = None /\ seq s [] None None 0 (fst r, snd r, e).

End WithTable.
