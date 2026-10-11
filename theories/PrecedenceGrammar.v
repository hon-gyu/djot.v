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
   as a kind with no live opener and none barred, or as a delimiter whose
   only live opener is right before it, with nothing to enclose (M3).
   Such a token is read as an opener when it may open, and is text
   otherwise. *)
Definition free (L : list key) (pv : option key) (B : list key) (t : token) : Prop :=
  forall k, closes_as t = Some k ->
    (In k L /\ needs_content k = true /\ pv = Some k) \/ (~ In k L /\ ~ In k B).

(* A closer that only a destination keeps from its opener: text, even if
   it may open. *)
Definition barred_tok (L B : list key) (t : token) : Prop :=
  exists k, closes_as t = Some k /\ ~ In k L /\ In k B.

(* Where a level goes on after a pair closed at `e`: after a delimiter,
   or past the region of a `]`.  Nowhere when a destination or a label
   does not close. *)
Definition past (s : string) (e : nat) (tc : token) (le : nat) : option nat :=
  match tc with
  | TClose b => option_map S (region_end s e b)
  | TSpan b _ => Some (e + S (S (S (String.length b))))
  | _ => Some (e + le)
  end.

(*
The grammar
===========

A level of the paragraph is `seq s L F pv B p`, read from offset `p`:

- `L`, the kinds with a live opener: a closer of one must close;
- `F`, the kind of the pair this is the content of, if any: its opener
  may not be left unmatched here, or it would be the closest;
- `pv`, the kind of a live opener right before `p`, if any;
- `B`, the kinds barred by a destination that does not close.

  R0  ε                                          at the paragraph's end, or at a closer of F
  R1  text                                       seq L F - B
  R2  close_k                                    seq L F - B        free, and may not open
  R2' close_k                                    seq L F - B        barred
  R3  open_k                                     seq (k+L) F k B    k is not F
  R4  open_k  seq (k+L) k k B  close_k           seq L F - B        a delimiter encloses something
  R5  [  seq ([+L) [ [ B  ]  region              seq L F - B        the region ends
  R6  [  seq ([+L) [ [ B  ](                     seq - F - (L+B)    no balancing `)`: to the end
  R7  [  seq ([+L) [ [ B  ][                                        no `]`: the rest is the label

Tokens are the specification's (`tok_at`), walked by byte offset as a
reading's chain is.  An opener in R3 to R7 is a token that may open and
is free. *)

Inductive seq (s : string)
  : list key -> option key -> option key -> list key -> nat -> gparse -> Prop :=
  | seq_end : forall L F pv B p,
      tok_at s p = None ->
      seq s L F pv B p ([], [], p)
  | seq_stop : forall L pv B p t l k,
      tok_at s p = Some (t, l) -> closes_as t = Some k ->
      seq s L (Some k) pv B p ([], [], p)
  | seq_text : forall L F pv B p t l r,
      tok_at s p = Some (t, l) ->
      (opens_as t = None /\ free L pv B t) \/ barred_tok L B t ->
      seq s L F None B (p + l) r ->
      seq s L F pv B p r
  | seq_open : forall L F pv B p t l k m os e,
      tok_at s p = Some (t, l) -> opens_as t = Some k -> free L pv B t ->
      F <> Some k ->
      seq s (k :: L) F (Some k) B (p + l) (m, os, e) ->
      seq s L F pv B p (m, os ++ [p], e)
  | seq_pair : forall L F pv B p t l k m1 os1 e tc le q m2 os2 e2,
      tok_at s p = Some (t, l) -> opens_as t = Some k -> free L pv B t ->
      seq s (k :: L) (Some k) (Some k) B (p + l) (m1, os1, e) ->
      tok_at s e = Some (tc, le) -> closes_as tc = Some k ->
      (needs_content k = true -> p + l < e) ->
      past s e tc le = Some q ->
      seq s L F None B q (m2, os2, e2) ->
      seq s L F pv B p (m2 ++ (p, e) :: m1, os2 ++ os1 ++ [p], e2)
  | seq_dest : forall L F pv B p t l m1 os1 e le m2 os2 e2,
      tok_at s p = Some (t, l) -> opens_as t = Some KBracket -> free L pv B t ->
      seq s (KBracket :: L) (Some KBracket) (Some KBracket) B (p + l) (m1, os1, e) ->
      tok_at s e = Some (TClose true, le) -> region_end s e true = None ->
      seq s [] F None (L ++ B) (S e) (m2, os2, e2) -> tok_at s e2 = None ->
      seq s L F pv B p (m2 ++ (p, e) :: m1, os2 ++ os1 ++ [p], e2)
  | seq_label : forall L F pv B p t l m1 os1 e le,
      tok_at s p = Some (t, l) -> opens_as t = Some KBracket -> free L pv B t ->
      seq s (KBracket :: L) (Some KBracket) (Some KBracket) B (p + l) (m1, os1, e) ->
      tok_at s e = Some (TClose false, le) -> region_end s e false = None ->
      seq s L F pv B p ((p, e) :: m1, os1 ++ [p], String.length s).

(* A paragraph's parses: a top level read to the paragraph's end. *)
Definition parses (s : string) (r : reading) : Prop :=
  exists e, tok_at s e = None /\ seq s [] None None [] 0 (fst r, snd r, e).

End WithTable.
