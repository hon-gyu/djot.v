(* ai-disclosure: autonomous *)

(* The precedence rules (`Precedence.v`) as a grammar over a paragraph's
   tokens, run as an enumerator of its parses.  Not proved: `make
   check-grammar` compares it with `ref_read` on generated paragraphs, and
   `.project/inline-grammar.md` states it for reading.

   A level of the paragraph, `Seq(S, F, p, B)`, carries
   - `S`, the kinds with a live opener: a closer of one must close;
   - `F`, the kind of the pair whose content this is: its opener may not
     be left unmatched here, or it would be the closest;
   - `p`, the kind of a live opener right before, which a delimiter
     closer may not pair with (nothing to enclose);
   - `B`, the kinds barred by a destination that does not close: a closer
     of one is text.

   Tokens and regions are the specification's (`tok_at`, `region_end`),
   the tokens read straight through the paragraph and indexed in order;
   a parse's positions are turned into byte offsets at the end. *)

From Stdlib Require Import String Ascii List Bool Arith.
From DjotV Require Import Strings InlineTable Precedence.
Import ListNotations.

Section WithTable.
Context {T : dtable}.

(*
Parses
======
*)

(* The paragraph's tokens and their offsets, with no region skipped. *)
Fixpoint toks_from (s : string) (fuel p : nat) : list (nat * token) :=
  match fuel with
  | O => []
  | S f =>
      match tok_at s p with
      | Some (t, l) => (p, t) :: toks_from s f (p + l)
      | None => []
      end
  end.

Definition para_toks (s : string) : list (nat * token) :=
  toks_from s (S (String.length s)) 0.

Fixpoint index_of (z : nat) (offs : list nat) (i : nat) : option nat :=
  match offs with
  | [] => None
  | o :: rest => if Nat.eqb o z then Some i else index_of z rest (S i)
  end.

(* `region_end` on token indices. *)
Definition region_ix (s : string) (offs : list nat) (e : nat) (b : bool) : option nat :=
  match region_end s (nth e offs 0) b with
  | Some z => index_of z offs 0
  | None => None
  end.

(* A parse of a stretch of tokens: its pairs, its openers, and where it
   stopped, as a position and the tokens from there. *)
Definition gparse : Type := (matching * list nat * nat * list token)%type.

Definition kmem (k : key) (ks : list key) : bool := existsb (key_eq k) ks.

Definition kis (k : key) (o : option key) : bool :=
  match o with Some k' => key_eq k k' | None => false end.

(* Each parse of `rest` from `rest'`, its pairs and openers added. *)
Local Definition after (m : matching) (os : list nat) (rs : list gparse) : list gparse :=
  map (fun '(m', os', j, r) => ((m ++ m')%list, (os ++ os')%list, j, r)) rs.

(*
The grammar
===========

`seq` gives every parse of a level from token `i`, `rest` being the tokens
from `i`.  A level stops (R0) at the end of the paragraph, or inside a
pair at a closer of its kind; R4 to R7 then decide whether that closer
pairs.

  R0  ε
  R1  text                               Seq(S, F, -, B)
  R2  close_k                            Seq(S, F, -, B)     k not live, or only right before
  R2' close_k                            Seq(S, F, -, B)     k barred: text, does not open
  R3  open_k                             Seq(S+k, F, k, B)   k is not F
  R4  open_k Seq(S+k, k, k, B) close_k   Seq(S, F, -, B)     a delimiter pair encloses something
  R5  open_[ Seq(S+[, [, [, B) ]  region Seq(S, F, -, B)     the region to its end (`region_end`)
  R6  open_[ Seq(S+[, [, [, B) ](  Seq(-, F, -, B+S)         a destination that does not close:
                                                             the rest of the paragraph, barred
  R7  open_[ Seq(S+[, [, [, B) ][  rest                      a label that does not close: source

A token that may both open and close is a closer first (R2's condition
and the rule that a live kind must close), an opener when it closes
nothing; a barred one is neither. *)

Fixpoint seq (fuel : nat) (s : string) (offs : list nat) (ts : list token) (i : nat) (rest : list token)
  (live : list key) (forb : option key) (prev : option key) (barred : list key)
  : list gparse :=
  match fuel with
  | O => []
  | S fuel' =>
      let r0 := ([], [], i, rest) in
      match rest with
      | [] => [r0]
      | t :: more =>
          let text := seq fuel' s offs ts (S i) more live forb None barred in
          (* R3 and R4 to R7, for an opener of `k` at `i`. *)
          let opener (k : key) : list gparse :=
            let r3 :=
              if kis k forb then []
              else after [] [i] (seq fuel' s offs ts (S i) more (k :: live) forb (Some k) barred) in
            (* Not a rule, a shortcut: with no closer of `k` ahead, R4 to
               R7 have nothing to end on.  Without it an unclosed opener
               costs a search of the rest of the paragraph, and a few of
               them make the enumeration exponential. *)
            let closer_ahead :=
              existsb (fun u => kis k (closes_as u)) more in
            let pairs :=
              if negb closer_ahead then [] else
              flat_map
                (fun '(m1, os1, e, r1) =>
                   match r1 with
                   | tc :: r2 =>
                       match closes_as tc with
                       | Some k' =>
                           if key_eq k k' && (negb (needs_content k) || Nat.ltb (S i) e)
                           then
                             let m := ((i, e) :: m1)%list in
                             let os := (i :: os1)%list in
                             match tc with
                             | TClose b =>
                                 match region_ix s offs e b with
                                 | Some z =>                                         (* R5 *)
                                     after m os
                                       (seq fuel' s offs ts (S z) (skipn (S z) ts) live forb None barred)
                                 | None =>
                                     if b
                                     then                                            (* R6 *)
                                       filter (fun '(_, _, _, r) => match r with [] => true | _ => false end)
                                         (after m os
                                            (seq fuel' s offs ts (S e) r2 [] forb None (live ++ barred)))
                                     else [(m, os, length ts, [])]                   (* R7 *)
                                 end
                             | _ =>                                                  (* R4 *)
                                 after m os (seq fuel' s offs ts (S e) r2 live forb None barred)
                             end
                           else []
                       | None => []
                       end
                   | [] => []
                   end)
                (seq fuel' s offs ts (S i) more (k :: live) (Some k) (Some k) barred) in
            (r3 ++ pairs)%list in
          let as_opener :=
            match opens_as t with Some k => opener k | None => text end in
          (* R0 inside a pair: the level ends at a closer of the pair's
             kind, which it cannot read itself.  Anywhere else no parse
             would follow, so the level does not stop there. *)
          let ends :=
            match forb, closes_as t with
            | Some f, Some k => key_eq f k && negb (needs_content k && kis k prev)
            | _, _ => false
            end in
          (if ends then [r0] else []) ++
          match closes_as t with
          | Some k =>
              if kmem k live
              then if needs_content k && kis k prev then as_opener else []  (* R2, adjacent *)
              else if kmem k barred then text                                (* R2' *)
              else as_opener                                                 (* R2, or an opener *)
          | None =>
              match opens_as t with
              | Some k => opener k
              | None => text                                                 (* R1 *)
              end
          end
      end
  end.

(* The parses of a whole paragraph, in byte offsets. *)
Definition grammar_read (s : string) : list (matching * list nat) :=
  let pts := para_toks s in
  let offs := map fst pts in
  let ts := map snd pts in
  let off i := nth i offs 0 in
  flat_map
    (fun '(m, os, _, r) =>
       match r with
       | [] => [(map (fun '(i, j) => (off i, off j)) m, map off os)]
       | _ => []
       end)
    (seq (S (S (length ts))) s offs ts 0 ts [] None None []).

End WithTable.
