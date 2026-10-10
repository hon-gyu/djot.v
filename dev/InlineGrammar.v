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
   and a parse walks the paragraph by byte offset as a reading's chain
   does: a token from where the last one ended, or from past a region. *)

From Stdlib Require Import String Ascii List Bool Arith.
From DjotV Require Import Strings InlineTable Precedence.
Import ListNotations.

Section WithTable.
Context {T : dtable}.

(*
Parses
======
*)

Definition kmem (k : key) (ks : list key) : bool := existsb (key_eq k) ks.

Definition kis (k : key) (o : option key) : bool :=
  match o with Some k' => key_eq k k' | None => false end.

(* Whether a token at some offset from `p` on closes as `k`, whatever
   the reading. *)
Definition closer_from (s : string) (k : key) (p : nat) : bool :=
  existsb (fun q => match tok_at s q with Some (u, _) => kis k (closes_as u) | None => false end)
    (seq p (String.length s - p)).

(* A parse of a stretch of the paragraph: its pairs, its openers, and the
   offset where it stopped. *)
Definition gparse : Type := (matching * list nat * nat)%type.

(* Each parse of `rest` from `rest'`, its pairs and openers added. *)
Local Definition after (m : matching) (os : list nat) (rs : list gparse) : list gparse :=
  map (fun '(m', os', j) => ((m ++ m')%list, (os ++ os')%list, j)) rs.

(*
The grammar
===========

`level` gives every parse of a level from offset `p`.  A level stops
(R0) at the end of the paragraph, or inside a pair at a closer of its
kind; R4 to R7 then decide whether that closer pairs.

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

Fixpoint level (fuel : nat) (s : string) (p : nat)
  (live : list key) (forb : option key) (prev : option key) (barred : list key)
  : list gparse :=
  match fuel with
  | O => []
  | S fuel' =>
      let r0 := ([], [], p) in
      match tok_at s p with
      | None => [r0]
      | Some (t, l) =>
          let q := p + l in
          let text := level fuel' s q live forb None barred in
          (* R3 and R4 to R7, for an opener of `k` at `p`. *)
          let opener (k : key) : list gparse :=
            let r3 :=
              if kis k forb then []
              else after [] [p] (level fuel' s q (k :: live) forb (Some k) barred) in
            (* Not a rule, a shortcut: with no closer of `k` ahead, R4 to
               R7 have nothing to end on.  Without it an unclosed opener
               costs a search of the rest of the paragraph, and a few of
               them make the enumeration exponential. *)
            let pairs :=
              if negb (closer_from s k q) then [] else
              flat_map
                (fun '(m1, os1, e) =>
                   match tok_at s e with
                   | Some (tc, le) =>
                       match closes_as tc with
                       | Some k' =>
                           if key_eq k k' && (negb (needs_content k) || Nat.ltb q e)
                           then
                             let m := ((p, e) :: m1)%list in
                             let os := (p :: os1)%list in
                             match tc with
                             | TClose b =>
                                 match region_end s e b with
                                 | Some z =>                                         (* R5 *)
                                     after m os (level fuel' s (S z) live forb None barred)
                                 | None =>
                                     if b
                                     then                                            (* R6 *)
                                       filter (fun '(_, _, r) => Nat.eqb r (String.length s))
                                         (after m os
                                            (level fuel' s (e + le) [] forb None (live ++ barred)))
                                     else [(m, os, String.length s)]                 (* R7 *)
                                 end
                             | _ =>                                                  (* R4 *)
                                 after m os (level fuel' s (e + le) live forb None barred)
                             end
                           else []
                       | None => []
                       end
                   | None => []
                   end)
                (level fuel' s q (k :: live) (Some k) (Some k) barred) in
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

(* The parses of a whole paragraph. *)
Definition grammar_read (s : string) : list (matching * list nat) :=
  flat_map
    (fun '(m, os, r) => if Nat.eqb r (String.length s) then [(m, os)] else [])
    (level (S (S (String.length s))) s 0 [] None None []).

End WithTable.
