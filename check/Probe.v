(* ai-disclosure: ai-generated *)

(* The parser-coupled half of the probe apparatus: pools of inputs, a
   comparison on states, and the probe runs themselves.

   Not in the dune build, and not because it is slow -- it is about a
   second.  It is out because everything here is a *liability against
   parser drift*: `show_pstate` matches on every `pstate` constructor, so
   adding one breaks this file.  That break is wanted (a state the
   printer ignores would silently compare equal to a different one), but
   it should land on `make probe` rather than on `dune build`, so that a
   parser edit is never blocked by a testing file.  The combinators it
   uses are in `theories/Probe.v`, which is Stdlib-only and does build.

   How to use it.  To decide whether a candidate lemma is worth proving,
   add a `Compute` below and run `make probe`.  A `Some` is a
   counterexample and the statement is dead.  A `None` is *not* a proof:
   read the tally beside it, and disbelieve any result whose `t_pass` is
   0, because the guard discarded everything. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Strings Line Ast Attributes Parser Render Probe.
Import ListNotations.

Local Open Scope string_scope.

(*
Showing states
==============

The printer is the comparison: `st_eqb` is `String.eqb` on the rendering.
That is sound as an equality test only if the printer is injective, so
every list and every string is written with its length in front --
`2:ab` rather than `ab` -- which makes the encoding unambiguous without
needing an escape convention.

The one place that argument does not reach is `blocks`, printed with
`render_djot` rather than structurally.  `roundtrip_blocks` makes
`render_djot` injective on the canonical fragment, so two states holding
canonical blocks compare correctly; two holding blocks *outside* that
fragment could in principle print alike and produce a spurious pass.
Every state in `state_pool` is a parser output on canonical input, so the
gap is not reachable from here.  A probe over hand-built states with
exotic block content should not trust a `None`.
*)

Definition s_str (s : string) : string :=
  nat_str (String.length s) ++ ":" ++ s.

Definition s_nat (n : nat) : string := nat_str n ++ ";".

Definition s_bool (b : bool) : string := if b then "T" else "F".

Definition s_list {A : Type} (f : A -> string) (xs : list A) : string :=
  nat_str (List.length xs) ++ "[" ++ String.concat "" (map f xs) ++ "]".

Definition s_ascii (c : ascii) : string := String c EmptyString.

Definition s_blocks (bs : blocks) : string := s_str (render_djot bs).

Definition s_kv (kv : string * string) : string :=
  s_str (fst kv) ++ s_str (snd kv).

Definition s_attr (a : attr) : string := s_list s_kv a.

Definition s_fence (f : fence) : string :=
  s_ascii (f_ch f) ++ s_nat (f_len f) ++ s_str (f_info f).

Definition s_astate (a : astate) : string :=
  match a with
  | AScan => "sc" | AId => "id" | AClass => "cl" | AKey => "ke"
  | AVal => "va" | ABare => "ba" | AQuot => "qu" | AEsc => "es"
  | AComment => "co" | AFail => "fa" | ADone => "do"
  end.

Definition s_aparser (p : aparser) : string :=
  s_astate (ap_st p) ++ s_str (ap_tok p) ++ s_str (ap_key p)
  ++ s_attr (ap_attrs p).

Definition s_ols (n : ordered_list_style) : string :=
  match n with
  | Decimal => "d" | LetterUpper => "A" | LetterLower => "a"
  | RomanUpper => "I" | RomanLower => "i"
  end.

Definition s_old (d : ordered_list_delim) : string :=
  match d with RightPeriod => "." | RightParen => ")" | LeftRightParen => "(" end.

Definition s_lstyle (y : lstyle) : string :=
  match y with
  | SBullet c => "b" ++ s_ascii c
  | SOrd n d => "o" ++ s_ols n ++ s_old d
  end.

Definition s_cand (p : lstyle * nat) : string :=
  s_lstyle (fst p) ++ s_nat (snd p).

Definition s_lstate (ls : list_state) : string :=
  s_nat (ls_indent ls) ++ s_list s_cand (ls_styles ls)
  ++ s_bool (ls_loose ls) ++ s_bool (ls_blanks ls)
  ++ s_list s_blocks (ls_items ls).

Fixpoint show_pstate (st : pstate) : string :=
  match st with
  | PPara cur => "Para" ++ s_list s_str cur
  | PHeading lvl cur => "Head" ++ s_nat lvl ++ s_list s_str cur
  | PFence f acc => "Fence" ++ s_fence f ++ s_list s_str acc
  | PQuote done inner => "Quote" ++ s_blocks done ++ "(" ++ show_pstate inner ++ ")"
  | PDiv len cls done inner =>
      "Div" ++ s_nat len ++ s_str cls ++ s_blocks done
      ++ "(" ++ show_pstate inner ++ ")"
  | PList ls done inner =>
      "List" ++ s_lstate ls ++ s_blocks done ++ "(" ++ show_pstate inner ++ ")"
  | PAttr pend ind ap slices =>
      "Attr" ++ s_attr pend ++ s_nat ind ++ s_aparser ap ++ s_list s_str slices
  | PPend pend inner =>
      "Pend" ++ s_attr pend ++ "(" ++ show_pstate inner ++ ")"
  end.

Definition st_eqb (a b : pstate) : bool :=
  String.eqb (show_pstate a) (show_pstate b).

Definition bs_eqb (a b : blocks) : bool :=
  String.eqb (render_djot a) (render_djot b).

(* The pair a `step` probe compares. *)
Definition out_eqb (a b : blocks * pstate) : bool :=
  bs_eqb (fst a) (fst b) && st_eqb (snd a) (snd b).

(*
The pools
=========

Curated, not enumerated: one line per `line_kind` constructor and one
seed per `pstate` constructor, plus the few variants where a second
inhabitant is known to behave differently (an indented marker, a list
with its blank flag armed, a nested list).  `.project`'s generator note
applies here too -- coverage of shapes, not volume -- with the added
reason that these pools get multiplied together.
*)

(* One per `line_kind`, then the indented spellings, which is where the
   column bugs in the lessons file lived. *)
Definition line_pool : list string :=
  [ ""; "  "                                   (* KBlank *)
  ; "---"; "***"                               (* KThematic *)
  ; "```"; "``` c"; "~~~"                      (* KFence *)
  ; "::: c"; ":::"                             (* KDiv *)
  ; "> a"; ">"                                 (* KQuote *)
  ; "# h"; "## h"                              (* KHeading *)
  ; "- a"; "* a"; "+ a"                        (* KList, bullet *)
  ; "1. a"; "1) a"; "(1) a"                    (* KList, decimal *)
  ; "i. a"; "a. a"                             (* KList, ambiguous / alpha *)
  ; "{#i}"; "{#i"                              (* KAttr, done / pending *)
  ; "a"; "<}"                                  (* KText *)
  ; "  a"; "  - a"; "  > a"; "  ```"           (* the same, indented *)
  ].

(* Prefixes chosen so that running them lands on each `pstate`
   constructor.  Reachability is the point: a `pstate` built by hand is
   usually one no run produces, and a counterexample at such a state
   refutes nothing a theorem about the parser claims. *)
Definition seed_prefixes : list (list string) :=
  [ []                                         (* idle *)
  ; ["a"]; ["a"; "b"]                          (* PPara *)
  ; ["# h"]                                    (* PHeading *)
  ; ["```"]; ["``` x"; "raw"]                  (* PFence *)
  ; ["> a"]; ["> - a"]                         (* PQuote *)
  ; ["::: c"]; ["::: c"; "a"]                  (* PDiv *)
  ; ["- a"]; ["- a"; ""]; ["1. a"]; ["i. a"]   (* PList *)
  ; ["- - a"]; ["  - a"]                       (* PList, nested / indented *)
  ; ["{#i"]                                    (* PAttr *)
  ; ["{#i}"]; ["{#i}"; "a"]                    (* PPend *)
  ].

Definition state_pool : list pstate :=
  map (fun ls => snd (run_lines ls (PPara []))) seed_prefixes.

(* The product every `forall st l` probe runs over: 19 x 29 = 551. *)
Definition sl_pool : list (pstate * string) := pairs state_pool line_pool.

Definition show_sl (p : pstate * string) : string :=
  show_pstate (fst p) ++ " |= " ++ s_str (snd p).

(*
Probes
======

Three standing runs.  They are not regressions on the parser -- the
suites already cover that -- they are regressions on the apparatus, and
they are what a new probe should be copied from.
*)

(* Sanity: the pools reach what they claim to.  If a `pstate`
   constructor stops appearing here, a seed has gone stale and every
   probe below has quietly narrowed. *)
Compute map show_pstate state_pool.

(* A true statement, to show what a pass looks like.  `step_at 0` is
   `step` (`step_at_zero`), so this must find nothing, and its tally must
   be all-pass: an unconditional probe that reports skips is malformed. *)
Compute report show_sl
  (fun p => holds (out_eqb (step_at 0 (snd p) (fst p)) (step (snd p) (fst p))))
  sl_pool.

(* A false statement, to show what a failure looks like, and to keep the
   comparison honest: if `st_eqb` ever degenerates to `true` this stops
   reporting.  Padding a line by one column is *not* the same as leaving
   it alone -- that is the whole content of `step_fuel_pad`'s `pad_safe`
   hypothesis -- so a witness is expected here. *)
Compute probe show_sl
  (fun p => holds (out_eqb (step (" " ++ snd p) (fst p)) (step (snd p) (fst p))))
  sl_pool.

(*
Which ordered starts survive their own rendering
-----------------------------------------------

The side condition the roman and alpha chains need, measured rather than
argued.  Note what is *not* used here: `bs_eqb` renders, and the renderer
emits nothing for a non-decimal ordered list, so it would call every pair
equal and report a clean pass.  This compares the attributes the question
is actually about.
*)

Definition ol_shape (bs : blocks)
  : option (ordered_list_style * ordered_list_delim * nat * nat) :=
  match bs with
  | [n] =>
      match node_contents n with
      | OrderedList oa _ items =>
          Some (ol_style oa, ol_delim oa, ol_start oa, List.length items)
      | _ => None
      end
  | _ => None
  end.

Definition shape_eqb (a b : option (ordered_list_style * ordered_list_delim * nat * nat))
  : bool :=
  match a, b with
  | Some (n1, d1, s1, c1), Some (n2, d2, s2, c2) =>
      (ols_eqb n1 n2 && old_eqb d1 d2 && Nat.eqb s1 s2 && Nat.eqb c1 c2)%bool
  | None, None => true
  | _, _ => false
  end.

(* A run of `count` items from `start`, each item one line. *)
Definition ord_litems (mkm : nat -> marker) (start count : nat) : list litem :=
  map (fun k => (mkm (start + k), ["x"])) (seq 0 count).

Definition ord_marker (core : nat -> string) (d : ordered_list_delim)
                      (n : nat) : marker := MOrd (core n) d.

(* Does the canonical rendering of that run parse back to the ordered
   list it names?  `items_ok` is asked separately, because the two can
   part company: the parser may well accept a run the uniformity chain's
   hypothesis cannot describe, and that gap is the thing being measured. *)
Definition ord_rt (sty : ordered_list_style) (core : nat -> string)
                  (d : ordered_list_delim) (start count : nat) : bool :=
  let its := ord_litems (ord_marker core d) start count in
  shape_eqb
    (ol_shape (parse_lines (list_lines Tight (map litem_lines its)) (PPara [])))
    (Some (sty, d, start, count)).

Definition ord_items_ok (core : nat -> string) (d : ordered_list_delim)
                        (start count : nat) : bool :=
  match ord_litems (ord_marker core d) start count with
  | [] => false
  | (m0, _) :: _ as its => items_ok m0 its
  end.

(* Roman: which starts does a 3-item run round-trip at, and which does
   `items_ok` describe?  The answers are expected to coincide except
   where the first numeral is a bare roman letter. *)
Compute fails 40 (fun s => holds (ord_rt RomanLower (roman_str false) RightPeriod s 3))
                 (seq 1 30).
Compute fails 40 (fun s => holds (ord_items_ok (roman_str false) RightPeriod s 3))
                 (seq 1 30).

(* Alpha: same two questions.  Here the expected exceptions are the seven
   letters that are also roman digits. *)
Compute fails 40 (fun s => holds (ord_rt LetterLower (alpha_str false) RightPeriod s 3))
                 (seq 1 24).
Compute fails 40 (fun s => holds (ord_items_ok (alpha_str false) RightPeriod s 3))
                 (seq 1 24).

(* The real form, and the one to copy: a *conditional* statement, where
   `guarded` separates the discards out.  Read the tally first.  A shift
   of the offset and a pad of the line agree wherever `pad_safe` holds,
   which is `step_pad`. *)
Compute report show_sl
  (fun p => guarded (pad_safe (fst p))
              (out_eqb (step (" " ++ snd p) (fst p))
                       (step_at 1 (snd p) (fst p))))
  sl_pool.
