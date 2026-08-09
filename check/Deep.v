(* ai-disclosure: ai-generated *)

(* The depth-3 half of `theories/Generate.v`, kept out of the dune build.

   Why it is here.  These two checks cost ~260s of a ~270s clean build,
   and they are downstream of `Parser.v`, so every edit to the parser or
   the AST paid for them.  Measured with `coqc -time`:

   | check              | vm_compute | Qed    |
   | ------------------ | ---------- | ------ |
   | `gen_roundtrip_3`  | 88.5s      | 87.6s  |
   | `accepted_counts`  | 42.1s      | 42.4s  |
   | all of Generate.v besides | ~2s | |

   The `Qed` column is not a mistake: `vm_compute; reflexivity` runs the
   conversion in the tactic, and the kernel runs it again from scratch
   when it checks the proof term.  Both checks pay it twice, and there is
   no way around that short of trusting the tactic.

   This directory has no dune stanza, so dune ignores it.  Run it with
   `make deep`, which compiles this file against the theory dune already
   built.  It is not automatic: run it whenever `cb_ok`, the enumeration,
   the renderer or the block parser changes.  The depth-1 and depth-2
   roundtrips stay in `Generate.v` and do run on every build, so an
   ordinary regression still surfaces in ~1s; what only depth 3 adds is
   a container nested three deep. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Ast Parser Render Generate.
Import ListNotations.

Local Open Scope string_scope.

Example gen_roundtrip_3 : map rt_lhs (accepted 3) = map rt_rhs (accepted 3).
Proof. vm_compute. reflexivity. Qed.

(* Divs took these from (53, 593, 6437) to (68, 888, 11368): a div
   accepts any block sequence its contents do not close, so it roughly
   doubles the container arm.  Tightening `seps_loosen` -- a separator
   loosens only when the item after it does not open with a list marker
   -- took them back down, by making some `Loose` spellings
   unrenderable. *)
Example accepted_counts : (List.length (accepted 1),
                           List.length (accepted 2),
                           List.length (accepted 3)) = (65, 796, 9511).
Proof. vm_compute. reflexivity. Qed.
