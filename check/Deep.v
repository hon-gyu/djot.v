(* ai-disclosure: ai-generated *)

(* The depth-3 half of `theories/Generate.v`, in the Rocq kernel.

   **`make roundtrip` is the routine check now.**  It runs this exact
   sweep -- `Generate.rt_lhs` and `rt_rhs`, the same functions -- in the
   extracted parser, at depth 3 in about five seconds, and it pins the
   counts too.  This file does the same work in the kernel and takes
   about twenty minutes, so run it when you want the *certification*
   rather than the answer: before a release, or when the extraction
   itself is in doubt.

   Why the kernel is so much slower, and why the obvious fix is not one.
   `vm_compute` normalizes the sweep and then `Qed` converts the proof
   term again, so the cost looks like it should halve with a single
   kernel-side cast.  Measured at depth 2 on 2026-08-21: 16.9s split
   between tactic and `Qed`, 16.2s as one `vm_cast_no_check`.  A 4%
   saving.  The conversion is the cost, and it is paid either way.

   | check              | vm_compute | Qed    |
   | ------------------ | ---------- | ------ |
   | `gen_roundtrip_3`  | 88.5s      | 87.6s  |
   | `accepted_counts`  | 42.1s      | 42.4s  |

   Those were measured at 17140 accepted documents; the pool is 24220 now
   and the file takes ~20 minutes.

   This directory has no dune stanza, so dune ignores it.  The depth-1
   and depth-2 roundtrips stay in `Generate.v` and do run on every build,
   in ~17s, so the kernel still certifies the small instance on every
   edit and only the deep sweep moved. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Ast Parser Render Generate.
Import ListNotations.

Local Open Scope string_scope.

Example gen_roundtrip_3 : map rt_lhs (accepted 3) = map rt_rhs (accepted 3).
Proof. vm_compute. reflexivity. Qed.

(* The delimiter leaf took these to (82, 1009, 12054), the link leaf to
   (99, 1222, 14597) and the image leaf to (116, 1435, 17140).  The
   reference definition and the reference link landed together and took
   them to (150, 1861, 22226); `blank_absorbed` then admitted more
   spacings, and admitting a code block inside a list item -- which the
   fence's recorded column bought -- took them to (160, 2020, 24220).
   The autolink and raw leaves took them to (228, 2708, 31272), and a
   paragraph whose interior line is an escaped bullet marker -- the leaf
   that reaches the escaper's line-initial rule -- took them to
   (245, 2910, 33605). Splitting raw blocks from code blocks in the
   canonical generator took them to (262, 3112, 35938), and the explicit
   id -- a wrapper, so one named copy of every block in the pool -- moved
   them to (278, 3470, 41186).  The escaped-backtick table/link leaf gives
   the numbers below. A tightness rule or a lifted
   exclusion can enlarge the fragment without adding a construct. Either way
   the count is a coverage witness: a change here must enlarge the generated
   fragment rather than only change its proofs. *)
Example accepted_counts : (List.length (accepted 1),
                           List.length (accepted 2),
                           List.length (accepted 3)) = (296, 3695, 43857).
Proof. vm_compute. reflexivity. Qed.
