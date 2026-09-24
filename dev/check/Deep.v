(* ai-disclosure: ai-generated *)

(* The depth-3 half of `dev/Generate.v`, in the Rocq kernel.

   `test/roundtrip.exe` runs the same sweep (`Generate.rt_lhs` and `rt_rhs`)
   in the extracted parser in seconds and pins the counts too.  This file
   does the work in the kernel, in about twenty minutes, for when the
   certification is wanted rather than the answer: before a release, or
   when the extraction itself is in doubt.

   The cost is conversion, and it is paid either way: replacing
   `vm_compute` then `Qed` with one kernel-side `vm_cast_no_check` saved
   about 4% at depth 2.

   `dev/check/dune` leaves this file out of the build.  Depths 1 and 2
   are checked in `Generate.v` on every build. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Ast Parser Render.
From DjotVDev Require Import Generate.
Import ListNotations.

Local Open Scope string_scope.

Example gen_roundtrip_3 : map rt_lhs (accepted 3) = map rt_rhs (accepted 3).
Proof. vm_compute. reflexivity. Qed.

(* The size of the accepted fragment at each depth.  A new leaf in
   `Generate.leaves` moves these, and so can a tightness rule or a lifted
   exclusion, which enlarge the fragment without adding a construct.
   Either way the count is a coverage witness: a change here must enlarge
   the generated fragment rather than only change its proofs. *)
Example accepted_counts : (List.length (accepted 1),
                           List.length (accepted 2),
                           List.length (accepted 3)) = (296, 3695, 43857).
Proof. vm_compute. reflexivity. Qed.
