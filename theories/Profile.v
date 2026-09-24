(* ai-disclosure: autonomous *)

(** * Composable syntax profiles

   A profile is a reviewed pairing of the independently customizable inline
   and block configurations.  It is intentionally not an enum: callers may
   start from a named profile, update either fine-grained configuration, and
   bundle the result again.

   [djot_profile] is the compatibility baseline. [markdown_like_profile] is
   djot with Markdown spellings added, not a claim of full CommonMark or GFM
   compatibility. *)

From Stdlib Require Import String.
From DjotV Require Import Ast Inline Step Parser Document.

Record profile : Type := Profile {
  profile_inline : dtable;
  profile_block : bconfig
}.

Definition with_inline_profile (T : dtable) (P : profile) : profile :=
  Profile T (profile_block P).

Definition with_block_profile (K : bconfig) (P : profile) : profile :=
  Profile (profile_inline P) K.

(** The one capability that spans both layers. A footnote reference and a
   footnote definition are two halves of one construct, and neither
   record can name the other's field, so this is where they move
   together.  The half-knobs stay exported for a caller who really means
   one of them. *)
Definition with_footnotes (enabled : bool) (P : profile) : profile :=
  let T := profile_inline P in
  Profile
    (DTable (with_inline_footnotes enabled (@cfg T))
       (with_inline_footnotes_preserves_admissible enabled (@cfg T) (@cfg_ok T)))
    (with_block_footnotes enabled (profile_block P)).

Definition djot_profile : profile :=
  Profile djot_table djot_bconfig.

(** Markdown-like, not CommonMark or GFM: djot with strong spelled `**`,
   setext headings, sublists without a blank line, and one-line ATX
   headings.  Every djot construct stays available; each setting is a
   starting point that [with_inline_profile] and [with_block_profile]
   can change. *)
Definition markdown_like_profile : profile :=
  Profile markdown_like_table markdown_like_bconfig.

Definition parse_profile_blocks (P : profile) (s : string) : blocks :=
  @parse_blocks (profile_inline P) (profile_block P) _ _ s.

Definition parse_profile_doc (P : profile) (s : string) : doc :=
  @parse_doc (profile_inline P) (profile_block P) _ s.
