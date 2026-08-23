(* ai-disclosure: autonomous *)

(* A profile is a reviewed pairing of the independently customizable inline
   and block configurations.  It is intentionally not an enum: callers may
   start from a named profile, update either fine-grained configuration, and
   bundle the result again. *)

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

Definition djot_profile : profile :=
  Profile djot_table djot_bconfig.

(* This remains deliberately "Markdown-like": Djot-only constructs are being
   removed capability by capability, and GFM tables do not yet exist. *)
Definition markdown_like_profile : profile :=
  Profile markdown_like_table markdown_bconfig.

Definition parse_profile_blocks (P : profile) (s : string) : blocks :=
  @parse_blocks (profile_inline P) (profile_block P) s.

Definition parse_profile_doc (P : profile) (s : string) : doc :=
  @parse_doc (profile_inline P) (profile_block P) s.
