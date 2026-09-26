open Inline
open InlineTable
open Step

type profile = { profile_inline : dtable; profile_block : bconfig }

val with_footnotes : bool -> profile -> profile

val djot_profile : profile

val markdown_like_profile : profile
