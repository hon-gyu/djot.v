open Inline
open InlineTable
open Step

type profile = { profile_inline : dtable; profile_block : bconfig }

(** val with_footnotes : bool -> profile -> profile **)

let with_footnotes enabled p =
  let t = p.profile_inline in
  { profile_inline = (with_inline_footnotes enabled t); profile_block =
  (with_block_footnotes enabled p.profile_block) }

(** val djot_profile : profile **)

let djot_profile =
  { profile_inline = djot_table; profile_block = djot_bconfig }

(** val markdown_like_profile : profile **)

let markdown_like_profile =
  { profile_inline = markdown_like_table; profile_block =
    markdown_like_bconfig }
