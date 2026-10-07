open Inline
open InlineTable
open Profile

(** val block : bool -> bool -> bool -> bool -> options **)

let block list_interrupts setext keyed callouts0 =
  { o_inline = djot_table; o_list_interrupts = list_interrupts; o_setext =
    setext; o_tables = true; o_heading_continuation = true; o_divs = true;
    o_tasks = true; o_raw_blocks = true; o_deflists = true; o_block_attrs =
    true; o_keyed = keyed; o_callouts = callouts0 }

(** val inline : dtable -> options **)

let inline t =
  { o_inline = t; o_list_interrupts = false; o_setext = false; o_tables =
    true; o_heading_continuation = true; o_divs = true; o_tasks = true;
    o_raw_blocks = true; o_deflists = true; o_block_attrs = true; o_keyed =
    false; o_callouts = false }

(** val wikilinks : options **)

let wikilinks =
  inline (with_wikilinks true djot_config)

(** val dollar_math : options **)

let dollar_math =
  inline (with_dollar_math true djot_config)

(** val custom_tags : options **)

let custom_tags =
  inline (with_inline_tags true djot_config)

(** val holes : options **)

let holes =
  inline (with_holes true djot_config)

(** val list_interruption : options **)

let list_interruption =
  block true false false false

(** val setext_headings : options **)

let setext_headings =
  block false true false false

(** val keyed_blocks : options **)

let keyed_blocks =
  block false false true false

(** val callouts : options **)

let callouts =
  block false false false true

(** val all : (string * options) list **)

let all =
  ("callouts", callouts) :: (("custom-tags", custom_tags) :: (("dollar-math",
    dollar_math) :: (("holes", holes) :: (("keyed-blocks",
    keyed_blocks) :: (("list-interruption",
    list_interruption) :: (("setext-headings",
    setext_headings) :: (("wikilinks", wikilinks) :: [])))))))
