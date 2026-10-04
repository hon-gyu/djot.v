open Inline
open InlineTable
open Step

type options = { o_inline : dtable; o_list_interrupts : bool;
                 o_setext : bool; o_tables : bool;
                 o_heading_continuation : bool; o_divs : bool;
                 o_tasks : bool; o_raw_blocks : bool; o_deflists : bool;
                 o_block_attrs : bool; o_keyed : bool; o_callouts : bool }

val bconfig_of : options -> bconfig

val djot_options : options

val markdown_like_options : options
