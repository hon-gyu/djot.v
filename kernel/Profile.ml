open Inline
open InlineTable
open Step

type options = { o_inline : dtable; o_list_interrupts : bool;
                 o_setext : bool; o_tables : bool;
                 o_heading_continuation : bool; o_divs : bool;
                 o_tasks : bool; o_raw_blocks : bool; o_deflists : bool;
                 o_block_attrs : bool; o_keyed : bool; o_callouts : bool }

(** val bconfig_of : options -> bconfig **)

let bconfig_of o =
  let c = o.o_inline in
  { bmarker_interrupts =
  (if o.o_list_interrupts then prose_safe_markers else no_interrupt);
  bunderline = (if o.o_setext then setext_underline else no_underline);
  btables = o.o_tables; bheading_continues = o.o_heading_continuation; bdivs =
  o.o_divs; btasks = o.o_tasks; braw_blocks = o.o_raw_blocks; bdeflists =
  o.o_deflists; battrs = o.o_block_attrs; bfootnotes = c.dc_footnotes;
  bkeyed = o.o_keyed; bcallouts = o.o_callouts; bdiv_names = c.dc_tags }

(** val djot_options : options **)

let djot_options =
  { o_inline = djot_table; o_list_interrupts = false; o_setext = false;
    o_tables = true; o_heading_continuation = true; o_divs = true; o_tasks =
    true; o_raw_blocks = true; o_deflists = true; o_block_attrs = true;
    o_keyed = false; o_callouts = false }

(** val markdown_like_options : options **)

let markdown_like_options =
  { o_inline = markdown_like_table; o_list_interrupts = true; o_setext = true;
    o_tables = true; o_heading_continuation = false; o_divs = true; o_tasks =
    true; o_raw_blocks = true; o_deflists = true; o_block_attrs = true;
    o_keyed = false; o_callouts = false }
