open Ast
open Attributes
open Datatypes
open InlineLocated
open InlineScan
open InlineTable
open Line
open List0
open ListDef
open Marker
open Nat0
open Strings

type bconfig = { bmarker_interrupts : (lstyle list -> string -> task_marker
                                      option -> string -> bool);
                 bunderline : (char -> int -> int option); btables :
                 bool; bheading_continues : bool; bdivs : bool;
                 btasks : bool; braw_blocks : bool; bdeflists : bool;
                 battrs : bool; bfootnotes : bool; bkeyed : bool;
                 bcallouts : bool }

type coq_LineIx = int
  (* singleton inductive, whose constructor was LineIxAt *)

(** val semantic_line_ix : coq_LineIx **)

let semantic_line_ix =
  0

(** val no_interrupt :
    lstyle list -> string -> task_marker option -> string -> bool **)

let no_interrupt _ _ _ _ =
  false

(** val no_underline : char -> int -> int option **)

let no_underline _ _ =
  None

(** val prose_safe_markers :
    lstyle list -> string -> task_marker option -> string -> bool **)

let prose_safe_markers _ core _ _ =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> true)
    (fun _ _ -> (=) core "1")
    core

(** val setext_underline : char -> int -> int option **)

let setext_underline c n =
  if (=) c '='
  then Some 0
  else if (=) c '-'
       then if ( <= ) (Stdlib.succ (Stdlib.succ 0)) n
            then Some (Stdlib.succ 0)
            else None
       else None

(** val djot_bconfig : bconfig **)

let djot_bconfig =
  { bmarker_interrupts = no_interrupt; bunderline = no_underline; btables =
    true; bheading_continues = true; bdivs = true; btasks = true;
    braw_blocks = true; bdeflists = true; battrs = true; bfootnotes = true;
    bkeyed = false; bcallouts = false }

(** val with_marker_interrupts :
    (lstyle list -> string -> task_marker option -> string -> bool) ->
    bconfig -> bconfig **)

let with_marker_interrupts f k =
  { bmarker_interrupts = f; bunderline = k.bunderline; btables = k.btables;
    bheading_continues = k.bheading_continues; bdivs = k.bdivs; btasks =
    k.btasks; braw_blocks = k.braw_blocks; bdeflists = k.bdeflists; battrs =
    k.battrs; bfootnotes = k.bfootnotes; bkeyed = k.bkeyed; bcallouts =
    k.bcallouts }

(** val with_underline : (char -> int -> int option) -> bconfig -> bconfig **)

let with_underline f k =
  { bmarker_interrupts = k.bmarker_interrupts; bunderline = f; btables =
    k.btables; bheading_continues = k.bheading_continues; bdivs = k.bdivs;
    btasks = k.btasks; braw_blocks = k.braw_blocks; bdeflists = k.bdeflists;
    battrs = k.battrs; bfootnotes = k.bfootnotes; bkeyed = k.bkeyed;
    bcallouts = k.bcallouts }

(** val with_tables : bool -> bconfig -> bconfig **)

let with_tables enabled k =
  { bmarker_interrupts = k.bmarker_interrupts; bunderline = k.bunderline;
    btables = enabled; bheading_continues = k.bheading_continues; bdivs =
    k.bdivs; btasks = k.btasks; braw_blocks = k.braw_blocks; bdeflists =
    k.bdeflists; battrs = k.battrs; bfootnotes = k.bfootnotes; bkeyed =
    k.bkeyed; bcallouts = k.bcallouts }

(** val with_heading_continuation : bool -> bconfig -> bconfig **)

let with_heading_continuation enabled k =
  { bmarker_interrupts = k.bmarker_interrupts; bunderline = k.bunderline;
    btables = k.btables; bheading_continues = enabled; bdivs = k.bdivs;
    btasks = k.btasks; braw_blocks = k.braw_blocks; bdeflists = k.bdeflists;
    battrs = k.battrs; bfootnotes = k.bfootnotes; bkeyed = k.bkeyed;
    bcallouts = k.bcallouts }

(** val with_divs : bool -> bconfig -> bconfig **)

let with_divs enabled k =
  { bmarker_interrupts = k.bmarker_interrupts; bunderline = k.bunderline;
    btables = k.btables; bheading_continues = k.bheading_continues; bdivs =
    enabled; btasks = k.btasks; braw_blocks = k.braw_blocks; bdeflists =
    k.bdeflists; battrs = k.battrs; bfootnotes = k.bfootnotes; bkeyed =
    k.bkeyed; bcallouts = k.bcallouts }

(** val with_tasks : bool -> bconfig -> bconfig **)

let with_tasks enabled k =
  { bmarker_interrupts = k.bmarker_interrupts; bunderline = k.bunderline;
    btables = k.btables; bheading_continues = k.bheading_continues; bdivs =
    k.bdivs; btasks = enabled; braw_blocks = k.braw_blocks; bdeflists =
    k.bdeflists; battrs = k.battrs; bfootnotes = k.bfootnotes; bkeyed =
    k.bkeyed; bcallouts = k.bcallouts }

(** val with_raw_blocks : bool -> bconfig -> bconfig **)

let with_raw_blocks enabled k =
  { bmarker_interrupts = k.bmarker_interrupts; bunderline = k.bunderline;
    btables = k.btables; bheading_continues = k.bheading_continues; bdivs =
    k.bdivs; btasks = k.btasks; braw_blocks = enabled; bdeflists =
    k.bdeflists; battrs = k.battrs; bfootnotes = k.bfootnotes; bkeyed =
    k.bkeyed; bcallouts = k.bcallouts }

(** val with_deflists : bool -> bconfig -> bconfig **)

let with_deflists enabled k =
  { bmarker_interrupts = k.bmarker_interrupts; bunderline = k.bunderline;
    btables = k.btables; bheading_continues = k.bheading_continues; bdivs =
    k.bdivs; btasks = k.btasks; braw_blocks = k.braw_blocks; bdeflists =
    enabled; battrs = k.battrs; bfootnotes = k.bfootnotes; bkeyed = k.bkeyed;
    bcallouts = k.bcallouts }

(** val with_block_attrs : bool -> bconfig -> bconfig **)

let with_block_attrs enabled k =
  { bmarker_interrupts = k.bmarker_interrupts; bunderline = k.bunderline;
    btables = k.btables; bheading_continues = k.bheading_continues; bdivs =
    k.bdivs; btasks = k.btasks; braw_blocks = k.braw_blocks; bdeflists =
    k.bdeflists; battrs = enabled; bfootnotes = k.bfootnotes; bkeyed =
    k.bkeyed; bcallouts = k.bcallouts }

(** val with_block_footnotes : bool -> bconfig -> bconfig **)

let with_block_footnotes enabled k =
  { bmarker_interrupts = k.bmarker_interrupts; bunderline = k.bunderline;
    btables = k.btables; bheading_continues = k.bheading_continues; bdivs =
    k.bdivs; btasks = k.btasks; braw_blocks = k.braw_blocks; bdeflists =
    k.bdeflists; battrs = k.battrs; bfootnotes = enabled; bkeyed = k.bkeyed;
    bcallouts = k.bcallouts }

(** val with_keyed : bool -> bconfig -> bconfig **)

let with_keyed enabled k =
  { bmarker_interrupts = k.bmarker_interrupts; bunderline = k.bunderline;
    btables = k.btables; bheading_continues = k.bheading_continues; bdivs =
    k.bdivs; btasks = k.btasks; braw_blocks = k.braw_blocks; bdeflists =
    k.bdeflists; battrs = k.battrs; bfootnotes = k.bfootnotes; bkeyed =
    enabled; bcallouts = k.bcallouts }

(** val with_callouts : bool -> bconfig -> bconfig **)

let with_callouts enabled k =
  { bmarker_interrupts = k.bmarker_interrupts; bunderline = k.bunderline;
    btables = k.btables; bheading_continues = k.bheading_continues; bdivs =
    k.bdivs; btasks = k.btasks; braw_blocks = k.braw_blocks; bdeflists =
    k.bdeflists; battrs = k.battrs; bfootnotes = k.bfootnotes; bkeyed =
    k.bkeyed; bcallouts = enabled }

(** val keyed_bconfig : bconfig **)

let keyed_bconfig =
  with_keyed true djot_bconfig

(** val markdown_like_bconfig : bconfig **)

let markdown_like_bconfig =
  with_heading_continuation false
    (with_underline setext_underline
      (with_marker_interrupts prose_safe_markers djot_bconfig))

(** val configured_list_styles :
    bconfig -> lstyle list -> task_marker option -> lstyle list **)

let configured_list_styles h sty chk =
  if h.btasks
  then sty
  else (match sty with
        | [] -> sty
        | l :: l0 ->
          (match l with
           | STask c ->
             (match l0 with
              | [] ->
                (match chk with
                 | Some _ -> (SBullet c) :: []
                 | None -> sty)
              | _ :: _ -> sty)
           | _ -> sty))

(** val configured_list_check :
    bconfig -> task_marker option -> task_status **)

let configured_list_check h chk =
  if h.btasks
  then (match chk with
        | Some m -> m.tm_status
        | None -> Incomplete)
  else Incomplete

(** val configured_list_rest :
    bconfig -> task_marker option -> string -> string **)

let configured_list_rest h chk rest =
  if h.btasks
  then rest
  else (match chk with
        | Some m -> (^) (task_marker_source m) rest
        | None -> rest)

(** val binterrupt : bconfig -> line_kind -> bool **)

let binterrupt h = function
| KList (sty, core, chk, rest) ->
  h.bmarker_interrupts (configured_list_styles h sty chk) core
    (if h.btasks then chk else None) (configured_list_rest h chk rest)
| _ -> false

(** val bunderline_of : bconfig -> string -> int option **)

let bunderline_of h l =
  match underline_of l with
  | Some p -> let (c, n) = p in h.bunderline c n
  | None -> None

(** val bcuts : bconfig -> string -> bool **)

let bcuts h l =
  match bunderline_of h l with
  | Some _ -> true
  | None -> binterrupt h (classify l)

type stored_line = int * string

(** val remember_line : coq_LineIx -> string -> stored_line **)

let remember_line lI s =
  (lI, s)

(** val line_texts : stored_line list -> string list **)

let line_texts lines =
  map snd lines

type extent = { extent_start : spot; extent_stop : spot }

(** val spot_at : coq_LineIx -> string -> int -> spot **)

let spot_at lI l column =
  { spot_line = lI; spot_rem = (sub (String.length l) column) }

(** val line_stop : coq_LineIx -> spot **)

let line_stop lI =
  { spot_line = lI; spot_rem = 0 }

(** val line_span_from : coq_LineIx -> string -> int -> span **)

let line_span_from lI l column =
  { span_start = (spot_at lI l column); span_stop = (line_stop lI) }

(** val open_extent : coq_LineIx -> string -> int -> extent **)

let open_extent lI l column =
  { extent_start = (spot_at lI l column); extent_stop = (line_stop lI) }

(** val touch_extent : coq_LineIx -> extent -> extent **)

let touch_extent lI e =
  { extent_start = e.extent_start; extent_stop = (line_stop lI) }

(** val extent_span : extent -> span **)

let extent_span e =
  { span_start = e.extent_start; span_stop = e.extent_stop }

(** val stored_start : stored_line -> spot **)

let stored_start sl =
  { spot_line = (fst sl); spot_rem = (String.length (snd sl)) }

(** val stored_stop : stored_line -> spot **)

let stored_stop sl =
  { spot_line = (fst sl); spot_rem = 0 }

(** val stored_span : stored_line list -> span **)

let stored_span cur = match cur with
| [] ->
  { span_start = { spot_line = 0; spot_rem = 0 }; span_stop = { spot_line =
    0; spot_rem = 0 } }
| newest :: _ ->
  { span_start = (stored_start (last cur newest)); span_stop =
    (stored_stop newest) }

(** val span_through_line : coq_LineIx -> span -> span **)

let span_through_line lI r =
  { span_start = r.span_start; span_stop = (line_stop lI) }

(** val fence_block : bconfig -> fence -> string list -> block node **)

let fence_block k f content =
  let text = join_nl content in
  ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

     (fun _ -> mk (CodeBlock ("", text)))
     (fun a fmt ->
     (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
       (fun b b0 b1 b2 b3 b4 b5 b6 ->
       if b
       then if b0
            then mk (CodeBlock
                   (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                   (((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
                   (true, true, b1, b2, b3, b4, b5, b6)), fmt)), text))
            else if b1
                 then if b2
                      then if b3
                           then if b4
                                then if b5
                                     then mk (CodeBlock
                                            (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                                            (((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
                                            (true, false, true, true, true,
                                            true, true, b6)), fmt)), text))
                                     else if b6
                                          then mk (CodeBlock
                                                 (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                                                 ('\189', fmt)), text))
                                          else if k.braw_blocks
                                               then mk (RawBlock (fmt, text))
                                               else mk (CodeBlock
                                                      (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                                                      ('=', fmt)), text))
                                else mk (CodeBlock
                                       (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                                       (((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
                                       (true, false, true, true, true, false,
                                       b5, b6)), fmt)), text))
                           else mk (CodeBlock
                                  (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                                  (((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
                                  (true, false, true, true, false, b4, b5,
                                  b6)), fmt)), text))
                      else mk (CodeBlock
                             (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                             (((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
                             (true, false, true, false, b3, b4, b5, b6)),
                             fmt)), text))
                 else mk (CodeBlock
                        (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                        (((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
                        (true, false, false, b2, b3, b4, b5, b6)), fmt)),
                        text))
       else mk (CodeBlock
              (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

              (((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
              (false, b0, b1, b2, b3, b4, b5, b6)), fmt)), text)))
       a)
     f.f_info)

(** val cells_of :
    dtable -> cell_type -> align list -> string list -> cell list **)

let rec cells_of t ct aligns = function
| [] -> []
| c :: cs' ->
  (match aligns with
   | [] ->
     (Cell (ct, AlignDefault,
       (parse_inline_line t c))) :: (cells_of t ct [] cs')
   | a :: als ->
     (Cell (ct, a, (parse_inline_line t c))) :: (cells_of t ct als cs'))

(** val head_of : align list -> cell list -> cell list **)

let rec head_of aligns = function
| [] -> []
| c :: r' ->
  let Cell (_, _, ils) = c in
  (match aligns with
   | [] -> (Cell (HeadCell, AlignDefault, ils)) :: (head_of [] r')
   | a :: als -> (Cell (HeadCell, a, ils)) :: (head_of als r'))

(** val table_fold :
    dtable -> trow list -> align list -> cell list list -> cell list list **)

let rec table_fold t rows aligns acc =
  match rows with
  | [] -> rev acc
  | t0 :: rest ->
    (match t0 with
     | TSep als ->
       table_fold t rest als
         (match acc with
          | [] -> []
          | r :: acc' -> (head_of als r) :: acc')
     | TCells cs ->
       table_fold t rest aligns ((cells_of t BodyCell aligns cs) :: acc))

type cell_part = { cell_range : span; cell_text_start : spot }

type row_part = span * cell_part list

type tcap =
| TOpen of row_part list
| TAfterBlank of row_part list
| TCaption of row_part list * spot * stored_line list

(** val caption_of : dtable -> coq_PosPolicy -> tcap -> inlines option **)

let caption_of t p = function
| TCaption (_, _, ls) ->
  let ils = para_inlines_at t p 0 (rev ls) in
  if nonempty ils then Some ils else None
| _ -> None

(** val cap_row_parts : tcap -> row_part list **)

let cap_row_parts = function
| TOpen rs -> rs
| TAfterBlank rs -> rs
| TCaption (rs, _, _) -> rs

(** val table_parts : dtable -> coq_PosPolicy -> tcap -> parts **)

let table_parts t p c =
  let caption =
    match c with
    | TOpen _ -> None
    | TAfterBlank _ -> None
    | TCaption (row_parts, start, ls) ->
      (match caption_of t p (TCaption (row_parts, start, ls)) with
       | Some _ ->
         Some { span_start = start; span_stop =
           (stored_stop (hd (0, "") ls)) }
       | None -> None)
  in
  PTable (caption,
  (map (fun r -> ((fst r), (map (fun c0 -> c0.cell_range) (snd r))))
    (rev (cap_row_parts c))))

(** val cells_of_located :
    dtable -> coq_PosPolicy -> cell_type -> align list -> string list ->
    cell_part list -> cell list **)

let rec cells_of_located t p ct aligns cs parts0 =
  match cs with
  | [] -> []
  | c :: cs' ->
    let al = match aligns with
             | [] -> AlignDefault
             | a :: _ -> a in
    let als = match aligns with
              | [] -> []
              | _ :: als -> als in
    let ils =
      match parts0 with
      | [] -> parse_inline_line t c
      | part :: _ ->
        parse_inline_line_located t p part.cell_text_start.spot_line
          part.cell_text_start.spot_rem c
    in
    let rest = match parts0 with
               | [] -> []
               | _ :: ps -> ps in
    (Cell (ct, al, ils)) :: (cells_of_located t p ct als cs' rest)

(** val table_fold_located :
    dtable -> coq_PosPolicy -> trow list -> row_part list -> align list ->
    cell list list -> cell list list **)

let rec table_fold_located t p rows parts0 aligns acc =
  match rows with
  | [] -> rev acc
  | t0 :: rest ->
    (match t0 with
     | TSep als ->
       table_fold_located t p rest parts0 als
         (match acc with
          | [] -> []
          | r :: acc' -> (head_of als r) :: acc')
     | TCells cs ->
       let cell_parts =
         match parts0 with
         | [] -> []
         | r :: _ -> let (_, ps) = r in ps
       in
       let rest_parts = match parts0 with
                        | [] -> []
                        | _ :: ps -> ps in
       table_fold_located t p rest rest_parts aligns
         ((cells_of_located t p BodyCell aligns cs cell_parts) :: acc))

(** val table_block :
    dtable -> coq_PosPolicy -> trow list -> tcap -> block node **)

let table_block t p rows c =
  mk (Table ((caption_of t p c),
    (if p.pos_records
     then table_fold_located t p rows (rev (cap_row_parts c)) [] []
     else table_fold t rows [] [])))

(** val table_row_part : coq_LineIx -> string -> trow -> row_part option **)

let table_row_part lI l = function
| TSep _ -> None
| TCells _ ->
  (match row_body l with
   | Some body ->
     (match row_cells_trace (row_inner body) 0 0 false "" [] (Stdlib.succ 0) 0 with
      | Some cells ->
        let width = String.length (drop_leading_ws l) in
        let cell_part_of = fun x ->
          let (y, text_start) = x in
          let (y0, b) = y in
          let (_, a) = y0 in
          { cell_range = { span_start = { spot_line = lI; spot_rem =
          (sub width a) }; span_stop = { spot_line = lI; spot_rem =
          (sub width b) } }; cell_text_start = { spot_line = lI; spot_rem =
          (sub width text_start) } }
        in
        Some ({ span_start = { spot_line = lI; spot_rem = width };
        span_stop = { spot_line = lI; spot_rem =
        (sub width (Stdlib.succ (String.length body))) } },
        (map cell_part_of cells))
      | None -> None)
   | None -> None)

type list_state = { ls_indent : int; ls_extent : extent;
                    ls_item_extent : extent; ls_item_extents : extent list;
                    ls_styles : (lstyle * int) list; ls_loose : bool;
                    ls_blanks : bool; ls_items : blocks list;
                    ls_check : task_status; ls_checks : task_status list }

type pstate =
| PPara of stored_line list
| PHeading of int * extent * stored_line list
| PFence of fence * int * extent * span * stored_line list
| PQuote of extent * ((string * callout_fold option) * stored_line) option
   * blocks * pstate
| PDiv of int * string * extent * span * blocks * pstate
| PList of list_state * blocks * pstate
| PAttr of attr * span list * extent * int * aparser * stored_line list
| PParaOff of int * stored_line list
| PRef of extent * int * string * string
| PFoot of extent * int * string * blocks * pstate
| PTable of extent * trow list * tcap
| PPend of attr * span list * pstate
| PKey of extent * string * string * pstate

(** val pstate_depth : pstate -> int **)

let rec pstate_depth = function
| PQuote (_, _, _, inner) -> Stdlib.succ (pstate_depth inner)
| PDiv (_, _, _, _, _, inner) -> Stdlib.succ (pstate_depth inner)
| PList (_, _, inner) -> Stdlib.succ (pstate_depth inner)
| PAttr (_, _, _, _, _, _) -> Stdlib.succ (Stdlib.succ 0)
| PRef (_, _, _, _) -> Stdlib.succ 0
| PFoot (_, _, _, _, inner) -> Stdlib.succ (pstate_depth inner)
| PTable (_, _, _) -> Stdlib.succ 0
| PPend (_, _, inner) -> Stdlib.succ (pstate_depth inner)
| PKey (_, _, _, inner) -> Stdlib.succ (pstate_depth inner)
| _ -> 0

(** val is_idle : pstate -> bool **)

let is_idle = function
| PPara cur -> (match cur with
                | [] -> true
                | _ :: _ -> false)
| _ -> false

(** val heading_block :
    dtable -> coq_PosPolicy -> int -> stored_line list -> block node **)

let heading_block t p lvl cur =
  mk (Heading (lvl, (para_inlines_at t p 0 (rev cur))))

(** val heading_block_off :
    dtable -> coq_PosPolicy -> int -> int -> stored_line list -> block node **)

let heading_block_off t p k lvl cur =
  mk (Heading (lvl, (para_inlines_at t p k (rev cur))))

(** val callout_title : dtable -> coq_PosPolicy -> stored_line -> inlines **)

let callout_title t h = function
| (line, source) ->
  let title = strip_trailing_ws source in
  if h.pos_records
  then parse_inline_line_located t h line (String.length source) title
  else parse_inline_line t title

(** val quote_block :
    dtable -> coq_PosPolicy -> ((string * callout_fold option) * stored_line)
    option -> blocks -> block **)

let quote_block t h header bs =
  match header with
  | Some p ->
    let (p0, source) = p in
    let (kind, fold) = p0 in
    Ext_callout (kind, fold, (callout_title t h source), bs)
  | None -> BlockQuote bs

(** val para_recover : int -> stored_line list -> pstate **)

let para_recover extra slices =
  PParaOff ((( + ) extra (length slices)), slices)

(** val finish_para_recover :
    dtable -> coq_PosPolicy -> stored_line list -> blocks **)

let finish_para_recover t p slices = match slices with
| [] -> []
| _ :: _ ->
  (set_pos p (prov_at (stored_span slices))
    (mk (Para (para_inlines_at t p (length slices) (rev slices))))) :: []

(** val div_block : string -> blocks -> block node **)

let div_block cls bs =
  if (=) cls ""
  then mk (Div bs)
  else Node (NoPos, (("class", cls) :: []), (Div bs))

(** val styles_list :
    bconfig -> (lstyle * int) list -> list_spacing -> blocks list -> block
    node **)

let styles_list k s sp items =
  match s with
  | [] -> mk (BulletList (sp, items))
  | p :: _ ->
    let (l0, start) = p in
    (match l0 with
     | SBullet c ->
       if (&&) ((=) c ':') k.bdeflists
       then mk (DefinitionList (sp, (def_items items)))
       else mk (BulletList (sp, items))
     | STask _ -> mk (BulletList (sp, items))
     | SOrd (n, d) ->
       mk (OrderedList ({ ol_style = n; ol_delim = d; ol_start = start }, sp,
         items)))

(** val styles_list_checked :
    bconfig -> (lstyle * int) list -> list_spacing -> task_status list ->
    blocks list -> block node **)

let styles_list_checked k s sp checks items =
  match s with
  | [] -> styles_list k s sp items
  | p :: _ ->
    let (l0, _) = p in
    (match l0 with
     | STask _ -> mk (TaskList (sp, (task_items checks items)))
     | _ -> styles_list k s sp items)

(** val def_term_span : blocks -> span option **)

let rec def_term_span = function
| [] -> None
| n :: rest ->
  (match node_contents n with
   | Para _ -> option_map (fun p -> p.node_span) (node_provenance n)
   | x -> if invisible_block x then def_term_span rest else None)

(** val blocks_span : blocks -> spot -> span **)

let blocks_span bs fallback =
  match bs with
  | [] -> { span_start = fallback; span_stop = fallback }
  | first :: _ ->
    (match node_provenance first with
     | Some p ->
       (match node_provenance (last bs first) with
        | Some q ->
          { span_start = p.node_span.span_start; span_stop =
            q.node_span.span_stop }
        | None -> { span_start = fallback; span_stop = fallback })
     | None -> { span_start = fallback; span_stop = fallback })

(** val def_item_spans :
    span list -> blocks list -> ((span * span) * span) list **)

let rec def_item_spans ranges items =
  match ranges with
  | [] -> []
  | item :: ranges' ->
    (match items with
     | [] -> []
     | bs :: items' ->
       let term =
         match def_term_span bs with
         | Some r -> r
         | None ->
           { span_start = item.span_start; span_stop = item.span_start }
       in
       let definition = blocks_span (snd (def_item bs)) term.span_stop in
       ((item, term), definition) :: (def_item_spans ranges' items'))

(** val list_parts : bconfig -> list_state -> blocks -> parts **)

let list_parts k ls last0 =
  let ranges = map extent_span (rev (ls.ls_item_extent :: ls.ls_item_extents))
  in
  (match ls.ls_styles with
   | [] -> PItems ranges
   | p :: _ ->
     let (l0, _) = p in
     (match l0 with
      | SBullet c ->
        if (&&) ((=) c ':') k.bdeflists
        then PDefItems (def_item_spans ranges (rev (last0 :: ls.ls_items)))
        else PItems ranges
      | _ -> PItems ranges))

(** val list_block : bconfig -> list_state -> blocks -> block node **)

let list_block k ls last0 =
  styles_list_checked k ls.ls_styles (if ls.ls_loose then Loose else Tight)
    (rev (ls.ls_check :: ls.ls_checks)) (rev (last0 :: ls.ls_items))

(** val ref_block : string -> string -> block node **)

let ref_block lbl val0 =
  mk (RefDef (lbl, val0))

(** val foot_block : string -> blocks -> block node **)

let foot_block lbl bs =
  mk (FootnoteDef (lbl, bs))

(** val key_label : dtable -> coq_PosPolicy -> spot -> string -> inlines **)

let key_label t p start lbl =
  if p.pos_records
  then parse_inline_line_located t p start.spot_line start.spot_rem
         (strip_trailing_ws lbl)
  else para_inlines t (lbl :: [])

(** val key_close :
    dtable -> coq_PosPolicy -> spot -> string -> string -> blocks -> blocks **)

let key_close t p start lbl src = function
| [] -> (mk (Para (para_inlines t (src :: [])))) :: []
| b :: rest -> (mk (Ext_keyed ((key_label t p start lbl), b))) :: rest

(** val ref_cont : string -> string option **)

let ref_cont l =
  let t = drop_leading_ws l in
  if (&&) (nonempty_str t) (no_ws t) then Some t else None

(** val finish : dtable -> bconfig -> coq_PosPolicy -> pstate -> blocks **)

let rec finish t k p = function
| PPara cur ->
  (match cur with
   | [] -> []
   | _ :: _ ->
     (set_pos p (prov_at (stored_span cur))
       (mk (Para (para_inlines_at t p 0 (rev cur))))) :: [])
| PHeading (lvl, range, cur) ->
  (set_pos p (prov_at (extent_span range)) (heading_block t p lvl cur)) :: []
| PFence (f, _, range, opener, acc) ->
  (set_pos p (prov_with (extent_span range) ((ROpenFence, opener) :: []))
    (fence_block k f (line_texts (rev acc)))) :: []
| PQuote (range, header, done0, inner) ->
  let bs = app (rev done0) (finish t k p inner) in
  (set_pos p (prov_at (extent_span range)) (mk (quote_block t p header bs))) :: []
| PDiv (_, cls, range, opener, done0, inner) ->
  (set_pos p (prov_with (extent_span range) ((ROpenFence, opener) :: []))
    (div_block cls (app (rev done0) (finish t k p inner)))) :: []
| PList (ls, done0, inner) ->
  let last0 = app (rev done0) (finish t k p inner) in
  (set_pos p { node_span = (extent_span ls.ls_extent); syntax_spans = [];
    part_spans = (list_parts k ls last0) } (list_block k ls last0)) :: []
| PAttr (pend, specs, _, _, ap, slices) ->
  if ap_done ap
  then []
  else add_roles_head p (attr_roles specs)
         (decorate_head pend (finish_para_recover t p slices))
| PParaOff (k0, cur) ->
  (set_pos p (prov_at (stored_span cur))
    (mk (Para (para_inlines_at t p k0 (rev cur))))) :: []
| PRef (range, _, lbl, val0) ->
  (set_pos p (prov_at (extent_span range)) (ref_block lbl val0)) :: []
| PFoot (range, _, lbl, done0, inner) ->
  (set_pos p (prov_at (extent_span range))
    (foot_block lbl (app (rev done0) (finish t k p inner)))) :: []
| PTable (range, rows, cap) ->
  (set_pos p { node_span = (extent_span range); syntax_spans = [];
    part_spans = (table_parts t p cap) } (table_block t p (rev rows) cap)) :: []
| PPend (pend, specs, inner) ->
  add_roles_head p (attr_roles specs)
    (decorate_head pend (finish t k p inner))
| PKey (range, lbl, src, inner) ->
  pos_head p (prov_at (extent_span range))
    (key_close t p range.extent_start lbl src (finish t k p inner))

(** val lazy_ok : bconfig -> pstate -> bool **)

let rec lazy_ok k = function
| PPara cur -> (match cur with
                | [] -> false
                | _ :: _ -> true)
| PHeading (_, _, _) -> k.bheading_continues
| PQuote (_, _, _, inner) -> lazy_ok k inner
| PDiv (_, _, _, _, _, inner) -> lazy_ok k inner
| PList (_, _, inner) -> lazy_ok k inner
| PParaOff (_, _) -> true
| PFoot (_, _, _, _, inner) -> lazy_ok k inner
| PPend (_, _, inner) -> lazy_ok k inner
| PKey (_, _, _, inner) -> lazy_ok k inner
| _ -> false

(** val in_fence : pstate -> bool **)

let rec in_fence = function
| PFence (_, _, _, _, _) -> true
| PQuote (_, _, _, inner) -> in_fence inner
| PDiv (_, _, _, _, _, inner) -> in_fence inner
| PList (_, _, inner) -> in_fence inner
| PFoot (_, _, _, _, inner) -> in_fence inner
| PPend (_, _, inner) -> in_fence inner
| PKey (_, _, _, inner) -> in_fence inner
| _ -> false

(** val is_lazy : bconfig -> line_kind -> pstate -> bool **)

let is_lazy k k0 inner =
  match k0 with
  | KText -> lazy_ok k inner
  | _ -> false

(** val list_content :
    coq_LineIx -> list_state -> line_kind -> bool -> list_state **)

let list_content lI ls k kept =
  let loose =
    match k with
    | KList (_, _, _, _) -> ls.ls_loose
    | _ -> if kept then ls.ls_loose else (||) ls.ls_loose ls.ls_blanks
  in
  { ls_indent = ls.ls_indent; ls_extent = (touch_extent lI ls.ls_extent);
  ls_item_extent = (touch_extent lI ls.ls_item_extent); ls_item_extents =
  ls.ls_item_extents; ls_styles = ls.ls_styles; ls_loose = loose; ls_blanks =
  false; ls_items = ls.ls_items; ls_check = ls.ls_check; ls_checks =
  ls.ls_checks }

(** val feed_lazy : coq_LineIx -> string -> pstate -> pstate **)

let rec feed_lazy lI l st = match st with
| PPara cur -> PPara ((remember_line lI (drop_leading_ws l)) :: cur)
| PHeading (lvl, range, cur) ->
  PHeading (lvl, (touch_extent lI range),
    ((remember_line lI (drop_leading_ws l)) :: cur))
| PFence (f, ind, range, opener, acc) -> PFence (f, ind, range, opener, acc)
| PQuote (range, header, done0, inner) ->
  PQuote ((touch_extent lI range), header, done0, (feed_lazy lI l inner))
| PDiv (len, cls, range, opener, done0, inner) ->
  PDiv (len, cls, (touch_extent lI range), opener, done0,
    (feed_lazy lI l inner))
| PList (ls, done0, inner) ->
  PList ((list_content lI ls KText false), done0, (feed_lazy lI l inner))
| PParaOff (k, cur) ->
  PParaOff (k, ((remember_line lI (drop_leading_ws l)) :: cur))
| PFoot (range, ind, lbl, done0, inner) ->
  PFoot ((touch_extent lI range), ind, lbl, done0, (feed_lazy lI l inner))
| PPend (pend, specs, inner) -> PPend (pend, specs, (feed_lazy lI l inner))
| PKey (range, lbl, src, inner) ->
  PKey ((touch_extent lI range), lbl, src, (feed_lazy lI l inner))
| _ -> st

(** val push_text :
    coq_LineIx -> string -> stored_line list -> stored_line list **)

let push_text lI rest cur =
  if is_blank rest
  then cur
  else (remember_line lI (drop_leading_ws rest)) :: cur

(** val open_text :
    dtable -> coq_LineIx -> bconfig -> string -> blocks * pstate **)

let open_text t lI h t0 =
  match if h.bkeyed then key_split t t0 else None with
  | Some p ->
    let (lbl, v) = p in
    ([], (PKey ((open_extent lI t0 0), lbl, t0, (PPara (push_text lI v [])))))
  | None -> ([], (PPara ((remember_line lI t0) :: [])))

(** val keyless : dtable -> bconfig -> string -> bool **)

let keyless t h l =
  match if h.bkeyed then key_split t l else None with
  | Some _ -> false
  | None -> true

(** val open_kind :
    dtable -> coq_LineIx -> coq_PosPolicy -> bconfig -> string -> line_kind
    -> blocks * pstate **)

let open_kind t lI p h l = function
| KThematic ->
  (((posnode p (prov_at (line_span_from lI l (indent_of l))) ThematicBreak) :: []),
    (PPara []))
| KDiv (len, cls) ->
  if h.bdivs
  then ([], (PDiv (len, cls, (open_extent lI l (indent_of l)),
         (line_span_from lI l (indent_of l)), [], (PPara []))))
  else ([], (PPara ((remember_line lI (drop_leading_ws l)) :: [])))
| KHeading (lvl, rest) ->
  ([], (PHeading (lvl, (open_extent lI l (indent_of l)),
    (push_text lI rest []))))
| KRow r ->
  if h.btables
  then ([], (PTable ((open_extent lI l (indent_of l)), (r :: []), (TOpen
         (if p.pos_records
          then (match table_row_part lI l r with
                | Some p0 -> p0 :: []
                | None -> [])
          else [])))))
  else ([], (PPara ((remember_line lI (drop_leading_ws l)) :: [])))
| KText -> open_text t lI h (drop_leading_ws l)
| _ -> ([], (PPara []))

(** val close_reopen :
    dtable -> bconfig -> coq_PosPolicy -> pstate -> (blocks * pstate) ->
    blocks * pstate **)

let close_reopen t k p st = function
| (bs, st') -> ((app (finish t k p st) bs), st')

(** val pend_result :
    coq_PosPolicy -> attr -> span list -> (blocks * pstate) -> blocks * pstate **)

let pend_result p pend specs = function
| (bs, st') ->
  (match bs with
   | [] -> ([], (PPend (pend, specs, st')))
   | _ :: _ ->
     ((add_roles_head p (attr_roles specs) (decorate_head pend bs)), st'))

(** val key_result :
    dtable -> coq_PosPolicy -> extent -> string -> string ->
    (blocks * pstate) -> blocks * pstate **)

let key_result t p range lbl src = function
| (bs, st') ->
  (match bs with
   | [] -> ([], (PKey (range, lbl, src, st')))
   | _ :: _ ->
     ((pos_head p (prov_at (extent_span range))
        (key_close t p range.extent_start lbl src bs)),
       st'))

(** val open_quote :
    coq_LineIx -> string -> (blocks * pstate) -> blocks * pstate **)

let open_quote lI l = function
| (bs, inner) ->
  ([], (PQuote ((open_extent lI l (indent_of l)), None, (rev bs), inner)))

(** val quote_header :
    bconfig -> string -> ((string * callout_fold option) * string) option **)

let quote_header k rest =
  if k.bcallouts then callout_header rest else None

(** val open_callout :
    coq_LineIx -> string -> string -> callout_fold option -> string ->
    blocks * pstate **)

let open_callout lI l kind fold title =
  ([], (PQuote ((open_extent lI l (indent_of l)), (Some ((kind, fold),
    (remember_line lI title))), [], (PPara []))))

(** val open_attr :
    bconfig -> coq_LineIx -> attr -> span list -> int -> aparser -> string ->
    blocks * pstate **)

let open_attr k lI pend specs ind ap l =
  if k.battrs
  then ([], (PAttr (pend, specs, (open_extent lI l (indent_of l)), ind, ap,
         ((remember_line lI (drop_leading_ws l)) :: []))))
  else ([], (PPara ((remember_line lI (drop_leading_ws l)) :: [])))

(** val open_fence :
    coq_LineIx -> string -> int -> fence -> blocks * pstate **)

let open_fence lI l ind f =
  let col = indent_of l in
  ([], (PFence (f, ind, (open_extent lI l col), (line_span_from lI l col),
  [])))

(** val open_ref :
    coq_LineIx -> string -> int -> string -> string -> blocks * pstate **)

let open_ref lI l ind lbl val0 =
  ([], (PRef ((open_extent lI l (indent_of l)), ind, lbl, val0)))

(** val open_foot :
    bconfig -> coq_LineIx -> string -> int -> string -> (blocks * pstate) ->
    blocks * pstate **)

let open_foot k lI l ind lbl descended =
  if k.bfootnotes
  then let (bs, inner) = descended in
       ([], (PFoot ((open_extent lI l (indent_of l)), ind, lbl, (rev bs),
       inner)))
  else ([], (PPara ((remember_line lI (drop_leading_ws l)) :: [])))

(** val list_opened :
    coq_LineIx -> string -> int -> (lstyle * int) list -> task_status ->
    list_state **)

let list_opened lI l ind sty chk =
  let range = open_extent lI l (indent_of l) in
  { ls_indent = ind; ls_extent = range; ls_item_extent = range;
  ls_item_extents = []; ls_styles = sty; ls_loose = false; ls_blanks = false;
  ls_items = []; ls_check = chk; ls_checks = [] }

(** val open_list :
    coq_LineIx -> string -> int -> (lstyle * int) list -> task_status ->
    (blocks * pstate) -> blocks * pstate **)

let open_list lI l ind sty chk = function
| (bs, inner) ->
  ([], (PList ((list_opened lI l ind sty chk), (rev bs), inner)))

(** val list_blank : list_state -> list_state **)

let list_blank ls =
  { ls_indent = ls.ls_indent; ls_extent = ls.ls_extent; ls_item_extent =
    ls.ls_item_extent; ls_item_extents = ls.ls_item_extents; ls_styles =
    ls.ls_styles; ls_loose = ls.ls_loose; ls_blanks = true; ls_items =
    ls.ls_items; ls_check = ls.ls_check; ls_checks = ls.ls_checks }

(** val list_narrow : list_state -> (lstyle * int) list -> list_state **)

let list_narrow ls ns =
  { ls_indent = ls.ls_indent; ls_extent = ls.ls_extent; ls_item_extent =
    ls.ls_item_extent; ls_item_extents = ls.ls_item_extents; ls_styles = ns;
    ls_loose = ls.ls_loose; ls_blanks = ls.ls_blanks; ls_items = ls.ls_items;
    ls_check = ls.ls_check; ls_checks = ls.ls_checks }

(** val announces_end : pstate -> bool **)

let announces_end = function
| PFence (_, _, _, _, _) -> true
| PDiv (_, _, _, _, _, _) -> true
| _ -> false

(** val claimable : line_kind -> bool **)

let claimable = function
| KThematic -> true
| KFence _ -> true
| KDiv (_, _) -> true
| _ -> false

(** val key_claims : string -> pstate -> bool **)

let rec key_claims l = function
| PDiv (_, _, _, _, _, inner) -> key_claims l inner
| PList (_, _, inner) -> key_claims l inner
| PFoot (_, _, _, _, inner) -> key_claims l inner
| PPend (_, _, inner) -> key_claims l inner
| PKey (_, _, _, inner) ->
  if is_idle inner then claimable (classify l) else announces_end inner
| _ -> false

(** val list_takes : list_state -> int -> string -> pstate -> bool **)

let list_takes ls off l inner =
  (||) (key_claims l inner) (( < ) ls.ls_indent (( + ) off (indent_of l)))

(** val blank_held : pstate -> bool **)

let rec blank_held = function
| PFence (_, _, _, _, _) -> true
| PDiv (_, _, _, _, _, inner) -> blank_held inner
| PList (_, _, inner) -> blank_held inner
| PAttr (_, _, _, _, _, _) -> true
| PFoot (_, _, _, _, inner) -> blank_held inner
| PPend (_, _, inner) -> blank_held inner
| PKey (_, _, _, inner) -> (||) (announces_end inner) (blank_held inner)
| _ -> false

(** val blank_absorbed : pstate -> bool **)

let rec blank_absorbed = function
| PFence (_, _, _, _, _) -> true
| PDiv (_, _, _, _, _, inner) -> blank_held inner
| PList (_, _, _) -> true
| PAttr (_, _, _, _, _, _) -> true
| PFoot (_, _, _, _, inner) -> blank_absorbed inner
| PPend (_, _, inner) -> blank_absorbed inner
| PKey (_, _, _, inner) -> (||) (announces_end inner) (blank_absorbed inner)
| _ -> false

(** val keeps_line : bconfig -> int -> string -> pstate -> bool **)

let rec keeps_line k off l = function
| PDiv (_, _, _, _, _, inner) -> negb (lazy_ok k inner)
| PFoot (_, ind, _, _, inner) ->
  (&&) (negb (lazy_ok k inner)) (( < ) ind (( + ) off (indent_of l)))
| PTable (_, _, _) ->
  (match caption_open l with
   | Some _ -> true
   | None -> false)
| PPend (_, _, inner) -> keeps_line k off l inner
| PKey (_, _, _, inner) -> keeps_line k off l inner
| _ -> false

(** val list_next :
    coq_LineIx -> list_state -> blocks -> task_status -> string -> list_state **)

let list_next lI ls item chk l =
  { ls_indent = ls.ls_indent; ls_extent = (touch_extent lI ls.ls_extent);
    ls_item_extent = (open_extent lI l (indent_of l)); ls_item_extents =
    (ls.ls_item_extent :: ls.ls_item_extents); ls_styles = ls.ls_styles;
    ls_loose = ((||) ls.ls_loose ls.ls_blanks); ls_blanks = false; ls_items =
    (item :: ls.ls_items); ls_check = chk; ls_checks =
    (ls.ls_check :: ls.ls_checks) }

(** val consumed : string -> string -> int **)

let consumed l rest =
  sub (String.length l) (String.length rest)

(** val open_line :
    dtable -> bconfig -> coq_LineIx -> coq_PosPolicy -> (string ->
    blocks * pstate) -> int -> string -> line_kind -> blocks * pstate **)

let open_line t k lI p descend ind l k0 = match k0 with
| KFence f -> open_fence lI l ind f
| KQuote rest ->
  (match quote_header k rest with
   | Some p0 ->
     let (p1, title) = p0 in
     let (kind, fold) = p1 in open_callout lI l kind fold title
   | None -> open_quote lI l (descend rest))
| KList (sty, core, chk, rest) ->
  open_list lI l ind (with_starts (configured_list_styles k sty chk) core)
    (configured_list_check k chk) (descend (configured_list_rest k chk rest))
| KAttr ap -> open_attr k lI [] [] ind ap l
| KFoot (lbl, rest) -> open_foot k lI l ind lbl (descend rest)
| KRef (lbl, v) -> open_ref lI l ind lbl v
| _ -> open_kind t lI p k l k0

(** val step_fuel :
    dtable -> bconfig -> coq_LineIx -> coq_PosPolicy -> int -> int -> string
    -> pstate -> blocks * pstate **)

let rec step_fuel t k lI p n off l st =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> ([], st))
    (fun n' ->
    let descend = fun rest ->
      step_fuel t k lI p n' (( + ) off (consumed l rest)) rest (PPara [])
    in
    (match st with
     | PPara cur ->
       (match cur with
        | [] ->
          open_line t k lI p descend (( + ) off (indent_of l)) l (classify l)
        | c :: cur' ->
          (match bunderline_of k l with
           | Some lvl ->
             (((set_pos p
                 (prov_at (span_through_line lI (stored_span (c :: cur'))))
                 (heading_block t p (Stdlib.succ lvl) (c :: cur'))) :: []),
               (PPara []))
           | None ->
             (match classify l with
              | KBlank ->
                close_reopen t k p (PPara (c :: cur'))
                  (open_kind t lI p k l KBlank)
              | x ->
                if binterrupt k x
                then close_reopen t k p (PPara (c :: cur'))
                       (open_line t k lI p descend (( + ) off (indent_of l))
                         l x)
                else ([], (PPara
                       ((remember_line lI (drop_leading_ws l)) :: (c :: cur')))))))
     | PHeading (lvl, range, cur) ->
       (match classify l with
        | KHeading (lvl', rest) ->
          if k.bheading_continues
          then if ( = ) lvl' lvl
               then ([], (PHeading (lvl, (touch_extent lI range),
                      (push_text lI rest cur))))
               else close_reopen t k p (PHeading (lvl, range, cur))
                      (open_kind t lI p k l (KHeading (lvl', rest)))
          else close_reopen t k p (PHeading (lvl, range, cur))
                 (open_kind t lI p k l (KHeading (lvl', rest)))
        | KText ->
          if k.bheading_continues
          then ([], (PHeading (lvl, (touch_extent lI range),
                 ((remember_line lI (drop_leading_ws l)) :: cur))))
          else close_reopen t k p (PHeading (lvl, range, cur))
                 (open_kind t lI p k l KText)
        | x ->
          close_reopen t k p (PHeading (lvl, range, cur))
            (open_line t k lI p descend (( + ) off (indent_of l)) l x))
     | PFence (f, ind, range, opener, acc) ->
       if fence_close f l
       then (((set_pos p
                (prov_with (extent_span (touch_extent lI range))
                  ((ROpenFence, opener) :: ((RCloseFence,
                  (line_span_from lI l (indent_of l))) :: [])))
                (fence_block k f (line_texts (rev acc)))) :: []),
              (PPara []))
       else ([], (PFence (f, ind, (touch_extent lI range), opener,
              ((remember_line lI (drop_ws_upto (sub ind off) l)) :: acc))))
     | PQuote (range, header, done0, inner) ->
       (match classify l with
        | KQuote rest ->
          let (bs, inner') =
            step_fuel t k lI p n' (( + ) off (consumed l rest)) rest inner
          in
          ([], (PQuote ((touch_extent lI range), header,
          (app (rev bs) done0), inner')))
        | x ->
          if is_lazy k x inner
          then ([], (PQuote ((touch_extent lI range), header, done0,
                 (feed_lazy lI l inner))))
          else close_reopen t k p (PQuote (range, header, done0, inner))
                 (open_line t k lI p descend (( + ) off (indent_of l)) l x))
     | PDiv (len, cls, range, opener, done0, inner) ->
       if (&&) (negb (in_fence inner)) (div_close len l)
       then (((set_pos p
                (prov_with (extent_span (touch_extent lI range))
                  ((ROpenFence, opener) :: ((RCloseFence,
                  (line_span_from lI l (indent_of l))) :: [])))
                (div_block cls (app (rev done0) (finish t k p inner)))) :: []),
              (PPara []))
       else let (bs, inner') = step_fuel t k lI p n' off l inner in
            ([], (PDiv (len, cls, (touch_extent lI range), opener,
            (app (rev bs) done0), inner')))
     | PList (ls, done0, inner) ->
       (match classify l with
        | KBlank ->
          let (bs, inner') = step_fuel t k lI p n' off l inner in
          let ls' = if blank_absorbed inner then ls else list_blank ls in
          ([], (PList (ls', (app (rev bs) done0), inner')))
        | x ->
          if list_takes ls off l inner
          then let (bs, inner') = step_fuel t k lI p n' off l inner in
               ([], (PList
               ((list_content lI ls x (keeps_line k off l inner)),
               (app (rev bs) done0), inner')))
          else (match x with
                | KList (sty, core, chk, rest) ->
                  (match narrow ls.ls_styles
                           (configured_list_styles k sty chk) with
                   | [] ->
                     close_reopen t k p (PList (ls, done0, inner))
                       (open_line t k lI p descend (( + ) off (indent_of l))
                         l (KList (sty, core, chk, rest)))
                   | p0 :: l0 ->
                     let item = app (rev done0) (finish t k p inner) in
                     let (bs, inner') =
                       step_fuel t k lI p n'
                         (( + ) off
                           (consumed l (configured_list_rest k chk rest)))
                         (configured_list_rest k chk rest) (PPara [])
                     in
                     ([], (PList
                     ((list_next lI (list_narrow ls (p0 :: l0)) item
                        (configured_list_check k chk) l),
                     (rev bs), inner'))))
                | _ ->
                  if is_lazy k x inner
                  then ([], (PList ((list_content lI ls x false), done0,
                         (feed_lazy lI l inner))))
                  else close_reopen t k p (PList (ls, done0, inner))
                         (open_line t k lI p descend
                           (( + ) off (indent_of l)) l x)))
     | PAttr (pend, specs, range, ind, ap, slices) ->
       if ap_done ap
       then step_fuel t k lI p n' off l (PPend
              ((Attr.merge ap.ap_attrs pend),
              (app specs ((extent_span range) :: [])), (PPara [])))
       else if ( < ) ind (( + ) off (indent_of l))
            then let ap' = attr_feed l ap in
                 if ap_failed ap'
                 then pend_result p pend specs
                        (step_fuel t k lI p n' off l
                          (para_recover (Stdlib.succ 0) slices))
                 else ([], (PAttr (pend, specs, (touch_extent lI range), ind,
                        ap', (push_text lI l slices))))
            else if is_blank l
                 then ([], (PPend (pend, specs, (para_recover 0 slices))))
                 else pend_result p pend specs
                        (step_fuel t k lI p n' off l (para_recover 0 slices))
     | PParaOff (koff, cur) ->
       (match bunderline_of k l with
        | Some lvl ->
          (((set_pos p (prov_at (span_through_line lI (stored_span cur)))
              (heading_block_off t p koff (Stdlib.succ lvl) cur)) :: []),
            (PPara []))
        | None ->
          (match classify l with
           | KBlank ->
             close_reopen t k p (PParaOff (koff, cur))
               (open_kind t lI p k l KBlank)
           | x ->
             if binterrupt k x
             then close_reopen t k p (PParaOff (koff, cur))
                    (open_line t k lI p descend (( + ) off (indent_of l)) l x)
             else ([], (PParaOff (koff,
                    ((remember_line lI (drop_leading_ws l)) :: cur))))))
     | PRef (range, ind, lbl, val0) ->
       (match if ( < ) ind (( + ) off (indent_of l)) then ref_cont l else None with
        | Some t0 ->
          ([], (PRef ((touch_extent lI range), ind, lbl, ((^) val0 t0))))
        | None ->
          let (bs, st') = step_fuel t k lI p n' off l (PPara []) in
          (((set_pos p (prov_at (extent_span range)) (ref_block lbl val0)) :: bs),
          st'))
     | PFoot (range, ind, lbl, done0, inner) ->
       if is_blank l
       then let (bs, inner') = step_fuel t k lI p n' off l inner in
            ([], (PFoot ((touch_extent lI range), ind, lbl,
            (app (rev bs) done0), inner')))
       else if ( < ) ind (( + ) off (indent_of l))
            then let (bs, inner') = step_fuel t k lI p n' off l inner in
                 ([], (PFoot ((touch_extent lI range), ind, lbl,
                 (app (rev bs) done0), inner')))
            else if is_lazy k (classify l) inner
                 then ([], (PFoot ((touch_extent lI range), ind, lbl, done0,
                        (feed_lazy lI l inner))))
                 else let (bs, st') = step_fuel t k lI p n' off l (PPara [])
                      in
                      (((set_pos p (prov_at (extent_span range))
                          (foot_block lbl
                            (app (rev done0) (finish t k p inner)))) :: bs),
                      st')
     | PTable (range, rows, cap) ->
       (match cap with
        | TCaption (parts0, start, ls) ->
          if is_blank l
          then (((set_pos p { node_span = (extent_span range); syntax_spans =
                   []; part_spans = (table_parts t p cap) }
                   (table_block t p (rev rows) cap)) :: []),
                 (PPara []))
          else ([], (PTable ((touch_extent lI range), rows, (TCaption
                 (parts0, start,
                 ((remember_line lI (drop_leading_ws l)) :: ls))))))
        | _ ->
          (match caption_open l with
           | Some rest ->
             ([], (PTable ((touch_extent lI range), rows, (TCaption
               ((cap_row_parts cap), (spot_at lI l (indent_of l)),
               (push_text lI rest []))))))
           | None ->
             if is_blank l
             then ([], (PTable (range, rows, (TAfterBlank
                    (cap_row_parts cap)))))
             else (match classify l with
                   | KRow r ->
                     (match cap with
                      | TOpen parts0 ->
                        ([], (PTable ((touch_extent lI range), (r :: rows),
                          (TOpen
                          (if p.pos_records
                           then (match table_row_part lI l r with
                                 | Some p0 -> p0 :: parts0
                                 | None -> parts0)
                           else parts0)))))
                      | _ ->
                        let (bs, st') = step_fuel t k lI p n' off l (PPara [])
                        in
                        (((set_pos p { node_span = (extent_span range);
                            syntax_spans = []; part_spans =
                            (table_parts t p cap) }
                            (table_block t p (rev rows) cap)) :: bs),
                        st'))
                   | _ ->
                     let (bs, st') = step_fuel t k lI p n' off l (PPara []) in
                     (((set_pos p { node_span = (extent_span range);
                         syntax_spans = []; part_spans =
                         (table_parts t p cap) }
                         (table_block t p (rev rows) cap)) :: bs),
                     st'))))
     | PPend (pend, specs, inner) ->
       (match classify l with
        | KBlank ->
          if is_idle inner
          then ([], (PPara []))
          else pend_result p pend specs (step_fuel t k lI p n' off l inner)
        | KAttr ap ->
          if is_idle inner
          then open_attr k lI pend specs (( + ) off (indent_of l)) ap l
          else pend_result p pend specs (step_fuel t k lI p n' off l inner)
        | _ -> pend_result p pend specs (step_fuel t k lI p n' off l inner))
     | PKey (range, lbl, src, inner) ->
       if (&&) (is_blank l) (is_idle inner)
       then (((posnode p (prov_at (extent_span range)) (Para
                (para_inlines t (src :: [])))) :: []),
              (PPara []))
       else key_result t p (touch_extent lI range) lbl src
              (step_fuel t k lI p n' off l inner)))
    n

(** val step :
    dtable -> bconfig -> coq_LineIx -> coq_PosPolicy -> string -> pstate ->
    blocks * pstate **)

let step t k lI p l st =
  step_fuel t k lI p (Stdlib.succ
    (( + ) (String.length l) (pstate_depth st))) 0 l st

(** val parse_lines :
    dtable -> bconfig -> coq_LineIx -> coq_PosPolicy -> string list -> pstate
    -> blocks **)

let rec parse_lines t k lI p lines st =
  match lines with
  | [] -> finish t k p st
  | l :: rest ->
    let (bs, st') = step t k lI p l st in
    app bs (parse_lines t k lI p rest st')

(** val parse_blocks :
    dtable -> bconfig -> coq_LineIx -> coq_PosPolicy -> string -> blocks **)

let parse_blocks t k lI p s =
  parse_lines t k lI p (split_lines s) (PPara [])

(** val pad_safe : pstate -> bool **)

let rec pad_safe = function
| PDiv (_, _, _, _, _, inner) -> pad_safe inner
| PList (_, _, inner) -> pad_safe inner
| PAttr (_, _, _, _, _, _) -> false
| PFoot (_, _, _, _, inner) -> pad_safe inner
| PPend (_, _, inner) -> pad_safe inner
| PKey (_, _, _, inner) -> pad_safe inner
| _ -> true

(** val blank_safe : pstate -> bool **)

let rec blank_safe = function
| PFence (_, _, _, _, _) -> false
| PDiv (_, _, _, _, _, inner) -> blank_safe inner
| PList (_, _, inner) -> blank_safe inner
| PAttr (_, _, _, _, _, _) -> false
| PFoot (_, _, _, _, inner) -> blank_safe inner
| PPend (_, _, inner) -> (&&) (blank_safe inner) (negb (is_idle inner))
| PKey (_, _, _, inner) ->
  (&&) (blank_safe inner) (negb (announces_end inner))
| _ -> true

(** val run_lines_tagged :
    dtable -> bconfig -> coq_PosPolicy -> (int * string) list -> pstate ->
    blocks * pstate **)

let rec run_lines_tagged t k p lines st =
  match lines with
  | [] -> ([], st)
  | p0 :: rest ->
    let (i, l) = p0 in
    let (bs, st') = step t k i p l st in
    let (more, final) = run_lines_tagged t k p rest st' in
    ((app bs more), final)

(** val finish_lines_tagged :
    dtable -> bconfig -> coq_PosPolicy -> (int * string) list -> pstate ->
    blocks **)

let finish_lines_tagged t k p lines st =
  let (bs, final) = run_lines_tagged t k p lines st in
  app bs (finish t k p final)

(** val parse_blocks_located : dtable -> bconfig -> string -> blocks **)

let parse_blocks_located t k s =
  finish_lines_tagged t k located_pos (split_lines_indexed s) (PPara [])
