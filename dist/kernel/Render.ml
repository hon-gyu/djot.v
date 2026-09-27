open Ast
open Attributes
open Datatypes
open Document
open InlineScan
open InlineTable
open InlineView
open Line
open List0
open ListDef
open ListUniformity
open OrderedList
open PeanoNat
open Step
open Strings
open Uniformity

(** val thematic_line : string **)

let thematic_line =
  "* * * *"

(** val ref_line : string -> string -> string **)

let ref_line label dest =
  (^) "[" ((^) label ((^) "]: " dest))

(** val key_line : string -> string -> string **)

let key_line label value =
  (^) label ((^) ": " value)

(** val key_inline_ok : dtable -> string -> string -> bool **)

let key_inline_ok t label value =
  let l = key_line label value in
  (&&) ((&&) (line_ok l) (is_text l))
    (match key_split t l with
     | Some p -> let (lbl, v) = p in (&&) ((=) lbl label) ((=) v value)
     | None -> false)

(** val key_lines : dtable -> string -> bool -> string list -> string list **)

let key_lines t label para ls = match ls with
| [] -> ((^) label ":") :: []
| l0 :: rest ->
  if (&&) para (key_inline_ok t label l0)
  then (key_line label l0) :: rest
  else ((^) label ":") :: ls

(** val code_close : string **)

let code_close =
  "```"

(** val code_open : string -> string **)

let code_open info =
  (^) "```" info

(** val align_dashes : align -> string **)

let align_dashes = function
| AlignLeft -> ":--"
| AlignRight -> "--:"
| AlignCenter -> ":-:"
| AlignDefault -> "---"

(** val sep_body : align list -> string **)

let rec sep_body = function
| [] -> ""
| a :: rest -> (^) (align_dashes a) ((^) "|" (sep_body rest))

(** val sep_line : align list -> string **)

let sep_line als =
  (^) "|" (sep_body als)

(** val cells_body : string list -> string **)

let rec cells_body = function
| [] -> ""
| c :: rest -> (^) " " ((^) c ((^) " |" (cells_body rest)))

(** val cells_line : string list -> string **)

let cells_line cs =
  (^) "|" (cells_body cs)

(** val sep_lines : string list list -> string list **)

let rec sep_lines = function
| [] -> []
| ls :: rest ->
  (match rest with
   | [] -> ls
   | _ :: _ -> app ls ("" :: (sep_lines rest)))

type ctrow =
| CTBody of cinline list list
| CTHead of align list * cinline list list

(** val ctrow_cells : ctrow -> cinline list list **)

let ctrow_cells = function
| CTBody cs -> cs
| CTHead (_, cs) -> cs

(** val ctrow_lines : dtable -> ctrow -> string list **)

let ctrow_lines t = function
| CTBody cs -> (cells_line (map (ci_line t) cs)) :: []
| CTHead (als, cs) ->
  (cells_line (map (ci_line t) cs)) :: ((sep_line als) :: [])

(** val ccells_of :
    cell_type -> align list -> cinline list list -> cell list **)

let rec ccells_of ct als = function
| [] -> []
| c :: cs' ->
  (match als with
   | [] -> (Cell (ct, AlignDefault, (ci_inlines c))) :: (ccells_of ct [] cs')
   | a :: als' -> (Cell (ct, a, (ci_inlines c))) :: (ccells_of ct als' cs'))

(** val ctable_cells : align list -> ctrow list -> cell list list **)

let rec ctable_cells als = function
| [] -> []
| c :: rest ->
  (match c with
   | CTBody cs -> (ccells_of BodyCell als cs) :: (ctable_cells als rest)
   | CTHead (als', cs) ->
     (ccells_of HeadCell als' cs) :: (ctable_cells als' rest))

type cblock =
| CPara of cinline list list
| CThematic
| CCode of string * string list
| CRaw of string * string list
| CHeading of int * cinline list list
| CQuote of cblock list
| CCallout of string * callout_fold option * cinline list * cblock list
| CDiv of cblock list
| CList of list_kind * list_spacing * cblock list list
| CRef of string * string
| CTable of ctrow list
| CId of string * cblock
| CKey of cinline * cblock

(** val cb_lines : dtable -> cblock -> string list **)

let rec cb_lines t cb =
  let itemss =
    let rec goitems = function
    | [] -> []
    | it :: rest -> (sep_lines (map (cb_lines t) it)) :: (goitems rest)
    in goitems
  in
  (match cb with
   | CPara lss -> map (ci_line t) lss
   | CThematic -> thematic_line :: []
   | CCode (info, content) ->
     (code_open info) :: (app content (code_close :: []))
   | CRaw (format, content) ->
     (code_open
       ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

       ('=', format))) :: (app content (code_close :: []))
   | CHeading (lvl, lss) -> map (heading_line lvl) (map (ci_line t) lss)
   | CQuote inner -> map quote_line (sep_lines (map (cb_lines t) inner))
   | CCallout (kind, fold, title, inner) ->
     (quote_line (callout_header_line kind fold (ci_line t title))) ::
       (map quote_line (sep_lines (map (cb_lines t) inner)))
   | CDiv inner ->
     div_fence :: (app (sep_lines (map (cb_lines t) inner)) (div_fence :: []))
   | CList (k, sp, items) ->
     list_lines sp (map litem_lines (ck_items k (itemss items)))
   | CRef (label, dest) -> (ref_line label dest) :: []
   | CTable rows -> flat_map (ctrow_lines t) rows
   | CId (id, inner) -> ((^) "{#" ((^) id "}")) :: (cb_lines t inner)
   | CKey (label, inner) ->
     key_lines t (ci_line t (label :: []))
       (match inner with
        | CPara _ -> true
        | _ -> false)
       (cb_lines t inner))

(** val cb_ast : cblock -> block node **)

let rec cb_ast cb =
  let itemsof =
    let rec goitems = function
    | [] -> []
    | it :: rest -> (map cb_ast it) :: (goitems rest)
    in goitems
  in
  (match cb with
   | CPara lss -> mk (Para (ci_para lss))
   | CThematic -> mk ThematicBreak
   | CCode (info, content) -> mk (CodeBlock (info, (join_nl content)))
   | CRaw (format, content) -> mk (RawBlock (format, (join_nl content)))
   | CHeading (lvl, lss) -> mk (Heading (lvl, (ci_para lss)))
   | CQuote inner -> mk (BlockQuote (map cb_ast inner))
   | CCallout (kind, fold, title, inner) ->
     mk (Ext_callout (kind, fold, (ci_inlines title), (map cb_ast inner)))
   | CDiv inner -> mk (Div (map cb_ast inner))
   | CList (k, sp, items) -> mk (ck_block k sp (itemsof items))
   | CRef (label, dest) -> mk (RefDef (label, dest))
   | CTable rows -> mk (Table (None, (ctable_cells [] rows)))
   | CId (id, inner) -> add_attr (("id", id) :: []) (cb_ast inner)
   | CKey (label, inner) ->
     mk (Ext_keyed (((ci_ast label) :: []), (cb_ast inner))))

(** val item_lines : dtable -> cblock list -> string list **)

let item_lines t it =
  sep_lines (map (cb_lines t) it)

(** val blocks_of_cblocks : cblock list -> blocks **)

let blocks_of_cblocks cbs =
  map cb_ast cbs

(** val cline : string -> cinline list **)

let cline s =
  (CIStr s) :: []

(** val cpara : string list -> cblock **)

let cpara ls =
  CPara (map cline ls)

(** val cheading : int -> string list -> cblock **)

let cheading lvl ls =
  CHeading (lvl, (map cline ls))

(** val para_ok : dtable -> bconfig -> string list -> bool **)

let para_ok t k ls = match ls with
| [] -> false
| a :: _ ->
  (&&)
    ((&&) ((&&) ((&&) (is_text a) (keyless t k a)) (forallb line_ok ls))
      (forallb (fun l -> negb (bcuts k l)) ls))
    ((=) (strip_trailing_ws (last ls "")) (last ls ""))

(** val code_ok : string -> string list -> bool **)

let code_ok info content =
  (&&) (all_info_chars info)
    (forallb (fun l ->
      (&&) (no_nl l)
        (negb
          (fence_close { f_ch = '`'; f_len = (Stdlib.succ (Stdlib.succ
            (Stdlib.succ 0))); f_info = info } l)))
      content)

(** val raw_ok : string -> string list -> bool **)

let raw_ok format content =
  code_ok
    ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    ('=', format)) content

(** val heading_ok : bconfig -> int -> string list -> bool **)

let heading_ok k lvl ls =
  (&&)
    ((&&)
      ((&&) ((&&) (( <= ) (Stdlib.succ 0) lvl) (nonempty ls))
        (forallb line_ok ls))
      ((||) k.bheading_continues (( = ) (length ls) (Stdlib.succ 0))))
    ((=) (strip_trailing_ws (last ls "")) (last ls ""))

(** val quote_header_safe : dtable -> bconfig -> cblock list -> bool **)

let quote_header_safe t k inner =
  match sep_lines (map (cb_lines t) inner) with
  | [] -> true
  | l :: _ -> (match quote_header k l with
               | Some _ -> false
               | None -> true)

(** val callout_title_ok : dtable -> cinline list -> bool **)

let callout_title_ok t title = match title with
| [] -> true
| _ :: _ ->
  (&&) (line_ok (ci_line t title))
    ((=) (strip_trailing_ws (ci_line t title)) (ci_line t title))

(** val item_forces_loose : dtable -> bconfig -> cblock list -> bool **)

let item_forces_loose t k item =
  item_loose t k (item_lines t item)

(** val items_force_loose : dtable -> bconfig -> cblock list list -> bool **)

let items_force_loose t k items =
  existsb (item_forces_loose t k) items

(** val items_seps_loosen : dtable -> bconfig -> cblock list list -> bool **)

let items_seps_loosen t k items =
  seps_loosen t k (map (item_lines t) items)

(** val is_clist : cblock -> bool **)

let is_clist = function
| CList (_, _, _) -> true
| _ -> false

(** val is_cid : cblock -> bool **)

let is_cid = function
| CId (_, _) -> true
| _ -> false

(** val ends_clist : cblock -> bool **)

let rec ends_clist = function
| CList (_, _, _) -> true
| CId (_, inner) -> ends_clist inner
| CKey (_, inner) -> ends_clist inner
| _ -> false

(** val ends_ctable : cblock -> bool **)

let rec ends_ctable = function
| CTable _ -> true
| CId (_, inner) -> ends_ctable inner
| CKey (_, inner) -> ends_ctable inner
| _ -> false

(** val is_cref : cblock -> bool **)

let rec is_cref = function
| CRef (_, _) -> true
| CId (_, inner) -> is_cref inner
| CKey (_, inner) -> is_cref inner
| _ -> false

(** val closes_table : dtable -> cblock -> bool **)

let closes_table t cb =
  match cb_lines t cb with
  | [] -> false
  | a :: _ ->
    (&&) (negb (is_blank a))
      (match caption_open a with
       | Some _ -> false
       | None -> true)

(** val cb_pair_ok : dtable -> cblock -> cblock -> bool **)

let cb_pair_ok t c1 c2 =
  (&&) (negb ((&&) (ends_clist c1) (is_clist c2)))
    ((||) (negb (ends_ctable c1)) (closes_table t c2))

(** val cb_pairs_ok : dtable -> cblock list -> bool **)

let rec cb_pairs_ok t = function
| [] -> true
| c1 :: rest ->
  (match rest with
   | [] -> true
   | c2 :: _ -> (&&) (cb_pair_ok t c1 c2) (cb_pairs_ok t rest))

(** val ref_ok : string -> string -> bool **)

let ref_ok label dest =
  (&&)
    ((&&) ((&&) (no_char ']' label) (negb (is_footnote_label label)))
      (no_nl label))
    (no_ws dest)

(** val row_reparses : trow -> string -> bool **)

let row_reparses r l =
  match classify l with
  | KRow r' -> trow_eqb r' r
  | _ -> false

(** val cdef_head_ok : cblock list -> bool **)

let cdef_head_ok = function
| [] -> true
| c :: _ -> negb ((||) (is_cid c) (is_cref c))

(** val ck_content_ok : list_kind -> cblock list list -> bool **)

let ck_content_ok k items =
  match k with
  | LKDef -> forallb cdef_head_ok items
  | _ -> true

(** val ctrow_ok : dtable -> ctrow -> bool **)

let ctrow_ok t r =
  let cs = ctrow_cells r in
  (&&)
    ((&&)
      ((&&) ((&&) (nonempty cs) (forallb (cis_ok t) cs))
        (line_ok (cells_line (map (ci_line t) cs))))
      (row_reparses (TCells (map (ci_line t) cs))
        (cells_line (map (ci_line t) cs))))
    (match r with
     | CTBody _ -> true
     | CTHead (als, _) ->
       (&&) (( = ) (length als) (length cs))
         (row_reparses (TSep als) (sep_line als)))

(** val ckey_label_ok : dtable -> cinline -> bool **)

let ckey_label_ok t label =
  let src = ci_line t (label :: []) in
  let l = (^) src ":" in
  (&&)
    ((&&) ((&&) ((&&) (cis_ok t (label :: [])) (line_ok l)) (is_text l))
      ((=) (strip_trailing_ws src) src))
    (match key_split t l with
     | Some p -> let (lbl, value) = p in (&&) ((=) lbl src) ((=) value "")
     | None -> false)

(** val cb_ok : dtable -> bconfig -> cblock -> bool **)

let rec cb_ok t k cb =
  let inner_ok =
    let rec go = function
    | [] -> false
    | c :: rest ->
      (match rest with
       | [] -> cb_ok t k c
       | _ :: _ -> (&&) (cb_ok t k c) (go rest))
    in go
  in
  let divs_ok =
    let rec godiv = function
    | [] -> true
    | c :: rest -> (&&) (cb_ok t k c) (godiv rest)
    in godiv
  in
  let items_ok =
    let rec goitems = function
    | [] -> true
    | it :: rest -> (&&) (inner_ok it) (goitems rest)
    in goitems
  in
  (match cb with
   | CPara lss ->
     (&&) (para_ok t k (map (ci_line t) lss)) (forallb (cis_ok t) lss)
   | CThematic -> true
   | CCode (info, content) ->
     (&&) (code_ok info content)
       ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

          (fun _ -> true)
          (fun a _ ->
          (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
            (fun b b0 b1 b2 b3 b4 b5 b6 ->
            if b
            then if b0
                 then true
                 else if b1
                      then if b2
                           then if b3
                                then if b4
                                     then if b5
                                          then true
                                          else if b6
                                               then true
                                               else negb k.braw_blocks
                                     else true
                                else true
                           else true
                      else true
            else true)
            a)
          info)
   | CRaw (format, content) -> (&&) k.braw_blocks (raw_ok format content)
   | CHeading (lvl, lss) ->
     (&&) (heading_ok k lvl (map (ci_line t) lss)) (forallb (cis_ok t) lss)
   | CQuote inner ->
     (&&) ((&&) (inner_ok inner) (cb_pairs_ok t inner))
       (quote_header_safe t k inner)
   | CCallout (kind, _, title, inner) ->
     (&&)
       ((&&)
         ((&&)
           ((&&) ((&&) k.bcallouts (callout_kind_ok kind))
             (callout_title_ok t title))
           (cis_ok t title))
         (divs_ok inner))
       (cb_pairs_ok t inner)
   | CDiv inner ->
     (&&) ((&&) ((&&) k.bdivs (divs_ok inner)) (cb_pairs_ok t inner))
       (div_content_ok t k (sep_lines (map (cb_lines t) inner)))
   | CList (k0, sp, items) ->
     (&&)
       ((&&)
         ((&&)
           ((&&)
             ((&&) ((&&) (nonempty items) (items_ok items))
               (ck_ok k k0 (length items)))
             (forallb (fun it -> item_ok t k (ck_first k0) (item_lines t it))
               items))
           (forallb (cb_pairs_ok t) items))
         (match sp with
          | Tight -> negb (items_force_loose t k items)
          | Loose ->
            (||) (items_seps_loosen t k items) (items_force_loose t k items)))
       (ck_content_ok k0 items)
   | CRef (label, dest) -> ref_ok label dest
   | CTable rows ->
     (&&) ((&&) k.btables (nonempty rows)) (forallb (ctrow_ok t) rows)
   | CId (id, inner) ->
     (&&) ((&&) ((&&) k.battrs (explicit_id_ok id)) (negb (is_cid inner)))
       (cb_ok t k inner)
   | CKey (label, inner) ->
     (&&) ((&&) ((&&) k.bkeyed (ckey_label_ok t label)) (cb_ok t k inner))
       (key_content_ok t k (cb_lines t inner) (PPara [])))

(** val lk_of_ol : ordered_list_attributes -> list_kind **)

let lk_of_ol oa =
  match oa.ol_style with
  | Decimal -> LKDecimal (oa.ol_delim, oa.ol_start)
  | LetterUpper -> LKAlpha (true, oa.ol_delim, oa.ol_start)
  | LetterLower -> LKAlpha (false, oa.ol_delim, oa.ol_start)
  | RomanUpper -> LKRoman (true, oa.ol_delim, oa.ol_start)
  | RomanLower -> LKRoman (false, oa.ol_delim, oa.ol_start)

(** val cell_text : dtable -> cell -> string **)

let cell_text t = function
| Cell (_, _, ils) -> hd "" (inline_lines t ils "")

(** val cell_align : cell -> align **)

let cell_align = function
| Cell (_, al, _) -> al

(** val render_row : dtable -> cell list -> string list **)

let render_row t r =
  (cells_line (map (cell_text t) r)) :: (match r with
                                         | [] -> []
                                         | c :: _ ->
                                           let Cell (ct, _, _) = c in
                                           (match ct with
                                            | HeadCell ->
                                              (sep_line (map cell_align r)) :: []
                                            | BodyCell -> []))

(** val initial_sep : cell list list -> string list **)

let initial_sep = function
| [] -> []
| r :: _ ->
  (match r with
   | [] -> []
   | c :: _ ->
     let Cell (ct, a, _) = c in
     (match ct with
      | HeadCell -> []
      | BodyCell ->
        if align_eqb a AlignDefault
        then []
        else (sep_line (map cell_align r)) :: []))

(** val table_lines : dtable -> cell list list -> string list **)

let table_lines t rows =
  app (initial_sep rows) (flat_map (render_row t) rows)

(** val text_lines : dtable -> inlines -> string list **)

let text_lines t ils =
  split_lines (join_nl (inline_lines t ils ""))

(** val caption_lines : dtable -> inlines -> string list **)

let caption_lines t ils =
  match text_lines t ils with
  | [] -> "^" :: []
  | l :: rest -> ((^) "^ " l) :: rest

(** val task_open : task_status -> string **)

let task_open = function
| Complete -> "- [x] "
| Incomplete -> "- [ ] "

(** val task_empty : task_status -> string **)

let task_empty = function
| Complete -> "- [x]"
| Incomplete -> "- [ ]"

(** val task_litem_lines : (task_status * string list) -> string list **)

let task_litem_lines = function
| (chk, l) ->
  (match l with
   | [] -> (task_empty chk) :: []
   | l0 :: more ->
     ((^) (task_open chk) l0) :: (map (fun l1 ->
                                   (^)
                                     (blanks (Stdlib.succ (Stdlib.succ
                                       (Stdlib.succ (Stdlib.succ (Stdlib.succ
                                       (Stdlib.succ 0)))))))
                                     l1)
                                   more))

(** val item_or_marker_lines : litem -> string list **)

let item_or_marker_lines it =
  match snd it with
  | [] -> (strip_trailing_ws (mk_open (fst it))) :: []
  | _ :: _ -> litem_lines it

(** val attr_lines : attr -> string list **)

let attr_lines a = match a with
| [] -> []
| _ :: _ -> (attr_spec a) :: []

(** val fence_class : attr -> block -> string **)

let fence_class a = function
| Div _ ->
  (match a with
   | [] -> ""
   | p :: _ ->
     let (k, c) = p in
     if (&&) ((=) k "class") (class_word_ok c) then c else "")
| _ -> ""

(** val drop_class : string -> attr -> attr **)

let drop_class cls a =
  if (=) cls "" then a else filter (fun kv -> negb ((=) (fst kv) "class")) a

(** val closer_run : string -> int **)

let closer_run l =
  let (n, r) = count_run ':' (drop_leading_ws l) in
  if (&&) (( <= ) (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))) n) (is_blank r)
  then n
  else 0

(** val div_fence_for : dtable -> bconfig -> string list -> string **)

let div_fence_for t k body =
  if div_content_ok t k body
  then div_fence
  else chars ':'
         (Nat.max (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))) (Stdlib.succ
           (list_max (map closer_run body))))

(** val div_open_line : string -> string -> string **)

let div_open_line fence cls =
  if (=) cls "" then fence else (^) fence ((^) " " cls)

(** val note_indent : string -> string **)

let note_indent l =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun _ _ -> (^) "  " l)
    l

(** val render_lines : dtable -> bconfig -> attr -> block -> string list **)

let rec render_lines t k a b =
  let itemss =
    let rec goitems = function
    | [] -> []
    | it :: rest ->
      (sep_lines
        (map (fun n -> render_lines t k (node_attrs n) (node_contents n)) it)) ::
        (goitems rest)
    in goitems
  in
  let taskitemss =
    let rec gotasks = function
    | [] -> []
    | p :: rest ->
      let (chk, it) = p in
      (chk,
      (sep_lines
        (map (fun n -> render_lines t k (node_attrs n) (node_contents n)) it))) ::
      (gotasks rest)
    in gotasks
  in
  let defitemss =
    let rec godefs = function
    | [] -> []
    | p :: rest ->
      let (term, it) = p in
      (sep_lines
        (app (match term with
              | [] -> []
              | _ :: _ -> (text_lines t term) :: [])
          (map (fun n -> render_lines t k (node_attrs n) (node_contents n))
            it))) :: (godefs rest)
    in godefs
  in
  let cls = fence_class a b in
  app (attr_lines (drop_class cls a))
    (match b with
     | Para ils -> text_lines t ils
     | Section bs ->
       sep_lines
         (map (fun n -> render_lines t k (node_attrs n) (node_contents n)) bs)
     | Heading (lvl, ils) -> map (heading_line lvl) (text_lines t ils)
     | BlockQuote bs ->
       map quote_line
         (sep_lines
           (map (fun n -> render_lines t k (node_attrs n) (node_contents n))
             bs))
     | CodeBlock (lang, text) ->
       (code_open lang) :: (app (split_lines text) (code_close :: []))
     | Div bs ->
       let body =
         sep_lines
           (map (fun n -> render_lines t k (node_attrs n) (node_contents n))
             bs)
       in
       (div_open_line (div_fence_for t k body) cls) :: (app body
                                                         ((div_fence_for t k
                                                            body) :: []))
     | OrderedList (oa, sp, items) ->
       list_lines sp
         (map item_or_marker_lines (ck_items (lk_of_ol oa) (itemss items)))
     | BulletList (sp, items) ->
       list_lines sp
         (map item_or_marker_lines (ck_items LKBullet (itemss items)))
     | TaskList (sp, items) ->
       list_lines sp (map task_litem_lines (taskitemss items))
     | DefinitionList (sp, its) ->
       list_lines sp
         (map item_or_marker_lines (ck_items LKDef (defitemss its)))
     | ThematicBreak -> thematic_line :: []
     | Table (cap, rows) ->
       app (table_lines t rows)
         (match cap with
          | Some ils -> caption_lines t ils
          | None -> [])
     | RawBlock (fmt, text) ->
       (code_open ((^) "=" fmt)) :: (app (split_lines text)
                                      (code_close :: []))
     | FootnoteDef (label, bs) ->
       ((^) "[^" ((^) label "]:")) :: (map note_indent
                                        (sep_lines
                                          (map (fun n ->
                                            render_lines t k (node_attrs n)
                                              (node_contents n))
                                            bs)))
     | RefDef (label, dest) -> (ref_line label dest) :: []
     | Ext_keyed (label, inner) ->
       key_lines t
         (String.concat ""
           (map (fun n -> inline_text t (node_contents n)) label))
         (let Node (_, a0, x) = inner in
          (match a0 with
           | [] -> (match x with
                    | Para _ -> true
                    | _ -> false)
           | _ :: _ -> false))
         (render_lines t k (node_attrs inner) (node_contents inner))
     | Ext_callout (kind, fold, title, bs) ->
       (quote_line
         (callout_header_line kind fold
           (String.concat " " (text_lines t title)))) :: (map quote_line
                                                           (sep_lines
                                                             (map (fun n ->
                                                               render_lines t
                                                                 k
                                                                 (node_attrs
                                                                   n)
                                                                 (node_contents
                                                                   n))
                                                               bs))))

(** val render_node_lines : dtable -> bconfig -> block node -> string list **)

let render_node_lines t k n =
  render_lines t k (node_attrs n) (node_contents n)

(** val render_blocks_lines :
    dtable -> bconfig -> blocks -> string list list **)

let render_blocks_lines t k bs =
  map (render_node_lines t k) bs

(** val render_djot : dtable -> bconfig -> blocks -> string **)

let render_djot t k bs =
  String.concat nl (sep_lines (render_blocks_lines t k bs))

(** val drop_id_if : string -> attr -> attr **)

let drop_id_if v a =
  match alist_lookup "id" a with
  | Some v' ->
    if (=) v v' then filter (fun kv -> negb ((=) (fst kv) "id")) a else a
  | None -> a

(** val base_id : inlines -> string **)

let base_id ils =
  id_base (inlines_text ils)

(** val drop_auto_ids : block -> pos -> attr -> block node **)

let rec drop_auto_ids b p a =
  let go =
    let rec go = function
    | [] -> []
    | n :: rest ->
      let Node (p', a', x) = n in (drop_auto_ids x p' a') :: (go rest)
    in go
  in
  let goits =
    let rec goits = function
    | [] -> []
    | it :: rest -> (go it) :: (goits rest)
    in goits
  in
  (match b with
   | Section bs ->
     let a' =
       match bs with
       | [] -> a
       | n :: _ ->
         let Node (_, _, x) = n in
         (match x with
          | Heading (_, ils) -> drop_id_if (base_id ils) a
          | _ -> a)
     in
     Node (p, a', (Section (go bs)))
   | Heading (lvl, ils) ->
     Node (p, (drop_id_if (base_id ils) a), (Heading (lvl, ils)))
   | BlockQuote bs -> Node (p, a, (BlockQuote (go bs)))
   | Div bs -> Node (p, a, (Div (go bs)))
   | OrderedList (oa, sp, its) ->
     Node (p, a, (OrderedList (oa, sp, (goits its))))
   | BulletList (sp, its) -> Node (p, a, (BulletList (sp, (goits its))))
   | TaskList (sp, its) ->
     Node (p, a, (TaskList (sp,
       (let rec gotasks = function
        | [] -> []
        | p0 :: rest -> let (chk, it) = p0 in (chk, (go it)) :: (gotasks rest)
        in gotasks its))))
   | DefinitionList (sp, its) ->
     Node (p, a, (DefinitionList (sp,
       (let rec godefs = function
        | [] -> []
        | p0 :: rest ->
          let (term, it) = p0 in (term, (go it)) :: (godefs rest)
        in godefs its))))
   | FootnoteDef (l, bs) -> Node (p, a, (FootnoteDef (l, (go bs))))
   | Ext_keyed (label, b0) ->
     let Node (p', a', x) = b0 in
     Node (p, a, (Ext_keyed (label, (drop_auto_ids x p' a'))))
   | Ext_callout (kind, fold, title, bs) ->
     Node (p, a, (Ext_callout (kind, fold, title, (go bs))))
   | _ -> Node (p, a, b))

(** val doc_source_blocks : doc -> blocks **)

let doc_source_blocks d =
  app
    (map (fun n -> let Node (p, a, x) = n in drop_auto_ids x p a)
      d.doc_blocks)
    (map (fun ln -> mk (FootnoteDef ((fst ln), (snd ln)))) d.doc_footnotes)

(** val render_doc : dtable -> bconfig -> doc -> string **)

let render_doc t k d =
  render_djot t k (doc_source_blocks d)
