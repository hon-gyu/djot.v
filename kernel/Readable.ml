open Ast
open Attributes
open Datatypes
open InlineTable
open InlineView
open Line
open List0
open ListDef
open ListUniformity
open Nat0
open OrderedList
open PeanoNat
open Render
open Step
open Strings

(** val own_char : dtable -> dstyle -> char option -> bool **)

let own_char t k = function
| Some ch -> (=) ch (dchar t k)
| None -> false

(** val bare_ok :
    dtable -> dstyle -> char option -> string -> dstyle list -> bool **)

let bare_ok t k before body around =
  let first =
    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

      (fun _ -> None)
      (fun c _ -> Some c)
      body
  in
  let last = str_last body None in
  (&&)
    ((&&)
      ((&&) ((&&) (dbare t k before) (nonspace_at first)) (nonspace_at last))
      (negb ((&&) (nonspace_at before) (existsb (dstyle_eq k) around))))
    (negb
      ((||) ((||) (own_char t k before) (own_char t k first))
        (own_char t k last)))

(** val direct_close : string -> string **)

let direct_close dst =
  (^) "](" ((^) dst ")")

(** val readable_text :
    dtable -> inline -> char option -> dstyle list -> string **)

let rec readable_text t il before around =
  let go =
    let rec go ns before0 around0 =
      match ns with
      | [] -> ""
      | n :: rest ->
        let Node (_, a, x) = n in
        let s =
          (^) (readable_text t x before0 around0)
            (match a with
             | [] -> ""
             | _ :: _ -> attr_spec a)
        in
        (^) s (go rest (str_last s before0) around0)
    in go
  in
  let marked = fun k ns ->
    let body = go ns (Some (dchar t k)) (k :: around) in
    if bare_ok t k before body around
    then (^) (dtoken t k) ((^) body (dtoken t k))
    else (^) (marked_open t k) ((^) body (marked_close t k ""))
  in
  let inside = fun ns -> go ns (Some lbrack) around in
  (match il with
   | Str s -> s
   | Emph ns -> marked DEmph ns
   | Strong ns -> marked DStrong ns
   | Highlight ns -> marked DMark ns
   | Insert ns -> marked DInsert ns
   | Delete ns -> marked DDelete ns
   | Superscript ns -> marked DSuper ns
   | Subscript ns -> marked DSub ns
   | Verbatim s -> verb_text s
   | Symbol s -> (^) (one ':') ((^) s (one ':'))
   | Math (style, s) ->
     (match style with
      | DisplayMath -> (^) (one '$') ((^) (one '$') (verb_text s))
      | InlineMath -> (^) (one '$') (verb_text s))
   | Link (ns, tgt) ->
     (match tgt with
      | Direct dst ->
        (^) (bracket_open false) ((^) (inside ns) (direct_close dst))
      | Reference label ->
        (^) (bracket_open false) ((^) (inside ns) (ref_close label "")))
   | Image (ns, tgt) ->
     (match tgt with
      | Direct dst ->
        (^) (bracket_open true) ((^) (inside ns) (direct_close dst))
      | Reference label ->
        (^) (bracket_open true) ((^) (inside ns) (ref_close label "")))
   | Span (name, ns) -> (^) (tag_open name) ((^) (inside ns) (one ']'))
   | FootnoteReference label -> note_text label
   | UrlLink s -> auto_text s
   | EmailLink s -> auto_text s
   | RawInline (fmt, s) -> raw_text fmt s
   | NonBreakingSpace ->
     (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

       (bslash, (one ' '))
   | Quoted (qt, ns) ->
     (match qt with
      | SingleQuotes -> marked DSQuote ns
      | DoubleQuotes -> marked DDQuote ns)
   | SoftBreak -> one '\n'
   | HardBreak ->
     (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

       (bslash, (one '\n'))
   | Ext_wikilink (embed, t0, al) -> wiki_text embed t0 al)

(** val readable_nodes : dtable -> inlines -> char option -> string **)

let rec readable_nodes t ns before =
  match ns with
  | [] -> ""
  | n :: rest ->
    let Node (_, a, x) = n in
    let s =
      (^) (readable_text t x before [])
        (match a with
         | [] -> ""
         | _ :: _ -> attr_spec a)
    in
    (^) s (readable_nodes t rest (str_last s before))

(** val readable_inline_lines : dtable -> inlines -> string list **)

let readable_inline_lines t ils =
  split_lines (readable_nodes t ils None)

(** val prefixed : string -> string -> string **)

let prefixed p l =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun _ _ -> (^) p l)
    l

(** val quoted : string -> string **)

let quoted l =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> ">")
    (fun _ _ -> quote_line l)
    l

(** val first_then : string -> string -> string list -> string list **)

let first_then first rest = function
| [] -> []
| l :: more -> ((^) first l) :: (map (prefixed rest) more)

(** val item_lines : litem -> string list **)

let item_lines it =
  match snd it with
  | [] -> (strip_trailing_ws (mk_open (fst it))) :: []
  | s :: l -> first_then (mk_open (fst it)) (mk_cont (fst it)) (s :: l)

(** val task_lines : (task_status * string list) -> string list **)

let task_lines it =
  let box = match fst it with
            | Complete -> "- [x]"
            | Incomplete -> "- [ ]" in
  (match snd it with
   | [] -> box :: []
   | s :: l ->
     first_then ((^) box " ")
       (blanks (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
         (Stdlib.succ (Stdlib.succ 0)))))))
       (s :: l))

(** val note_lines : string -> bool -> string list -> string list **)

let note_lines label para ls =
  let open0 = (^) "[^" ((^) label "]:") in
  if para
  then (match ls with
        | [] -> open0 :: (map (prefixed "  ") ls)
        | _ :: _ -> first_then ((^) open0 " ") "  " ls)
  else open0 :: (map (prefixed "  ") ls)

(** val caption_lines : string list -> string list **)

let caption_lines = function
| [] -> "^" :: []
| l :: rest -> ((^) "^ " l) :: rest

(** val cell_text : dtable -> cell -> string **)

let cell_text t = function
| Cell (_, _, ils) -> hd "" (readable_inline_lines t ils)

(** val cell_align : cell -> align **)

let cell_align = function
| Cell (_, al, _) -> al

(** val max_zip : int list -> int list -> int list **)

let rec max_zip a b =
  match a with
  | [] -> b
  | x :: a' ->
    (match b with
     | [] -> a
     | y :: b' -> (Nat.max x y) :: (max_zip a' b'))

(** val col_widths : string list list -> int list **)

let col_widths rows =
  fold_right (fun r ws ->
    max_zip
      (map (fun c ->
        Nat.max (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))) (String.length c))
        r)
      ws)
    [] rows

(** val row_body : int list -> string list -> string **)

let rec row_body ws = function
| [] -> ""
| c :: rest ->
  (^) " "
    ((^) c
      ((^) (blanks (sub (hd 0 ws) (String.length c)))
        ((^) " |" (row_body (tl ws) rest))))

(** val sep_cell : int -> align -> string **)

let sep_cell w = function
| AlignLeft -> (^) ":" (chars '-' (( + ) w (Stdlib.succ 0)))
| AlignRight -> (^) (chars '-' (( + ) w (Stdlib.succ 0))) ":"
| AlignCenter -> (^) ":" ((^) (chars '-' w) ":")
| AlignDefault -> chars '-' (( + ) w (Stdlib.succ (Stdlib.succ 0)))

(** val sep_row_body : int list -> align list -> string **)

let rec sep_row_body ws = function
| [] -> ""
| a :: rest ->
  (^)
    (sep_cell (Nat.max (Stdlib.succ (Stdlib.succ (Stdlib.succ 0))) (hd 0 ws))
      a)
    ((^) "|" (sep_row_body (tl ws) rest))

(** val table_lines : dtable -> cell list list -> string list **)

let table_lines t rows =
  let ws = col_widths (map (map (cell_text t)) rows) in
  let sep = fun r -> (^) "|" (sep_row_body ws (map cell_align r)) in
  let row = fun r ->
    ((^) "|" (row_body ws (map (cell_text t) r))) :: (match r with
                                                      | [] -> []
                                                      | c :: _ ->
                                                        let Cell (ct, _, _) =
                                                          c
                                                        in
                                                        (match ct with
                                                         | HeadCell ->
                                                           (sep r) :: []
                                                         | BodyCell -> []))
  in
  app
    (match rows with
     | [] -> []
     | r :: _ ->
       (match r with
        | [] -> []
        | c :: _ ->
          let Cell (ct, a, _) = c in
          (match ct with
           | HeadCell -> []
           | BodyCell ->
             if align_eqb a AlignDefault then [] else (sep r) :: [])))
    (flat_map row rows)

(** val readable_lines : dtable -> bconfig -> attr -> block -> string list **)

let rec readable_lines t k a b =
  let itemss =
    let rec goitems = function
    | [] -> []
    | n :: rest ->
      let Node (_, _, it) = n in
      (sep_lines
        (map (fun n0 ->
          readable_lines t k (node_attrs n0) (node_contents n0)) it)) ::
      (goitems rest)
    in goitems
  in
  let taskitemss =
    let rec gotasks = function
    | [] -> []
    | n :: rest ->
      let Node (_, _, x) = n in
      let (chk, it) = x in
      (chk,
      (sep_lines
        (map (fun n0 ->
          readable_lines t k (node_attrs n0) (node_contents n0)) it))) ::
      (gotasks rest)
    in gotasks
  in
  let defitemss =
    let rec godefs = function
    | [] -> []
    | n :: rest ->
      let Node (_, _, x) = n in
      let (n0, n1) = x in
      let Node (_, _, term) = n0 in
      let Node (_, _, it) = n1 in
      (sep_lines
        (app
          (match term with
           | [] -> []
           | _ :: _ -> (readable_inline_lines t term) :: [])
          (map (fun n2 ->
            readable_lines t k (node_attrs n2) (node_contents n2)) it))) ::
      (godefs rest)
    in godefs
  in
  let cls = fence_class k a b in
  app (attr_lines (drop_class cls a))
    (match b with
     | Para ils -> readable_inline_lines t ils
     | Section bs ->
       sep_lines
         (map (fun n -> readable_lines t k (node_attrs n) (node_contents n))
           bs)
     | Heading (lvl, ils) ->
       map (heading_line lvl) (readable_inline_lines t ils)
     | BlockQuote bs ->
       map quoted
         (sep_lines
           (map (fun n ->
             readable_lines t k (node_attrs n) (node_contents n)) bs))
     | CodeBlock (lang, text) ->
       (code_open lang) :: (app (split_lines text) (code_close :: []))
     | Div (name, bs) ->
       let body =
         sep_lines
           (map (fun n ->
             readable_lines t k (node_attrs n) (node_contents n)) bs)
       in
       let word =
         (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

           (fun _ -> cls)
           (fun _ _ -> name)
           name
       in
       (div_open_line (div_fence_for t k body) word) :: (app body
                                                          ((div_fence_for t k
                                                             body) :: []))
     | OrderedList (oa, sp, items) ->
       list_lines sp (map item_lines (ck_items (lk_of_ol oa) (itemss items)))
     | BulletList (sp, items) ->
       list_lines sp (map item_lines (ck_items LKBullet (itemss items)))
     | TaskList (sp, items) ->
       list_lines sp (map task_lines (taskitemss items))
     | DefinitionList (sp, its) ->
       list_lines sp (map item_lines (ck_items LKDef (defitemss its)))
     | ThematicBreak -> thematic_line :: []
     | Table (cap, rows) ->
       app
         (table_lines t
           (map (fun r -> map node_contents (node_contents r)) rows))
         (match node_contents cap with
          | [] -> []
          | n :: l -> caption_lines (readable_inline_lines t (n :: l)))
     | RawBlock (fmt, text) ->
       (code_open ((^) "=" fmt)) :: (app (split_lines text)
                                      (code_close :: []))
     | FootnoteDef (label, bs) ->
       note_lines label
         (match bs with
          | [] -> false
          | n :: _ ->
            let Node (_, a0, x) = n in
            (match a0 with
             | [] -> (match x with
                      | Para _ -> true
                      | _ -> false)
             | _ :: _ -> false))
         (sep_lines
           (map (fun n ->
             readable_lines t k (node_attrs n) (node_contents n)) bs))
     | RefDef (label, dest) -> (ref_line label dest) :: []
     | Ext_keyed (label, inner) ->
       key_lines t (readable_nodes t label None)
         (let Node (_, a0, x) = inner in
          (match a0 with
           | [] -> (match x with
                    | Para _ -> true
                    | _ -> false)
           | _ :: _ -> false))
         (readable_lines t k (node_attrs inner) (node_contents inner))
     | Ext_callout (kind, fold, title, bs) ->
       (quote_line
         (callout_header_line kind fold
           (String.concat " " (readable_inline_lines t title)))) :: (map
                                                                    quoted
                                                                    (sep_lines
                                                                    (map
                                                                    (fun n ->
                                                                    readable_lines
                                                                    t k
                                                                    (node_attrs
                                                                    n)
                                                                    (node_contents
                                                                    n)) bs))))

(** val readable_djot : dtable -> bconfig -> blocks -> string **)

let readable_djot t k bs =
  String.concat nl
    (sep_lines
      (map (fun n -> readable_lines t k (node_attrs n) (node_contents n)) bs))

(** val readable_doc : dtable -> bconfig -> doc -> string **)

let readable_doc t k d =
  readable_djot t k (doc_source_blocks d)
