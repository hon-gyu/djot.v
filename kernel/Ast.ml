open Datatypes
open List0
open ListDef

(** val alist_lookup : string -> (string * 'a1) list -> 'a1 option **)

let rec alist_lookup k = function
| [] -> None
| p :: rest ->
  let (k', v) = p in if (=) k k' then Some v else alist_lookup k rest

(** val alist_set :
    string -> 'a1 -> (string * 'a1) list -> (string * 'a1) list **)

let rec alist_set k v = function
| [] -> (k, v) :: []
| p :: rest ->
  let (k', v') = p in
  if (=) k k' then (k, v) :: rest else (k', v') :: (alist_set k v rest)

type attr = (string * string) list

module Attr =
 struct
  (** val integrate : (string * string) -> attr -> attr **)

  let integrate kv kvs =
    let (k, v) = kv in
    (match alist_lookup k kvs with
     | Some v' ->
       if (=) k "class"
       then (k,
              ((^) v ((^) " " v'))) :: (filter (fun p ->
                                         negb ((=) (fst p) "class")) kvs)
       else kvs
     | None -> (k, v) :: kvs)

  (** val union : attr -> attr -> attr **)

  let union a b =
    fold_right integrate b a

  (** val set : string -> string -> attr -> attr **)

  let set =
    alist_set

  (** val add_class : string -> attr -> attr **)

  let add_class v a =
    match alist_lookup "class" a with
    | Some old -> set "class" ((^) old ((^) " " v)) a
    | None -> set "class" v a

  (** val put : (string * string) -> attr -> attr **)

  let put kv a =
    if (=) (fst kv) "class"
    then add_class (snd kv) a
    else set (fst kv) (snd kv) a

  (** val merge : attr -> attr -> attr **)

  let merge new0 acc =
    fold_left (fun acc' kv -> put kv acc') new0 acc

  (** val apply_pending : attr -> attr -> attr **)

  let apply_pending pending a =
    fold_left (fun a' kv -> set (fst kv) (snd kv) a') pending a
 end

type spot = { spot_line : int; spot_rem : int }

type span = { span_start : spot; span_stop : spot }

type coq_InlineCursor = { cursor_start : spot; cursor_stop : spot;
                          cursor_origin : spot }

(** val semantic_inline_cursor : coq_InlineCursor **)

let semantic_inline_cursor =
  { cursor_start = { spot_line = 0; spot_rem = 0 }; cursor_stop =
    { spot_line = 0; spot_rem = 0 }; cursor_origin = { spot_line = 0;
    spot_rem = 0 } }

type syntax_role =
| RAttrSpec
| ROpenFence
| RCloseFence

type parts =
| PNone
| PItems of span list
| PDefItems of ((span * span) * span) list
| PTable of span option * (span * span list) list

type provenance = { node_span : span;
                    syntax_spans : (syntax_role * span) list;
                    part_spans : parts }

type pos =
| NoPos
| SomePos of provenance

type 'a node =
| Node of pos * attr * 'a

(** val node_provenance : 'a1 node -> provenance option **)

let node_provenance = function
| Node (p0, _, _) -> (match p0 with
                      | NoPos -> None
                      | SomePos p -> Some p)

(** val mk : 'a1 -> 'a1 node **)

let mk x =
  Node (NoPos, [], x)

(** val node_contents : 'a1 node -> 'a1 **)

let node_contents = function
| Node (_, _, x) -> x

(** val node_attrs : 'a1 node -> attr **)

let node_attrs = function
| Node (_, a, _) -> a

(** val add_attr : attr -> 'a1 node -> 'a1 node **)

let add_attr a = function
| Node (p, a', x) -> Node (p, (Attr.union a' a), x)

type coq_PosPolicy = { mkpos : (provenance -> pos); pos_records : bool }

(** val semantic_pos : coq_PosPolicy **)

let semantic_pos =
  { mkpos = (fun _ -> NoPos); pos_records = false }

(** val located_pos : coq_PosPolicy **)

let located_pos =
  { mkpos = (fun x -> SomePos x); pos_records = true }

(** val posnode : coq_PosPolicy -> provenance -> 'a1 -> 'a1 node **)

let posnode h p x =
  Node ((h.mkpos p), [], x)

(** val null_span : span **)

let null_span =
  { span_start = { spot_line = 0; spot_rem = 0 }; span_stop = { spot_line =
    0; spot_rem = 0 } }

(** val pspan : coq_PosPolicy -> span -> span **)

let pspan h r =
  if h.pos_records then r else null_span

(** val prov_at : span -> provenance **)

let prov_at r =
  { node_span = r; syntax_spans = []; part_spans = PNone }

(** val prov_with : span -> (syntax_role * span) list -> provenance **)

let prov_with r rs =
  { node_span = r; syntax_spans = rs; part_spans = PNone }

(** val attr_roles : span list -> (syntax_role * span) list **)

let attr_roles specs =
  map (fun r -> (RAttrSpec, r)) specs

(** val set_pos : coq_PosPolicy -> provenance -> 'a1 node -> 'a1 node **)

let set_pos h p n =
  match h.mkpos p with
  | NoPos -> n
  | SomePos p0 -> let Node (_, a, x) = n in Node ((SomePos p0), a, x)

(** val pos_head :
    coq_PosPolicy -> provenance -> 'a1 node list -> 'a1 node list **)

let pos_head h p ns =
  match h.mkpos p with
  | NoPos -> ns
  | SomePos _ ->
    (match ns with
     | [] -> []
     | n :: rest -> (set_pos h p n) :: rest)

(** val add_roles :
    coq_PosPolicy -> (syntax_role * span) list -> 'a1 node -> 'a1 node **)

let add_roles h rs n =
  if h.pos_records
  then let Node (p0, a, x) = n in
       (match p0 with
        | NoPos -> n
        | SomePos p ->
          Node ((SomePos { node_span = p.node_span; syntax_spans =
            (app p.syntax_spans rs); part_spans = p.part_spans }), a, x))
  else n

(** val add_roles_head :
    coq_PosPolicy -> (syntax_role * span) list -> 'a1 node list -> 'a1 node
    list **)

let add_roles_head h rs ns =
  if h.pos_records
  then (match ns with
        | [] -> []
        | n :: rest -> (add_roles h rs n) :: rest)
  else ns

(** val hull_pos : coq_PosPolicy -> 'a1 node list -> pos **)

let hull_pos h ns =
  if h.pos_records
  then (match ns with
        | [] -> NoPos
        | first :: _ ->
          (match node_provenance first with
           | Some p ->
             (match node_provenance (last ns first) with
              | Some q ->
                SomePos
                  (prov_at { span_start = p.node_span.span_start; span_stop =
                    q.node_span.span_stop })
              | None -> NoPos)
           | None -> NoPos))
  else NoPos

(** val hull_pos_with : coq_PosPolicy -> 'a1 node list -> pos **)

let hull_pos_with h ns =
  match hull_pos h ns with
  | NoPos -> NoPos
  | SomePos p ->
    (match ns with
     | [] -> SomePos p
     | first :: _ ->
       (match node_provenance first with
        | Some q ->
          SomePos { node_span = p.node_span; syntax_spans = q.syntax_spans;
            part_spans = p.part_spans }
        | None -> SomePos p))

type math_style =
| DisplayMath
| InlineMath

type target =
| Direct of string
| Reference of string

type quote_type =
| SingleQuotes
| DoubleQuotes

type inline =
| Str of string
| Emph of inline node list
| Strong of inline node list
| Highlight of inline node list
| Insert of inline node list
| Delete of inline node list
| Superscript of inline node list
| Subscript of inline node list
| Verbatim of string
| Symbol of string
| Math of math_style * string
| Link of inline node list * target
| Image of inline node list * target
| Span of string * inline node list
| FootnoteReference of string
| UrlLink of string
| EmailLink of string
| Ext_wikilink of bool * string * string option
| RawInline of string * string
| NonBreakingSpace
| Quoted of quote_type * inline node list
| SoftBreak
| HardBreak

type inlines = inline node list

type list_spacing =
| Tight
| Loose

type ordered_list_style =
| Decimal
| LetterUpper
| LetterLower
| RomanUpper
| RomanLower

type ordered_list_delim =
| RightPeriod
| RightParen
| LeftRightParen

type ordered_list_attributes = { ol_style : ordered_list_style;
                                 ol_delim : ordered_list_delim; ol_start :
                                 int }

type task_status =
| Complete
| Incomplete

type callout_fold =
| FoldExpanded
| FoldCollapsed

type align =
| AlignLeft
| AlignRight
| AlignCenter
| AlignDefault

type cell_type =
| HeadCell
| BodyCell

(** val align_eqb : align -> align -> bool **)

let align_eqb a b =
  match a with
  | AlignLeft -> (match b with
                  | AlignLeft -> true
                  | _ -> false)
  | AlignRight -> (match b with
                   | AlignRight -> true
                   | _ -> false)
  | AlignCenter -> (match b with
                    | AlignCenter -> true
                    | _ -> false)
  | AlignDefault -> (match b with
                     | AlignDefault -> true
                     | _ -> false)

type cell =
| Cell of cell_type * align * inlines

type block =
| Para of inlines
| Section of block node list
| Heading of int * inlines
| BlockQuote of block node list
| CodeBlock of string * string
| Div of string * block node list
| OrderedList of ordered_list_attributes * list_spacing * block node list list
| BulletList of list_spacing * block node list list
| TaskList of list_spacing * (task_status * block node list) list
| DefinitionList of list_spacing * (inlines * block node list) list
| ThematicBreak
| Table of inlines * cell list list
| RawBlock of string * string
| FootnoteDef of string * block node list
| RefDef of string * string
| Ext_keyed of inlines * block node
| Ext_callout of string * callout_fold option * inlines * block node list

type blocks = block node list

(** val decorate_head : attr -> blocks -> blocks **)

let decorate_head pending = function
| [] -> []
| n :: rest ->
  let Node (p, a, x) = n in
  (Node (p, (Attr.apply_pending pending a), x)) :: rest

(** val invisible_block : block -> bool **)

let invisible_block = function
| FootnoteDef (_, _) -> true
| RefDef (_, _) -> true
| _ -> false

(** val def_split : blocks -> (inlines * blocks) option **)

let rec def_split = function
| [] -> None
| n :: rest ->
  let Node (q, a, x) = n in
  (match x with
   | Para ils -> Some (ils, rest)
   | _ ->
     if invisible_block x
     then (match def_split rest with
           | Some p ->
             let (ils, more) = p in Some (ils, ((Node (q, a, x)) :: more))
           | None -> None)
     else None)

(** val def_item : blocks -> inlines * blocks **)

let def_item bs =
  match def_split bs with
  | Some r -> r
  | None -> ([], bs)

(** val def_items : blocks list -> (inlines * blocks) list **)

let def_items its =
  map def_item its

(** val task_items :
    task_status list -> blocks list -> (task_status * blocks) list **)

let rec task_items chks = function
| [] -> []
| it :: rest ->
  (match chks with
   | [] -> (Incomplete, it) :: (task_items [] rest)
   | c :: cs -> (c, it) :: (task_items cs rest))

module Shift =
 struct
  (** val of_spot : int -> spot -> spot **)

  let of_spot d s =
    { spot_line = (( + ) d s.spot_line); spot_rem = s.spot_rem }

  (** val of_span : int -> span -> span **)

  let of_span d r =
    { span_start = (of_spot d r.span_start); span_stop =
      (of_spot d r.span_stop) }

  (** val of_parts : int -> parts -> parts **)

  let of_parts d = function
  | PNone -> PNone
  | PItems items -> PItems (map (of_span d) items)
  | PDefItems items ->
    PDefItems
      (map (fun pat ->
        let (y, b) = pat in
        let (i, t) = y in (((of_span d i), (of_span d t)), (of_span d b)))
        items)
  | PTable (cap, rows) ->
    PTable ((option_map (of_span d) cap),
      (map (fun pat ->
        let (r, cs) = pat in ((of_span d r), (map (of_span d) cs))) rows))

  (** val of_pos : int -> pos -> pos **)

  let of_pos d = function
  | NoPos -> NoPos
  | SomePos pr ->
    SomePos { node_span = (of_span d pr.node_span); syntax_spans =
      (map (fun pat -> let (role, r) = pat in (role, (of_span d r)))
        pr.syntax_spans);
      part_spans = (of_parts d pr.part_spans) }

  (** val of_inline : int -> inline -> inline **)

  let rec of_inline d i =
    let go =
      let rec go = function
      | [] -> []
      | n :: rest ->
        let Node (p, a, x) = n in
        (Node ((of_pos d p), a, (of_inline d x))) :: (go rest)
      in go
    in
    (match i with
     | Emph ils -> Emph (go ils)
     | Strong ils -> Strong (go ils)
     | Highlight ils -> Highlight (go ils)
     | Insert ils -> Insert (go ils)
     | Delete ils -> Delete (go ils)
     | Superscript ils -> Superscript (go ils)
     | Subscript ils -> Subscript (go ils)
     | Link (ils, tgt) -> Link ((go ils), tgt)
     | Image (ils, tgt) -> Image ((go ils), tgt)
     | Span (name, ils) -> Span (name, (go ils))
     | Quoted (qt, ils) -> Quoted (qt, (go ils))
     | _ -> i)

  (** val of_inlines : int -> inlines -> inlines **)

  let rec of_inlines d = function
  | [] -> []
  | n :: rest ->
    let Node (p, a, x) = n in
    (Node ((of_pos d p), a, (of_inline d x))) :: (of_inlines d rest)

  (** val of_cell : int -> cell -> cell **)

  let of_cell d = function
  | Cell (ct, al, ils) -> Cell (ct, al, (of_inlines d ils))

  (** val of_block : int -> block -> block **)

  let rec of_block d b =
    let go =
      let rec go = function
      | [] -> []
      | n :: rest ->
        let Node (p, a, x) = n in
        (Node ((of_pos d p), a, (of_block d x))) :: (go rest)
      in go
    in
    let goitems =
      let rec goitems = function
      | [] -> []
      | item :: rest -> (go item) :: (goitems rest)
      in goitems
    in
    (match b with
     | Para ils -> Para (of_inlines d ils)
     | Section bs -> Section (go bs)
     | Heading (lvl, ils) -> Heading (lvl, (of_inlines d ils))
     | BlockQuote bs -> BlockQuote (go bs)
     | Div (name, bs) -> Div (name, (go bs))
     | OrderedList (attrs, sp, items) ->
       OrderedList (attrs, sp, (goitems items))
     | BulletList (sp, items) -> BulletList (sp, (goitems items))
     | TaskList (sp, items) ->
       TaskList (sp,
         (let rec gotasks = function
          | [] -> []
          | p :: rest ->
            let (status, item) = p in (status, (go item)) :: (gotasks rest)
          in gotasks items))
     | DefinitionList (sp, items) ->
       DefinitionList (sp,
         (let rec godefs = function
          | [] -> []
          | p :: rest ->
            let (term, item) = p in
            ((of_inlines d term), (go item)) :: (godefs rest)
          in godefs items))
     | Table (caption, rows) ->
       Table ((of_inlines d caption), (map (map (of_cell d)) rows))
     | FootnoteDef (label, bs) -> FootnoteDef (label, (go bs))
     | Ext_keyed (label, b0) ->
       let Node (p, a, x) = b0 in
       Ext_keyed ((of_inlines d label), (Node ((of_pos d p), a,
       (of_block d x))))
     | Ext_callout (kind, fold, title, bs) ->
       Ext_callout (kind, fold, (of_inlines d title), (go bs))
     | _ -> b)

  (** val of_blocks : int -> blocks -> blocks **)

  let rec of_blocks d = function
  | [] -> []
  | n :: rest ->
    let Node (p, a, b) = n in
    (Node ((of_pos d p), a, (of_block d b))) :: (of_blocks d rest)
 end

(** val rev_chars : char list -> string **)

let rec rev_chars = (fun cs ->
     let n = List.length cs in
     let b = Bytes.create n and i = ref n in
     List.iter (fun c -> decr i; Bytes.set b !i c) cs;
     Bytes.to_string b)

(** val words : (char -> bool) -> string -> string list **)

let words = (fun sep s ->
     let acc = ref [] and word = Buffer.create 32 in
     let flush () =
       if Buffer.length word <> 0 then begin
         acc := Buffer.contents word :: !acc; Buffer.clear word
       end in
     String.iter (fun c -> if sep c then flush () else Buffer.add_char word c) s;
     flush (); List.rev !acc)

(** val is_label_ws : char -> bool **)

let is_label_ws c =
  (||) ((||) ((||) ((=) c ' ') ((=) c '\t')) ((=) c '\r')) ((=) c '\n')

(** val normalize_label : string -> string **)

let normalize_label s =
  String.concat " " (words is_label_ws s)

type note_map = (string * blocks) list

type reference_map = (string * (string * attr)) list

(** val lookup_reference :
    string -> reference_map -> (string * attr) option **)

let lookup_reference label m =
  alist_lookup (normalize_label label) m

type doc = { doc_blocks : blocks; doc_footnotes : note_map;
             doc_references : reference_map;
             doc_auto_references : reference_map;
             doc_auto_identifiers : string list }
