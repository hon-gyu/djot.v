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

type spot = { spot_line : nat; spot_rem : nat }

type span = { span_start : spot; span_stop : spot }

type coq_InlineCursor = { cursor_start : spot; cursor_stop : spot;
                          cursor_origin : spot }

(** val semantic_inline_cursor : coq_InlineCursor **)

let semantic_inline_cursor =
  { cursor_start = { spot_line = O; spot_rem = O }; cursor_stop =
    { spot_line = O; spot_rem = O }; cursor_origin = { spot_line = O;
    spot_rem = O } }

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
  { span_start = { spot_line = O; spot_rem = O }; span_stop = { spot_line =
    O; spot_rem = O } }

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
| Span of inline node list
| FootnoteReference of string
| UrlLink of string
| EmailLink of string
| Wikilink of bool * string * string option
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
                                 nat }

type task_status =
| Complete
| Incomplete

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
| Heading of nat * inlines
| BlockQuote of block node list
| CodeBlock of string * string
| Div of block node list
| OrderedList of ordered_list_attributes * list_spacing * block node list list
| BulletList of list_spacing * block node list list
| TaskList of list_spacing * (task_status * block node list) list
| DefinitionList of list_spacing * (inlines * block node list) list
| ThematicBreak
| Table of inlines option * cell list list
| RawBlock of string * string
| FootnoteDef of string * block node list
| RefDef of string * string
| Keyed of inlines * block node

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

(** val words_aux :
    (char -> bool) -> string -> string -> string list -> string list **)

let rec words_aux sep s cur acc =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ ->
    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

      (fun _ -> acc)
      (fun _ _ -> cur :: acc)
      cur)
    (fun c s' ->
    if sep c
    then ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

            (fun _ -> words_aux sep s' "" acc)
            (fun _ _ -> words_aux sep s' "" (cur :: acc))
            cur)
    else words_aux sep s'
           ((^) cur
             ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

             (c, "")))
           acc)
    s

(** val words : (char -> bool) -> string -> string list **)

let words sep s =
  rev (words_aux sep s "" [])

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
