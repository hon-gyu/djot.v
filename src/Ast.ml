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

(** val lookup_attr : string -> attr -> string option **)

let rec lookup_attr k = function
| [] -> None
| p :: rest ->
  let (k', v) = p in if (=) k k' then Some v else lookup_attr k rest

(** val integrate : (string * string) -> attr -> attr **)

let integrate kv kvs =
  let (k, v) = kv in
  (match lookup_attr k kvs with
   | Some v' ->
     if (=) k "class"
     then (k,
            ((^) v ((^) " " v'))) :: (filter (fun p ->
                                       negb ((=) (fst p) "class")) kvs)
     else kvs
   | None -> (k, v) :: kvs)

(** val attr_union : attr -> attr -> attr **)

let attr_union a b =
  fold_right integrate b a

(** val attr_set : string -> string -> attr -> attr **)

let attr_set =
  alist_set

(** val attr_add_class : string -> attr -> attr **)

let attr_add_class v a =
  match lookup_attr "class" a with
  | Some old -> attr_set "class" ((^) old ((^) " " v)) a
  | None -> attr_set "class" v a

(** val attr_put : (string * string) -> attr -> attr **)

let attr_put kv a =
  if (=) (fst kv) "class"
  then attr_add_class (snd kv) a
  else attr_set (fst kv) (snd kv) a

(** val attr_merge : attr -> attr -> attr **)

let attr_merge new0 acc =
  fold_left (fun acc' kv -> attr_put kv acc') new0 acc

(** val attr_apply : attr -> attr -> attr **)

let attr_apply pending a =
  fold_left (fun a' kv -> attr_set (fst kv) (snd kv) a') pending a

type pos =
| NoPos
| SomePos of nat * nat * nat * nat

type 'a node =
| Node of pos * attr * 'a

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
| Node (p, a', x) -> Node (p, (attr_union a' a), x)

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
  let Node (p, a, x) = n in (Node (p, (attr_apply pending a), x)) :: rest

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
