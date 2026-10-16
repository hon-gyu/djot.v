open Ast
open Bool0

(** val list_eqb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eqb f xs ys =
  match xs with
  | [] -> (match ys with
           | [] -> true
           | _ :: _ -> false)
  | x :: xs' ->
    (match ys with
     | [] -> false
     | y :: ys' -> (&&) (f x y) (list_eqb f xs' ys'))

(** val pair_eqb :
    ('a1 -> 'a1 -> bool) -> ('a2 -> 'a2 -> bool) -> ('a1 * 'a2) -> ('a1 * 'a2)
    -> bool **)

let pair_eqb f g p q =
  let (a, b) = p in let (c, d) = q in (&&) (f a c) (g b d)

(** val option_eqb :
    ('a1 -> 'a1 -> bool) -> 'a1 option -> 'a1 option -> bool **)

let option_eqb f x y =
  match x with
  | Some a -> (match y with
               | Some b -> f a b
               | None -> false)
  | None -> (match y with
             | Some _ -> false
             | None -> true)

(** val spot_eqb : spot -> spot -> bool **)

let spot_eqb p q =
  (&&) (( = ) p.spot_line q.spot_line) (( = ) p.spot_rem q.spot_rem)

(** val span_eqb : span -> span -> bool **)

let span_eqb r t =
  (&&) (spot_eqb r.span_start t.span_start) (spot_eqb r.span_stop t.span_stop)

(** val role_eqb : syntax_role -> syntax_role -> bool **)

let role_eqb r t =
  match r with
  | RAttrSpec -> (match t with
                  | RAttrSpec -> true
                  | _ -> false)
  | ROpenFence -> (match t with
                   | ROpenFence -> true
                   | _ -> false)
  | RCloseFence -> (match t with
                    | RCloseFence -> true
                    | _ -> false)

(** val pos_eqb : pos -> pos -> bool **)

let pos_eqb p q =
  match p with
  | NoPos -> (match q with
              | NoPos -> true
              | SomePos _ -> false)
  | SomePos p0 ->
    let { node_span = r; syntax_spans = rs } = p0 in
    (match q with
     | NoPos -> false
     | SomePos p1 ->
       let { node_span = t; syntax_spans = ts } = p1 in
       (&&) (span_eqb r t) (list_eqb (pair_eqb role_eqb span_eqb) rs ts))

(** val attr_eqb : attr -> attr -> bool **)

let attr_eqb =
  list_eqb (pair_eqb (=) (=))

(** val node_eqb : ('a1 -> 'a1 -> bool) -> 'a1 node -> 'a1 node -> bool **)

let node_eqb f m n =
  let Node (p, a, x) = m in
  let Node (q, b, y) = n in (&&) ((&&) (pos_eqb p q) (attr_eqb a b)) (f x y)

(** val math_style_eqb : math_style -> math_style -> bool **)

let math_style_eqb x y =
  match x with
  | DisplayMath -> (match y with
                    | DisplayMath -> true
                    | InlineMath -> false)
  | InlineMath -> (match y with
                   | DisplayMath -> false
                   | InlineMath -> true)

(** val quote_type_eqb : quote_type -> quote_type -> bool **)

let quote_type_eqb x y =
  match x with
  | SingleQuotes ->
    (match y with
     | SingleQuotes -> true
     | DoubleQuotes -> false)
  | DoubleQuotes ->
    (match y with
     | SingleQuotes -> false
     | DoubleQuotes -> true)

(** val target_eqb : target -> target -> bool **)

let target_eqb x y =
  match x with
  | Direct s -> (match y with
                 | Direct t -> (=) s t
                 | Reference _ -> false)
  | Reference s -> (match y with
                    | Direct _ -> false
                    | Reference t -> (=) s t)

(** val inline_eqb : inline -> inline -> bool **)

let rec inline_eqb x y =
  match x with
  | Str s -> (match y with
              | Str t -> (=) s t
              | _ -> false)
  | Emph a ->
    (match y with
     | Emph b -> list_eqb (node_eqb inline_eqb) a b
     | _ -> false)
  | Strong a ->
    (match y with
     | Strong b -> list_eqb (node_eqb inline_eqb) a b
     | _ -> false)
  | Highlight a ->
    (match y with
     | Highlight b -> list_eqb (node_eqb inline_eqb) a b
     | _ -> false)
  | Insert a ->
    (match y with
     | Insert b -> list_eqb (node_eqb inline_eqb) a b
     | _ -> false)
  | Delete a ->
    (match y with
     | Delete b -> list_eqb (node_eqb inline_eqb) a b
     | _ -> false)
  | Superscript a ->
    (match y with
     | Superscript b -> list_eqb (node_eqb inline_eqb) a b
     | _ -> false)
  | Subscript a ->
    (match y with
     | Subscript b -> list_eqb (node_eqb inline_eqb) a b
     | _ -> false)
  | Verbatim s -> (match y with
                   | Verbatim t -> (=) s t
                   | _ -> false)
  | Symbol s -> (match y with
                 | Symbol t -> (=) s t
                 | _ -> false)
  | Math (m, s) ->
    (match y with
     | Math (n, t) -> (&&) (math_style_eqb m n) ((=) s t)
     | _ -> false)
  | Link (a, u) ->
    (match y with
     | Link (b, v) ->
       (&&) (list_eqb (node_eqb inline_eqb) a b) (target_eqb u v)
     | _ -> false)
  | Image (a, u) ->
    (match y with
     | Image (b, v) ->
       (&&) (list_eqb (node_eqb inline_eqb) a b) (target_eqb u v)
     | _ -> false)
  | Span (m, a) ->
    (match y with
     | Span (n, b) -> (&&) ((=) m n) (list_eqb (node_eqb inline_eqb) a b)
     | _ -> false)
  | FootnoteReference s ->
    (match y with
     | FootnoteReference t -> (=) s t
     | _ -> false)
  | UrlLink s -> (match y with
                  | UrlLink t -> (=) s t
                  | _ -> false)
  | EmailLink s -> (match y with
                    | EmailLink t -> (=) s t
                    | _ -> false)
  | RawInline (f, s) ->
    (match y with
     | RawInline (g, t) -> (&&) ((=) f g) ((=) s t)
     | _ -> false)
  | NonBreakingSpace -> (match y with
                         | NonBreakingSpace -> true
                         | _ -> false)
  | Quoted (q, a) ->
    (match y with
     | Quoted (r, b) ->
       (&&) (quote_type_eqb q r) (list_eqb (node_eqb inline_eqb) a b)
     | _ -> false)
  | SoftBreak -> (match y with
                  | SoftBreak -> true
                  | _ -> false)
  | HardBreak -> (match y with
                  | HardBreak -> true
                  | _ -> false)
  | Ext_wikilink (e, s, a) ->
    (match y with
     | Ext_wikilink (f, t, b) ->
       (&&) ((&&) (eqb e f) ((=) s t)) (option_eqb (=) a b)
     | _ -> false)
  | Hole s -> (match y with
               | Hole t -> (=) s t
               | _ -> false)

(** val inlines_eqb : inlines -> inlines -> bool **)

let inlines_eqb =
  list_eqb (node_eqb inline_eqb)

(** val spacing_eqb : list_spacing -> list_spacing -> bool **)

let spacing_eqb x y =
  match x with
  | Tight -> (match y with
              | Tight -> true
              | Loose -> false)
  | Loose -> (match y with
              | Tight -> false
              | Loose -> true)

(** val ol_style_eqb : ordered_list_style -> ordered_list_style -> bool **)

let ol_style_eqb x y =
  match x with
  | Decimal -> (match y with
                | Decimal -> true
                | _ -> false)
  | LetterUpper -> (match y with
                    | LetterUpper -> true
                    | _ -> false)
  | LetterLower -> (match y with
                    | LetterLower -> true
                    | _ -> false)
  | RomanUpper -> (match y with
                   | RomanUpper -> true
                   | _ -> false)
  | RomanLower -> (match y with
                   | RomanLower -> true
                   | _ -> false)

(** val ol_delim_eqb : ordered_list_delim -> ordered_list_delim -> bool **)

let ol_delim_eqb x y =
  match x with
  | RightPeriod -> (match y with
                    | RightPeriod -> true
                    | _ -> false)
  | RightParen -> (match y with
                   | RightParen -> true
                   | _ -> false)
  | LeftRightParen -> (match y with
                       | LeftRightParen -> true
                       | _ -> false)

(** val ol_attrs_eqb :
    ordered_list_attributes -> ordered_list_attributes -> bool **)

let ol_attrs_eqb x y =
  (&&)
    ((&&) (ol_style_eqb x.ol_style y.ol_style)
      (ol_delim_eqb x.ol_delim y.ol_delim))
    (( = ) x.ol_start y.ol_start)

(** val task_eqb : task_status -> task_status -> bool **)

let task_eqb x y =
  match x with
  | Complete -> (match y with
                 | Complete -> true
                 | Incomplete -> false)
  | Incomplete -> (match y with
                   | Complete -> false
                   | Incomplete -> true)

(** val cell_type_eqb : cell_type -> cell_type -> bool **)

let cell_type_eqb x y =
  match x with
  | HeadCell -> (match y with
                 | HeadCell -> true
                 | BodyCell -> false)
  | BodyCell -> (match y with
                 | HeadCell -> false
                 | BodyCell -> true)

(** val cell_eqb : cell -> cell -> bool **)

let cell_eqb x y =
  let Cell (t, a, ils) = x in
  let Cell (u, b, jls) = y in
  (&&) ((&&) (cell_type_eqb t u) (align_eqb a b)) (inlines_eqb ils jls)

(** val fold_eqb : callout_fold -> callout_fold -> bool **)

let fold_eqb x y =
  match x with
  | FoldExpanded ->
    (match y with
     | FoldExpanded -> true
     | FoldCollapsed -> false)
  | FoldCollapsed ->
    (match y with
     | FoldExpanded -> false
     | FoldCollapsed -> true)

(** val block_eqb : block -> block -> bool **)

let rec block_eqb x y =
  match x with
  | Para a -> (match y with
               | Para b -> inlines_eqb a b
               | _ -> false)
  | Section a ->
    (match y with
     | Section b -> list_eqb (node_eqb block_eqb) a b
     | _ -> false)
  | Heading (m, a) ->
    (match y with
     | Heading (n, b) -> (&&) (( = ) m n) (inlines_eqb a b)
     | _ -> false)
  | BlockQuote a ->
    (match y with
     | BlockQuote b -> list_eqb (node_eqb block_eqb) a b
     | _ -> false)
  | CodeBlock (f, s) ->
    (match y with
     | CodeBlock (g, t) -> (&&) ((=) f g) ((=) s t)
     | _ -> false)
  | Div (m, a) ->
    (match y with
     | Div (n, b) -> (&&) ((=) m n) (list_eqb (node_eqb block_eqb) a b)
     | _ -> false)
  | OrderedList (o, s, a) ->
    (match y with
     | OrderedList (p, t, b) ->
       (&&) ((&&) (ol_attrs_eqb o p) (spacing_eqb s t))
         (list_eqb (node_eqb (list_eqb (node_eqb block_eqb))) a b)
     | _ -> false)
  | BulletList (c, s, a) ->
    (match y with
     | BulletList (d, t, b) ->
       (&&) ((&&) ((=) c d) (spacing_eqb s t))
         (list_eqb (node_eqb (list_eqb (node_eqb block_eqb))) a b)
     | _ -> false)
  | TaskList (s, a) ->
    (match y with
     | TaskList (t, b) ->
       (&&) (spacing_eqb s t)
         (list_eqb
           (node_eqb (pair_eqb task_eqb (list_eqb (node_eqb block_eqb)))) a b)
     | _ -> false)
  | DefinitionList (s, a) ->
    (match y with
     | DefinitionList (t, b) ->
       (&&) (spacing_eqb s t)
         (list_eqb
           (node_eqb
             (pair_eqb (node_eqb inlines_eqb)
               (node_eqb (list_eqb (node_eqb block_eqb)))))
           a b)
     | _ -> false)
  | ThematicBreak -> (match y with
                      | ThematicBreak -> true
                      | _ -> false)
  | Table (c, r) ->
    (match y with
     | Table (d, t) ->
       (&&) (node_eqb inlines_eqb c d)
         (list_eqb (node_eqb (list_eqb (node_eqb cell_eqb))) r t)
     | _ -> false)
  | RawBlock (f, s) ->
    (match y with
     | RawBlock (g, t) -> (&&) ((=) f g) ((=) s t)
     | _ -> false)
  | FootnoteDef (m, a) ->
    (match y with
     | FootnoteDef (n, b) ->
       (&&) ((=) m n) (list_eqb (node_eqb block_eqb) a b)
     | _ -> false)
  | RefDef (l, s) ->
    (match y with
     | RefDef (m, t) -> (&&) ((=) l m) ((=) s t)
     | _ -> false)
  | AttrBlock -> (match y with
                  | AttrBlock -> true
                  | _ -> false)
  | Ext_keyed (l, a) ->
    (match y with
     | Ext_keyed (m, b) -> (&&) (inlines_eqb l m) (node_eqb block_eqb a b)
     | _ -> false)
  | Ext_callout (k, f, t, a) ->
    (match y with
     | Ext_callout (l, g, u, b) ->
       (&&)
         ((&&) ((&&) ((=) k l) (option_eqb fold_eqb f g)) (inlines_eqb t u))
         (list_eqb (node_eqb block_eqb) a b)
     | _ -> false)

(** val blocks_eqb : blocks -> blocks -> bool **)

let blocks_eqb =
  list_eqb (node_eqb block_eqb)
