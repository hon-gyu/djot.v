open Ast
open Datatypes
open FMapAVL
open InlineTable
open List0
open ListDef
open MSetAVL
open Nat0
open OrderedTypeEx
open OrdersEx
open Reparse
open Step
open Strings

module StrSet = Make(String_as_OT)

module StrMap = FMapAVL.Make(OrderedTypeEx.String_as_OT)

(** val inline_text : inline -> string **)

let rec inline_text il =
  let go =
    let rec go = function
    | [] -> ""
    | n :: rest -> let Node (_, _, x) = n in (^) (inline_text x) (go rest)
    in go
  in
  (match il with
   | Str s -> s
   | Emph ils -> go ils
   | Strong ils -> go ils
   | Highlight ils -> go ils
   | Insert ils -> go ils
   | Delete ils -> go ils
   | Superscript ils -> go ils
   | Subscript ils -> go ils
   | Verbatim s -> s
   | Math (_, s) -> s
   | Link (ils, _) -> go ils
   | Image (ils, _) -> go ils
   | Span (_, ils) -> go ils
   | UrlLink s -> s
   | EmailLink s -> s
   | RawInline (_, s) -> s
   | Quoted (_, ils) -> go ils
   | SoftBreak -> nl
   | HardBreak -> nl
   | Ext_wikilink (_, t0, al) -> wiki_display t0 al
   | _ -> "")

(** val inlines_text : inlines -> string **)

let inlines_text ils =
  String.concat "" (map (fun n -> inline_text (node_contents n)) ils)

(** val is_id_sep : char -> bool **)

let is_id_sep c =
  (||)
    ((||)
      ((||)
        ((||) ((||) ((||) ((=) c '\t') ((=) c '\n')) ((=) c '\011'))
          ((=) c '\012'))
        ((=) c '\r'))
      ((=) c ' '))
    ((||)
      ((||)
        ((||)
          ((||)
            ((||)
              ((||)
                ((||)
                  ((||)
                    ((||)
                      ((||)
                        ((||)
                          ((||)
                            ((||)
                              ((||)
                                ((||)
                                  ((||)
                                    ((||)
                                      ((||)
                                        ((||)
                                          ((||)
                                            ((||)
                                              ((||)
                                                ((||)
                                                  ((||)
                                                    ((||) ((=) c '[')
                                                      ((=) c ']'))
                                                    ((=) c '~'))
                                                  ((=) c '!'))
                                                ((=) c '@'))
                                              ((=) c '#'))
                                            ((=) c '$'))
                                          ((=) c '%'))
                                        ((=) c '^'))
                                      ((=) c '&'))
                                    ((=) c '*'))
                                  ((=) c '('))
                                ((=) c ')'))
                              ((=) c '{'))
                            ((=) c '}'))
                          ((=) c '`'))
                        ((=) c ','))
                      ((=) c '.'))
                    ((=) c '<'))
                  ((=) c '>'))
                ((=) c '\\'))
              ((=) c '|'))
            ((=) c '='))
          ((=) c '+'))
        ((=) c '/'))
      ((=) c '?'))

(** val id_base : string -> string **)

let id_base s =
  String.concat "-" (words is_id_sep s)

(** val id_candidate : string -> int -> string **)

let id_candidate base i =
  if ( = ) i 0
  then base
  else (^)
         ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

            (fun _ -> "s")
            (fun _ _ -> base)
            base)
         ((^) "-" (nat_str i))

type id_state = { id_used : string list; id_refs : reference_map;
                  id_count : int; id_used_set : StrSet.t;
                  id_ref_labels : StrSet.t; id_next : int StrMap.t;
                  id_derived : string list }

(** val id_state_init : id_state **)

let id_state_init =
  { id_used = []; id_refs = []; id_count = 0; id_used_set = StrSet.empty;
    id_ref_labels = StrSet.empty; id_next = StrMap.empty; id_derived = [] }

(** val take_id : string -> id_state -> id_state **)

let take_id ident st =
  { id_used = (ident :: st.id_used); id_refs = st.id_refs; id_count =
    (Stdlib.succ st.id_count); id_used_set =
    (StrSet.add ident st.id_used_set); id_ref_labels = st.id_ref_labels;
    id_next = st.id_next; id_derived = st.id_derived }

(** val add_auto_ref : string -> string -> id_state -> id_state **)

let add_auto_ref label ident st =
  if StrSet.mem label st.id_ref_labels
  then st
  else { id_used = st.id_used; id_refs = ((label, (((^) "#" ident),
         [])) :: st.id_refs); id_count = st.id_count; id_used_set =
         st.id_used_set; id_ref_labels = (StrSet.add label st.id_ref_labels);
         id_next = st.id_next; id_derived = st.id_derived }

(** val register_id : attr -> id_state -> id_state **)

let register_id a st =
  match alist_lookup "id" a with
  | Some ident -> take_id ident st
  | None -> st

(** val fresh_index : StrSet.t -> string -> int -> int -> int **)

let rec fresh_index taken base fuel i =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> i)
    (fun f ->
    let cand = id_candidate base i in
    if (&&) (nonempty_str cand) (negb (StrSet.mem cand taken))
    then i
    else fresh_index taken base f (Stdlib.succ i))
    fuel

(** val fresh_for : id_state -> string -> int **)

let fresh_for st base =
  let start = match StrMap.find base st.id_next with
              | Some n -> n
              | None -> 0
  in
  fresh_index st.id_used_set base
    (sub (Stdlib.succ (Stdlib.succ st.id_count)) start) start

(** val assign_heading_id :
    pos -> attr -> int -> inlines -> id_state -> id_state * block node **)

let assign_heading_id p a lvl ils st =
  let text = inlines_text ils in
  (match alist_lookup "id" a with
   | Some ident ->
     ((add_auto_ref (normalize_label text) ident (register_id a st)), (Node
       (p, a, (Heading (lvl, ils)))))
   | None ->
     let base = id_base text in
     let i = fresh_for st base in
     let ident = id_candidate base i in
     let st1 = take_id ident st in
     let st' = { id_used = st1.id_used; id_refs = st1.id_refs; id_count =
       st1.id_count; id_used_set = st1.id_used_set; id_ref_labels =
       st1.id_ref_labels; id_next =
       (StrMap.add base (Stdlib.succ i) st1.id_next); id_derived =
       (ident :: st1.id_derived) }
     in
     ((add_auto_ref (normalize_label text) ident st'), (Node (p, (("id",
     ident) :: a), (Heading (lvl, ils))))))

module Ids =
 struct
  (** val of_block :
      block -> pos -> attr -> id_state -> id_state * block node **)

  let rec of_block b p a st =
    let go =
      let rec go ns s =
        match ns with
        | [] -> (s, [])
        | n :: rest ->
          let Node (p', a', x) = n in
          let (s1, n1) = of_block x p' a' s in
          let (s2, rest1) = go rest s1 in (s2, (n1 :: rest1))
      in go
    in
    (match b with
     | Heading (lvl, ils) -> assign_heading_id p a lvl ils st
     | BlockQuote bs ->
       let (st', bs') = go bs (register_id a st) in
       (st', (Node (p, a, (BlockQuote bs'))))
     | Div (name, bs) ->
       let (st', bs') = go bs (register_id a st) in
       (st', (Node (p, a, (Div (name, bs')))))
     | OrderedList (oa, sp, items) ->
       let (st', items') =
         let rec goit its s =
           match its with
           | [] -> (s, [])
           | n :: rest ->
             let Node (ip, ia, it) = n in
             let (s1, it1) = go it s in
             let (s2, rest1) = goit rest s1 in
             (s2, ((Node (ip, ia, it1)) :: rest1))
         in goit items (register_id a st)
       in
       (st', (Node (p, a, (OrderedList (oa, sp, items')))))
     | BulletList (bc, sp, items) ->
       let (st', items') =
         let rec goit its s =
           match its with
           | [] -> (s, [])
           | n :: rest ->
             let Node (ip, ia, it) = n in
             let (s1, it1) = go it s in
             let (s2, rest1) = goit rest s1 in
             (s2, ((Node (ip, ia, it1)) :: rest1))
         in goit items (register_id a st)
       in
       (st', (Node (p, a, (BulletList (bc, sp, items')))))
     | TaskList (sp, items) ->
       let (st', items') =
         let rec got its s =
           match its with
           | [] -> (s, [])
           | n :: rest ->
             let Node (ip, ia, x) = n in
             let (chk, it) = x in
             let (s1, it1) = go it s in
             let (s2, rest1) = got rest s1 in
             (s2, ((Node (ip, ia, (chk, it1))) :: rest1))
         in got items (register_id a st)
       in
       (st', (Node (p, a, (TaskList (sp, items')))))
     | DefinitionList (sp, items) ->
       let (st', items') =
         let rec god its s =
           match its with
           | [] -> (s, [])
           | n :: rest ->
             let Node (ip, ia, x) = n in
             let (term, n0) = x in
             let Node (dp, da, it) = n0 in
             let (s1, it1) = go it s in
             let (s2, rest1) = god rest s1 in
             (s2, ((Node (ip, ia, (term, (Node (dp, da, it1))))) :: rest1))
         in god items (register_id a st)
       in
       (st', (Node (p, a, (DefinitionList (sp, items')))))
     | FootnoteDef (label, bs) ->
       let (st', bs') = go bs (register_id a st) in
       (st', (Node (p, a, (FootnoteDef (label, bs')))))
     | Ext_keyed (label, b0) ->
       let Node (p', a', x) = b0 in
       let (st', n') = of_block x p' a' (register_id a st) in
       (st', (Node (p, a, (Ext_keyed (label, n')))))
     | Ext_callout (kind, fold0, title, bs) ->
       let (st', bs') = go bs (register_id a st) in
       (st', (Node (p, a, (Ext_callout (kind, fold0, title, bs')))))
     | _ -> ((register_id a st), (Node (p, a, b))))

  (** val of_node : block node -> id_state -> id_state * block node **)

  let of_node n st =
    let Node (p, a, b) = n in of_block b p a st

  (** val of_list : blocks -> id_state -> id_state * blocks **)

  let rec of_list ns st =
    match ns with
    | [] -> (st, [])
    | n :: rest ->
      let (st1, n1) = of_node n st in
      let (st2, rest1) = of_list rest st1 in (st2, (n1 :: rest1))
 end

type sect_state = ((int * attr) * blocks) list

(** val sect_init : sect_state **)

let sect_init =
  ((0, []), []) :: []

(** val section_node : coq_PosPolicy -> attr -> blocks -> block node **)

let section_node p a bs =
  Node ((hull_pos_with p bs), a, (Section bs))

(** val close_ge :
    coq_PosPolicy -> int -> blocks -> sect_state -> sect_state **)

let rec close_ge p lvl pending = function
| [] -> []
| p0 :: outer ->
  let (p1, acc) = p0 in
  let (l, a) = p1 in
  (match outer with
   | [] -> ((l, a), (app pending acc)) :: []
   | _ :: _ ->
     if ( <= ) lvl l
     then close_ge p lvl ((section_node p a (rev (app pending acc))) :: [])
            outer
     else ((l, a), (app pending acc)) :: outer)

(** val close_all : coq_PosPolicy -> blocks -> sect_state -> sect_state **)

let rec close_all p pending = function
| [] -> []
| p0 :: outer ->
  let (p1, acc) = p0 in
  let (l, a) = p1 in
  (match outer with
   | [] -> ((l, a), (app pending acc)) :: []
   | _ :: _ ->
     close_all p ((section_node p a (rev (app pending acc))) :: []) outer)

(** val sect_push : block node -> sect_state -> sect_state **)

let sect_push b = function
| [] -> []
| p :: rest -> let (p0, acc) = p in (p0, (b :: acc)) :: rest

(** val sect_step :
    coq_PosPolicy -> sect_state -> block node -> sect_state **)

let sect_step p stk n = match n with
| Node (p0, a, x) ->
  (match x with
   | Heading (lvl, ils) ->
     ((lvl, a), ((Node (p0, [], (Heading (lvl,
       ils)))) :: [])) :: (close_ge p lvl [] stk)
   | _ -> sect_push n stk)

(** val sect_bottom : sect_state -> blocks **)

let rec sect_bottom = function
| [] -> []
| p :: outer ->
  let (_, acc) = p in
  (match outer with
   | [] -> rev acc
   | _ :: _ -> sect_bottom outer)

(** val sectionize : coq_PosPolicy -> blocks -> blocks **)

let sectionize p bs =
  sect_bottom (close_all p [] (fold_left (sect_step p) bs sect_init))

(** val add_ref : pos -> attr -> block -> reference_map -> reference_map **)

let add_ref _ a b m =
  match b with
  | RefDef (label, dest) ->
    if nonempty_str label
    then alist_set (normalize_label label) (dest, a) m
    else m
  | _ -> m

module Refs =
 struct
  (** val of_block :
      block -> pos -> attr -> reference_map -> reference_map **)

  let rec of_block b p a m =
    let go =
      let rec go ns acc =
        match ns with
        | [] -> acc
        | n :: rest ->
          let Node (p', a', x) = n in go rest (of_block x p' a' acc)
      in go
    in
    let goit =
      let rec goit its acc =
        match its with
        | [] -> acc
        | n :: rest ->
          let Node (_, _, it) = n in
          goit rest
            (let rec go' ns acc' =
               match ns with
               | [] -> acc'
               | n0 :: more ->
                 let Node (p', a', x) = n0 in go' more (of_block x p' a' acc')
             in go' it acc)
      in goit
    in
    (match b with
     | Section bs -> go bs m
     | BlockQuote bs -> go bs m
     | Div (_, bs) -> go bs m
     | OrderedList (_, _, items) -> goit items m
     | BulletList (_, _, items) -> goit items m
     | TaskList (_, items) ->
       let rec got its acc =
         match its with
         | [] -> acc
         | n :: rest ->
           let Node (_, _, x) = n in
           let (_, it) = x in
           got rest
             (let rec go' ns acc' =
                match ns with
                | [] -> acc'
                | n0 :: more ->
                  let Node (p', a', x0) = n0 in
                  go' more (of_block x0 p' a' acc')
              in go' it acc)
       in got items m
     | DefinitionList (_, items) ->
       let rec god its acc =
         match its with
         | [] -> acc
         | n :: rest ->
           let Node (_, _, x) = n in
           let (_, n1) = x in
           let Node (_, _, it) = n1 in
           god rest
             (let rec go' ns acc' =
                match ns with
                | [] -> acc'
                | n0 :: more ->
                  let Node (p', a', x0) = n0 in
                  go' more (of_block x0 p' a' acc')
              in go' it acc)
       in god items m
     | FootnoteDef (_, bs) -> go bs m
     | Ext_keyed (_, b0) -> let Node (p', a', x) = b0 in of_block x p' a' m
     | Ext_callout (_, _, _, bs) -> go bs m
     | _ -> add_ref p a b m)

  (** val of_list : blocks -> reference_map -> reference_map **)

  let rec of_list ns m =
    match ns with
    | [] -> m
    | n :: rest -> let Node (p, a, b) = n in of_list rest (of_block b p a m)
 end

module Notes =
 struct
  (** val of_block : block -> note_map -> note_map **)

  let rec of_block b m =
    let go =
      let rec go ns acc =
        match ns with
        | [] -> acc
        | n :: rest -> let Node (_, _, x) = n in go rest (of_block x acc)
      in go
    in
    let goit =
      let rec goit its acc =
        match its with
        | [] -> acc
        | n :: rest ->
          let Node (_, _, it) = n in
          goit rest
            (let rec go' ns acc' =
               match ns with
               | [] -> acc'
               | n0 :: more ->
                 let Node (_, _, x) = n0 in go' more (of_block x acc')
             in go' it acc)
      in goit
    in
    (match b with
     | Section bs -> go bs m
     | BlockQuote bs -> go bs m
     | Div (_, bs) -> go bs m
     | OrderedList (_, _, items) -> goit items m
     | BulletList (_, _, items) -> goit items m
     | TaskList (_, items) ->
       let rec got its acc =
         match its with
         | [] -> acc
         | n :: rest ->
           let Node (_, _, x) = n in
           let (_, it) = x in
           got rest
             (let rec go' ns acc' =
                match ns with
                | [] -> acc'
                | n0 :: more ->
                  let Node (_, _, x0) = n0 in go' more (of_block x0 acc')
              in go' it acc)
       in got items m
     | DefinitionList (_, items) ->
       let rec god its acc =
         match its with
         | [] -> acc
         | n :: rest ->
           let Node (_, _, x) = n in
           let (_, n1) = x in
           let Node (_, _, it) = n1 in
           god rest
             (let rec go' ns acc' =
                match ns with
                | [] -> acc'
                | n0 :: more ->
                  let Node (_, _, x0) = n0 in go' more (of_block x0 acc')
              in go' it acc)
       in god items m
     | FootnoteDef (label, bs) ->
       alist_set (normalize_label label) bs (go bs m)
     | Ext_keyed (_, b0) -> let Node (_, _, x) = b0 in of_block x m
     | Ext_callout (_, _, _, bs) -> go bs m
     | _ -> m)

  (** val of_list : blocks -> note_map -> note_map **)

  let rec of_list ns m =
    match ns with
    | [] -> m
    | n :: rest -> let Node (_, _, b) = n in of_list rest (of_block b m)
 end

(** val doc_pass : coq_PosPolicy -> blocks -> doc **)

let doc_pass p bs =
  let (st, bs') = Ids.of_list bs id_state_init in
  { doc_blocks = (sectionize p bs'); doc_footnotes = (Notes.of_list bs' []);
  doc_references = (Refs.of_list bs' []); doc_auto_references =
  (rev st.id_refs); doc_auto_identifiers = (rev st.id_derived) }

(** val parse_doc : dtable -> bconfig -> coq_PosPolicy -> string -> doc **)

let parse_doc t0 k p s =
  doc_pass p (parse_blocks t0 k semantic_line_ix p s)

(** val parse_doc_located : dtable -> bconfig -> string -> doc **)

let parse_doc_located t0 k s =
  doc_pass located_pos (parse_blocks_located t0 k s)

(** val unsection_block : block -> pos -> attr -> blocks **)

let rec unsection_block b p a =
  match b with
  | Section inner ->
    (match let rec go = function
           | [] -> []
           | n :: rest ->
             let Node (p', a', x) = n in
             app (unsection_block x p' a') (go rest)
           in go inner with
     | [] -> []
     | n :: rest ->
       let Node (hp, a0, x) = n in
       (match x with
        | Heading (lvl, ils) -> (Node (hp, a, (Heading (lvl, ils)))) :: rest
        | x0 -> (Node (hp, a0, x0)) :: rest))
  | _ -> (Node (p, a, b)) :: []

(** val unsection : blocks -> blocks **)

let unsection bs =
  flat_map (fun n -> let Node (p, a, b) = n in unsection_block b p a) bs
