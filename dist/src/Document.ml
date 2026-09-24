open Ast
open Datatypes
open InlineTable
open List0
open ListDef
open Nat0
open Step
open Strings

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
   | Span ils -> go ils
   | UrlLink s -> s
   | EmailLink s -> s
   | Wikilink (_, t, al) -> wiki_display t al
   | RawInline (_, s) -> s
   | Quoted (_, ils) -> go ils
   | SoftBreak -> nl
   | HardBreak -> nl
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

(** val id_taken : string list -> string -> bool **)

let id_taken used s =
  existsb ((=) s) used

(** val id_candidate : string -> nat -> string **)

let id_candidate base i =
  if eqb i O
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

(** val unique_id_from : nat -> nat -> string list -> string -> string **)

let rec unique_id_from fuel i used base =
  let cand = id_candidate base i in
  (match fuel with
   | O -> cand
   | S f ->
     if (&&) (nonempty_str cand) (negb (id_taken used cand))
     then cand
     else unique_id_from f (S i) used base)

(** val unique_id : string list -> string -> string **)

let unique_id used base =
  unique_id_from (S (S (length used))) O used base

type id_state = { id_used : string list; id_refs : reference_map }

(** val id_state_init : id_state **)

let id_state_init =
  { id_used = []; id_refs = [] }

(** val add_auto_ref : string -> string -> id_state -> id_state **)

let add_auto_ref label ident st =
  if existsb (fun p -> (=) (fst p) label) st.id_refs
  then st
  else { id_used = st.id_used; id_refs = ((label, (((^) "#" ident),
         [])) :: st.id_refs) }

(** val register_id : attr -> id_state -> id_state **)

let register_id a st =
  match alist_lookup "id" a with
  | Some ident -> { id_used = (ident :: st.id_used); id_refs = st.id_refs }
  | None -> st

(** val assign_heading_id :
    pos -> attr -> nat -> inlines -> id_state -> id_state * block node **)

let assign_heading_id p a lvl ils st =
  let text = inlines_text ils in
  (match alist_lookup "id" a with
   | Some ident ->
     ((add_auto_ref (normalize_label text) ident (register_id a st)), (Node
       (p, a, (Heading (lvl, ils)))))
   | None ->
     let ident = unique_id st.id_used (id_base text) in
     let st' = { id_used = (ident :: st.id_used); id_refs = st.id_refs } in
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
     | Div bs ->
       let (st', bs') = go bs (register_id a st) in
       (st', (Node (p, a, (Div bs'))))
     | OrderedList (oa, sp, items) ->
       let (st', items') =
         let rec goit its s =
           match its with
           | [] -> (s, [])
           | it :: rest ->
             let (s1, it1) = go it s in
             let (s2, rest1) = goit rest s1 in (s2, (it1 :: rest1))
         in goit items (register_id a st)
       in
       (st', (Node (p, a, (OrderedList (oa, sp, items')))))
     | BulletList (sp, items) ->
       let (st', items') =
         let rec goit its s =
           match its with
           | [] -> (s, [])
           | it :: rest ->
             let (s1, it1) = go it s in
             let (s2, rest1) = goit rest s1 in (s2, (it1 :: rest1))
         in goit items (register_id a st)
       in
       (st', (Node (p, a, (BulletList (sp, items')))))
     | TaskList (sp, items) ->
       let (st', items') =
         let rec got its s =
           match its with
           | [] -> (s, [])
           | p0 :: rest ->
             let (chk, it) = p0 in
             let (s1, it1) = go it s in
             let (s2, rest1) = got rest s1 in (s2, ((chk, it1) :: rest1))
         in got items (register_id a st)
       in
       (st', (Node (p, a, (TaskList (sp, items')))))
     | DefinitionList (sp, items) ->
       let (st', items') =
         let rec god its s =
           match its with
           | [] -> (s, [])
           | p0 :: rest ->
             let (term, it) = p0 in
             let (s1, it1) = go it s in
             let (s2, rest1) = god rest s1 in (s2, ((term, it1) :: rest1))
         in god items (register_id a st)
       in
       (st', (Node (p, a, (DefinitionList (sp, items')))))
     | FootnoteDef (label, bs) ->
       let (st', bs') = go bs (register_id a st) in
       (st', (Node (p, a, (FootnoteDef (label, bs')))))
     | Keyed (label, b0) ->
       let Node (p', a', x) = b0 in
       let (st', n') = of_block x p' a' (register_id a st) in
       (st', (Node (p, a, (Keyed (label, n')))))
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

type sect_state = ((nat * attr) * blocks) list

(** val sect_init : sect_state **)

let sect_init =
  ((O, []), []) :: []

(** val section_node : coq_PosPolicy -> attr -> blocks -> block node **)

let section_node p a bs =
  Node ((hull_pos_with p bs), a, (Section bs))

(** val close_ge :
    coq_PosPolicy -> nat -> blocks -> sect_state -> sect_state **)

let rec close_ge p lvl pending = function
| [] -> []
| p0 :: outer ->
  let (p1, acc) = p0 in
  let (l, a) = p1 in
  (match outer with
   | [] -> ((l, a), (app pending acc)) :: []
   | _ :: _ ->
     if leb lvl l
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
        | it :: rest ->
          goit rest
            (let rec go' ns acc' =
               match ns with
               | [] -> acc'
               | n :: more ->
                 let Node (p', a', x) = n in go' more (of_block x p' a' acc')
             in go' it acc)
      in goit
    in
    (match b with
     | Section bs -> go bs m
     | BlockQuote bs -> go bs m
     | Div bs -> go bs m
     | OrderedList (_, _, items) -> goit items m
     | BulletList (_, items) -> goit items m
     | TaskList (_, items) ->
       let rec got its acc =
         match its with
         | [] -> acc
         | p0 :: rest ->
           let (_, it) = p0 in
           got rest
             (let rec go' ns acc' =
                match ns with
                | [] -> acc'
                | n :: more ->
                  let Node (p', a', x) = n in go' more (of_block x p' a' acc')
              in go' it acc)
       in got items m
     | DefinitionList (_, items) ->
       let rec god its acc =
         match its with
         | [] -> acc
         | p0 :: rest ->
           let (_, it) = p0 in
           god rest
             (let rec go' ns acc' =
                match ns with
                | [] -> acc'
                | n :: more ->
                  let Node (p', a', x) = n in go' more (of_block x p' a' acc')
              in go' it acc)
       in god items m
     | FootnoteDef (_, bs) -> go bs m
     | Keyed (_, b0) -> let Node (p', a', x) = b0 in of_block x p' a' m
     | _ -> add_ref p a b m)

  (** val of_list : blocks -> reference_map -> reference_map **)

  let rec of_list ns m =
    match ns with
    | [] -> m
    | n :: rest -> let Node (p, a, b) = n in of_list rest (of_block b p a m)
 end

module Notes =
 struct
  (** val of_block :
      block -> pos -> attr -> note_map -> note_map * block node option **)

  let rec of_block b p a m =
    let go =
      let rec go ns acc =
        match ns with
        | [] -> (acc, [])
        | n :: rest ->
          let Node (p', a', x) = n in
          let (acc1, n1) = of_block x p' a' acc in
          let (acc2, rest1) = go rest acc1 in
          (match n1 with
           | Some n0 -> (acc2, (n0 :: rest1))
           | None -> (acc2, rest1))
      in go
    in
    let goit =
      let rec goit its acc =
        match its with
        | [] -> (acc, [])
        | it :: rest ->
          let (acc1, it1) = go it acc in
          let (acc2, rest1) = goit rest acc1 in (acc2, (it1 :: rest1))
      in goit
    in
    (match b with
     | BlockQuote bs ->
       let (m', bs') = go bs m in (m', (Some (Node (p, a, (BlockQuote bs')))))
     | Div bs ->
       let (m', bs') = go bs m in (m', (Some (Node (p, a, (Div bs')))))
     | OrderedList (oa, sp, items) ->
       let (m', items') = goit items m in
       (m', (Some (Node (p, a, (OrderedList (oa, sp, items'))))))
     | BulletList (sp, items) ->
       let (m', items') = goit items m in
       (m', (Some (Node (p, a, (BulletList (sp, items'))))))
     | TaskList (sp, items) ->
       let (m', items') =
         let rec got its acc =
           match its with
           | [] -> (acc, [])
           | p0 :: rest ->
             let (chk, it) = p0 in
             let (acc1, it1) = go it acc in
             let (acc2, rest1) = got rest acc1 in
             (acc2, ((chk, it1) :: rest1))
         in got items m
       in
       (m', (Some (Node (p, a, (TaskList (sp, items'))))))
     | DefinitionList (sp, items) ->
       let (m', items') =
         let rec god its acc =
           match its with
           | [] -> (acc, [])
           | p0 :: rest ->
             let (term, it) = p0 in
             let (acc1, it1) = go it acc in
             let (acc2, rest1) = god rest acc1 in
             (acc2, ((term, it1) :: rest1))
         in god items m
       in
       (m', (Some (Node (p, a, (DefinitionList (sp, items'))))))
     | FootnoteDef (label, bs) ->
       let (m', bs') = go bs m in
       ((alist_set (normalize_label label) bs' m'), None)
     | Keyed (label, b0) ->
       let Node (p', a', x) = b0 in
       let (m', o) = of_block x p' a' m in
       (m',
       (match o with
        | Some n' -> Some (Node (p, a, (Keyed (label, n'))))
        | None -> None))
     | _ -> (m, (Some (Node (p, a, b)))))

  (** val of_list : blocks -> note_map -> note_map * blocks **)

  let rec of_list ns m =
    match ns with
    | [] -> (m, [])
    | n :: rest ->
      let Node (p, a, b) = n in
      let (m1, n1) = of_block b p a m in
      let (m2, rest1) = of_list rest m1 in
      (match n1 with
       | Some n0 -> (m2, (n0 :: rest1))
       | None -> (m2, rest1))
 end

(** val doc_pass : coq_PosPolicy -> blocks -> doc **)

let doc_pass p bs =
  let (st, bs') = Ids.of_list bs id_state_init in
  let (notes, visible) = Notes.of_list bs' [] in
  { doc_blocks = (sectionize p visible); doc_footnotes = notes;
  doc_references = (Refs.of_list bs' []); doc_auto_references =
  (rev st.id_refs); doc_auto_identifiers = (rev st.id_used) }

(** val parse_doc : dtable -> bconfig -> coq_PosPolicy -> string -> doc **)

let parse_doc t k p s =
  doc_pass p (parse_blocks t k semantic_line_ix p s)

(** val parse_doc_located : dtable -> bconfig -> string -> doc **)

let parse_doc_located t k s =
  doc_pass located_pos (parse_blocks_located t k s)
