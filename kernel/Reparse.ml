open Ast
open Datatypes
open InlineTable
open List0
open ListDef
open Step

type piece = { piece_lines : string list; piece_blocks : blocks }

(** val pieces_text : piece list -> string list **)

let pieces_text cs =
  concat (map (fun p -> p.piece_lines) cs)

(** val pieces_tree : piece list -> blocks **)

let pieces_tree cs =
  concat (map (fun p -> p.piece_blocks) cs)

type pending = { pend_lines : string list; pend_blocks : blocks;
                 pend_state : pstate }

(** val fresh : pending **)

let fresh =
  { pend_lines = []; pend_blocks = []; pend_state = (PPara []) }

(** val cut :
    dtable -> bconfig -> string list -> pending -> piece list * pending **)

let rec cut t k ls p =
  match ls with
  | [] -> ([], p)
  | l :: rest ->
    let (out, st) = step t k semantic_line_ix semantic_pos l p.pend_state in
    let lines = l :: p.pend_lines in
    let bs = app p.pend_blocks out in
    if is_idle st
    then let (cs, p') = cut t k rest fresh in
         (({ piece_lines = (rev lines); piece_blocks = bs } :: cs), p')
    else cut t k rest { pend_lines = lines; pend_blocks = bs; pend_state =
           st }

(** val close : dtable -> bconfig -> pending -> piece list **)

let close t k p =
  match p.pend_lines with
  | [] -> []
  | _ :: _ ->
    { piece_lines = (rev p.pend_lines); piece_blocks =
      (app p.pend_blocks (finish t k semantic_pos p.pend_state)) } :: []

(** val pieces : dtable -> bconfig -> string list -> piece list **)

let pieces t k ls =
  let (cs, p) = cut t k ls fresh in app cs (close t k p)

(** val settle : dtable -> bconfig -> pending -> piece list -> piece list **)

let rec settle t k p post =
  if is_idle p.pend_state
  then app (close t k p) post
  else (match post with
        | [] -> close t k p
        | c :: post' ->
          let (cs, p') = cut t k c.piece_lines p in
          app cs (settle t k p' post'))

(** val replace :
    dtable -> bconfig -> piece list -> string list -> piece list -> piece list **)

let replace t k pre new0 post =
  let (cs, p) = cut t k new0 fresh in app pre (app cs (settle t k p post))

(** val splice :
    dtable -> bconfig -> piece list -> int -> int -> string list -> piece list **)

let splice t k cs i j new0 =
  match skipn j cs with
  | [] ->
    ((fun fO fS n -> if n = 0 then fO () else fS (n - 1))
       (fun _ -> replace t k (firstn i cs) new0 [])
       (fun i' ->
       replace t k (firstn i' cs)
         (app (pieces_text (firstn (Stdlib.succ 0) (skipn i' cs))) new0) [])
       i)
  | p :: l -> replace t k (firstn i cs) new0 (p :: l)
