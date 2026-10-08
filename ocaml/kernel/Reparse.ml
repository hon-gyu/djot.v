open Ast
open Datatypes
open InlineTable
open List0
open ListDef
open Step
open Strings

type piece = { piece_lines : string list; piece_blocks : blocks }

(** val pieces_text : piece list -> string list **)

let pieces_text cs =
  concat (map (fun p -> p.piece_lines) cs)

(** val pieces_tree : piece list -> blocks **)

let pieces_tree cs =
  concat (map (fun p -> p.piece_blocks) cs)

type pending = { pend_lines : string list; pend_blocks : blocks;
                 pend_state : pstate; pend_count : int }

(** val fresh : pending **)

let fresh =
  { pend_lines = []; pend_blocks = []; pend_state = (PPara []); pend_count =
    0 }

(** val cut :
    (int -> string -> pstate -> blocks * pstate) -> string list -> pending ->
    piece list * pending **)

let rec cut stp ls p =
  match ls with
  | [] -> ([], p)
  | l :: rest ->
    let (out, st) = stp p.pend_count l p.pend_state in
    let lines = l :: p.pend_lines in
    let bs = app p.pend_blocks out in
    if is_idle st
    then let (cs, p') = cut stp rest fresh in
         (({ piece_lines = (rev lines); piece_blocks = bs } :: cs), p')
    else cut stp rest { pend_lines = lines; pend_blocks = bs; pend_state = st;
           pend_count = (Stdlib.succ p.pend_count) }

(** val close : (pstate -> blocks) -> pending -> piece list **)

let close fin p =
  match p.pend_lines with
  | [] -> []
  | _ :: _ ->
    { piece_lines = (rev p.pend_lines); piece_blocks =
      (app p.pend_blocks (fin p.pend_state)) } :: []

(** val pieces :
    (int -> string -> pstate -> blocks * pstate) -> (pstate -> blocks) ->
    string list -> piece list **)

let pieces stp fin ls =
  let (cs, p) = cut stp ls fresh in app cs (close fin p)

(** val settle :
    (int -> string -> pstate -> blocks * pstate) -> (pstate -> blocks) ->
    pending -> piece list -> piece list **)

let rec settle stp fin p post =
  if is_idle p.pend_state
  then app (close fin p) post
  else (match post with
        | [] -> close fin p
        | c :: post' ->
          let (cs, p') = cut stp c.piece_lines p in
          app cs (settle stp fin p' post'))

(** val replace :
    (int -> string -> pstate -> blocks * pstate) -> (pstate -> blocks) ->
    piece list -> string list -> piece list -> piece list **)

let replace stp fin pre new0 post =
  let (cs, p) = cut stp new0 fresh in app pre (app cs (settle stp fin p post))

(** val splice :
    (int -> string -> pstate -> blocks * pstate) -> (pstate -> blocks) ->
    piece list -> int -> int -> string list -> piece list **)

let splice stp fin cs i j new0 =
  match skipn j cs with
  | [] ->
    ((fun fO fS n -> if n = 0 then fO () else fS (n - 1))
       (fun _ -> replace stp fin (firstn i cs) new0 [])
       (fun i' ->
       replace stp fin (firstn i' cs)
         (app (pieces_text (firstn (Stdlib.succ 0) (skipn i' cs))) new0) [])
       i)
  | p :: l -> replace stp fin (firstn i cs) new0 (p :: l)

(** val sem_step :
    dtable -> bconfig -> int -> string -> pstate -> blocks * pstate **)

let sem_step t k _ l st =
  step t k semantic_line_ix semantic_pos l st

(** val loc_step :
    dtable -> bconfig -> int -> string -> pstate -> blocks * pstate **)

let loc_step t k k0 l st =
  step t k k0 located_pos l st

(** val loc_pieces : dtable -> bconfig -> string list -> piece list **)

let loc_pieces t k ls =
  pieces (loc_step t k) (finish t k located_pos) ls

(** val assemble : int -> piece list -> blocks **)

let rec assemble off = function
| [] -> []
| c :: rest ->
  app (Shift.of_blocks off c.piece_blocks)
    (assemble (( + ) off (length c.piece_lines)) rest)

(** val parse_blocks_located : dtable -> bconfig -> string -> blocks **)

let parse_blocks_located t k s =
  assemble 0 (loc_pieces t k (split_lines s))
