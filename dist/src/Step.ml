open Ast
open Attributes
open Datatypes
open Inline
open Line
open List0
open Marker
open Nat0
open PeanoNat
open String0
open Strings

type bconfig = { bmarker_interrupts : (lstyle list -> string -> task_marker
                                      option -> string -> bool);
                 bunderline : (char -> nat -> nat option); btables : 
                 bool; bheading_continues : bool; bdivs : bool;
                 btasks : bool; braw_blocks : bool; bdeflists : bool;
                 battrs : bool; bfootnotes : bool; bkeyed : bool }

(** val no_interrupt :
    lstyle list -> string -> task_marker option -> string -> bool **)

let no_interrupt _ _ _ _ =
  false

(** val no_underline : char -> nat -> nat option **)

let no_underline _ _ =
  None

(** val djot_bconfig : bconfig **)

let djot_bconfig =
  { bmarker_interrupts = no_interrupt; bunderline = no_underline; btables =
    true; bheading_continues = true; bdivs = true; btasks = true;
    braw_blocks = true; bdeflists = true; battrs = true; bfootnotes = true;
    bkeyed = false }

(** val with_keyed : bool -> bconfig -> bconfig **)

let with_keyed enabled k =
  { bmarker_interrupts = k.bmarker_interrupts; bunderline = k.bunderline;
    btables = k.btables; bheading_continues = k.bheading_continues; bdivs =
    k.bdivs; btasks = k.btasks; braw_blocks = k.braw_blocks; bdeflists =
    k.bdeflists; battrs = k.battrs; bfootnotes = k.bfootnotes; bkeyed =
    enabled }

(** val keyed_bconfig : bconfig **)

let keyed_bconfig =
  with_keyed true djot_bconfig

(** val configured_list_styles :
    bconfig -> lstyle list -> task_marker option -> lstyle list **)

let configured_list_styles h sty chk =
  if h.btasks
  then sty
  else (match sty with
        | [] -> sty
        | l :: l0 ->
          (match l with
           | STask c ->
             (match l0 with
              | [] ->
                (match chk with
                 | Some _ -> (SBullet c) :: []
                 | None -> sty)
              | _ :: _ -> sty)
           | _ -> sty))

(** val configured_list_check :
    bconfig -> task_marker option -> task_status **)

let configured_list_check h chk =
  if h.btasks
  then (match chk with
        | Some m -> m.tm_status
        | None -> Incomplete)
  else Incomplete

(** val configured_list_rest :
    bconfig -> task_marker option -> string -> string **)

let configured_list_rest h chk rest =
  if h.btasks
  then rest
  else (match chk with
        | Some m -> (^) (task_marker_source m) rest
        | None -> rest)

(** val binterrupt : bconfig -> line_kind -> bool **)

let binterrupt h = function
| KList (sty, core, chk, rest) ->
  h.bmarker_interrupts (configured_list_styles h sty chk) core
    (if h.btasks then chk else None) (configured_list_rest h chk rest)
| _ -> false

(** val bunderline_of : bconfig -> string -> nat option **)

let bunderline_of h l =
  match underline_of l with
  | Some p -> let (c, n) = p in h.bunderline c n
  | None -> None

(** val bcuts : bconfig -> string -> bool **)

let bcuts h l =
  match bunderline_of h l with
  | Some _ -> true
  | None -> binterrupt h (classify l)

(** val fence_block : bconfig -> fence -> string list -> block node **)

let fence_block k f content =
  let text = join_nl content in
  ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

     (fun _ -> mk (CodeBlock ("", text)))
     (fun a fmt ->
     (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
       (fun b b0 b1 b2 b3 b4 b5 b6 ->
       if b
       then if b0
            then mk (CodeBlock
                   (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                   (((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
                   (true, true, b1, b2, b3, b4, b5, b6)), fmt)), text))
            else if b1
                 then if b2
                      then if b3
                           then if b4
                                then if b5
                                     then mk (CodeBlock
                                            (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                                            (((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
                                            (true, false, true, true, true,
                                            true, true, b6)), fmt)), text))
                                     else if b6
                                          then mk (CodeBlock
                                                 (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                                                 ('\189', fmt)), text))
                                          else if k.braw_blocks
                                               then mk (RawBlock (fmt, text))
                                               else mk (CodeBlock
                                                      (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                                                      ('=', fmt)), text))
                                else mk (CodeBlock
                                       (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                                       (((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
                                       (true, false, true, true, true, false,
                                       b5, b6)), fmt)), text))
                           else mk (CodeBlock
                                  (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                                  (((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
                                  (true, false, true, true, false, b4, b5,
                                  b6)), fmt)), text))
                      else mk (CodeBlock
                             (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                             (((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
                             (true, false, true, false, b3, b4, b5, b6)),
                             fmt)), text))
                 else mk (CodeBlock
                        (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                        (((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
                        (true, false, false, b2, b3, b4, b5, b6)), fmt)),
                        text))
       else mk (CodeBlock
              (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

              (((* If this appears, you're using Ascii internals. Please don't *)
 (fun (b0,b1,b2,b3,b4,b5,b6,b7) ->
  let f b i = if b then 1 lsl i else 0 in
  Char.chr (f b0 0 + f b1 1 + f b2 2 + f b3 3 + f b4 4 + f b5 5 + f b6 6 + f b7 7))
              (false, b0, b1, b2, b3, b4, b5, b6)), fmt)), text)))
       a)
     f.f_info)

(** val cells_of :
    dtable -> cell_type -> align list -> string list -> cell list **)

let rec cells_of t ct aligns = function
| [] -> []
| c :: cs' ->
  (match aligns with
   | [] ->
     (Cell (ct, AlignDefault,
       (parse_inline_line t c))) :: (cells_of t ct [] cs')
   | a :: als ->
     (Cell (ct, a, (parse_inline_line t c))) :: (cells_of t ct als cs'))

(** val head_of : align list -> cell list -> cell list **)

let rec head_of aligns = function
| [] -> []
| c :: r' ->
  let Cell (_, _, ils) = c in
  (match aligns with
   | [] -> (Cell (HeadCell, AlignDefault, ils)) :: (head_of [] r')
   | a :: als -> (Cell (HeadCell, a, ils)) :: (head_of als r'))

(** val table_fold :
    dtable -> trow list -> align list -> cell list list -> cell list list **)

let rec table_fold t rows aligns acc =
  match rows with
  | [] -> rev acc
  | t0 :: rest ->
    (match t0 with
     | TSep als ->
       table_fold t rest als
         (match acc with
          | [] -> []
          | r :: acc' -> (head_of als r) :: acc')
     | TCells cs ->
       table_fold t rest aligns ((cells_of t BodyCell aligns cs) :: acc))

type tcap =
| TOpen
| TAfterBlank
| TCaption of string list

(** val caption_of : dtable -> tcap -> inlines option **)

let caption_of t = function
| TCaption ls ->
  let ils = para_inlines t (rev ls) in if nonempty ils then Some ils else None
| _ -> None

(** val table_block : dtable -> trow list -> tcap -> block node **)

let table_block t rows c =
  mk (Table ((caption_of t c), (table_fold t rows [] [])))

type list_state = { ls_indent : nat; ls_styles : (lstyle * nat) list;
                    ls_loose : bool; ls_blanks : bool;
                    ls_items : blocks list; ls_check : task_status;
                    ls_checks : task_status list }

type pstate =
| PPara of string list
| PHeading of nat * string list
| PFence of fence * nat * string list
| PQuote of blocks * pstate
| PDiv of nat * string * blocks * pstate
| PList of list_state * blocks * pstate
| PAttr of attr * nat * aparser * string list
| PParaOff of nat * string list
| PRef of nat * string * string
| PFoot of nat * string * blocks * pstate
| PTable of trow list * tcap
| PPend of attr * pstate
| PKey of string * string * pstate

(** val pstate_depth : pstate -> nat **)

let rec pstate_depth = function
| PQuote (_, inner) -> S (pstate_depth inner)
| PDiv (_, _, _, inner) -> S (pstate_depth inner)
| PList (_, _, inner) -> S (pstate_depth inner)
| PAttr (_, _, _, _) -> S (S O)
| PRef (_, _, _) -> S O
| PFoot (_, _, _, inner) -> S (pstate_depth inner)
| PTable (_, _) -> S O
| PPend (_, inner) -> S (pstate_depth inner)
| PKey (_, _, inner) -> S (pstate_depth inner)
| _ -> O

(** val is_idle : pstate -> bool **)

let is_idle = function
| PPara cur -> (match cur with
                | [] -> true
                | _ :: _ -> false)
| _ -> false

(** val heading_block : dtable -> nat -> string list -> block node **)

let heading_block t lvl cur =
  mk (Heading (lvl, (para_inlines t (rev cur))))

(** val heading_block_off :
    dtable -> nat -> nat -> string list -> block node **)

let heading_block_off t k lvl cur =
  mk (Heading (lvl, (para_inlines_off t k (rev cur))))

(** val para_recover : nat -> string list -> pstate **)

let para_recover extra slices =
  PParaOff ((add extra (Datatypes.length slices)), slices)

(** val finish_para_recover : dtable -> string list -> blocks **)

let finish_para_recover t slices = match slices with
| [] -> []
| _ :: _ ->
  (mk (Para (para_inlines_off t (Datatypes.length slices) (rev slices)))) :: []

(** val div_block : string -> blocks -> block node **)

let div_block cls bs =
  if (=) cls ""
  then mk (Div bs)
  else Node (NoPos, (("class", cls) :: []), (Div bs))

(** val styles_list :
    bconfig -> (lstyle * nat) list -> list_spacing -> blocks list -> block
    node **)

let styles_list k s sp items =
  match s with
  | [] -> mk (BulletList (sp, items))
  | p :: _ ->
    let (l0, start) = p in
    (match l0 with
     | SBullet c ->
       if (&&) ((=) c ':') k.bdeflists
       then mk (DefinitionList (sp, (def_items items)))
       else mk (BulletList (sp, items))
     | STask _ -> mk (BulletList (sp, items))
     | SOrd (n, d) ->
       mk (OrderedList ({ ol_style = n; ol_delim = d; ol_start = start }, sp,
         items)))

(** val styles_list_checked :
    bconfig -> (lstyle * nat) list -> list_spacing -> task_status list ->
    blocks list -> block node **)

let styles_list_checked k s sp checks items =
  match s with
  | [] -> styles_list k s sp items
  | p :: _ ->
    let (l0, _) = p in
    (match l0 with
     | STask _ -> mk (TaskList (sp, (task_items checks items)))
     | _ -> styles_list k s sp items)

(** val list_block : bconfig -> list_state -> blocks -> block node **)

let list_block k ls last =
  styles_list_checked k ls.ls_styles (if ls.ls_loose then Loose else Tight)
    (rev (ls.ls_check :: ls.ls_checks)) (rev (last :: ls.ls_items))

(** val ref_block : string -> string -> block node **)

let ref_block lbl val0 =
  mk (RefDef (lbl, val0))

(** val foot_block : string -> blocks -> block node **)

let foot_block lbl bs =
  mk (FootnoteDef (lbl, bs))

(** val key_close : dtable -> string -> string -> blocks -> blocks **)

let key_close t lbl src = function
| [] -> (mk (Para (para_inlines t (src :: [])))) :: []
| b :: rest -> (mk (Keyed ((para_inlines t (lbl :: [])), b))) :: rest

(** val ref_cont : string -> string option **)

let ref_cont l =
  let t = drop_leading_ws l in
  if (&&) (nonempty_str t) (no_ws t) then Some t else None

(** val finish : dtable -> bconfig -> pstate -> blocks **)

let rec finish t k = function
| PPara cur ->
  (match cur with
   | [] -> []
   | _ :: _ -> (mk (Para (para_inlines t (rev cur)))) :: [])
| PHeading (lvl, cur) -> (heading_block t lvl cur) :: []
| PFence (f, _, acc) -> (fence_block k f (rev acc)) :: []
| PQuote (done0, inner) ->
  (mk (BlockQuote (app (rev done0) (finish t k inner)))) :: []
| PDiv (_, cls, done0, inner) ->
  (div_block cls (app (rev done0) (finish t k inner))) :: []
| PList (ls, done0, inner) ->
  (list_block k ls (app (rev done0) (finish t k inner))) :: []
| PAttr (pend, _, ap, slices) ->
  if ap_done ap then [] else decorate_head pend (finish_para_recover t slices)
| PParaOff (k0, cur) -> (mk (Para (para_inlines_off t k0 (rev cur)))) :: []
| PRef (_, lbl, val0) -> (ref_block lbl val0) :: []
| PFoot (_, lbl, done0, inner) ->
  (foot_block lbl (app (rev done0) (finish t k inner))) :: []
| PTable (rows, cap) -> (table_block t (rev rows) cap) :: []
| PPend (pend, inner) -> decorate_head pend (finish t k inner)
| PKey (lbl, src, inner) -> key_close t lbl src (finish t k inner)

(** val lazy_ok : pstate -> bool **)

let rec lazy_ok = function
| PPara cur -> (match cur with
                | [] -> false
                | _ :: _ -> true)
| PHeading (_, _) -> true
| PQuote (_, inner) -> lazy_ok inner
| PDiv (_, _, _, inner) -> lazy_ok inner
| PList (_, _, inner) -> lazy_ok inner
| PParaOff (_, _) -> true
| PFoot (_, _, _, inner) -> lazy_ok inner
| PPend (_, inner) -> lazy_ok inner
| PKey (_, _, inner) -> lazy_ok inner
| _ -> false

(** val in_fence : pstate -> bool **)

let rec in_fence = function
| PFence (_, _, _) -> true
| PQuote (_, inner) -> in_fence inner
| PDiv (_, _, _, inner) -> in_fence inner
| PList (_, _, inner) -> in_fence inner
| PFoot (_, _, _, inner) -> in_fence inner
| PPend (_, inner) -> in_fence inner
| PKey (_, _, inner) -> in_fence inner
| _ -> false

(** val is_lazy : line_kind -> pstate -> bool **)

let is_lazy k inner =
  match k with
  | KText -> lazy_ok inner
  | _ -> false

(** val feed_lazy : string -> pstate -> pstate **)

let rec feed_lazy l st = match st with
| PPara cur -> PPara ((drop_leading_ws l) :: cur)
| PHeading (lvl, cur) -> PHeading (lvl, ((drop_leading_ws l) :: cur))
| PFence (f, ind, acc) -> PFence (f, ind, acc)
| PQuote (done0, inner) -> PQuote (done0, (feed_lazy l inner))
| PDiv (len, cls, done0, inner) -> PDiv (len, cls, done0, (feed_lazy l inner))
| PList (ls, done0, inner) -> PList (ls, done0, (feed_lazy l inner))
| PParaOff (k, cur) -> PParaOff (k, ((drop_leading_ws l) :: cur))
| PFoot (ind, lbl, done0, inner) ->
  PFoot (ind, lbl, done0, (feed_lazy l inner))
| PPend (pend, inner) -> PPend (pend, (feed_lazy l inner))
| PKey (lbl, src, inner) -> PKey (lbl, src, (feed_lazy l inner))
| _ -> st

(** val push_text : string -> string list -> string list **)

let push_text rest cur =
  if is_blank rest then cur else (drop_leading_ws rest) :: cur

(** val open_text : dtable -> bconfig -> string -> blocks * pstate **)

let open_text t h t0 =
  match if h.bkeyed then key_split t t0 else None with
  | Some p ->
    let (lbl, v) = p in ([], (PKey (lbl, t0, (PPara (push_text v [])))))
  | None -> ([], (PPara (t0 :: [])))

(** val keyless : dtable -> bconfig -> string -> bool **)

let keyless t h l =
  match if h.bkeyed then key_split t l else None with
  | Some _ -> false
  | None -> true

(** val open_kind :
    dtable -> bconfig -> string -> line_kind -> blocks * pstate **)

let open_kind t h l = function
| KThematic -> (((mk ThematicBreak) :: []), (PPara []))
| KDiv (len, cls) ->
  if h.bdivs
  then ([], (PDiv (len, cls, [], (PPara []))))
  else ([], (PPara ((drop_leading_ws l) :: [])))
| KHeading (lvl, rest) -> ([], (PHeading (lvl, (push_text rest []))))
| KRow r ->
  if h.btables
  then ([], (PTable ((r :: []), TOpen)))
  else ([], (PPara ((drop_leading_ws l) :: [])))
| KText -> open_text t h (drop_leading_ws l)
| _ -> ([], (PPara []))

(** val close_reopen :
    dtable -> bconfig -> pstate -> (blocks * pstate) -> blocks * pstate **)

let close_reopen t k st = function
| (bs, st') -> ((app (finish t k st) bs), st')

(** val pend_result : attr -> (blocks * pstate) -> blocks * pstate **)

let pend_result pend = function
| (bs, st') ->
  (match bs with
   | [] -> ([], (PPend (pend, st')))
   | _ :: _ -> ((decorate_head pend bs), st'))

(** val key_result :
    dtable -> string -> string -> (blocks * pstate) -> blocks * pstate **)

let key_result t lbl src = function
| (bs, st') ->
  (match bs with
   | [] -> ([], (PKey (lbl, src, st')))
   | _ :: _ -> ((key_close t lbl src bs), st'))

(** val open_quote : (blocks * pstate) -> blocks * pstate **)

let open_quote = function
| (bs, inner) -> ([], (PQuote ((rev bs), inner)))

(** val open_attr :
    bconfig -> attr -> nat -> aparser -> string -> blocks * pstate **)

let open_attr k pend ind ap l =
  if k.battrs
  then ([], (PAttr (pend, ind, ap, ((drop_leading_ws l) :: []))))
  else ([], (PPara ((drop_leading_ws l) :: [])))

(** val open_fence : nat -> fence -> blocks * pstate **)

let open_fence ind f =
  ([], (PFence (f, ind, [])))

(** val open_ref : nat -> string -> string -> blocks * pstate **)

let open_ref ind lbl val0 =
  ([], (PRef (ind, lbl, val0)))

(** val open_foot :
    bconfig -> string -> nat -> string -> (blocks * pstate) -> blocks * pstate **)

let open_foot k l ind lbl descended =
  if k.bfootnotes
  then let (bs, inner) = descended in
       ([], (PFoot (ind, lbl, (rev bs), inner)))
  else ([], (PPara ((drop_leading_ws l) :: [])))

(** val open_list :
    nat -> (lstyle * nat) list -> task_status -> (blocks * pstate) ->
    blocks * pstate **)

let open_list ind sty chk = function
| (bs, inner) ->
  ([], (PList ({ ls_indent = ind; ls_styles = sty; ls_loose = false;
    ls_blanks = false; ls_items = []; ls_check = chk; ls_checks = [] },
    (rev bs), inner)))

(** val list_blank : list_state -> list_state **)

let list_blank ls =
  { ls_indent = ls.ls_indent; ls_styles = ls.ls_styles; ls_loose =
    ls.ls_loose; ls_blanks = true; ls_items = ls.ls_items; ls_check =
    ls.ls_check; ls_checks = ls.ls_checks }

(** val list_narrow : list_state -> (lstyle * nat) list -> list_state **)

let list_narrow ls ns =
  { ls_indent = ls.ls_indent; ls_styles = ns; ls_loose = ls.ls_loose;
    ls_blanks = ls.ls_blanks; ls_items = ls.ls_items; ls_check = ls.ls_check;
    ls_checks = ls.ls_checks }

(** val announces_end : pstate -> bool **)

let announces_end = function
| PFence (_, _, _) -> true
| PDiv (_, _, _, _) -> true
| _ -> false

(** val claimable : line_kind -> bool **)

let claimable = function
| KThematic -> true
| KFence _ -> true
| KDiv (_, _) -> true
| _ -> false

(** val key_claims : string -> pstate -> bool **)

let rec key_claims l = function
| PDiv (_, _, _, inner) -> key_claims l inner
| PList (_, _, inner) -> key_claims l inner
| PFoot (_, _, _, inner) -> key_claims l inner
| PPend (_, inner) -> key_claims l inner
| PKey (_, _, inner) ->
  if is_idle inner then claimable (classify l) else announces_end inner
| _ -> false

(** val list_takes : list_state -> nat -> string -> pstate -> bool **)

let list_takes ls off l inner =
  (||) (key_claims l inner) (Nat.ltb ls.ls_indent (add off (indent_of l)))

(** val blank_absorbed : pstate -> bool **)

let rec blank_absorbed = function
| PFence (_, _, _) -> true
| PDiv (_, _, _, _) -> true
| PList (_, _, _) -> true
| PAttr (_, _, _, _) -> true
| PFoot (_, _, _, _) -> true
| PPend (_, inner) -> blank_absorbed inner
| PKey (_, _, inner) -> blank_absorbed inner
| _ -> false

(** val div_closer : string -> pstate -> bool **)

let rec div_closer l = function
| PDiv (len, _, _, inner) -> (&&) (negb (in_fence inner)) (div_close len l)
| PPend (_, inner) -> div_closer l inner
| PKey (_, _, inner) -> div_closer l inner
| _ -> false

(** val list_content : list_state -> line_kind -> list_state **)

let list_content ls k =
  let loose =
    match k with
    | KList (_, _, _, _) -> ls.ls_loose
    | _ -> (||) ls.ls_loose ls.ls_blanks
  in
  { ls_indent = ls.ls_indent; ls_styles = ls.ls_styles; ls_loose = loose;
  ls_blanks = false; ls_items = ls.ls_items; ls_check = ls.ls_check;
  ls_checks = ls.ls_checks }

(** val list_next :
    list_state -> blocks -> task_status -> string -> list_state **)

let list_next ls item chk rest =
  let items = item :: ls.ls_items in
  let checks = ls.ls_check :: ls.ls_checks in
  if is_blank rest
  then { ls_indent = ls.ls_indent; ls_styles = ls.ls_styles; ls_loose =
         ls.ls_loose; ls_blanks = ls.ls_blanks; ls_items = items; ls_check =
         chk; ls_checks = checks }
  else let loose =
         match classify rest with
         | KList (_, _, _, _) -> ls.ls_loose
         | _ -> (||) ls.ls_loose ls.ls_blanks
       in
       { ls_indent = ls.ls_indent; ls_styles = ls.ls_styles; ls_loose =
       loose; ls_blanks = false; ls_items = items; ls_check = chk;
       ls_checks = checks }

(** val consumed : string -> string -> nat **)

let consumed l rest =
  sub (length l) (length rest)

(** val open_line :
    dtable -> bconfig -> (string -> blocks * pstate) -> nat -> string ->
    line_kind -> blocks * pstate **)

let open_line t k descend ind l k0 = match k0 with
| KFence f -> open_fence ind f
| KQuote rest -> open_quote (descend rest)
| KList (sty, core, chk, rest) ->
  open_list ind (with_starts (configured_list_styles k sty chk) core)
    (configured_list_check k chk) (descend (configured_list_rest k chk rest))
| KAttr ap -> open_attr k [] ind ap l
| KFoot (lbl, rest) -> open_foot k l ind lbl (descend rest)
| KRef (lbl, v) -> open_ref ind lbl v
| _ -> open_kind t k l k0

(** val step_fuel :
    dtable -> bconfig -> nat -> nat -> string -> pstate -> blocks * pstate **)

let rec step_fuel t k n off l st =
  match n with
  | O -> ([], st)
  | S n' ->
    let descend = fun rest ->
      step_fuel t k n' (add off (consumed l rest)) rest (PPara [])
    in
    (match st with
     | PPara cur ->
       (match cur with
        | [] -> open_line t k descend (add off (indent_of l)) l (classify l)
        | c :: cur' ->
          (match bunderline_of k l with
           | Some lvl ->
             (((heading_block t (S lvl) (c :: cur')) :: []), (PPara []))
           | None ->
             (match classify l with
              | KBlank ->
                close_reopen t k (PPara (c :: cur')) (open_kind t k l KBlank)
              | x ->
                if binterrupt k x
                then close_reopen t k (PPara (c :: cur'))
                       (open_line t k descend (add off (indent_of l)) l x)
                else ([], (PPara ((drop_leading_ws l) :: (c :: cur')))))))
     | PHeading (lvl, cur) ->
       (match classify l with
        | KHeading (lvl', rest) ->
          if k.bheading_continues
          then if Nat.eqb lvl' lvl
               then ([], (PHeading (lvl, (push_text rest cur))))
               else close_reopen t k (PHeading (lvl, cur))
                      (open_kind t k l (KHeading (lvl', rest)))
          else close_reopen t k (PHeading (lvl, cur))
                 (open_kind t k l (KHeading (lvl', rest)))
        | KText ->
          if k.bheading_continues
          then ([], (PHeading (lvl, ((drop_leading_ws l) :: cur))))
          else close_reopen t k (PHeading (lvl, cur)) (open_kind t k l KText)
        | x ->
          close_reopen t k (PHeading (lvl, cur))
            (open_line t k descend (add off (indent_of l)) l x))
     | PFence (f, ind, acc) ->
       if fence_close f l
       then (((fence_block k f (rev acc)) :: []), (PPara []))
       else ([], (PFence (f, ind, ((drop_ws_upto (sub ind off) l) :: acc))))
     | PQuote (done0, inner) ->
       (match classify l with
        | KQuote rest ->
          let (bs, inner') =
            step_fuel t k n' (add off (consumed l rest)) rest inner
          in
          ([], (PQuote ((app (rev bs) done0), inner')))
        | x ->
          if is_lazy x inner
          then ([], (PQuote (done0, (feed_lazy l inner))))
          else close_reopen t k (PQuote (done0, inner))
                 (open_line t k descend (add off (indent_of l)) l x))
     | PDiv (len, cls, done0, inner) ->
       if (&&) (negb (in_fence inner)) (div_close len l)
       then (((div_block cls (app (rev done0) (finish t k inner))) :: []),
              (PPara []))
       else let (bs, inner') = step_fuel t k n' off l inner in
            ([], (PDiv (len, cls, (app (rev bs) done0), inner')))
     | PList (ls, done0, inner) ->
       (match classify l with
        | KBlank ->
          let (bs, inner') = step_fuel t k n' off l inner in
          let ls' = if blank_absorbed inner then ls else list_blank ls in
          ([], (PList (ls', (app (rev bs) done0), inner')))
        | x ->
          if list_takes ls off l inner
          then let (bs, inner') = step_fuel t k n' off l inner in
               let ls' =
                 if div_closer l inner
                 then list_blank ls
                 else list_content ls x
               in
               ([], (PList (ls', (app (rev bs) done0), inner')))
          else (match x with
                | KList (sty, core, chk, rest) ->
                  (match narrow ls.ls_styles
                           (configured_list_styles k sty chk) with
                   | [] ->
                     close_reopen t k (PList (ls, done0, inner))
                       (open_line t k descend (add off (indent_of l)) l
                         (KList (sty, core, chk, rest)))
                   | p :: l0 ->
                     let item = app (rev done0) (finish t k inner) in
                     let (bs, inner') =
                       step_fuel t k n'
                         (add off
                           (consumed l (configured_list_rest k chk rest)))
                         (configured_list_rest k chk rest) (PPara [])
                     in
                     ([], (PList
                     ((list_next (list_narrow ls (p :: l0)) item
                        (configured_list_check k chk)
                        (configured_list_rest k chk rest)),
                     (rev bs), inner'))))
                | _ ->
                  if is_lazy x inner
                  then ([], (PList (ls, done0, (feed_lazy l inner))))
                  else close_reopen t k (PList (ls, done0, inner))
                         (open_line t k descend (add off (indent_of l)) l x)))
     | PAttr (pend, ind, ap, slices) ->
       if ap_done ap
       then step_fuel t k n' off l (PPend ((attr_merge ap.ap_attrs pend),
              (PPara [])))
       else if Nat.ltb ind (add off (indent_of l))
            then let ap' = attr_feed l ap in
                 if ap_failed ap'
                 then pend_result pend
                        (step_fuel t k n' off l (para_recover (S O) slices))
                 else ([], (PAttr (pend, ind, ap', (push_text l slices))))
            else if is_blank l
                 then ([], (PPend (pend, (para_recover O slices))))
                 else pend_result pend
                        (step_fuel t k n' off l (para_recover O slices))
     | PParaOff (koff, cur) ->
       (match bunderline_of k l with
        | Some lvl ->
          (((heading_block_off t koff (S lvl) cur) :: []), (PPara []))
        | None ->
          (match classify l with
           | KBlank ->
             close_reopen t k (PParaOff (koff, cur)) (open_kind t k l KBlank)
           | x ->
             if binterrupt k x
             then close_reopen t k (PParaOff (koff, cur))
                    (open_line t k descend (add off (indent_of l)) l x)
             else ([], (PParaOff (koff, ((drop_leading_ws l) :: cur))))))
     | PRef (ind, lbl, val0) ->
       (match if Nat.ltb ind (add off (indent_of l)) then ref_cont l else None with
        | Some t0 -> ([], (PRef (ind, lbl, ((^) val0 t0))))
        | None ->
          let (bs, st') = step_fuel t k n' off l (PPara []) in
          (((ref_block lbl val0) :: bs), st'))
     | PFoot (ind, lbl, done0, inner) ->
       if is_blank l
       then let (bs, inner') = step_fuel t k n' off l inner in
            ([], (PFoot (ind, lbl, (app (rev bs) done0), inner')))
       else if Nat.ltb ind (add off (indent_of l))
            then let (bs, inner') = step_fuel t k n' off l inner in
                 ([], (PFoot (ind, lbl, (app (rev bs) done0), inner')))
            else let (bs, st') = step_fuel t k n' off l (PPara []) in
                 (((foot_block lbl (app (rev done0) (finish t k inner))) :: bs),
                 st')
     | PTable (rows, cap) ->
       (match cap with
        | TCaption ls ->
          if is_blank l
          then (((table_block t (rev rows) cap) :: []), (PPara []))
          else ([], (PTable (rows, (TCaption ((drop_leading_ws l) :: ls)))))
        | _ ->
          (match caption_open l with
           | Some rest ->
             ([], (PTable (rows, (TCaption (push_text rest [])))))
           | None ->
             if is_blank l
             then ([], (PTable (rows, TAfterBlank)))
             else (match classify l with
                   | KRow r ->
                     (match cap with
                      | TOpen -> ([], (PTable ((r :: rows), TOpen)))
                      | _ ->
                        let (bs, st') = step_fuel t k n' off l (PPara []) in
                        (((table_block t (rev rows) cap) :: bs), st'))
                   | _ ->
                     let (bs, st') = step_fuel t k n' off l (PPara []) in
                     (((table_block t (rev rows) cap) :: bs), st'))))
     | PPend (pend, inner) ->
       (match classify l with
        | KBlank ->
          if is_idle inner
          then ([], (PPara []))
          else pend_result pend (step_fuel t k n' off l inner)
        | KAttr ap ->
          if is_idle inner
          then open_attr k pend (add off (indent_of l)) ap l
          else pend_result pend (step_fuel t k n' off l inner)
        | _ -> pend_result pend (step_fuel t k n' off l inner))
     | PKey (lbl, src, inner) ->
       if (&&) (is_blank l) (is_idle inner)
       then (((mk (Para (para_inlines t (src :: [])))) :: []), (PPara []))
       else key_result t lbl src (step_fuel t k n' off l inner))

(** val step : dtable -> bconfig -> string -> pstate -> blocks * pstate **)

let step t k l st =
  step_fuel t k (S (add (length l) (pstate_depth st))) O l st

(** val parse_lines : dtable -> bconfig -> string list -> pstate -> blocks **)

let rec parse_lines t k lines st =
  match lines with
  | [] -> finish t k st
  | l :: rest ->
    let (bs, st') = step t k l st in app bs (parse_lines t k rest st')

(** val parse_blocks : dtable -> bconfig -> string -> blocks **)

let parse_blocks t k s =
  parse_lines t k (split_lines s) (PPara [])

(** val pad_safe : pstate -> bool **)

let rec pad_safe = function
| PDiv (_, _, _, inner) -> pad_safe inner
| PList (_, _, inner) -> pad_safe inner
| PAttr (_, _, _, _) -> false
| PFoot (_, _, _, inner) -> pad_safe inner
| PPend (_, inner) -> pad_safe inner
| PKey (_, _, inner) -> pad_safe inner
| _ -> true

(** val blank_safe : pstate -> bool **)

let rec blank_safe = function
| PFence (_, _, _) -> false
| PDiv (_, _, _, inner) -> blank_safe inner
| PList (_, _, inner) -> blank_safe inner
| PAttr (_, _, _, _) -> false
| PFoot (_, _, _, inner) -> blank_safe inner
| PPend (_, inner) -> (&&) (blank_safe inner) (negb (is_idle inner))
| PKey (_, _, inner) -> (&&) (blank_safe inner) (negb (announces_end inner))
| _ -> true
