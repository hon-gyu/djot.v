open Ast
open Attributes
open Bool0
open Datatypes
open InlineTable
open InlineView
open List0
open Nat0
open PeanoNat
open Strings

(** val strip_pad : string -> string **)

let strip_pad s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> s)
    (fun c rest -> if (&&) ((=) c ' ') (starts_tick rest) then rest else s)
    s

(** val trim_verb : string -> string **)

let trim_verb s =
  rev_string (strip_pad (rev_string (strip_pad s)))

type oitem =
| OIn of inline node
| OMark of attr * span * spot option

type oitems = oitem list

type frame_kind =
| FKDelim of dstyle * bool
| FKBracket of bool
| FKDest of bool

type frame = { fr_kind : frame_kind; fr_marked : bool; fr_open : span;
               fr_out : oitems }

(** val fr_src : dtable -> frame -> string **)

let fr_src t f =
  match f.fr_kind with
  | FKDelim (k, cm) -> ddecay_str t k f.fr_marked cm
  | FKBracket image -> bracket_open image
  | FKDest image -> bracket_open image

(** val fr_barrier : frame -> bool **)

let fr_barrier f =
  match f.fr_kind with
  | FKDest _ -> true
  | _ -> false

type ostate = { os_out : oitems; os_stk : frame list;
                os_word_start : spot option }

(** val ostart : ostate **)

let ostart =
  { os_out = []; os_stk = []; os_word_start = None }

(** val spot_later : spot -> spot -> spot **)

let spot_later a b =
  if ( < ) a.spot_line b.spot_line
  then b
  else if ( < ) b.spot_line a.spot_line
       then a
       else if ( < ) a.spot_rem b.spot_rem then a else b

(** val roles_stop : provenance -> spot **)

let roles_stop p =
  fold_left (fun acc e -> spot_later acc (snd e).span_stop) p.syntax_spans
    p.node_span.span_stop

(** val node_stop : spot -> inline node -> spot **)

let node_stop fallback n =
  match node_provenance n with
  | Some p -> roles_stop p
  | None -> fallback

(** val items_stop : spot -> oitems -> spot **)

let rec items_stop fallback = function
| [] -> fallback
| o :: _ ->
  (match o with
   | OIn n -> node_stop fallback n
   | OMark (_, spec, _) -> spec.span_stop)

(** val text_start : coq_InlineCursor -> ostate -> spot **)

let text_start h o =
  match o.os_stk with
  | [] -> items_stop h.cursor_origin o.os_out
  | f :: _ -> items_stop f.fr_open.span_stop f.fr_out

(** val remember_word_start :
    coq_PosPolicy -> coq_InlineCursor -> char -> ostate -> ostate **)

let remember_word_start h h0 c o =
  if (&&) h.pos_records (is_ws c)
  then { os_out = o.os_out; os_stk = o.os_stk; os_word_start = (Some
         h0.cursor_stop) }
  else o

(** val oword_reset : ostate -> ostate **)

let oword_reset o =
  { os_out = o.os_out; os_stk = o.os_stk; os_word_start = None }

(** val inline_prov : spot -> spot -> provenance **)

let inline_prov start stop =
  prov_at { span_start = start; span_stop = stop }

(** val imk : coq_PosPolicy -> spot -> spot -> inline -> inline node **)

let imk h start stop x =
  if h.pos_records then posnode h (inline_prov start stop) x else mk x

(** val imk_here :
    coq_PosPolicy -> coq_InlineCursor -> inline -> inline node **)

let imk_here h h0 x =
  imk h h0.cursor_start h0.cursor_stop x

(** val fr_lit : dtable -> coq_PosPolicy -> frame -> inline node **)

let fr_lit t h f =
  imk h f.fr_open.span_start f.fr_open.span_stop (Str (fr_src t f))

(** val add_inline_role :
    coq_PosPolicy -> syntax_role -> span -> inline node -> inline node **)

let add_inline_role h role r n =
  add_roles h ((role, r) :: []) n

(** val dmatch : dstyle -> bool -> frame -> bool **)

let dmatch k m f =
  match f.fr_kind with
  | FKDelim (k', _) -> (&&) (dstyle_eq k k') (eqb m f.fr_marked)
  | _ -> false

(** val merge_text_pos : pos -> pos -> pos **)

let merge_text_pos left right =
  match left with
  | NoPos -> left
  | SomePos p ->
    (match right with
     | NoPos -> left
     | SomePos q ->
       SomePos { node_span = { span_start = p.node_span.span_start;
         span_stop = q.node_span.span_stop }; syntax_spans =
         (app p.syntax_spans q.syntax_spans); part_spans = PNone })

(** val isnoc : inline node -> inlines -> inlines **)

let isnoc n out = match out with
| [] -> n :: out
| n0 :: rest ->
  let Node (p, a, x) = n0 in
  (match a with
   | [] ->
     (match x with
      | Str t ->
        let Node (q, a0, x0) = n in
        (match a0 with
         | [] ->
           (match x0 with
            | Str s ->
              (Node ((merge_text_pos p q), [], (Str ((^) t s)))) :: rest
            | _ -> n :: out)
         | _ :: _ -> n :: out)
      | _ -> n :: out)
   | _ :: _ -> n :: out)

(** val istarts_str : inlines -> bool **)

let istarts_str = function
| [] -> false
| n :: _ ->
  let Node (_, a, x) = n in
  (match a with
   | [] -> (match x with
            | Str _ -> true
            | _ -> false)
   | _ :: _ -> false)

(** val osnoc : oitem -> oitems -> oitems **)

let osnoc n out = match out with
| [] -> n :: out
| o :: rest ->
  (match o with
   | OIn n0 ->
     let Node (p, a, x) = n0 in
     (match a with
      | [] ->
        (match x with
         | Str t ->
           (match n with
            | OIn n1 ->
              let Node (q, a0, x0) = n1 in
              (match a0 with
               | [] ->
                 (match x0 with
                  | Str s ->
                    (OIn (Node ((merge_text_pos p q), [], (Str
                      ((^) t s))))) :: rest
                  | _ -> n :: out)
               | _ :: _ -> n :: out)
            | OMark (_, _, _) -> n :: out)
         | _ -> n :: out)
      | _ :: _ -> n :: out)
   | OMark (_, _, _) -> n :: out)

(** val oapp : oitems -> oitems -> oitems **)

let rec oapp cur out =
  match cur with
  | [] -> out
  | n :: rest ->
    (match rest with
     | [] -> osnoc n out
     | _ :: _ -> n :: (oapp rest out))

(** val oemit : inline node -> ostate -> ostate **)

let oemit n o =
  let word = o.os_word_start in
  (match o.os_stk with
   | [] ->
     { os_out = ((OIn n) :: o.os_out); os_stk = []; os_word_start = word }
   | f :: rest ->
     { os_out = o.os_out; os_stk = ({ fr_kind = f.fr_kind; fr_marked =
       f.fr_marked; fr_open = f.fr_open; fr_out = ((OIn
       n) :: f.fr_out) } :: rest); os_word_start = word })

(** val omark : attr -> span -> ostate -> ostate **)

let omark a spec o =
  match o.os_stk with
  | [] ->
    { os_out = ((OMark (a, spec, o.os_word_start)) :: o.os_out); os_stk = [];
      os_word_start = None }
  | f :: rest ->
    { os_out = o.os_out; os_stk = ({ fr_kind = f.fr_kind; fr_marked =
      f.fr_marked; fr_open = f.fr_open; fr_out = ((OMark (a, spec,
      o.os_word_start)) :: f.fr_out) } :: rest); os_word_start = None }

(** val flush_text_at :
    coq_PosPolicy -> coq_InlineCursor -> string -> ostate -> ostate **)

let flush_text_at h h0 txt o =
  if nonempty_str txt
  then oemit (imk h (text_start h0 o) h0.cursor_start (Str txt)) o
  else o

(** val flush_text_to_at :
    coq_PosPolicy -> coq_InlineCursor -> spot -> string -> ostate -> ostate **)

let flush_text_to_at h h0 stop txt o =
  if nonempty_str txt
  then oemit (imk h (text_start h0 o) stop (Str txt)) o
  else o

(** val opush_at : dstyle -> bool -> bool -> span -> ostate -> ostate **)

let opush_at k m cm open0 o =
  { os_out = o.os_out; os_stk = ({ fr_kind = (FKDelim (k, cm)); fr_marked =
    m; fr_open = open0; fr_out = [] } :: o.os_stk); os_word_start =
    o.os_word_start }

(** val previous_spot : spot -> spot **)

let previous_spot p =
  { spot_line = p.spot_line; spot_rem = (Stdlib.succ p.spot_rem) }

(** val source_shape : string -> (int * int) * int **)

let rec source_shape s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> ((0, 0), 0))
    (fun c rest ->
    let (p, total) = source_shape rest in
    let (lines, first) = p in
    if (=) c nl_char
    then (((Stdlib.succ lines), 0), (Stdlib.succ total))
    else ((lines, (Stdlib.succ first)), (Stdlib.succ total)))
    s

(** val spot_before : spot -> string -> spot **)

let spot_before p s =
  let (p0, total) = source_shape s in
  let (lines, first) = p0 in
  if ( = ) lines 0
  then { spot_line = p.spot_line; spot_rem = (( + ) p.spot_rem total) }
  else { spot_line = (sub p.spot_line lines); spot_rem = first }

(** val spot_plus : int -> spot -> spot **)

let spot_plus n p =
  { spot_line = p.spot_line; spot_rem = (( + ) p.spot_rem n) }

(** val dtoken_span :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> dstyle -> bool -> span **)

let dtoken_span t h h0 k marked =
  pspan h { span_start =
    (spot_before h0.cursor_start
      ((^) (if marked then one lbrace else "") (dtoken t k)));
    span_stop = h0.cursor_start }

(** val opush :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> dstyle -> bool -> ostate
    -> ostate **)

let opush t h h0 k m o =
  opush_at k m false (dtoken_span t h h0 k m) o

(** val bpush :
    coq_PosPolicy -> coq_InlineCursor -> bool -> ostate -> ostate **)

let bpush h h0 image o =
  let start = if image then previous_spot h0.cursor_start else h0.cursor_start
  in
  { os_out = o.os_out; os_stk = ({ fr_kind = (FKBracket image); fr_marked =
  false; fr_open =
  (pspan h { span_start = start; span_stop = h0.cursor_stop }); fr_out =
  [] } :: o.os_stk); os_word_start = o.os_word_start }

(** val dpush : bool -> span -> ostate -> ostate **)

let dpush image open0 o =
  { os_out = o.os_out; os_stk = ({ fr_kind = (FKDest image); fr_marked =
    false; fr_open = open0; fr_out = [] } :: o.os_stk); os_word_start =
    o.os_word_start }

(** val last_ws_split : string -> string * string **)

let rec last_ws_split s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> ("", ""))
    (fun c rest ->
    let (pre, w) = last_ws_split rest in
    ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

       (fun _ ->
       if is_ws c
       then ((one c), w)
       else ("",
              ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

              (c, w))))
       (fun _ _ ->
       (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

       (c, pre)), w))
       pre))
    s

(** val split_text_pos : pos -> spot option -> pos * pos **)

let split_text_pos p word_start =
  match p with
  | NoPos -> (p, p)
  | SomePos pr ->
    (match word_start with
     | Some w ->
       ((SomePos
         (prov_at { span_start = pr.node_span.span_start; span_stop = w })),
         (SomePos
         (prov_at { span_start = w; span_stop = pr.node_span.span_stop })))
     | None -> (p, p))

(** val oattach_list :
    coq_PosPolicy -> attr -> span -> spot option -> inlines -> inlines **)

let oattach_list h a spec word_start out = match out with
| [] -> out
| n :: rest ->
  let Node (p, a0, x) = n in
  (match a0 with
   | [] ->
     (match x with
      | Str s ->
        let (pre, w) = last_ws_split s in
        if nonempty_str w
        then (match a with
              | [] -> out
              | _ :: _ ->
                let (pp, wp) = split_text_pos p word_start in
                let out1 =
                  if nonempty_str pre
                  then isnoc (Node (pp, [], (Str pre))) rest
                  else rest
                in
                isnoc
                  (add_inline_role h RAttrSpec spec (Node (wp, a, (Str w))))
                  out1)
        else out
      | SoftBreak -> out
      | _ ->
        (add_inline_role h RAttrSpec spec
          (let Node (p0, a', v) = n in Node (p0, (Attr.merge a a'), v))) :: rest)
   | _ :: _ ->
     (match x with
      | SoftBreak -> out
      | _ ->
        (add_inline_role h RAttrSpec spec
          (let Node (p0, a', v) = n in Node (p0, (Attr.merge a a'), v))) :: rest))

(** val oresolve_go : coq_PosPolicy -> oitems -> inlines * bool **)

let rec oresolve_go h = function
| [] -> ([], false)
| o :: rest ->
  (match o with
   | OIn n ->
     let (out, m) = oresolve_go h rest in
     ((if m then isnoc n out else n :: out), false)
   | OMark (a, spec, word_start) ->
     let (out, _) = oresolve_go h rest in
     let out' = oattach_list h a spec word_start out in
     (out', (istarts_str out')))

(** val oresolve : coq_PosPolicy -> oitems -> inlines **)

let oresolve h l =
  fst (oresolve_go h l)

(** val oclose_go :
    dtable -> coq_PosPolicy -> dstyle -> bool -> oitems -> frame list ->
    ((oitems * span) * frame list) option **)

let rec oclose_go t h k m pend = function
| [] -> None
| f :: rest ->
  let content = oapp pend f.fr_out in
  if dmatch k m f
  then if nonempty content then Some ((content, f.fr_open), rest) else None
  else if fr_barrier f
       then None
       else oclose_go t h k m (oapp content ((OIn (fr_lit t h f)) :: [])) rest

(** val oclose_barred_go : dstyle -> bool -> bool -> frame list -> bool **)

let rec oclose_barred_go k m past = function
| [] -> false
| f :: rest ->
  if dmatch k m f
  then past
  else oclose_barred_go k m ((||) past (fr_barrier f)) rest

(** val oclose_barred : dstyle -> bool -> ostate -> bool **)

let oclose_barred k m o =
  oclose_barred_go k m false o.os_stk

(** val oclose :
    dtable -> coq_PosPolicy -> dstyle -> bool -> spot -> ostate -> ostate
    option **)

let oclose t h k m stop o =
  match oclose_go t h k m [] o.os_stk with
  | Some p ->
    let (p0, rest) = p in
    let (content, open0) = p0 in
    Some
    (oemit (imk h open0.span_start stop (dnode k (rev (oresolve h content))))
      { os_out = o.os_out; os_stk = rest; os_word_start = o.os_word_start })
  | None -> None

(** val bclose_go :
    dtable -> coq_PosPolicy -> oitems -> frame list ->
    (((oitems * bool) * span) * frame list) option **)

let rec bclose_go t h pend = function
| [] -> None
| f :: rest ->
  let content = oapp pend f.fr_out in
  (match f.fr_kind with
   | FKDelim (_, _) ->
     bclose_go t h (oapp content ((OIn (fr_lit t h f)) :: [])) rest
   | FKBracket image -> Some (((content, image), f.fr_open), rest)
   | FKDest _ -> None)

(** val bclose :
    dtable -> coq_PosPolicy -> ostate -> (((inlines * bool) * span) * ostate)
    option **)

let bclose t h o =
  match bclose_go t h [] o.os_stk with
  | Some p ->
    let (p0, rest) = p in
    let (p1, open0) = p0 in
    let (content, image) = p1 in
    Some ((((rev (oresolve h content)), image), open0), { os_out = o.os_out;
    os_stk = rest; os_word_start = o.os_word_start })
  | None -> None

(** val bunpush : ostate -> ((bool * span) * ostate) option **)

let bunpush o =
  match o.os_stk with
  | [] -> None
  | f :: rest ->
    let { fr_kind = fr_kind0; fr_marked = _; fr_open = open0; fr_out =
      fr_out0 } = f
    in
    (match fr_kind0 with
     | FKBracket image ->
       (match fr_out0 with
        | [] ->
          Some ((image, open0), { os_out = o.os_out; os_stk = rest;
            os_word_start = o.os_word_start })
        | _ :: _ -> None)
     | _ -> None)

(** val opop_str : ostate -> string * ostate **)

let opop_str o =
  match o.os_stk with
  | [] ->
    (match o.os_out with
     | [] -> ("", o)
     | o0 :: rest ->
       (match o0 with
        | OIn n ->
          let Node (_, a, x) = n in
          (match a with
           | [] ->
             (match x with
              | Str s ->
                (s, { os_out = rest; os_stk = []; os_word_start =
                  o.os_word_start })
              | _ -> ("", o))
           | _ :: _ -> ("", o))
        | OMark (_, _, _) -> ("", o)))
  | f :: fs ->
    (match f.fr_out with
     | [] -> ("", o)
     | o0 :: rest ->
       (match o0 with
        | OIn n ->
          let Node (_, a, x) = n in
          (match a with
           | [] ->
             (match x with
              | Str s ->
                (s, { os_out = o.os_out; os_stk = ({ fr_kind = f.fr_kind;
                  fr_marked = f.fr_marked; fr_open = f.fr_open; fr_out =
                  rest } :: fs); os_word_start = o.os_word_start })
              | _ -> ("", o))
           | _ :: _ -> ("", o))
        | OMark (_, _, _) -> ("", o)))

(** val bflat :
    coq_PosPolicy -> coq_InlineCursor -> inlines -> string -> ostate ->
    string * ostate **)

let rec bflat h h0 kids txt o =
  match kids with
  | [] -> (txt, o)
  | n :: rest ->
    let Node (_, a, x) = n in
    (match a with
     | [] ->
       (match x with
        | Str s -> bflat h h0 rest ((^) txt s) o
        | _ -> bflat h h0 rest "" (oemit n (flush_text_at h h0 txt o)))
     | _ :: _ -> bflat h h0 rest "" (oemit n (flush_text_at h h0 txt o)))

(** val bsplit_nl :
    coq_PosPolicy -> coq_InlineCursor -> string -> string -> ostate ->
    string * ostate **)

let rec bsplit_nl h h0 s txt o =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> (txt, o))
    (fun c rest ->
    if (=) c nl_char
    then bsplit_nl h h0 rest ""
           (oemit (imk_here h h0 SoftBreak) (flush_text_at h h0 txt o))
    else bsplit_nl h h0 rest ((^) txt (one c)) o)
    s

(** val bclosed_lit :
    coq_PosPolicy -> coq_InlineCursor -> inlines -> bool -> ostate ->
    string * ostate **)

let bclosed_lit h h0 kids image o =
  let (pre, o1) = opop_str o in
  let (txt, o2) = bflat h h0 kids ((^) pre (bracket_open image)) o1 in
  (((^) txt (one rbrack)), o2)

(** val bspan_lit :
    coq_PosPolicy -> coq_InlineCursor -> inlines -> bool -> string -> ostate
    -> string * ostate **)

let bspan_lit h h0 kids image src o =
  let (txt, o') = bclosed_lit h h0 kids image o in
  bsplit_nl h h0 src ((^) txt (one lbrace)) o'

(** val battr_lit :
    coq_PosPolicy -> coq_InlineCursor -> string -> string -> ostate ->
    string * ostate **)

let battr_lit h h0 src txt o =
  bsplit_nl h h0 src ((^) txt (one lbrace)) o

(** val blit_prev : string -> char option **)

let blit_prev t =
  str_last t (Some nl_char)

(** val bref_lit :
    coq_PosPolicy -> coq_InlineCursor -> inlines -> bool -> string -> ostate
    -> string * ostate **)

let bref_lit h h0 kids image label o =
  let (txt, o') = bclosed_lit h h0 kids image o in
  (((^) txt ((^) (one lbrack) label)), o')

(** val drop_nl : string -> string **)

let rec drop_nl s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun c rest ->
    if (=) c nl_char
    then drop_nl rest
    else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, (drop_nl rest)))
    s

(** val oapp_rev : oitems -> oitems -> oitems **)

let oapp_rev acc out =
  match acc with
  | [] -> rev out
  | n :: rest -> app (rev (osnoc n out)) rest

(** val oflatten_rev :
    dtable -> coq_PosPolicy -> oitems -> frame list -> oitems -> oitems **)

let rec oflatten_rev t h acc stk bottom =
  match stk with
  | [] -> oapp_rev acc bottom
  | f :: rest ->
    oflatten_rev t h
      (oapp_rev (oapp_rev acc f.fr_out) ((OIn (fr_lit t h f)) :: [])) rest
      bottom

(** val oitems_of : dtable -> coq_PosPolicy -> ostate -> oitems **)

let oitems_of t h o =
  match o.os_stk with
  | [] -> o.os_out
  | f :: l -> rev (oflatten_rev t h [] (f :: l) o.os_out)

(** val ofinish : dtable -> coq_PosPolicy -> ostate -> inlines **)

let ofinish t h o =
  oresolve h (oitems_of t h o)

type vkind =
| VVerb
| VMath of math_style

(** val vnode : vkind -> string -> inline **)

let vnode vk s =
  match vk with
  | VVerb -> Verbatim s
  | VMath st -> Math (st, s)

(** val vkind_verb : vkind -> bool **)

let vkind_verb = function
| VVerb -> true
| VMath _ -> false

type iscan =
| IText of bool * string * char option * ostate
| IEscWs of string * string * char option * ostate
| IBrace of string * char option * ostate
| IDelim of dstyle * int * string * char option * bool * ostate
| IOpen of int * vkind * ostate
| IVerb of int * int * string * vkind * ostate
| IDollar of bool * string * char option * ostate
| IPeriod of bool * string * char option * ostate
| IDash of int * string * char option * ostate
| IBang of string * char option * ostate
| IClosed of string * ostate
| ISpan of inlines * bool * span * aparser * string * ostate
| IAttr of aparser * string * string * char option * iscan * ostate
| IReference of inlines * bool * span * string * ostate
| INote of bool * bool * string * span * ostate
| IWiki of bool * bool * bool * string * span * ostate
| IDest of inlines * bool * span * bool * int * string * iscan * ostate
| IAuto of string * string * ostate
| ISymbol of string * string * iscan * ostate
| IRaw of string * string * ostate

(** val note_pos : string -> char option -> bool **)

let note_pos txt prev =
  (&&) (negb (nonempty_str txt))
    (match prev with
     | Some p -> (=) p lbrack
     | None -> false)

(** val ilead :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> string -> char
    option -> ostate -> iscan **)

let ilead t h h0 c txt prev o =
  if is_bslash c
  then IText (true, txt, (Some c), o)
  else if is_tick c
       then IOpen ((Stdlib.succ 0), VVerb, (flush_text_at h h0 txt o))
       else if (=) c dollar
            then IDollar (false, txt, prev, o)
            else if (=) c period
                 then IPeriod (false, txt, prev, o)
                 else if (=) c hyphen
                      then IDash ((Stdlib.succ 0), txt, prev, o)
                      else if (=) c lbrace
                           then IBrace (txt, prev, o)
                           else if (=) c bang
                                then IBang (txt, prev, o)
                                else if (=) c lt
                                     then IAuto ("", txt, o)
                                     else if (=) c ':'
                                          then ISymbol ("", txt, (IText
                                                 (false, ((^) txt (one c)),
                                                 (Some c),
                                                 (remember_word_start h h0 c
                                                   o))),
                                                 o)
                                          else if (=) c lbrack
                                               then (match if (&&)
                                                                (note_pos txt
                                                                  prev)
                                                                (wikilinks_enabled
                                                                  t)
                                                           then bunpush o
                                                           else None with
                                                     | Some p ->
                                                       let (p0, o') = p in
                                                       let (image, open0) = p0
                                                       in
                                                       IWiki (false, false,
                                                       image, "", open0, o')
                                                     | None ->
                                                       IText (false, "",
                                                         (Some lbrack),
                                                         (bpush h h0 false
                                                           (flush_text_at h
                                                             h0 txt o))))
                                               else if (=) c rbrack
                                                    then IClosed (txt, o)
                                                    else (match if (&&)
                                                                    ((&&)
                                                                    ((=) c
                                                                    hat)
                                                                    (note_pos
                                                                    txt prev))
                                                                    (notes_enabled
                                                                    t)
                                                                then bunpush o
                                                                else None with
                                                          | Some p ->
                                                            let (p0, o') = p
                                                            in
                                                            let (image, open0) =
                                                              p0
                                                            in
                                                            INote (false,
                                                            image, "", open0,
                                                            o')
                                                          | None ->
                                                            (match dstyle_of
                                                                    t c with
                                                             | Some k ->
                                                               IDelim (k, 0,
                                                                 txt, prev,
                                                                 false, o)
                                                             | None ->
                                                               IText (false,
                                                                 ((^) txt
                                                                   (one c)),
                                                                 (Some c),
                                                                 (remember_word_start
                                                                   h h0 c o))))

(** val idest_open :
    coq_PosPolicy -> coq_InlineCursor -> inlines -> bool -> span -> ostate ->
    iscan **)

let idest_open h h0 kids image open0 o =
  let (txt, o') = bflat h h0 kids "" (dpush image open0 o) in
  IText (false, ((^) txt ((^) (one rbrack) (one lparen))), (Some lparen), o')

(** val null : 'a1 list -> bool **)

let null = function
| [] -> true
| _ :: _ -> false

(** val ellipsis : string **)

let ellipsis =
  "\226\128\166"

(** val endash : string **)

let endash =
  "\226\128\147"

(** val emdash : string **)

let emdash =
  "\226\128\148"

(** val periods : bool -> string **)

let periods = function
| true ->
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (period, (one period))
| false -> one period

(** val typography_ellipsis : dtable -> string **)

let typography_ellipsis t =
  if smart_typography t
  then ellipsis
  else chars period (Stdlib.succ (Stdlib.succ (Stdlib.succ 0)))

(** val srep : string -> int -> string **)

let rec srep s n =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> "")
    (fun m -> (^) s (srep s m))
    n

(** val dash_counts : int -> (int * int) * int **)

let dash_counts n =
  if ( = ) (Nat.modulo n (Stdlib.succ (Stdlib.succ (Stdlib.succ 0)))) 0
  then (((Nat.div n (Stdlib.succ (Stdlib.succ (Stdlib.succ 0)))), 0), 0)
  else if ( = ) (Nat.modulo n (Stdlib.succ (Stdlib.succ 0))) 0
       then ((0, (Nat.div n (Stdlib.succ (Stdlib.succ 0)))), 0)
       else if ( = ) n (Stdlib.succ 0)
            then ((0, 0), (Stdlib.succ 0))
            else if ( = )
                      (Nat.modulo n (Stdlib.succ (Stdlib.succ (Stdlib.succ
                        (Stdlib.succ (Stdlib.succ (Stdlib.succ 0)))))))
                      (Stdlib.succ (Stdlib.succ (Stdlib.succ (Stdlib.succ
                      (Stdlib.succ 0)))))
                 then (((Nat.div (sub n (Stdlib.succ (Stdlib.succ 0)))
                          (Stdlib.succ (Stdlib.succ (Stdlib.succ 0)))),
                        (Stdlib.succ 0)), 0)
                 else (((Nat.div
                          (sub n (Stdlib.succ (Stdlib.succ (Stdlib.succ
                            (Stdlib.succ 0)))))
                          (Stdlib.succ (Stdlib.succ (Stdlib.succ 0)))),
                        (Stdlib.succ (Stdlib.succ 0))), 0)

(** val dashes : int -> string **)

let dashes n =
  let (p, lit) = dash_counts n in
  let (em, en) = p in
  (^) (srep emdash em) ((^) (srep endash en) (chars hyphen lit))

(** val typography_dashes : dtable -> int -> string **)

let typography_dashes t n =
  if smart_typography t then dashes n else chars hyphen n

(** val dollars : bool -> string **)

let dollars = function
| true -> (^) (one dollar) (one dollar)
| false -> one dollar

(** val auto_lit : string -> string -> string **)

let auto_lit src txt =
  (^) txt
    ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (lt, src))

(** val islice_end : dtable -> iscan -> iscan **)

let rec islice_end t st = match st with
| IText (esc, txt, _, o) ->
  if esc then IText (false, ((^) txt (one bslash)), (Some bslash), o) else st
| IBrace (txt, _, o) ->
  IText (false, ((^) txt (one lbrace)), (Some lbrace), o)
| IPeriod (two, txt, _, o) ->
  IText (false, ((^) txt (periods two)), (Some period), o)
| IDash (n, txt, _, o) ->
  IText (false, ((^) txt (typography_dashes t n)), (Some hyphen), o)
| IClosed (txt, o) -> IText (false, ((^) txt (one rbrack)), (Some rbrack), o)
| IAuto (src, txt, o) ->
  IText (false, (auto_lit src txt), (blit_prev (auto_lit src txt)), o)
| ISymbol (_, _, sh, _) -> islice_end t sh
| _ -> st

(** val iattr_mark :
    coq_PosPolicy -> coq_InlineCursor -> string -> attr -> string -> ostate
    -> iscan **)

let iattr_mark h h0 src a txt o =
  let spec_start =
    spot_before h0.cursor_start
      ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      (lbrace, src))
  in
  let spec = pspan h { span_start = spec_start; span_stop = h0.cursor_stop }
  in
  IText (false, "", (Some rbrace),
  (omark a spec (flush_text_to_at h h0 spec_start txt o)))

(** val iattr_feed :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> aparser -> string
    -> string -> char option -> iscan -> ostate -> iscan **)

let iattr_feed t h h0 c p src txt prev sh o =
  let p' = astep p c in
  if ap_failed p'
  then sh
  else if ap_done p'
       then iattr_mark h h0 src p'.ap_attrs txt o
       else IAttr (p', ((^) src (one c)), txt, prev, (islice_end t sh), o)

(** val idelim_marked : dstyle -> int -> string -> ostate -> iscan **)

let idelim_marked k extra txt o =
  IDelim (k, extra, txt, None, true, o)

(** val oopen_marked :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> dstyle -> bool -> string
    -> ostate -> ostate **)

let oopen_marked t h h0 k cm txt o =
  let open0 = dtoken_span t h h0 k true in
  opush_at k true cm open0 (flush_text_to_at h h0 open0.span_start txt o)

(** val idelim_open_marked :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> dstyle -> bool -> string
    -> ostate -> iscan **)

let idelim_open_marked t h h0 k cm txt o =
  IText (false, "", (Some (dchar t k)), (oopen_marked t h h0 k cm txt o))

(** val idelim_run : dtable -> dstyle -> int -> bool -> string **)

let idelim_run t k extra marked =
  (^) (if marked then one lbrace else "")
    (chars (dchar t k) (Stdlib.succ extra))

(** val ibrace_step_at :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> bool -> char -> string ->
    char option -> ostate -> iscan **)

let ibrace_step_at t h h0 attrs_enabled c txt prev o =
  match dstyle_of t c with
  | Some k -> idelim_marked k 0 txt o
  | None ->
    if attrs_enabled
    then iattr_feed t h h0 c ap_init "" txt prev
           (ilead t h h0 c ((^) txt (one lbrace)) (Some lbrace) o) o
    else let (t0, o') = battr_lit h h0 "" txt o in
         ilead t h h0 c t0 (blit_prev t0) o'

(** val ospan_bang :
    coq_PosPolicy -> coq_InlineCursor -> bool -> ostate -> ostate **)

let ospan_bang h h0 image o =
  if image
  then let (pre, o1) = opop_str o in
       flush_text_at h h0 ((^) pre (one bang)) o1
  else o

(** val ispan_feed :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> inlines -> bool ->
    span -> aparser -> string -> ostate -> iscan **)

let ispan_feed t h h0 c kids image open0 p src o =
  let p' = astep p c in
  if ap_failed p'
  then let (txt, o') = bspan_lit h h0 kids image src o in
       ilead t h h0 c txt (blit_prev txt) o'
  else if ap_done p'
       then let spec_start =
              spot_before h0.cursor_start
                ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                (lbrace, src))
            in
            let spec = { span_start = spec_start; span_stop = h0.cursor_stop }
            in
            IText (false, "", (Some rbrace),
            (oemit
              (add_inline_role h RAttrSpec spec (Node
                ((h.mkpos (inline_prov open0.span_start spec_start)),
                p'.ap_attrs, (Span kids))))
              (ospan_bang h h0 image o)))
       else ISpan (kids, image, open0, p', ((^) src (one c)), o)

(** val inote_step :
    coq_PosPolicy -> coq_InlineCursor -> char -> bool -> bool -> string ->
    span -> ostate -> iscan **)

let inote_step h h0 c esc image label open0 o =
  if esc
  then INote (false, image, ((^) label ((^) (one bslash) (one c))), open0, o)
  else if is_bslash c
       then INote (true, image, label, open0, o)
       else if (=) c rbrack
            then IText (false, "", (Some rbrack),
                   (oemit
                     (imk h open0.span_start h0.cursor_stop
                       (FootnoteReference (normalize_label label)))
                     (ospan_bang h h0 image o)))
            else INote (false, image, ((^) label (one c)), open0, o)

(** val iauto_step :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> string -> string
    -> ostate -> iscan **)

let iauto_step t h h0 c src txt o =
  if (&&) ((&&) ((=) c gt) (auto_body_ok src)) (auto_kind_ok src)
  then let start =
         spot_before h0.cursor_start
           ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (lt, src))
       in
       IText (false, "", (Some gt),
       (oemit (imk h start h0.cursor_stop (auto_node src))
         (flush_text_to_at h h0 start txt o)))
  else if (||) ((||) ((=) c gt) (is_ws c)) ((=) c lt)
       then ilead t h h0 c (auto_lit src txt) (blit_prev (auto_lit src txt)) o
       else IAuto (((^) src (one c)), txt, o)

(** val isymbol_step :
    coq_PosPolicy -> coq_InlineCursor -> char -> string -> string -> ostate
    -> iscan -> iscan **)

let isymbol_step h h0 c alias txt o sh' =
  if symbol_char c
  then ISymbol (((^) alias (one c)), txt, sh', o)
  else if (&&) ((=) c ':') (nonempty_str alias)
       then let start = spot_before h0.cursor_start ((^) (one ':') alias) in
            IText (false, "", (Some c),
            (oemit (imk h start h0.cursor_stop (Symbol alias))
              (flush_text_to_at h h0 start txt o)))
       else sh'

(** val iraw_lit : string -> string **)

let iraw_lit spec =
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (lbrace, spec)

(** val iraw_step_at :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> bool -> char -> string ->
    string -> ostate -> iscan **)

let iraw_step_at t h h0 attrs_enabled c spec txt o =
  let vstop =
    spot_before h0.cursor_start
      ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      (lbrace, spec))
  in
  if (&&) ((=) c rbrace) (raw_spec_ok spec)
  then if raw_inline_enabled t
       then IText (false, "", (Some rbrace),
              (oemit
                (imk h (text_start h0 o) h0.cursor_stop (RawInline
                  ((raw_format spec), txt)))
                o))
       else ilead t h h0 c (iraw_lit spec) (blit_prev (iraw_lit spec))
              (oemit (imk h (text_start h0 o) vstop (Verbatim txt)) o)
  else if (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

            (fun _ -> negb ((=) c eqchar))
            (fun _ _ -> (||) ((=) c rbrace) (raw_stop c))
            spec
       then let closed =
              oemit (imk h (text_start h0 o) vstop (Verbatim txt)) o
            in
            ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

               (fun _ ->
               ibrace_step_at t h h0 attrs_enabled c "" (Some tick) closed)
               (fun _ _ ->
               ilead t h h0 c (iraw_lit spec) (blit_prev (iraw_lit spec))
                 closed)
               spec)
       else IRaw (((^) spec (one c)), txt, o)

(** val bnote_lit :
    coq_PosPolicy -> coq_InlineCursor -> bool -> bool -> string -> ostate ->
    string * ostate **)

let bnote_lit _ _ esc image label o =
  let (pre, o1) = opop_str o in
  (((^) pre
     ((^) (bracket_open image)
       ((^) (one hat) ((^) label (if esc then one bslash else ""))))),
  o1)

(** val wiki_split : string -> string * string option **)

let rec wiki_split s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> ("", None))
    (fun c rest ->
    if is_bslash c
    then ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

            (fun _ -> ((one c), None))
            (fun c' rest' ->
            let (t, al) = wiki_split rest' in
            (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

            (c,
            ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

            (c', t)))), al))
            rest)
    else if (=) c vbar
         then ("", (Some rest))
         else let (t, al) = wiki_split rest in
              (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

              (c, t)), al))
    s

(** val wiki_lit : bool -> bool -> bool -> string -> string **)

let wiki_lit esc rb image region =
  (^) (bracket_open image)
    ((^) (one lbrack)
      ((^) region
        ((^) (if rb then one rbrack else "") (if esc then one bslash else ""))))

(** val bwiki_lit :
    bool -> bool -> bool -> string -> ostate -> string * ostate **)

let bwiki_lit esc rb image region o =
  let (pre, o1) = opop_str o in (((^) pre (wiki_lit esc rb image region)), o1)

(** val iwiki_close :
    coq_PosPolicy -> coq_InlineCursor -> bool -> string -> span -> ostate ->
    iscan **)

let iwiki_close h h0 image region open0 o =
  let (t, al) = wiki_split region in
  ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

     (fun _ ->
     let (txt, o') = bwiki_lit false true image region o in
     IText (false, ((^) txt (one rbrack)), (Some rbrack), o'))
     (fun _ _ -> IText (false, "", (Some rbrack),
     (oemit (imk h open0.span_start h0.cursor_stop (Wikilink (image, t, al)))
       o)))
     t)

(** val iwiki_step :
    coq_PosPolicy -> coq_InlineCursor -> char -> bool -> bool -> bool ->
    string -> span -> ostate -> iscan **)

let iwiki_step h h0 c esc rb image region open0 o =
  if esc
  then IWiki (false, false, image, ((^) region ((^) (one bslash) (one c))),
         open0, o)
  else if (&&) rb ((=) c rbrack)
       then iwiki_close h h0 image region open0 o
       else let region' = if rb then (^) region (one rbrack) else region in
            if is_bslash c
            then IWiki (true, false, image, region', open0, o)
            else if (=) c rbrack
                 then IWiki (false, true, image, region', open0, o)
                 else IWiki (false, false, image, ((^) region' (one c)),
                        open0, o)

(** val ibang_step :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> string -> char
    option -> ostate -> iscan **)

let ibang_step t h h0 c txt _ o =
  if (=) c lbrack
  then IText (false, "", (Some lbrack),
         (bpush h h0 true
           (flush_text_to_at h h0 (previous_spot h0.cursor_start) txt o)))
  else ilead t h h0 c ((^) txt (one bang)) (Some bang) o

(** val idelim_lit : dtable -> dstyle -> string -> bool -> string **)

let idelim_lit t k txt marker =
  (^) txt (ddecay_str t k false marker)

(** val idelim_lit_prev : dtable -> dstyle -> bool -> char option **)

let idelim_lit_prev t k marker =
  Some (if marker then rbrace else dchar t k)

(** val idelim_done :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> dstyle -> string -> char
    option -> bool -> char option -> ostate -> iscan **)

let idelim_done t h h0 k txt before marker next o =
  if (&&) ((&&) (dbare t k before) (negb marker)) (nonspace_at next)
  then IText (false, "", (Some (dchar t k)),
         (opush t h h0 k false
           (flush_text_to_at h h0 (dtoken_span t h h0 k false).span_start txt
             o)))
  else IText (false, (idelim_lit t k txt marker),
         (idelim_lit_prev t k marker), o)

(** val idelim_resolve :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> dstyle -> string -> char
    option -> bool -> char option -> ostate -> iscan **)

let idelim_resolve t h h0 k txt before marker next o =
  if (||) (nonspace_at before) marker
  then (match oclose t h k marker
                (if marker then h0.cursor_stop else h0.cursor_start)
                (flush_text_to_at h h0
                  (dtoken_span t h h0 k false).span_start txt o) with
        | Some o' ->
          IText (false, "", (Some (if marker then rbrace else dchar t k)), o')
        | None ->
          if oclose_barred k marker o
          then IText (false, (idelim_lit t k txt marker),
                 (idelim_lit_prev t k marker), o)
          else idelim_done t h h0 k txt before marker next o)
  else idelim_done t h h0 k txt before marker next o

(** val idollar_step :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> bool -> string ->
    char option -> ostate -> iscan **)

let idollar_step t h h0 c two txt prev o =
  if (=) c dollar
  then if two
       then IDollar (true, ((^) txt (one dollar)), prev, o)
       else IDollar (true, txt, prev, o)
  else if (&&) (is_tick c) (math_enabled t)
       then IOpen ((Stdlib.succ 0), (VMath
              (if two then DisplayMath else InlineMath)),
              (flush_text_to_at h h0
                (spot_before h0.cursor_start (dollars two)) txt o))
       else ilead t h h0 c ((^) txt (dollars two)) (Some dollar) o

(** val iperiod_step :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> bool -> string ->
    char option -> ostate -> iscan **)

let iperiod_step t h h0 c two txt prev o =
  if (=) c period
  then if two
       then IText (false, ((^) txt (typography_ellipsis t)), (Some c), o)
       else IPeriod (true, txt, prev, o)
  else ilead t h h0 c ((^) txt (periods two)) (Some period) o

(** val idash_step :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> int -> string ->
    char option -> ostate -> iscan **)

let idash_step t h h0 c n txt prev o =
  if (=) c hyphen
  then IDash ((Stdlib.succ n), txt, prev, o)
  else if (=) c rbrace
       then (match dstyle_of t hyphen with
             | Some k ->
               if ( <= ) (dwidth t k) n
               then idelim_resolve t h h0 k
                      ((^) txt (typography_dashes t (sub n (dwidth t k))))
                      None true (Some c) o
               else IText (false,
                      ((^) txt ((^) (typography_dashes t n) (one rbrace))),
                      (Some rbrace), o)
             | None ->
               IText (false,
                 ((^) txt ((^) (typography_dashes t n) (one rbrace))), (Some
                 rbrace), o))
       else ilead t h h0 c ((^) txt (typography_dashes t n)) (Some hyphen) o

(** val iresolve :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> iscan -> iscan **)

let iresolve t h h0 st = match st with
| IBrace (txt, _, o) ->
  IText (false, ((^) txt (one lbrace)), (Some lbrace), o)
| IDelim (k, extra, txt, before, marked, o) ->
  if ( < ) (Stdlib.succ extra) (dwidth t k)
  then IText (false, ((^) txt (idelim_run t k extra marked)), (Some
         (dchar t k)), o)
  else if marked
       then idelim_open_marked t h h0 k false txt o
       else idelim_resolve t h h0 k txt before false None o
| IDollar (two, txt, _, o) ->
  IText (false, ((^) txt (dollars two)), (Some dollar), o)
| IPeriod (two, txt, _, o) ->
  IText (false, ((^) txt (periods two)), (Some period), o)
| IDash (n, txt, _, o) ->
  IText (false, ((^) txt (typography_dashes t n)), (Some hyphen), o)
| IBang (txt, _, o) -> IText (false, ((^) txt (one bang)), (Some bang), o)
| IClosed (txt, o) -> IText (false, ((^) txt (one rbrack)), (Some rbrack), o)
| _ -> st

(** val iescws_resolve :
    coq_PosPolicy -> coq_InlineCursor -> string -> string -> char option ->
    ostate -> (string * char option) * ostate **)

let iescws_resolve h h0 ws txt prev o =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> ((((^) txt (one bslash)), (Some bslash)), o))
    (fun c rest ->
    if (=) c ' '
    then ((rest, (str_last rest (Some c))),
           (oemit
             (imk h (spot_before h0.cursor_start ws)
               (spot_before h0.cursor_start rest) NonBreakingSpace)
             (flush_text_to_at h h0
               (spot_before h0.cursor_start ((^) (one bslash) ws)) txt o)))
    else ((((^) txt ((^) (one bslash) ws)), (str_last ws prev)), o))
    ws

(** val iesc_hard :
    coq_PosPolicy -> coq_InlineCursor -> string -> string -> ostate -> ostate **)

let iesc_hard h h0 ws txt o =
  let kept = strip_trailing_ws txt in
  let over = Stdlib.succ
    (( + ) (String.length ws) (sub (String.length txt) (String.length kept)))
  in
  oemit (imk_here h h0 HardBreak)
    (flush_text_to_at h h0 (spot_plus over h0.cursor_start) kept o)

(** val istep_at :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> bool -> char -> iscan ->
    iscan **)

let rec istep_at t h h0 attrs_enabled c = function
| IText (esc, txt, prev, o) ->
  if esc
  then if is_ws c
       then IEscWs ((one c), txt, prev, o)
       else IText (false,
              ((^) txt
                (if is_punct c
                 then one c
                 else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                        ('\\', (one c)))),
              (Some c), o)
  else ilead t h h0 c txt prev o
| IEscWs (ws, txt, prev, o) ->
  if is_ws c
  then IEscWs (((^) ws (one c)), txt, prev, o)
  else let (p, o') = iescws_resolve h h0 ws txt prev o in
       let (txt', prev') = p in ilead t h h0 c txt' prev' o'
| IBrace (txt, prev, o) -> ibrace_step_at t h h0 attrs_enabled c txt prev o
| IDelim (k, extra, txt, before, marked, o) ->
  if ( < ) (Stdlib.succ extra) (dwidth t k)
  then if (=) c (dchar t k)
       then if marked
            then idelim_marked k (Stdlib.succ extra) txt o
            else IDelim (k, (Stdlib.succ extra), txt, before, false, o)
       else ilead t h h0 c ((^) txt (idelim_run t k extra marked)) (Some
              (dchar t k)) o
  else if marked
       then ilead t h h0 c "" (Some (dchar t k))
              (oopen_marked t h h0 k ((=) c rbrace) txt o)
       else let marker = (=) c rbrace in
            let st' = idelim_resolve t h h0 k txt before marker (Some c) o in
            if marker
            then st'
            else (match st' with
                  | IText (esc, txt', prev', o') ->
                    if esc then st' else ilead t h h0 c txt' prev' o'
                  | _ -> st')
| IOpen (n, vk, o) ->
  if is_tick c
  then IOpen ((Stdlib.succ n), vk, o)
  else IVerb (n, 0, (one c), vk, o)
| IVerb (n, run, txt, vk, o) ->
  if is_tick c
  then IVerb (n, (Stdlib.succ run), txt, vk, o)
  else if ( = ) run n
       then if (&&) ((=) c lbrace) (vkind_verb vk)
            then IRaw ("", (trim_verb txt), o)
            else ilead t h h0 c "" (Some tick)
                   (oemit
                     (imk h (text_start h0 o) h0.cursor_start
                       (vnode vk (trim_verb txt)))
                     o)
       else IVerb (n, 0, ((^) txt ((^) (ticks run) (one c))), vk, o)
| IDollar (two, txt, prev, o) -> idollar_step t h h0 c two txt prev o
| IPeriod (two, txt, prev, o) -> iperiod_step t h h0 c two txt prev o
| IDash (n, txt, prev, o) -> idash_step t h h0 c n txt prev o
| IBang (txt, prev, o) -> ibang_step t h h0 c txt prev o
| IClosed (txt, o) ->
  (match if (||) ((||) ((=) c lparen) ((=) c lbrack))
              ((&&) ((=) c lbrace) attrs_enabled)
         then bclose t h
                (flush_text_to_at h h0 (previous_spot h0.cursor_start) txt o)
         else None with
   | Some p ->
     let (p0, o') = p in
     let (p1, open0) = p0 in
     let (kids, image) = p1 in
     if (=) c lparen
     then IDest (kids, image, open0, false, 0, "",
            (idest_open h h0 kids image open0 o'), o')
     else if (=) c lbrack
          then IReference (kids, image, open0, "", o')
          else ISpan (kids, image, open0, ap_init, "", o')
   | None -> ilead t h h0 c ((^) txt (one rbrack)) (Some rbrack) o)
| ISpan (kids, image, open0, p, src, o) ->
  ispan_feed t h h0 c kids image open0 p src o
| IAttr (p, src, txt, prev, sh, o) ->
  if ap_failed (astep p c)
  then istep_at t h h0 false c sh
  else iattr_feed t h h0 c p src txt prev (istep_at t h h0 false c sh) o
| IReference (kids, image, open0, label, o) ->
  if (=) c rbrack
  then let key =
         (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

           (fun _ -> reference_inlines_text kids)
           (fun _ _ -> label)
           label
       in
       IText (false, "", (Some rbrack),
       (oemit
         (imk h open0.span_start h0.cursor_stop
           (bnode image kids (Reference (normalize_label key))))
         o))
  else IReference (kids, image, open0, ((^) label (one c)), o)
| INote (esc, image, label, open0, o) ->
  inote_step h h0 c esc image label open0 o
| IWiki (esc, rb, image, region, open0, o) ->
  iwiki_step h h0 c esc rb image region open0 o
| IDest (kids, image, open0, esc, depth, dst, sh, o) ->
  if esc
  then IDest (kids, image, open0, false, depth,
         ((^) dst
           (if is_punct c
            then one c
            else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                   (bslash, (one c)))),
         (istep_at t h h0 attrs_enabled c sh), o)
  else if is_bslash c
       then IDest (kids, image, open0, true, depth, dst,
              (istep_at t h h0 attrs_enabled c sh), o)
       else if (=) c lparen
            then IDest (kids, image, open0, false, (Stdlib.succ depth),
                   ((^) dst (one lparen)),
                   (istep_at t h h0 attrs_enabled c sh), o)
            else if (=) c rparen
                 then ((fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                         (fun _ -> IText (false, "", (Some rparen),
                         (oemit
                           (imk h open0.span_start h0.cursor_stop
                             (bnode image kids (Direct (drop_nl dst))))
                           o)))
                         (fun d -> IDest (kids, image, open0, false, d,
                         ((^) dst (one rparen)),
                         (istep_at t h h0 attrs_enabled c sh), o))
                         depth)
                 else IDest (kids, image, open0, false, depth,
                        ((^) dst (one c)),
                        (istep_at t h h0 attrs_enabled c sh), o)
| IAuto (src, txt, o) -> iauto_step t h h0 c src txt o
| ISymbol (alias, txt, sh, o) ->
  isymbol_step h h0 c alias txt o (istep_at t h h0 attrs_enabled c sh)
| IRaw (spec, txt, o) -> iraw_step_at t h h0 attrs_enabled c spec txt o

(** val istep :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> iscan -> iscan **)

let istep t h h0 c st =
  istep_at t h h0 (inline_attrs_enabled t) c st

(** val ifinish_ostate_flat :
    coq_PosPolicy -> coq_InlineCursor -> iscan -> ostate **)

let ifinish_ostate_flat h h0 = function
| IText (esc, txt, _, o) ->
  if esc then iesc_hard h h0 "" txt o else flush_text_at h h0 txt o
| IEscWs (ws, txt, _, o) -> iesc_hard h h0 ws txt o
| IBrace (_, _, o) -> o
| IDelim (_, _, _, _, _, o) -> o
| IOpen (_, vk, o) ->
  oemit (imk h (text_start h0 o) h0.cursor_start (vnode vk "")) o
| IVerb (n, run, txt, vk, o) ->
  oemit
    (imk h (text_start h0 o) h0.cursor_start
      (vnode vk
        (trim_verb (if ( = ) run n then txt else (^) txt (ticks run)))))
    o
| IDollar (_, _, _, o) -> o
| IPeriod (_, _, _, o) -> o
| IDash (_, _, _, o) -> o
| IBang (_, _, o) -> o
| IClosed (_, o) -> o
| ISpan (kids, image, _, _, src, o) ->
  let (txt, o') = bspan_lit h h0 kids image src o in flush_text_at h h0 txt o'
| IAttr (_, src, txt, _, _, o) ->
  let (t, o') = battr_lit h h0 src txt o in flush_text_at h h0 t o'
| IReference (kids, image, _, label, o) ->
  let (txt, o') = bref_lit h h0 kids image label o in
  flush_text_at h h0 txt o'
| INote (esc, image, label, _, o) ->
  let (txt, o') = bnote_lit h h0 esc image label o in
  flush_text_at h h0 txt o'
| IWiki (esc, rb, image, region, _, o) ->
  let (txt, o') = bwiki_lit esc rb image region o in flush_text_at h h0 txt o'
| IDest (_, _, _, _, _, _, _, o) -> o
| IAuto (src, txt, o) -> flush_text_at h h0 (auto_lit src txt) o
| ISymbol (_, _, _, o) -> o
| IRaw (spec, txt, o) ->
  let spec_start =
    spot_before h0.cursor_start
      ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      (lbrace, spec))
  in
  flush_text_at h h0 (iraw_lit spec)
    (oemit (imk h (text_start h0 o) spec_start (Verbatim txt)) o)

(** val ifinish_ostate :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> iscan -> ostate **)

let rec ifinish_ostate t h h0 st = match st with
| IAttr (_, _, _, _, sh, _) -> ifinish_ostate t h h0 sh
| IDest (_, _, _, _, _, _, sh, _) -> ifinish_ostate t h h0 sh
| ISymbol (_, _, sh, _) -> ifinish_ostate t h h0 sh
| _ -> ifinish_ostate_flat h h0 (iresolve t h h0 st)

(** val ifinish_rev :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> iscan -> inlines **)

let ifinish_rev t h h0 st =
  ofinish t h (ifinish_ostate t h h0 st)

(** val ifinish :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> iscan -> inlines **)

let ifinish t h h0 st =
  rev (ifinish_rev t h h0 st)

(** val ibreak_flat :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> iscan -> iscan **)

let rec ibreak_flat t h h0 st = match st with
| IText (esc, txt, _, o) ->
  if esc
  then IText (false, "", None, (oword_reset (iesc_hard h h0 "" txt o)))
  else IText (false, "", None,
         (oword_reset
           (oemit (imk_here h h0 SoftBreak) (flush_text_at h h0 txt o))))
| IEscWs (ws, txt, _, o) ->
  IText (false, "", None, (oword_reset (iesc_hard h h0 ws txt o)))
| IOpen (n, vk, o) -> IVerb (n, 0, nl, vk, o)
| IVerb (n, run, txt, vk, o) ->
  if ( = ) run n
  then IText (false, "", None,
         (oword_reset
           (oemit (imk_here h h0 SoftBreak)
             (oemit
               (imk h (text_start h0 o) h0.cursor_start
                 (vnode vk (trim_verb txt)))
               o))))
  else IVerb (n, 0, ((^) txt ((^) (ticks run) nl)), vk, o)
| ISpan (kids, image, open0, p, src, o) ->
  ispan_feed t h h0 nl_char kids image open0 p src o
| IAttr (p, src, txt, prev, sh, o) ->
  iattr_feed t h h0 nl_char p src txt prev sh o
| IReference (kids, image, open0, label, o) ->
  IReference (kids, image, open0, ((^) label nl), o)
| INote (esc, image, label, open0, o) ->
  INote (false, image, ((^) label ((^) (if esc then one bslash else "") nl)),
    open0, o)
| IWiki (esc, rb, image, region, _, o) ->
  let (txt, o') = bwiki_lit esc rb image region o in
  IText (false, "", None,
  (oword_reset (oemit (imk_here h h0 SoftBreak) (flush_text_at h h0 txt o'))))
| IAuto (src, txt, o) ->
  IText (false, "", None,
    (oword_reset
      (oemit (imk_here h h0 SoftBreak)
        (flush_text_at h h0 (auto_lit src txt) o))))
| ISymbol (_, _, sh, _) -> ibreak_flat t h h0 sh
| IRaw (spec, txt, o) ->
  let spec_start =
    spot_before h0.cursor_start
      ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

      (lbrace, spec))
  in
  IText (false, "", None,
  (oword_reset
    (oemit (imk_here h h0 SoftBreak)
      (flush_text_at h h0 (iraw_lit spec)
        (oemit (imk h (text_start h0 o) spec_start (Verbatim txt)) o)))))
| _ -> st

(** val ibreak_at :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> bool -> iscan -> iscan **)

let rec ibreak_at t h h0 attrs_enabled st = match st with
| IAttr (p, src, txt, prev, sh, o) ->
  iattr_feed t h h0 nl_char p src txt prev (ibreak_at t h h0 false sh) o
| IDest (kids, image, open0, esc, depth, dst, sh, o) ->
  IDest (kids, image, open0, false, depth,
    ((^) dst ((^) (if esc then one bslash else "") nl)),
    (ibreak_at t h h0 attrs_enabled sh), o)
| ISymbol (_, _, sh, _) -> ibreak_at t h h0 attrs_enabled sh
| _ -> ibreak_flat t h h0 (iresolve t h h0 st)

(** val ibreak :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> iscan -> iscan **)

let ibreak t h h0 st =
  ibreak_at t h h0 (inline_attrs_enabled t) st

(** val iclosed_at : iscan -> bool **)

let iclosed_at = function
| IText (esc, _, _, o) -> (&&) (negb esc) (null o.os_stk)
| IVerb (n, run, _, _, o) -> (&&) (( = ) run n) (null o.os_stk)
| IWiki (_, _, _, _, _, o) -> null o.os_stk
| IAuto (_, _, o) -> null o.os_stk
| IRaw (_, _, o) -> null o.os_stk
| _ -> false

(** val iresolve_next :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> iscan -> iscan **)

let iresolve_next t h h0 c st = match st with
| IDelim (k, extra, txt, before, marked, o) ->
  if ( < ) (Stdlib.succ extra) (dwidth t k)
  then IText (false, ((^) txt (idelim_run t k extra marked)), (Some
         (dchar t k)), o)
  else if marked
       then idelim_open_marked t h h0 k ((=) c rbrace) txt o
       else idelim_resolve t h h0 k txt before false (Some c) o
| _ -> iresolve t h h0 st

(** val iscan_settled :
    dtable -> coq_PosPolicy -> coq_InlineCursor -> char -> iscan -> bool **)

let iscan_settled t h h0 c st =
  iclosed_at (iresolve_next t h h0 c st)

(** val iscan_str : dtable -> string -> iscan -> iscan **)

let rec iscan_str = (fun t s st ->
     let plain c =
       ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
        || (c >= '0' && c <= '9') || c = ' ')
       && dstyle_of t c = None in
     let i = ref 0 and state = ref st and n = String.length s in
     while !i < n do
       match !state with
       | IText (false, txt, _, o) when plain s.[!i] ->
           let j = ref !i in
           while !j < n && plain s.[!j] do incr j done;
           state := IText (false, txt ^ String.sub s !i (!j - !i),
                           Some s.[!j - 1], o);
           i := !j
       | _ ->
           state := istep t semantic_pos semantic_inline_cursor s.[!i] !state;
           incr i
     done;
     !state)

(** val iscan_lines : dtable -> string list -> iscan -> iscan **)

let rec iscan_lines t l st =
  match l with
  | [] -> st
  | x :: rest ->
    (match rest with
     | [] -> iscan_str t (strip_trailing_ws x) st
     | _ :: _ ->
       iscan_lines t rest
         (ibreak t semantic_pos semantic_inline_cursor (iscan_str t x st)))

(** val iscan_str_off : dtable -> string -> iscan -> iscan **)

let rec iscan_str_off = (fun t s st ->
     let plain c =
       ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
        || (c >= '0' && c <= '9') || c = ' ')
       && dstyle_of t c = None in
     let i = ref 0 and state = ref st and n = String.length s in
     while !i < n do
       match !state with
       | IText (false, txt, _, o) when plain s.[!i] ->
           let j = ref !i in
           while !j < n && plain s.[!j] do incr j done;
           state := IText (false, txt ^ String.sub s !i (!j - !i),
                           Some s.[!j - 1], o);
           i := !j
       | _ ->
           state := istep_at t semantic_pos semantic_inline_cursor false
                      s.[!i] !state;
           incr i
     done;
     !state)

(** val iscan_lines_off : dtable -> int -> string list -> iscan -> iscan **)

let rec iscan_lines_off t k l st =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> iscan_lines t l st)
    (fun k' ->
    match l with
    | [] -> st
    | x :: rest ->
      (match rest with
       | [] -> iscan_str_off t (strip_trailing_ws x) st
       | _ :: _ ->
         iscan_lines_off t k' rest
           (ibreak_at t semantic_pos semantic_inline_cursor false
             (iscan_str_off t x st))))
    k

(** val istart : iscan **)

let istart =
  IText (false, "", None, ostart)

(** val parse_inline_line : dtable -> string -> inlines **)

let parse_inline_line t s =
  ifinish t semantic_pos semantic_inline_cursor (iscan_str t s istart)

(** val para_inlines : dtable -> string list -> inlines **)

let para_inlines t l =
  ifinish t semantic_pos semantic_inline_cursor (iscan_lines t l istart)

(** val para_inlines_off : dtable -> int -> string list -> inlines **)

let para_inlines_off t k l =
  ifinish t semantic_pos semantic_inline_cursor (iscan_lines_off t k l istart)

(** val key_before : char option -> bool **)

let key_before = function
| Some c -> negb (is_ws c)
| None -> false

(** val key_after : string -> bool **)

let key_after rest =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> true)
    (fun c _ -> (=) c ' ')
    rest

(** val key_scan :
    dtable -> string -> string -> char option -> iscan -> (string * string)
    option **)

let rec key_scan t s lbl prev st =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c rest ->
    if (&&) ((&&) ((&&) ((=) c ':') (key_before prev)) (key_after rest))
         (iscan_settled t semantic_pos semantic_inline_cursor c st)
    then Some ((rev_string lbl), (drop_leading_ws rest))
    else key_scan t rest
           ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, lbl)) (Some c)
           (istep t semantic_pos semantic_inline_cursor c st))
    s

(** val key_point : dtable -> string -> (string * string) option **)

let key_point t l =
  key_scan t (drop_leading_ws l) "" None istart

(** val key_label_ok : dtable -> string -> bool **)

let key_label_ok t lbl =
  match para_inlines t (lbl :: []) with
  | [] -> false
  | _ :: l -> (match l with
               | [] -> true
               | _ :: _ -> false)

(** val key_split : dtable -> string -> (string * string) option **)

let key_split t l =
  match key_point t l with
  | Some p ->
    let (lbl, v) = p in if key_label_ok t lbl then Some (lbl, v) else None
  | None -> None
