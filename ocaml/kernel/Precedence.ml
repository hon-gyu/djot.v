open Ast
open Attributes
open Bool0
open Datatypes
open InlineTable
open InlineView
open List0
open Nat0
open String0
open Strings

(** val self_row : dtable -> dstyle -> bool **)

let self_row t k =
  match dsyntax_of t k with
  | DOff -> false
  | DBareAfterBreak -> false
  | _ -> (match t.dc_decay k with
          | DDSelf -> true
          | DDPair (_, _, _) -> false)

(** val bare_opens : dtable -> dstyle -> bool **)

let bare_opens t k =
  match dsyntax_of t k with
  | DBare -> true
  | _ -> false

(** val in_alphabet : dtable -> char -> bool **)

let in_alphabet t c =
  (&&)
    ((&&)
      ((&&) (negb ((=) c nl_char))
        ((||)
          ((||)
            ((||)
              ((||)
                ((||)
                  ((||) ((||) ((=) c lbrace) ((=) c rbrace)) ((=) c lbrack))
                  ((=) c rbrack))
                (is_tick c))
              ((=) c lt))
            ((&&) ((=) c dollar) (negb (dollar_math_enabled t))))
          ((&&) (negb (dreserved c))
            (negb ((&&) (holes_enabled t) ((=) c percent))))))
      (negb ((=) c hyphen)))
    (match dstyle_of t c with
     | Some k ->
       (&&) (self_row t k) (negb ((||) ((=) c lparen) ((=) c rparen)))
     | None -> true)

(** val starts_row : dtable -> string -> bool **)

let starts_row t s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> false)
    (fun d _ -> is_delim t d)
    s

(** val starts_with : char -> string -> bool **)

let starts_with c s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> false)
    (fun d _ -> (=) d c)
    s

(** val fmt_go : string -> string option **)

let rec fmt_go s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c r ->
    if (=) c rbrace
    then Some ""
    else if (||) (raw_stop c) ((=) c nl_char)
         then None
         else option_map (fun x ->
                (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                (c, x)) (fmt_go r))
    s

(** val raw_spec : string -> string option **)

let raw_spec s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun b s0 ->
    (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

      (fun _ -> None)
      (fun e r ->
      if (&&) ((=) b lbrace) ((=) e eqchar)
      then (match fmt_go r with
            | Some s1 ->
              ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                 (fun _ -> None)
                 (fun c f -> Some
                 ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                 (c, f)))
                 s1)
            | None -> None)
      else None)
      s0)
    s

(** val auto_stop : char -> bool **)

let auto_stop c =
  (||) ((||) ((||) ((=) c gt) (is_ws c)) ((=) c lt)) ((=) c nl_char)

(** val auto_go : string -> string * char option **)

let rec auto_go s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> ("", None))
    (fun c r ->
    if auto_stop c
    then ("", (Some c))
    else let (src, stop) = auto_go r in
         (((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

         (c, src)), stop))
    s

(** val auto_clean : string -> bool **)

let rec auto_clean s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> true)
    (fun c r ->
    if auto_stop c then true else (&&) (negb (is_bslash c)) (auto_clean r))
    s

(** val raw_ahead : dtable -> string -> bool **)

let raw_ahead t s =
  (&&) (raw_inline_enabled t)
    (match raw_spec s with
     | Some _ -> true
     | None -> false)

(** val follow_ok : dtable -> char -> string -> bool **)

let follow_ok t c rest =
  (&&)
    ((&&)
      ((&&)
        ((&&) ((||) (negb ((=) c lbrace)) (starts_row t rest))
          (negb
            ((&&) ((=) c lbrack)
              ((||) (starts_with lbrack rest) (starts_with hat rest)))))
        (negb ((&&) ((=) c rbrack) (starts_with lbrace rest))))
      (negb
        ((&&) ((&&) (is_tick c) (starts_with lbrace rest))
          (negb (raw_ahead t rest)))))
    (negb ((&&) ((=) c lt) (negb (auto_clean rest))))

(** val over_alphabet : dtable -> string -> bool **)

let rec over_alphabet t s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> true)
    (fun c rest ->
    if is_bslash c
    then ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

            (fun _ -> true)
            (fun d rest' ->
            (&&)
              ((&&) (negb ((=) d nl_char))
                (negb
                  ((&&) ((&&) (is_tick d) (starts_with lbrace rest'))
                    (negb (raw_ahead t rest')))))
              (over_alphabet t rest'))
            rest)
    else (&&) ((&&) (in_alphabet t c) (follow_ok t c rest))
           (over_alphabet t rest))
    s

type token =
| TText of char
| TBreak
| TDelim of dstyle * bool * bool * bool
| TOpen
| TClose of bool
| TEsc of char
| TEscWs of string
| THard of string
| TVerb of int * int * string * bool * string option
| TDollars of int
| TAuto of string * bool

(** val ws_run : string -> string **)

let rec ws_run s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun c rest ->
    if is_ws c
    then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, (ws_run rest))
    else "")
    s

(** val line_rest : string -> string **)

let rec line_rest s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun c rest ->
    if (=) c nl_char
    then ""
    else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, (line_rest rest)))
    s

(** val tick_run : string -> int **)

let rec tick_run s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> 0)
    (fun c r -> if is_tick c then Stdlib.succ (tick_run r) else 0)
    s

(** val verb_go : int -> int -> string -> (string * int) * bool **)

let rec verb_go n run s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ ->
    if ( = ) run n then (("", 0), true) else (((ticks run), 0), false))
    (fun c rest ->
    if is_tick c
    then let (p, cl) = verb_go n (Stdlib.succ run) rest in
         let (b, l) = p in ((b, (Stdlib.succ l)), cl)
    else if ( = ) run n
         then (("", 0), true)
         else let (p, cl) = verb_go n 0 rest in
              let (b, l) = p in
              ((((^) (ticks run)
                  ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                  (c, b))),
              (Stdlib.succ l)), cl))
    s

(** val verb_tok : dtable -> int -> string -> token * int **)

let verb_tok t pre s =
  let n = tick_run s in
  let (p, closed) = verb_go n 0 (sdrop n s) in
  let (body, used) = p in
  (match if (&&) ((&&) closed (( = ) pre 0)) (raw_inline_enabled t)
         then raw_spec (sdrop (( + ) n used) s)
         else None with
   | Some f ->
     ((TVerb (pre, n, body, closed, (Some f))),
       (( + ) (( + ) n used) (Stdlib.succ (Stdlib.succ (Stdlib.succ
         (String.length f))))))
   | None -> ((TVerb (pre, n, body, closed, None)), (( + ) n used)))

(** val dollar_run : string -> int **)

let rec dollar_run s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> 0)
    (fun c r -> if (=) c dollar then Stdlib.succ (dollar_run r) else 0)
    s

(** val auto_tok : string -> token * int **)

let auto_tok s =
  let (src, stop) = auto_go s in
  if (&&)
       ((&&) (match stop with
              | Some c -> (=) c gt
              | None -> false)
         (auto_body_ok src))
       (auto_kind_ok src)
  then ((TAuto (src, true)), (Stdlib.succ (Stdlib.succ (String.length src))))
  else ((TAuto (src, false)), (Stdlib.succ (String.length src)))

(** val dollar_tok : dtable -> string -> token * int **)

let dollar_tok t s =
  let k = dollar_run s in
  let rest = sdrop k s in
  if (&&) (math_enabled t) (starts_with tick rest)
  then let (t0, l) = verb_tok t k rest in (t0, (( + ) k l))
  else ((TDollars k), k)

(** val at_rbrace : char option -> bool **)

let at_rbrace = function
| Some b -> (=) b rbrace
| None -> false

(** val next_tok : dtable -> char option -> string -> (token * int) option **)

let next_tok t prev s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c rest -> Some
    (if (=) c nl_char
     then (TBreak, (Stdlib.succ 0))
     else if is_bslash c
          then if is_blank (line_rest rest)
               then ((THard (line_rest rest)), (Stdlib.succ
                      (String.length (line_rest rest))))
               else ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                       (fun _ -> ((THard ""), (Stdlib.succ 0)))
                       (fun d _ ->
                       if is_ws d
                       then ((TEscWs (ws_run rest)), (Stdlib.succ
                              (String.length (ws_run rest))))
                       else ((TEsc d), (Stdlib.succ (Stdlib.succ 0))))
                       rest)
          else if is_tick c
               then verb_tok t 0 s
               else if (=) c dollar
                    then dollar_tok t s
                    else if (=) c lt
                         then auto_tok rest
                         else if (=) c lbrack
                              then (TOpen, (Stdlib.succ 0))
                              else if (=) c rbrack
                                   then ((if starts_with lparen rest
                                          then TClose true
                                          else if starts_with lbrack rest
                                               then TClose false
                                               else TText c),
                                          (Stdlib.succ 0))
                                   else if (=) c lbrace
                                        then (match (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                                      (fun _ ->
                                                      None)
                                                      (fun d _ ->
                                                      dstyle_of t d)
                                                      rest with
                                              | Some k ->
                                                if (fun s1 s2 ->
     let l1 = String.length s1 and l2 = String.length s2 in
     l1 <= l2 && String.sub s2 0 l1 = s1)
                                                     (dtoken t k) rest
                                                then ((TDelim (k, true, true,
                                                       false)), (Stdlib.succ
                                                       (dwidth t k)))
                                                else ((TText c), (Stdlib.succ
                                                       0))
                                              | None ->
                                                ((TText c), (Stdlib.succ 0)))
                                        else (match dstyle_of t c with
                                              | Some k ->
                                                if (fun s1 s2 ->
     let l1 = String.length s1 and l2 = String.length s2 in
     l1 <= l2 && String.sub s2 0 l1 = s1)
                                                     (dtoken t k) s
                                                then if at_rbrace
                                                          (get (dwidth t k) s)
                                                     then ((TDelim (k, true,
                                                            false, true)),
                                                            (Stdlib.succ
                                                            (dwidth t k)))
                                                     else ((TDelim (k, false,
                                                            ((&&)
                                                              (bare_opens t k)
                                                              (nonspace_at
                                                                (get
                                                                  (dwidth t k)
                                                                  s))),
                                                            (nonspace_at prev))),
                                                            (dwidth t k))
                                                else ((TText c), (Stdlib.succ
                                                       0))
                                              | None ->
                                                ((TText c), (Stdlib.succ 0)))))
    s

(** val before : string -> int -> char option **)

let before s p =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> None)
    (fun q -> get q s)
    p

(** val tok_at : dtable -> string -> int -> (token * int) option **)

let tok_at t s p =
  next_tok t (before s p) (sdrop p s)

(** val tok_of : dtable -> string -> int -> token option **)

let tok_of t s p =
  option_map fst (tok_at t s p)

(** val para_string : string list -> string **)

let rec para_string = function
| [] -> ""
| x :: rest ->
  (match rest with
   | [] -> strip_trailing_ws x
   | _ :: _ ->
     (^) x
       ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

       (nl_char, (para_string rest))))

type matching = (int * int) list

type key =
| KDelim of dstyle * bool
| KBracket

(** val key_eq : key -> key -> bool **)

let key_eq a b =
  match a with
  | KDelim (k, m) ->
    (match b with
     | KDelim (k', m') -> (&&) (dstyle_eq k k') (eqb m m')
     | KBracket -> false)
  | KBracket -> (match b with
                 | KDelim (_, _) -> false
                 | KBracket -> true)

(** val needs_content : key -> bool **)

let needs_content = function
| KDelim (_, _) -> true
| KBracket -> false

(** val opens_as : token -> key option **)

let opens_as = function
| TDelim (k, mr, opens, _) -> if opens then Some (KDelim (k, mr)) else None
| TOpen -> Some KBracket
| _ -> None

(** val closes_as : token -> key option **)

let closes_as = function
| TDelim (k, mr, _, closes) -> if closes then Some (KDelim (k, mr)) else None
| TClose _ -> Some KBracket
| _ -> None

(** val tok_end : dtable -> string -> int -> int **)

let tok_end t s p =
  match tok_at t s p with
  | Some p0 -> let (_, l) = p0 in ( + ) p l
  | None -> p

(** val dest_close : bool -> int -> int -> string -> int option **)

let rec dest_close esc depth i s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c rest ->
    if esc
    then dest_close false depth (Stdlib.succ i) rest
    else if is_bslash c
         then dest_close true depth (Stdlib.succ i) rest
         else if (=) c lparen
              then dest_close false (Stdlib.succ depth) (Stdlib.succ i) rest
              else if (=) c rparen
                   then ((fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                           (fun _ -> Some i)
                           (fun d ->
                           dest_close false d (Stdlib.succ i) rest)
                           depth)
                   else dest_close false depth (Stdlib.succ i) rest)
    s

(** val label_close : bool -> int -> string -> int option **)

let rec label_close esc i s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c rest ->
    if esc
    then label_close false (Stdlib.succ i) rest
    else if is_bslash c
         then label_close true (Stdlib.succ i) rest
         else if (=) c rbrack
              then Some i
              else label_close false (Stdlib.succ i) rest)
    s

(** val region_end : string -> int -> bool -> int option **)

let region_end s d = function
| true ->
  dest_close false 0 (Stdlib.succ (Stdlib.succ d))
    (sdrop (Stdlib.succ (Stdlib.succ d)) s)
| false ->
  label_close false (Stdlib.succ (Stdlib.succ d))
    (sdrop (Stdlib.succ (Stdlib.succ d)) s)

(** val is_opener : matching -> int -> bool **)

let is_opener m i =
  existsb (fun e -> ( = ) (fst e) i) m

(** val is_closer : matching -> int -> bool **)

let is_closer m j =
  existsb (fun e -> ( = ) (snd e) j) m

(** val resume : string -> int -> bool -> int option **)

let resume s d dest =
  match region_end s d dest with
  | Some e -> Some (Stdlib.succ e)
  | None -> if dest then Some (Stdlib.succ d) else None

(** val chain_next : dtable -> string -> matching -> int -> int option **)

let chain_next t s m p =
  match tok_at t s p with
  | Some p0 ->
    let (t0, l) = p0 in
    (match t0 with
     | TClose b -> if is_closer m p then resume s p b else Some (( + ) p l)
     | _ -> Some (( + ) p l))
  | None -> None

type reading = matching * int list

type litem =
| LOpen of int * key
| LBar of int

(** val has_key : key -> litem list -> bool **)

let rec has_key k = function
| [] -> false
| l :: rest ->
  (match l with
   | LOpen (_, k') -> (||) (key_eq k k') (has_key k rest)
   | LBar _ -> has_key k rest)

type pick_res =
| PFound of int * litem list
| PBarred
| PNone

(** val pick : key -> litem list -> pick_res **)

let rec pick k = function
| [] -> PNone
| l :: rest ->
  (match l with
   | LOpen (p, k') -> if key_eq k k' then PFound (p, rest) else pick k rest
   | LBar _ -> if has_key k rest then PBarred else PNone)

type rstate = { rs_live : litem list; rs_pairs : matching; rs_os : int list }

(** val ropen : int -> key -> bool -> rstate -> rstate **)

let ropen i k op st =
  if op
  then { rs_live = ((LOpen (i, k)) :: st.rs_live); rs_pairs = st.rs_pairs;
         rs_os = (i :: st.rs_os) }
  else st

(** val rstep : dtable -> string -> int -> token -> rstate -> rstate **)

let rstep t s i t0 st =
  match t0 with
  | TDelim (k, mr, op, cl) ->
    (match if cl then pick (KDelim (k, mr)) st.rs_live else PNone with
     | PFound (p, below) ->
       if ( < ) (tok_end t s p) i
       then { rs_live = below; rs_pairs = ((p, i) :: st.rs_pairs); rs_os =
              st.rs_os }
       else ropen i (KDelim (k, mr)) op st
     | PBarred -> st
     | PNone -> ropen i (KDelim (k, mr)) op st)
  | TOpen -> ropen i KBracket true st
  | TClose b ->
    (match pick KBracket st.rs_live with
     | PFound (p, below) ->
       let pairs = (p, i) :: st.rs_pairs in
       (match region_end s i b with
        | Some _ -> { rs_live = below; rs_pairs = pairs; rs_os = st.rs_os }
        | None ->
          if b
          then { rs_live = ((LBar i) :: below); rs_pairs = pairs; rs_os =
                 st.rs_os }
          else { rs_live = below; rs_pairs = pairs; rs_os = st.rs_os })
     | _ -> st)
  | _ -> st

(** val rgo : dtable -> string -> int -> int -> rstate -> rstate **)

let rec rgo t s fuel p st =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> st)
    (fun f ->
    match tok_of t s p with
    | Some t0 ->
      let st' = rstep t s p t0 st in
      (match chain_next t s st'.rs_pairs p with
       | Some q -> rgo t s f q st'
       | None -> st')
    | None -> st)
    fuel

(** val rstart : rstate **)

let rstart =
  { rs_live = []; rs_pairs = []; rs_os = [] }

(** val ref_read : dtable -> string -> reading **)

let ref_read t s =
  let st = rgo t s (Stdlib.succ (String.length s)) 0 rstart in
  (st.rs_pairs, st.rs_os)

(** val str_snoc : string -> inlines -> inlines **)

let str_snoc s out = match out with
| [] -> (mk (Str s)) :: out
| n :: rest ->
  let Node (p, a, x) = n in
  (match a with
   | [] ->
     (match x with
      | Str t -> (Node (p, [], (Str ((^) t s)))) :: rest
      | _ -> (mk (Str s)) :: out)
   | _ :: _ -> (mk (Str s)) :: out)

(** val esc_text : char -> string **)

let esc_text c =
  if is_punct c
  then one c
  else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

         (bslash, (one c))

(** val raw_text : string option -> string **)

let raw_text = function
| Some f ->
  (^)
    ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (lbrace,
    ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (eqchar, f)))) (one rbrace)
| None -> ""

(** val tok_text : dtable -> token -> string **)

let tok_text t = function
| TText c -> one c
| TBreak -> one nl_char
| TDelim (k, marked, opens, _) ->
  if marked
  then if opens
       then (^) (one lbrace) (dtoken t k)
       else (^) (dtoken t k) (one rbrace)
  else dtoken t k
| TOpen -> one lbrack
| TClose _ -> one rbrack
| TEsc c ->
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (bslash, (one c))
| TEscWs ws ->
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (bslash, ws)
| THard ws ->
  (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (bslash, ws)
| TVerb (pre, n, body, closed, raw) ->
  (^) (chars dollar pre)
    ((^) (ticks n)
      ((^) body ((^) (if closed then ticks n else "") (raw_text raw))))
| TDollars k -> chars dollar k
| TAuto (src, ok) ->
  (^)
    ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

    (lt, src)) (if ok then one gt else "")

(** val nbsp_rest : string -> string option **)

let nbsp_rest ws =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> None)
    (fun c rest -> if (=) c ' ' then Some rest else None)
    ws

(** val str_trim : inlines -> inlines **)

let str_trim out = match out with
| [] -> out
| n :: rest ->
  let Node (p, a, x) = n in
  (match a with
   | [] ->
     (match x with
      | Str t ->
        ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

           (fun _ -> rest)
           (fun a0 s -> (Node (p, [], (Str
           ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (a0, s))))) :: rest)
           (strip_trailing_ws t))
      | _ -> out)
   | _ :: _ -> out)

(** val no_nl : string -> string **)

let rec no_nl s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun c rest ->
    if (=) c nl_char
    then no_nl rest
    else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, (no_nl rest)))
    s

(** val dest_text : bool -> string -> string **)

let rec dest_text esc s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun c rest ->
    if esc
    then (^) (esc_text c) (dest_text false rest)
    else if is_bslash c
         then dest_text true rest
         else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                (c, (dest_text false rest)))
    s

(** val region_text : string -> int -> int -> bool -> string **)

let region_text s d e dest =
  let txt =
    substring (Stdlib.succ (Stdlib.succ d))
      (sub e (Stdlib.succ (Stdlib.succ d))) s
  in
  if dest then dest_text false txt else txt

(** val region_node : bool -> inlines -> string -> inline **)

let region_node dest kids txt =
  if dest
  then Link (kids, (Direct (no_nl txt)))
  else Link (kids, (Reference
         (normalize_label
           ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

              (fun _ -> reference_inlines_text kids)
              (fun _ _ -> txt)
              txt))))

type tkind =
| TKDelim of dstyle
| TKBracket

type tframes = (tkind * inlines) list

(** val temit : inline node -> tframes -> inlines -> tframes * inlines **)

let temit n fs top =
  match fs with
  | [] -> ([], (n :: top))
  | p :: rest -> let (k, acc) = p in (((k, (n :: acc)) :: rest), top)

(** val temit_str : string -> tframes -> inlines -> tframes * inlines **)

let temit_str s fs top =
  match fs with
  | [] -> ([], (str_snoc s top))
  | p :: rest -> let (k, acc) = p in (((k, (str_snoc s acc)) :: rest), top)

(** val ttrim : tframes -> inlines -> tframes * inlines **)

let ttrim fs top =
  match fs with
  | [] -> ([], (str_trim top))
  | p :: rest -> let (k, acc) = p in (((k, (str_trim acc)) :: rest), top)

(** val temit_all : inlines -> tframes -> inlines -> tframes * inlines **)

let rec temit_all ns fs top =
  match ns with
  | [] -> (fs, top)
  | n :: rest ->
    let Node (_, a, x) = n in
    (match a with
     | [] ->
       (match x with
        | Str s ->
          let (fs', top') = temit_str s fs top in temit_all rest fs' top'
        | _ -> let (fs', top') = temit n fs top in temit_all rest fs' top')
     | _ :: _ -> let (fs', top') = temit n fs top in temit_all rest fs' top')

(** val is_hard : token -> bool **)

let is_hard = function
| THard _ -> true
| _ -> false

(** val verb_node : int -> string option -> string -> inline **)

let verb_node pre raw body =
  match raw with
  | Some f -> RawInline (f, (trim_verb body))
  | None ->
    ((fun fO fS n -> if n = 0 then fO () else fS (n - 1))
       (fun _ -> Verbatim (trim_verb body))
       (fun n ->
       (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
         (fun _ -> Math (InlineMath, (trim_verb body)))
         (fun _ -> Math (DisplayMath, (trim_verb body)))
         n)
       pre)

(** val tstep :
    dtable -> string -> matching -> int -> token -> bool -> tframes -> inlines
    -> tframes * inlines **)

let tstep t s m i t0 hard fs top =
  match t0 with
  | TBreak -> if hard then (fs, top) else temit (mk SoftBreak) fs top
  | TDelim (k, _, _, _) ->
    if is_opener m i
    then ((((TKDelim k), []) :: fs), top)
    else if is_closer m i
         then (match fs with
               | [] -> temit_str (tok_text t t0) fs top
               | p :: fs0 ->
                 let (t1, acc) = p in
                 (match t1 with
                  | TKDelim k' -> temit (mk (dnode k' (rev acc))) fs0 top
                  | TKBracket -> temit_str (tok_text t t0) fs top))
         else temit_str (tok_text t t0) fs top
  | TOpen ->
    if is_opener m i
    then (((TKBracket, []) :: fs), top)
    else temit_str (tok_text t t0) fs top
  | TClose b ->
    if is_closer m i
    then (match fs with
          | [] -> temit_str (tok_text t t0) fs top
          | p :: fs0 ->
            let (_, acc) = p in
            let kids = rev acc in
            (match region_end s i b with
             | Some e ->
               temit (mk (region_node b kids (region_text s i e b))) fs0 top
             | None ->
               temit_all
                 ((mk (Str (one lbrack))) :: (app kids
                                               ((mk (Str
                                                  ((^) (one rbrack)
                                                    (if b
                                                     then ""
                                                     else sdrop (Stdlib.succ
                                                            i) s)))) :: [])))
                 fs0 top))
    else temit_str (tok_text t t0) fs top
  | TEsc c -> temit_str (esc_text c) fs top
  | TEscWs ws ->
    (match nbsp_rest ws with
     | Some rest ->
       let (fs', top') = temit (mk NonBreakingSpace) fs top in
       if nonempty_str rest then temit_str rest fs' top' else (fs', top')
     | None -> temit_str (tok_text t t0) fs top)
  | THard _ -> let (fs', top') = ttrim fs top in temit (mk HardBreak) fs' top'
  | TVerb (pre, _, body, _, raw) ->
    let (fs', top') =
      if ( < ) (Stdlib.succ (Stdlib.succ 0)) pre
      then temit_str (chars dollar (sub pre (Stdlib.succ (Stdlib.succ 0)))) fs
             top
      else (fs, top)
    in
    temit (mk (verb_node pre raw body)) fs' top'
  | TAuto (src, ok) ->
    if ok
    then temit (mk (auto_node src)) fs top
    else temit_str (tok_text t t0) fs top
  | _ -> temit_str (tok_text t t0) fs top

(** val tgo :
    dtable -> string -> matching -> int -> int -> bool -> tframes -> inlines
    -> tframes * inlines **)

let rec tgo t s m fuel i hard fs top =
  (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
    (fun _ -> (fs, top))
    (fun f ->
    match tok_of t s i with
    | Some t0 ->
      let (fs', top') = tstep t s m i t0 hard fs top in
      (match chain_next t s m i with
       | Some q -> tgo t s m f q (is_hard t0) fs' top'
       | None -> (fs', top'))
    | None -> (fs, top))
    fuel

(** val tree_of : dtable -> string -> matching -> inlines **)

let tree_of t s m =
  rev (snd (tgo t s m (Stdlib.succ (String.length s)) 0 false [] []))
