open Bool0
open Datatypes
open InlineTable
open InlineView
open ListDef
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
          ((||) ((||) ((||) ((=) c lbrace) ((=) c rbrace)) ((=) c lbrack))
            ((=) c rbrack))
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

(** val follow_ok : dtable -> char -> string -> bool **)

let follow_ok t c rest =
  (&&)
    ((&&) ((||) (negb ((=) c lbrace)) (starts_row t rest))
      (negb
        ((&&) ((=) c lbrack)
          ((||) (starts_with lbrack rest) (starts_with hat rest)))))
    (negb ((&&) ((=) c rbrack) (starts_with lbrace rest)))

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
            (fun _ rest' -> over_alphabet t rest')
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

(** val at_rbrace : char option -> bool **)

let at_rbrace = function
| Some b -> (=) b rbrace
| None -> false

(** val lex : dtable -> char option -> int -> string -> token list **)

let rec lex t prev skip s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> [])
    (fun c rest ->
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ ->
      if is_bslash c
      then (if is_blank rest
            then THard rest
            else ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                    (fun _ -> THard "")
                    (fun d _ ->
                    if is_ws d then TEscWs (ws_run rest) else TEsc d)
                    rest)) :: (lex t (Some c)
                                (if is_blank rest
                                 then String.length rest
                                 else ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                         (fun _ -> 0)
                                         (fun d _ ->
                                         if is_ws d
                                         then String.length (ws_run rest)
                                         else Stdlib.succ 0)
                                         rest))
                                rest)
      else if (=) c lbrack
           then TOpen :: (lex t (Some c) 0 rest)
           else if (=) c rbrack
                then (if starts_with lparen rest
                      then TClose true
                      else if starts_with lbrack rest
                           then TClose false
                           else TText c) :: (lex t (Some c) 0 rest)
                else if (=) c lbrace
                     then (match (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

                                   (fun _ -> None)
                                   (fun d _ -> dstyle_of t d)
                                   rest with
                           | Some k ->
                             if (fun s1 s2 ->
     let l1 = String.length s1 and l2 = String.length s2 in
     l1 <= l2 && String.sub s2 0 l1 = s1)
                                  (dtoken t k) rest
                             then (TDelim (k, true, true,
                                    false)) :: (lex t (Some c) (dwidth t k)
                                                 rest)
                             else (TText c) :: (lex t (Some c) 0 rest)
                           | None -> (TText c) :: (lex t (Some c) 0 rest))
                     else (match dstyle_of t c with
                           | Some k ->
                             if (fun s1 s2 ->
     let l1 = String.length s1 and l2 = String.length s2 in
     l1 <= l2 && String.sub s2 0 l1 = s1)
                                  (dtoken t k) s
                             then if at_rbrace (get (dwidth t k) s)
                                  then (TDelim (k, true, false,
                                         true)) :: (lex t (Some c)
                                                     (dwidth t k) rest)
                                  else (TDelim (k, false,
                                         ((&&) (bare_opens t k)
                                           (nonspace_at (get (dwidth t k) s))),
                                         (nonspace_at prev))) :: (lex t (Some
                                                                   c)
                                                                   (pred
                                                                    (dwidth t
                                                                    k))
                                                                   rest)
                             else (TText c) :: (lex t (Some c) 0 rest)
                           | None -> (TText c) :: (lex t (Some c) 0 rest)))
      (fun n -> lex t (Some c) n rest)
      skip)
    s

(** val tokens : dtable -> string -> token list **)

let tokens t s =
  lex t None 0 s

(** val para_tokens : dtable -> string list -> token list **)

let rec para_tokens t = function
| [] -> []
| x :: rest ->
  (match rest with
   | [] -> tokens t (strip_trailing_ws x)
   | _ :: _ -> app (tokens t x) (TBreak :: (para_tokens t rest)))

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

(** val paren_close : int -> int -> token list -> int option **)

let rec paren_close depth i = function
| [] -> None
| t :: rest ->
  (match t with
   | TText c ->
     if (=) c lparen
     then paren_close (Stdlib.succ depth) (Stdlib.succ i) rest
     else if (=) c rparen
          then ((fun fO fS n -> if n = 0 then fO () else fS (n - 1))
                  (fun _ -> Some i)
                  (fun d -> paren_close d (Stdlib.succ i) rest)
                  depth)
          else paren_close depth (Stdlib.succ i) rest
   | _ -> paren_close depth (Stdlib.succ i) rest)

(** val rbrack_at : int -> token list -> int option **)

let rec rbrack_at i = function
| [] -> None
| t :: rest ->
  (match t with
   | TText c ->
     if (=) c rbrack then Some i else rbrack_at (Stdlib.succ i) rest
   | TClose _ -> Some i
   | _ -> rbrack_at (Stdlib.succ i) rest)

(** val region_end : token list -> int -> bool -> int option **)

let region_end ts d = function
| true ->
  paren_close 0 (Stdlib.succ (Stdlib.succ d))
    (skipn (Stdlib.succ (Stdlib.succ d)) ts)
| false ->
  rbrack_at (Stdlib.succ (Stdlib.succ d))
    (skipn (Stdlib.succ (Stdlib.succ d)) ts)

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

type rmode =
| RNormal
| RInert of int option

type rstate = { rs_live : litem list; rs_pairs : matching; rs_os : int list;
                rs_mode : rmode }

(** val ropen : int -> key -> bool -> rstate -> rstate **)

let ropen i k op s =
  if op
  then { rs_live = ((LOpen (i, k)) :: s.rs_live); rs_pairs = s.rs_pairs;
         rs_os = (i :: s.rs_os); rs_mode = s.rs_mode }
  else s

(** val rstep : token list -> int -> token -> rstate -> rstate **)

let rstep ts i t s =
  match s.rs_mode with
  | RNormal ->
    (match t with
     | TDelim (k, mr, op, cl) ->
       (match if cl then pick (KDelim (k, mr)) s.rs_live else PNone with
        | PFound (p, below) ->
          if ( < ) (Stdlib.succ p) i
          then { rs_live = below; rs_pairs = ((p, i) :: s.rs_pairs); rs_os =
                 s.rs_os; rs_mode = RNormal }
          else ropen i (KDelim (k, mr)) op s
        | PBarred -> s
        | PNone -> ropen i (KDelim (k, mr)) op s)
     | TOpen -> ropen i KBracket true s
     | TClose b ->
       (match pick KBracket s.rs_live with
        | PFound (p, below) ->
          let pairs = (p, i) :: s.rs_pairs in
          (match region_end ts i b with
           | Some e ->
             { rs_live = below; rs_pairs = pairs; rs_os = s.rs_os; rs_mode =
               (RInert (Some e)) }
           | None ->
             if b
             then { rs_live = ((LBar i) :: below); rs_pairs = pairs; rs_os =
                    s.rs_os; rs_mode = RNormal }
             else { rs_live = below; rs_pairs = pairs; rs_os = s.rs_os;
                    rs_mode = (RInert None) })
        | _ -> s)
     | _ -> s)
  | RInert e0 ->
    (match e0 with
     | Some e ->
       if ( = ) i e
       then { rs_live = s.rs_live; rs_pairs = s.rs_pairs; rs_os = s.rs_os;
              rs_mode = RNormal }
       else s
     | None -> s)

(** val rrun : token list -> int -> token list -> rstate -> rstate **)

let rec rrun ts i rest s =
  match rest with
  | [] -> s
  | t :: more -> rrun ts (Stdlib.succ i) more (rstep ts i t s)

(** val rstart : rstate **)

let rstart =
  { rs_live = []; rs_pairs = []; rs_os = []; rs_mode = RNormal }

(** val ref_read : token list -> reading **)

let ref_read ts =
  let s = rrun ts 0 ts rstart in (s.rs_pairs, s.rs_os)
