open Ast
open Attributes
open Bool0
open Datatypes
open InlineTable
open InlineView
open ListDef
open Render
open Step
open Strings

(** val attr_eqb : attr -> attr -> bool **)

let rec attr_eqb a b =
  match a with
  | [] -> (match b with
           | [] -> true
           | _ :: _ -> false)
  | p :: a' ->
    let (k, v) = p in
    (match b with
     | [] -> false
     | p0 :: b' ->
       let (l, w) = p0 in (&&) ((&&) ((=) k l) ((=) v w)) (attr_eqb a' b'))

(** val target_eqb : target -> target -> bool **)

let target_eqb x y =
  match x with
  | Direct s -> (match y with
                 | Direct t -> (=) s t
                 | Reference _ -> false)
  | Reference s -> (match y with
                    | Direct _ -> false
                    | Reference t -> (=) s t)

(** val opt_eqb : string option -> string option -> bool **)

let opt_eqb x y =
  match x with
  | Some s -> (match y with
               | Some t -> (=) s t
               | None -> false)
  | None -> (match y with
             | Some _ -> false
             | None -> true)

(** val inline_eqb : inline -> inline -> bool **)

let rec inline_eqb x y =
  let go =
    let rec go xs ys =
      match xs with
      | [] -> (match ys with
               | [] -> true
               | _ :: _ -> false)
      | n :: xs' ->
        let Node (_, a, x') = n in
        (match ys with
         | [] -> false
         | n0 :: ys' ->
           let Node (_, b, y') = n0 in
           (&&) ((&&) (attr_eqb a b) (inline_eqb x' y')) (go xs' ys'))
    in go
  in
  (match x with
   | Str s -> (match y with
               | Str t -> (=) s t
               | _ -> false)
   | Emph xs -> (match y with
                 | Emph ys -> go xs ys
                 | _ -> false)
   | Strong xs -> (match y with
                   | Strong ys -> go xs ys
                   | _ -> false)
   | Highlight xs -> (match y with
                      | Highlight ys -> go xs ys
                      | _ -> false)
   | Insert xs -> (match y with
                   | Insert ys -> go xs ys
                   | _ -> false)
   | Delete xs -> (match y with
                   | Delete ys -> go xs ys
                   | _ -> false)
   | Superscript xs -> (match y with
                        | Superscript ys -> go xs ys
                        | _ -> false)
   | Subscript xs -> (match y with
                      | Subscript ys -> go xs ys
                      | _ -> false)
   | Verbatim s -> (match y with
                    | Verbatim t -> (=) s t
                    | _ -> false)
   | Symbol s -> (match y with
                  | Symbol t -> (=) s t
                  | _ -> false)
   | Math (style, s) ->
     (match style with
      | DisplayMath ->
        (match y with
         | Math (style0, t) ->
           (match style0 with
            | DisplayMath -> (=) s t
            | InlineMath -> false)
         | _ -> false)
      | InlineMath ->
        (match y with
         | Math (style0, t) ->
           (match style0 with
            | DisplayMath -> false
            | InlineMath -> (=) s t)
         | _ -> false))
   | Link (xs, u) ->
     (match y with
      | Link (ys, v) -> (&&) (target_eqb u v) (go xs ys)
      | _ -> false)
   | Image (xs, u) ->
     (match y with
      | Image (ys, v) -> (&&) (target_eqb u v) (go xs ys)
      | _ -> false)
   | Span (m, xs) ->
     (match y with
      | Span (n, ys) -> (&&) ((=) m n) (go xs ys)
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
   | Quoted (qt, xs) ->
     (match qt with
      | SingleQuotes ->
        (match y with
         | Quoted (qt0, ys) ->
           (match qt0 with
            | SingleQuotes -> go xs ys
            | DoubleQuotes -> false)
         | _ -> false)
      | DoubleQuotes ->
        (match y with
         | Quoted (qt0, ys) ->
           (match qt0 with
            | SingleQuotes -> false
            | DoubleQuotes -> go xs ys)
         | _ -> false))
   | SoftBreak -> (match y with
                   | SoftBreak -> true
                   | _ -> false)
   | HardBreak -> (match y with
                   | HardBreak -> true
                   | _ -> false)
   | Ext_wikilink (e, s, a) ->
     (match y with
      | Ext_wikilink (f, t, b) ->
        (&&) ((&&) (eqb e f) ((=) s t)) (opt_eqb a b)
      | _ -> false)
   | Hole s -> (match y with
                | Hole t -> (=) s t
                | _ -> false))

(** val inlines_eqb : inlines -> inlines -> bool **)

let rec inlines_eqb xs ys =
  match xs with
  | [] -> (match ys with
           | [] -> true
           | _ :: _ -> false)
  | n :: xs' ->
    let Node (_, a, x) = n in
    (match ys with
     | [] -> false
     | n0 :: ys' ->
       let Node (_, b, y) = n0 in
       (&&) ((&&) (attr_eqb a b) (inline_eqb x y)) (inlines_eqb xs' ys'))

(** val text_bytes : string -> (bool * char) list **)

let rec text_bytes s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> [])
    (fun c rest -> (true, c) :: (text_bytes rest))
    s

(** val fixed : string -> (bool * char) list **)

let rec fixed s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> [])
    (fun c rest -> (false, c) :: (fixed rest))
    s

(** val inline_bytes : dtable -> inline -> (bool * char) list **)

let rec inline_bytes t il =
  let go =
    let rec go = function
    | [] -> []
    | n :: rest ->
      let Node (_, a, x) = n in
      (match a with
       | [] -> app (inline_bytes t x) (go rest)
       | _ :: _ ->
         app (inline_bytes t x) (app (fixed (attr_spec a)) (go rest)))
    in go
  in
  let marked = fun k ns ->
    app (fixed (marked_open t k)) (app (go ns) (fixed (marked_close t k "")))
  in
  (match il with
   | Str s -> text_bytes s
   | Emph ns -> marked DEmph ns
   | Strong ns -> marked DStrong ns
   | Highlight ns -> marked DMark ns
   | Insert ns -> marked DInsert ns
   | Delete ns -> marked DDelete ns
   | Superscript ns -> marked DSuper ns
   | Subscript ns -> marked DSub ns
   | Link (ns, tgt) ->
     (match tgt with
      | Direct dst ->
        app (fixed (bracket_open false))
          (app (go ns) (fixed (link_close dst "")))
      | Reference label ->
        app (fixed (bracket_open false))
          (app (go ns) (fixed (ref_close label ""))))
   | Image (ns, tgt) ->
     (match tgt with
      | Direct dst ->
        app (fixed (bracket_open true))
          (app (go ns) (fixed (link_close dst "")))
      | Reference label ->
        app (fixed (bracket_open true))
          (app (go ns) (fixed (ref_close label ""))))
   | Span (name, ns) ->
     app (fixed (tag_open name)) (app (go ns) (fixed (one ']')))
   | Quoted (qt, ns) ->
     (match qt with
      | SingleQuotes -> marked DSQuote ns
      | DoubleQuotes -> marked DDQuote ns)
   | _ -> fixed (inline_text t il))

(** val para_bytes : dtable -> inlines -> (bool * char) list **)

let rec para_bytes t = function
| [] -> []
| n :: rest ->
  let Node (_, a, il) = n in
  (match a with
   | [] ->
     (match il with
      | SoftBreak -> app (fixed nl) (para_bytes t rest)
      | HardBreak ->
        app
          (fixed
            ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

            (bslash, nl)))
          (para_bytes t rest)
      | _ -> app (inline_bytes t il) (para_bytes t rest))
   | _ :: _ ->
     (match il with
      | SoftBreak -> app (fixed nl) (para_bytes t rest)
      | HardBreak ->
        app
          (fixed
            ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

            (bslash, nl)))
          (para_bytes t rest)
      | _ ->
        app (inline_bytes t il)
          (app (fixed (attr_spec a)) (para_bytes t rest))))

(** val full : (bool * char) list -> string **)

let rec full = function
| [] -> ""
| p :: rest ->
  let (d, c) = p in
  if (&&) d (is_punct c)
  then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

         (bslash,
         ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

         (c, (full rest))))
  else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

         (c, (full rest))

(** val line_rev : string -> string -> string **)

let rec line_rev s acc =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> acc)
    (fun c rest ->
    if (=) c '\n'
    then line_rev rest ""
    else line_rev rest
           ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, acc)))
    s

(** val line_forced : dtable -> string -> char -> string -> bool **)

let line_forced t pre c rest =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> (||) (needs_escape t c) (opens_line c))
    (fun _ _ ->
    (&&) ((&&) ((||) ((=) c period) ((=) c rparen)) (marker_core pre))
      ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

         (fun _ -> true)
         (fun d _ -> (||) (is_ws d) ((=) d '\n'))
         rest))
    pre

(** val reads : dtable -> bconfig -> string -> inlines option **)

let reads t k s =
  match parse_blocks t k semantic_line_ix semantic_pos s with
  | [] -> None
  | n :: l ->
    let Node (_, a, x) = n in
    (match a with
     | [] ->
       (match x with
        | Para ils -> (match l with
                       | [] -> Some ils
                       | _ :: _ -> None)
        | _ -> None)
     | _ :: _ -> None)

(** val reads_eqb : inlines option -> inlines option -> bool **)

let reads_eqb x y =
  match x with
  | Some xs -> (match y with
                | Some ys -> inlines_eqb xs ys
                | None -> false)
  | None -> (match y with
             | Some _ -> false
             | None -> true)

(** val spell :
    dtable -> bconfig -> inlines option -> string -> (bool * char) list ->
    string **)

let rec spell t k want out = function
| [] -> out
| p :: rest ->
  let (d, c) = p in
  let tail = full rest in
  let esc =
    (&&) ((&&) d (is_punct c))
      ((||)
        ((||) (match want with
               | Some _ -> false
               | None -> true)
          (line_forced t (line_rev out "") c tail))
        (negb
          (reads_eqb
            (reads t k
              ((^) out
                ((* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                (c, tail))))
            want)))
  in
  spell t k want
    ((^) out
      (if esc
       then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

              (bslash, (one c))
       else one c))
    rest

(** val text_lines_scan : dtable -> bconfig -> inlines -> string list **)

let text_lines_scan t k ils =
  let bs = para_bytes t ils in
  split_lines (spell t k (reads t k (full bs)) "" bs)

(** val render_djot_scan : dtable -> bconfig -> blocks -> string **)

let render_djot_scan t k bs =
  String.concat nl
    (sep_lines
      (map (fun n ->
        render_lines_with t k (text_lines_scan t k) (node_attrs n)
          (node_contents n))
        bs))
