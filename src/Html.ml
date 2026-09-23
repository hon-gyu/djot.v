open Ast
open Datatypes
open Document
open Inline
open List0
open ListDef
open Nat0
open PeanoNat
open Step
open Strings

(** val escape_char : char -> string **)

let escape_char c =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b b0 b1 b2 b3 b4 b5 b6 ->
    if b
    then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

           (c, "")
    else if b0
         then if b1
              then if b2
                   then if b3
                        then if b4
                             then if b5
                                  then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                                         (c, "")
                                  else if b6
                                       then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                                              (c, "")
                                       else "&gt;"
                             else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                                    (c, "")
                        else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                               (c, "")
                   else if b3
                        then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                               (c, "")
                        else if b4
                             then if b5
                                  then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                                         (c, "")
                                  else if b6
                                       then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                                              (c, "")
                                       else "&amp;"
                             else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                                    (c, "")
              else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                     (c, "")
         else if b1
              then if b2
                   then if b3
                        then if b4
                             then if b5
                                  then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                                         (c, "")
                                  else if b6
                                       then (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                                              (c, "")
                                       else "&lt;"
                             else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                                    (c, "")
                        else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                               (c, "")
                   else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                          (c, "")
              else (* If this appears, you're using String internals. Please don't *)
  (fun (c, s) -> String.make 1 c ^ s)

                     (c, ""))
    c

(** val escape : string -> string **)

let rec escape s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun c s' -> (^) (escape_char c) (escape s'))
    s

(** val escape_attr_char : char -> string **)

let escape_attr_char c =
  (* If this appears, you're using Ascii internals. Please don't *)
 (fun f c ->
  let n = Char.code c in
  let h i = (n land (1 lsl i)) <> 0 in
  f (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7))
    (fun b b0 b1 b2 b3 b4 b5 b6 ->
    if b
    then escape_char c
    else if b0
         then if b1
              then escape_char c
              else if b2
                   then escape_char c
                   else if b3
                        then escape_char c
                        else if b4
                             then if b5
                                  then escape_char c
                                  else if b6 then escape_char c else "&quot;"
                             else escape_char c
         else escape_char c)
    c

(** val escape_attr : string -> string **)

let rec escape_attr s =
  (* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

    (fun _ -> "")
    (fun c s' -> (^) (escape_attr_char c) (escape_attr s'))
    s

(** val render_attrs : attr -> string **)

let render_attrs a =
  String.concat ""
    (map (fun kv ->
      (^) " " ((^) (fst kv) ((^) "=\"" ((^) (escape_attr (snd kv)) "\"")))) a)

type helt =
| HText of string
| HRaw of string
| HVoid of string * bool * attr
| HElem of string * nat * attr * helt list

(** val open_tag : string -> bool -> attr -> string **)

let open_tag tag self a =
  (^) "<" ((^) tag ((^) (render_attrs a) (if self then "/>" else ">")))

(** val serialize_elt : helt -> string **)

let rec serialize_elt e =
  let go =
    let rec go = function
    | [] -> ""
    | e' :: rest -> (^) (serialize_elt e') (go rest)
    in go
  in
  (match e with
   | HText s -> escape s
   | HRaw s -> s
   | HVoid (tag, self, a) -> open_tag tag self a
   | HElem (tag, nls, a, kids) ->
     (^) (open_tag tag false a)
       ((^) (if Nat.leb (S (S O)) nls then nl else "")
         ((^) (go kids)
           ((^) "</"
             ((^) tag ((^) ">" (if Nat.leb (S O) nls then nl else "")))))))

(** val serialize : helt list -> string **)

let rec serialize = function
| [] -> ""
| e :: rest -> (^) (serialize_elt e) (serialize rest)

(** val checkbox_elt : task_status -> helt **)

let checkbox_elt chk =
  HVoid ("input", true,
    (app (("disabled", "") :: (("type", "checkbox") :: []))
      (match chk with
       | Complete -> ("checked", "") :: []
       | Incomplete -> [])))

(** val ref_extra : attr -> attr -> attr **)

let ref_extra a0 a =
  filter (fun kv ->
    match alist_lookup (fst kv) a with
    | Some _ -> false
    | None -> true) a0

(** val ol_attrs : ordered_list_attributes -> attr **)

let ol_attrs oa =
  app
    (if Nat.eqb oa.ol_start (S O)
     then []
     else ("start", (nat_str oa.ol_start)) :: [])
    (match oa.ol_style with
     | Decimal -> []
     | LetterUpper -> ("type", "A") :: []
     | LetterLower -> ("type", "a") :: []
     | RomanUpper -> ("type", "I") :: []
     | RomanLower -> ("type", "i") :: [])

(** val plain_text : inline -> string **)

let rec plain_text il =
  let go =
    let rec go = function
    | [] -> ""
    | n :: rest -> let Node (_, _, x) = n in (^) (plain_text x) (go rest)
    in go
  in
  (match il with
   | Str s -> s
   | Emph ns -> go ns
   | Strong ns -> go ns
   | Highlight ns -> go ns
   | Insert ns -> go ns
   | Delete ns -> go ns
   | Superscript ns -> go ns
   | Subscript ns -> go ns
   | Verbatim s -> s
   | Symbol _ -> ""
   | Math (_, s) -> s
   | Link (ns, _) -> go ns
   | Image (ns, _) -> go ns
   | Span ns -> go ns
   | FootnoteReference _ -> ""
   | UrlLink s -> s
   | EmailLink s -> s
   | Wikilink (_, t, al) -> wiki_display t al
   | RawInline (_, s) -> s
   | NonBreakingSpace -> " "
   | Quoted (_, ns) -> go ns
   | _ -> nl)

(** val plain_texts : inline node list -> string **)

let plain_texts ns =
  String.concat "" (map (fun n -> plain_text (node_contents n)) ns)

(** val render_inline : reference_map -> inline -> attr -> helt list **)

let rec render_inline refs il a =
  let render_ils =
    let rec go = function
    | [] -> []
    | n :: rest ->
      let Node (_, a', x) = n in app (render_inline refs x a') (go rest)
    in go
  in
  (match il with
   | Str s ->
     (match a with
      | [] -> (HText s) :: []
      | _ :: _ -> (HElem ("span", O, a, ((HText s) :: []))) :: [])
   | Emph ils -> (HElem ("em", O, a, (render_ils ils))) :: []
   | Strong ils -> (HElem ("strong", O, a, (render_ils ils))) :: []
   | Highlight ils -> (HElem ("mark", O, a, (render_ils ils))) :: []
   | Insert ils -> (HElem ("ins", O, a, (render_ils ils))) :: []
   | Delete ils -> (HElem ("del", O, a, (render_ils ils))) :: []
   | Superscript ils -> (HElem ("sup", O, a, (render_ils ils))) :: []
   | Subscript ils -> (HElem ("sub", O, a, (render_ils ils))) :: []
   | Verbatim s -> (HElem ("code", O, a, ((HText s) :: []))) :: []
   | Symbol s -> (HText ((^) ":" ((^) s ":"))) :: []
   | Math (style, s) ->
     (match style with
      | DisplayMath ->
        (HElem ("span", O, (("class", "math display") :: []), ((HText
          ((^) "\\[" ((^) s "\\]"))) :: []))) :: []
      | InlineMath ->
        (HElem ("span", O, (("class", "math inline") :: []), ((HText
          ((^) "\\(" ((^) s "\\)"))) :: []))) :: [])
   | Link (ils, tgt) ->
     (match tgt with
      | Direct url ->
        (HElem ("a", O, (("href", url) :: a), (render_ils ils))) :: []
      | Reference label ->
        (match lookup_reference label refs with
         | Some p ->
           let (url, a0) = p in
           (HElem ("a", O, (("href", url) :: (app (ref_extra a0 a) a)),
           (render_ils ils))) :: []
         | None -> (HElem ("a", O, a, (render_ils ils))) :: []))
   | Image (ils, tgt) ->
     (match tgt with
      | Direct url ->
        (HVoid ("img", false, (("alt", (plain_texts ils)) :: (("src",
          url) :: a)))) :: []
      | Reference label ->
        (match lookup_reference label refs with
         | Some p ->
           let (url, a0) = p in
           (HVoid ("img", false, (("alt", (plain_texts ils)) :: (("src",
           url) :: (app (ref_extra a0 a) a))))) :: []
         | None ->
           (HVoid ("img", false, (("alt", (plain_texts ils)) :: a))) :: []))
   | Span ils -> (HElem ("span", O, a, (render_ils ils))) :: []
   | FootnoteReference _ -> []
   | UrlLink url ->
     (HElem ("a", O, (("href", url) :: a), ((HText url) :: []))) :: []
   | EmailLink addr ->
     (HElem ("a", O, (("href", ((^) "mailto:" addr)) :: a), ((HText
       addr) :: []))) :: []
   | Wikilink (embed, t, al) ->
     if embed
     then (HVoid ("img", false, (("alt", (wiki_display t al)) :: (("src",
            t) :: a)))) :: []
     else (HElem ("a", O, (("href", t) :: a), ((HText
            (wiki_display t al)) :: []))) :: []
   | RawInline (fmt, s) -> if (=) fmt "html" then (HRaw s) :: [] else []
   | NonBreakingSpace -> (HRaw "&nbsp;") :: []
   | Quoted (qt, ils) ->
     (match qt with
      | SingleQuotes ->
        app ((HText lsquo) :: []) (app (render_ils ils) ((HText rsquo) :: []))
      | DoubleQuotes ->
        app ((HText ldquo) :: []) (app (render_ils ils) ((HText rdquo) :: [])))
   | SoftBreak -> (HText nl) :: []
   | HardBreak -> (HVoid ("br", false, [])) :: ((HText nl) :: []))

(** val render_inlines : reference_map -> inlines -> helt list **)

let render_inlines refs ils =
  flat_map (fun n -> let Node (_, a, x) = n in render_inline refs x a) ils

(** val align_attr : align -> attr **)

let align_attr = function
| AlignLeft -> ("style", "text-align: left;") :: []
| AlignRight -> ("style", "text-align: right;") :: []
| AlignCenter -> ("style", "text-align: center;") :: []
| AlignDefault -> []

(** val render_cell : reference_map -> cell -> helt **)

let render_cell refs = function
| Cell (ct, al, ils) ->
  let tag = match ct with
            | HeadCell -> "th"
            | BodyCell -> "td" in
  HElem (tag, (S O), (align_attr al), (render_inlines refs ils))

(** val render_row : reference_map -> cell list -> helt **)

let render_row refs r =
  HElem ("tr", (S (S O)), [], (map (render_cell refs) r))

(** val render_caption : reference_map -> inlines option -> helt list **)

let render_caption refs = function
| Some ils -> (HElem ("caption", (S O), [], (render_inlines refs ils))) :: []
| None -> []

(** val render_block : reference_map -> bool -> block -> attr -> helt list **)

let rec render_block refs tight b a =
  let render_bs_at =
    let rec go t = function
    | [] -> []
    | n :: rest ->
      let Node (_, a', x) = n in app (render_block refs t x a') (go t rest)
    in go
  in
  let render_bs = render_bs_at tight in
  let render_items =
    let rec goi sp = function
    | [] -> []
    | it :: rest ->
      (HElem ("li", (S (S O)), [],
        (render_bs_at (match sp with
                       | Tight -> true
                       | Loose -> false) it))) :: (goi sp rest)
    in goi
  in
  let render_def_items =
    let rec god = function
    | [] -> []
    | p :: rest ->
      let (term, it) = p in
      (HElem ("dt", (S O), [], (render_inlines refs term))) :: ((HElem ("dd",
      (S (S O)), [], (render_bs it))) :: (god rest))
    in god
  in
  let render_task_items =
    let rec got sp = function
    | [] -> []
    | p :: rest ->
      let (st, it) = p in
      (HElem ("li", (S (S O)), [], ((checkbox_elt st) :: ((HText
      nl) :: (render_bs_at (match sp with
                            | Tight -> true
                            | Loose -> false) it))))) :: (got sp rest)
    in got
  in
  (match b with
   | Para ils ->
     if tight
     then app (render_inlines refs ils) ((HText nl) :: [])
     else (HElem ("p", (S O), a, (render_inlines refs ils))) :: []
   | Section bs -> (HElem ("section", (S (S O)), a, (render_bs bs))) :: []
   | Heading (lvl, ils) ->
     (HElem (((^) "h" (nat_str lvl)), (S O), a,
       (render_inlines refs ils))) :: []
   | BlockQuote bs ->
     (HElem ("blockquote", (S (S O)), a, (render_bs bs))) :: []
   | CodeBlock (lang, code) ->
     (HElem ("pre", (S O), a, ((HElem ("code", O,
       ((* If this appears, you're using String internals. Please don't *)
 (fun f0 f1 s ->
    let l = String.length s in
    if l = 0 then f0 () else f1 (String.get s 0) (String.sub s 1 (l-1)))

          (fun _ -> [])
          (fun _ _ -> ("class", ((^) "language-" lang)) :: [])
          lang),
       ((HText code) :: []))) :: []))) :: []
   | Div bs -> (HElem ("div", (S (S O)), a, (render_bs bs))) :: []
   | OrderedList (oa, sp, items) ->
     (HElem ("ol", (S (S O)), (app (ol_attrs oa) a),
       (render_items sp items))) :: []
   | BulletList (sp, items) ->
     (HElem ("ul", (S (S O)), a, (render_items sp items))) :: []
   | TaskList (sp, items) ->
     (HElem ("ul", (S (S O)), (("class", "task-list") :: a),
       (render_task_items sp items))) :: []
   | DefinitionList (_, items) ->
     (HElem ("dl", (S (S O)), a, (render_def_items items))) :: []
   | ThematicBreak -> (HVoid ("hr", false, a)) :: ((HText nl) :: [])
   | Table (caption, rows) ->
     (HElem ("table", (S (S O)), a,
       (app (render_caption refs caption) (map (render_row refs) rows)))) :: []
   | RawBlock (fmt, contents) ->
     if (=) fmt "html" then (HRaw contents) :: [] else []
   | Keyed (label, b0) ->
     (HElem ("dl", (S (S O)), (("class", "keyed") :: a), ((HElem ("dt", (S
       O), [], (render_inlines refs label))) :: ((HElem ("dd", (S (S O)), [],
       (render_bs (b0 :: [])))) :: [])))) :: []
   | _ -> [])

type foot_state = { foot_numbers : (string * nat) list; foot_next : nat }

(** val foot_initial : foot_state **)

let foot_initial =
  { foot_numbers = []; foot_next = (S O) }

(** val number_footnote :
    string -> foot_state -> (foot_state * nat) * bool **)

let number_footnote label st =
  let label0 = normalize_label label in
  (match alist_lookup label0 st.foot_numbers with
   | Some n -> ((st, n), false)
   | None ->
     let n = st.foot_next in
     (({ foot_numbers = (app st.foot_numbers ((label0, n) :: []));
     foot_next = (S n) }, n), true))

(** val render_inline_foot :
    reference_map -> foot_state -> inline -> attr -> foot_state * helt list **)

let rec render_inline_foot refs st il a =
  let render_ils =
    let rec go st0 = function
    | [] -> (st0, [])
    | n :: rest ->
      let Node (_, a', x) = n in
      let (st1, s1) = render_inline_foot refs st0 x a' in
      let (st2, s2) = go st1 rest in (st2, (app s1 s2))
    in go
  in
  (match il with
   | Emph ils ->
     let (st', s) = render_ils st ils in
     (st', ((HElem ("em", O, a, s)) :: []))
   | Strong ils ->
     let (st', s) = render_ils st ils in
     (st', ((HElem ("strong", O, a, s)) :: []))
   | Highlight ils ->
     let (st', s) = render_ils st ils in
     (st', ((HElem ("mark", O, a, s)) :: []))
   | Insert ils ->
     let (st', s) = render_ils st ils in
     (st', ((HElem ("ins", O, a, s)) :: []))
   | Delete ils ->
     let (st', s) = render_ils st ils in
     (st', ((HElem ("del", O, a, s)) :: []))
   | Superscript ils ->
     let (st', s) = render_ils st ils in
     (st', ((HElem ("sup", O, a, s)) :: []))
   | Subscript ils ->
     let (st', s) = render_ils st ils in
     (st', ((HElem ("sub", O, a, s)) :: []))
   | Link (ils, target) ->
     let (st', s) = render_ils st ils in
     (match target with
      | Direct url -> (st', ((HElem ("a", O, (("href", url) :: a), s)) :: []))
      | Reference label ->
        (match lookup_reference label refs with
         | Some p ->
           let (url, a0) = p in
           (st', ((HElem ("a", O, (("href",
           url) :: (app (ref_extra a0 a) a)), s)) :: []))
         | None -> (st', ((HElem ("a", O, a, s)) :: []))))
   | Span ils ->
     let (st', s) = render_ils st ils in
     (st', ((HElem ("span", O, a, s)) :: []))
   | FootnoteReference label ->
     let (p, first) = number_footnote label st in
     let (st', n) = p in
     let sn = nat_str n in
     (st', ((HElem ("a", O,
     (app (if first then ("id", ((^) "fnref" sn)) :: [] else [])
       (app (("href", ((^) "#fn" sn)) :: (("role", "doc-noteref") :: [])) a)),
     ((HElem ("sup", O, [], ((HText sn) :: []))) :: []))) :: []))
   | Quoted (q, ils) ->
     let (st', s) = render_ils st ils in
     (match q with
      | SingleQuotes ->
        (st', (app ((HText lsquo) :: []) (app s ((HText rsquo) :: []))))
      | DoubleQuotes ->
        (st', (app ((HText ldquo) :: []) (app s ((HText rdquo) :: [])))))
   | _ -> (st, (render_inline refs il a)))

(** val render_inlines_foot :
    reference_map -> foot_state -> inlines -> foot_state * helt list **)

let render_inlines_foot refs st ils =
  fold_left (fun acc n ->
    let (st0, out) = acc in
    let (st1, s) = let Node (_, a, x) = n in render_inline_foot refs st0 x a
    in
    (st1, (app out s))) ils (st, [])

(** val render_cell_foot :
    reference_map -> foot_state -> cell -> foot_state * helt **)

let render_cell_foot refs st = function
| Cell (ct, al, ils) ->
  let tag = match ct with
            | HeadCell -> "th"
            | BodyCell -> "td" in
  let (st', s) = render_inlines_foot refs st ils in
  (st', (HElem (tag, (S O), (align_attr al), s)))

(** val render_cells_foot :
    reference_map -> foot_state -> cell list -> foot_state * helt list **)

let rec render_cells_foot refs st = function
| [] -> (st, [])
| c :: rest ->
  let (st1, e) = render_cell_foot refs st c in
  let (st2, es) = render_cells_foot refs st1 rest in (st2, (e :: es))

(** val render_rows_foot :
    reference_map -> foot_state -> cell list list -> foot_state * helt list **)

let rec render_rows_foot refs st = function
| [] -> (st, [])
| r :: rest ->
  let (st1, cells) = render_cells_foot refs st r in
  let (st2, es) = render_rows_foot refs st1 rest in
  (st2, ((HElem ("tr", (S (S O)), [], cells)) :: es))

(** val render_caption_foot :
    reference_map -> foot_state -> inlines option -> foot_state * helt list **)

let render_caption_foot refs st = function
| Some ils ->
  let (st', s) = render_inlines_foot refs st ils in
  (st', ((HElem ("caption", (S O), [], s)) :: []))
| None -> (st, [])

(** val render_block_foot :
    reference_map -> foot_state -> bool -> block -> attr -> foot_state * helt
    list **)

let rec render_block_foot refs st tight b a =
  let render_bs_at =
    let rec go st0 t = function
    | [] -> (st0, [])
    | n :: rest ->
      let Node (_, a', x) = n in
      let (st1, s1) = render_block_foot refs st0 t x a' in
      let (st2, s2) = go st1 t rest in (st2, (app s1 s2))
    in go
  in
  let render_items =
    let rec goi st0 sp = function
    | [] -> (st0, [])
    | it :: rest ->
      let t = match sp with
              | Tight -> true
              | Loose -> false in
      let (st1, s1) = render_bs_at st0 t it in
      let (st2, s2) = goi st1 sp rest in
      (st2, ((HElem ("li", (S (S O)), [], s1)) :: s2))
    in goi
  in
  let render_task_items =
    let rec got st0 sp = function
    | [] -> (st0, [])
    | p :: rest ->
      let (chk, it) = p in
      let t = match sp with
              | Tight -> true
              | Loose -> false in
      let (st1, s1) = render_bs_at st0 t it in
      let (st2, s2) = got st1 sp rest in
      (st2, ((HElem ("li", (S (S O)), [], ((checkbox_elt chk) :: ((HText
      nl) :: s1)))) :: s2))
    in got
  in
  let render_def_items =
    let rec god st0 = function
    | [] -> (st0, [])
    | p :: rest ->
      let (term, it) = p in
      let (st1, s1) = render_inlines_foot refs st0 term in
      let (st2, s2) = render_bs_at st1 tight it in
      let (st3, s3) = god st2 rest in
      (st3, ((HElem ("dt", (S O), [], s1)) :: ((HElem ("dd", (S (S O)), [],
      s2)) :: s3)))
    in god
  in
  (match b with
   | Para ils ->
     let (st', s) = render_inlines_foot refs st ils in
     if tight
     then (st', (app s ((HText nl) :: [])))
     else (st', ((HElem ("p", (S O), a, s)) :: []))
   | Section bs ->
     let (st', s) = render_bs_at st tight bs in
     (st', ((HElem ("section", (S (S O)), a, s)) :: []))
   | Heading (lvl, ils) ->
     let (st', s) = render_inlines_foot refs st ils in
     (st', ((HElem (((^) "h" (nat_str lvl)), (S O), a, s)) :: []))
   | BlockQuote bs ->
     let (st', s) = render_bs_at st tight bs in
     (st', ((HElem ("blockquote", (S (S O)), a, s)) :: []))
   | Div bs ->
     let (st', s) = render_bs_at st tight bs in
     (st', ((HElem ("div", (S (S O)), a, s)) :: []))
   | OrderedList (oa, sp, items) ->
     let (st', s) = render_items st sp items in
     (st', ((HElem ("ol", (S (S O)), (app (ol_attrs oa) a), s)) :: []))
   | BulletList (sp, items) ->
     let (st', s) = render_items st sp items in
     (st', ((HElem ("ul", (S (S O)), a, s)) :: []))
   | TaskList (sp, items) ->
     let (st', s) = render_task_items st sp items in
     (st', ((HElem ("ul", (S (S O)), (("class", "task-list") :: a),
     s)) :: []))
   | DefinitionList (_, items) ->
     let (st', s) = render_def_items st items in
     (st', ((HElem ("dl", (S (S O)), a, s)) :: []))
   | Table (caption, rows) ->
     let (st1, s1) = render_caption_foot refs st caption in
     let (st2, s2) = render_rows_foot refs st1 rows in
     (st2, ((HElem ("table", (S (S O)), a, (app s1 s2))) :: []))
   | Keyed (label, b0) ->
     let (st1, s1) = render_inlines_foot refs st label in
     let (st2, s2) = render_bs_at st1 tight (b0 :: []) in
     (st2, ((HElem ("dl", (S (S O)), (("class", "keyed") :: a), ((HElem
     ("dt", (S O), [], s1)) :: ((HElem ("dd", (S (S O)), [],
     s2)) :: [])))) :: []))
   | _ -> (st, (render_block refs tight b a)))

(** val render_blocks_foot :
    reference_map -> foot_state -> blocks -> foot_state * helt list **)

let render_blocks_foot refs st bs =
  fold_left (fun acc n ->
    let (st0, out) = acc in
    let (st1, s) =
      let Node (_, a, b) = n in render_block_foot refs st0 false b a
    in
    (st1, (app out s))) bs (st, [])

(** val note_backlink : nat -> helt **)

let note_backlink n =
  HElem ("a", O, (("href", ((^) "#fnref" (nat_str n))) :: (("role",
    "doc-backlink") :: [])), ((HText "\226\134\169\239\184\142") :: []))

(** val add_backlink : helt list -> nat -> helt list **)

let add_backlink body n =
  match rev body with
  | [] -> app body ((HElem ("p", (S O), [], ((note_backlink n) :: []))) :: [])
  | h :: earlier ->
    (match h with
     | HElem (tag, nls, a, kids) ->
       if (=) tag "p"
       then rev ((HElem (tag, nls, a,
              (app kids ((note_backlink n) :: [])))) :: earlier)
       else app body ((HElem ("p", (S O), [],
              ((note_backlink n) :: []))) :: [])
     | _ ->
       app body ((HElem ("p", (S O), [], ((note_backlink n) :: []))) :: []))

(** val render_note_defs :
    reference_map -> foot_state -> note_map -> foot_state * (string * helt
    list) list **)

let rec render_note_defs refs st = function
| [] -> (st, [])
| p :: rest ->
  let (label, bs) = p in
  let (st1, body) = render_blocks_foot refs st bs in
  let (st2, rendered) = render_note_defs refs st1 rest in
  (st2, ((label, body) :: rendered))

(** val label_at : nat -> (string * nat) list -> string option **)

let rec label_at n = function
| [] -> None
| p :: rest ->
  let (label, n') = p in if Nat.eqb n n' then Some label else label_at n rest

(** val rendered_note_at :
    nat -> foot_state -> (string * helt list) list -> helt list **)

let rendered_note_at n st rendered =
  match label_at n st.foot_numbers with
  | Some label ->
    (match alist_lookup label rendered with
     | Some s -> s
     | None -> [])
  | None -> []

(** val render_note_items :
    nat -> nat -> foot_state -> (string * helt list) list -> helt list **)

let rec render_note_items fuel n st rendered =
  match fuel with
  | O -> []
  | S fuel' ->
    (HElem ("li", (S (S O)), (("id", ((^) "fn" (nat_str n))) :: []),
      (add_backlink (rendered_note_at n st rendered) n))) :: (render_note_items
                                                               fuel' (S n) st
                                                               rendered)

(** val render_document_foot :
    reference_map -> blocks -> note_map -> helt list **)

let render_document_foot refs blocks0 notes =
  let (st1, body) = render_blocks_foot refs foot_initial blocks0 in
  if Nat.eqb st1.foot_next (S O)
  then body
  else let (st2, rendered) = render_note_defs refs st1 notes in
       app body ((HElem ("section", (S (S O)), (("role",
         "doc-endnotes") :: []), ((HVoid ("hr", false, [])) :: ((HText
         nl) :: ((HElem ("ol", (S (S O)), [],
         (render_note_items (sub st2.foot_next (S O)) (S O) st2 rendered))) :: []))))) :: [])

(** val doc_refs : doc -> reference_map **)

let doc_refs d =
  app d.doc_references d.doc_auto_references

(** val html_tree : doc -> helt list **)

let html_tree d =
  render_document_foot (doc_refs d) d.doc_blocks d.doc_footnotes

(** val render_html : doc -> string **)

let render_html d =
  serialize (html_tree d)

(** val convert : string -> string **)

let convert s =
  render_html (parse_doc djot_table djot_bconfig semantic_pos s)
