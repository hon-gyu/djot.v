(* ai-disclosure: ai-generated *)

open Djot

let bytes t = Textloc.first_byte t, Textloc.last_byte t
let parse ?(locs = false) s = Doc.of_string ~locs ~frontmatter:true s
let ranges d = List.map (fun n -> bytes (Doc.textloc d n)) (Doc.blocks d)

let same a b =
  For_testing.kernel a = For_testing.kernel b
  && Doc.frontmatter a = Doc.frontmatter b
  && ranges a = ranges b
;;

(* A mapping between two [---] lines is the frontmatter, and the blocks
   are those of the text after it, located in the whole text. *)
let () =
  let src = "---\ntitle: A note\ntags: [a, b]\n---\n# h\n\np\n" in
  let d = parse ~locs:true src in
  let fm = Option.get (Doc.frontmatter d) in
  assert (
    fm.fields = [ "title", `String "A note"; "tags", `A [ `String "a"; `String "b" ] ]);
  assert (fm.text = "title: A note\ntags: [a, b]\n");
  assert (bytes fm.loc = (0, 33));
  assert (Textloc.first_line fm.loc = (1, 0) && Textloc.last_line fm.loc = (4, 31));
  assert (String.sub src 31 3 = "---");
  assert (
    For_testing.kernel (parse src) = For_testing.kernel (Doc.of_string "# h\n\np\n"));
  let rec leaves = function
    | Node (_, _, Block.Section bs) -> List.concat_map leaves bs
    | n -> [ n ]
  in
  let text n =
    let a, b = bytes (Doc.textloc d n) in
    String.sub src a (b - a + 1)
  in
  assert (List.map text (List.concat_map leaves (Doc.blocks d)) = [ "# h"; "p" ]);
  assert (Textloc.first_line (Doc.textloc d (List.hd (Doc.blocks d))) = (5, 35))
;;

(* No line between the delimiters is frontmatter with no field. A closing
   [---] can be the last line, without a newline. *)
let () =
  let fields s =
    Option.map (fun (f : Frontmatter.t) -> f.fields) (Doc.frontmatter (parse s))
  in
  assert (fields "---\n---\n" = Some []);
  assert (fields "---\n---" = Some []);
  assert (fields "--- \n---\t\na\n" = Some []);
  assert (fields "---\na: 1\n---" = Some [ "a", `Float 1. ]);
  assert (fields "---\r\na: x\r\n---\r\nb\r\n" = Some [ "a", `String "x" ])
;;

(* Anything else is djot from its first line. *)
let () =
  List.iter
    (fun src ->
      List.iter
        (fun locs ->
          let d = parse ~locs src in
          assert (Doc.frontmatter d = None);
          assert (same d (Doc.of_string ~locs src)))
        [ false; true ])
    [ ""
    ; "---"
    ; "---\n"
    ; "---\na: 1\n"
    ; "---\n\n---\n"
    ; "---\n\na\n\n---\n"
    ; "---\nfoo\n---\n"
    ; "---\n- a\n- b\n---\n"
    ; "---\na: [b\n---\n"
    ; "----\na: 1\n----\n"
    ; " ---\na: 1\n---\n"
    ; "\n---\na: 1\n---\n"
    ; "---\na: 1\n ---\n"
    ; "a: 1\n---\n"
    ];
  (* Without the argument, never. *)
  assert (Doc.frontmatter (Doc.of_string "---\na: 1\n---\n") = None)
;;

(* The first closing line ends it. *)
let () =
  let d = parse "---\na: 1\n---\nb: 2\n---\n" in
  assert ((Option.get (Doc.frontmatter d)).text = "a: 1\n");
  assert (Html.of_doc d = Html.of_doc (Doc.of_string "b: 2\n---\n"))
;;

let docs =
  [ "---\na: 1\n---\n# h\n\np\n\n- x\n- y\n"
  ; "---\n---\n```\nk\n```\n"
  ; "---\na: 1\nb:\n  - c\n---"
  ; "---\n\np\n\n---\n"
  ; "---\nfoo\n---\nq\n"
  ; "p\n\n---\na: 1\n---\n"
  ; "---\na: 1\n"
  ]
;;

(* Writing a document back gives a text that parses to it. *)
let () =
  List.iter
    (fun src ->
      let d = parse src in
      let d' = parse (Doc.to_string d) in
      assert (For_testing.kernel d = For_testing.kernel d');
      assert (
        Option.map (fun (f : Frontmatter.t) -> f.text) (Doc.frontmatter d)
        = Option.map (fun (f : Frontmatter.t) -> f.text) (Doc.frontmatter d')))
    docs
;;

(* Replacing lines gives the parse of the edited text, for every range,
   whether the edit is after the frontmatter, inside it, makes it or
   unmakes it. *)
let () =
  let news = [ ""; "x\n"; "---\n"; "a: 1\n"; "b: [\n"; "---\nc: 2\n---\n"; "```\n" ] in
  let lines_of s = Array.of_list (Kernel.Strings.split_lines s) in
  List.iter
    (fun locs ->
      List.iter
        (fun src ->
          let t = Source.of_string ~locs ~frontmatter:true src in
          let ls = lines_of src in
          let n = Array.length ls in
          for first = 1 to n + 1 do
            for last = first - 1 to n do
              List.iter
                (fun s ->
                  let t', (c : Source.change) =
                    Source.replace_lines_changed t ~first ~last s
                  in
                  let text = Source.to_string t' in
                  assert (
                    Array.to_list (lines_of text)
                    = Array.to_list (Array.sub ls 0 (first - 1))
                      @ Array.to_list (lines_of s)
                      @ Array.to_list (Array.sub ls last (n - last)));
                  assert (same (Source.doc t') (parse ~locs text));
                  let n' = Array.length (lines_of text) in
                  assert (c.first <= first && last <= c.old_last);
                  assert (c.old_last <= n && n - c.old_last = n' - c.new_last);
                  (* A further edit starts from the same state. *)
                  let again = Source.replace_lines t' ~first:1 ~last:0 "" in
                  assert (same (Source.doc again) (Source.doc t')))
                news
            done
          done)
        docs)
    [ false; true ]
;;

(* An edit after the frontmatter parses only its piece. *)
let () =
  let t = Source.of_string ~frontmatter:true "---\na: 1\n---\np\n\nq\n\nr\n" in
  let _, (c : Source.change) = Source.replace_lines_changed t ~first:6 ~last:6 "x" in
  assert (c = { first = 6; old_last = 7; new_last = 7 });
  let _, (c : Source.change) = Source.replace_lines_changed t ~first:2 ~last:2 "b: 2" in
  assert (c = { first = 1; old_last = 8; new_last = 8 })
;;

let identified d =
  let rec flat bs =
    List.concat_map
      (function
        | Node (_, a, Block.Section (Node (p, _, h) :: rest)) -> Node (p, a, h) :: flat rest
        | n -> [ n ])
      bs
  in
  flat (Doc.blocks d)
;;

let chunks k s =
  let n = String.length s in
  List.init ((n + k - 1) / k) (fun i -> String.sub s (i * k) (min k (n - (i * k))))
;;

(* However the input is cut, the returned blocks followed by [peek] are
   the parse, and [finish] is [Source.of_string]. *)
let () =
  List.iter
    (fun locs ->
      List.iter
        (fun src ->
          let expected = parse ~locs src in
          for k = 1 to String.length src + 1 do
            let bs, t =
              List.fold_left
                (fun (acc, t) x ->
                  let bs, t = Stream.feed_string t x in
                  acc @ bs, t)
                ([], Stream.start ~locs ~frontmatter:true ())
                (chunks k src)
            in
            assert (bs @ Stream.peek t = identified expected);
            let s = Stream.finish t in
            assert (Source.to_string s = src);
            assert (same (Source.doc s) expected);
            let s' = Source.replace_lines s ~first:1 ~last:0 "" in
            assert (same (Source.doc s') expected)
          done)
        docs)
    [ false; true ]
;;

(* Nothing is returned while the lines may still be frontmatter. *)
let () =
  let bs, t = Stream.feed_string (Stream.start ~frontmatter:true ()) "---\n\np\n\n" in
  assert (bs = []);
  assert (List.length (Stream.peek t) = 2);
  let bs, _ = Stream.feed_string t "---\n\n" in
  assert (List.length bs = 3)
;;

(* Made frontmatter reads back as its fields, and a document made with it
   writes it first. *)
let () =
  let fields : (string * Frontmatter.value) list =
    [ "title", `String "A: note"
    ; "n", `Float 3.
    ; "s", `String "1"
    ; "t", `String "true"
    ; "nil", `Null
    ; "ok", `Bool false
    ; "dash", `String "---"
    ; "list", `A [ `String "a"; `O [ "k", `String "v\nw" ] ]
    ; "empty", `O []
    ]
  in
  let fm = Frontmatter.make fields in
  assert (fm.fields = fields && Textloc.is_none fm.loc);
  let d = Doc.make ~frontmatter:fm [ Node.make (Block.Para [ Node.make (Inline.Str "p") ]) ] in
  let d' = parse (Doc.to_string d) in
  assert ((Option.get (Doc.frontmatter d')).fields = fields);
  assert (For_testing.kernel d = For_testing.kernel d');
  assert ((Frontmatter.make []).text = "");
  assert (Doc.to_string (Doc.make ~frontmatter:(Frontmatter.make []) []) = "---\n---");
  (* Numbers that are not finite have a YAML text. *)
  let fm = Frontmatter.make [ "x", `Float Float.nan; "y", `Float Float.infinity ] in
  assert (compare fm.fields [ "x", `Float Float.nan; "y", `Float Float.infinity ] = 0)
;;

(* A text is frontmatter when it would be between delimiters. *)
let () =
  let text s = Option.map (fun (f : Frontmatter.t) -> f.text) (Frontmatter.of_string s) in
  assert (text "a: 1" = Some "a: 1\n");
  assert (text "a: 1\nb: 2\n" = Some "a: 1\nb: 2\n");
  assert (text "" = Some "");
  assert (text "foo" = None);
  assert (text "a: 1\n---\nb: 2\n" = None);
  assert (text "\n" = None)
;;

(* Changing the frontmatter leaves the blocks and their positions. *)
let () =
  let d = parse ~locs:true "---\na: 1\n---\np\n" in
  let d' = Doc.with_frontmatter (Frontmatter.of_string "b: 2") d in
  assert (Doc.to_string d' = "---\nb: 2\n---\n\np");
  assert (ranges d' = ranges d);
  let none = Doc.with_frontmatter None d in
  assert (Doc.frontmatter none = None && Doc.to_string none = "p")
;;
