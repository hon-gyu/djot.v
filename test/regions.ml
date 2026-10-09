(* ai-disclosure: ai-generated *)

(* Throwaway: step 0 of `.project/261009.plan.eager-regions.md`, deleted
   with `dev/RegionProto.v`.  The prototype's tree of its reading against
   the scanner, on random paragraphs the prototype's alphabet admits.

   Usage:
     regions [N] [--seed S] *)

module R = Djot_fixtures.RegionProto

let table = Djot.Inline.djot_table

let pieces =
  [| "_"; "*"; "^"; "~"; "{_"; "_}"; "{*"; "*}"; "{="; "=}"; "{+"; "+}";
     "["; "]"; "]("; "]["; "("; ")"; "a"; "b"; " "; "\\"; "\\*"; "\\]";
     "\\("; "\\`"; "[a]("; "[a][";
     "`"; "``"; "$`"; "$$`"; "{=html}"; "{=h"; "<"; ">"; "<a:b>"; "<x@y>";
     "http:"; ":"; ":ab:"; "a_b"; "$"; "\""; "."; "-"; "!" |]

let gen_line () =
  let n = Random.int 10 in
  String.concat "" (List.init n (fun _ -> pieces.(Random.int (Array.length pieces))))

let gen_para () = List.init (1 + Random.int 3) (fun _ -> gen_line ())

let rec render ils = String.concat " " (List.map node ils)

and node (Djot.Ast.Node (_, a, x)) =
  let open Djot.Ast in
  let w name kids = Printf.sprintf "%s(%s)" name (render kids) in
  (if a <> [] then "@" else "")
  ^
  match x with
  | Str s -> Printf.sprintf "%S" s
  | Emph k -> w "Emph" k | Strong k -> w "Strong" k
  | Highlight k -> w "Mark" k | Insert k -> w "Ins" k | Delete k -> w "Del" k
  | Superscript k -> w "Sup" k | Subscript k -> w "Sub" k
  | Verbatim s -> Printf.sprintf "Verb%S" s
  | Symbol s -> Printf.sprintf "Sym%S" s
  | Math (_, s) -> Printf.sprintf "Math%S" s
  | Link (k, Direct d) -> Printf.sprintf "Link(%s|%S)" (render k) d
  | Link (k, Reference d) -> Printf.sprintf "Ref(%s|%S)" (render k) d
  | UrlLink s -> Printf.sprintf "Url%S" s
  | EmailLink s -> Printf.sprintf "Email%S" s
  | RawInline (f, s) -> Printf.sprintf "Raw%S%S" f s
  | NonBreakingSpace -> "Nbsp" | SoftBreak -> "Soft" | HardBreak -> "Hard"
  | _ -> "?"

let () =
  let n = ref 200000 and seed = ref 7 in
  let rec args = function
    | [] -> ()
    | "--seed" :: v :: rest -> seed := int_of_string v; args rest
    | v :: rest -> n := int_of_string v; args rest
  in
  args (List.tl (Array.to_list Sys.argv));
  Random.init !seed;
  let checked = ref 0 and bad = ref 0 in
  let seen = Hashtbl.create 16 in
  let rec count ils =
    List.iter
      (fun (Djot.Ast.Node (_, _, x)) ->
        let open Djot.Ast in
        let tag k = Hashtbl.replace seen k (1 + try Hashtbl.find seen k with Not_found -> 0) in
        match x with
        | Verbatim _ -> tag "verbatim" | Math _ -> tag "math" | Symbol _ -> tag "symbol"
        | UrlLink _ | EmailLink _ -> tag "autolink" | RawInline _ -> tag "raw"
        | Link (k, Direct d) ->
            tag "link"; if String.contains d '`' || String.contains d '<' then tag "dest-claims";
            count k
        | Link (k, Reference d) ->
            tag "ref"; if String.contains d '`' then tag "label-claims"; count k
        | Emph k | Strong k | Highlight k | Insert k | Delete k | Superscript k | Subscript k ->
            count k
        | _ -> ())
      ils
  in
  let fixed =
    [ [ "*a `b* c`" ]; [ "[a `b](x)` c" ]; [ "[a](b`c)d` e" ]; [ "a](b `c) d`" ];
      [ "`a\\`b` c" ]; [ "<http://a\\>b> c" ]; [ "*<ab*c" ]; [ "*<http://a*b c*" ];
      [ "_x :a_b c_" ]; [ "`x`{=html} *a*" ]; [ "`x`{=htm *a*" ]; [ "`a"; "b` c" ];
      [ "[a][b `c] d`" ]; [ "*[a](b `c*)` d" ] ]
  in
  let gens = ref (List.map (fun l -> l) fixed) in
  for _ = 1 to !n do
    let l = match !gens with x :: r -> gens := r; x | [] -> gen_para () in
    if R.proto_adm table l then begin
      incr checked;
      let a = Djot.InlineScan.para_inlines table l and b = R.proto_tree table l in
      count a;
      if a <> b then begin
        incr bad;
        if !bad <= 8 then
          Printf.printf "--- %s\n  scanner: %s\n  proto:   %s\n"
            (String.concat " / " (List.map (Printf.sprintf "%S") l))
            (render a) (render b)
      end
    end
  done;
  Hashtbl.iter (fun k v -> Printf.printf "  %s: %d\n" k v) seen;
  Printf.printf "regions: %d paragraphs admitted, %d differ\n" !checked !bad;
  exit (if !bad = 0 then 0 else 1)
