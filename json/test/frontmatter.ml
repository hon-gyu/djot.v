(* ai-disclosure: ai-generated *)

(* The JSON form of a document with frontmatter. *)

open Djot

let () =
  let d =
    Doc.of_string ~frontmatter:true "---\ntitle: A note\ntags: [a, 1]\nx: .inf\n---\np\n"
  in
  let json = Djot_json.to_string d in
  assert (
    String.starts_with
      ~prefix:{|doc frontmatter={"title":"A note","tags":["a",1],"x":null}|}
      (Djot_json.to_ast_string d));
  let prefix =
    {|{"tag":"doc","frontmatter":{"title":"A note","tags":["a",1],"x":null},|}
  in
  assert (String.starts_with ~prefix json);
  (* Read back, the fields are the same but for the number JSON has no form for. *)
  let d' = Result.get_ok (Djot_json.of_string json) in
  assert (
    (Option.get (Doc.frontmatter d')).fields
    = [ "title", `String "A note"; "tags", `A [ `String "a"; `Float 1. ]; "x", `Null ]);
  assert (Html.of_doc d' = Html.of_doc d);
  (* No frontmatter, no member. *)
  let plain = Djot_json.to_string (Doc.of_string "p\n") in
  assert (String.starts_with ~prefix:{|{"tag":"doc","references"|} plain);
  assert (Doc.frontmatter (Result.get_ok (Djot_json.of_string plain)) = None);
  assert (
    Result.is_error (Djot_json.of_string {|{"tag":"doc","frontmatter":[],"children":[]}|}))
;;
