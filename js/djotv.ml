(* ai-disclosure: ai-generated *)

(* The exports of the module: parse, toHtml and toDjot.  A tree crosses as
   the object of Djot_json's JSON.  A failure throws a JavaScript Error.
   index.d.ts states the types. *)

exception Failed of string

let fail fmt = Printf.ksprintf (fun s -> raise (Failed s)) fmt

(* The exports object of a CommonJS module, the global object elsewhere. *)
external exports : unit -> Jv.t = "djotv_exports"

let field (o : Jv.t) (k : string) : Jv.t option =
  if Jv.is_none o then None else Jv.find o k
;;

let string_field o k : string option =
  match field o k with
  | None -> None
  | Some v when Jstr.to_string (Jv.typeof v) = "string" -> Some (Jv.to_string v)
  | Some _ -> fail "%s must be a string" k
;;

let switch name =
  match
    List.find_opt (fun s -> Djot.Profile.Switch.name s = name) Djot.Profile.switches
  with
  | Some s -> s
  | None -> fail "unknown switch %S" name
;;

let base = function
  | "djot" -> Djot.Profile.djot
  | "markdown_like" -> Djot.Profile.markdown_like
  | name -> fail "unknown profile %S" name
;;

(* [options.profile]: the profile [base] names, with each of [switches] set. *)
let profile (options : Jv.t) : Djot.Profile.t =
  match field options "profile" with
  | None -> Djot.Profile.djot
  | Some p ->
    let start = Option.fold ~none:Djot.Profile.djot ~some:base (string_field p "base") in
    (match field p "switches" with
     | None -> start
     | Some s ->
       let names =
         Jv.to_list Jv.to_string (Jv.call (Jv.get Jv.global "Object") "keys" [| s |])
       in
       List.fold_left
         (fun acc name ->
            Djot.Profile.Switch.set (switch name) (Jv.to_bool (Jv.get s name)) acc)
         start
         names)
;;

let style (options : Jv.t) : Djot.style =
  match string_field options "style" with
  | None | Some "irredundant" -> `Irredundant
  | Some "checked" -> `Checked
  | Some "safe" -> `Safe
  | Some "naive" -> `Naive
  | Some s -> fail "unknown style %S" s
;;

(* [j] with no text location, which would name the JSON text in errors. *)
let rec unlocated (j : Jsont.json) : Jsont.json =
  let none x = x, Jsont.Meta.none in
  match j with
  | Null (x, _) -> Null (none x)
  | Bool (x, _) -> Bool (none x)
  | Number (x, _) -> Number (none x)
  | String (x, _) -> String (none x)
  | Array (js, _) -> Array (none (List.map unlocated js))
  | Object (mems, _) ->
    Object (none (List.map (fun ((n, _), j) -> none n, unlocated j) mems))
;;

(* Through JSON text: [Jsont_brr.decode_jv] reads an object's members sorted by
   name, which would reorder attributes. *)
let of_tree profile (tree : Jv.t) : Djot.Doc.t =
  let text = Jstr.to_string (Brr.Json.encode tree) in
  let doc =
    Result.bind (Jsont_bytesrw.decode_string Jsont.json text) (fun j ->
      Djot_json.to_doc ~profile (unlocated j))
  in
  match doc with
  | Ok doc -> doc
  | Error e -> fail "%s" e
;;

let to_tree (doc : Djot.Doc.t) : Jv.t =
  match Jsont_brr.encode_jv' Jsont.json (Djot_json.of_doc doc) with
  | Ok tree -> tree
  | Error e -> fail "%s" (Jsont.Error.to_string e)
;;

let parse text options =
  let locs = Option.fold ~none:false ~some:Jv.to_bool (field options "locs") in
  to_tree (Djot.Doc.of_string ~profile:(profile options) ~locs (Jv.to_string text))
;;

let to_html source options =
  let profile = profile options in
  let doc =
    if Jstr.to_string (Jv.typeof source) = "string"
    then Djot.Doc.of_string ~profile (Jv.to_string source)
    else of_tree profile source
  in
  Jv.of_string (Djot.Html.of_doc doc)
;;

let to_djot tree options =
  Jv.of_string
    (Djot.Doc.to_string ~style:(style options) (of_tree (profile options) tree))
;;

(* [f] with its OCaml exceptions thrown as JavaScript errors. *)
let export name (f : Jv.t -> Jv.t -> Jv.t) =
  let call a b =
    try f a b with
    | Failed message -> Jv.throw (Jstr.v message)
    | Stack_overflow -> Jv.throw (Jstr.v "the document is nested too deeply")
  in
  Jv.set (exports ()) name (Jv.callback ~arity:2 call)
;;

let () =
  Jsont.Error.disable_ansi_styler ();
  export "parse" parse;
  export "toHtml" to_html;
  export "toDjot" to_djot
;;
