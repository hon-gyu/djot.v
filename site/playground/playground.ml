(* ai-disclosure: ai-generated *)

(* The playground's interface.  It never parses: the text and the profile
   go to the worker ([worker.ml]) and the outputs come back. *)

open Brr
open Site_common
module Profile = Djot.Profile
module Switch = Profile.Switch
module Delimiter = Profile.Delimiter
module P = Djot_properties

let str = Jstr.v
let default_text =
  {|# A heading that is long enough
to be wrapped

A paragraph with _emphasis_, *strong* text and a [link](https://djot.net).
Wrap it anywhere: a line that starts with
- a hyphen stays in the paragraph.

> A quote
> with a list:
>
> 1. one
> 2. two
|}
;;

let profile = ref Profile.djot
let tab = ref "preview"
let locs = ref false
let result : Jv.t option ref = ref None
let delimiter_error : (string * string) option ref = ref None

(* The statuses shown before the last change of profile, by property id. *)
let before : (string * string) list ref = ref []

let el ?(cls = "") ?(at = []) tag children =
  let at = if cls = "" then at else At.class' (str cls) :: at in
  El.v ~at (str tag) children
;;

let txt s = El.txt' s
let on ev f e = ignore (Ev.listen ev f (El.as_target e))
let value e = Jstr.to_string (El.prop El.Prop.value e)

let editor =
  el "textarea" ~at:[ At.spellcheck (str "false"); At.v (str "aria-label") (str "djot source") ] []
;;

let output = el "div" ~cls:"output" []
let profile_panel = el "div" ~cls:"panel" []
let property_panel = el "div" ~cls:"panel" []
let tabs = el "div" ~cls:"tabs" []
let timing = el "span" ~cls:"timing" []

(*
The worker
----------

One request at a time.  A change made while one is out is sent when the
answer comes back, so only the latest text is parsed.
*)

let parser = lazy (Brr_webworkers.Worker.create (str "worker.js"))
let sent = ref 0
let busy = ref false
let stale = ref false

(* The page's theme, which the preview follows. *)
let theme () =
  match El.at (str "data-theme") (Document.root G.document) with
  | Some t -> Jstr.to_string t
  | None -> "light"
;;

let show_output () =
  match !result with
  | None -> ()
  | Some r ->
    let field k = Jv.find r k |> Option.map Jv.to_string in
    (match field "error", !tab with
     | Some e, _ -> El.set_children output [ el "pre" ~cls:"error" [ txt e ] ]
     | None, "preview" ->
       let frame =
         el
           "iframe"
           ~at:
             [ At.v (str "sandbox") (str "")
             ; At.v (str "title") (str "preview")
             ; At.v
                 (str "srcdoc")
                 (str
                    (Printf.sprintf
                       "<!doctype html><html data-theme=\"%s\"><meta charset=utf-8><link \
                        rel=stylesheet href=\"../theme.css\"><link rel=stylesheet \
                        href=\"../preview.css\">%s"
                       (theme ())
                       (Option.value (field "html") ~default:"")))
             ]
           []
       in
       El.set_children output [ frame ]
     | None, t ->
       El.set_children output [ el "pre" [ txt (Option.value (field t) ~default:"") ] ]);
    El.set_children
      timing
      [ txt (Printf.sprintf "%.0f ms" (Jv.to_float (Jv.get r "ms"))) ]
;;

let rec parse () =
  if !busy
  then stale := true
  else (
    busy := true;
    incr sent;
    Brr_webworkers.Worker.post
      (Lazy.force parser)
      (Jv.obj
         [| "id", Jv.of_int !sent
          ; "text", Jv.of_string (value editor)
          ; "profile", Jv.of_string (Spec.to_string !profile)
          ; "locs", Jv.of_bool !locs
         |]))

and answered e =
  result := Some (Brr_io.Message.Ev.data (Ev.as_type e));
  busy := false;
  show_output ();
  if !stale
  then (
    stale := false;
    parse ())
;;

(*
The address
-----------

The text and the profile are in the fragment, so a state can be linked.
*)

let encode s =
  Jstr.to_string (Result.value (Uri.encode_component (str s)) ~default:Jstr.empty)
;;

let decode s =
  Jstr.to_string (Result.value (Uri.decode_component (str s)) ~default:Jstr.empty)
;;

let write_address () =
  let fragment =
    Printf.sprintf
      "#profile=%s&text=%s"
      (encode (Spec.to_string !profile))
      (encode (value editor))
  in
  let uri = Uri.of_jstr (str fragment) ~base:(Uri.to_jstr (Window.location G.window)) in
  match uri with
  | Ok uri -> Window.History.replace_state ~uri (Window.history G.window)
  | Error _ -> ()
;;

let read_address () =
  let fragment = Jstr.to_string (Uri.fragment (Window.location G.window)) in
  let field name =
    List.find_map
      (fun kv ->
        match String.index_opt kv '=' with
        | Some i when String.sub kv 0 i = name ->
          Some (decode (String.sub kv (i + 1) (String.length kv - i - 1)))
        | _ -> None)
      (String.split_on_char '&' fragment)
  in
  (match Option.map Spec.of_string (field "profile") with
   | Some (Ok p) -> profile := p
   | _ -> ());
  El.set_prop El.Prop.value (str (Option.value (field "text") ~default:default_text)) editor
;;

let timer = ref None

let changed () =
  Option.iter G.stop_timer !timer;
  timer
  := Some
       (G.set_timeout ~ms:120 (fun () ->
          write_address ();
          parse ()))
;;

(*
Properties
----------
*)

let glyph : P.status -> string = function
  | Proved -> "\xE2\x9C\x93"
  | Conditional _ -> "\xE2\x9C\x93*"
  | Broken _ -> "\xE2\x9C\x97"
  | Conjectured -> "?"
  | Unknown -> "\xE2\x80\x93"
  | Inapplicable _ -> "n/a"
;;

let source_link name =
  match Links.theorem name with
  | Some href -> el "a" ~at:[ At.href (str href) ] [ el "code" [ txt name ] ]
  | None -> el "code" [ txt name ]
;;

let rec render_properties () =
  let row p =
    let status = P.status p !profile in
    let cls = P.status_name status in
    let moved =
      match List.assoc_opt (P.id p) !before with
      | Some c when c <> cls -> " moved"
      | _ -> ""
    in
    let note =
      match status with
      | Conditional s | Inapplicable s -> [ el "p" ~cls:"note" [ txt s ] ]
      | Broken { reason; example } ->
        let load = el "button" [ txt "Load an example" ] in
        on Ev.click
          (fun _ ->
            El.set_prop El.Prop.value (str example) editor;
            changed ())
          load;
        [ el "p" ~cls:"note" [ txt reason ]; load ]
      | Conjectured -> [ el "p" ~cls:"note" [ txt "Not proved for this profile." ] ]
      | Proved | Unknown -> []
    in
    let theorems =
      match P.theorems p with
      | [] -> []
      | ts ->
        [ el
            "p"
            ~cls:"theorems"
            (List.concat_map (fun t -> [ source_link t; txt " " ]) ts)
        ]
    in
    el
      "details"
      ~cls:("property " ^ cls ^ moved)
      (el
         "summary"
         [ el "span" ~cls:"status" ~at:[ At.title (str cls) ] [ txt (glyph status) ]
         ; txt (P.statement p)
         ]
       :: el "p" [ txt (P.implication p) ]
       :: (note @ theorems))
  in
  let groups =
    List.fold_left
      (fun gs p -> if List.mem (P.group p) gs then gs else gs @ [ P.group p ])
      []
      P.all
  in
  let group g =
    el "h3" [ txt g ] :: List.map row (List.filter (fun p -> P.group p = g) P.all)
  in
  let count c =
    List.length
      (List.filter (fun p -> P.status_name (P.status p !profile) = c) P.all)
  in
  let summary =
    Printf.sprintf
      "%d proved, %d conditional, %d broken, %d conjectured"
      (count "proved")
      (count "conditional")
      (count "broken")
      (count "conjectured")
  in
  El.set_children
    property_panel
    (el "h2" [ txt "Properties" ]
     :: el "p" ~cls:"summary" [ txt summary ]
     :: List.concat_map group groups)

(*
Profile
-------

The switches and the delimiters are the state.  The preset shown is worked
out from them.
*)

and set_profile p =
  before
  := List.map
       (fun q -> P.id q, P.status_name (P.status q !profile))
       P.all;
  profile := p;
  render_profile ();
  render_properties ();
  changed ()

and distance p q =
  List.length (List.filter (fun s -> Switch.get s p <> Switch.get s q) Profile.switches)
  + List.length
      (List.filter (fun d -> Spec.spelling d p <> Spec.spelling d q) Profile.delimiters)

and render_profile () =
  let nearest, n =
    List.fold_left
      (fun (best, n) (name, q) ->
        let m = distance !profile q in
        if m < n then name, m else best, n)
      ("", max_int)
      Spec.presets
  in
  let select =
    el
      "select"
      (List.map
         (fun (name, _) ->
           el
             "option"
             ~at:(At.value (str name) :: (if name = nearest then [ At.selected ] else []))
             [ txt name ])
         Spec.presets)
  in
  on Ev.change (fun _ -> set_profile (List.assoc (value select) Spec.presets)) select;
  let changes =
    if n = 0
    then []
    else [ el "span" ~cls:"changes" [ txt (Printf.sprintf " + %d change%s" n (if n = 1 then "" else "s")) ] ]
  in
  let switch s =
    let box =
      el
        "input"
        ~at:
          (At.type' (str "checkbox")
           :: (if Switch.get s !profile then [ At.checked ] else []))
        []
    in
    on Ev.change
      (fun _ -> set_profile (Switch.set s (El.prop El.Prop.checked box) !profile))
      box;
    let differs =
      if Switch.get s !profile <> Switch.get s (List.assoc nearest Spec.presets)
      then "switch differs"
      else "switch"
    in
    el
      "label"
      ~cls:differs
      [ box
      ; el "span" ~cls:"name" [ txt (Switch.name s) ]
      ; el "span" ~cls:"doc" [ txt (Switch.doc s) ]
      ]
  in
  let delimiter d =
    let run, syntax = Spec.spelling d !profile in
    let input = el "input" ~at:[ At.value (str run); At.v (str "size") (str "3") ] [] in
    let choice =
      el
        "select"
        (List.map
           (fun (s, shown) ->
             el
               "option"
               ~at:(At.value (str s) :: (if s = syntax then [ At.selected ] else []))
               [ txt shown ])
           [ "bare", run ^ "x" ^ run
           ; "braced", Printf.sprintf "{%sx%s} only" run run
           ; "off", "off"
           ])
    in
    let apply _ =
      match Spec.respell d (value input) (value choice) !profile with
      | Ok p ->
        delimiter_error := None;
        set_profile p
      | Error e ->
        delimiter_error := Some (Delimiter.name d, e);
        render_profile ()
    in
    on Ev.change apply input;
    on Ev.change apply choice;
    let error =
      match !delimiter_error with
      | Some (name, e) when name = Delimiter.name d -> [ el "span" ~cls:"error" [ txt e ] ]
      | _ -> []
    in
    el
      "div"
      ~cls:"delimiter"
      ([ el "span" ~cls:"name" [ txt (Delimiter.name d) ]; input; choice ] @ error)
  in
  let extensions, constructs = List.partition Switch.is_extension Profile.switches in
  El.set_children
    profile_panel
    ([ el "h2" [ txt "Profile" ]; el "div" ~cls:"preset" (select :: changes) ]
     @ [ el "h3" [ txt "djot constructs" ] ]
     @ List.map switch constructs
     @ [ el "h3" [ txt "Extensions" ] ]
     @ List.map switch extensions
     @ [ el "h3" [ txt "Delimiters" ] ]
     @ List.map delimiter Profile.delimiters)
;;

let render_tabs () =
  let button (name, text) =
    let b = el "button" ~cls:(if name = !tab then "tab on" else "tab") [ txt text ] in
    on Ev.click
      (fun _ ->
        tab := name;
        show_output ())
      b;
    b
  in
  let positions =
    let box = el "input" ~at:[ At.type' (str "checkbox") ] [] in
    on Ev.change
      (fun _ ->
        locs := El.prop El.Prop.checked box;
        parse ())
      box;
    el "label" ~cls:"positions" [ box; txt "positions" ]
  in
  let buttons =
    List.map
      button
      [ "preview", "Preview"; "html", "HTML"; "json", "JSON"; "ast", "AST" ]
  in
  List.iter
    (fun b ->
      on Ev.click
        (fun _ ->
          List.iter (El.set_class (str "on") false) buttons;
          El.set_class (str "on") true b)
        b)
    buttons;
  El.set_children tabs (buttons @ [ positions; timing ])
;;

let page () =
  match Document.find_el_by_id G.document (str "playground") with
  | None -> ()
  | Some root ->
    read_address ();
    ignore
      (Ev.listen
         Brr_io.Message.Ev.message
         answered
         (Brr_webworkers.Worker.as_target (Lazy.force parser)));
    on Ev.input (fun _ -> changed ()) editor;
    ignore (Ev.listen (Ev.Type.void (str "themechange")) (fun _ -> show_output ()) (Window.as_target G.window));
    render_tabs ();
    render_profile ();
    render_properties ();
    El.set_children
      root
      [ el "aside" [ profile_panel ]
      ; el "aside" [ property_panel ]
      ; el "div" ~cls:"editor" [ editor ]
      ; el "div" ~cls:"result" [ tabs; output ]
      ];
    parse ()
;;

let () = page ()
