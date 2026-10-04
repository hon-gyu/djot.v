(* ai-disclosure: ai-generated *)

(* The playground's parser, run as a web worker so that typing is not held
   up by a long document.  A request is the text, the profile as
   [Spec.to_string] writes it, and whether to record positions; the answer
   is every output, or an error. *)

open Brr
open Site_common

let get_string o k = Jv.to_string (Jv.get o k)

let outputs text profile locs =
  let d = Djot.Doc.of_string ~profile ~locs text in
  [| "html", Jv.of_string (Djot.Html.of_doc d)
   ; "json", Jv.of_string (Djot_json.to_string ~format:Jsont.Indent d)
   ; "ast", Jv.of_string (Djot_json.to_ast_string d)
  |]
;;

let () =
  let answer e =
    let msg : Jv.t = Brr_io.Message.Ev.data (Ev.as_type e) in
    let t0 = Performance.now_ms G.performance in
    let fields =
      match Spec.of_string (get_string msg "profile") with
      | Error e -> [| "error", Jv.of_string e |]
      | Ok profile ->
        (try outputs (get_string msg "text") profile (Jv.to_bool (Jv.get msg "locs")) with
         | exn -> [| "error", Jv.of_string (Printexc.to_string exn) |])
    in
    let ms = Performance.now_ms G.performance -. t0 in
    Brr_webworkers.Worker.G.post
      (Jv.obj (Array.append [| "id", Jv.get msg "id"; "ms", Jv.of_float ms |] fields))
  in
  ignore (Ev.listen Brr_io.Message.Ev.message answer G.target)
;;
