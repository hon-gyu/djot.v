(* ai-disclosure: ai-generated *)

(* The statuses of the named profiles, and each [Broken] example checked:
   it parses under the profile to something other than what djot gives. *)

open Djot
module P = Kernel.Properties

let html profile src = Html.of_doc (Doc.of_string ~profile src)

let show name (profile : Profile.t) =
  Printf.printf "%s\n%s\n" name (String.make 20 '=');
  List.iter
    (fun (p : P.property) ->
      let s = p.P.p_status (profile :> Kernel.Profile.options) in
      Printf.printf "%s: %s\n" p.P.p_id (P.status_name s);
      match s with
      | Broken (_, example) -> assert (html profile example <> html Profile.djot example)
      | _ -> ())
    P.all;
  Printf.printf "\n"
;;

let () =
  let open Profile in
  show "djot" djot;
  show "markdown_like" markdown_like;
  show "djot, wikilinks and dollar math on" (djot |> with_ext_wikilinks true |> with_ext_dollar_math true);
  show "djot, keyed on" (with_ext_keyed true djot);
  show "djot, callouts on, divs off" (djot |> with_ext_callouts true |> with_divs false)
;;
