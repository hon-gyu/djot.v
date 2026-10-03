(* ai-disclosure: ai-generated *)

(* Profiles: what a source parses to under a named profile and with a
   switch flipped, and a profile printed. Compared against
   profiles.expected. *)

open Djot

(* [src]'s parse under each named profile. *)
let parses src profiles =
  Printf.printf "\n%s\n" (Outline.quote src);
  List.iter
    (fun (name, profile) ->
      Printf.printf "-- %s\n" name;
      Outline.print (Doc.of_string ~profile src))
    profiles
;;

let () =
  let open Profile in
  parses "| a |\n|---|\n" [ "djot", djot; "tables off", with_tables false djot ];
  parses "**a**\n" [ "djot", djot; "markdown_like", markdown_like ];
  parses "[[a|b]]\n" [ "djot", djot; "wikilinks on", with_ext_wikilinks true djot ];
  parses
    "> [!warning]- Do not rename\n> body\n"
    [ "djot", djot
    ; "markdown_like", markdown_like
    ; "callouts on", with_ext_callouts true djot
    ];
  parses
    "a\n===\n"
    [ "djot", djot
    ; "markdown_like", markdown_like
    ; "markdown_like, setext off", with_ext_setext_headings false markdown_like
    ; "setext on", with_ext_setext_headings true djot
    ];
  parses
    "a\n- b\n"
    [ "djot", djot; "list interrupts on", with_ext_list_interrupts true djot ]
;;

let () =
  Format.printf "@.== pp djot@.%a@." Profile.pp Profile.djot;
  Format.printf "@.== pp markdown_like@.%a@." Profile.pp Profile.markdown_like;
  Format.printf
    "@.== pp_delimiters markdown_like@.%a@."
    Profile.pp_delimiters
    Profile.markdown_like
;;

(* The two block rules print as switches, recognized after being set. *)
let () =
  let lines p = String.split_on_char '\n' (Format.asprintf "%a" Profile.pp p) in
  let p =
    Profile.(djot |> with_ext_setext_headings true |> with_ext_list_interrupts true)
  in
  assert (List.mem "ext_setext_headings: on" (lines p));
  assert (List.mem "ext_list_interrupts: on" (lines p))
;;
