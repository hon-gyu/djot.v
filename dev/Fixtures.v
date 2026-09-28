(* ai-disclosure: ai-generated *)

(* Test fixtures for the test/ executables: the generated corpus as
   data.  Extracted alongside the parser but kept out of the parser's
   library, so nothing a consumer links against carries a test corpus. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Strings Line Ast Inline Step Render.
From DjotVDev Require Import Generate.
Import ListNotations.
Local Open Scope string_scope.

Definition render_cb (c : cblock) : string :=
  @render_djot _ DjotV.Step.djot_bconfig (blocks_of_cblocks [c]).

Definition generated_docs (d : nat) : list string := map render_cb (accepted d).

(* Every `cb_ok` block the enumerator produces, rendered to djot source,
   so that the shapes the roundtrip admits are checked against djot
   itself and not only against our own renderer.

   `Eval vm_compute in` forces the list to string literals here, so what
   crosses into OCaml is data rather than the enumerator.

   Depth 2 rather than 3 : this file rebuilds on
   every proof edit (about 2s at depth 2, 23s at depth 3), and depth 2
   already contains a list inside a list item.

   Ordered lists ride along rather than joining `enum_cblock`, for the
   reason `Generate.ordered_pool` gives.  Against djot.js they matter
   most, since the marker text is what our renderer invents. *)
Definition generated : list string :=
  Eval vm_compute in (generated_docs 2 ++ map render_cb ordered_accepted
                      ++ map render_cb def_accepted)%list.

(*
Lazy variants
=============

The generated documents, and the same documents as a footnote's body,
with the container prefixes dropped from every line that continues an
open paragraph inside a container.  `step_lazy_restore` says our parser
reads each variant as it reads the original; djot.js reading it the same
way is what this checks.  A document with no such line gives no
variant.
*)

(* The line with the prefixes of the containers open in `st` removed.
   `None` when a quote's `>` is missing, which a renderer line never
   is. *)
Fixpoint strip_spine (st : pstate) (l : string) : option string :=
  match st with
  | PQuote _ _ _ inner =>
      match quote_prefix l with
      | Some rest => strip_spine inner rest
      | None => None
      end
  | PList _ _ inner | PFoot _ _ _ _ inner => strip_spine inner (drop_leading_ws l)
  | PDiv _ _ _ _ _ inner | PPend _ _ inner | PKey _ _ _ inner => strip_spine inner l
  | _ => Some (drop_leading_ws l)
  end.

(* The residue, when the line may be written lazily and dropping the
   prefixes changes it. *)
Definition lazy_residue (st : pstate) (l : string) : option string :=
  match strip_spine st l with
  | Some r =>
      if (lazy_ok st && negb (String.eqb r l)
          && match classify r with KText => true | _ => false end
          && match bunderline_of r with None => true | _ => false end)%bool
      then Some r else None
  | None => None
  end.

(* Each line is fed to the parser as it will appear in the variant, so a
   later line is judged against the state the variant reaches. *)
Fixpoint lazy_lines (st : pstate) (ls : list string) : bool * list string :=
  match ls with
  | [] => (false, [])
  | l :: rest =>
      let l' := match lazy_residue st l with Some r => r | None => l end in
      let '(changed, rest') := lazy_lines (snd (step l' st)) rest in
      ((changed || negb (String.eqb l' l))%bool, l' :: rest')
  end.

Definition newline : string := String (Ascii.ascii_of_nat 10) EmptyString.

Definition lazy_variant (doc : string) : option string :=
  let '(changed, ls) := lazy_lines (PPara []) (split_lines doc) in
  if changed then Some (String.concat newline ls) else None.

(* A document as a footnote's body: the canonical fragment has no
   footnote block, so without this no variant would drop a footnote's
   indentation.  The body starts on the line after `[^n]:`, which keeps
   clear of `footnote_list_shift_counterexample`. *)
Definition footnoted (doc : string) : string :=
  String.concat newline
    ("[^n]:" :: map (fun l => ("  " ++ l)%string) (split_lines doc) ++ [""; "[^n]"])%list.

Definition lazy_generated : list string :=
  Eval vm_compute in
    flat_map (fun d => match lazy_variant d with Some v => [v] | None => [] end)
      (generated ++ map footnoted generated)%list.
