(* ai-disclosure: ai-generated *)

(* Ordered lists at the canonical rendering: one style, one delimiter,
   consecutive numbering from a start, so each item carries its own
   marker rather than the list carrying one.

   `list_kind` packages the flavours the renderer emits and
   `ck_uniformity` is `ListUniformity.list_uniformity` at them.  Roman
   and alpha reach this file through their codecs in `Marker.v`; what
   they still need is recorded in .project/260810.ordered-lists.md. *)

From Stdlib Require Import String Ascii List Bool PeanoNat Lia.
From DjotV Require Import Strings Line Ast Attributes Marker Step Uniformity ListUniformity.
Import ListNotations.

Local Open Scope string_scope.

(*
Ordered lists
=============
*)

(*
Decimal ordered lists
---------------------

The canonical rendering djot.js produces: one style, one delimiter, and
consecutive numbering from a start.  `canon.mjs` (see
.project/260810.ordered-lists.md) checked that decimal lists survive
their own rendering at every start and length it tried, so unlike the
alpha styles this needs no side condition beyond the ones every list has.
*)

Definition dec_marker (d : ordered_list_delim) (n : nat) : marker :=
  MOrd (dec_str n) d.

Lemma styles_of_core_dec :
  forall core d, nonempty_str core = true -> str_forallb is_digit core = true ->
    styles_of_core core d = [SOrd Decimal d].
Proof.
  intros [|c rest] d Hne Hd; [discriminate|].
  cbn [styles_of_core]. rewrite Hd. reflexivity.
Qed.

Lemma dec_marker_sty :
  forall d n, mk_sty (dec_marker d n) = [SOrd Decimal d].
Proof.
  intros d n. cbn [mk_sty dec_marker].
  apply styles_of_core_dec; [apply dec_str_nonempty | apply dec_str_digits].
Qed.

Lemma dec_marker_ok : forall d n, marker_ok (dec_marker d n) = true.
Proof.
  intros d n. cbn [marker_ok dec_marker].
  rewrite dec_str_nonempty, (str_digits_alnum _ (dec_str_digits n)).
  change (styles_of_core (dec_str n) d) with (mk_sty (dec_marker d n)).
  rewrite dec_marker_sty. reflexivity.
Qed.

(* A decimal marker opens with a digit or "(", so its line never reads as
   a thematic break -- which is the one part of `item_ok` that mentions
   the marker, and therefore the reason a decimal item's acceptability
   does not depend on its number. *)
Lemma is_thematic_dec_marker :
  forall d n l, is_thematic (mk_open (dec_marker d n) ++ l) = false.
Proof.
  intros d n l.
  assert (Hd : str_forallb is_digit (dec_str n) = true) by apply dec_str_digits.
  assert (Hne : nonempty_str (dec_str n) = true) by apply dec_str_nonempty.
  destruct d; cbn [mk_open dec_marker].
  - destruct (dec_str n) as [|c t] eqn:E; [discriminate Hne|].
    cbn [str_forallb] in Hd. apply andb_true_iff in Hd as [Hc _].
    change ((String c t ++ ". ") ++ l)%string with (String c ((t ++ ". ") ++ l))%string.
    apply thematic_first_char;
      [apply is_alnum_not_marker | apply is_alnum_not_special];
      apply is_digit_alnum, Hc.
  - destruct (dec_str n) as [|c t] eqn:E; [discriminate Hne|].
    cbn [str_forallb] in Hd. apply andb_true_iff in Hd as [Hc _].
    change ((String c t ++ ") ") ++ l)%string with (String c ((t ++ ") ") ++ l))%string.
    apply thematic_first_char;
      [apply is_alnum_not_marker | apply is_alnum_not_special];
      apply is_digit_alnum, Hc.
  - change (("(" ++ dec_str n ++ ") ") ++ l)%string
      with (String "(" ((dec_str n ++ ") ") ++ l))%string.
    apply thematic_first_char; reflexivity.
Qed.

Lemma item_ok_dec_marker :
  forall d k n L, item_ok (dec_marker d k) L = item_ok (dec_marker d n) L.
Proof.
  intros d k n [|l0 more]; [reflexivity|].
  cbn [item_ok]. rewrite !is_thematic_dec_marker. reflexivity.
Qed.

Lemma dec_marker_styles :
  forall d n, mk_styles (dec_marker d n) = [(SOrd Decimal d, n)].
Proof.
  intros d n. unfold mk_styles, with_starts. rewrite dec_marker_sty.
  cbn [map]. cbn [mk_core dec_marker style_start].
  rewrite dec_value_dec_str. reflexivity.
Qed.

(* So a decimal list closes to the `OrderedList` its start names. *)
Lemma marker_list_dec :
  forall d n sp items,
    marker_list (dec_marker d n) sp items
    = mk (OrderedList (OLAttrs Decimal d n) sp items).
Proof.
  intros d n sp items. unfold marker_list. rewrite dec_marker_styles. reflexivity.
Qed.

(* The markers of a decimal list: consecutive from its start. *)
Fixpoint dec_items (d : ordered_list_delim) (n : nat) (lss : list (list string))
  : list litem :=
  match lss with
  | [] => []
  | L :: rest => (dec_marker d n, L) :: dec_items d (S n) rest
  end.

Lemma map_snd_dec_items :
  forall d n lss, map snd (dec_items d n lss) = lss.
Proof.
  intros d n lss. revert n.
  induction lss as [|L rest IH]; intros n; [reflexivity|].
  cbn [dec_items map snd]. rewrite IH. reflexivity.
Qed.

Lemma items_ok_dec_items :
  forall d n0 n lss,
    forallb (item_ok (dec_marker d n0)) lss = true ->
    items_ok (dec_marker d n0) (dec_items d n lss) = true.
Proof.
  intros d n0 n lss. revert n.
  induction lss as [|L rest IH]; intros n Hok; [reflexivity|].
  cbn [forallb] in Hok. apply andb_prop in Hok as [HL Hrest].
  cbn [dec_items items_ok forallb fst snd].
  rewrite dec_marker_ok, (item_ok_dec_marker d n n0 L), HL.
  assert (Hs : admits (dec_marker d n0) (dec_marker d n) = true).
  { apply admits_agree. rewrite !dec_marker_sty. reflexivity. }
  rewrite Hs. cbn [andb].
  change (forallb _ (dec_items d (S n) rest))
    with (items_ok (dec_marker d n0) (dec_items d (S n) rest)).
  apply IH, Hrest.
Qed.

Lemma map_litem_lines_dec_items :
  forall d n lss,
    map litem_lines (dec_items d n lss)
    = map (fun p => indent_lines (mk_open (dec_marker d (fst p)))
                                 (mk_cont (dec_marker d (fst p))) (snd p))
          (combine (seq n (length lss)) lss).
Proof.
  intros d n lss. revert n.
  induction lss as [|L rest IH]; intros n; [reflexivity|].
  cbn [dec_items map length seq combine fst snd].
  unfold litem_lines at 1. cbn [fst snd]. rewrite IH. reflexivity.
Qed.

Lemma map_parse_dec_items :
  forall d n lss,
    map (fun it => parse_lines (snd it) (PPara [])) (dec_items d n lss)
    = map (fun L => parse_lines L (PPara [])) lss.
Proof.
  intros d n lss. revert n.
  induction lss as [|L rest IH]; intros n; [reflexivity|].
  cbn [dec_items map snd]. rewrite IH. reflexivity.
Qed.

(* Uniformity for a decimal ordered list: consecutive markers from
   `start`, each with its own width.  No side condition beyond the ones
   every list has -- `canon.mjs` checked that decimal lists survive their
   own canonical rendering at every start and length it tried, which is
   what distinguishes them from the alpha styles. *)
Theorem ordered_decimal_uniformity :
  forall d start sp lss,
    lss <> [] ->
    forallb (item_ok (dec_marker d start)) lss = true ->
    parse_lines (list_lines sp (map litem_lines (dec_items d start lss)))
                (PPara [])
    = [mk (OrderedList (OLAttrs Decimal d start) (list_spacing_of sp lss)
             (map (fun L => parse_lines L (PPara [])) lss))].
Proof.
  intros d start sp lss Hne Hok.
  destruct lss as [|L0 rest]; [congruence|].
  pose proof (items_ok_dec_items d start start (L0 :: rest) Hok) as Hio.
  cbn [dec_items] in Hio |- *.
  rewrite (list_uniformity (dec_marker d start) sp L0
             (dec_items d (S start) rest) (dec_marker_ok d start) Hio).
  rewrite marker_list_dec.
  cbn [map snd]. rewrite map_snd_dec_items, map_parse_dec_items. reflexivity.
Qed.

(* The same, with the list closed by a following line rather than by the
   end of the input.  The two endings are `list_uniformity`'s and
   `list_uniformity_tail`'s; everything between them is shared. *)
Theorem ordered_decimal_uniformity_tail :
  forall d start sp lss next tail,
    lss <> [] ->
    forallb (item_ok (dec_marker d start)) lss = true ->
    classify next <> KBlank ->
    (forall a b c, classify next <> KList a b c) ->
    indent_of next = 0 ->
    parse_lines (list_lines sp (map litem_lines (dec_items d start lss))
                 ++ EmptyString :: next :: tail)%list (PPara [])
    = mk (OrderedList (OLAttrs Decimal d start) (list_spacing_of sp lss)
            (map (fun L => parse_lines L (PPara [])) lss))
      :: parse_lines (next :: tail) (PPara []).
Proof.
  intros d start sp lss next tail Hne Hok Hnb Hnl Hindent.
  destruct lss as [|L0 rest]; [congruence|].
  pose proof (items_ok_dec_items d start start (L0 :: rest) Hok) as Hio.
  cbn [dec_items] in Hio |- *.
  rewrite (list_uniformity_tail (dec_marker d start) sp L0
             (dec_items d (S start) rest) next tail
             (dec_marker_ok d start) Hio Hnb Hnl Hindent).
  rewrite marker_list_dec.
  cbn [map snd]. rewrite map_snd_dec_items, map_parse_dec_items. reflexivity.
Qed.

(*
The list flavours the canonical rendering produces
--------------------------------------------------

A canonical list is a bullet list or a decimal ordered list, and the two
differ only in the markers their items carry: one repeated `-`, or
consecutive numerals from a start.  Naming that difference once is what
lets the roundtrip keep a single list case.  `ck_items` says which
markers the items get, `ck_first` names the marker `item_ok` is asked
for, `ck_block` the block the list closes to, and `ck_uniformity` is the
one theorem the block layer consumes.

Roman and alpha are absent on purpose.  `canon.mjs` (see
.project/260810.ordered-lists.md) found alpha lists that do not survive
their own canonical rendering (the letters that are also roman digits,
and the wrap past `z`), so they carry a side condition decimal does not,
and admitting them here would put that condition on every list.
*)
Inductive list_kind : Type :=
  | LKBullet
  | LKDecimal (d : ordered_list_delim) (start : nat).

Definition ck_first (k : list_kind) : marker :=
  match k with
  | LKBullet => bullet
  | LKDecimal d start => dec_marker d start
  end.

Definition ck_items (k : list_kind) (lss : list (list string)) : list litem :=
  match k with
  | LKBullet => same_marker bullet lss
  | LKDecimal d start => dec_items d start lss
  end.

Definition ck_block (k : list_kind) (sp : list_spacing) (items : list blocks)
  : block :=
  match k with
  | LKBullet => BulletList sp items
  | LKDecimal d start => OrderedList (OLAttrs Decimal d start) sp items
  end.

Lemma ck_items_lines :
  forall k lss, map snd (ck_items k lss) = lss.
Proof.
  intros [|d start] lss; [apply map_snd_same_marker | apply map_snd_dec_items].
Qed.

Lemma ck_items_markers_ok :
  forall k lss, forallb (fun it => marker_ok (fst it)) (ck_items k lss) = true.
Proof.
  intros [|d start] lss.
  - unfold ck_items, same_marker.
    induction lss as [|L rest IH]; [reflexivity|].
    cbn [map forallb fst]. rewrite bullet_ok. exact IH.
  - cbn [ck_items]. revert start.
    induction lss as [|L rest IH]; intros start; [reflexivity|].
    cbn [dec_items forallb fst]. rewrite dec_marker_ok. apply IH.
Qed.

Lemma ck_lines_nonempty :
  forall k lss, lss <> [] -> map litem_lines (ck_items k lss) <> [].
Proof.
  intros k lss H Hnil. apply H. rewrite <- (ck_items_lines k lss).
  destruct (ck_items k lss); [reflexivity | discriminate Hnil].
Qed.

(** Uniformity at either flavour: the rendering of a list whose items are
    `lss` parses back to the list its kind names, with the items' lines
    parsed at top level and the spacing read off those same lines. *)
Theorem ck_uniformity :
  forall k sp lss,
    lss <> [] ->
    forallb (item_ok (ck_first k)) lss = true ->
    parse_lines (list_lines sp (map litem_lines (ck_items k lss))) (PPara [])
    = [mk (ck_block k (list_spacing_of sp lss)
             (map (fun L => parse_lines L (PPara [])) lss))].
Proof.
  intros [|d start] sp lss Hne Hok.
  - cbn [ck_items ck_block ck_first] in Hok |- *.
    rewrite map_litem_lines_same_marker.
    exact (list_uniformity_same bullet sp lss bullet_ok Hne Hok).
  - exact (ordered_decimal_uniformity d start sp lss Hne Hok).
Qed.

(** The same with the list closed by a following line. *)
Theorem ck_uniformity_tail :
  forall k sp lss next tail,
    lss <> [] ->
    forallb (item_ok (ck_first k)) lss = true ->
    classify next <> KBlank ->
    (forall a b c, classify next <> KList a b c) ->
    indent_of next = 0 ->
    parse_lines (list_lines sp (map litem_lines (ck_items k lss))
                 ++ EmptyString :: next :: tail)%list (PPara [])
    = mk (ck_block k (list_spacing_of sp lss)
            (map (fun L => parse_lines L (PPara [])) lss))
      :: parse_lines (next :: tail) (PPara []).
Proof.
  intros [|d start] sp lss next tail Hne Hok Hnb Hnl Hindent.
  - cbn [ck_items ck_block ck_first] in Hok |- *.
    rewrite map_litem_lines_same_marker.
    exact (list_uniformity_tail_same bullet sp lss next tail bullet_ok Hne Hok
             Hnb Hnl Hindent).
  - exact (ordered_decimal_uniformity_tail d start sp lss next tail
             Hne Hok Hnb Hnl Hindent).
Qed.

(*
What the narrowing condition reaches, and what it does not
---------------------------------------------------------

`items_ok` asks that each sibling *admit* the styles the list opened
with, not that it offer exactly them.  The two are the same for bullets
and for decimal, where every marker names one style; they part company
at the ambiguous ordered markers, and the examples below are the
boundary.

A roman numeral that is a bare roman letter -- `i`, `v`, `x`, `l`, `c`,
`d`, `m` -- is also a single letter, so it offers roman *and* alpha; any
longer numeral offers only roman.  So a run is covered exactly when its
*first* numeral is unambiguous: later ones may be ambiguous, since a
superset narrows to the identity.  The same reading covers an alpha list
whose first letter is not a roman digit.

What is left out is the run whose first marker is ambiguous, `i.` / `ii.`
being the shortest.  The parser accepts it (it narrows to roman and says
so), but the list state's style set *moves*, and every statement in the
chain carries `ls_styles ls = mk_styles m0`.  Admitting it means making
that invariant the running narrowing rather than a constant, which is a
change to twelve statements rather than to one hypothesis.
*)

(* Covered: roman from 2, running through the ambiguous `v`. *)
Example roman_from_two_items_ok :
  items_ok (MOrd "ii" RightPeriod)
    [(MOrd "ii" RightPeriod, ["a"]); (MOrd "iii" RightPeriod, ["b"]);
     (MOrd "iv" RightPeriod, ["c"]); (MOrd "v" RightPeriod, ["d"])] = true.
Proof. reflexivity. Qed.

Example roman_from_two_parses :
  parse_lines ["ii. a"; "iii. b"; "iv. c"; "v. d"] (PPara [])
  = [mk (OrderedList (OLAttrs RomanLower RightPeriod 2) Tight
           [[mk (Para [mk (Str "a")])]; [mk (Para [mk (Str "b")])];
            [mk (Para [mk (Str "c")])]; [mk (Para [mk (Str "d")])]])].
Proof. reflexivity. Qed.

(* ...and so the uniformity theorem applies to it, with no proof of its
   own -- which is the point of weakening the condition. *)
Corollary roman_from_two_uniformity :
  forall sp,
    parse_lines (list_lines sp
                   (map litem_lines
                      [(MOrd "ii" RightPeriod, ["a"]); (MOrd "iii" RightPeriod, ["b"]);
                       (MOrd "iv" RightPeriod, ["c"]); (MOrd "v" RightPeriod, ["d"])]))
                (PPara [])
    = [mk (OrderedList (OLAttrs RomanLower RightPeriod 2)
             (list_spacing_of sp [["a"]; ["b"]; ["c"]; ["d"]])
             [parse_lines ["a"] (PPara []); parse_lines ["b"] (PPara []);
              parse_lines ["c"] (PPara []); parse_lines ["d"] (PPara [])])].
Proof.
  intros sp.
  exact (list_uniformity (MOrd "ii" RightPeriod) sp ["a"]
           [(MOrd "iii" RightPeriod, ["b"]); (MOrd "iv" RightPeriod, ["c"]);
            (MOrd "v" RightPeriod, ["d"])]
           eq_refl eq_refl).
Qed.

(* Covered: alpha whose first letter is not a roman digit, running
   through `l`, which is one. *)
Example alpha_from_e_items_ok :
  items_ok (MOrd "e" RightPeriod)
    [(MOrd "e" RightPeriod, ["a"]); (MOrd "l" RightPeriod, ["b"])] = true.
Proof. reflexivity. Qed.

(* Not covered, and this is the record of where the boundary sits: the
   parser reads these two lines as one roman list, and `items_ok` cannot
   say so. *)
Example roman_from_one_items_ok_fails :
  items_ok (MOrd "i" RightPeriod)
    [(MOrd "i" RightPeriod, ["a"]); (MOrd "ii" RightPeriod, ["b"])] = false.
Proof. reflexivity. Qed.

Example roman_from_one_parses_anyway :
  parse_lines ["i. a"; "ii. b"] (PPara [])
  = [mk (OrderedList (OLAttrs RomanLower RightPeriod 1) Tight
           [[mk (Para [mk (Str "a")])]; [mk (Para [mk (Str "b")])]])].
Proof. reflexivity. Qed.

(* The generalization, exercised.  `*` and `+` are separate list styles in
   djot, and each gets the uniformity theorem by instantiation — no new
   proof, which is the whole point of the section above.  If a future
   marker needs its own argument, that is the signal that `marker` is the
   wrong abstraction, not that these should be copied. *)
Corollary star_uniformity :
  forall sp lss,
    lss <> [] -> forallb (item_ok star) lss = true ->
    parse_lines (list_lines sp (map (indent_lines (mk_open star) (mk_cont star)) lss))
                (PPara [])
    = [marker_list star (list_spacing_of sp lss)
             (map (fun L => parse_lines L (PPara [])) lss)].
Proof. intros sp lss. exact (list_uniformity_same star sp lss star_ok). Qed.

Corollary plus_uniformity :
  forall sp lss,
    lss <> [] -> forallb (item_ok plus) lss = true ->
    parse_lines (list_lines sp (map (indent_lines (mk_open plus) (mk_cont plus)) lss))
                (PPara [])
    = [marker_list plus (list_spacing_of sp lss)
             (map (fun L => parse_lines L (PPara [])) lss)].
Proof. intros sp lss. exact (list_uniformity_same plus sp lss plus_ok). Qed.

(* The section reaches ordered markers too, and that is the point of
   generalizing `marker` past a style character: `1.` is an instance in
   exactly the way `*` is.

   What this does *not* yet cover is the canonical rendering, which
   renumbers its items — `9.`, `10.`, `11.` — and so needs a marker per
   item rather than one for the list.  That is the remaining step, and
   the hypothesis it will have to discharge is visible in
   `run_item_sibling`: every item's marker must leave the narrowing
   nonempty.  `list_uniformity` above is the version that lets the marker
   vary; this is it with one marker serving every item, which is what
   `list_uniformity_same` packages. *)
Corollary ordered_uniformity :
  forall m sp itemss,
    marker_ok m = true -> itemss <> [] ->
    forallb (item_ok m) itemss = true ->
    parse_lines (list_lines sp (map (indent_lines (mk_open m) (mk_cont m)) itemss))
                (PPara [])
    = [marker_list m (list_spacing_of sp itemss)
             (map (fun L => parse_lines L (PPara [])) itemss)].
Proof. intros m sp itemss Hm. exact (list_uniformity_same m sp itemss Hm). Qed.

(* The point of a marker per item, and the case a repeated marker cannot
   express: a renumbering list whose continuation indent changes in the
   middle.  djot.js renders exactly these lines and parses them back to
   `<ol start="9">` with two items. *)
Example renumbering_list_parses :
  parse_lines (list_lines Tight
                 (map litem_lines [(MOrd "9" RightPeriod, ["a"; "a2"]);
                                   (MOrd "10" RightPeriod, ["b"; "b2"])]))
              (PPara [])
  = [mk (OrderedList (OLAttrs Decimal RightPeriod 9) Tight
           [[mk (Para [mk (Str "a"); mk SoftBreak; mk (Str "a2")])];
            [mk (Para [mk (Str "b"); mk SoftBreak; mk (Str "b2")])]])].
Proof. reflexivity. Qed.

(* And the rendering really is the one whose pad moves. *)
Example renumbering_list_lines :
  map litem_lines [(MOrd "9" RightPeriod, ["a"; "a2"]);
                   (MOrd "10" RightPeriod, ["b"; "b2"])]
  = [["9. a"; "   a2"]; ["10. b"; "    b2"]].
Proof. reflexivity. Qed.

Example renumbering_items_ok :
  items_ok (MOrd "9" RightPeriod)
    [(MOrd "9" RightPeriod, ["a"; "a2"]);
     (MOrd "10" RightPeriod, ["b"; "b2"])] = true.
Proof. reflexivity. Qed.

(* Not vacuous: a decimal list with a repeated marker is what djot.js
   produces `<ol>` for, non-consecutive numbering included. *)
Example decimal_list_parses :
  parse_lines ["3. a"; "3. b"] (PPara [])
  = [mk (OrderedList (OLAttrs Decimal RightPeriod 3) Tight
           [[mk (Para [mk (Str "a")])]; [mk (Para [mk (Str "b")])]])].
Proof. reflexivity. Qed.

Example decimal_item_ok : item_ok (MOrd "3" RightPeriod) ["a"] = true.
Proof. reflexivity. Qed.

Example paren_list_parses :
  parse_lines ["(1) a"; "(1) b"] (PPara [])
  = [mk (OrderedList (OLAttrs Decimal LeftRightParen 1) Tight
           [[mk (Para [mk (Str "a")])]; [mk (Para [mk (Str "b")])]])].
Proof. reflexivity. Qed.

(* And it is not vacuous at the new markers. *)
Example star_list_parses :
  parse_lines ["* a"; "* b"] (PPara [])
  = [mk (BulletList Tight [[mk (Para [mk (Str "a")])];
                           [mk (Para [mk (Str "b")])]])].
Proof. reflexivity. Qed.

Example star_item_ok : item_ok star ["a"] = true.
Proof. reflexivity. Qed.

