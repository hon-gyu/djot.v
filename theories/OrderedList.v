(* ai-disclosure: autonomous *)

(* Ordered lists at the canonical rendering: one style, one delimiter,
   consecutive numbering from a start, so each item carries its own
   marker rather than the list carrying one.

   Parse-side, despite the name: it proves that the markers the canonical
   renderer emits parse back to the list they came from.  It sits above
   `Marker.v`, which holds the numeral codecs, and above the uniformity
   chain it instantiates; `Parser.v` re-exports it.

   `nsc_uniformity` states the list-level argument once for any numbering
   scheme; decimal, roman and alpha are three instantiations.
   `list_kind` packages the flavours the renderer emits, `ck_ok` the side
   condition roman, alpha and decimal carry, and `ck_uniformity` is the one
   theorem the block layer consumes. *)

From Stdlib Require Import String Ascii List Bool PeanoNat Lia.
From DjotV Require Import Strings Line Ast Attributes Inline Marker Step Uniformity ListUniformity.
Import ListNotations.

Local Open Scope string_scope.

(* The delimiter table this file is read at.  Implicit, so nothing below
   mentions it: what it buys is that the statements quantify over the
   family rather than over djot's spelling. *)
Section WithTable.
Context {T : dtable}.
Context {K : bconfig}.

(*
Ordered lists
=============
*)

(*
Numbering schemes
-----------------

A canonical ordered list is a numbering scheme -- a numeral per position
-- plus a delimiter.  Decimal, roman and alpha differ only in the scheme,
so the list-level argument is stated once here and instantiated three
times.  `nsc_uniformity` is the whole of it, and it is short because
`ListUniformity.list_uniformity` already lets the marker vary per item:
all that is left is to say which markers, and that the first one names
the style and start the `OrderedList` node carries.

Its three hypotheses are decidable, so an instantiation at a concrete
start discharges them by computation; what a *general* instantiation
needs is a proof that its numerals name one style, which is where the
schemes genuinely differ.  Roman and alpha carry a range condition;
decimal carries only a length limit on its numerals.
*)

Definition nsc_marker (core : nat -> string) (d : ordered_list_delim) (n : nat)
  : marker := MOrd (core n) d.

(* The markers a scheme gives a run of items: consecutive from `n`. *)
Fixpoint nsc_items (core : nat -> string) (d : ordered_list_delim) (n : nat)
                   (lss : list (list string)) : list litem :=
  match lss with
  | [] => []
  | L :: rest => (nsc_marker core d n, L) :: nsc_items core d (S n) rest
  end.

Local Lemma map_snd_nsc_items :
  forall core d n lss, map snd (nsc_items core d n lss) = lss.
Proof.
  intros core d n lss. revert n.
  induction lss as [|L rest IH]; intros n; [reflexivity|].
  cbn [nsc_items map snd]. rewrite IH. reflexivity.
Qed.

Local Lemma map_parse_nsc_items :
  forall core d n lss,
    map (fun it => parse_lines (snd it) (PPara [])) (nsc_items core d n lss)
    = map (fun L => parse_lines L (PPara [])) lss.
Proof.
  intros core d n lss. revert n.
  induction lss as [|L rest IH]; intros n; [reflexivity|].
  cbn [nsc_items map snd]. rewrite IH. reflexivity.
Qed.

Local Lemma map_litem_lines_nsc_items :
  forall core d n lss,
    map litem_lines (nsc_items core d n lss)
    = map (fun p => indent_lines (mk_open (nsc_marker core d (fst p)))
                                 (mk_cont (nsc_marker core d (fst p))) (snd p))
          (combine (seq n (length lss)) lss).
Proof.
  intros core d n lss. revert n.
  induction lss as [|L rest IH]; intros n; [reflexivity|].
  cbn [nsc_items map length seq combine fst snd].
  unfold litem_lines at 1. cbn [fst snd]. rewrite IH. reflexivity.
Qed.

(* Uniformity for any scheme.  `mk_styles` carrying `(SOrd sty d, start)`
   at its head is what makes the list close to the node named in the
   conclusion; `items_ok` is `list_uniformity`'s hypothesis unchanged. *)
Theorem nsc_uniformity :
  forall sty core d start sp lss,
    lss <> [] ->
    marker_ok (nsc_marker core d start) = true ->
    mk_styles (nsc_marker core d start) = [(SOrd sty d, start)] ->
    items_ok (nsc_marker core d start) (nsc_items core d start lss) = true ->
    parse_lines (list_lines sp (map litem_lines (nsc_items core d start lss)))
                (PPara [])
    = [mk (OrderedList (OLAttrs sty d start) (list_spacing_of sp lss)
             (map (fun L => parse_lines L (PPara [])) lss))].
Proof.
  intros sty core d start sp lss Hne Hm Hsty Hio.
  destruct lss as [|L0 rest]; [congruence|].
  cbn [nsc_items] in Hio |- *.
  rewrite (list_uniformity (nsc_marker core d start) sp L0
             (nsc_items core d (S start) rest) Hm Hio).
  unfold marker_list_checked. rewrite Hsty.
  cbn [map snd]. rewrite map_snd_nsc_items, map_parse_nsc_items. reflexivity.
Qed.

(* The same, with the list closed by a following line. *)
Theorem nsc_uniformity_tail :
  forall sty core d start sp lss next tail,
    lss <> [] ->
    marker_ok (nsc_marker core d start) = true ->
    mk_styles (nsc_marker core d start) = [(SOrd sty d, start)] ->
    items_ok (nsc_marker core d start) (nsc_items core d start lss) = true ->
    classify next <> KBlank ->
    (forall a b c d, classify next <> KList a b c d) ->
    indent_of next = 0 ->
    parse_lines (list_lines sp (map litem_lines (nsc_items core d start lss))
                 ++ EmptyString :: next :: tail)%list (PPara [])
    = mk (OrderedList (OLAttrs sty d start) (list_spacing_of sp lss)
            (map (fun L => parse_lines L (PPara [])) lss))
      :: parse_lines (next :: tail) (PPara []).
Proof.
  intros sty core d start sp lss next tail Hne Hm Hsty Hio Hnb Hnl Hindent.
  destruct lss as [|L0 rest]; [congruence|].
  cbn [nsc_items] in Hio |- *.
  rewrite (list_uniformity_tail (nsc_marker core d start) sp L0
             (nsc_items core d (S start) rest) next tail Hm Hio Hnb Hnl Hindent).
  unfold marker_list_checked. rewrite Hsty.
  cbn [map snd]. rewrite map_snd_nsc_items, map_parse_nsc_items. reflexivity.
Qed.

(*
Decimal ordered lists
---------------------

One style, one delimiter, and consecutive numbering from a start.  The
side condition is `dec_fits` of the last number: the parser takes no
marker core longer than `dec_digits_max` digits.
*)

Definition dec_marker (d : ordered_list_delim) (n : nat) : marker :=
  MOrd (dec_str n) d.

Local Lemma styles_of_core_dec :
  forall core d, nonempty_str core = true -> str_forallb is_digit core = true ->
    Nat.leb (String.length core) dec_digits_max = true ->
    styles_of_core core d = [SOrd Decimal d].
Proof.
  intros [|c rest] d Hne Hd Hl; [discriminate|].
  cbn [styles_of_core]. rewrite Hd, Hl. reflexivity.
Qed.

Local Lemma dec_marker_sty :
  forall d n, dec_fits n = true -> mk_sty (dec_marker d n) = [SOrd Decimal d].
Proof.
  intros d n Hfit. cbn [mk_sty dec_marker].
  apply styles_of_core_dec; [apply dec_str_nonempty | apply dec_str_digits | exact Hfit].
Qed.

Local Lemma dec_marker_ok :
  forall d n, dec_fits n = true -> marker_ok (dec_marker d n) = true.
Proof.
  intros d n Hfit. cbn [marker_ok dec_marker].
  rewrite dec_str_nonempty, (str_digits_alnum _ (dec_str_digits n)).
  change (styles_of_core (dec_str n) d) with (mk_sty (dec_marker d n)).
  rewrite (dec_marker_sty d n Hfit). reflexivity.
Qed.

(* A decimal marker opens with a digit or "(", so its line never reads as
   a thematic break -- which is the one part of `item_ok` that mentions
   the marker, and therefore the reason a decimal item's acceptability
   does not depend on its number. *)
Local Lemma is_thematic_dec_marker :
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

Local Lemma item_ok_dec_marker :
  forall d k n L, item_ok (dec_marker d k) L = item_ok (dec_marker d n) L.
Proof.
  intros d k n [|l0 more]; [reflexivity|].
  cbn [item_ok]. rewrite !is_thematic_dec_marker. reflexivity.
Qed.

Local Lemma dec_marker_styles :
  forall d n, dec_fits n = true -> mk_styles (dec_marker d n) = [(SOrd Decimal d, n)].
Proof.
  intros d n Hfit. unfold mk_styles, with_starts. rewrite (dec_marker_sty d n Hfit).
  cbn [map]. cbn [mk_core dec_marker style_start].
  rewrite dec_value_dec_str. reflexivity.
Qed.

(* So a decimal list closes to the `OrderedList` its start names. *)
Local Lemma marker_list_dec :
  forall d n sp checks items,
    dec_fits n = true ->
    marker_list_checked (dec_marker d n) sp checks items
    = mk (OrderedList (OLAttrs Decimal d n) sp items).
Proof.
  intros d n sp checks items Hfit. unfold marker_list_checked.
  rewrite (dec_marker_styles d n Hfit). reflexivity.
Qed.

(* The markers of a decimal list: consecutive from its start. *)
Fixpoint dec_items (d : ordered_list_delim) (n : nat) (lss : list (list string))
  : list litem :=
  match lss with
  | [] => []
  | L :: rest => (dec_marker d n, L) :: dec_items d (S n) rest
  end.

Local Lemma map_snd_dec_items :
  forall d n lss, map snd (dec_items d n lss) = lss.
Proof.
  intros d n lss. revert n.
  induction lss as [|L rest IH]; intros n; [reflexivity|].
  cbn [dec_items map snd]. rewrite IH. reflexivity.
Qed.

Local Lemma items_ok_dec_items :
  forall d n0 n lss,
    dec_fits n0 = true -> dec_fits (n + length lss - 1) = true ->
    forallb (item_ok (dec_marker d n0)) lss = true ->
    items_ok (dec_marker d n0) (dec_items d n lss) = true.
Proof.
  intros d n0 n lss Hfit0. revert n.
  induction lss as [|L rest IH]; intros n Hfit Hok; [reflexivity|].
  cbn [forallb] in Hok. apply andb_prop in Hok as [HL Hrest].
  cbn [length] in Hfit.
  assert (Hn : dec_fits n = true)
    by (apply (dec_fits_le n (n + S (length rest) - 1)); [lia | exact Hfit]).
  cbn [dec_items items_ok items_ok_at forallb fst snd].
  rewrite (dec_marker_ok d n Hn), (item_ok_dec_marker d n n0 L), HL.
  assert (Hs : admits_styles (mk_styles (dec_marker d n0)) (dec_marker d n) = true).
  { apply admits_agree. rewrite (dec_marker_sty d n Hn), (dec_marker_sty d n0 Hfit0).
    reflexivity. }
  rewrite Hs. cbn [andb].
  change (forallb _ (dec_items d (S n) rest))
    with (items_ok_at (mk_styles (dec_marker d n0)) (dec_items d (S n) rest)).
  apply IH; [|exact Hrest]. replace (S n + length rest - 1) with (n + S (length rest) - 1)
    by lia. exact Hfit.
Qed.

Local Lemma map_litem_lines_dec_items :
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

Local Lemma map_parse_dec_items :
  forall d n lss,
    map (fun it => parse_lines (snd it) (PPara [])) (dec_items d n lss)
    = map (fun L => parse_lines L (PPara [])) lss.
Proof.
  intros d n lss. revert n.
  induction lss as [|L rest IH]; intros n; [reflexivity|].
  cbn [dec_items map snd]. rewrite IH. reflexivity.
Qed.

(* Uniformity for a decimal ordered list: consecutive markers from
   `start`, each with its own width, the last short enough to parse. *)
Theorem ordered_decimal_uniformity :
  forall d start sp lss,
    lss <> [] ->
    dec_fits (start + length lss - 1) = true ->
    forallb (item_ok (dec_marker d start)) lss = true ->
    parse_lines (list_lines sp (map litem_lines (dec_items d start lss)))
                (PPara [])
    = [mk (OrderedList (OLAttrs Decimal d start) (list_spacing_of sp lss)
             (map (fun L => parse_lines L (PPara [])) lss))].
Proof.
  intros d start sp lss Hne Hfit Hok.
  destruct lss as [|L0 rest]; [congruence|].
  assert (H0 : dec_fits start = true)
    by (apply (dec_fits_le start (start + length (L0 :: rest) - 1));
        [cbn [length]; lia | exact Hfit]).
  pose proof (items_ok_dec_items d start start (L0 :: rest) H0 Hfit Hok) as Hio.
  cbn [dec_items] in Hio |- *.
  rewrite (list_uniformity (dec_marker d start) sp L0
             (dec_items d (S start) rest) (dec_marker_ok d start H0) Hio).
  rewrite (marker_list_dec _ _ _ _ _ H0).
  cbn [map snd]. rewrite map_snd_dec_items, map_parse_dec_items. reflexivity.
Qed.

(* The same, with the list closed by a following line rather than by the
   end of the input.  The two endings are `list_uniformity`'s and
   `list_uniformity_tail`'s; everything between them is shared. *)
Theorem ordered_decimal_uniformity_tail :
  forall d start sp lss next tail,
    lss <> [] ->
    dec_fits (start + length lss - 1) = true ->
    forallb (item_ok (dec_marker d start)) lss = true ->
    classify next <> KBlank ->
    (forall a b c d, classify next <> KList a b c d) ->
    indent_of next = 0 ->
    parse_lines (list_lines sp (map litem_lines (dec_items d start lss))
                 ++ EmptyString :: next :: tail)%list (PPara [])
    = mk (OrderedList (OLAttrs Decimal d start) (list_spacing_of sp lss)
            (map (fun L => parse_lines L (PPara [])) lss))
      :: parse_lines (next :: tail) (PPara []).
Proof.
  intros d start sp lss next tail Hne Hfit Hok Hnb Hnl Hindent.
  destruct lss as [|L0 rest]; [congruence|].
  assert (H0 : dec_fits start = true)
    by (apply (dec_fits_le start (start + length (L0 :: rest) - 1));
        [cbn [length]; lia | exact Hfit]).
  pose proof (items_ok_dec_items d start start (L0 :: rest) H0 Hfit Hok) as Hio.
  cbn [dec_items] in Hio |- *.
  rewrite (list_uniformity_tail (dec_marker d start) sp L0
             (dec_items d (S start) rest) next tail
             (dec_marker_ok d start H0) Hio Hnb Hnl Hindent).
  rewrite (marker_list_dec _ _ _ _ _ H0).
  cbn [map snd]. rewrite map_snd_dec_items, map_parse_dec_items. reflexivity.
Qed.

(*
Roman and alpha ordered lists
-----------------------------

Two more instantiations of `nsc_uniformity`, and the side condition they
carry that decimal does not.  It is one condition in two spellings: the
first marker must name exactly one style.

A bare roman letter (`i`, `v`, `x`, `l`, `c`, `d`, `m`) is also a single
letter, so it offers roman and alpha both; any longer numeral offers only
roman.  A single letter that is not a roman digit offers only alpha.  So
a roman list is covered when its first numeral is at least two
characters, and an alpha list when its first letter is not a roman
digit.  Later markers are unconstrained either way, because `admits`
asks only that a sibling still offer what the list opened with, and
every roman numeral offers roman just as every letter offers alpha.

The exception sets are roman starts 1, 5, 10, 50, 100, 500, 1000 and
alpha starts 3, 4, 9, 12, 13, 22, 24 (`c d i l m v x`).  The parser
round-trips all of them: the sets bound the reach of the hypothesis, not
of the parser.

The `_any` theorems below lift it.  A style set that narrows as the run
proceeds costs the ambiguous opener nothing: one item closes on the
unnarrowed head, and a second narrows to the singleton and holds it.  So
`ck_ok` asks roman for a range and nothing else, and asks alpha only for
an opener that names alpha alone or a second item to settle it.
*)

Definition roman_sty (up : bool) : ordered_list_style :=
  if up then RomanUpper else RomanLower.

Definition alpha_sty (up : bool) : ordered_list_style :=
  if up then LetterUpper else LetterLower.

Local Lemma styles_of_core_roman :
  forall (up : bool) core d,
    str_forallb (if up then is_roman_up else is_roman_lo) core = true ->
    2 <= String.length core ->
    styles_of_core core d = [SOrd (roman_sty up) d].
Proof.
  intros up [|c rest] d H Hlen; [cbn in Hlen; lia|].
  destruct rest as [|c' rest']; [cbn in Hlen; lia|].
  cbn [styles_of_core].
  rewrite (str_roman_not_digit up c (String c' rest') H).
  destruct up.
  - assert (Hlo : str_forallb is_roman_lo (String c (String c' rest')) = false).
    { cbn [str_forallb] in *. apply andb_true_iff in H as [Hc _].
      rewrite (is_upper_not_roman_lo c (is_roman_up_upper c Hc)). reflexivity. }
    rewrite Hlo, H. reflexivity.
  - rewrite H. reflexivity.
Qed.

Local Lemma styles_of_core_alpha :
  forall (up : bool) c d,
    (if up then is_upper else is_lower) c = true ->
    (if up then is_roman_up else is_roman_lo) c = false ->
    styles_of_core (String c EmptyString) d = [SOrd (alpha_sty up) d].
Proof.
  intros up c d Hcase Hnr. destruct up; cbn [styles_of_core str_forallb].
  - rewrite (is_upper_not_digit c Hcase). cbn [andb].
    rewrite (is_upper_not_roman_lo c Hcase), Hnr,
            (is_upper_not_lower c Hcase), Hcase. reflexivity.
  - rewrite (is_lower_not_digit c Hcase). cbn [andb].
    rewrite Hnr, (is_lower_not_roman_up c Hcase), Hcase. reflexivity.
Qed.

(* The two hypotheses `nsc_uniformity` asks of a first marker, discharged
   for roman under its range and length conditions. *)
Local Lemma roman_marker_styles :
  forall (up : bool) d n,
    1 <= n -> n <= Roman.upper -> 2 <= String.length (Roman.str up n) ->
    mk_styles (nsc_marker (Roman.str up) d n) = [(SOrd (roman_sty up) d, n)].
Proof.
  intros up d n H1 H2 Hlen. unfold mk_styles, with_starts.
  cbn [mk_sty nsc_marker].
  rewrite (styles_of_core_roman up _ d (Roman.str_alphabet up n H1 H2) Hlen).
  cbn [map mk_core nsc_marker]. unfold roman_sty.
  destruct up; cbn [style_start]; rewrite (Roman.value_str _ n H1 H2); reflexivity.
Qed.

Local Lemma roman_marker_ok :
  forall (up : bool) d n,
    1 <= n -> n <= Roman.upper -> 2 <= String.length (Roman.str up n) ->
    marker_ok (nsc_marker (Roman.str up) d n) = true.
Proof.
  intros up d n H1 H2 Hlen. cbn [marker_ok nsc_marker].
  rewrite (Roman.str_nonempty up n H1 H2).
  assert (Halnum : str_forallb is_alnum (Roman.str up n) = true).
  { apply (str_forallb_impl (if up then is_roman_up else is_roman_lo)).
    - intros c Hc. unfold is_alnum. destruct up.
      + rewrite (is_roman_up_upper c Hc), !orb_true_r. reflexivity.
      + rewrite (is_roman_lo_lower c Hc), orb_true_r. reflexivity.
    - apply Roman.str_alphabet; assumption. }
  rewrite Halnum.
  rewrite (styles_of_core_roman up _ d (Roman.str_alphabet up n H1 H2) Hlen).
  reflexivity.
Qed.

Local Lemma alpha_marker_styles :
  forall (up : bool) d n,
    1 <= n -> n <= Alpha.upper ->
    (if up then is_roman_up else is_roman_lo)
      (ascii_of_nat ((if up then 64 else 96) + n)) = false ->
    mk_styles (nsc_marker (Alpha.str up) d n) = [(SOrd (alpha_sty up) d, n)].
Proof.
  intros up d n H1 H2 Hnr. unfold mk_styles, with_starts.
  cbn [mk_sty nsc_marker].
  assert (Hcase : (if up then is_upper else is_lower)
                    (ascii_of_nat ((if up then 64 else 96) + n)) = true).
  { pose proof (Alpha.str_alphabet up n H1 H2) as H.
    unfold Alpha.str in H. cbn [str_forallb] in H.
    apply andb_true_iff in H as [H _]. exact H. }
  unfold Alpha.str.
  rewrite (styles_of_core_alpha up _ d Hcase Hnr).
  cbn [map mk_core nsc_marker]. unfold alpha_sty.
  pose proof (Alpha.value_str up n H1 H2) as Hv. unfold Alpha.str in Hv.
  destruct up; cbn [style_start]; rewrite Hv; reflexivity.
Qed.

Local Lemma alpha_marker_ok :
  forall (up : bool) d n,
    1 <= n -> n <= Alpha.upper ->
    (if up then is_roman_up else is_roman_lo)
      (ascii_of_nat ((if up then 64 else 96) + n)) = false ->
    marker_ok (nsc_marker (Alpha.str up) d n) = true.
Proof.
  intros up d n H1 H2 Hnr. cbn [marker_ok nsc_marker].
  rewrite (Alpha.str_nonempty up n H1 H2).
  assert (Hcase : (if up then is_upper else is_lower)
                    (ascii_of_nat ((if up then 64 else 96) + n)) = true).
  { pose proof (Alpha.str_alphabet up n H1 H2) as H.
    unfold Alpha.str in H. cbn [str_forallb] in H.
    apply andb_true_iff in H as [H _]. exact H. }
  assert (Halnum : str_forallb is_alnum (Alpha.str up n) = true).
  { apply (str_forallb_impl (if up then is_upper else is_lower)).
    - intros c Hc. unfold is_alnum. destruct up.
      + rewrite Hc, !orb_true_r. reflexivity.
      + rewrite Hc, orb_true_r. reflexivity.
    - apply Alpha.str_alphabet; assumption. }
  rewrite Halnum. unfold Alpha.str.
  rewrite (styles_of_core_alpha up _ d Hcase Hnr). reflexivity.
Qed.

(*
Deriving `items_ok` for a run
-----------------------------

`nsc_uniformity` takes `items_ok` as a hypothesis, which a concrete start
can compute but a general theorem cannot.  These lemmas derive it from
what a caller actually has: a range, a condition on the *first* marker,
and `item_ok` at that one marker -- which is exactly the shape
`Render.cb_ok` produces.

Two facts do the work, and they are why later items need no condition.
Every marker in the run still *offers* the style the list opened with
(`roman_item_facts`, `alpha_item_facts`), which is all `admits` asks; and
`item_ok` depends on its marker only through `is_thematic`, which is
false for every marker whose numeral starts with an alphanumeric, so
`item_ok` at one marker of the run gives it at all of them.
*)

Local Lemma styles_of_core_roman_cons :
  forall (up : bool) core d,
    str_forallb (if up then is_roman_up else is_roman_lo) core = true ->
    nonempty_str core = true ->
    exists rest, styles_of_core core d = SOrd (roman_sty up) d :: rest.
Proof.
  intros up [|c rest] d H Hne; [discriminate|].
  destruct rest as [|c' rest'].
  - cbn [str_forallb] in H. apply andb_true_iff in H as [Hc _].
    destruct up; cbn [styles_of_core str_forallb].
    + rewrite (is_upper_not_digit c (is_roman_up_upper c Hc)). cbn [andb].
      rewrite (is_upper_not_roman_lo c (is_roman_up_upper c Hc)), Hc.
      eexists. reflexivity.
    + rewrite (is_lower_not_digit c (is_roman_lo_lower c Hc)). cbn [andb].
      rewrite Hc. eexists. reflexivity.
  - exists []. apply (styles_of_core_roman up _ d H). cbn [String.length]. lia.
Qed.

Local Lemma existsb_nonempty :
  forall {A} (f : A -> bool) l, existsb f l = true -> nonempty l = true.
Proof. intros A f [|x l] H; [discriminate|reflexivity]. Qed.

(* Alpha items get membership, not a singleton: a letter that is also a
   roman digit offers roman *first*, and only the first marker of a list
   is required to name one style. *)
Local Lemma styles_of_core_alpha_mem :
  forall (up : bool) c d,
    (if up then is_upper else is_lower) c = true ->
    existsb (lstyle_eqb (SOrd (alpha_sty up) d))
            (styles_of_core (String c EmptyString) d) = true.
Proof.
  intros up c d Hcase. destruct up; cbn [styles_of_core str_forallb].
  - rewrite (is_upper_not_digit c Hcase). cbn [andb].
    rewrite (is_upper_not_roman_lo c Hcase).
    destruct (is_roman_up c) eqn:Eru.
    + cbn [existsb alpha_sty]. rewrite lstyle_eqb_refl, orb_true_r. reflexivity.
    + rewrite (is_upper_not_lower c Hcase), Hcase.
      cbn [existsb alpha_sty]. rewrite lstyle_eqb_refl. reflexivity.
  - rewrite (is_lower_not_digit c Hcase). cbn [andb].
    destruct (is_roman_lo c) eqn:Erl.
    + cbn [existsb alpha_sty]. rewrite lstyle_eqb_refl, orb_true_r. reflexivity.
    + rewrite (is_lower_not_roman_up c Hcase), Hcase.
      cbn [existsb alpha_sty]. rewrite lstyle_eqb_refl. reflexivity.
Qed.

Local Lemma is_thematic_ord_marker :
  forall c rest d l,
    is_alnum c = true ->
    is_thematic (mk_open (MOrd (String c rest) d) ++ l) = false.
Proof.
  intros c rest d l Hc. destruct d; cbn [mk_open].
  - change ((String c rest ++ ". ") ++ l)%string
      with (String c ((rest ++ ". ") ++ l))%string.
    apply thematic_first_char;
      [apply is_alnum_not_marker | apply is_alnum_not_special]; exact Hc.
  - change ((String c rest ++ ") ") ++ l)%string
      with (String c ((rest ++ ") ") ++ l))%string.
    apply thematic_first_char;
      [apply is_alnum_not_marker | apply is_alnum_not_special]; exact Hc.
  - change (("(" ++ String c rest ++ ") ") ++ l)%string
      with (String "(" ((String c rest ++ ") ") ++ l))%string.
    apply thematic_first_char; reflexivity.
Qed.

(* The whole of `item_ok`'s dependence on its marker.  The task-marker
   conjunct is not part of it: it tests the line alone (`Line.task_start`). *)
Local Lemma item_ok_thematic_indep :
  forall m m' L,
    (forall l, is_thematic (mk_open m ++ l) = false) ->
    (forall l, is_thematic (mk_open m' ++ l) = false) ->
    item_ok m L = item_ok m' L.
Proof.
  intros m m' [|l0 more] H H'; [reflexivity|].
  cbn [item_ok]. rewrite H, H'. reflexivity.
Qed.

Local Lemma items_ok_nsc_run :
  forall core d Sty m0 lss n,
    (forall k, k < length lss ->
       marker_ok (nsc_marker core d (n + k)) = true
       /\ admits_styles Sty (nsc_marker core d (n + k)) = true
       /\ (forall l, is_thematic (mk_open (nsc_marker core d (n + k)) ++ l) = false)) ->
    (forall l, is_thematic (mk_open m0 ++ l) = false) ->
    forallb (item_ok m0) lss = true ->
    items_ok_at Sty (nsc_items core d n lss) = true.
Proof.
  intros core d Sty m0 lss. induction lss as [|L rest IH]; intros n Hrun Hm0 Hok;
    [reflexivity|].
  cbn [forallb] in Hok. apply andb_true_iff in Hok as [HL Hrest].
  destruct (Hrun 0 ltac:(cbn [length]; lia)) as (Hmk & Had & Hth).
  rewrite Nat.add_0_r in Hmk, Had, Hth.
  cbn [nsc_items items_ok items_ok_at forallb fst snd].
  rewrite Hmk, Had, (item_ok_thematic_indep _ m0 L Hth Hm0), HL.
  cbn [andb].
  change (forallb _ (nsc_items core d (S n) rest))
    with (items_ok_at Sty (nsc_items core d (S n) rest)).
  apply IH; [|exact Hm0|exact Hrest].
  intros k Hk. destruct (Hrun (S k) ltac:(cbn [length]; lia)) as (A & B & C).
  rewrite <- Nat.add_succ_comm in A, B, C. exact (conj A (conj B C)).
Qed.

(* What every item of a roman run satisfies, with no condition beyond the
   range -- a bare `v` included. *)
Local Lemma roman_item_facts :
  forall (up : bool) d n, 1 <= n -> n <= Roman.upper ->
    marker_ok (nsc_marker (Roman.str up) d n) = true
    /\ existsb (lstyle_eqb (SOrd (roman_sty up) d))
               (mk_sty (nsc_marker (Roman.str up) d n)) = true
    /\ (forall l, is_thematic (mk_open (nsc_marker (Roman.str up) d n) ++ l) = false).
Proof.
  intros up d n H1 H2.
  pose proof (Roman.str_alphabet up n H1 H2) as Halpha.
  pose proof (Roman.str_nonempty up n H1 H2) as Hne.
  destruct (styles_of_core_roman_cons up (Roman.str up n) d Halpha Hne) as [rest Hs].
  assert (Halnum : str_forallb is_alnum (Roman.str up n) = true).
  { apply (str_forallb_impl (if up then is_roman_up else is_roman_lo)); [|exact Halpha].
    intros c Hc. unfold is_alnum. destruct up.
    - rewrite (is_roman_up_upper c Hc), !orb_true_r. reflexivity.
    - rewrite (is_roman_lo_lower c Hc), orb_true_r. reflexivity. }
  destruct (Roman.str up n) as [|c t] eqn:E; [discriminate Hne|].
  cbn [str_forallb] in Halnum. apply andb_true_iff in Halnum as [Hc Ht].
  split; [|split].
  - cbn [marker_ok nsc_marker]. rewrite E in *. rewrite Hne.
    cbn [str_forallb]. rewrite Hc, Ht, Hs. reflexivity.
  - cbn [mk_sty nsc_marker]. rewrite E, Hs.
    cbn [existsb]. rewrite lstyle_eqb_refl. reflexivity.
  - intros l. unfold nsc_marker. rewrite E. apply is_thematic_ord_marker, Hc.
Qed.

Local Lemma alpha_item_facts :
  forall (up : bool) d n, 1 <= n -> n <= Alpha.upper ->
    marker_ok (nsc_marker (Alpha.str up) d n) = true
    /\ existsb (lstyle_eqb (SOrd (alpha_sty up) d))
               (mk_sty (nsc_marker (Alpha.str up) d n)) = true
    /\ (forall l, is_thematic (mk_open (nsc_marker (Alpha.str up) d n) ++ l) = false).
Proof.
  intros up d n H1 H2.
  pose proof (Alpha.str_alphabet up n H1 H2) as Halpha.
  unfold Alpha.str in Halpha |- *.
  cbn [str_forallb] in Halpha. apply andb_true_iff in Halpha as [Hcase _].
  pose proof (styles_of_core_alpha_mem up _ d Hcase) as Hmem.
  assert (Halnum : is_alnum (ascii_of_nat ((if up then 64 else 96) + n)) = true).
  { unfold is_alnum. destruct up.
    - rewrite Hcase, !orb_true_r. reflexivity.
    - rewrite Hcase, orb_true_r. reflexivity. }
  split; [|split].
  - unfold nsc_marker. cbn [marker_ok str_forallb nonempty_str].
    rewrite Halnum. cbn [andb]. exact (existsb_nonempty _ _ Hmem).
  - unfold nsc_marker. cbn [mk_sty]. exact Hmem.
  - intros l. unfold nsc_marker. apply is_thematic_ord_marker, Halnum.
Qed.

(*
Roman at every start
--------------------

The ambiguity condition drops out for roman entirely.  Two facts do it.
A roman numeral's candidate set always has `(RomanLower, n)` at its
head, ambiguous or not, so a one-item list closes correctly with no
narrowing at all.  And no two consecutive roman numerals are both a
single character (`Roman.consec_lt`), so a list with a second item has
its set narrowed to the singleton by that item, and everything after
holds it.

Alpha gets no such theorem: `c` and `d` are adjacent and both roman
digits, as are `l` and `m`, so an alpha list from 3 or 12 is still
unresolved after its second marker.
*)

Local Lemma styles_of_core_roman_single :
  forall (up : bool) c d,
    (if up then is_roman_up else is_roman_lo) c = true ->
    styles_of_core (String c EmptyString) d
    = [SOrd (roman_sty up) d; SOrd (alpha_sty up) d].
Proof.
  intros up c d Hc. destruct up; cbn [styles_of_core str_forallb].
  - rewrite (is_upper_not_digit c (is_roman_up_upper c Hc)). cbn [andb].
    rewrite (is_upper_not_roman_lo c (is_roman_up_upper c Hc)), Hc. reflexivity.
  - rewrite (is_lower_not_digit c (is_roman_lo_lower c Hc)). cbn [andb].
    rewrite Hc. reflexivity.
Qed.

(* The head, with no length condition. *)
Local Lemma roman_marker_head :
  forall (up : bool) d n, 1 <= n -> n <= Roman.upper ->
    exists rest, mk_styles (nsc_marker (Roman.str up) d n)
                 = (SOrd (roman_sty up) d, n) :: rest.
Proof.
  intros up d n H1 H2.
  destruct (styles_of_core_roman_cons up (Roman.str up n) d
              (Roman.str_alphabet up n H1 H2) (Roman.str_nonempty up n H1 H2))
    as [rest Hs].
  unfold mk_styles, with_starts. cbn [mk_sty nsc_marker]. rewrite Hs.
  cbn [map mk_core nsc_marker].
  eexists. f_equal. f_equal.
  unfold roman_sty; destruct up; cbn [style_start];
    apply Roman.value_str; assumption.
Qed.

(* And the set a second item narrows it to, always the singleton. *)
Local Lemma roman_narrow_singleton :
  forall (up : bool) d n, 1 <= n -> S n <= Roman.upper ->
    narrow (mk_styles (nsc_marker (Roman.str up) d n))
           (mk_sty (nsc_marker (Roman.str up) d (S n)))
    = [(SOrd (roman_sty up) d, n)].
Proof.
  intros up d n H1 H2.
  destruct (Nat.leb 2 (String.length (Roman.str up n))) eqn:Hl.
  - (* this numeral is unambiguous already *)
    apply Nat.leb_le in Hl.
    rewrite (roman_marker_styles up d n H1 ltac:(lia) Hl).
    cbn [narrow filter fst].
    rewrite (proj1 (proj2 (roman_item_facts up d (S n) ltac:(lia) H2))).
    reflexivity.
  - (* it is a bare roman letter, so the next numeral is not *)
    apply Nat.leb_gt in Hl.
    destruct (Roman.consec_lt up n H1 ltac:(lia)) as [Hbad | Hlen]; [lia|].
    pose proof (Roman.str_alphabet up n H1 ltac:(lia)) as Ha.
    pose proof (Roman.str_nonempty up n H1 ltac:(lia)) as Hne.
    destruct (Roman.str up n) as [|c t] eqn:E; [discriminate Hne|].
    destruct t as [|c' t']; [|cbn [String.length] in Hl; lia].
    cbn [str_forallb] in Ha. apply andb_true_iff in Ha as [Hc _].
    unfold mk_styles, with_starts. cbn [mk_sty nsc_marker mk_core]. rewrite E.
    rewrite (styles_of_core_roman_single up c d Hc).
    rewrite (styles_of_core_roman up _ d (Roman.str_alphabet up (S n) ltac:(lia) H2)
               Hlen).
    cbn [map narrow filter fst existsb].
    rewrite lstyle_eqb_refl. cbn [orb].
    assert (Hne2 : lstyle_eqb (SOrd (alpha_sty up) d) (SOrd (roman_sty up) d) = false)
      by (unfold alpha_sty, roman_sty; destruct up; reflexivity).
    rewrite Hne2. cbn [orb].
    f_equal. f_equal. rewrite <- E.
    unfold roman_sty; destruct up; cbn [style_start];
      apply Roman.value_str; [lia|lia|lia|lia].
Qed.

(* Uniformity for a roman ordered list at *any* start in range.  One item
   closes on the unnarrowed head; two or more narrow to the singleton at
   the second, and hold it. *)
Theorem ordered_roman_uniformity_any :
  forall (up : bool) d start sp lss,
    lss <> [] -> 1 <= start -> start + length lss <= S Roman.upper ->
    forallb (item_ok (nsc_marker (Roman.str up) d start)) lss = true ->
    parse_lines (list_lines sp (map litem_lines (nsc_items (Roman.str up) d start lss)))
                (PPara [])
    = [mk (OrderedList (OLAttrs (roman_sty up) d start) (list_spacing_of sp lss)
             (map (fun L => parse_lines L (PPara [])) lss))].
Proof.
  intros up d start sp lss Hne H1 H2 Hok.
  assert (Hl : 1 <= length lss) by (destruct lss; [congruence|cbn [length]; lia]).
  destruct (roman_item_facts up d start H1 ltac:(lia)) as (Hmk0 & Hmem0 & Hth0).
  destruct lss as [|L0 [|L1 rest]]; [congruence| |].
  - (* one item: no sibling, and the head is roman already *)
    cbn [forallb] in Hok. apply andb_true_iff in Hok as [HL0 _].
    destruct (roman_marker_head up d start H1 ltac:(cbn [length] in H2; lia))
      as [r Hhead].
    cbn [nsc_items].
    etransitivity;
      [exact (list_uniformity (nsc_marker (Roman.str up) d start) sp L0 [] Hmk0
                ltac:(unfold items_ok, items_ok_at; cbn [forallb fst snd];
                      rewrite Hmk0, HL0, admits_styles_refl; reflexivity))|].
    unfold marker_list_checked. rewrite Hhead.
    cbn [map snd styles_list_checked styles_list]. reflexivity.
  - (* two or more: the second numeral resolves the set *)
    cbn [length] in H2.
    destruct (roman_item_facts up d (S start) ltac:(lia) ltac:(lia))
      as (Hmk1 & Hmem1 & Hth1).
    cbn [forallb] in Hok. apply andb_true_iff in Hok as [HL0 Hok'].
    pose proof Hok' as Hok''. apply andb_true_iff in Hok'' as [HL1 Hrest].
    destruct L1 as [|l1 more1]; [cbn [item_ok] in HL1; discriminate|].
    assert (HS : narrow (mk_styles (nsc_marker (Roman.str up) d start))
                        (mk_sty (nsc_marker (Roman.str up) d (S start)))
                 = [(SOrd (roman_sty up) d, start)])
      by (apply roman_narrow_singleton; lia).
    assert (Hitems : items_ok_at [(SOrd (roman_sty up) d, start)]
                       (nsc_items (Roman.str up) d (S (S start)) rest) = true).
    { apply (items_ok_nsc_run (Roman.str up) d [(SOrd (roman_sty up) d, start)]
               (nsc_marker (Roman.str up) d start) rest (S (S start))).
      - intros k Hk.
        destruct (roman_item_facts up d (S (S start) + k) ltac:(lia) ltac:(lia))
          as (A & B & C).
        split; [exact A|]. split; [|exact C].
        unfold admits_styles. cbn [forallb fst]. rewrite B. reflexivity.
      - exact Hth0.
      - exact Hrest. }
    cbn [nsc_items].
    rewrite (list_uniformity_narrow (nsc_marker (Roman.str up) d start)
               (nsc_marker (Roman.str up) d (S start))
               [(SOrd (roman_sty up) d, start)] sp L0 (l1 :: more1)
               (nsc_items (Roman.str up) d (S (S start)) rest)
               Hmk0 Hmk1 eq_refl eq_refl ltac:(discriminate) HS HL0
               (ltac:(rewrite (item_ok_thematic_indep _ _ (l1 :: more1) Hth1 Hth0);
                      exact HL1))
               ltac:(discriminate) Hitems).
    cbn [styles_list_checked styles_list map snd].
    rewrite map_snd_nsc_items, map_parse_nsc_items.
    reflexivity.
Qed.

Theorem ordered_roman_uniformity_any_tail :
  forall (up : bool) d start sp lss next tl,
    lss <> [] -> 1 <= start -> start + length lss <= S Roman.upper ->
    forallb (item_ok (nsc_marker (Roman.str up) d start)) lss = true ->
    classify next <> KBlank ->
    (forall a b c d, classify next <> KList a b c d) ->
    indent_of next = 0 ->
    parse_lines (list_lines sp (map litem_lines (nsc_items (Roman.str up) d start lss))
                 ++ EmptyString :: next :: tl)%list (PPara [])
    = mk (OrderedList (OLAttrs (roman_sty up) d start) (list_spacing_of sp lss)
             (map (fun L => parse_lines L (PPara [])) lss))
      :: parse_lines (next :: tl) (PPara []).
Proof.
  intros up d start sp lss next tl Hne H1 H2 Hok Hnb Hnl Hindent.
  assert (Hl : 1 <= length lss) by (destruct lss; [congruence|cbn [length]; lia]).
  destruct (roman_item_facts up d start H1 ltac:(lia)) as (Hmk0 & Hmem0 & Hth0).
  destruct lss as [|L0 [|L1 rest]]; [congruence| |].
  - (* one item: no sibling, and the head is roman already *)
    cbn [forallb] in Hok. apply andb_true_iff in Hok as [HL0 _].
    destruct (roman_marker_head up d start H1 ltac:(cbn [length] in H2; lia))
      as [r Hhead].
    cbn [nsc_items].
    etransitivity;
      [exact (list_uniformity_tail (nsc_marker (Roman.str up) d start) sp L0 [] next tl Hmk0
                ltac:(unfold items_ok, items_ok_at; cbn [forallb fst snd];
                      rewrite Hmk0, HL0, admits_styles_refl; reflexivity)
                Hnb Hnl Hindent)|].
    unfold marker_list_checked. rewrite Hhead.
    cbn [map snd styles_list_checked styles_list]. reflexivity.
  - (* two or more: the second numeral resolves the set *)
    cbn [length] in H2.
    destruct (roman_item_facts up d (S start) ltac:(lia) ltac:(lia))
      as (Hmk1 & Hmem1 & Hth1).
    cbn [forallb] in Hok. apply andb_true_iff in Hok as [HL0 Hok'].
    pose proof Hok' as Hok''. apply andb_true_iff in Hok'' as [HL1 Hrest].
    destruct L1 as [|l1 more1]; [cbn [item_ok] in HL1; discriminate|].
    assert (HS : narrow (mk_styles (nsc_marker (Roman.str up) d start))
                        (mk_sty (nsc_marker (Roman.str up) d (S start)))
                 = [(SOrd (roman_sty up) d, start)])
      by (apply roman_narrow_singleton; lia).
    assert (Hitems : items_ok_at [(SOrd (roman_sty up) d, start)]
                       (nsc_items (Roman.str up) d (S (S start)) rest) = true).
    { apply (items_ok_nsc_run (Roman.str up) d [(SOrd (roman_sty up) d, start)]
               (nsc_marker (Roman.str up) d start) rest (S (S start))).
      - intros k Hk.
        destruct (roman_item_facts up d (S (S start) + k) ltac:(lia) ltac:(lia))
          as (A & B & C).
        split; [exact A|]. split; [|exact C].
        unfold admits_styles. cbn [forallb fst]. rewrite B. reflexivity.
      - exact Hth0.
      - exact Hrest. }
    cbn [nsc_items].
    rewrite (list_uniformity_narrow_tail (nsc_marker (Roman.str up) d start)
               (nsc_marker (Roman.str up) d (S start))
               [(SOrd (roman_sty up) d, start)] sp L0 (l1 :: more1)
               (nsc_items (Roman.str up) d (S (S start)) rest) next tl
               Hmk0 Hmk1 eq_refl eq_refl ltac:(discriminate) HS HL0
               (ltac:(rewrite (item_ok_thematic_indep _ _ (l1 :: more1) Hth1 Hth0);
                      exact HL1))
               ltac:(discriminate) Hitems Hnb Hnl Hindent).
    cbn [styles_list_checked styles_list map snd].
    rewrite map_snd_nsc_items, map_parse_nsc_items.
    reflexivity.
Qed.

(* Uniformity for a roman ordered list.  The hypotheses are the run's
   range, the first numeral being at least two characters (so it names
   roman alone), and `item_ok` at the first marker. *)
Theorem ordered_roman_uniformity :
  forall (up : bool) d start sp lss,
    lss <> [] ->
    1 <= start -> start + length lss <= S Roman.upper ->
    2 <= String.length (Roman.str up start) ->
    forallb (item_ok (nsc_marker (Roman.str up) d start)) lss = true ->
    parse_lines (list_lines sp (map litem_lines (nsc_items (Roman.str up) d start lss)))
                (PPara [])
    = [mk (OrderedList (OLAttrs (roman_sty up) d start) (list_spacing_of sp lss)
             (map (fun L => parse_lines L (PPara [])) lss))].
Proof.
  intros up d start sp lss Hne H1 H2 Hlen Hok.
  assert (Hl : 1 <= length lss) by (destruct lss; [congruence|cbn [length]; lia]).
  assert (Hsty : mk_styles (nsc_marker (Roman.str up) d start)
                 = [(SOrd (roman_sty up) d, start)])
    by (apply roman_marker_styles; [lia|lia|exact Hlen]).
  assert (Hio : items_ok (nsc_marker (Roman.str up) d start)
                  (nsc_items (Roman.str up) d start lss) = true).
  { apply (items_ok_nsc_run (Roman.str up) d (mk_styles (nsc_marker (Roman.str up) d start))
             (nsc_marker (Roman.str up) d start) lss start).
    - intros k Hk.
      destruct (roman_item_facts up d (start + k) ltac:(lia) ltac:(lia)) as (A & B & C).
      split; [exact A|]. split; [|exact C].
      unfold admits_styles. rewrite Hsty. cbn [forallb fst].
      rewrite B. reflexivity.
    - exact (proj2 (proj2 (roman_item_facts up d start ltac:(lia) ltac:(lia)))).
    - exact Hok. }
  exact (nsc_uniformity (roman_sty up) (Roman.str up) d start sp lss Hne
           (roman_marker_ok up d start ltac:(lia) ltac:(lia) Hlen) Hsty Hio).
Qed.

(*
Alpha where the second letter resolves it
----------------------------------------

Alpha has neither of roman's two properties, so it needs a condition and
gets a weaker theorem.  Its head is *wrong* at an ambiguous start -- `i`
heads roman -- so a one-item list there cannot work at all, and that is
not a gap: `i. a` is also what roman from 1 renders, so at most one of
the two canonical trees can round-trip.  What can be recovered is the
case where the *second* letter is not a roman digit, which resolves the
set in one narrowing exactly as roman's second numeral does.

That reaches five of the seven ambiguous starts.  It misses 3 and 12,
where the next letter (`d` after `c`, `m` after `l`) is itself a roman
digit and the set survives two markers.
*)

Local Definition alpha_char (up : bool) (n : nat) : ascii :=
  ascii_of_nat ((if up then 64 else 96) + n).

(* Is this position's letter also a roman digit?  The seven that are --
   c, d, i, l, m, v, x -- are what make an alpha marker ambiguous. *)
Definition alpha_roman_digit (up : bool) (n : nat) : bool :=
  (if up then is_roman_up else is_roman_lo) (alpha_char up n).

(* Narrowing by a letter that is itself a roman digit changes nothing:
   it offers both candidates, so every style the list still has survives.
   This is the step that makes an alpha list from `c` or from `l` need a
   second peel -- `d` and `m` leave the set exactly where it was. *)
Local Lemma alpha_narrow_id :
  forall (up : bool) d n m, 1 <= n -> n <= Alpha.upper -> 1 <= m -> m <= Alpha.upper ->
    alpha_roman_digit up m = true ->
    narrow (mk_styles (nsc_marker (Alpha.str up) d n))
           (mk_sty (nsc_marker (Alpha.str up) d m))
    = mk_styles (nsc_marker (Alpha.str up) d n).
Proof.
  intros up d n m H1 H2 Hm1 Hm2 Hr. unfold alpha_roman_digit in Hr.
  assert (Hc0 : (if up then is_upper else is_lower) (alpha_char up n) = true).
  { pose proof (Alpha.str_alphabet up n H1 H2) as H.
    unfold Alpha.str, alpha_char in *. cbn [str_forallb] in H.
    apply andb_true_iff in H as [H _]. exact H. }
  apply narrow_admits_styles.
  unfold admits_styles, mk_styles, with_starts, nsc_marker. cbn [mk_sty mk_core].
  change (Alpha.str up m) with (String (alpha_char up m) EmptyString).
  change (Alpha.str up n) with (String (alpha_char up n) EmptyString).
  rewrite (styles_of_core_roman_single up _ d Hr).
  destruct (alpha_roman_digit up n) eqn:Hr0; unfold alpha_roman_digit in Hr0.
  - rewrite (styles_of_core_roman_single up _ d Hr0).
    cbn [map forallb fst existsb].
    rewrite !lstyle_eqb_refl, ?orb_true_r, ?andb_true_r. reflexivity.
  - rewrite (styles_of_core_alpha up _ d Hc0 Hr0).
    cbn [map forallb fst existsb].
    rewrite lstyle_eqb_refl, ?orb_true_r, ?andb_true_r. reflexivity.
Qed.

Local Lemma alpha_narrow_by :
  forall (up : bool) d n m, 1 <= n -> n <= Alpha.upper -> 1 <= m -> m <= Alpha.upper ->
    alpha_roman_digit up m = false ->
    narrow (mk_styles (nsc_marker (Alpha.str up) d n))
           (mk_sty (nsc_marker (Alpha.str up) d m))
    = [(SOrd (alpha_sty up) d, n)].
Proof.
  intros up d n m H1 H2 Hm1 Hm2 Hnr. unfold alpha_roman_digit in Hnr.
  assert (Hc1 : (if up then is_upper else is_lower) (alpha_char up m) = true).
  { pose proof (Alpha.str_alphabet up m Hm1 Hm2) as H.
    unfold Alpha.str, alpha_char in *. cbn [str_forallb] in H.
    apply andb_true_iff in H as [H _]. exact H. }
  assert (Hc0 : (if up then is_upper else is_lower) (alpha_char up n) = true).
  { pose proof (Alpha.str_alphabet up n H1 H2) as H.
    unfold Alpha.str, alpha_char in *. cbn [str_forallb] in H.
    apply andb_true_iff in H as [H _]. exact H. }
  assert (Hval : Alpha.value up (Alpha.str up n) = n)
    by (apply Alpha.value_str; [lia|lia]).
  cbn [mk_sty nsc_marker]. unfold Alpha.str at 2.
  fold (alpha_char up m).
  rewrite (styles_of_core_alpha up _ d Hc1 Hnr).
  unfold mk_styles, with_starts. cbn [mk_sty mk_core nsc_marker].
  change (Alpha.str up n) with (String (alpha_char up n) EmptyString).
  assert (Hdiff : lstyle_eqb (SOrd (roman_sty up) d) (SOrd (alpha_sty up) d) = false)
    by (unfold roman_sty, alpha_sty; destruct up; reflexivity).
  destruct ((if up then is_roman_up else is_roman_lo) (alpha_char up n)) eqn:Hr0.
  - (* this letter is also a roman digit: two candidates, alpha second *)
    rewrite (styles_of_core_roman_single up _ d Hr0).
    cbn [map narrow filter fst existsb].
    rewrite Hdiff, lstyle_eqb_refl. cbn [orb].
    f_equal; f_equal; unfold alpha_sty, alpha_char in *;
      destruct up; cbn [style_start Alpha.value]; exact Hval.
  - (* it names alpha alone *)
    rewrite (styles_of_core_alpha up _ d Hc0 Hr0).
    cbn [map narrow filter fst existsb].
    rewrite lstyle_eqb_refl. cbn [orb].
    f_equal; f_equal; unfold alpha_sty, alpha_char in *;
      destruct up; cbn [style_start Alpha.value]; exact Hval.
Qed.

(* Uniformity for an alpha ordered list.  Same shape; the condition on
   the first marker is that its letter is not a roman digit, and the
   range condition is where the wrap past `z` is excluded. *)
Theorem ordered_alpha_uniformity :
  forall (up : bool) d start sp lss,
    lss <> [] ->
    1 <= start -> start + length lss <= S Alpha.upper ->
    (if up then is_roman_up else is_roman_lo)
      (ascii_of_nat ((if up then 64 else 96) + start)) = false ->
    forallb (item_ok (nsc_marker (Alpha.str up) d start)) lss = true ->
    parse_lines (list_lines sp (map litem_lines (nsc_items (Alpha.str up) d start lss)))
                (PPara [])
    = [mk (OrderedList (OLAttrs (alpha_sty up) d start) (list_spacing_of sp lss)
             (map (fun L => parse_lines L (PPara [])) lss))].
Proof.
  intros up d start sp lss Hne H1 H2 Hnr Hok.
  assert (Hl : 1 <= length lss) by (destruct lss; [congruence|cbn [length]; lia]).
  assert (Hsty : mk_styles (nsc_marker (Alpha.str up) d start)
                 = [(SOrd (alpha_sty up) d, start)])
    by (apply alpha_marker_styles; [lia|lia|exact Hnr]).
  assert (Hio : items_ok (nsc_marker (Alpha.str up) d start)
                  (nsc_items (Alpha.str up) d start lss) = true).
  { apply (items_ok_nsc_run (Alpha.str up) d (mk_styles (nsc_marker (Alpha.str up) d start))
             (nsc_marker (Alpha.str up) d start) lss start).
    - intros k Hk.
      destruct (alpha_item_facts up d (start + k) ltac:(lia) ltac:(lia)) as (A & B & C).
      split; [exact A|]. split; [|exact C].
      unfold admits_styles. rewrite Hsty. cbn [forallb fst].
      rewrite B. reflexivity.
    - exact (proj2 (proj2 (alpha_item_facts up d start ltac:(lia) ltac:(lia)))).
    - exact Hok. }
  exact (nsc_uniformity (alpha_sty up) (Alpha.str up) d start sp lss Hne
           (alpha_marker_ok up d start ltac:(lia) ltac:(lia) Hnr) Hsty Hio).
Qed.

Theorem ordered_alpha_uniformity_tail :
  forall (up : bool) d start sp lss next tl,
    lss <> [] ->
    1 <= start -> start + length lss <= S Alpha.upper ->
    (if up then is_roman_up else is_roman_lo)
      (ascii_of_nat ((if up then 64 else 96) + start)) = false ->
    forallb (item_ok (nsc_marker (Alpha.str up) d start)) lss = true ->
    classify next <> KBlank ->
    (forall a b c d, classify next <> KList a b c d) ->
    indent_of next = 0 ->
    parse_lines (list_lines sp (map litem_lines (nsc_items (Alpha.str up) d start lss))
                 ++ EmptyString :: next :: tl)%list (PPara [])
    = mk (OrderedList (OLAttrs (alpha_sty up) d start) (list_spacing_of sp lss)
             (map (fun L => parse_lines L (PPara [])) lss))
      :: parse_lines (next :: tl) (PPara []).
Proof.
  intros up d start sp lss next tl Hne H1 H2 Hnr Hok Hnb Hnl Hindent.
  assert (Hl : 1 <= length lss) by (destruct lss; [congruence|cbn [length]; lia]).
  assert (Hsty : mk_styles (nsc_marker (Alpha.str up) d start)
                 = [(SOrd (alpha_sty up) d, start)])
    by (apply alpha_marker_styles; [lia|lia|exact Hnr]).
  assert (Hio : items_ok (nsc_marker (Alpha.str up) d start)
                  (nsc_items (Alpha.str up) d start lss) = true).
  { apply (items_ok_nsc_run (Alpha.str up) d (mk_styles (nsc_marker (Alpha.str up) d start))
             (nsc_marker (Alpha.str up) d start) lss start).
    - intros k Hk.
      destruct (alpha_item_facts up d (start + k) ltac:(lia) ltac:(lia)) as (A & B & C).
      split; [exact A|]. split; [|exact C].
      unfold admits_styles. rewrite Hsty. cbn [forallb fst].
      rewrite B. reflexivity.
    - exact (proj2 (proj2 (alpha_item_facts up d start ltac:(lia) ltac:(lia)))).
    - exact Hok. }
  exact (nsc_uniformity_tail (alpha_sty up) (Alpha.str up) d start sp lss next tl Hne
           (alpha_marker_ok up d start ltac:(lia) ltac:(lia) Hnr) Hsty Hio
           Hnb Hnl Hindent).
Qed.

(* Alpha at any start the second letter can resolve.  The disjunction is
   the condition: either the opener already names alpha alone, or the
   list has a second item whose letter is not a roman digit. *)
Theorem ordered_alpha_uniformity_any :
  forall (up : bool) d start sp lss,
    lss <> [] -> 1 <= start -> start + length lss <= S Alpha.upper ->
    (alpha_roman_digit up start = false
     \/ (2 <= length lss /\ alpha_roman_digit up (S start) = false)
     \/ (3 <= length lss /\ alpha_roman_digit up (S start) = true
         /\ alpha_roman_digit up (S (S start)) = false)) ->
    forallb (item_ok (nsc_marker (Alpha.str up) d start)) lss = true ->
    parse_lines (list_lines sp (map litem_lines (nsc_items (Alpha.str up) d start lss)))
                (PPara [])
    = [mk (OrderedList (OLAttrs (alpha_sty up) d start) (list_spacing_of sp lss)
             (map (fun L => parse_lines L (PPara [])) lss))].
Proof.
  intros up d start sp lss Hne H1 H2 Hcond Hok.
  destruct Hcond as [Hnr | [[Hlen Hnr] | [Hlen3 [Hd1 Hnr]]]].
  - unfold alpha_char in Hnr.
    exact (ordered_alpha_uniformity up d start sp lss Hne H1 H2 Hnr Hok).
  - destruct lss as [|L0 [|L1 rest]];
      [congruence | cbn [length] in Hlen; lia | ].
    cbn [length] in H2, Hlen.
    destruct (alpha_item_facts up d start ltac:(lia) ltac:(lia))
      as (Hmk0 & Hmem0 & Hth0).
    destruct (alpha_item_facts up d (S start) ltac:(lia) ltac:(lia))
      as (Hmk1 & Hmem1 & Hth1).
    cbn [forallb] in Hok. apply andb_true_iff in Hok as [HL0 Hok'].
    pose proof Hok' as Hok''. apply andb_true_iff in Hok'' as [HL1 Hrest].
    destruct L1 as [|l1 more1]; [cbn [item_ok] in HL1; discriminate|].
    assert (HS : narrow (mk_styles (nsc_marker (Alpha.str up) d start))
                        (mk_sty (nsc_marker (Alpha.str up) d (S start)))
                 = [(SOrd (alpha_sty up) d, start)])
      by (apply (alpha_narrow_by up d start (S start)); [lia|lia|lia|lia|exact Hnr]).
    assert (Hitems : items_ok_at [(SOrd (alpha_sty up) d, start)]
                       (nsc_items (Alpha.str up) d (S (S start)) rest) = true).
    { apply (items_ok_nsc_run (Alpha.str up) d [(SOrd (alpha_sty up) d, start)]
               (nsc_marker (Alpha.str up) d start) rest (S (S start))).
      - intros k Hk.
        destruct (alpha_item_facts up d (S (S start) + k) ltac:(lia) ltac:(lia))
          as (A & B & C).
        split; [exact A|]. split; [|exact C].
        unfold admits_styles. cbn [forallb fst]. rewrite B. reflexivity.
      - exact Hth0.
      - exact Hrest. }
    cbn [nsc_items].
    rewrite (list_uniformity_narrow (nsc_marker (Alpha.str up) d start)
               (nsc_marker (Alpha.str up) d (S start))
               [(SOrd (alpha_sty up) d, start)] sp L0 (l1 :: more1)
               (nsc_items (Alpha.str up) d (S (S start)) rest)
               Hmk0 Hmk1 eq_refl eq_refl ltac:(discriminate) HS HL0
               (ltac:(rewrite (item_ok_thematic_indep _ _ (l1 :: more1) Hth1 Hth0);
                      exact HL1))
               ltac:(discriminate) Hitems).
    cbn [styles_list_checked styles_list map snd].
    rewrite map_snd_nsc_items, map_parse_nsc_items.
    reflexivity.
  - (* the opener and the second marker are both roman digits; the third
       letter is what resolves it, so the set is peeled twice *)
    destruct lss as [|L0 [|L1 [|L2 rest]]];
      [ congruence | cbn [length] in Hlen3; lia | cbn [length] in Hlen3; lia | ].
    cbn [length] in H2, Hlen3.
    destruct (alpha_item_facts up d start ltac:(lia) ltac:(lia))
      as (Hmk0 & _ & Hth0).
    destruct (alpha_item_facts up d (S start) ltac:(lia) ltac:(lia))
      as (Hmk1 & _ & Hth1).
    destruct (alpha_item_facts up d (S (S start)) ltac:(lia) ltac:(lia))
      as (Hmk2 & _ & Hth2).
    cbn [forallb] in Hok. apply andb_true_iff in Hok as [HL0 Hok1].
    apply andb_true_iff in Hok1 as [HL1 Hok2].
    apply andb_true_iff in Hok2 as [HL2 Hrest].
    destruct L1 as [|l1 more1]; [cbn [item_ok] in HL1; discriminate|].
    destruct L2 as [|l2 more2]; [cbn [item_ok] in HL2; discriminate|].
    assert (HS1 : narrow (mk_styles (nsc_marker (Alpha.str up) d start))
                         (mk_sty (nsc_marker (Alpha.str up) d (S start)))
                  = mk_styles (nsc_marker (Alpha.str up) d start))
      by (apply alpha_narrow_id; [lia|lia|lia|lia|exact Hd1]).
    assert (HS2 : narrow (mk_styles (nsc_marker (Alpha.str up) d start))
                         (mk_sty (nsc_marker (Alpha.str up) d (S (S start))))
                  = [(SOrd (alpha_sty up) d, start)])
      by (apply alpha_narrow_by; [lia|lia|lia|lia|exact Hnr]).
    assert (Hitems : items_ok_at [(SOrd (alpha_sty up) d, start)]
                       (nsc_items (Alpha.str up) d (S (S (S start))) rest) = true).
    { apply (items_ok_nsc_run (Alpha.str up) d [(SOrd (alpha_sty up) d, start)]
               (nsc_marker (Alpha.str up) d start) rest (S (S (S start)))).
      - intros k Hk.
        destruct (alpha_item_facts up d (S (S (S start)) + k) ltac:(lia) ltac:(lia))
          as (A & B & C).
        split; [exact A|]. split; [|exact C].
        unfold admits_styles. cbn [forallb fst]. rewrite B. reflexivity.
      - exact Hth0.
      - exact Hrest. }
    cbn [nsc_items].
    rewrite (list_uniformity_narrow2 (nsc_marker (Alpha.str up) d start)
               (nsc_marker (Alpha.str up) d (S start))
               (nsc_marker (Alpha.str up) d (S (S start)))
               (mk_styles (nsc_marker (Alpha.str up) d start))
               [(SOrd (alpha_sty up) d, start)] sp L0 (l1 :: more1) (l2 :: more2)
               (nsc_items (Alpha.str up) d (S (S (S start))) rest)
               Hmk0 Hmk1 Hmk2 eq_refl eq_refl eq_refl
               (mk_styles_nonempty _ Hmk0) ltac:(discriminate)
               HS1 HS2 HL0
               (ltac:(rewrite (item_ok_thematic_indep _ _ (l1 :: more1) Hth1 Hth0);
                      exact HL1)) ltac:(discriminate)
               (ltac:(rewrite (item_ok_thematic_indep _ _ (l2 :: more2) Hth2 Hth0);
                      exact HL2)) ltac:(discriminate)
               Hitems).
    cbn [styles_list_checked styles_list map snd].
    rewrite map_snd_nsc_items, map_parse_nsc_items.
    reflexivity.
Qed.

(* The same with the list closed by a following line. *)
Theorem ordered_alpha_uniformity_any_tail :
  forall (up : bool) d start sp lss next tl,
    lss <> [] -> 1 <= start -> start + length lss <= S Alpha.upper ->
    (alpha_roman_digit up start = false
     \/ (2 <= length lss /\ alpha_roman_digit up (S start) = false)
     \/ (3 <= length lss /\ alpha_roman_digit up (S start) = true
         /\ alpha_roman_digit up (S (S start)) = false)) ->
    forallb (item_ok (nsc_marker (Alpha.str up) d start)) lss = true ->
    classify next <> KBlank ->
    (forall a b c d, classify next <> KList a b c d) ->
    indent_of next = 0 ->
    parse_lines (list_lines sp (map litem_lines (nsc_items (Alpha.str up) d start lss))
                 ++ EmptyString :: next :: tl)%list (PPara [])
    = mk (OrderedList (OLAttrs (alpha_sty up) d start) (list_spacing_of sp lss)
             (map (fun L => parse_lines L (PPara [])) lss))
      :: parse_lines (next :: tl) (PPara []).
Proof.
  intros up d start sp lss next tl Hne H1 H2 Hcond Hok Hnb Hnl Hindent.
  destruct Hcond as [Hnr | [[Hlen Hnr] | [Hlen3 [Hd1 Hnr]]]].
  - unfold alpha_char in Hnr.
    exact (ordered_alpha_uniformity_tail up d start sp lss next tl
             Hne H1 H2 Hnr Hok Hnb Hnl Hindent).
  - destruct lss as [|L0 [|L1 rest]];
      [congruence | cbn [length] in Hlen; lia | ].
    cbn [length] in H2, Hlen.
    destruct (alpha_item_facts up d start ltac:(lia) ltac:(lia))
      as (Hmk0 & Hmem0 & Hth0).
    destruct (alpha_item_facts up d (S start) ltac:(lia) ltac:(lia))
      as (Hmk1 & Hmem1 & Hth1).
    cbn [forallb] in Hok. apply andb_true_iff in Hok as [HL0 Hok'].
    pose proof Hok' as Hok''. apply andb_true_iff in Hok'' as [HL1 Hrest].
    destruct L1 as [|l1 more1]; [cbn [item_ok] in HL1; discriminate|].
    assert (HS : narrow (mk_styles (nsc_marker (Alpha.str up) d start))
                        (mk_sty (nsc_marker (Alpha.str up) d (S start)))
                 = [(SOrd (alpha_sty up) d, start)])
      by (apply (alpha_narrow_by up d start (S start)); [lia|lia|lia|lia|exact Hnr]).
    assert (Hitems : items_ok_at [(SOrd (alpha_sty up) d, start)]
                       (nsc_items (Alpha.str up) d (S (S start)) rest) = true).
    { apply (items_ok_nsc_run (Alpha.str up) d [(SOrd (alpha_sty up) d, start)]
               (nsc_marker (Alpha.str up) d start) rest (S (S start))).
      - intros k Hk.
        destruct (alpha_item_facts up d (S (S start) + k) ltac:(lia) ltac:(lia))
          as (A & B & C).
        split; [exact A|]. split; [|exact C].
        unfold admits_styles. cbn [forallb fst]. rewrite B. reflexivity.
      - exact Hth0.
      - exact Hrest. }
    cbn [nsc_items].
    rewrite (list_uniformity_narrow_tail (nsc_marker (Alpha.str up) d start)
               (nsc_marker (Alpha.str up) d (S start))
               [(SOrd (alpha_sty up) d, start)] sp L0 (l1 :: more1)
               (nsc_items (Alpha.str up) d (S (S start)) rest) next tl
               Hmk0 Hmk1 eq_refl eq_refl ltac:(discriminate) HS HL0
               (ltac:(rewrite (item_ok_thematic_indep _ _ (l1 :: more1) Hth1 Hth0);
                      exact HL1))
               ltac:(discriminate) Hitems Hnb Hnl Hindent).
    cbn [styles_list_checked styles_list map snd].
    rewrite map_snd_nsc_items, map_parse_nsc_items.
    reflexivity.
  - (* the opener and the second marker are both roman digits; the third
       letter is what resolves it, so the set is peeled twice *)
    destruct lss as [|L0 [|L1 [|L2 rest]]];
      [ congruence | cbn [length] in Hlen3; lia | cbn [length] in Hlen3; lia | ].
    cbn [length] in H2, Hlen3.
    destruct (alpha_item_facts up d start ltac:(lia) ltac:(lia))
      as (Hmk0 & _ & Hth0).
    destruct (alpha_item_facts up d (S start) ltac:(lia) ltac:(lia))
      as (Hmk1 & _ & Hth1).
    destruct (alpha_item_facts up d (S (S start)) ltac:(lia) ltac:(lia))
      as (Hmk2 & _ & Hth2).
    cbn [forallb] in Hok. apply andb_true_iff in Hok as [HL0 Hok1].
    apply andb_true_iff in Hok1 as [HL1 Hok2].
    apply andb_true_iff in Hok2 as [HL2 Hrest].
    destruct L1 as [|l1 more1]; [cbn [item_ok] in HL1; discriminate|].
    destruct L2 as [|l2 more2]; [cbn [item_ok] in HL2; discriminate|].
    assert (HS1 : narrow (mk_styles (nsc_marker (Alpha.str up) d start))
                         (mk_sty (nsc_marker (Alpha.str up) d (S start)))
                  = mk_styles (nsc_marker (Alpha.str up) d start))
      by (apply alpha_narrow_id; [lia|lia|lia|lia|exact Hd1]).
    assert (HS2 : narrow (mk_styles (nsc_marker (Alpha.str up) d start))
                         (mk_sty (nsc_marker (Alpha.str up) d (S (S start))))
                  = [(SOrd (alpha_sty up) d, start)])
      by (apply alpha_narrow_by; [lia|lia|lia|lia|exact Hnr]).
    assert (Hitems : items_ok_at [(SOrd (alpha_sty up) d, start)]
                       (nsc_items (Alpha.str up) d (S (S (S start))) rest) = true).
    { apply (items_ok_nsc_run (Alpha.str up) d [(SOrd (alpha_sty up) d, start)]
               (nsc_marker (Alpha.str up) d start) rest (S (S (S start)))).
      - intros k Hk.
        destruct (alpha_item_facts up d (S (S (S start)) + k) ltac:(lia) ltac:(lia))
          as (A & B & C).
        split; [exact A|]. split; [|exact C].
        unfold admits_styles. cbn [forallb fst]. rewrite B. reflexivity.
      - exact Hth0.
      - exact Hrest. }
    cbn [nsc_items].
    rewrite (list_uniformity_narrow2_tail (nsc_marker (Alpha.str up) d start)
               (nsc_marker (Alpha.str up) d (S start))
               (nsc_marker (Alpha.str up) d (S (S start)))
               (mk_styles (nsc_marker (Alpha.str up) d start))
               [(SOrd (alpha_sty up) d, start)] sp L0 (l1 :: more1) (l2 :: more2)
               (nsc_items (Alpha.str up) d (S (S (S start))) rest) next tl
               Hmk0 Hmk1 Hmk2 eq_refl eq_refl eq_refl
               (mk_styles_nonempty _ Hmk0) ltac:(discriminate)
               HS1 HS2 HL0
               (ltac:(rewrite (item_ok_thematic_indep _ _ (l1 :: more1) Hth1 Hth0);
                      exact HL1)) ltac:(discriminate)
               (ltac:(rewrite (item_ok_thematic_indep _ _ (l2 :: more2) Hth2 Hth0);
                      exact HL2)) ltac:(discriminate)
               Hitems Hnb Hnl Hindent).
    cbn [styles_list_checked styles_list map snd].
    rewrite map_snd_nsc_items, map_parse_nsc_items.
    reflexivity.
Qed.


(*
The list flavours the canonical rendering produces
--------------------------------------------------

A canonical list is a bullet list or an ordered list under one of the
three numbering schemes.  They differ only in the markers their items
carry, so naming that difference once lets the roundtrip keep a single
list case.  `ck_items` says which markers the items get, `ck_first`
names the marker `item_ok` is asked for, `ck_block` the block the list
closes to, and `ck_uniformity` is the one theorem the block layer
consumes.

`ck_ok` is the fourth piece, because the ordered kinds carry a condition
bullets do not.  It takes the item count as well as the kind: the range
has to cover the whole run, which is where the alpha wrap past `z` and a
decimal numeral past `dec_digits_max` digits are excluded.  Bullet
answers `true` unconditionally.
*)

Inductive list_kind : Type :=
  | LKBullet
  (* A definition list is a bullet list whose marker is `:`; the four
     pieces below differ from `LKBullet`'s only in `ck_block`, which is
     where the term split happens. *)
  | LKDef
  | LKTask (checks : list task_status)
  | LKDecimal (d : ordered_list_delim) (start : nat)
  | LKRoman (up : bool) (d : ordered_list_delim) (start : nat)
  | LKAlpha (up : bool) (d : ordered_list_delim) (start : nat).

Definition ck_first (k : list_kind) : marker :=
  match k with
  | LKBullet => bullet
  | LKDef => colon
  | LKTask checks => MTask "-" (hd Incomplete checks)
  | LKDecimal d start => dec_marker d start
  | LKRoman up d start => nsc_marker (Roman.str up) d start
  | LKAlpha up d start => nsc_marker (Alpha.str up) d start
  end.

Fixpoint task_ck_items (checks : list task_status) (lss : list (list string))
  : list litem :=
  match lss with
  | [] => []
  | L :: rest =>
      match checks with
      | [] => (MTask "-" Incomplete, L) :: task_ck_items [] rest
      | c :: cs => (MTask "-" c, L) :: task_ck_items cs rest
      end
  end.

Definition ck_items (k : list_kind) (lss : list (list string)) : list litem :=
  match k with
  | LKBullet => same_marker bullet lss
  | LKDef => same_marker colon lss
  | LKTask checks => task_ck_items checks lss
  | LKDecimal d start => dec_items d start lss
  | LKRoman up d start => nsc_items (Roman.str up) d start lss
  | LKAlpha up d start => nsc_items (Alpha.str up) d start lss
  end.

Definition ck_block (k : list_kind) (sp : list_spacing) (items : list blocks)
  : block :=
  match k with
  | LKBullet => BulletList sp items
  | LKDef => DefinitionList sp (def_items items)
  | LKTask checks => TaskList sp (task_items checks items)
  | LKDecimal d start => OrderedList (OLAttrs Decimal d start) sp items
  | LKRoman up d start => OrderedList (OLAttrs (roman_sty up) d start) sp items
  | LKAlpha up d start => OrderedList (OLAttrs (alpha_sty up) d start) sp items
  end.

(* The side condition, at a list of `n` items. *)
Definition ck_ok (k : list_kind) (n : nat) : bool :=
  match k with
  | LKBullet => true
  (* The colon marker is canonical at every setting; what needs the
     capability is the term split, which is the only thing `ck_block`
     does with it. *)
  | LKDef => (@bdeflists K)
  | LKTask checks => (@btasks K) && Nat.eqb (length checks) n
  | LKDecimal _ start => dec_fits (start + n - 1)
  (* No ambiguity condition: a roman numeral's set has roman at its head
     whatever its length, and a second item narrows it to the singleton
     (`roman_narrow_singleton`).  Only the range is needed. *)
  | LKRoman up d start =>
      (Nat.leb 1 start && Nat.leb (start + n) (S Roman.upper))%bool
  (* Either the opener already names alpha alone, or there is a second
     item whose letter is not a roman digit to resolve it, or -- when the
     second is a roman digit too, which happens only at 3 and 12 -- a
     third.  Three disjuncts is all it takes: the roman digits are
     c d i l m v x, whose only consecutive runs are (3,4) and (12,13),
     never three, so no start needs a fourth marker to settle. *)
  | LKAlpha up d start =>
      (Nat.leb 1 start && Nat.leb (start + n) (S Alpha.upper)
       && (negb (alpha_roman_digit up start)
           || (Nat.leb 2 n && negb (alpha_roman_digit up (S start)))
           || (Nat.leb 3 n && alpha_roman_digit up (S start)
               && negb (alpha_roman_digit up (S (S start))))))%bool
  end.

Local Lemma task_ck_items_lines :
  forall checks lss, map snd (task_ck_items checks lss) = lss.
Proof.
  intros checks lss. induction lss as [|L rest IH] in checks |- *;
    [reflexivity|]. destruct checks; cbn [task_ck_items map snd];
    rewrite IH; reflexivity.
Qed.

Lemma ck_items_lines :
  forall k lss, map snd (ck_items k lss) = lss.
Proof.
  intros [| |checks|d start|up d start|up d start] lss;
    [apply map_snd_same_marker | apply map_snd_same_marker
    | apply task_ck_items_lines
    | apply map_snd_dec_items
    | apply map_snd_nsc_items | apply map_snd_nsc_items].
Qed.

Local Lemma task_ck_items_checks :
  forall checks lss,
    length checks = length lss ->
    map (fun it => mk_check (fst it)) (task_ck_items checks lss) = checks.
Proof.
  induction checks as [|c checks IH]; intros [|L rest] H; try discriminate;
    [reflexivity|].
  cbn [task_ck_items map fst mk_check length] in H |- *.
  f_equal. apply IH. injection H. trivial.
Qed.

Local Lemma map_parse_task_ck_items :
  forall checks lss,
    map (fun it => parse_lines (snd it) (PPara []))
      (task_ck_items checks lss) =
    map (fun L => parse_lines L (PPara [])) lss.
Proof.
  intros checks lss. induction lss as [|L rest IH] in checks |- *;
    [reflexivity|]. destruct checks; cbn [task_ck_items map fst snd];
    rewrite IH; reflexivity.
Qed.

Local Lemma task_marker_thematic :
  forall chk l, is_thematic (mk_open (MTask "-" chk) ++ l) = false.
Proof. intros [] l; reflexivity. Qed.

Local Lemma item_ok_task_status :
  forall a b L, item_ok (MTask "-" a) L = item_ok (MTask "-" b) L.
Proof. intros [] [] [|l more]; reflexivity. Qed.

Local Lemma task_ck_items_ok :
  forall checks lss,
    (@btasks K) = true ->
    length checks = length lss ->
    forallb (item_ok (MTask "-" (hd Incomplete checks))) lss = true ->
    items_ok (MTask "-" (hd Incomplete checks))
      (task_ck_items checks lss) = true.
Proof.
  intros checks lss Htasks Hlen Hok.
  assert (Hbullet : is_task_bullet "-" = true) by reflexivity.
  assert (Had : forall st,
      admits_styles [(STask "-", 1)] (MTask "-" st) = true)
    by (intros []; reflexivity).
  destruct checks as [|c checks]; destruct lss as [|L rest]; try discriminate;
    [reflexivity|].
  cbn [length] in Hlen. injection Hlen as Hlen.
  cbn [forallb] in Hok. apply andb_true_iff in Hok as [HL Hrest].
  cbn [hd] in HL, Hrest.
  unfold items_ok, items_ok_at. cbn [task_ck_items forallb fst snd hd].
  rewrite HL, Htasks.
  cbn [marker_ok marker_tasks_ok mk_sty mk_styles with_starts mk_core style_start
                    admits_styles narrow lstyle_eqb].
  assert (Htail : items_ok_at [(STask "-"%char, 1)]
                    (task_ck_items checks rest) = true).
  { clear HL. revert rest Hlen Hrest.
    induction checks as [|c' checks IH]; intros [|L' rest] Hlen Hrest;
      try discriminate; [reflexivity|].
    cbn [length] in Hlen. injection Hlen as Hlen.
    cbn [forallb] in Hrest. apply andb_true_iff in Hrest as [HL' Hrest].
    unfold items_ok_at.
    cbn [task_ck_items forallb fst snd marker_ok]. rewrite Htasks, Hbullet.
    rewrite (item_ok_task_status c' c L'), HL'.
    rewrite Had.
    cbn [marker_tasks_ok
         mk_sty mk_styles with_starts mk_core style_start
         admits_styles lstyle_eqb andb].
    specialize (IH rest Hlen Hrest). unfold items_ok_at in IH.
    rewrite Htasks in IH. exact IH. }
  rewrite Hbullet, Had. cbn [andb].
  unfold items_ok_at in Htail. rewrite Htasks in Htail. exact Htail.
Qed.

Local Lemma nsc_items_markers_ok :
  forall core d n lss,
    (forall k, k < length lss -> marker_ok (nsc_marker core d (n + k)) = true) ->
    forallb (fun it => marker_ok (fst it)) (nsc_items core d n lss) = true.
Proof.
  intros core d n lss. revert n.
  induction lss as [|L rest IH]; intros n H; [reflexivity|].
  cbn [nsc_items forallb fst].
  pose proof (H 0 ltac:(cbn [length]; lia)) as H0. rewrite Nat.add_0_r in H0.
  rewrite H0. cbn [andb]. apply IH.
  intros k Hk. pose proof (H (S k) ltac:(cbn [length]; lia)) as Hs.
  rewrite <- Nat.add_succ_comm in Hs. exact Hs.
Qed.

Lemma ck_items_markers_ok :
  forall k lss, ck_ok k (length lss) = true ->
    forallb (fun it => marker_ok (fst it)) (ck_items k lss) = true.
Proof.
  intros [| |checks|d start|up d start|up d start] lss Hck.
  - clear Hck. unfold ck_items, same_marker.
    induction lss as [|L rest IH]; [reflexivity|].
    cbn [map forallb fst]. rewrite bullet_ok. exact IH.
  - clear Hck. unfold ck_items, same_marker.
    induction lss as [|L rest IH]; [reflexivity|].
    cbn [map forallb fst]. rewrite colon_ok. exact IH.
  - clear Hck. cbn [ck_items].
    induction lss as [|L rest IH] in checks |- *; [reflexivity|].
    destruct checks; cbn [task_ck_items forallb fst marker_ok];
      rewrite IH; reflexivity.
  - cbn [ck_ok ck_items] in *. revert start Hck.
    induction lss as [|L rest IH]; intros start Hck; [reflexivity|].
    cbn [length] in Hck.
    cbn [dec_items forallb fst].
    rewrite (dec_marker_ok d start
               (dec_fits_le start (start + S (length rest) - 1) ltac:(lia) Hck)).
    apply IH. replace (S start + length rest - 1)
      with (start + S (length rest) - 1) by lia. exact Hck.
  - cbn [ck_ok] in Hck.
    apply andb_true_iff in Hck as [Hs Hr].
    apply Nat.leb_le in Hs. apply Nat.leb_le in Hr.
    cbn [ck_items]. apply nsc_items_markers_ok. intros k Hk.
    exact (proj1 (roman_item_facts up d (start + k) ltac:(lia) ltac:(lia))).
  - cbn [ck_ok] in Hck.
    apply andb_true_iff in Hck as [Hck Hnr].
    apply andb_true_iff in Hck as [Hs Hr].
    apply Nat.leb_le in Hs. apply Nat.leb_le in Hr.
    cbn [ck_items]. apply nsc_items_markers_ok. intros k Hk.
    exact (proj1 (alpha_item_facts up d (start + k) ltac:(lia) ltac:(lia))).
Qed.

Lemma ck_lines_nonempty :
  forall k lss, lss <> [] -> map litem_lines (ck_items k lss) <> [].
Proof.
  intros k lss H Hnil. apply H. rewrite <- (ck_items_lines k lss).
  destruct (ck_items k lss); [reflexivity | discriminate Hnil].
Qed.

Local Lemma task_uniformity :
  forall checks sp lss,
    (@btasks K) = true -> lss <> [] -> length checks = length lss ->
    forallb (item_ok (MTask "-" (hd Incomplete checks))) lss = true ->
    parse_lines (list_lines sp (map litem_lines (task_ck_items checks lss)))
      (PPara []) =
    [mk (TaskList (list_spacing_of sp lss)
           (task_items checks
             (map (fun L => parse_lines L (PPara [])) lss)))].
Proof.
  intros checks sp lss Htasks Hne Hlen Hok.
  destruct checks as [|c checks]; destruct lss as [|L0 rest]; try contradiction;
    try discriminate.
  cbn [length] in Hlen. injection Hlen as Hlen.
  pose proof (task_ck_items_ok (c :: checks) (L0 :: rest) Htasks
                ltac:(cbn [length]; congruence) Hok) as Hio.
  cbn [task_ck_items] in Hio |- *.
  rewrite (list_uniformity (MTask "-" c) sp L0
             (task_ck_items checks rest) eq_refl Hio).
  unfold marker_list_checked, styles_list_checked, mk_styles, with_starts,
    mk_sty, mk_core, style_start. cbn [map fst snd mk_check].
  rewrite (task_ck_items_checks checks rest Hlen), task_ck_items_lines.
  rewrite map_parse_task_ck_items.
  reflexivity.
Qed.

Local Lemma task_uniformity_tail :
  forall checks sp lss next tail,
    (@btasks K) = true -> lss <> [] -> length checks = length lss ->
    forallb (item_ok (MTask "-" (hd Incomplete checks))) lss = true ->
    classify next <> KBlank ->
    (forall a b c d, classify next <> KList a b c d) ->
    indent_of next = 0 ->
    parse_lines
      (list_lines sp (map litem_lines (task_ck_items checks lss))
       ++ EmptyString :: next :: tail)%list (PPara []) =
    mk (TaskList (list_spacing_of sp lss)
          (task_items checks (map (fun L => parse_lines L (PPara [])) lss)))
    :: parse_lines (next :: tail) (PPara []).
Proof.
  intros checks sp lss next tail Htasks Hne Hlen Hok Hnb Hnl Hindent.
  destruct checks as [|c checks]; destruct lss as [|L0 rest]; try contradiction;
    try discriminate.
  cbn [length] in Hlen. injection Hlen as Hlen.
  pose proof (task_ck_items_ok (c :: checks) (L0 :: rest)
                Htasks ltac:(cbn [length]; congruence) Hok) as Hio.
  cbn [task_ck_items] in Hio |- *.
  rewrite (list_uniformity_tail (MTask "-" c) sp L0
             (task_ck_items checks rest) next tail eq_refl Hio Hnb Hnl Hindent).
  unfold marker_list_checked, styles_list_checked, mk_styles, with_starts,
    mk_sty, mk_core, style_start. cbn [map fst snd mk_check].
  rewrite (task_ck_items_checks checks rest Hlen), task_ck_items_lines.
  rewrite map_parse_task_ck_items.
  reflexivity.
Qed.

(** Uniformity at every flavour: the rendering of a list whose items are
    `lss` parses back to the list its kind names, with the items' lines
    parsed at top level and the spacing read off those same lines. *)
Theorem ck_uniformity :
  forall k sp lss,
    lss <> [] ->
    ck_ok k (length lss) = true ->
    forallb (item_ok (ck_first k)) lss = true ->
    parse_lines (list_lines sp (map litem_lines (ck_items k lss))) (PPara [])
    = [mk (ck_block k (list_spacing_of sp lss)
             (map (fun L => parse_lines L (PPara [])) lss))].
Proof.
  intros [| |checks|d start|up d start|up d start] sp lss Hne Hck Hok.
  - cbn [ck_items ck_block ck_first] in Hok |- *.
    rewrite map_litem_lines_same_marker.
    exact (list_uniformity_same bullet sp lss bullet_ok eq_refl Hne Hok).
  (* The colon reaches the same generic theorem; `marker_list colon` is
     the `DefinitionList` arm of `styles_list` once the capability is
     known on, which is what `ck_ok LKDef` says, so `ck_block LKDef`
     needs no separate step. *)
  - cbn [ck_items ck_block ck_first] in Hok |- *.
    rewrite map_litem_lines_same_marker.
    cbn [ck_ok] in Hck.
    rewrite <- (marker_list_checked_colon _
                  (map (fun _ => mk_check colon) lss) _ Hck).
    exact (list_uniformity_same colon sp lss colon_ok eq_refl Hne Hok).
  - cbn [ck_ok] in Hck. apply andb_true_iff in Hck as [Htasks Hck].
    apply Nat.eqb_eq in Hck.
    exact (task_uniformity checks sp lss Htasks Hne Hck Hok).
  - exact (ordered_decimal_uniformity d start sp lss Hne Hck Hok).
  - cbn [ck_ok] in Hck.
    apply andb_true_iff in Hck as [Hs Hr].
    apply Nat.leb_le in Hs. apply Nat.leb_le in Hr.
    exact (ordered_roman_uniformity_any up d start sp lss Hne Hs Hr Hok).
  - cbn [ck_ok] in Hck.
    apply andb_true_iff in Hck as [Hck Hres].
    apply andb_true_iff in Hck as [Hs Hr].
    apply Nat.leb_le in Hs. apply Nat.leb_le in Hr.
    apply (ordered_alpha_uniformity_any up d start sp lss Hne Hs Hr); [|exact Hok].
    apply orb_true_iff in Hres as [H|H].
    + apply orb_true_iff in H as [H|H].
      * left. apply negb_true_iff, H.
      * right; left. apply andb_true_iff in H as [Hn H].
        split; [apply Nat.leb_le, Hn | apply negb_true_iff, H].
    + right; right. apply andb_true_iff in H as [H Hd2].
      apply andb_true_iff in H as [Hn Hd1].
      split; [apply Nat.leb_le, Hn|].
      split; [exact Hd1 | apply negb_true_iff, Hd2].
Qed.

(** The colon-marker instance, named separately so clients can use the
    definition-list statement without unpacking [list_kind].  Each item's
    blocks are parsed at top level before [def_items] pairs definitions
    with their terms. *)
Theorem definition_list_uniformity :
  forall sp lss,
    bdeflists = true ->
    lss <> [] ->
    forallb (item_ok colon) lss = true ->
    parse_lines (list_lines sp (map litem_lines (same_marker colon lss)))
      (PPara []) =
    [mk (DefinitionList (list_spacing_of sp lss)
      (def_items (map (fun L => parse_lines L (PPara [])) lss)))].
Proof.
  intros sp lss Hdefs Hne Hok.
  exact (ck_uniformity LKDef sp lss Hne Hdefs Hok).
Qed.

(** The same with the list closed by a following line. *)
Theorem ck_uniformity_tail :
  forall k sp lss next tail,
    lss <> [] ->
    ck_ok k (length lss) = true ->
    forallb (item_ok (ck_first k)) lss = true ->
    classify next <> KBlank ->
    (forall a b c d, classify next <> KList a b c d) ->
    indent_of next = 0 ->
    parse_lines (list_lines sp (map litem_lines (ck_items k lss))
                 ++ EmptyString :: next :: tail)%list (PPara [])
    = mk (ck_block k (list_spacing_of sp lss)
            (map (fun L => parse_lines L (PPara [])) lss))
      :: parse_lines (next :: tail) (PPara []).
Proof.
  intros [| |checks|d start|up d start|up d start] sp lss next tail
    Hne Hck Hok Hnb Hnl Hindent.
  - cbn [ck_items ck_block ck_first] in Hok |- *.
    rewrite map_litem_lines_same_marker.
    exact (list_uniformity_tail_same bullet sp lss next tail bullet_ok eq_refl Hne Hok
             Hnb Hnl Hindent).
  - cbn [ck_items ck_block ck_first] in Hok |- *.
    rewrite map_litem_lines_same_marker.
    cbn [ck_ok] in Hck.
    rewrite <- (marker_list_checked_colon _
                  (map (fun _ => mk_check colon) lss) _ Hck).
    exact (list_uniformity_tail_same colon sp lss next tail colon_ok eq_refl Hne Hok
             Hnb Hnl Hindent).
  - cbn [ck_ok] in Hck. apply andb_true_iff in Hck as [Htasks Hck].
    apply Nat.eqb_eq in Hck.
    exact (task_uniformity_tail checks sp lss next tail Htasks Hne Hck Hok
             Hnb Hnl Hindent).
  - exact (ordered_decimal_uniformity_tail d start sp lss next tail
             Hne Hck Hok Hnb Hnl Hindent).
  - cbn [ck_ok] in Hck.
    apply andb_true_iff in Hck as [Hs Hr].
    apply Nat.leb_le in Hs. apply Nat.leb_le in Hr.
    exact (ordered_roman_uniformity_any_tail up d start sp lss next tail
             Hne Hs Hr Hok Hnb Hnl Hindent).
  - cbn [ck_ok] in Hck.
    apply andb_true_iff in Hck as [Hck Hres].
    apply andb_true_iff in Hck as [Hs Hr].
    apply Nat.leb_le in Hs. apply Nat.leb_le in Hr.
    apply (ordered_alpha_uniformity_any_tail up d start sp lss next tail Hne Hs Hr);
      [|exact Hok|exact Hnb|exact Hnl|exact Hindent].
    apply orb_true_iff in Hres as [H|H].
    + apply orb_true_iff in H as [H|H].
      * left. apply negb_true_iff, H.
      * right; left. apply andb_true_iff in H as [Hn H].
        split; [apply Nat.leb_le, Hn | apply negb_true_iff, H].
    + right; right. apply andb_true_iff in H as [H Hd2].
      apply andb_true_iff in H as [Hn Hd1].
      split; [apply Nat.leb_le, Hn|].
      split; [exact Hd1 | apply negb_true_iff, Hd2].
Qed.

(* The first item's marker is the one `item_ok` is asked for: every
   flavour builds its items left to right and `ck_first` names what it
   starts with. *)
Local Lemma ck_items_first :
  forall k L rest, exists more, ck_items k (L :: rest) = (ck_first k, L) :: more.
Proof.
  intros [| |checks|d start|up d start|up d start] L rest;
    cbn [ck_items ck_first same_marker task_ck_items dec_items nsc_items];
    try (eexists; reflexivity).
  destruct checks; eexists; reflexivity.
Qed.

(* A rendered list opens with a marker line, so it neither drops pending
   block attributes nor claims them for a spec of its own.  This is the
   list arm of `Roundtrip.cb_lines_first_ready`; the other constructors
   read their first line's classification off their own opener. *)
Lemma ck_lines_first_ready :
  forall k sp lss a rest,
    ck_ok k (length lss) = true ->
    forallb (item_ok (ck_first k)) lss = true ->
    list_lines sp (map litem_lines (ck_items k lss)) = (a :: rest)%list ->
    pend_ready (PPara []) a = true.
Proof.
  intros k sp lss a rest Hck Hok Hlines.
  destruct lss as [|L lss'];
    [destruct k;
     cbn [ck_items same_marker task_ck_items dec_items nsc_items map list_lines]
       in Hlines; discriminate Hlines|].
  destruct (ck_items_first k L lss') as [more Hitems].
  pose proof (ck_items_markers_ok k (L :: lss') Hck) as Hm.
  rewrite Hitems in Hm. cbn [forallb fst] in Hm.
  apply andb_true_iff in Hm as [Hm _].
  cbn [forallb] in Hok. apply andb_true_iff in Hok as [Hitem _].
  destruct L as [|l0 more']; [discriminate Hitem|].
  cbn [item_ok] in Hitem.
  apply andb_true_iff in Hitem as [Hitem _].
  apply andb_true_iff in Hitem as [Hitem _].
  apply andb_true_iff in Hitem as [Hitem _].
  apply andb_true_iff in Hitem as [Hth _].
  apply andb_true_iff in Hth as [Hth Hts].
  apply negb_true_iff in Hth. apply negb_true_iff in Hts.
  rewrite Hitems in Hlines. cbn [map] in Hlines.
  assert (Hhd : forall x xs yss,
             exists tl, list_lines sp ((x :: xs) :: yss) = x :: tl).
  { intros x xs [|y yss]; [exists xs; reflexivity|].
    rewrite (list_lines_cons2 sp (x :: xs) (y :: yss) ltac:(discriminate)).
    cbn [app]. eexists; reflexivity. }
  unfold litem_lines in Hlines. cbn [fst snd indent_lines] in Hlines.
  destruct (Hhd (mk_open (ck_first k) ++ l0)
              (map (fun x : string => mk_cont (ck_first k) ++ x) more')
              (map (fun it : litem =>
                      indent_lines (mk_open (fst it)) (mk_cont (fst it)) (snd it))
                   more)) as [tl Htl].
  rewrite Htl in Hlines. injection Hlines as <- _.
  unfold pend_ready.
  rewrite (classify_marker_open (ck_first k) l0 Hm Hth
             (task_start_shadow _ _ Hts)).
  reflexivity.
Qed.

End WithTable.

(*
What the narrowing condition reaches, and what it does not
---------------------------------------------------------

`items_ok` asks that each sibling admit the styles the list opened with,
not that it offer exactly them.  The two are the same for bullets and
for decimal, where every marker names one style; they part company at
the ambiguous ordered markers, and the examples below are the boundary.

A roman numeral that is a bare roman letter (`i`, `v`, `x`, `l`, `c`,
`d`, `m`) is also a single letter, so it offers roman and alpha; any
longer numeral offers only roman.  So `items_ok` covers a run exactly
when its first numeral is unambiguous: later ones may be ambiguous,
since a superset narrows to the identity.  The same reading covers an
alpha list whose first letter is not a roman digit.

What `items_ok` leaves out is a run whose first marker is ambiguous,
`i.` / `ii.` being the shortest.  The parser narrows it to roman, but
the list state's style set moves, and `items_ok` asks every sibling to
admit both of `i.`'s styles.  `list_uniformity_narrow`, stated on the
set, covers it.
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

(* Covered by `list_uniformity_narrow`: `i.` opens offering roman and
   alpha, `ii.` narrows to roman alone, and the list closes to the
   narrowed set.  `items_ok` says false here, since it asks every sibling
   to admit both of `i.`'s styles, which is why the theorem that reaches
   this case is the one stated on the set. *)
Corollary roman_from_one_uniformity :
  forall sp,
    parse_lines (list_lines sp
                   (map litem_lines [(MOrd "i" RightPeriod, ["a"]);
                                     (MOrd "ii" RightPeriod, ["b"])]))
                (PPara [])
    = [mk (OrderedList (OLAttrs RomanLower RightPeriod 1)
             (list_spacing_of sp [["a"]; ["b"]])
             [parse_lines ["a"] (PPara []); parse_lines ["b"] (PPara [])])].
Proof.
  intros sp.
  exact (list_uniformity_narrow (MOrd "i" RightPeriod) (MOrd "ii" RightPeriod)
           [(SOrd RomanLower RightPeriod, 1)] sp ["a"] ["b"] []
           eq_refl eq_refl eq_refl eq_refl
           ltac:(discriminate) eq_refl eq_refl eq_refl
           ltac:(discriminate) eq_refl).
Qed.

(* And the other branch of the same fork: `j.` narrows `i.`'s set the
   other way, so the list is alpha from 9.  The resolved style is not a
   function of the first marker -- the same `i.` opens both. *)
Corollary alpha_from_nine_uniformity :
  forall sp,
    parse_lines (list_lines sp
                   (map litem_lines [(MOrd "i" RightPeriod, ["a"]);
                                     (MOrd "j" RightPeriod, ["b"])]))
                (PPara [])
    = [mk (OrderedList (OLAttrs LetterLower RightPeriod 9)
             (list_spacing_of sp [["a"]; ["b"]])
             [parse_lines ["a"] (PPara []); parse_lines ["b"] (PPara [])])].
Proof.
  intros sp.
  exact (list_uniformity_narrow (MOrd "i" RightPeriod) (MOrd "j" RightPeriod)
           [(SOrd LetterLower RightPeriod, 9)] sp ["a"] ["b"] []
           eq_refl eq_refl eq_refl eq_refl
           ltac:(discriminate) eq_refl eq_refl eq_refl
           ltac:(discriminate) eq_refl).
Qed.

(* `items_ok` still cannot describe either, which is the point: it asks
   every sibling to admit *both* of `i.`'s candidates. *)
Example roman_from_one_items_ok_fails :
  items_ok (MOrd "i" RightPeriod)
    [(MOrd "i" RightPeriod, ["a"]); (MOrd "ii" RightPeriod, ["b"])] = false.
Proof. reflexivity. Qed.

Example roman_from_one_parses_anyway :
  parse_lines ["i. a"; "ii. b"] (PPara [])
  = [mk (OrderedList (OLAttrs RomanLower RightPeriod 1) Tight
           [[mk (Para [mk (Str "a")])]; [mk (Para [mk (Str "b")])]])].
Proof. reflexivity. Qed.

(* The generalization, exercised.  `*` and `+` are separate list styles
   in djot, and each gets the uniformity theorem by instantiation, with no
   new proof.  A marker that needed its own argument would mean `marker`
   is the wrong abstraction. *)
Corollary star_uniformity :
  forall sp lss,
    lss <> [] -> forallb (item_ok star) lss = true ->
    parse_lines (list_lines sp (map (indent_lines (mk_open star) (mk_cont star)) lss))
                (PPara [])
    = [marker_list_checked star (list_spacing_of sp lss)
             (map (fun _ => mk_check star) lss)
             (map (fun L => parse_lines L (PPara [])) lss)].
Proof. intros sp lss. exact (list_uniformity_same star sp lss star_ok eq_refl). Qed.

Corollary plus_uniformity :
  forall sp lss,
    lss <> [] -> forallb (item_ok plus) lss = true ->
    parse_lines (list_lines sp (map (indent_lines (mk_open plus) (mk_cont plus)) lss))
                (PPara [])
    = [marker_list_checked plus (list_spacing_of sp lss)
             (map (fun _ => mk_check plus) lss)
             (map (fun L => parse_lines L (PPara [])) lss)].
Proof. intros sp lss. exact (list_uniformity_same plus sp lss plus_ok eq_refl). Qed.

(* Ordered markers are instances too: `1.` is one in the same way `*` is.
   This is `list_uniformity` with one marker serving every item
   (`list_uniformity_same`); a renumbering rendering, which needs a
   marker per item, uses `list_uniformity` directly. *)
Corollary ordered_uniformity :
  forall m sp itemss,
    marker_ok m = true -> itemss <> [] ->
    forallb (item_ok m) itemss = true ->
    parse_lines (list_lines sp (map (indent_lines (mk_open m) (mk_cont m)) itemss))
                (PPara [])
    = [marker_list_checked m (list_spacing_of sp itemss)
             (map (fun _ => mk_check m) itemss)
             (map (fun L => parse_lines L (PPara [])) itemss)].
Proof.
  intros m sp itemss Hm.
  assert (Htasks : marker_tasks_ok btasks m = true) by (destruct m; reflexivity).
  exact (list_uniformity_same m sp itemss Hm Htasks).
Qed.

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

(* A nineteen-digit numeral is past `dec_digits_max` and is not a marker. *)
Example decimal_too_long_is_text :
  parse_lines ["1234567890123456789. a"] (PPara [])
  = [mk (Para [mk (Str "1234567890123456789. a")])].
Proof. vm_compute. reflexivity. Qed.

Example paren_list_parses :
  parse_lines ["(1) a"; "(1) b"] (PPara [])
  = [mk (OrderedList (OLAttrs Decimal LeftRightParen 1) Tight
           [[mk (Para [mk (Str "a")])]; [mk (Para [mk (Str "b")])]])].
Proof. reflexivity. Qed.

(* And it is not vacuous at ordered markers. *)
Example star_list_parses :
  parse_lines ["* a"; "* b"] (PPara [])
  = [mk (BulletList Tight [[mk (Para [mk (Str "a")])];
                           [mk (Para [mk (Str "b")])]])].
Proof. reflexivity. Qed.

Example star_item_ok : item_ok star ["a"] = true.
Proof. reflexivity. Qed.


(* Non-vacuity, and the shape of an instantiation: every hypothesis of
   `ordered_roman_uniformity` but the nonemptiness is decidable, so a
   concrete start discharges them by computation. *)
Example roman_from_two_lines :
  map litem_lines (nsc_items (Roman.str false) RightPeriod 2 [["a"]; ["b"]; ["c"]])
  = [["ii. a"]; ["iii. b"]; ["iv. c"]].
Proof. reflexivity. Qed.

Corollary roman_from_two_uniform :
  forall sp,
    parse_lines (list_lines sp
                   (map litem_lines
                      (nsc_items (Roman.str false) RightPeriod 2 [["a"]; ["b"]; ["c"]])))
                (PPara [])
    = [mk (OrderedList (OLAttrs RomanLower RightPeriod 2)
             (list_spacing_of sp [["a"]; ["b"]; ["c"]])
             [parse_lines ["a"] (PPara []); parse_lines ["b"] (PPara []);
              parse_lines ["c"] (PPara [])])].
Proof.
  intros sp.
  exact (ordered_roman_uniformity false RightPeriod 2 sp [["a"]; ["b"]; ["c"]]
           ltac:(discriminate) ltac:(lia) ltac:(vm_compute; lia)
           ltac:(vm_compute; lia) eq_refl).
Qed.

(* Alpha from `a`, running through `c` and `d`, which are roman digits:
   only the *first* marker is constrained. *)
Example alpha_from_one_lines :
  map litem_lines (nsc_items (Alpha.str false) RightParen 1 [["x"]; ["y"]; ["z"]; ["w"]])
  = [["a) x"]; ["b) y"]; ["c) z"]; ["d) w"]].
Proof. reflexivity. Qed.

Corollary alpha_from_one_uniform :
  forall sp,
    parse_lines (list_lines sp
                   (map litem_lines
                      (nsc_items (Alpha.str false) RightParen 1
                         [["x"]; ["y"]; ["z"]; ["w"]])))
                (PPara [])
    = [mk (OrderedList (OLAttrs LetterLower RightParen 1)
             (list_spacing_of sp [["x"]; ["y"]; ["z"]; ["w"]])
             [parse_lines ["x"] (PPara []); parse_lines ["y"] (PPara []);
              parse_lines ["z"] (PPara []); parse_lines ["w"] (PPara [])])].
Proof.
  intros sp.
  exact (ordered_alpha_uniformity false RightParen 1 sp
           [["x"]; ["y"]; ["z"]; ["w"]]
           ltac:(discriminate) ltac:(lia) ltac:(vm_compute; lia)
           eq_refl eq_refl).
Qed.

(* The boundary, kept as a failing-by-construction pair: the parser reads
   a roman list from 1 correctly, and `items_ok` cannot say so. *)
Example roman_from_one_items_ok_still_fails :
  items_ok (nsc_marker (Roman.str false) RightPeriod 1)
           (nsc_items (Roman.str false) RightPeriod 1 [["a"]; ["b"]]) = false.
Proof. reflexivity. Qed.

Example roman_from_one_parses_anyway_too :
  parse_lines ["i. a"; "ii. b"] (PPara [])
  = [mk (OrderedList (OLAttrs RomanLower RightPeriod 1) Tight
           [[mk (Para [mk (Str "a")])]; [mk (Para [mk (Str "b")])]])].
Proof. reflexivity. Qed.
