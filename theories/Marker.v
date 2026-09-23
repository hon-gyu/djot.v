(* ai-disclosure: autonomous *)

(* Marker numerals and the candidate styles a marker admits: arithmetic
   on numerals and a filter on style sets, not parsing.

   `Line.styles_of_core` says which styles a marker's core could be; this
   file decodes the start number under each of them, and `narrow` is the
   intersection siblings take. *)

From Stdlib Require Import String Ascii List Bool PeanoNat Lia.
From DjotV Require Import Strings Line Ast.
Import ListNotations.

Local Open Scope string_scope.

(*
List styles and start numbers
=============================

A marker's numeral, decoded per candidate style.  This is the whole of
what the block layer does with a number: it reads one, at the list's
first item, and never counts.  Renumbering is the renderer's job.
*)

Fixpoint dec_acc (s : string) (acc : nat) : nat :=
  match s with
  | EmptyString => acc
  | String c s' => dec_acc s' (acc * 10 + (nat_of_ascii c - 48))
  end.

Definition dec_value (s : string) : nat := dec_acc s 0.

(* ...and its inverse: an ordered list's start number is rendered into
   its first marker and has to come back.  Rendered here rather than with
   `Strings.nat_str`, whose round-trip is stated against the stdlib's
   decoder rather than `dec_value`. *)
Definition digit_char (d : nat) : ascii := ascii_of_nat (48 + d).

Fixpoint dec_str_fuel (fuel n : nat) : string :=
  match fuel with
  | O => EmptyString
  | S f =>
      if Nat.ltb n 10
      then String (digit_char n) EmptyString
      else (dec_str_fuel f (Nat.div n 10)
            ++ String (digit_char (Nat.modulo n 10)) EmptyString)%string
  end.

Definition dec_str (n : nat) : string := dec_str_fuel (S n) n.

Lemma dec_acc_app :
  forall s1 s2 a, dec_acc (s1 ++ s2) a = dec_acc s2 (dec_acc s1 a).
Proof.
  induction s1 as [|c s1 IH]; intros s2 a; [reflexivity|].
  cbn [append dec_acc]. apply IH.
Qed.

Lemma digit_char_value :
  forall d, d < 10 -> nat_of_ascii (digit_char d) - 48 = d.
Proof.
  intros d Hd. unfold digit_char.
  rewrite nat_ascii_embedding by lia. lia.
Qed.

Lemma dec_str_fuel_value :
  forall fuel n, n < fuel -> dec_acc (dec_str_fuel fuel n) 0 = n.
Proof.
  induction fuel as [|f IH]; intros n Hn; [lia|].
  cbn [dec_str_fuel]. destruct (Nat.ltb n 10) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt. cbn [dec_acc].
    rewrite digit_char_value by exact Hlt. reflexivity.
  - apply Nat.ltb_ge in Hlt.
    rewrite dec_acc_app, IH.
    + cbn [dec_acc].
      rewrite digit_char_value by (apply Nat.mod_upper_bound; lia).
      rewrite Nat.mul_comm. symmetry. apply Nat.div_mod_eq.
    + apply Nat.Div0.div_lt_upper_bound; lia.
Qed.

Lemma dec_value_dec_str : forall n, dec_value (dec_str n) = n.
Proof. intros n. unfold dec_value, dec_str. apply dec_str_fuel_value. lia. Qed.

Lemma dec_str_fuel_digits :
  forall fuel n, str_forallb is_digit (dec_str_fuel fuel n) = true
                 /\ (0 < fuel -> dec_str_fuel fuel n <> EmptyString).
Proof.
  induction fuel as [|f IH]; intros n; [split; [reflexivity|lia]|].
  cbn [dec_str_fuel]. destruct (Nat.ltb n 10) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt. split; [|discriminate].
    cbn [str_forallb]. unfold is_digit, in_range, digit_char.
    rewrite nat_ascii_embedding by lia.
    rewrite (proj2 (Nat.leb_le 48 (48 + n))) by lia.
    rewrite (proj2 (Nat.leb_le (48 + n) 57)) by lia. reflexivity.
  - apply Nat.ltb_ge in Hlt. split.
    + destruct (IH (Nat.div n 10)) as [Hd _].
      assert (Hm : Nat.modulo n 10 < 10) by (apply Nat.mod_upper_bound; lia).
      revert Hd. generalize (dec_str_fuel f (Nat.div n 10)) as t. intros t Hd.
      induction t as [|c t IHt].
      * cbn [append str_forallb]. unfold is_digit, in_range, digit_char.
        rewrite nat_ascii_embedding by lia.
        rewrite (proj2 (Nat.leb_le 48 (48 + Nat.modulo n 10))) by lia.
        rewrite (proj2 (Nat.leb_le (48 + Nat.modulo n 10) 57)) by lia. reflexivity.
      * cbn [str_forallb] in Hd. apply andb_true_iff in Hd as [Hc Ht].
        cbn [append str_forallb]. rewrite Hc, (IHt Ht). reflexivity.
    + intros _. destruct (dec_str_fuel f (Nat.div n 10)); discriminate.
Qed.

Lemma dec_str_digits : forall n, str_forallb is_digit (dec_str n) = true.
Proof. intros n. apply (dec_str_fuel_digits (S n) n). Qed.

Lemma dec_str_nonempty : forall n, nonempty_str (dec_str n) = true.
Proof.
  intros n. destruct (dec_str_fuel_digits (S n) n) as [_ Hne].
  unfold dec_str. destruct (dec_str_fuel (S n) n) eqn:E; [|reflexivity].
  exfalso. apply (Hne ltac:(lia)). reflexivity.
Qed.

Definition roman_digit (c : ascii) : nat :=
  if (Ascii.eqb c "i" || Ascii.eqb c "I")%char%bool then 1
  else if (Ascii.eqb c "v" || Ascii.eqb c "V")%char%bool then 5
  else if (Ascii.eqb c "x" || Ascii.eqb c "X")%char%bool then 10
  else if (Ascii.eqb c "l" || Ascii.eqb c "L")%char%bool then 50
  else if (Ascii.eqb c "c" || Ascii.eqb c "C")%char%bool then 100
  else if (Ascii.eqb c "d" || Ascii.eqb c "D")%char%bool then 500
  else if (Ascii.eqb c "m" || Ascii.eqb c "M")%char%bool then 1000
  else 0.

(* Scan right to left, subtracting a digit smaller than the one to its
   right, so `ix` is 9. *)
Fixpoint roman_acc (s : string) (prev total : nat) : nat :=
  match s with
  | EmptyString => total
  | String c s' =>
      let n := roman_digit c in
      roman_acc s' n (if Nat.ltb n prev then total - n else total + n)
  end.

Definition roman_value (s : string) : nat := roman_acc (rev_string s) 0 0.

(* An alpha numeral's value, from its first character: an alpha core is
   one character. *)
Definition alpha_value (up : bool) (core : string) : nat :=
  match core with
  | String c _ => nat_of_ascii c - (if up then 64 else 96)
  | EmptyString => 1
  end.

(* The largest roman start the codec covers.

   The encoder below is a left-to-right greedy emission and `roman_value`
   a right-to-left subtractive scan, inverse for a reason no induction on
   either exposes.  So every property the codec needs is proved by
   computation over a bounded range: `roman_ok` bundles them,
   `roman_ok_range` decides the bundle for every start at once, and
   `roman_ok_lt` is the only form the rest of the development sees.  The
   alpha codec needs a bound anyway (there is no 27th letter).

   1000 rather than 3999, where the standard spelling stops, because the
   check is quadratic in the bound (0.25s at 1000, 2.0s at 3999) and this
   file is upstream of everything. *)
Definition roman_upper : nat := 1000.

Definition roman_table (up : bool) : list (nat * string) :=
  if up
  then [(1000,"M");(900,"CM");(500,"D");(400,"CD");(100,"C");(90,"XC");(50,"L");
        (40,"XL");(10,"X");(9,"IX");(5,"V");(4,"IV");(1,"I")]
  else [(1000,"m");(900,"cm");(500,"d");(400,"cd");(100,"c");(90,"xc");(50,"l");
        (40,"xl");(10,"x");(9,"ix");(5,"v");(4,"iv");(1,"i")].

Fixpoint roman_pick (tbl : list (nat * string)) (n : nat) : option (nat * string) :=
  match tbl with
  | [] => None
  | (v, s) :: rest => if Nat.leb v n then Some (v, s) else roman_pick rest n
  end.

(* A table and a lookup rather than thirteen nested `if`s.  With the
   branches inlined the recursive call appears in all thirteen, so
   symbolically normalizing `roman_str up n` at an unknown `n` unfolds to
   13^16 branches, and a `Qed` that converts it does not terminate.
   `roman_pick` leaves one recursive call per level. *)
Fixpoint roman_fuel (up : bool) (fuel n : nat) : string :=
  match fuel with
  | O => EmptyString
  | S f =>
      match roman_pick (roman_table up) n with
      | None => EmptyString
      | Some (v, s) => s ++ roman_fuel up f (n - v)
      end
  end.

(* Fuel 16, not `n`: every step emits at least one character, and the
   longest numeral (3888, `mmmdccclxxxviii`) has 15.  `roman_ok_range`
   checks that it suffices, since exhausted fuel truncates the numeral.
   Not a speedup: the range check's cost is `Nat.leb 1000 n` on a unary
   `nat`, which does not depend on the fuel. *)
Definition roman_str (up : bool) (n : nat) : string := roman_fuel up 16 n.

Definition alpha_str (up : bool) (n : nat) : string :=
  String (ascii_of_nat ((if up then 64 else 96) + n)) EmptyString.

(* What a codec has to deliver for the marker layer: a nonempty core, in
   the alphabet its style is recognized by, decoding back to the number
   it was made from.  One boolean, so that one computation settles all
   three. *)
Definition roman_ok (up : bool) (n : nat) : bool :=
  let s := roman_str up n in
  (nonempty_str s
   && str_forallb (if up then is_roman_up else is_roman_lo) s
   && Nat.eqb (roman_value s) n)%bool.

Definition alpha_ok (up : bool) (n : nat) : bool :=
  let s := alpha_str up n in
  (nonempty_str s
   && str_forallb (if up then is_upper else is_lower) s
   && Nat.eqb (alpha_value up s) n)%bool.

Definition alpha_upper : nat := 26.

(* No two consecutive roman numerals are both a single character, so if a
   list's first numeral is ambiguous its second is not, and one narrowing
   settles the set.  Checked rather than argued: the single-character
   numerals are 1, 5, 10, 50, 100, 500, 1000 and none is adjacent to
   another, but that is a fact about the table, not about the code. *)
Definition roman_consec_ok (up : bool) (n : nat) : bool :=
  (Nat.leb 2 (String.length (roman_str up n))
   || Nat.leb 2 (String.length (roman_str up (S n))))%bool.

Example roman_consec_lo : forallb (roman_consec_ok false) (seq 1 roman_upper) = true.
Proof. vm_compute. reflexivity. Qed.

Example roman_consec_up : forallb (roman_consec_ok true) (seq 1 roman_upper) = true.
Proof. vm_compute. reflexivity. Qed.

(* The four computations the codecs rest on.  Everything below is
   bookkeeping on top of these. *)
Example roman_ok_lo : forallb (roman_ok false) (seq 1 roman_upper) = true.
Proof. vm_compute. reflexivity. Qed.

Example roman_ok_up : forallb (roman_ok true) (seq 1 roman_upper) = true.
Proof. vm_compute. reflexivity. Qed.

Example alpha_ok_lo : forallb (alpha_ok false) (seq 1 alpha_upper) = true.
Proof. vm_compute. reflexivity. Qed.

Example alpha_ok_up : forallb (alpha_ok true) (seq 1 alpha_upper) = true.
Proof. vm_compute. reflexivity. Qed.

(* Turning a checked range into the pointwise fact.  Generic: another
   codec supplies its own `forallb` and reuses this. *)
Lemma range_ok :
  forall (f : nat -> bool) (hi n : nat),
    forallb f (seq 1 hi) = true -> 1 <= n -> n <= hi -> f n = true.
Proof.
  intros f hi n H H1 H2.
  apply (proj1 (forallb_forall f (seq 1 hi)) H). apply in_seq. lia.
Qed.

Lemma roman_ok_lt :
  forall up n, 1 <= n -> n <= roman_upper -> roman_ok up n = true.
Proof.
  intros [|] n H1 H2;
    [ exact (range_ok _ _ _ roman_ok_up H1 H2)
    | exact (range_ok _ _ _ roman_ok_lo H1 H2) ].
Qed.

Lemma roman_consec_lt :
  forall (up : bool) n, 1 <= n -> n <= roman_upper ->
    2 <= String.length (roman_str up n) \/ 2 <= String.length (roman_str up (S n)).
Proof.
  intros up n H1 H2.
  assert (H : roman_consec_ok up n = true)
    by (destruct up; [exact (range_ok _ _ _ roman_consec_up H1 H2)
                     |exact (range_ok _ _ _ roman_consec_lo H1 H2)]).
  unfold roman_consec_ok in H. apply orb_true_iff in H as [H|H];
    [left|right]; apply Nat.leb_le, H.
Qed.

Lemma alpha_ok_lt :
  forall up n, 1 <= n -> n <= alpha_upper -> alpha_ok up n = true.
Proof.
  intros [|] n H1 H2;
    [ exact (range_ok _ _ _ alpha_ok_up H1 H2)
    | exact (range_ok _ _ _ alpha_ok_lo H1 H2) ].
Qed.

(* The three fields, unpacked.  Stated at `roman_str` / `alpha_str` so
   that the ordered-list chain never mentions `roman_ok`. *)
Lemma roman_str_nonempty :
  forall up n, 1 <= n -> n <= roman_upper -> nonempty_str (roman_str up n) = true.
Proof.
  intros up n H1 H2. pose proof (roman_ok_lt up n H1 H2) as H.
  unfold roman_ok in H. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _]. exact H.
Qed.

Lemma roman_str_alphabet :
  forall (up : bool) n, 1 <= n -> n <= roman_upper ->
    str_forallb (if up then is_roman_up else is_roman_lo) (roman_str up n) = true.
Proof.
  intros up n H1 H2. pose proof (roman_ok_lt up n H1 H2) as H.
  unfold roman_ok in H. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [_ H]. exact H.
Qed.

Lemma roman_value_str :
  forall up n, 1 <= n -> n <= roman_upper -> roman_value (roman_str up n) = n.
Proof.
  intros up n H1 H2. pose proof (roman_ok_lt up n H1 H2) as H.
  unfold roman_ok in H. apply andb_true_iff in H as [_ H].
  apply Nat.eqb_eq, H.
Qed.

Lemma alpha_str_nonempty :
  forall up n, 1 <= n -> n <= alpha_upper -> nonempty_str (alpha_str up n) = true.
Proof. intros. reflexivity. Qed.

Lemma alpha_str_alphabet :
  forall (up : bool) n, 1 <= n -> n <= alpha_upper ->
    str_forallb (if up then is_upper else is_lower) (alpha_str up n) = true.
Proof.
  intros up n H1 H2. pose proof (alpha_ok_lt up n H1 H2) as H.
  unfold alpha_ok in H. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [_ H]. exact H.
Qed.

Lemma alpha_value_str :
  forall up n, 1 <= n -> n <= alpha_upper -> alpha_value up (alpha_str up n) = n.
Proof.
  intros up n H1 H2. pose proof (alpha_ok_lt up n H1 H2) as H.
  unfold alpha_ok in H. apply andb_true_iff in H as [_ H].
  apply Nat.eqb_eq, H.
Qed.

(*
Alphabets
---------

Which character classes exclude which.  `styles_of_core` decides a
marker's styles by testing these in order, so reading its result off a
roman or alpha numeral means knowing that a roman letter is not a digit,
that an uppercase one is not a lowercase one, and so on.  Each is decided
by the seven-way `Ascii.eqb` disjunction or by the range arithmetic, and
none of them is interesting; they are here so the `styles_of_core`
lemmas downstream read as one rewrite each.
*)

Lemma str_forallb_impl :
  forall (p q : ascii -> bool) s,
    (forall c, p c = true -> q c = true) ->
    str_forallb p s = true -> str_forallb q s = true.
Proof.
  intros p q s Hpq. induction s as [|c s IH]; [reflexivity|].
  cbn [str_forallb]. intros H. apply andb_true_iff in H as [Hc Hs].
  rewrite (Hpq c Hc). apply IH, Hs.
Qed.

Lemma is_roman_lo_lower : forall c, is_roman_lo c = true -> is_lower c = true.
Proof.
  intros c H. unfold is_roman_lo in H.
  repeat (apply orb_true_iff in H as [H|H]);
    apply Ascii.eqb_eq in H; subst c; reflexivity.
Qed.

Lemma is_roman_up_upper : forall c, is_roman_up c = true -> is_upper c = true.
Proof.
  intros c H. unfold is_roman_up in H.
  repeat (apply orb_true_iff in H as [H|H]);
    apply Ascii.eqb_eq in H; subst c; reflexivity.
Qed.

Lemma is_lower_not_digit : forall c, is_lower c = true -> is_digit c = false.
Proof.
  intros c H. unfold is_lower, is_digit, in_range in *.
  apply andb_true_iff in H as [H1 H2].
  apply Nat.leb_le in H1. apply Nat.leb_le in H2.
  apply andb_false_iff. right. apply Nat.leb_gt. lia.
Qed.

Lemma is_upper_not_digit : forall c, is_upper c = true -> is_digit c = false.
Proof.
  intros c H. unfold is_upper, is_digit, in_range in *.
  apply andb_true_iff in H as [H1 H2].
  apply Nat.leb_le in H1. apply Nat.leb_le in H2.
  apply andb_false_iff. right. apply Nat.leb_gt. lia.
Qed.

Lemma is_upper_not_lower : forall c, is_upper c = true -> is_lower c = false.
Proof.
  intros c H. unfold is_upper, is_lower, in_range in *.
  apply andb_true_iff in H as [H1 H2].
  apply Nat.leb_le in H1. apply Nat.leb_le in H2.
  apply andb_false_iff. left. apply Nat.leb_gt. lia.
Qed.

Lemma is_lower_not_roman_up : forall c, is_lower c = true -> is_roman_up c = false.
Proof.
  intros c H. destruct (is_roman_up c) eqn:E; [|reflexivity].
  rewrite (is_upper_not_lower c (is_roman_up_upper c E)) in H. discriminate.
Qed.

Lemma is_upper_not_roman_lo : forall c, is_upper c = true -> is_roman_lo c = false.
Proof.
  intros c H. destruct (is_roman_lo c) eqn:E; [|reflexivity].
  pose proof (is_roman_lo_lower c E) as Hl.
  rewrite (is_upper_not_lower c H) in Hl. discriminate.
Qed.

Lemma str_roman_not_digit :
  forall (up : bool) c rest,
    str_forallb (if up then is_roman_up else is_roman_lo) (String c rest) = true ->
    str_forallb is_digit (String c rest) = false.
Proof.
  intros up c rest H. cbn [str_forallb] in *.
  apply andb_true_iff in H as [Hc _].
  destruct up.
  - rewrite (is_upper_not_digit c (is_roman_up_upper c Hc)). reflexivity.
  - rewrite (is_lower_not_digit c (is_roman_lo_lower c Hc)). reflexivity.
Qed.

(* A marker's start number under one of its candidate styles. *)
Definition style_start (s : lstyle) (core : string) : nat :=
  match s with
  | SBullet _ | STask _ => 1
  | SOrd Decimal _ => dec_value core
  | SOrd LetterLower _ => alpha_value false core
  | SOrd LetterUpper _ => alpha_value true core
  | SOrd RomanLower _ | SOrd RomanUpper _ => roman_value core
  end.

Definition with_starts (sty : list lstyle) (core : string)
  : list (lstyle * nat) :=
  map (fun s => (s, style_start s core)) sty.

(* Narrowing: keep the candidates this list already had that the new
   marker also admits.  Filtering `old` rather than `new` preserves the
   first marker's start numbers. *)
Definition narrow (old : list (lstyle * nat)) (new : list lstyle)
  : list (lstyle * nat) :=
  filter (fun p => existsb (lstyle_eqb (fst p)) new) old.

(* The style set a canonical rendering of `mrk` opens with. *)
Definition mk_styles (m : marker) : list (lstyle * nat) :=
  with_starts (mk_sty m) (mk_core m).

Lemma lstyle_eqb_refl : forall s, lstyle_eqb s s = true.
Proof.
  intros [c|c|n d]; cbn [lstyle_eqb].
  - apply Ascii.eqb_refl.
  - apply Ascii.eqb_refl.
  - destruct n, d; reflexivity.
Qed.

(* Narrowing a set by the very styles it was built from is the identity.
   This is what makes the uniformity chain blind to styles: a canonical
   rendering repeats one marker, so every sibling re-offers exactly the
   candidates the list already has. *)
Lemma filter_map_all :
  forall (sty : list lstyle) (f : lstyle -> nat) (p : lstyle * nat -> bool),
    (forall s, In s sty -> p (s, f s) = true) ->
    filter p (map (fun s => (s, f s)) sty) = map (fun s => (s, f s)) sty.
Proof.
  induction sty as [|s rest IH]; intros f p Hp; [reflexivity|].
  cbn [map filter]. rewrite (Hp s (or_introl eq_refl)).
  f_equal. apply IH. intros s' Hin. apply Hp, or_intror, Hin.
Qed.

Lemma narrow_with_starts_self :
  forall sty core, narrow (with_starts sty core) sty = with_starts sty core.
Proof.
  intros sty core. unfold narrow, with_starts.
  apply filter_map_all. intros s Hin. cbn [fst].
  apply existsb_exists. exists s. split; [exact Hin | apply lstyle_eqb_refl].
Qed.

Lemma narrow_mk_styles :
  forall m, narrow (mk_styles m) (mk_sty m) = mk_styles m.
Proof. intros m. apply narrow_with_starts_self. Qed.

Lemma mk_styles_nonempty : forall m, marker_ok m = true -> mk_styles m <> [].
Proof.
  intros m Hm. destruct (mk_sty_cons m Hm) as (s & ss & Hs).
  unfold mk_styles, with_starts. rewrite Hs. discriminate.
Qed.

(* When a sibling leaves the list's candidate set exactly where it was:
   every style the list still offers is one this marker also admits.
   Equality of the two style *sets* is the special case, and it is too
   strong for the ambiguous markers -- `ii.` offers only roman where
   `i.` offered roman and alpha, so the sets differ while the narrowing
   is still the identity in the direction that matters.  Filtering `old`
   is what makes the weaker condition the right one: the list keeps its
   first marker's starts either way. *)
Definition admits_styles (S : list (lstyle * nat)) (m : marker) : bool :=
  forallb (fun p => existsb (lstyle_eqb (fst p)) (mk_sty m)) S.

Definition admits (m0 m : marker) : bool := admits_styles (mk_styles m0) m.

Lemma narrow_admits_styles :
  forall S m, admits_styles S m = true -> narrow S (mk_sty m) = S.
Proof. intros S m H. apply forallb_filter_id, H. Qed.

Lemma narrow_admits :
  forall m0 m, admits m0 m = true ->
    narrow (mk_styles m0) (mk_sty m) = mk_styles m0.
Proof. intros m0 m H. apply forallb_filter_id, H. Qed.

Lemma admits_agree : forall m0 m, mk_sty m = mk_sty m0 -> admits m0 m = true.
Proof.
  intros m0 m H. unfold admits, admits_styles, mk_styles, with_starts. rewrite H.
  apply forallb_forall. intros p Hin.
  apply in_map_iff in Hin as [s [Hs Hin]]. subst p. cbn [fst].
  apply existsb_exists. exists s. split; [exact Hin | apply lstyle_eqb_refl].
Qed.

Lemma admits_refl : forall m, admits m m = true.
Proof. intros m. apply admits_agree. reflexivity. Qed.

(* The same fact at the spelling `items_ok_at` leaves in a goal. *)
Lemma admits_styles_refl : forall m, admits_styles (mk_styles m) m = true.
Proof. exact admits_refl. Qed.

