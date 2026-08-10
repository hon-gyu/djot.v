(* ai-disclosure: ai-generated *)

(* Marker numerals and the candidate styles a marker admits.

   Split out of `Parser.v`: this is arithmetic on numerals and a filter
   on style sets, not parsing.  Nothing here mentions `pstate`, and the
   roman and alpha codecs land here.

   `Line.styles_of_core` says which styles a marker's core *could* be;
   this file decodes the start number under each of them, and `narrow`
   is the intersection siblings take. *)

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

(* ...and its inverse, which the roundtrip needs: an ordered list's start
   number is rendered into its first marker and has to come back.
   `Strings.nat_str` goes through the stdlib's decimal machinery, whose
   round-trip is stated against `NilZero.uint_of_string` rather than
   against `dec_value`; rendering here instead keeps the pair
   self-contained and the proof two lemmas. *)
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

(* djot.js's `romanToNumber` (parse.ts:80-100): scan right to left, and
   subtract a digit smaller than the one to its right, so `ix` is 9. *)
Fixpoint roman_acc (s : string) (prev total : nat) : nat :=
  match s with
  | EmptyString => total
  | String c s' =>
      let n := roman_digit c in
      roman_acc s' n (if Nat.ltb n prev then total - n else total + n)
  end.

Definition roman_value (s : string) : nat := roman_acc (rev_string s) 0 0.

(* `getListStart` (parse.ts:102-113).  Alpha reads the first character
   only, which is exact rather than a simplification: `[a-zA-Z][.)]` is
   the only alpha marker pattern, so an alpha core is one character. *)
Definition style_start (s : lstyle) (core : string) : nat :=
  match s with
  | SBullet _ => 1
  | SOrd Decimal _ => dec_value core
  | SOrd LetterLower _ =>
      match core with String c _ => nat_of_ascii c - 96 | _ => 1 end
  | SOrd LetterUpper _ =>
      match core with String c _ => nat_of_ascii c - 64 | _ => 1 end
  | SOrd RomanLower _ | SOrd RomanUpper _ => roman_value core
  end.

Definition with_starts (sty : list lstyle) (core : string)
  : list (lstyle * nat) :=
  map (fun s => (s, style_start s core)) sty.

(* Narrowing, djot.js block.ts:389-399: keep the candidates this list
   already had that the new marker also admits.  Filtering `old` rather
   than `new` is what preserves the first marker's start numbers. *)
Definition narrow (old : list (lstyle * nat)) (new : list lstyle)
  : list (lstyle * nat) :=
  filter (fun p => existsb (lstyle_eqb (fst p)) new) old.

(* The style set a canonical rendering of `mrk` opens with. *)
Definition mk_styles (m : marker) : list (lstyle * nat) :=
  with_starts (mk_sty m) (mk_core m).

Lemma lstyle_eqb_refl : forall s, lstyle_eqb s s = true.
Proof.
  intros [c|n d]; cbn [lstyle_eqb].
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
Definition admits (m0 m : marker) : bool :=
  forallb (fun p => existsb (lstyle_eqb (fst p)) (mk_sty m)) (mk_styles m0).

Lemma narrow_admits :
  forall m0 m, admits m0 m = true ->
    narrow (mk_styles m0) (mk_sty m) = mk_styles m0.
Proof. intros m0 m H. apply forallb_filter_id, H. Qed.

Lemma admits_agree : forall m0 m, mk_sty m = mk_sty m0 -> admits m0 m = true.
Proof.
  intros m0 m H. unfold admits, mk_styles, with_starts. rewrite H.
  apply forallb_forall. intros p Hin.
  apply in_map_iff in Hin as [s [Hs Hin]]. subst p. cbn [fst].
  apply existsb_exists. exists s. split; [exact Hin | apply lstyle_eqb_refl].
Qed.

Lemma admits_refl : forall m, admits m m = true.
Proof. intros m. apply admits_agree. reflexivity. Qed.

(* The block a list rendered with marker `m` closes to.  Bullets give a
   `BulletList` definitionally, so instantiating the uniformity chain at
   `bullet` still reads as it did; an ordered marker gives the
   `OrderedList` its style and start. *)
Definition marker_list (m : marker) (sp : list_spacing) (items : list blocks)
  : node block :=
  match mk_styles m with
  | (SOrd n d, start) :: _ => mk (OrderedList (OLAttrs n d start) sp items)
  | _ => mk (BulletList sp items)
  end.
