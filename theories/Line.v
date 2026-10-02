(* ai-disclosure: autonomous *)

(* Line classification.

   Block structure in djot is a function of what each line looks like:
   the contribution a line makes to block structure never depends on a
   later line.  This module gives each line its kind, and the parser
   consumes kinds.  Render.v states renderability as "each rendered line
   classifies as intended", which keeps the roundtrip proofs local. *)

From Stdlib Require Import String Ascii List Bool PeanoNat Lia.
Import ListNotations.
From DjotV Require Import Strings Ast Attributes.

Local Open Scope string_scope.
Local Open Scope char_scope.

(* An opened code fence: its character (` or ~), length, and info string
   (language, or =FORMAT for raw blocks). *)
Record fence : Type := Fence
  { f_ch : ascii; f_len : nat; f_info : string }.

(* A list style.  The ordered half reuses `Ast`'s pair, which is what the
   `OrderedList` node carries.  A marker yields a set of these (see "List
   markers" below). *)
Inductive lstyle : Type :=
  | SBullet (c : ascii)
  (* A task marker's style, which keeps `- [ ] a` and `- b` two lists.
     The checkbox is not part of it, so `- [ ]` and `- [x]` are
     siblings. *)
  | STask (c : ascii)
  | SOrd (n : ordered_list_style) (d : ordered_list_delim).

(* The classifier keeps the source token as well as its semantic status.
   The AST needs only [tm_status], but a profile which disables task-list
   semantics must recover the ordinary bullet item's literal prefix exactly,
   including [x] versus [X] and the optional separator after the box. *)
Record task_marker : Type := TaskMarker {
  tm_status : task_status;
  tm_box : ascii;
  tm_sep : option ascii
}.

Definition task_marker_source (m : task_marker) : string :=
  String "[" (String (tm_box m) (String "]"
    (match tm_sep m with Some c => String c EmptyString | None => EmptyString end))).

Definition task_literal_rest (chk : option task_marker) (rest : string) : string :=
  match chk with Some m => task_marker_source m ++ rest | None => rest end.

Local Definition canonical_task_marker (st : task_status) : task_marker :=
  TaskMarker st
    (match st with Complete => "x"%char | Incomplete => " "%char end)
    (Some " "%char).

Definition ols_eqb (a b : ordered_list_style) : bool :=
  match a, b with
  | Decimal, Decimal | LetterUpper, LetterUpper | LetterLower, LetterLower
  | RomanUpper, RomanUpper | RomanLower, RomanLower => true
  | _, _ => false
  end.

Definition old_eqb (a b : ordered_list_delim) : bool :=
  match a, b with
  | RightPeriod, RightPeriod | RightParen, RightParen
  | LeftRightParen, LeftRightParen => true
  | _, _ => false
  end.

Definition lstyle_eqb (a b : lstyle) : bool :=
  match a, b with
  | SBullet x, SBullet y => Ascii.eqb x y
  | STask x, STask y => Ascii.eqb x y
  | SOrd n d, SOrd n' d' => (ols_eqb n n' && old_eqb d d')%bool
  | _, _ => false
  end.

(* What a table-row line contributes: a separator, which carries the
   alignments it sets, or a row of cells, which carries their trimmed
   source.  The head/align assignment is not made here, since a
   separator marks the row *before* it as a header -- that is a fold
   over the rows a table has collected, not a property of a line.  The
   recognizer is under "Table rows" below. *)
Inductive trow : Type :=
  | TSep (aligns : list align)
  | TCells (cells : list string).

(* Decided equality on rows, for the canonical view's check that a line
   scans back as the row it was rendered from. *)
Local Fixpoint aligns_eqb (xs ys : list align) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => (align_eqb x y && aligns_eqb xs' ys')%bool
  | _, _ => false
  end.

Local Fixpoint strs_eqb (xs ys : list string) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => (String.eqb x y && strs_eqb xs' ys')%bool
  | _, _ => false
  end.

Definition trow_eqb (x y : trow) : bool :=
  match x, y with
  | TSep a, TSep b => aligns_eqb a b
  | TCells a, TCells b => strs_eqb a b
  | _, _ => false
  end.

Local Lemma aligns_eqb_eq : forall xs ys, aligns_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; try discriminate; [reflexivity|].
  cbn [aligns_eqb] in H. apply andb_true_iff in H as [Hx Hxs].
  rewrite (align_eqb_eq _ _ Hx), (IH _ Hxs). reflexivity.
Qed.

Local Lemma strs_eqb_eq : forall xs ys, strs_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; try discriminate; [reflexivity|].
  cbn [strs_eqb] in H. apply andb_true_iff in H as [Hx Hxs].
  apply String.eqb_eq in Hx. rewrite Hx, (IH _ Hxs). reflexivity.
Qed.

Lemma trow_eqb_eq : forall x y, trow_eqb x y = true -> x = y.
Proof.
  intros [a|a] [b|b] H; try discriminate; cbn [trow_eqb] in H.
  - rewrite (aligns_eqb_eq _ _ H). reflexivity.
  - rewrite (strs_eqb_eq _ _ H). reflexivity.
Qed.

Inductive line_kind : Type :=
  | KBlank                 (* only whitespace *)
  | KThematic              (* thematic break: 3+ of - or * (mixed ok), ws between *)
  | KFence (f : fence)     (* code fence opener *)
  | KDiv (len : nat) (cls : string)    (* fenced-div opener, with its class *)
  | KQuote (rest : string) (* block-quote prefix, with the line it encloses *)
  | KHeading (level : nat) (rest : string)   (* #+ then ws, with its text *)
  (* A list marker: its candidate styles, its numeral core (empty for a
     bullet), its checkbox if it is a task marker, and the content after
     it.  The checkbox is `Some` exactly when the style set is a task
     style, and it is per *item*: `- [ ]` and `- [x]` are siblings. *)
  | KList (sty : list lstyle) (core : string) (chk : option task_marker)
          (rest : string)
  (* block attribute spec, with the machine's state after this line: it
     may already be complete (`ap_done`) or still want indented
     continuation lines *)
  | KAttr (p : aparser)
  (* a footnote definition's opener: its label (without the `^`) and
     the ordinary block content left on the opener line *)
  | KFoot (label : string) (rest : string)
  (* a reference definition's opening line: its label and the destination
     this line supplies, which later lines may extend *)
  | KRef (label : string) (val : string)
  (* a table row: either a separator, which carries the alignments it
     sets, or a row of cells, which carries their trimmed source *)
  | KRow (r : trow)
  | KText.                 (* anything else: paragraph text *)

(*
Recognizers
===========
*)

(* A thematic-break marker character. *)
Definition is_marker (c : ascii) : bool :=
  Ascii.eqb c "-" || Ascii.eqb c "*".

(* A thematic break: at least three markers, and nothing else but
   whitespace.  Indentation goes through the whitespace branch. *)

Local Fixpoint thematic_count (s : string) (count : nat) : bool :=
  match s with
  | EmptyString => Nat.leb 3 count
  | String c s' =>
      if is_marker c then thematic_count s' (S count)
      else if is_ws c then thematic_count s' count
      else false
  end.

Definition is_thematic (l : string) : bool := thematic_count l 0.

(* Marker and whitespace are disjoint character classes, so a thematic
   count run through an all-whitespace prefix never touches the marker
   branch: it just keeps the count. *)
Local Lemma is_ws_not_marker : forall c, is_ws c = true -> is_marker c = false.
Proof.
  intros c H. unfold is_marker.
  destruct (Ascii.eqb c "-") eqn:E1.
  - apply Ascii.eqb_eq in E1. subst c. discriminate H.
  - destruct (Ascii.eqb c "*") eqn:E2; [|reflexivity].
    apply Ascii.eqb_eq in E2. subst c. discriminate H.
Qed.

Local Lemma thematic_count_ws_prefix :
  forall p l n, is_blank p = true -> thematic_count (p ++ l) n = thematic_count l n.
Proof.
  induction p as [|c p IH]; intros l n H; [reflexivity|].
  cbn [is_blank] in H. apply andb_true_iff in H as [Hc Hp].
  change (String c p ++ l) with (String c (p ++ l)).
  cbn [thematic_count]. rewrite (is_ws_not_marker c Hc), Hc. apply IH, Hp.
Qed.

Local Lemma is_thematic_ws_prefix :
  forall p l, is_blank p = true -> is_thematic (p ++ l) = is_thematic l.
Proof. intros p l H. unfold is_thematic. apply thematic_count_ws_prefix, H. Qed.

(* An underline: one character repeated, with only whitespace around it.
   Which characters underline, and at what length, is a block setting
   (`Step.bunderline`), so this answers for any character.

   A query beside `classify` rather than a `line_kind`, because an
   underline's shapes already have kinds: `---` is `KThematic`, `-` a
   bullet marker, and `===` `KText`. *)
Local Fixpoint all_char (c : ascii) (s : string) : bool :=
  match s with
  | EmptyString => true
  | String a s' => (Ascii.eqb a c && all_char c s')%bool
  end.

Definition underline_of (l : string) : option (ascii * nat) :=
  match strip_trailing_ws (drop_leading_ws l) with
  | EmptyString => None
  | String c s => if all_char c s then Some (c, S (String.length s)) else None
  end.

(* Leading whitespace is dropped first, so an underline survives the
   padding a container prefix adds. *)
Lemma underline_of_ws_prefix :
  forall p l, is_blank p = true -> underline_of (p ++ l) = underline_of l.
Proof.
  intros p l H. unfold underline_of.
  rewrite (drop_leading_ws_ws_prefix p l H). reflexivity.
Qed.

(* Code fences: at least three of one fence character (` or ~), optional
   whitespace, one info token with neither whitespace nor backticks, and
   optional trailing whitespace.  The fence may be indented.  A closing
   line is the same character, at least the opening length, and nothing
   else but whitespace. *)

(* The longest prefix of `s` satisfying `p`, and what is left. *)
Local Fixpoint take_while (p : ascii -> bool) (s : string) : string * string :=
  match s with
  | String c s' =>
      if p c
      then let (a, b) := take_while p s' in (String c a, b)
      else (EmptyString, s)
  | EmptyString => (EmptyString, s)
  end.

Local Lemma take_while_length :
  forall p s, String.length (snd (take_while p s)) <= String.length s.
Proof.
  intros p s. induction s as [|c s' IH]; [reflexivity|].
  cbn [take_while]. destruct (p c); [|reflexivity].
  destruct (take_while p s') as [a b]. cbn [snd String.length] in *. lia.
Qed.

(* Length of the leading run of c, and the rest of the string. *)
Fixpoint count_run (c : ascii) (s : string) : nat * string :=
  match s with
  | String c' s' =>
      if Ascii.eqb c c'
      then let (n, r) := count_run c s' in (S n, r)
      else (O, s)
  | EmptyString => (O, s)
  end.

(* The run count_run measures: `n` copies of `c`.  Fence lines are
   stated with it. *)
Fixpoint char_run (c : ascii) (n : nat) : string :=
  match n with O => EmptyString | S n' => String c (char_run c n') end.

Local Lemma count_char_run : forall c n rest,
  count_run c rest = (O, rest) ->
  count_run c (char_run c n ++ rest) = (n, rest).
Proof.
  intros c n rest Hrest. induction n as [|n IH]; [exact Hrest|].
  cbn [char_run append count_run]. rewrite Ascii.eqb_refl, IH. reflexivity.
Qed.

Local Lemma count_run_split : forall c s n r,
  count_run c s = (n, r) -> s = char_run c n ++ r.
Proof.
  intros c s. induction s as [|c' s IH]; intros n r H.
  - injection H as <- <-. reflexivity.
  - cbn [count_run] in H. destruct (Ascii.eqb c c') eqn:E.
    + apply Ascii.eqb_eq in E. subst c'.
      destruct (count_run c s) as [m r'] eqn:Es. injection H as <- <-.
      rewrite (IH m r' eq_refl). reflexivity.
    + injection H as <- <-. reflexivity.
Qed.

(* A blank string has no run of a non-whitespace character. *)
Local Lemma count_run_blank : forall c s,
  is_ws c = false -> is_blank s = true -> count_run c s = (O, s).
Proof.
  intros c [|w s] Hc Hs; [reflexivity|].
  cbn [is_blank] in Hs. apply andb_true_iff in Hs as [Hw _].
  cbn [count_run]. destruct (Ascii.eqb c w) eqn:E; [|reflexivity].
  apply Ascii.eqb_eq in E. subst w. rewrite Hc in Hw. discriminate.
Qed.

Local Lemma drop_leading_ws_run : forall c n s,
  is_ws c = false -> 0 < n -> drop_leading_ws (char_run c n ++ s) = char_run c n ++ s.
Proof.
  intros c [|n] s Hc Hn; [lia|]. cbn [char_run append drop_leading_ws]. rewrite Hc.
  reflexivity.
Qed.

(* Characters admissible in a fence info string. *)
Definition is_info_char (c : ascii) : bool :=
  negb (is_ws c || Ascii.eqb c "`" || Ascii.eqb c "010").

(* Does this line open a fence, and if so which one? *)
Definition fence_open (l : string) : option fence :=
  match drop_leading_ws l with
  | String c _ as l' =>
      if Ascii.eqb c "`" || Ascii.eqb c "~"
      then
        let (n, r) := count_run c l' in
        if Nat.leb 3 n
        then
          let (info, r') := take_while is_info_char (drop_leading_ws r) in
          if is_blank r' then Some (Fence c n info) else None
        else None
      else None
  | EmptyString => None
  end.

(* Whether this line closes the given fence.  The only test applied to a
   line inside a fence: its content is never classified. *)
Definition fence_close (f : fence) (l : string) : bool :=
  let (n, r) := count_run (f_ch f) (drop_leading_ws l) in
  Nat.leb (f_len f) n && is_blank r.

(* The close test reads the line through `drop_leading_ws`, so a blank
   prefix in front of it is invisible -- a closer closes at any column. *)
Lemma fence_close_ws_prefix :
  forall f p l, is_blank p = true -> fence_close f (p ++ l) = fence_close f l.
Proof.
  intros f p l Hp. unfold fence_close.
  rewrite (drop_leading_ws_ws_prefix p l Hp). reflexivity.
Qed.

(* Fenced divs.  The opener may carry a class and the closer may not, so
   `::: foo` opens a div but never closes one.

   The close test is applied by the open div to every line, as
   `fence_close` is, and never by `classify`; hence no `KDivClose`.  A
   bare `:::` is both an opener and a closer, and the open div's test runs
   first (`step`'s PDiv branch). *)

(* The class token is `[\w_-]*`, narrower than a fence's info string.
   `:::a!` opens no div at all, because the pattern must match to end of
   line. *)
Definition is_class_char (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (Nat.leb 48 n && Nat.leb n 57)      (* 0-9 *)
  || (Nat.leb 65 n && Nat.leb n 90)   (* A-Z *)
  || (Nat.leb 97 n && Nat.leb n 122)  (* a-z *)
  || Ascii.eqb c "_" || Ascii.eqb c "-".

Definition div_open (l : string) : option (nat * string) :=
  match drop_leading_ws l with
  | String c _ as l' =>
      if Ascii.eqb c ":"
      then
        let (n, r) := count_run ":" l' in
        if Nat.leb 3 n
        then let (cls, r') := take_while is_class_char (drop_leading_ws r) in
             if is_blank r' then Some (n, cls) else None
        else None
      else None
  | EmptyString => None
  end.

(* Closes a div opened with `len` colons: at least that many, then only
   whitespace.  The leading `drop_leading_ws` makes a closer visible
   through any indentation, hence through any nesting, where a quote's
   `>` blocks the scan.  `div_uniformity`'s side condition is this
   asymmetry. *)
Definition div_close (len : nat) (l : string) : bool :=
  let (n, r) := count_run ":" (drop_leading_ws l) in
  Nat.leb len n && Nat.leb 3 n && is_blank r.

(* Block quotes: a `>` followed by whitespace or end of line, possibly
   indented.  The prefix is the `>` plus at most one whitespace
   character; the parser classifies the rest again, so nesting comes from
   re-entering `classify`.  `>x` is not a quote. *)
Definition quote_prefix (l : string) : option string :=
  match drop_leading_ws l with
  | String c rest =>
      if Ascii.eqb c ">"
      then match rest with
           | EmptyString => Some EmptyString
           | String c' rest' => if is_ws c' then Some rest' else None
           end
      else None
  | EmptyString => None
  end.

(* The enclosed line is strictly shorter, which is what makes the
   parser's descent into nested quotes terminate. *)
Local Lemma quote_prefix_length :
  forall l rest,
    quote_prefix l = Some rest -> String.length rest < String.length l.
Proof.
  intros l rest H. unfold quote_prefix in H.
  pose proof (drop_leading_ws_length l) as Hle.
  destruct (drop_leading_ws l) as [|c r] eqn:E; [discriminate|].
  destruct (Ascii.eqb c ">"); [|discriminate].
  simpl in Hle.
  destruct r as [|c' r'].
  - injection H as <-. simpl. lia.
  - destruct (is_ws c'); [|discriminate].
    injection H as <-. simpl in *. lia.
Qed.

(* Headings: one or more `#` followed by whitespace or end of line.
   Shaped like quote_prefix, but the text after it is not reclassified: a
   heading's content is inline, so `# > q` is a heading containing
   "> q". *)
Definition heading_open (l : string) : option (nat * string) :=
  let (n, r) := count_run "#" (drop_leading_ws l) in
  if Nat.leb 1 n
  then match r with
       | EmptyString => Some (n, EmptyString)
       | String c r' => if is_ws c then Some (n, r') else None
       end
  else None.

(*
List markers
------------

A marker's numeral is normalized out of its style: `3.` and `4.` both
have the style `1.`.  The container stack compares styles, never
numbers.  The numeral survives only as the marker's `core`, from which
each candidate style's start is decoded (`Marker.with_starts`).

A marker may be ambiguous: `i.` is roman or alpha, so a marker yields a
candidate set, which siblings intersect (`Marker.narrow`).  An empty
intersection ends the list. *)

(* `-x` is not a marker, and `* * *` is a thematic break: `classify` tests
   thematic breaks first.

   The colon is a bullet character: a definition list is an ordinary list
   whose style is `:`, and the term split happens when the list closes.
   `::` is not a marker, since the character after the first colon is not
   whitespace, and `:::` is a div, which `classify` tests first. *)
Local Definition is_bullet (c : ascii) : bool :=
  (Ascii.eqb c "-" || Ascii.eqb c "*" || Ascii.eqb c "+"
   || Ascii.eqb c ":")%char%bool.

(* The bullets a checkbox may follow.  Not the colon: `: [ ] a` is a
   definition item whose term is `[ ] a`. *)
Definition is_task_bullet (c : ascii) : bool :=
  (Ascii.eqb c "-" || Ascii.eqb c "*" || Ascii.eqb c "+")%char%bool.

(*
Marker character classes
------------------------
*)

Definition in_range (lo hi : nat) (c : ascii) : bool :=
  let n := nat_of_ascii c in (Nat.leb lo n && Nat.leb n hi)%bool.

Definition is_digit (c : ascii) : bool := in_range 48 57 c.
Definition is_lower (c : ascii) : bool := in_range 97 122 c.
Definition is_upper (c : ascii) : bool := in_range 65 90 c.
Definition is_alnum (c : ascii) : bool :=
  (is_digit c || is_lower c || is_upper c)%bool.

(* A callout header is recognized on the content of a newly opened quote,
   before that content is parsed as djot markup.  The separator after the
   closing bracket protects links, spans and reference definitions.  Its
   title is a source suffix, retaining trailing whitespace so the located
   inline parser can recover the original columns. *)
Definition callout_kind_char (c : ascii) : bool :=
  (is_alnum c || Ascii.eqb c "-" || Ascii.eqb c "_")%bool.

Definition callout_sep (c : ascii) : bool :=
  (Ascii.eqb c " " || Ascii.eqb c "009")%bool.

Definition callout_header (s : string)
  : option (string * option callout_fold * string) :=
  match s with
  | String a (String b rest) =>
      if (Ascii.eqb a "[" && Ascii.eqb b "!")%bool then
      let '(kind, rest) := take_while callout_kind_char rest in
      match kind, rest with
      | EmptyString, _ => None
      | _, String "]" tail =>
          let '(fold, tail) :=
            match tail with
            | String "+" more => (Some FoldExpanded, more)
            | String "-" more => (Some FoldCollapsed, more)
            | String _ _ => (None, tail)
            | EmptyString => (None, EmptyString)
            end in
          match tail with
          | EmptyString => Some (kind, fold, EmptyString)
          | String c title =>
              if callout_sep c then
                Some (kind, fold, drop_leading_ws title)
              else None
          end
      | _, _ => None
      end
      else None
  | _ => None
  end.

Lemma callout_header_other_prefix :
  forall s, (forall rest, s <> "[!" ++ rest) -> callout_header s = None.
Proof.
  intros s H. destruct s as [|a s]; [reflexivity|].
  destruct s as [|b s]; [reflexivity|].
  cbn [callout_header].
  destruct (Ascii.eqb a "[") eqn:Ha;
    destruct (Ascii.eqb b "!") eqn:Hb; cbn [andb]; try reflexivity.
  - apply Ascii.eqb_eq in Ha. apply Ascii.eqb_eq in Hb. subst.
    exfalso. apply (H s). reflexivity.
Qed.

(* The roman digits. *)
Definition is_roman_lo (c : ascii) : bool :=
  (Ascii.eqb c "i" || Ascii.eqb c "v" || Ascii.eqb c "x" || Ascii.eqb c "l"
   || Ascii.eqb c "c" || Ascii.eqb c "d" || Ascii.eqb c "m")%char%bool.

Definition is_roman_up (c : ascii) : bool :=
  (Ascii.eqb c "I" || Ascii.eqb c "V" || Ascii.eqb c "X" || Ascii.eqb c "L"
   || Ascii.eqb c "C" || Ascii.eqb c "D" || Ascii.eqb c "M")%char%bool.

Fixpoint str_forallb (p : ascii -> bool) (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => (p c && str_forallb p s')%bool
  end.

(*
Marker shape and candidate styles
---------------------------------
*)

(* An ordered marker's two halves: an alphanumeric `core` and a
   delimiter shape.  `(` forces the enclosed form, which is why this is
   one function rather than a delimiter test after a scan. *)
Local Definition marker_shape (s : string)
  : option (string * ordered_list_delim * string) :=
  match s with
  | EmptyString => None
  | String c s' =>
      if Ascii.eqb c "("
      then
        let (core, r) := take_while is_alnum s' in
        match r with
        | String c' r' =>
            if Ascii.eqb c' ")" then Some (core, LeftRightParen, r') else None
        | EmptyString => None
        end
      else
        let (core, r) := take_while is_alnum s in
        match r with
        | String c' r' =>
            if Ascii.eqb c' "." then Some (core, RightPeriod, r')
            else if Ascii.eqb c' ")" then Some (core, RightParen, r')
            else None
        | EmptyString => None
        end
  end.

Local Lemma marker_shape_length :
  forall s core d r,
    marker_shape s = Some (core, d, r) ->
    String.length r < String.length s.
Proof.
  intros s core d r H. unfold marker_shape in H.
  destruct s as [|c s']; [discriminate|].
  destruct (Ascii.eqb c "(").
  - pose proof (take_while_length is_alnum s') as Hle.
    destruct (take_while is_alnum s') as [a b].
    cbn [snd] in Hle.
    destruct b as [|c' b']; [discriminate|].
    destruct (Ascii.eqb c' ")"); [|discriminate].
    injection H as _ _ <-. cbn [String.length] in *. lia.
  - pose proof (take_while_length is_alnum (String c s')) as Hle.
    destruct (take_while is_alnum (String c s')) as [a b].
    cbn [snd] in Hle.
    destruct b as [|c' b']; [discriminate|].
    destruct (Ascii.eqb c' ".").
    + injection H as _ _ <-. cbn [String.length] in *. lia.
    + destruct (Ascii.eqb c' ")"); [|discriminate].
      injection H as _ _ <-. cbn [String.length] in *. lia.
Qed.

(* The longest decimal marker core.  Eighteen digits keep every decimal
   start below 10^18, inside a 63-bit integer, which is what the extracted
   parser represents `nat` by; `Marker.dec_start_bound` states it. *)
Definition dec_digits_max : nat := 18.

(* The candidate styles of a core that `marker_shape` split off.  A single
   roman character is ambiguous (`i.` is roman or alpha); a longer
   all-roman core is roman only.  An empty core, as in `().`, is not a
   marker, and is excluded before `str_forallb` would accept it
   vacuously.  A decimal core longer than `dec_digits_max` is not a
   marker either. *)
Definition styles_of_core (core : string) (d : ordered_list_delim)
  : list lstyle :=
  match core with
  | EmptyString => []
  | String c rest =>
      if str_forallb is_digit core then
        if Nat.leb (String.length core) dec_digits_max then [SOrd Decimal d]
        else []
      else match rest with
           | EmptyString =>
               if is_roman_lo c then [SOrd RomanLower d; SOrd LetterLower d]
               else if is_roman_up c then [SOrd RomanUpper d; SOrd LetterUpper d]
               else if is_lower c then [SOrd LetterLower d]
               else if is_upper c then [SOrd LetterUpper d]
               else []
           | _ =>
               if str_forallb is_roman_lo core then [SOrd RomanLower d]
               else if str_forallb is_roman_up core then [SOrd RomanUpper d]
               else []
           end
  end.

(* The checkbox of a task marker, and what is left of the line after it.
   It is read after the bullet's one space: `task_check` sees `[x] a`,
   never `- [x] a`.  Exactly one space before the bracket and whitespace
   or end of line after it, so `-  [ ] a` and `- [ ]a` are plain
   bullets. *)
Local Definition box_status (c : ascii) : option task_status :=
  if Ascii.eqb c " " then Some Incomplete
  else if (Ascii.eqb c "x" || Ascii.eqb c "X")%char%bool then Some Complete
  else None.

Local Definition task_check (l : string) : option (task_marker * string) :=
  match l with
  | String c0 (String b (String c2 r)) =>
      if (Ascii.eqb c0 "[" && Ascii.eqb c2 "]")%char%bool
      then match box_status b with
           | None => None
           | Some st =>
               match r with
               | EmptyString => Some (TaskMarker st b None, EmptyString)
               | String c' r' =>
                   if is_ws c' then Some (TaskMarker st b (Some c'), r') else None
               end
           end
      else None
  | _ => None
  end.

(* A list marker: its candidate styles, its numeral core (empty for a
   bullet, which has no number), its checkbox if it has one, and the
   content after it.  Same marker-then-at-most-one-space shape as quotes
   and headings. *)
Definition list_marker (l : string)
  : option (list lstyle * string * option task_marker * string) :=
  match drop_leading_ws l with
  | EmptyString => None
  | String c rest =>
      if is_bullet c
      then match rest with
           | EmptyString => Some ([SBullet c], EmptyString, None, EmptyString)
           | String c' rest' =>
               if is_ws c'
               then match (if is_task_bullet c then task_check rest' else None) with
                    | Some (chk, r) => Some ([STask c], EmptyString, Some chk, r)
                    | None => Some ([SBullet c], EmptyString, None, rest')
                    end
               else None
           end
      else
        match marker_shape (String c rest) with
        | None => None
        | Some (core, d, r) =>
            match styles_of_core core d with
            | [] => None
            | sty =>
                match r with
                | EmptyString => Some (sty, core, None, EmptyString)
                | String c' r' =>
                    if is_ws c' then Some (sty, core, None, r') else None
                end
            end
        end
  end.

(* The colon marker.  What a definition list closes to is decided in
   `Step.styles_list`, and the term split in `Ast.def_item`. *)
Example marker_colon :
  list_marker ": a" = Some ([SBullet ":"%char], EmptyString, None, "a"%string).
Proof. reflexivity. Qed.

Example marker_colon_tab :
  list_marker ":	a" = Some ([SBullet ":"%char], EmptyString, None, "a"%string).
Proof. reflexivity. Qed.

Example marker_colon_bare :
  list_marker ":" = Some ([SBullet ":"%char], EmptyString, None, EmptyString).
Proof. reflexivity. Qed.

(* Content is not stripped past the one marker space, as for any bullet. *)
Example marker_colon_wide :
  list_marker ":   a" = Some ([SBullet ":"%char], EmptyString, None, "  a"%string).
Proof. reflexivity. Qed.

Example marker_colon_tight : list_marker ":a" = None.
Proof. reflexivity. Qed.

(* The second colon is not the whitespace a marker needs.  Three colons
   are a div, which `classify` decides before it reaches this. *)
Example marker_two_colons : list_marker ":: a" = None.
Proof. reflexivity. Qed.

(* The task marker replaces the bullet marker rather than extending it:
   the style is `STask` and the residue starts after the bracket. *)
Example marker_task_unchecked :
  list_marker "- [ ] a"
  = Some ([STask "-"%char], EmptyString,
          Some (TaskMarker Incomplete " "%char (Some " "%char)), "a"%string).
Proof. reflexivity. Qed.

Example marker_task_checked :
  list_marker "- [x] a"
  = Some ([STask "-"%char], EmptyString,
          Some (TaskMarker Complete "x"%char (Some " "%char)), "a"%string).
Proof. reflexivity. Qed.

Example marker_task_checked_upper :
  list_marker "* [X] a"
  = Some ([STask "*"%char], EmptyString,
          Some (TaskMarker Complete "X"%char (Some " "%char)), "a"%string).
Proof. reflexivity. Qed.

(* A marker at end of line is a task item with no content. *)
Example marker_task_bare :
  list_marker "- [ ]"
  = Some ([STask "-"%char], EmptyString,
          Some (TaskMarker Incomplete " "%char None), EmptyString).
Proof. reflexivity. Qed.

(* Content is not stripped past the marker's one space, as for a bullet. *)
Example marker_task_wide :
  list_marker "- [ ]  a"
  = Some ([STask "-"%char], EmptyString,
          Some (TaskMarker Incomplete " "%char (Some " "%char)), " a"%string).
Proof. reflexivity. Qed.

(* The three shapes that are a plain bullet instead: no space after the
   bracket, two spaces before it, and a character that is not a box. *)
Example marker_task_tight :
  list_marker "- [ ]a"
  = Some ([SBullet "-"%char], EmptyString, None, "[ ]a"%string).
Proof. reflexivity. Qed.

Example marker_task_wide_bullet :
  list_marker "-  [ ] a"
  = Some ([SBullet "-"%char], EmptyString, None, " [ ] a"%string).
Proof. reflexivity. Qed.

Example marker_task_bad_box :
  list_marker "- [y] a"
  = Some ([SBullet "-"%char], EmptyString, None, "[y] a"%string).
Proof. reflexivity. Qed.

(* Only a bullet takes a checkbox. *)
Example marker_task_ordered :
  list_marker "1. [ ] a"
  = Some ([SOrd Decimal RightPeriod], "1"%string, None, "[ ] a"%string).
Proof. reflexivity. Qed.

Example marker_task_colon :
  list_marker ": [ ] a"
  = Some ([SBullet ":"%char], EmptyString, None, "[ ] a"%string).
Proof. reflexivity. Qed.

(* A checkbox is three characters and an optional separator, so what it
   leaves is shorter than what it was given. *)
Local Lemma task_check_length :
  forall l st r,
    task_check l = Some (st, r) -> String.length r < String.length l.
Proof.
  intros [|c0 [|c1 [|c2 rest]]] st r H; try (cbn in H; discriminate H).
  cbn [task_check] in H.
  destruct (Ascii.eqb c0 "[" && Ascii.eqb c2 "]")%char%bool; [|discriminate H].
  destruct (box_status c1); [|discriminate H].
  destruct rest as [|c' rest'].
  - injection H as _ <-. simpl. lia.
  - destruct (is_ws c'); [|discriminate H].
    injection H as _ <-. simpl. lia.
Qed.

Local Lemma task_check_source :
  forall l m r, task_check l = Some (m, r) -> l = task_marker_source m ++ r.
Proof.
  intros [|c0 [|c1 [|c2 rest]]] m r H; try (cbn in H; discriminate H).
  cbn [task_check] in H.
  destruct (Ascii.eqb c0 "[" && Ascii.eqb c2 "]")%char%bool eqn:E;
    [|discriminate H].
  apply andb_true_iff in E as [E0 E2].
  apply Ascii.eqb_eq in E0, E2. subst c0 c2.
  destruct (box_status c1) eqn:Es; [|discriminate H].
  destruct rest as [|c' rest'].
  - injection H as <- <-. reflexivity.
  - destruct (is_ws c') eqn:Ew; [|discriminate H].
    injection H as <- <-. reflexivity.
Qed.

(* Like quote_prefix_length: the content after a list marker is strictly
   shorter than the line, which is what makes the parser's descent into
   a list item terminate. *)
Local Lemma list_marker_length :
  forall l sty core chk rest,
    list_marker l = Some (sty, core, chk, rest) ->
    String.length rest < String.length l.
Proof.
  intros l sty core chk rest H. unfold list_marker in H.
  pose proof (drop_leading_ws_length l) as Hle.
  destruct (drop_leading_ws l) as [|c r] eqn:E; [discriminate|].
  destruct (is_bullet c).
  - simpl in Hle.
    destruct r as [|c' r'].
    + injection H as _ _ _ <-. simpl. lia.
    + destruct (is_ws c'); [|discriminate].
      destruct (if is_task_bullet c then task_check r' else None)
        as [[st tr]|] eqn:Et.
      * assert (Ht : String.length tr < String.length r').
        { destruct (is_task_bullet c); [|discriminate Et].
          exact (task_check_length r' st tr Et). }
        injection H as _ _ _ <-. simpl in *. lia.
      * injection H as _ _ _ <-. simpl in *. lia.
  - pose proof (marker_shape_length (String c r)) as Hms.
    destruct (marker_shape (String c r)) as [[[core' d] r0]|] eqn:Em;
      [|discriminate].
    specialize (Hms _ _ _ eq_refl).
    destruct (styles_of_core core' d) as [|s0 ss] eqn:Es; [discriminate|].
    destruct r0 as [|c' r0'].
    + injection H as _ _ _ <-. simpl in *. lia.
    + destruct (is_ws c'); [|discriminate].
      injection H as _ _ _ <-. simpl in *. lia.
Qed.

Local Lemma list_marker_literal_length :
  forall l sty core chk rest,
    list_marker l = Some (sty, core, chk, rest) ->
    String.length (task_literal_rest chk rest) < String.length l.
Proof.
  intros l sty core chk rest H. unfold list_marker in H.
  pose proof (drop_leading_ws_length l) as Hle.
  destruct (drop_leading_ws l) as [|c r] eqn:E; [discriminate|].
  destruct (is_bullet c).
  - simpl in Hle. destruct r as [|c' r'].
    + injection H as _ _ <- <-. cbn [task_literal_rest]. simpl. lia.
    + destruct (is_ws c'); [|discriminate].
      destruct (if is_task_bullet c then task_check r' else None)
        as [[m tr]|] eqn:Et.
      * injection H as _ _ <- <-.
        unfold task_literal_rest.
        assert (Hr : r' = task_marker_source m ++ tr).
        { destruct (is_task_bullet c); [exact (task_check_source _ _ _ Et)|discriminate Et]. }
        rewrite <- Hr. simpl in *. lia.
      * injection H as _ _ <- <-. cbn [task_literal_rest]. simpl in *. lia.
  - pose proof (marker_shape_length (String c r)) as Hms.
    destruct (marker_shape (String c r)) as [[[core' d] r0]|] eqn:Em;
      [|discriminate].
    specialize (Hms _ _ _ eq_refl).
    destruct (styles_of_core core' d) as [|s0 ss] eqn:Es; [discriminate|].
    destruct r0 as [|c' r0'].
    + injection H as _ _ <- <-. cbn [task_literal_rest]. simpl in *. lia.
    + destruct (is_ws c'); [|discriminate].
      injection H as _ _ <- <-. cbn [task_literal_rest]. simpl in *. lia.
Qed.

(*
Reference definitions
=====================

`[label]: destination`.  It yields a `RefDef` block, which renders to no
HTML; the document's reference map is derived from it.  The destination
may continue on following indented lines, so it opens a container state
(`Step.PRef`) rather than emitting on sight.
*)

(* The label: everything up to the first `]`, and the line after it.
   Only the bracket is excluded, so `[a[b]: u` defines `a[b`. *)
Local Fixpoint ref_label (s : string) : option (string * string) :=
  match s with
  | EmptyString => None
  | String c rest =>
      if Ascii.eqb c "]"
      then Some (EmptyString, rest)
      else match ref_label rest with
           | None => None
           | Some (lbl, tail) => Some (String c lbl, tail)
           end
  end.

(* What may follow the `:`: nothing, or whitespace and then one
   whitespace-free run to end of line.  So `[a]:u` and `[a]: u ` are not
   definitions. *)
Local Definition ref_value (s : string) : option string :=
  match s with
  | EmptyString => Some EmptyString
  | String c _ =>
      if is_ws c
      then let t := drop_leading_ws s in
           if no_ws t then Some t else None
      else None
  end.

(* A label the footnote container claims first: `^` and at least one more
   character.  `[^]: u` is a reference definition of the label `^`. *)
Definition is_footnote_label (lbl : string) : bool :=
  match lbl with
  | String "^"%char (String _ _) => true
  | _ => false
  end.

(* `[^label]: body`.  Unlike a reference definition, the body is ordinary
   block content and may contain spaces; only the one whitespace byte
   after the colon is removed. *)
Definition foot_open (l : string) : option (string * string) :=
  match drop_leading_ws l with
  | String c (String h rest) =>
      if negb (Ascii.eqb c "[") then None
      else if negb (Ascii.eqb h "^") then None
      else match ref_label rest with
           | Some (lbl, String col after) =>
               if negb (Ascii.eqb col ":") then None
               else if negb (nonempty_str lbl) then None
               else match after with
                    | EmptyString => Some (lbl, EmptyString)
                    | String w body =>
                        if is_ws w then Some (lbl, body) else None
                    end
           | _ => None
           end
  | _ => None
  end.

Local Lemma foot_open_ws_prefix :
  forall p l, is_blank p = true -> foot_open (p ++ l) = foot_open l.
Proof.
  intros p l Hp. unfold foot_open.
  rewrite (drop_leading_ws_ws_prefix p l Hp). reflexivity.
Qed.

(* A label can be written back between brackets. *)
Local Lemma ref_label_no_bracket :
  forall s lbl tail,
    ref_label s = Some (lbl, tail) -> no_char "]"%char lbl = true.
Proof.
  induction s as [|c s IH]; intros lbl tail H; [discriminate|].
  cbn [ref_label] in H. destruct (Ascii.eqb c "]") eqn:E.
  - injection H as <- _. reflexivity.
  - destruct (ref_label s) as [[lbl' tail']|] eqn:Er; [|discriminate].
    injection H as <- _. cbn [no_char]. rewrite E.
    apply (IH lbl' tail' eq_refl).
Qed.

Lemma foot_open_label_ok :
  forall l lbl rest,
    foot_open l = Some (lbl, rest) ->
    (nonempty_str lbl && no_char "]"%char lbl)%bool = true.
Proof.
  intros l lbl body H. unfold foot_open in H.
  destruct (drop_leading_ws l) as [|c [|h s]]; try discriminate.
  destruct (Ascii.eqb c "["); cbn [negb] in H; [|discriminate].
  destruct (Ascii.eqb h "^"); cbn [negb] in H; [|discriminate].
  destruct (ref_label s) as [[lbl' [|col after]]|] eqn:Er; try discriminate.
  destruct (Ascii.eqb col ":"); cbn [negb] in H; [|discriminate].
  destruct (nonempty_str lbl') eqn:Hne; cbn [negb] in H; [|discriminate].
  destruct after as [|w tail].
  - injection H as <- <-. rewrite Hne, andb_true_l.
    apply (ref_label_no_bracket s lbl' _ Er).
  - destruct (is_ws w); [|discriminate].
    injection H as <- <-. rewrite Hne, andb_true_l.
    apply (ref_label_no_bracket s lbl' _ Er).
Qed.

Local Lemma ref_label_tail_length :
  forall s lbl tail,
    ref_label s = Some (lbl, tail) -> String.length tail < String.length s.
Proof.
  induction s as [|c s IH]; intros lbl tail H; [discriminate|].
  cbn [ref_label] in H. destruct (Ascii.eqb c "]").
  - injection H as _ <-. cbn. lia.
  - destruct (ref_label s) as [[lbl' tail']|] eqn:E; [|discriminate].
    injection H as _ <-. specialize (IH lbl' tail' eq_refl). cbn. lia.
Qed.

Local Lemma foot_open_length :
  forall l lbl rest,
    foot_open l = Some (lbl, rest) -> String.length rest < String.length l.
Proof.
  intros l lbl body H. unfold foot_open in H.
  pose proof (drop_leading_ws_length l) as Hle.
  destruct (drop_leading_ws l) as [|c [|h s]] eqn:Ed; try discriminate.
  destruct (Ascii.eqb c "["); cbn [negb] in H; [|discriminate].
  destruct (Ascii.eqb h "^"); cbn [negb] in H; [|discriminate].
  destruct (ref_label s) as [[lbl' [|col after]]|] eqn:Er; try discriminate.
  pose proof (ref_label_tail_length s lbl' (String col after) Er) as Hr.
  destruct (Ascii.eqb col ":"); cbn [negb] in H; [|discriminate].
  destruct (nonempty_str lbl'); cbn [negb] in H; [|discriminate].
  destruct after as [|w tail].
  - injection H as _ <-. cbn in *. lia.
  - destruct (is_ws w); [|discriminate].
    injection H as _ <-. cbn in *. lia.
Qed.

(* Spelled with `Ascii.eqb` rather than character patterns: a literal
   pattern compiles to a tree of bit matches that no proof can `destruct`
   in one step. *)
Definition ref_open (l : string) : option (string * string) :=
  match drop_leading_ws l with
  | EmptyString => None
  | String c rest =>
      if negb (Ascii.eqb c "[") then None
      else
        match ref_label rest with
        | None => None
        | Some (_, EmptyString) => None
        | Some (lbl, String c' after) =>
            if negb (Ascii.eqb c' ":") then None
            else if is_footnote_label lbl then None
            else match ref_value after with
                 | Some v => Some (lbl, v)
                 | None => None
                 end
        end
  end.

Lemma ref_open_label_ok :
  forall l lbl v,
    ref_open l = Some (lbl, v) ->
    (no_char "]"%char lbl && negb (is_footnote_label lbl))%bool = true.
Proof.
  intros l lbl v H. unfold ref_open in H.
  destruct (drop_leading_ws l) as [|c rest]; [discriminate|].
  destruct (Ascii.eqb c "[") eqn:Ec; cbn [negb] in H; [|discriminate].
  destruct (ref_label rest) as [[lbl' [|c' after]]|] eqn:Er; try discriminate.
  destruct (Ascii.eqb c' ":") eqn:Ecol; cbn [negb] in H; [|discriminate].
  destruct (is_footnote_label lbl') eqn:Ef; [discriminate|].
  destruct (ref_value after) as [v'|] eqn:Ev; [|discriminate].
  injection H as <- <-. rewrite Ef, andb_true_r.
  apply (ref_label_no_bracket rest lbl' _ Er).
Qed.

Lemma ref_open_value_no_ws :
  forall l lbl v, ref_open l = Some (lbl, v) -> no_ws v = true.
Proof.
  intros l lbl v H. unfold ref_open in H.
  destruct (drop_leading_ws l) as [|c rest]; [discriminate|].
  destruct (Ascii.eqb c "["); cbn [negb] in H; [|discriminate].
  destruct (ref_label rest) as [[lbl' [|c' after]]|] eqn:Er; try discriminate.
  destruct (Ascii.eqb c' ":"); cbn [negb] in H; [|discriminate].
  destruct (is_footnote_label lbl'); [discriminate|].
  destruct (ref_value after) as [v'|] eqn:Ev; [|discriminate].
  injection H as _ <-. unfold ref_value in Ev.
  destruct after as [|ca after']; [injection Ev as <-; reflexivity|].
  destruct (is_ws ca); [|discriminate].
  destruct (no_ws (drop_leading_ws (String ca after'))) eqn:En; [|discriminate].
  injection Ev as <-. exact En.
Qed.

(* Leading whitespace is invisible to the recognizer, as it is to every
   other one here: the opener's column is recorded by the parser, from
   `indent_of`, not by the classification. *)
Local Lemma ref_open_ws_prefix :
  forall p l, is_blank p = true -> ref_open (p ++ l) = ref_open l.
Proof.
  intros p l Hp. unfold ref_open. rewrite (drop_leading_ws_ws_prefix p l Hp).
  reflexivity.
Qed.

(*
Table rows
==========

A row is a line whose first and last non-space characters are `|`, with
at least two bars.  Only whitespace may follow the final bar, so
`| a | x` is a paragraph.  A row is either a separator, whose cells set
the columns' alignment, or a row of cells; the separator is tried first.
*)

(* A separator cell: an optional `:`, one or more `-`, an optional `:`,
   then whitespace, then the bar that ends it and the whitespace after
   that bar.  The leading whitespace of a cell belongs to the *previous*
   cell's match, which is why `| :- |` is not a separator while
   `|:-| -: |` is: the first cell has no previous match to eat its
   space. *)
Definition separator_alignment (left right : bool) : align :=
  match left, right with
  | true, true => AlignCenter
  | true, false => AlignLeft
  | false, true => AlignRight
  | false, false => AlignDefault
  end.

(* One separator cell, from just after the bar that opens it.  Returns
   its alignment and what follows the bar that closes it. *)
Local Definition sep_cell (s : string) : option (align * string) :=
  let (left, s1) :=
    match s with
    | String c r => if Ascii.eqb c ":" then (true, r) else (false, s)
    | EmptyString => (false, s)
    end in
  match count_run "-" s1 with
  | (O, _) => None
  | (_, s2) =>
      let (right, s3) :=
        match s2 with
        | String c r => if Ascii.eqb c ":" then (true, r) else (false, s2)
        | EmptyString => (false, s2)
        end in
      match drop_leading_ws s3 with
      | String c r =>
          if Ascii.eqb c "|"
          then Some (separator_alignment left right, drop_leading_ws r)
          else None
      | EmptyString => None
      end
  end.

(* The cells of a separator line, from just after its opening bar.  Fuel
   is the string's length: every cell consumes at least the bar that
   ends it. *)
Local Fixpoint sep_cells_fuel (n : nat) (s : string) : option (list align) :=
  match n with
  | O => None
  | S n' =>
      match s with
      | EmptyString => Some []
      | _ =>
          match sep_cell s with
          | None => None
          | Some (a, rest) =>
              match sep_cells_fuel n' rest with
              | None => None
              | Some rest' => Some (a :: rest')
              end
          end
      end
  end.

Local Definition sep_cells (s : string) : option (list align) :=
  sep_cells_fuel (S (String.length s)) s.

(* A separator cell as `sep_cell` reads it: an optional `:`, `n` dashes,
   an optional `:`, whitespace `w`, and the bar that ends it. *)
Definition separator_colon (present : bool) (s : string) : string :=
  if present then String ":" s else s.

Definition separator_cell_text (left right : bool) (n : nat) (w : string)
  : string :=
  separator_colon left (char_run "-" n ++ separator_colon right (w ++ "|")).

Local Lemma separator_cell_text_app : forall left right n w rest,
  separator_cell_text left right n w ++ rest =
  separator_colon left (char_run "-" n ++ separator_colon right (w ++ "|" ++ rest)).
Proof.
  intros [] [] n w rest; unfold separator_cell_text; cbn [separator_colon append];
    rewrite ?append_assoc; cbn [append]; rewrite ?append_assoc; reflexivity.
Qed.

(* A string that starts with whitespace has no colon or dash first. *)
Local Lemma separator_ws_head : forall right w rest,
  is_blank w = true ->
  match separator_colon right (w ++ "|" ++ rest) with
  | String c r => if Ascii.eqb c ":" then (true, r)
                  else (false, separator_colon right (w ++ "|" ++ rest))
  | EmptyString => (false, separator_colon right (w ++ "|" ++ rest))
  end = (right, w ++ "|" ++ rest)
  /\ count_run "-" (separator_colon right (w ++ "|" ++ rest))
     = (O, separator_colon right (w ++ "|" ++ rest)).
Proof.
  intros right w rest Hw. destruct right; [split; reflexivity|].
  destruct w as [|c w]; [split; reflexivity|].
  cbn [is_blank] in Hw. apply andb_true_iff in Hw as [Hc _].
  cbn [separator_colon append count_run].
  split; [destruct (Ascii.eqb c ":") eqn:E|destruct (Ascii.eqb "-" c) eqn:E];
    try reflexivity; apply Ascii.eqb_eq in E; subst c; discriminate.
Qed.

(** The four alignment cases, for every positive dash width, any
    whitespace before the closing bar, and every position in a separator
    row.  The returned suffix is what the scan passes to the next cell. *)
Theorem separator_cell_alignment : forall left right n w rest,
  is_blank w = true ->
  sep_cell (separator_cell_text left right (S n) w ++ rest) =
    Some (separator_alignment left right, drop_leading_ws rest).
Proof.
  intros left right n w rest Hw.
  destruct (separator_ws_head right w rest Hw) as [Hr Hd].
  rewrite separator_cell_text_app. unfold sep_cell.
  replace (match separator_colon left (char_run "-" (S n) ++
                                       separator_colon right (w ++ "|" ++ rest)) with
           | String c r => if Ascii.eqb c ":" then (true, r) else (false, _)
           | EmptyString => (false, _)
           end)
    with (left, char_run "-" (S n) ++ separator_colon right (w ++ "|" ++ rest))
    by (destruct left; reflexivity).
  rewrite (count_char_run "-" (S n) _ Hd), Hr.
  rewrite (drop_leading_ws_ws_prefix w _ Hw). reflexivity.
Qed.

Local Lemma separator_cell_text_head : forall a b n w rest,
  exists c s, separator_cell_text a b (S n) w ++ rest = String c s /\
              is_ws c = false.
Proof.
  intros [] b n w rest; unfold separator_cell_text, separator_colon;
    cbn [char_run append]; eexists _, _; split; reflexivity.
Qed.

Local Lemma drop_leading_ws_separator_cell : forall a b n w rest,
  drop_leading_ws (separator_cell_text a b (S n) w ++ rest) =
  separator_cell_text a b (S n) w ++ rest.
Proof.
  intros a b n w rest.
  destruct (separator_cell_text_head a b n w rest) as (c & s & E & Hc).
  rewrite E. cbn [drop_leading_ws]. rewrite Hc. reflexivity.
Qed.

(* The cells after the first, each with the whitespace before it.  Each
   width is stored as its predecessor, so every cell has a positive dash
   run. *)
Fixpoint separator_text (cells : list (string * bool * bool * nat * string))
  : string :=
  match cells with
  | [] => EmptyString
  | (w0, a, b, n, w) :: rest =>
      w0 ++ separator_cell_text a b (S n) w ++ separator_text rest
  end.

Definition separator_alignments (cells : list (string * bool * bool * nat * string))
  : list align :=
  map (fun '(_, a, b, _, _) => separator_alignment a b) cells.

Definition separator_ws_ok (cell : string * bool * bool * nat * string) : Prop :=
  let '(w0, _, _, _, w) := cell in is_blank w0 = true /\ is_blank w = true.

Local Lemma sep_cells_fuel_step : forall fuel c s a rest aligns,
  sep_cell (String c s) = Some (a, rest) ->
  sep_cells_fuel fuel rest = Some aligns ->
  sep_cells_fuel (S fuel) (String c s) = Some (a :: aligns).
Proof.
  intros fuel c s a rest aligns Hcell Hrest.
  cbn [sep_cells_fuel]. rewrite Hcell, Hrest. reflexivity.
Qed.

Local Lemma separator_cells_fuel : forall cells a b n w,
  is_blank w = true -> Forall separator_ws_ok cells ->
  sep_cells_fuel (S (S (length cells)))
    (separator_cell_text a b (S n) w ++ separator_text cells) =
  Some (separator_alignment a b :: separator_alignments cells).
Proof.
  induction cells as [|[[[[w0 a'] b'] n'] w'] cells IH]; intros a b n w Hw Hc.
  - destruct (separator_cell_text_head a b n w EmptyString) as (c & s & E & _).
    cbn [separator_text]. rewrite E.
    apply (sep_cells_fuel_step _ _ _ _ EmptyString); [|reflexivity].
    rewrite <- E, (separator_cell_alignment a b n w EmptyString Hw). reflexivity.
  - inversion Hc as [|? ? Hx Hcs]; subst. destruct Hx as [Hw0 Hw'].
    destruct (separator_cell_text_head a b n w
                (separator_text ((w0, a', b', n', w') :: cells)))
      as (c & s & E & _).
    rewrite E.
    apply (sep_cells_fuel_step _ _ _ _
             (separator_cell_text a' b' (S n') w' ++ separator_text cells)).
    + rewrite <- E, (separator_cell_alignment a b n w _ Hw). cbn [separator_text].
      rewrite (drop_leading_ws_ws_prefix w0 _ Hw0), drop_leading_ws_separator_cell.
      reflexivity.
    + exact (IH a' b' n' w' Hw' Hcs).
Qed.

Local Lemma sep_cells_fuel_more : forall fuel extra s aligns,
  sep_cells_fuel fuel s = Some aligns ->
  sep_cells_fuel (fuel + extra) s = Some aligns.
Proof.
  induction fuel as [|fuel IH]; intros extra s aligns H; [discriminate|].
  destruct s as [|c s].
  - destruct aligns; inversion H; subst. destruct extra; reflexivity.
  - cbn [sep_cells_fuel] in H.
    destruct (sep_cell (String c s)) as [[a rest]|] eqn:E;
      [|discriminate].
    destruct (sep_cells_fuel fuel rest) as [xs|] eqn:Er;
      [|discriminate].
    inversion H; subst aligns.
    replace (S fuel + extra) with (S (fuel + extra)) by lia.
    cbn [sep_cells_fuel]. rewrite E.
    rewrite (IH extra rest xs Er). reflexivity.
Qed.

Local Lemma separator_cell_text_length : forall a b n w,
  2 <= String.length (separator_cell_text a b (S n) w).
Proof.
  intros [] [] n w; unfold separator_cell_text, separator_colon;
    cbn [char_run append String.length];
    rewrite ?length_append; cbn [String.length]; lia.
Qed.

Local Lemma separator_text_length : forall cells,
  length cells <= String.length (separator_text cells).
Proof.
  induction cells as [|[[[[w0 a] b] n] w] cells IH]; [cbn; lia|].
  cbn [separator_text length]. rewrite !length_append.
  pose proof (separator_cell_text_length a b n w). lia.
Qed.

Theorem separator_row_alignments : forall a b n w cells,
  is_blank w = true -> Forall separator_ws_ok cells ->
  sep_cells (separator_cell_text a b (S n) w ++ separator_text cells) =
    Some (separator_alignment a b :: separator_alignments cells).
Proof.
  intros a b n w cells Hw Hc. unfold sep_cells.
  pose proof (separator_cell_text_length a b n w).
  pose proof (separator_text_length cells).
  rewrite length_append.
  replace (S (String.length (separator_cell_text a b (S n) w) +
              String.length (separator_text cells)))
    with (S (S (length cells)) +
          (String.length (separator_cell_text a b (S n) w) +
           String.length (separator_text cells) - S (length cells)))
    by lia.
  apply sep_cells_fuel_more, separator_cells_fuel; assumption.
Qed.

(* Cell text is trimmed on both sides, except that an escaped whitespace
   character stops the right trim and everything after it is kept:
   `| a\ |` renders `a&nbsp;`.  Escapes are consumed in pairs, so this is
   a parity test: `a\\  ` trims, `a\   ` keeps one space. *)
Local Fixpoint cell_trim_r (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c1 s1 =>
      if Ascii.eqb c1 "\"
      then match s1 with
           | EmptyString => String c1 EmptyString
           | String c2 s2 => String c1 (String c2 (cell_trim_r s2))
           end
      else if is_ws c1
           then match cell_trim_r s1 with
                | EmptyString => EmptyString
                | r => String c1 r
                end
           else String c1 (cell_trim_r s1)
  end.

Local Definition cell_trim (s : string) : string :=
  cell_trim_r (drop_leading_ws s).

(* Splitting a row's interior into cells.  A bar ends a cell unless it is
   inside a verbatim span or the byte before it is a backslash.

   The backslash test is one byte, not parity: `| a\\|b |` is a single
   cell `a\\|b`, although the inline layer reads `\\` as an escaped
   backslash.  `cell_trim_r` above is where the inline layer's parity
   applies.

   `vb` is the verbatim state: 0 outside, otherwise the length of the
   backtick run that opened it, which only a run of exactly that length
   closes.  `run` is the backtick run being read, resolved against `vb`
   at the first byte that is not a backtick. *)
Local Definition vb_step (vb run : nat) : nat :=
  match run with
  | O => vb
  | _ => match vb with
         | O => run
         | _ => if Nat.eqb vb run then O else vb
         end
  end.

(* One cell's entry: its trimmed text, its start and stop relative to the
   opening bar, and where its content starts after leading whitespace. *)
Local Definition row_cell_entry (cur : string) (start stop : nat)
  : string * nat * nat * nat :=
  let raw := rev_string cur in
  let content := drop_leading_ws raw in
  (cell_trim raw, start, stop,
   S start + String.length raw - String.length content).

(* The cell scan.  `cur` and `acc` are reversed; `bs` records whether the
   previous byte was a backslash.  Outside verbatim, a backslash and the
   byte after it are consumed together, which gives inline escapes their
   parity: after two backslashes a backtick still opens verbatim.  `bs`
   keeps the separate one-byte rule that a bar right after a backslash
   does not close a cell.

   Each entry records the cell's interval relative to the opening bar, so
   the semantic row and its source parts project one scan.  The final bar
   was removed by `row_inner`, so the last stop is one past `pos`. *)
Fixpoint row_cells_trace
  (s : string) (vb run : nat) (bs : bool) (cur : string)
  (acc : list (string * nat * nat * nat)) (pos start : nat)
  : option (list (string * nat * nat * nat)) :=
  match s with
  | EmptyString =>
      (* The interior ends where the line's last bar is, so the cell open
         here is closed by that bar -- unless a backslash escapes it or a
         verbatim span swallowed it. *)
      if bs then None
      else match vb_step vb run with
           | O => Some (rev (row_cell_entry cur start (S pos) :: acc))
           | _ => None
           end
  | String c s' =>
      if Ascii.eqb c "`"
      then row_cells_trace s' vb (S run) false (String c cur) acc (S pos) start
      else
        let vb' := vb_step vb run in
        (* The inline scanner consumes an escape and its following byte in
           one step.  Do that only outside verbatim: inside a verbatim span
           a backslash is literal and cannot protect its closing run. *)
        if (Nat.eqb vb' O && Ascii.eqb c "\")%bool
        then match s' with
             | EmptyString => None
             | String c' s'' =>
                 row_cells_trace s'' O O (Ascii.eqb c' "\")
                   (String c' (String c cur)) acc (S (S pos)) start
             end
        else if (Ascii.eqb c "|" && Nat.eqb vb' O && negb bs)%bool
        then row_cells_trace s' O O false EmptyString
               (row_cell_entry cur start (S pos) :: acc)
               (S pos) pos
        else row_cells_trace s' vb' O (Ascii.eqb c "\") (String c cur)
               acc (S pos) start
  end.

Local Definition row_cells (s : string) (vb run : nat) (bs : bool)
  (cur : string) (acc : list string) : option (list string) :=
  option_map (map (fun x => let '(c, _, _, _) := x in c))
    (row_cells_trace s vb run bs cur
       (map (fun c => (c, 0, 0, 0)) acc) 1 0).

(* The line after its opening bar, trailing whitespace removed, provided
   it still ends in a bar: `None` unless the line is `|`, a body, `|`,
   whitespace.  The body keeps its final bar, because that is the bar
   each scan below ends on. *)
Definition row_body (l : string) : option string :=
  match drop_leading_ws l with
  | String c rest =>
      if negb (Ascii.eqb c "|") then None
      else
        let back := strip_trailing_ws rest in
        match rev_string back with
        | String c' _ => if Ascii.eqb c' "|" then Some back else None
        | EmptyString => None
        end
  | EmptyString => None
  end.

(* The body without its final bar: what `row_cells` scans, since the bar
   that closes the last cell is the one `row_body` guaranteed. *)
Definition row_inner (body : string) : string :=
  match rev_string body with
  | String _ back => rev_string back
  | EmptyString => EmptyString
  end.

Definition table_row (l : string) : option trow :=
  match row_body l with
  | None => None
  | Some body =>
      match sep_cells body with
      | Some ((_ :: _) as aligns) => Some (TSep aligns)
      | _ =>
          match row_cells (row_inner body) O O false EmptyString [] with
          | None => None
          | Some cells => Some (TCells cells)
          end
      end
  end.

(* Examples pinning the boundary.  In a separator, a leading space is
   allowed on every cell but the first, trailing whitespace after the
   final bar belongs to no cell, and one dash is enough. *)
(* String scope for the cell lists: `list string` does not propagate a
   scope to its elements, and char scope is the innermost one open. *)
Local Open Scope string_scope.

Example row_cells_two : table_row "| a | b |" = Some (TCells ["a"; "b"]).
Proof. reflexivity. Qed.

Example row_cells_trimmed :
  table_row "|   a   |   b  |" = Some (TCells ["a"; "b"]).
Proof. reflexivity. Qed.

Example row_cells_empty : table_row "||" = Some (TCells [""]).
Proof. reflexivity. Qed.

(* One bar is not a row. *)
Example row_one_bar : table_row "|" = None.
Proof. reflexivity. Qed.

(* Anything but whitespace after the final bar and the line is a
   paragraph. *)
Example row_trailing_text : table_row "| a | x" = None.
Proof. reflexivity. Qed.

Example row_sep_default_right :
  table_row "|---|--:|" = Some (TSep [AlignDefault; AlignRight]).
Proof. reflexivity. Qed.

Example row_sep_one_dash : table_row "|-|" = Some (TSep [AlignDefault]).
Proof. reflexivity. Qed.

Example row_sep_trailing_ws : table_row "|---|   " = Some (TSep [AlignDefault]).
Proof. reflexivity. Qed.

(* The leading space belongs to the previous cell's match, and the first
   cell has none: `| :- |` is a row of text, `|:-| -: |` a separator.
   djoths reads both as separators (`.project/djotjs-divergences.md`). *)
Example row_sep_leading_space : table_row "| --- |" = Some (TCells ["---"]).
Proof. reflexivity. Qed.

Example row_sep_inner_space :
  table_row "|:-| -: |" = Some (TSep [AlignLeft; AlignRight]).
Proof. reflexivity. Qed.

(* A cell that is not all dashes makes the whole line an ordinary row. *)
Example row_sep_mixed : table_row "|---|x|" = Some (TCells ["---"; "x"]).
Proof. reflexivity. Qed.

(* A bar preceded by a backslash does not split, whatever the parity. *)
Example row_escaped_bar : table_row "| a\|b | c |" = Some (TCells ["a\|b"; "c"]).
Proof. reflexivity. Qed.

(* Escapes affect the inline verbatim scan too, with ordinary parity.
   One and three backslashes make the backtick literal; two leave it able
   to open an unclosed verbatim span. *)
Example row_escaped_backtick :
  table_row "| a\`b |" = Some (TCells ["a\`b"]).
Proof. reflexivity. Qed.

Example row_double_backslash_before_backtick : table_row "| a\\`b |" = None.
Proof. reflexivity. Qed.

Example row_triple_backslash_before_backtick :
  table_row "| a\\\`b |" = Some (TCells ["a\\\`b"]).
Proof. reflexivity. Qed.

(* `row_inner` removes the last bar before scanning.  A trailing
   backslash says that bar was escaped, so it cannot close the row. *)
Example row_escaped_final_bar : table_row "| a\|" = None.
Proof. reflexivity. Qed.

Example row_verbatim_bar :
  table_row "| `a|b` | c |" = Some (TCells ["`a|b`"; "c"]).
Proof. reflexivity. Qed.

(* Backslashes are literal inside verbatim, including immediately before
   the run that closes it. *)
Example row_backslash_does_not_escape_verbatim_close :
  table_row "| `a\` b | c |" = Some (TCells ["`a\` b"; "c"]).
Proof. reflexivity. Qed.

(* A verbatim closes only on a run of its own length, and one left open
   swallows the bars that would have ended the cells. *)
Example row_verbatim_unclosed : table_row "| `a`` b | c |" = None.
Proof. reflexivity. Qed.

(* An escaped space survives the right trim; an escaped backslash does
   not protect the spaces after it. *)
Example row_escaped_space : table_row "| a\ |" = Some (TCells ["a\ "]).
Proof. reflexivity. Qed.

Example row_escaped_bslash : table_row "| a\\  |" = Some (TCells ["a\\"]).
Proof. reflexivity. Qed.

Example row_escaped_space_run : table_row "| a\   |" = Some (TCells ["a\ "]).
Proof. reflexivity. Qed.

Local Open Scope char_scope.

(*
Rows over every spelling
------------------------

PT1, PT2 and PT7 of the syntax reference as theorems about `table_row`.
The cell scan is followed through a few steps (`trace_*`), each stated
from outside verbatim with no pending backslash.
*)

(* A byte the cell scan passes over: not a bar, a backslash or a
   backtick. *)
Definition plain_cell_char (c : ascii) : bool :=
  negb (Ascii.eqb c "|" || Ascii.eqb c "\" || Ascii.eqb c "`").

Local Lemma plain_parts : forall c, plain_cell_char c = true ->
  Ascii.eqb c "|" = false /\ Ascii.eqb c "\" = false /\ Ascii.eqb c "`" = false.
Proof.
  intros c H. unfold plain_cell_char in H. apply negb_true_iff in H.
  apply orb_false_iff in H as [H Hb]. apply orb_false_iff in H as [Hp Hs]. auto.
Qed.

Local Lemma trace_plain : forall s rest cur acc pos start,
  str_forallb plain_cell_char s = true ->
  row_cells_trace (s ++ rest) 0 0 false cur acc pos start =
  row_cells_trace rest 0 0 false (rev_string s ++ cur) acc (String.length s + pos) start.
Proof.
  induction s as [|c s IH]; intros rest cur acc pos start H; [reflexivity|].
  cbn [str_forallb] in H. apply andb_true_iff in H as [Hc H].
  apply plain_parts in Hc as (Hp & Hs & Hb).
  cbn [append row_cells_trace]. rewrite Hb. cbn [vb_step Nat.eqb andb].
  rewrite Hs, Hp. cbn [andb]. rewrite IH by exact H.
  rewrite rev_string_cons, append_assoc. cbn [append String.length].
  f_equal. lia.
Qed.

Local Lemma trace_bar : forall rest cur acc pos start,
  row_cells_trace (String "|" rest) 0 0 false cur acc pos start =
  row_cells_trace rest 0 0 false EmptyString
    (row_cell_entry cur start (S pos) :: acc) (S pos) pos.
Proof. reflexivity. Qed.

Local Lemma trace_escape : forall c rest cur acc pos start,
  row_cells_trace (String "\" (String c rest)) 0 0 false cur acc pos start =
  row_cells_trace rest 0 0 (Ascii.eqb c "\") (String c (String "\" cur))
    acc (S (S pos)) start.
Proof. reflexivity. Qed.

(* Inside a verbatim span opened by one backtick, every byte up to the
   next backtick is content, bars and backslashes included. *)
Local Lemma trace_verbatim_body : forall x rest cur acc pos start bs,
  str_forallb (fun c => negb (Ascii.eqb c "`")) x = true ->
  row_cells_trace (x ++ String "`" rest) 1 0 bs cur acc pos start =
  row_cells_trace rest 1 1 false (String "`" (rev_string x ++ cur)) acc
    (S (String.length x + pos)) start.
Proof.
  induction x as [|c x IH]; intros rest cur acc pos start bs H; [reflexivity|].
  cbn [str_forallb] in H. apply andb_true_iff in H as [Hc H].
  apply negb_true_iff in Hc.
  cbn [append row_cells_trace]. rewrite Hc. cbn [vb_step Nat.eqb andb].
  rewrite IH by exact H. rewrite andb_false_r. cbn [andb].
  rewrite rev_string_cons, append_assoc. cbn [append String.length].
  f_equal. lia.
Qed.

(* A span with one backtick on each side.  The closing run is left
   pending; the next byte that is not a backtick resolves it
   (`trace_resume`). *)
Local Lemma trace_verbatim : forall v rest cur acc pos start,
  v <> EmptyString ->
  str_forallb (fun c => negb (Ascii.eqb c "`")) v = true ->
  row_cells_trace (String "`" (v ++ String "`" rest)) 0 0 false
    cur acc pos start =
  row_cells_trace rest 1 1 false
    (rev_string (String "`" (v ++ "`")) ++ cur) acc
    (2 + String.length v + pos) start.
Proof.
  intros [|c x] rest cur acc pos start Hne Hv; [contradiction|].
  cbn [str_forallb] in Hv. apply andb_true_iff in Hv as [Hc Hx].
  apply negb_true_iff in Hc.
  change (row_cells_trace (String "`" (String c x ++ String "`" rest)) 0 0 false
            cur acc pos start)
    with (row_cells_trace (String c x ++ String "`" rest) 0 1 false
            (String "`" cur) acc (S pos) start).
  cbn [append row_cells_trace]. rewrite Hc. cbn [vb_step Nat.eqb andb].
  rewrite andb_false_r. cbn [andb].
  rewrite trace_verbatim_body by exact Hx.
  rewrite !rev_string_cons, rev_string_app, !append_assoc.
  cbn [append rev_string rev_string_aux String.length].
  f_equal. lia.
Qed.

Local Lemma trace_resume : forall c rest cur acc pos start,
  Ascii.eqb c "`" = false ->
  row_cells_trace (String c rest) 1 1 false cur acc pos start =
  row_cells_trace (String c rest) 0 0 false cur acc pos start.
Proof.
  intros c rest cur acc pos start Hc. cbn [row_cells_trace]. rewrite Hc.
  reflexivity.
Qed.

Local Lemma cell_trim_r_blank : forall w, is_blank w = true -> cell_trim_r w = EmptyString.
Proof.
  induction w as [|c w IH]; intros H; [reflexivity|].
  cbn [is_blank] in H. apply andb_true_iff in H as [Hc H].
  cbn [cell_trim_r]. rewrite Hc, (IH H).
  destruct (Ascii.eqb c "\") eqn:E; [|reflexivity].
  apply Ascii.eqb_eq in E. subst c. discriminate.
Qed.

(* The right trim keeps everything up to a last byte that is neither
   whitespace nor a backslash, whatever the escapes before it. *)
Local Lemma cell_trim_r_last : forall n s z w,
  String.length s <= n ->
  is_ws z = false -> Ascii.eqb z "\" = false -> is_blank w = true ->
  cell_trim_r (s ++ String z w) = s ++ String z EmptyString.
Proof.
  induction n as [|n IH]; intros s z w Hn Hz Hzb Hw.
  - destruct s; [|cbn in Hn; lia].
    cbn [append cell_trim_r]. rewrite Hzb, Hz, (cell_trim_r_blank w Hw).
    reflexivity.
  - destruct s as [|c s].
    + cbn [append cell_trim_r]. rewrite Hzb, Hz, (cell_trim_r_blank w Hw).
      reflexivity.
    + cbn [String.length] in Hn. cbn [append cell_trim_r].
      destruct (Ascii.eqb c "\") eqn:Eb.
      * destruct s as [|c2 s].
        -- cbn [append]. rewrite (cell_trim_r_blank w Hw). reflexivity.
        -- cbn [append]. rewrite (IH s z w) by (cbn in Hn; lia || assumption).
           reflexivity.
      * rewrite (IH s z w) by (lia || assumption).
        destruct (is_ws c); [|reflexivity].
        destruct s; reflexivity.
Qed.

(* A cell's text survives the trim when it starts and ends with neither
   whitespace nor, at the end, a backslash. *)
Local Lemma cell_trim_padded : forall c,
  drop_leading_ws c = c ->
  (c = EmptyString \/ exists x z, c = x ++ String z EmptyString /\
                                  is_ws z = false /\ Ascii.eqb z "\" = false) ->
  cell_trim (" " ++ c ++ " ") = c.
Proof.
  intros c Hl Hr. unfold cell_trim.
  destruct Hr as [->|(x & z & -> & Hz & Hzb)]; [reflexivity|].
  cbn [append drop_leading_ws]. change (is_ws " ") with true. cbn iota.
  destruct x as [|h t].
  - cbn [append drop_leading_ws]. rewrite Hz.
    exact (cell_trim_r_last 0 EmptyString z " " (le_n 0) Hz Hzb eq_refl).
  - cbn [append] in Hl |- *. apply drop_leading_ws_fixed in Hl.
    cbn [drop_leading_ws]. rewrite Hl.
    rewrite append_assoc. cbn [append].
    exact (cell_trim_r_last _ (String h t) z " " (le_n _) Hz Hzb eq_refl).
Qed.

(* A row of cells as the renderer writes it, after the opening bar: each
   cell between a space and the bar that ends it. *)
Fixpoint cells_body (cs : list string) : string :=
  match cs with
  | [] => EmptyString
  | c :: rest => (" " ++ c ++ " |" ++ cells_body rest)%string
  end.

(* `cells_body` without its final bar, which is what the scan reads. *)
Local Fixpoint cells_inner (c : string) (cs : list string) : string :=
  " " ++ c ++ " " ++
  match cs with
  | [] => EmptyString
  | c' :: cs' => String "|" (cells_inner c' cs')
  end.

Local Lemma cells_body_inner : forall cs c,
  cells_body (c :: cs) = cells_inner c cs ++ "|".
Proof.
  induction cs as [|c' cs IH]; intros c.
  - cbn [cells_body cells_inner]. rewrite !append_assoc. reflexivity.
  - cbn [cells_body cells_inner] in *. rewrite IH, !append_assoc. reflexivity.
Qed.

Local Lemma rev_bar : forall x,
  rev_string (x ++ "|") = String "|" (rev_string x).
Proof. intros x. rewrite rev_string_app. reflexivity. Qed.

Local Lemma strip_trailing_bar : forall x,
  strip_trailing_ws (x ++ "|") = x ++ "|".
Proof.
  intros x. unfold strip_trailing_ws. rewrite rev_bar.
  cbn [drop_leading_ws]. change (is_ws "|") with false. cbn iota.
  rewrite rev_string_cons, rev_string_involutive. reflexivity.
Qed.

Local Lemma row_inner_bar : forall x, row_inner (x ++ "|") = x.
Proof.
  intros x. unfold row_inner. rewrite rev_bar, rev_string_involutive. reflexivity.
Qed.

Local Lemma row_body_bars : forall x,
  row_body (String "|" (x ++ "|")) = Some (x ++ "|").
Proof.
  intros x. unfold row_body. cbn [drop_leading_ws]. change (is_ws "|") with false.
  cbn iota. change (negb (Ascii.eqb "|" "|")) with false. cbn iota.
  rewrite strip_trailing_bar, rev_bar. reflexivity.
Qed.

(* A cell with no bar, backslash or backtick, and no whitespace at
   either end. *)
Definition plain_cell (c : string) : Prop :=
  str_forallb plain_cell_char c = true /\
  drop_leading_ws c = c /\ strip_trailing_ws c = c.

Local Lemma plain_cell_trim : forall c, plain_cell c ->
  cell_trim (" " ++ c ++ " ") = c.
Proof.
  intros c (Hp & Hl & Hr). apply cell_trim_padded; [exact Hl|].
  destruct (strip_trailing_last c Hr) as [->|(x & z & -> & Hz)]; [left; reflexivity|].
  right. exists x, z. repeat split; [exact Hz|].
  clear Hl Hr. induction x as [|h x IH].
  - cbn in Hp. apply andb_true_iff in Hp as [Hp _]. apply plain_parts in Hp as (_ & H & _).
    exact H.
  - cbn [append str_forallb] in Hp. apply andb_true_iff in Hp as [_ Hp]. exact (IH Hp).
Qed.

Local Lemma str_forallb_app : forall p a b,
  str_forallb p (a ++ b) = (str_forallb p a && str_forallb p b)%bool.
Proof.
  intros p a b. induction a as [|c a IH]; [reflexivity|].
  cbn [append str_forallb]. rewrite IH, andb_assoc. reflexivity.
Qed.

Local Lemma plain_padded : forall c, plain_cell c ->
  str_forallb plain_cell_char (" " ++ c ++ " ") = true.
Proof.
  intros c (Hp & _). rewrite !str_forallb_app, Hp. reflexivity.
Qed.

Local Lemma trace_cells : forall cs c acc pos start,
  Forall plain_cell (c :: cs) ->
  option_map (map (fun x => let '(c, _, _, _) := x in c))
    (row_cells_trace (cells_inner c cs) 0 0 false EmptyString acc pos start)
  = Some (rev (map (fun x => let '(c, _, _, _) := x in c) acc) ++ (c :: cs))%list.
Proof.
  induction cs as [|c' cs IH]; intros c acc pos start H;
    inversion H as [|? ? Hc Hcs]; subst.
  - cbn [cells_inner]. rewrite append_empty_r.
    rewrite <- (append_empty_r (" " ++ c ++ " ")).
    rewrite (trace_plain _ _ _ _ _ _ (plain_padded c Hc)).
    cbn [row_cells_trace vb_step option_map]. rewrite map_rev. cbn [map].
    unfold row_cell_entry. rewrite append_empty_r, rev_string_involutive.
    rewrite (plain_cell_trim c Hc). reflexivity.
  - cbn [cells_inner]. fold (cells_inner c' cs).
    replace (" " ++ c ++ " " ++ String "|" (cells_inner c' cs))
      with ((" " ++ c ++ " ") ++ String "|" (cells_inner c' cs))
      by (rewrite !append_assoc; reflexivity).
    rewrite (trace_plain _ _ _ _ _ _ (plain_padded c Hc)), trace_bar, IH by exact Hcs.
    cbn [map rev]. unfold row_cell_entry at 1.
    rewrite append_empty_r, rev_string_involutive, (plain_cell_trim c Hc).
    rewrite <- app_assoc. reflexivity.
Qed.

(** PT1, if: a row of plain cells, each written between a space and the
    bar that ends it, is a row of exactly those cells. *)
Theorem table_row_cells : forall c cs,
  Forall plain_cell (c :: cs) ->
  table_row ("|" ++ cells_body (c :: cs)) = Some (TCells (c :: cs)).
Proof.
  intros c cs H. unfold table_row.
  rewrite cells_body_inner. change ("|" ++ ?x) with (String "|" x).
  rewrite row_body_bars.
  assert (Hsep : sep_cells (cells_inner c cs ++ "|") = None)
    by (destruct cs; reflexivity).
  rewrite Hsep. unfold row_cells. rewrite row_inner_bar.
  cbn [map]. rewrite (trace_cells cs c [] 1 0 H). reflexivity.
Qed.

Local Lemma drop_leading_ws_app_nonws : forall a h t,
  drop_leading_ws a = a -> is_ws h = false ->
  drop_leading_ws (a ++ String h t) = a ++ String h t.
Proof.
  intros [|a0 a] h t Ha Hh.
  - cbn [append drop_leading_ws]. rewrite Hh. reflexivity.
  - apply drop_leading_ws_fixed in Ha. cbn [append drop_leading_ws]. rewrite Ha.
    reflexivity.
Qed.

(* The last character of `x ++ String h t`, when `t` is trimmed. *)
Local Lemma last_nonws : forall x h t,
  is_ws h = false -> Ascii.eqb h "\" = false ->
  strip_trailing_ws t = t -> str_forallb plain_cell_char t = true ->
  exists x' z, x ++ String h t = x' ++ String z EmptyString /\
               is_ws z = false /\ Ascii.eqb z "\" = false.
Proof.
  intros x h t Hh Hhb Ht Hp.
  destruct (strip_trailing_last t Ht) as [->|(y & z & -> & Hz)].
  - exists x, h. auto.
  - exists (x ++ String h y), z. split; [|split; [exact Hz|]].
    + rewrite !append_assoc. reflexivity.
    + rewrite str_forallb_app in Hp. apply andb_true_iff in Hp as [_ Hp].
      cbn [str_forallb] in Hp. apply andb_true_iff in Hp as [Hp _].
      apply plain_parts in Hp as (_ & H & _). exact H.
Qed.

(** PT7, the escape: `\|` inside a cell does not end it. *)
Theorem table_row_escaped_bar : forall a b,
  str_forallb plain_cell_char a = true -> str_forallb plain_cell_char b = true ->
  drop_leading_ws a = a -> strip_trailing_ws b = b ->
  table_row ("| " ++ a ++ "\|" ++ b ++ " |") = Some (TCells [a ++ "\|" ++ b]).
Proof.
  intros a b Ha Hb Hla Hrb. unfold table_row.
  replace ("| " ++ a ++ "\|" ++ b ++ " |")
    with (String "|" ((" " ++ a ++ "\|" ++ b ++ " ") ++ "|"))
    by (rewrite !append_assoc; reflexivity).
  rewrite row_body_bars.
  assert (Hsep : sep_cells ((" " ++ a ++ "\|" ++ b ++ " ") ++ "|") = None)
    by reflexivity.
  rewrite Hsep. unfold row_cells. rewrite row_inner_bar. cbn [map].
  replace (" " ++ a ++ "\|" ++ b ++ " ")
    with ((" " ++ a) ++ String "\" (String "|" (b ++ " ")))
    by (rewrite !append_assoc; reflexivity).
  rewrite trace_plain by (rewrite str_forallb_app, Ha; reflexivity).
  rewrite trace_escape. change (Ascii.eqb "|" "\") with false.
  rewrite <- (append_empty_r (b ++ " ")).
  rewrite trace_plain by (rewrite !str_forallb_app, Hb; reflexivity).
  cbn [row_cells_trace vb_step option_map rev map app].
  unfold row_cell_entry.
  rewrite rev_string_app, rev_string_involutive, append_empty_r.
  rewrite !rev_string_cons, rev_string_involutive.
  replace ((((" " ++ a) ++ String "\" EmptyString) ++ String "|" EmptyString) ++ b ++ " ")
    with (" " ++ (a ++ "\|" ++ b) ++ " ")
    by (rewrite !append_assoc; reflexivity).
  rewrite cell_trim_padded; [reflexivity| |].
  - apply drop_leading_ws_app_nonws; [exact Hla|reflexivity].
  - right. change ("\|" ++ b) with (String "\" (String "|" b)).
    destruct (last_nonws (a ++ "\") "|" b eq_refl eq_refl Hrb Hb) as (x & z & E & Hz).
    exists x, z. rewrite <- E, !append_assoc. split; [reflexivity|exact Hz].
Qed.

(** PT7, verbatim: a bar inside a verbatim span does not end the cell. *)
Theorem table_row_verbatim_bar : forall x y,
  str_forallb (fun c => negb (Ascii.eqb c "`")) x = true ->
  str_forallb (fun c => negb (Ascii.eqb c "`")) y = true ->
  table_row ("| `" ++ x ++ "|" ++ y ++ "` |") =
    Some (TCells ["`" ++ x ++ "|" ++ y ++ "`"]).
Proof.
  intros x y Hx Hy. unfold table_row.
  replace ("| `" ++ x ++ "|" ++ y ++ "` |")
    with (String "|" ((" " ++ ("`" ++ x ++ "|" ++ y ++ "`") ++ " ") ++ "|"))
    by (rewrite !append_assoc; reflexivity).
  rewrite row_body_bars.
  assert (Hsep : sep_cells ((" " ++ ("`" ++ x ++ "|" ++ y ++ "`") ++ " ") ++ "|")
                 = None) by reflexivity.
  rewrite Hsep. unfold row_cells. rewrite row_inner_bar. cbn [map].
  replace (" " ++ ("`" ++ x ++ "|" ++ y ++ "`") ++ " ")
    with (" " ++ String "`" ((x ++ "|" ++ y) ++ String "`" " "))
    by (rewrite !append_assoc; reflexivity).
  rewrite (trace_plain " ") by reflexivity.
  rewrite trace_verbatim.
  2: { destruct x; discriminate. }
  2: { rewrite !str_forallb_app, Hx, Hy. reflexivity. }
  rewrite trace_resume by reflexivity.
  rewrite <- (append_empty_r " "). rewrite (trace_plain " ") by reflexivity.
  cbn [row_cells_trace vb_step option_map rev map app].
  unfold row_cell_entry.
  rewrite !rev_string_app, !rev_string_involutive, !append_empty_r.
  replace (((rev_string EmptyString ++ " ") ++ String "`" ((x ++ "|" ++ y) ++ "`")) ++ " ")
    with (" " ++ ("`" ++ x ++ "|" ++ y ++ "`") ++ " ")
    by (cbn [rev_string rev_string_aux append]; rewrite !append_assoc;
        cbn [append]; rewrite !append_assoc; reflexivity).
  rewrite cell_trim_padded; [reflexivity|reflexivity|].
  right. exists (String "`" (x ++ "|" ++ y)), "`". split; [|split; reflexivity].
  cbn [append]. rewrite ?append_assoc. reflexivity.
Qed.

Local Lemma row_body_shape : forall l body,
  row_body l = Some body ->
  exists pre x post, is_blank pre = true /\ is_blank post = true /\
    body = x ++ "|" /\ l = pre ++ "|" ++ x ++ "|" ++ post.
Proof.
  intros l body H. unfold row_body in H.
  destruct (drop_leading_ws_split l) as (pre & Hpre & Hl).
  destruct (drop_leading_ws l) as [|c rest]; [discriminate|].
  destruct (Ascii.eqb c "|") eqn:Ec; [|discriminate]. cbn [negb] in H.
  apply Ascii.eqb_eq in Ec. subst c.
  destruct (strip_trailing_split rest) as (w & Hw & Er).
  destruct (rev_string (strip_trailing_ws rest)) as [|c' y] eqn:Ey; [discriminate|].
  destruct (Ascii.eqb c' "|") eqn:Ec'; [|discriminate].
  apply Ascii.eqb_eq in Ec'. subst c'. injection H as <-.
  assert (Eb : strip_trailing_ws rest = rev_string y ++ "|").
  { rewrite <- (rev_string_involutive (strip_trailing_ws rest)), Ey, rev_string_cons.
    reflexivity. }
  exists pre, (rev_string y), w. repeat split; try assumption.
  rewrite Hl, Er, Eb, !append_assoc. reflexivity.
Qed.

Local Lemma row_cells_trace_nonempty : forall n s vb run bs cur acc pos start xs,
  String.length s <= n ->
  row_cells_trace s vb run bs cur acc pos start = Some xs -> xs <> [].
Proof.
  induction n as [|n IH]; intros s vb run bs cur acc pos start xs Hn H.
  - destruct s; [|cbn in Hn; lia]. cbn [row_cells_trace] in H.
    destruct bs; [discriminate|]. destruct (vb_step vb run); [|discriminate].
    injection H as <-. intros E. destruct (rev acc); discriminate.
  - destruct s as [|c s].
    + apply (IH EmptyString vb run bs cur acc pos start); [cbn; lia|exact H].
    + cbn [String.length] in Hn. cbn [row_cells_trace] in H.
      destruct (Ascii.eqb c "`"); [eapply IH; [|exact H]; lia|].
      destruct (Nat.eqb (vb_step vb run) 0 && Ascii.eqb c "\")%bool.
      * destruct s as [|c' s'']; [discriminate|].
        eapply IH; [|exact H]. cbn in Hn. lia.
      * destruct (Ascii.eqb c "|" && Nat.eqb (vb_step vb run) 0 && negb bs)%bool;
          (eapply IH; [|exact H]; lia).
Qed.

(*
Where a cell's text is
----------------------

The scan records, for each cell, where its content starts after leading
whitespace.  The trimmed cell is a prefix of that content, so it sits in
the row at the recorded start.  The located parse reads a cell from
there.
*)

Local Lemma cell_trim_r_prefix : forall n s, String.length s <= n ->
  exists more, s = (cell_trim_r s ++ more)%string.
Proof.
  induction n as [|n IH]; intros s Hn.
  - destruct s; [exists EmptyString; reflexivity|cbn in Hn; lia].
  - destruct s as [|c1 s1]; [exists EmptyString; reflexivity|].
    cbn [String.length] in Hn. cbn [cell_trim_r].
    destruct (Ascii.eqb c1 "\").
    + destruct s1 as [|c2 s2]; [exists EmptyString; reflexivity|].
      cbn [String.length] in Hn. destruct (IH s2 ltac:(lia)) as (m & Hm).
      exists m. rewrite Hm at 1. reflexivity.
    + destruct (IH s1 ltac:(lia)) as (m & Hm).
      destruct (is_ws c1).
      * destruct (cell_trim_r s1) as [|c r] eqn:E.
        -- exists (String c1 s1). reflexivity.
        -- exists m. rewrite Hm at 1. reflexivity.
      * exists m. rewrite Hm at 1. reflexivity.
Qed.

(* The cell's text `c` is at byte `ts` of `D`. *)
Local Definition cell_at (D : string) (x : string * nat * nat * nat) : Prop :=
  let '(c, _, _, ts) := x in
  exists pre more, D = (pre ++ c ++ more)%string /\ String.length pre = ts.

Local Lemma row_cell_entry_at : forall D Y cur R start stop,
  D = (Y ++ rev_string cur ++ R)%string -> String.length Y = S start ->
  cell_at D (row_cell_entry cur start stop).
Proof.
  intros D Y cur R start stop HD HY. unfold row_cell_entry, cell_at, cell_trim.
  destruct (drop_leading_ws_split (rev_string cur)) as (w & _ & Hw).
  set (content := drop_leading_ws (rev_string cur)) in *.
  destruct (cell_trim_r_prefix (String.length content) content (le_n _)) as (m & Hm).
  exists (Y ++ w)%string, (m ++ R)%string. split.
  - rewrite HD, Hw at 1. rewrite Hm at 1. rewrite !append_assoc. reflexivity.
  - rewrite Hw, !length_append. lia.
Qed.

Local Lemma trace_at : forall n s vb run bs cur acc pos start cells D Y tail,
  String.length s <= n ->
  D = (Y ++ rev_string cur ++ s ++ tail)%string ->
  String.length Y = S start -> pos = S start + String.length cur ->
  Forall (cell_at D) acc ->
  row_cells_trace s vb run bs cur acc pos start = Some cells ->
  Forall (cell_at D) cells.
Proof.
  induction n as [|n IH];
    intros s vb run bs cur acc pos start cells D Y tail Hn HD HY Hp Hacc H.
  - destruct s; [|cbn in Hn; lia]. cbn [row_cells_trace] in H.
    destruct bs; [discriminate|]. destruct (vb_step vb run); [|discriminate].
    injection H as <-. apply Forall_app.
    split; [apply Forall_rev, Hacc|constructor; [|constructor]].
    exact (row_cell_entry_at D Y cur _ start (S pos) HD HY).
  - destruct s as [|c s'].
    + exact (IH EmptyString vb run bs cur acc pos start cells D Y tail
               ltac:(cbn; lia) HD HY Hp Hacc H).
    + cbn [String.length] in Hn. cbn [row_cells_trace] in H.
      (* One more byte of the open cell. *)
      assert (Hone : D = (Y ++ rev_string (String c cur) ++ s' ++ tail)%string)
        by (rewrite HD, rev_string_cons, !append_assoc; reflexivity).
      assert (Hone_p : S pos = S start + String.length (String c cur))
        by (cbn [String.length]; lia).
      destruct (Ascii.eqb c "`").
      { exact (IH s' _ _ _ _ _ _ _ cells D Y tail ltac:(lia) Hone HY Hone_p Hacc H). }
      destruct (Nat.eqb (vb_step vb run) 0 && Ascii.eqb c "\")%bool.
      { destruct s' as [|c' s'']; [discriminate|].
        refine (IH s'' _ _ _ _ _ _ _ cells D Y tail ltac:(cbn in Hn; lia) _ HY _ Hacc H).
        - rewrite Hone, !rev_string_cons, !append_assoc. reflexivity.
        - cbn [String.length]. lia. }
      destruct (Ascii.eqb c "|" && Nat.eqb (vb_step vb run) 0 && negb bs)%bool eqn:Ebar.
      { apply andb_true_iff in Ebar as [Ebar _]. apply andb_true_iff in Ebar as [Ebar _].
        apply Ascii.eqb_eq in Ebar. subst c.
        refine (IH s' _ _ _ _ _ _ _ cells D (Y ++ rev_string cur ++ "|")%string tail
                  ltac:(lia) _ _ _ _ H).
        - rewrite HD, !append_assoc. reflexivity.
        - rewrite !length_append, Strings.rev_length. cbn [String.length]. lia.
        - cbn [String.length]. lia.
        - constructor; [|exact Hacc].
          exact (row_cell_entry_at D Y cur _ start (S pos) HD HY). }
      exact (IH s' _ _ _ _ _ _ _ cells D Y tail ltac:(lia) Hone HY Hone_p Hacc H).
Qed.

(** Every cell of a row line is at the byte the scan records for it,
    counted from the row's opening bar. *)
Lemma table_row_trace : forall l cs, table_row l = Some (TCells cs) ->
  exists body cells,
    row_body l = Some body /\
    row_cells_trace (row_inner body) O O false EmptyString [] 1 0 = Some cells /\
    cs = map (fun x => let '(c, _, _, _) := x in c) cells /\
    Forall (fun x => let '(c, _, _, ts) := x in
      exists pre more, drop_leading_ws l = (pre ++ c ++ more)%string /\
                       String.length pre = ts) cells.
Proof.
  intros l cs H. unfold table_row in H.
  destruct (row_body l) as [body|] eqn:Eb; [|discriminate].
  destruct (sep_cells body) as [[|a als]|];
    try (injection H as H; discriminate H);
    (unfold row_cells in H; cbn [map] in H;
     destruct (row_cells_trace (row_inner body) 0 0 false "" [] 1 0) as [cells|] eqn:Et;
     [|discriminate]; cbn [option_map] in H; injection H as <-;
     exists body, cells; split; [reflexivity|split; [exact Et|split; [reflexivity|]]]).
  all: destruct (row_body_shape l body Eb) as (pre & x & post & Hpre & _ & Hbody & Hl);
    subst body; rewrite row_inner_bar in Et;
    assert (HD : drop_leading_ws l = ("|" ++ x ++ "|" ++ post)%string)
      by (rewrite Hl, (drop_leading_ws_ws_prefix pre _ Hpre); reflexivity);
    rewrite HD;
    exact (Forall_impl _ (fun y Hy => match y as y0 return cell_at _ y0 -> _ with
                                        (c, _, _, ts) => fun h => h end Hy)
             (trace_at (String.length x) x 0 0 false EmptyString [] 1 0 cells
                ("|" ++ x ++ "|" ++ post)%string "|" ("|" ++ post)%string
                (le_n _) eq_refl eq_refl eq_refl (Forall_nil _) Et)).
Qed.

(** PT1, only if: every row line starts and ends with a bar, after any
    indentation and before any trailing whitespace, and has at least one
    cell. *)
Theorem table_row_shape : forall l r,
  table_row l = Some r ->
  (exists pre x post, is_blank pre = true /\ is_blank post = true /\
     l = pre ++ "|" ++ x ++ "|" ++ post) /\
  match r with TSep als => als <> [] | TCells cs => cs <> [] end.
Proof.
  intros l r H. unfold table_row in H.
  destruct (row_body l) as [body|] eqn:Eb; [|discriminate].
  destruct (row_body_shape l body Eb) as (pre & x & post & Hpre & Hpost & _ & El).
  split; [exists pre, x, post; auto|].
  destruct (sep_cells body) as [[|a als]|].
  3: { unfold row_cells in H.
       destruct (row_cells_trace _ _ _ _ _ _ _ _) as [xs|] eqn:Et; [|discriminate].
       injection H as <-. intros E. apply map_eq_nil in E. subst xs.
       exact (row_cells_trace_nonempty _ _ _ _ _ _ _ _ _ [] (le_n _) Et eq_refl). }
  2: { injection H as <-. discriminate. }
  unfold row_cells in H.
  destruct (row_cells_trace _ _ _ _ _ _ _ _) as [xs|] eqn:Et; [|discriminate].
  injection H as <-. intros E. apply map_eq_nil in E. subst xs.
  exact (row_cells_trace_nonempty _ _ _ _ _ _ _ _ _ [] (le_n _) Et eq_refl).
Qed.

Local Lemma sct_ends_bar : forall a b n w cells,
  exists x, separator_cell_text a b n w ++ separator_text cells = x ++ "|".
Proof.
  intros a b n w cells. revert a b n w.
  induction cells as [|[[[[w0 a'] b'] n'] w'] cells IH]; intros a b n w.
  - exists (separator_colon a (char_run "-" n ++ separator_colon b w)).
    unfold separator_cell_text. cbn [separator_text]. rewrite append_empty_r.
    destruct a, b; cbn [separator_colon append]; rewrite ?append_assoc; reflexivity.
  - destruct (IH a' b' (S n') w') as (x & E).
    exists (separator_cell_text a b n w ++ w0 ++ x). cbn [separator_text]. rewrite E, !append_assoc. reflexivity.
Qed.

Local Lemma colon_split : forall s left s1,
  match s with
  | String c r => if Ascii.eqb c ":" then (true, r) else (false, s)
  | EmptyString => (false, s)
  end = (left, s1) -> s = separator_colon left s1.
Proof.
  intros [|c r] left s1 H; [injection H as <- <-; reflexivity|].
  destruct (Ascii.eqb c ":") eqn:E; injection H as <- <-; [|reflexivity].
  apply Ascii.eqb_eq in E. subst c. reflexivity.
Qed.

Local Lemma sep_cell_inv : forall s al rest,
  sep_cell s = Some (al, rest) ->
  exists a b n w r, is_blank w = true /\ s = separator_cell_text a b (S n) w ++ r /\
    rest = drop_leading_ws r /\ al = separator_alignment a b.
Proof.
  intros s al rest H. unfold sep_cell in H.
  match type of H with
  | context [match ?m with (_, _) => _ end] => destruct m as [left s1] eqn:E1
  end.
  apply colon_split in E1.
  destruct (count_run "-" s1) as [[|n] s2] eqn:E2; [discriminate|].
  apply count_run_split in E2.
  match type of H with
  | context [match ?m with (_, _) => _ end] => destruct m as [right s3] eqn:E3
  end.
  apply colon_split in E3.
  destruct (drop_leading_ws_split s3) as (w & Hw & E4).
  destruct (drop_leading_ws s3) as [|c r]; [discriminate|].
  destruct (Ascii.eqb c "|") eqn:Ec; [|discriminate].
  apply Ascii.eqb_eq in Ec. subst c. injection H as <- <-.
  exists left, right, n, w, r. split; [exact Hw|]. split; [|split; [reflexivity|]].
  - rewrite separator_cell_text_app, E1, E2, E3, E4. reflexivity.
  - destruct left, right; reflexivity.
Qed.

Local Lemma sep_fuel_inv : forall fuel s als,
  sep_cells_fuel fuel s = Some als -> s <> EmptyString ->
  exists a b n w cells t, is_blank w = true /\ Forall separator_ws_ok cells /\
    is_blank t = true /\ s = separator_cell_text a b (S n) w ++ separator_text cells ++ t /\
    als = separator_alignment a b :: separator_alignments cells.
Proof.
  induction fuel as [|fuel IH]; intros s als H Hs; [discriminate|].
  destruct s as [|c s']; [contradiction|].
  cbn [sep_cells_fuel] in H.
  destruct (sep_cell (String c s')) as [[al rest]|] eqn:Ec; [|discriminate].
  destruct (sep_cells_fuel fuel rest) as [als'|] eqn:Er; [|discriminate].
  injection H as <-.
  destruct (sep_cell_inv _ _ _ Ec) as (a & b & n & w & r & Hw & Es & Erest & Eal).
  destruct rest as [|c' rest'].
  - destruct fuel; [discriminate|]. injection Er as <-.
    exists a, b, n, w, [], r.
    split; [exact Hw|]. split; [constructor|].
    split; [apply drop_leading_ws_empty; symmetry; exact Erest|].
    split; [rewrite Es; reflexivity|rewrite Eal; reflexivity].
  - destruct (IH _ _ Er ltac:(discriminate))
      as (a' & b' & n' & w' & cells & t & Hw' & Hcs & Ht & E' & Eals).
    destruct (drop_leading_ws_split r) as (w0 & Hw0 & Er0).
    exists a, b, n, w, ((w0, a', b', n', w') :: cells), t.
    split; [exact Hw|]. split; [constructor; [split; assumption|exact Hcs]|].
    split; [exact Ht|]. split.
    + rewrite Es, Er0, <- Erest, E'. cbn [separator_text]. rewrite !append_assoc. reflexivity.
    + rewrite Eal, Eals. reflexivity.
Qed.

Local Lemma bar_blank_end : forall y t x,
  y ++ t = x ++ "|" -> is_blank t = true -> t = EmptyString.
Proof.
  intros y t x E Ht. apply (f_equal rev_string) in E.
  rewrite rev_string_app, rev_bar in E.
  destruct (rev_string t) as [|d u] eqn:Et.
  - rewrite <- (rev_string_involutive t), Et. reflexivity.
  - exfalso. cbn [append] in E. injection E as Ed _. subst d.
    rewrite <- rev_blank, Et in Ht. discriminate.
Qed.

Local Lemma row_body_padded : forall pre x post,
  is_blank pre = true -> is_blank post = true ->
  row_body (pre ++ String "|" (x ++ "|" ++ post)) = Some (x ++ "|").
Proof.
  intros pre x post Hpre Hpost. unfold row_body.
  rewrite (drop_leading_ws_ws_prefix pre _ Hpre). cbn [drop_leading_ws].
  change (is_ws "|") with false. cbn iota.
  change (negb (Ascii.eqb "|" "|")) with false. cbn iota.
  rewrite <- append_assoc, strip_trailing_ws_app_blank by exact Hpost.
  rewrite strip_trailing_bar, rev_bar. reflexivity.
Qed.

(** PT2: a line is a separator exactly when it is `|` followed by
    separator cells -- an optional `:`, one or more dashes, an optional
    `:`, whitespace, and a bar -- with whitespace between them but none
    before the first.  The alignments are read off the colons. *)
Theorem table_row_separator : forall l als,
  table_row l = Some (TSep als) <->
  exists pre a b n w cells post,
    is_blank pre = true /\ is_blank post = true /\ is_blank w = true /\
    Forall separator_ws_ok cells /\
    l = pre ++ "|" ++ separator_cell_text a b (S n) w ++ separator_text cells ++ post /\
    als = separator_alignment a b :: separator_alignments cells.
Proof.
  intros l als. split.
  - intros H. unfold table_row in H.
    destruct (row_body l) as [body|] eqn:Eb; [|discriminate].
    destruct (row_body_shape l body Eb) as (pre & x & post & Hpre & Hpost & Ebody & El).
    destruct (sep_cells body) as [[|a0 als0]|] eqn:Es.
    2: { injection H as <-. unfold sep_cells in Es.
         destruct (sep_fuel_inv _ _ _ Es)
           as (a & b & n & w & cells & t & Hw & Hcs & Ht & E & Eals).
         { rewrite Ebody. destruct x; discriminate. }
         assert (t = EmptyString) as ->.
         { apply (bar_blank_end (separator_cell_text a b (S n) w ++ separator_text cells) t x); [|exact Ht].
           rewrite append_assoc, <- E, Ebody. reflexivity. }
         exists pre, a, b, n, w, cells, post.
         split; [exact Hpre|]. split; [exact Hpost|]. split; [exact Hw|].
         split; [exact Hcs|]. split; [|exact Eals].
         rewrite El. rewrite append_empty_r in E.
         replace (x ++ "|" ++ post) with ((x ++ "|") ++ post) by apply append_assoc.
         rewrite <- Ebody, E, !append_assoc. reflexivity. }
    all: destruct (row_cells _ _ _ _ _ _); discriminate.
  - intros (pre & a & b & n & w & cells & post & Hpre & Hpost & Hw & Hcs & El & Eals).
    subst l als. unfold table_row.
    destruct (sct_ends_bar a b (S n) w cells) as (x & Ex).
    replace (pre ++ "|" ++ separator_cell_text a b (S n) w ++ separator_text cells ++ post)
      with (pre ++ String "|" (x ++ "|" ++ post))
      by (rewrite <- (append_assoc x "|" post), <- Ex, !append_assoc; reflexivity).
    rewrite (row_body_padded pre x post Hpre Hpost), <- Ex.
    rewrite (separator_row_alignments a b n w cells Hw Hcs). reflexivity.
Qed.

(* A table caption: `^` and at least one space or tab, then the first
   line of the caption's inline content.

   Not a `line_kind`: only a table's continuation consults it, so a
   caption with no table before it is a paragraph, as djoths reads it.
   djot.js opens a caption wherever a block may start and renders an
   orphan one as nothing (`.project/djotjs-divergences.md`). *)
Definition caption_open (l : string) : option string :=
  match drop_leading_ws l with
  | String c rest =>
      if negb (Ascii.eqb c "^") then None
      else match rest with
           | String c' _ => if is_ws c' then Some (drop_leading_ws rest) else None
           | EmptyString => None
           end
  | EmptyString => None
  end.

Local Open Scope string_scope.

Example caption_open_space : caption_open "^ cap" = Some "cap".
Proof. reflexivity. Qed.

(* A tab opens one too, and `^` alone does not: the pattern needs at
   least one space or tab after the caret. *)
Example caption_open_tab : caption_open "^	cap" = Some "cap".
Proof. reflexivity. Qed.

Example caption_open_bare : caption_open "^cap" = None.
Proof. reflexivity. Qed.

Example caption_open_empty : caption_open "^ " = Some "".
Proof. reflexivity. Qed.

Local Open Scope char_scope.

(* A blank line opens nothing: the caret has to be the first nonblank
   character, and a blank line has none. *)
Lemma drop_leading_ws_blank :
  forall s, is_blank s = true -> drop_leading_ws s = EmptyString.
Proof.
  induction s as [|c s IH]; [reflexivity|].
  cbn [is_blank drop_leading_ws]. destruct (is_ws c) eqn:E; [exact IH|discriminate].
Qed.

(* A blank line underlines nothing, whatever the setting. *)
Lemma underline_of_blank :
  forall l, is_blank l = true -> underline_of l = None.
Proof.
  intros l H. unfold underline_of.
  rewrite (drop_leading_ws_blank l H). reflexivity.
Qed.

Lemma caption_open_blank :
  forall l, is_blank l = true -> caption_open l = None.
Proof.
  intros l H. unfold caption_open. rewrite (drop_leading_ws_blank l H).
  reflexivity.
Qed.

Lemma caption_open_ws_prefix :
  forall p l, is_blank p = true -> caption_open (p ++ l) = caption_open l.
Proof.
  intros p l Hp. unfold caption_open.
  rewrite (drop_leading_ws_ws_prefix p l Hp). reflexivity.
Qed.

(* Leading whitespace is invisible here too. *)
Local Lemma table_row_ws_prefix :
  forall p l, is_blank p = true -> table_row (p ++ l) = table_row l.
Proof.
  intros p l Hp. unfold table_row, row_body.
  rewrite (drop_leading_ws_ws_prefix p l Hp). reflexivity.
Qed.

(* The classifier: one line in, one kind out, no lookahead.  The
   recognizers are tried in the order below; anything unrecognized is
   paragraph text. *)
Definition classify (l : string) : line_kind :=
  if is_blank l then KBlank
  else match quote_prefix l with
       | Some rest => KQuote rest
       | None =>
           match heading_open l with
           | Some (lvl, rest) => KHeading lvl rest
           | None =>
               match fence_open l with
               | Some f => KFence f
               | None =>
                   match div_open l with
                   | Some (n, cls) => KDiv n cls
                   | None =>
                       if is_thematic l then KThematic
                       else match list_marker l with
                            | Some (sty, core, chk, rest) => KList sty core chk rest
                            | None =>
                                match attr_open l with
                                | Some p => KAttr p
                                | None =>
                                    match foot_open l with
                                    | Some (lbl, rest) => KFoot lbl rest
                                    | None =>
                                        match ref_open l with
                                        | Some (lbl, v) => KRef lbl v
                                        | None =>
                                            match table_row l with
                                            | Some r => KRow r
                                            | None => KText
                                            end
                                        end
                                    end
                                end
                            end
                   end
               end
           end
       end.

(* Two colons are not a marker; three are a div. *)
Example classify_two_colons : classify ":: a" = KText.
Proof. reflexivity. Qed.

Example classify_three_colons : classify "::: a" = KDiv 3 "a".
Proof. reflexivity. Qed.

Example classify_colon_marker :
  classify ": a" = KList [SBullet ":"%char] EmptyString None "a"%string.
Proof. reflexivity. Qed.

(* A heading's level is at least 1. *)
Lemma classify_heading_level :
  forall l lvl rest, classify l = KHeading lvl rest -> Nat.leb 1 lvl = true.
Proof.
  intros l lvl rest H. unfold classify in H.
  destruct (is_blank l); [discriminate|].
  destruct (quote_prefix l); [discriminate|].
  unfold heading_open in H.
  destruct (count_run "#" (drop_leading_ws l)) as [n r].
  destruct (Nat.leb 1 n) eqn:E.
  - destruct r as [|c r']; [injection H as <- <-; exact E|].
    destruct (is_ws c); [injection H as <- <-; exact E|].
    destruct (fence_open l); [discriminate|].
    destruct (div_open l) as [[dn dc]|]; [discriminate|].
    destruct (is_thematic l); [discriminate|].
    destruct (list_marker l) as [[[[s0 c0] k0] r0]|]; [discriminate|].
    destruct (attr_open l); [discriminate|].
    destruct (foot_open l) as [[fl fr]|]; [discriminate|].
    destruct (ref_open l) as [[rl rv]|]; [discriminate|].
    destruct (table_row l); discriminate.
  - destruct (fence_open l); [discriminate|].
  destruct (div_open l) as [[dn dc]|]; [discriminate|].
    destruct (is_thematic l); [discriminate|].
    destruct (list_marker l) as [[[[s0 c0] k0] r0]|]; [discriminate|].
    destruct (attr_open l); [discriminate|].
    destruct (foot_open l) as [[fl fr]|]; [discriminate|].
    destruct (ref_open l) as [[rl rv]|]; [discriminate|].
    destruct (table_row l); discriminate.
Qed.

(*
Classification facts
====================
*)

Lemma classify_blank :
  forall l, is_blank l = true -> classify l = KBlank.
Proof. intros l H. unfold classify. rewrite H. reflexivity. Qed.

Lemma classify_kblank_blank :
  forall l, classify l = KBlank -> is_blank l = true.
Proof.
  intros l H. unfold classify in H.
  destruct (is_blank l); [reflexivity|].
  destruct (quote_prefix l); [discriminate|].
  destruct (heading_open l) as [[lvl rest]|]; [discriminate|].
  destruct (fence_open l); [discriminate|].
  destruct (div_open l) as [[dn dc]|]; [discriminate|].
  destruct (is_thematic l); [discriminate|].
  destruct (list_marker l) as [[[[s0 c0] k0] r0]|]; [discriminate|].
  destruct (attr_open l); [discriminate|].
  destruct (foot_open l) as [[fl fr]|]; [discriminate|].
    destruct (ref_open l) as [[rl rv]|]; [discriminate|].
    destruct (table_row l); discriminate.
Qed.

(* `quote_prefix_length` at the classifier, which is what the parser
   sees. *)
Lemma classify_quote_length :
  forall l rest,
    classify l = KQuote rest -> String.length rest < String.length l.
Proof.
  intros l rest H. apply quote_prefix_length.
  unfold classify in H.
  destruct (is_blank l); [discriminate|].
  destruct (quote_prefix l) as [r|].
  - injection H as <-. reflexivity.
  - destruct (heading_open l) as [[lvl r2]|]; [discriminate|].
    destruct (fence_open l); [discriminate|].
    destruct (div_open l) as [[dn dc]|]; [discriminate|].
    destruct (is_thematic l); [discriminate|].
    destruct (list_marker l) as [[[[s0 c0] k0] r0]|]; [discriminate|].
    destruct (attr_open l); [discriminate|].
    destruct (foot_open l) as [[fl fr]|]; [discriminate|].
    destruct (ref_open l) as [[rl rv]|]; [discriminate|].
    destruct (table_row l); discriminate.
Qed.

Lemma classify_list_length :
  forall l sty core chk rest,
    classify l = KList sty core chk rest ->
    String.length rest < String.length l.
Proof.
  intros l sty core chk rest H. apply (list_marker_length l sty core chk).
  unfold classify in H.
  destruct (is_blank l); [discriminate|].
  destruct (quote_prefix l); [discriminate|].
  destruct (heading_open l) as [[lvl r2]|]; [discriminate|].
  destruct (fence_open l); [discriminate|].
  destruct (div_open l) as [[dn dc]|]; [discriminate|].
  destruct (is_thematic l); [discriminate|].
  destruct (list_marker l) as [[[[s' c'] k'] r']|];
    [|destruct (attr_open l); [discriminate|];
      destruct (foot_open l) as [[fl fr]|]; [discriminate|];
      destruct (ref_open l) as [[rl rv]|]; [discriminate|];
      destruct (table_row l); discriminate].
  injection H as <- <- <- <-. reflexivity.
Qed.

Lemma classify_list_literal_length :
  forall l sty core chk rest,
    classify l = KList sty core chk rest ->
    String.length (task_literal_rest chk rest) < String.length l.
Proof.
  intros l sty core chk rest H.
  apply (list_marker_literal_length l sty core chk).
  unfold classify in H.
  destruct (is_blank l); [discriminate|].
  destruct (quote_prefix l); [discriminate|].
  destruct (heading_open l) as [[lvl r2]|]; [discriminate|].
  destruct (fence_open l); [discriminate|].
  destruct (div_open l) as [[dn dc]|]; [discriminate|].
  destruct (is_thematic l); [discriminate|].
  destruct (list_marker l) as [[[[s' c'] k'] r']|];
    [|destruct (attr_open l); [discriminate|];
      destruct (foot_open l) as [[fl fr]|]; [discriminate|];
      destruct (ref_open l) as [[rl rv]|]; [discriminate|];
      destruct (table_row l); discriminate].
  injection H as <- <- <- <-. reflexivity.
Qed.

(*
Suffixes
--------

Every residue the classifier hands on is what is left of the line after
a prefix: the parser cuts lines from the left only.  The located parse
counts positions from the end of a line, and this is why that count is
the same in the residue and in the line.
*)

Local Lemma take_while_sfx : forall p s, is_sfx (snd (take_while p s)) s.
Proof.
  intros p s. induction s as [|c s IH]; [apply is_sfx_refl|].
  cbn [take_while]. destruct (p c); [|apply is_sfx_refl].
  destruct (take_while p s) as [a b]. apply is_sfx_cons, IH.
Qed.

Local Lemma count_run_sfx : forall c s, is_sfx (snd (count_run c s)) s.
Proof.
  intros c s. induction s as [|c' s IH]; [apply is_sfx_refl|].
  cbn [count_run]. destruct (Ascii.eqb c c'); [|apply is_sfx_refl].
  destruct (count_run c s) as [n r]. apply is_sfx_cons, IH.
Qed.

Local Lemma marker_shape_sfx :
  forall s core d r, marker_shape s = Some (core, d, r) -> is_sfx r s.
Proof.
  intros s core d r H. unfold marker_shape in H.
  destruct s as [|c s']; [discriminate|].
  destruct (Ascii.eqb c "(").
  - pose proof (take_while_sfx is_alnum s') as Hs.
    destruct (take_while is_alnum s') as [a b]. cbn [snd] in Hs.
    destruct b as [|c' b']; [discriminate|].
    destruct (Ascii.eqb c' ")"); [|discriminate].
    injection H as _ _ <-. apply is_sfx_cons. exact (is_sfx_trans _ _ _ (is_sfx_tail c' b') Hs).
  - pose proof (take_while_sfx is_alnum (String c s')) as Hs.
    destruct (take_while is_alnum (String c s')) as [a b]. cbn [snd] in Hs.
    destruct b as [|c' b']; [discriminate|].
    assert (Ht : is_sfx b' (String c s')) by exact (is_sfx_trans _ _ _ (is_sfx_tail c' b') Hs).
    destruct (Ascii.eqb c' "."); [injection H as _ _ <-; exact Ht|].
    destruct (Ascii.eqb c' ")"); [injection H as _ _ <-; exact Ht|discriminate].
Qed.

Local Lemma list_marker_sfx :
  forall l sty core chk rest,
    list_marker l = Some (sty, core, chk, rest) ->
    is_sfx (task_literal_rest chk rest) l.
Proof.
  intros l sty core chk rest H. unfold list_marker in H.
  pose proof (drop_leading_ws_sfx l) as Hd.
  destruct (drop_leading_ws l) as [|c r] eqn:E; [discriminate|].
  apply (fun h => is_sfx_trans _ _ _ h Hd).
  destruct (is_bullet c).
  - destruct r as [|c' r'].
    + injection H as _ _ <- <-. apply is_sfx_empty.
    + destruct (is_ws c'); [|discriminate].
      apply is_sfx_cons, is_sfx_cons.
      destruct (if is_task_bullet c then task_check r' else None)
        as [[m tr]|] eqn:Et.
      * injection H as _ _ <- <-. unfold task_literal_rest.
        destruct (is_task_bullet c); [|discriminate Et].
        rewrite <- (task_check_source _ _ _ Et). apply is_sfx_refl.
      * injection H as _ _ <- <-. apply is_sfx_refl.
  - pose proof (marker_shape_sfx (String c r)) as Hms.
    destruct (marker_shape (String c r)) as [[[core' d] r0]|] eqn:Em;
      [|discriminate].
    specialize (Hms _ _ _ eq_refl).
    destruct (styles_of_core core' d) as [|s0 ss]; [discriminate|].
    destruct r0 as [|c' r0'].
    + injection H as _ _ <- <-. apply is_sfx_empty.
    + destruct (is_ws c'); [|discriminate].
      injection H as _ _ <- <-.
      exact (is_sfx_trans _ _ _ (is_sfx_tail c' r0') Hms).
Qed.

Local Lemma ref_label_sfx :
  forall s lbl tail, ref_label s = Some (lbl, tail) -> is_sfx tail s.
Proof.
  induction s as [|c s IH]; intros lbl tail H; [discriminate|].
  cbn [ref_label] in H. destruct (Ascii.eqb c "]").
  - injection H as _ <-. apply is_sfx_tail.
  - destruct (ref_label s) as [[l t]|] eqn:E; [|discriminate].
    injection H as _ <-. exact (is_sfx_cons _ _ _ (IH l t eq_refl)).
Qed.

Local Lemma foot_open_sfx :
  forall l lbl rest, foot_open l = Some (lbl, rest) -> is_sfx rest l.
Proof.
  intros l lbl rest H. unfold foot_open in H.
  pose proof (drop_leading_ws_sfx l) as Hd.
  destruct (drop_leading_ws l) as [|c [|h r]]; try discriminate.
  apply (fun x => is_sfx_trans _ _ _ x Hd). apply is_sfx_cons, is_sfx_cons.
  destruct (negb (Ascii.eqb c "[")); [discriminate|].
  destruct (negb (Ascii.eqb h "^")); [discriminate|].
  destruct (ref_label r) as [[lb [|col after]]|] eqn:Er; try discriminate.
  apply ref_label_sfx in Er.
  destruct (negb (Ascii.eqb col ":")); [discriminate|].
  destruct (negb (nonempty_str lb)); [discriminate|].
  destruct after as [|w body].
  - injection H as _ <-. apply is_sfx_empty.
  - destruct (is_ws w); [|discriminate]. injection H as _ <-.
    refine (is_sfx_trans _ _ _ _ Er). apply is_sfx_cons, is_sfx_tail.
Qed.

Lemma quote_prefix_sfx : forall l rest, quote_prefix l = Some rest -> is_sfx rest l.
Proof.
  intros l rest H. unfold quote_prefix in H.
  pose proof (drop_leading_ws_sfx l) as Hd.
  destruct (drop_leading_ws l) as [|c r]; [discriminate|].
  apply (fun x => is_sfx_trans _ _ _ x Hd).
  destruct (Ascii.eqb c ">"); [|discriminate].
  destruct r as [|c' r'].
  - injection H as <-. apply is_sfx_empty.
  - destruct (is_ws c'); [|discriminate]. injection H as <-.
    apply is_sfx_cons, is_sfx_tail.
Qed.

Local Lemma heading_open_sfx :
  forall l lvl rest, heading_open l = Some (lvl, rest) -> is_sfx rest l.
Proof.
  intros l lvl rest H. unfold heading_open in H.
  pose proof (drop_leading_ws_sfx l) as Hd.
  pose proof (count_run_sfx "#" (drop_leading_ws l)) as Hc.
  destruct (count_run "#" (drop_leading_ws l)) as [n r]. cbn [snd] in Hc.
  apply (fun x => is_sfx_trans _ _ _ x (is_sfx_trans _ _ _ Hc Hd)).
  destruct (Nat.leb 1 n); [|discriminate].
  destruct r as [|c r'].
  - injection H as _ <-. apply is_sfx_empty.
  - destruct (is_ws c); [|discriminate]. injection H as _ <-. apply is_sfx_tail.
Qed.

(** What the classifier hands on is a suffix of the line: the residue a
    quote, a heading, a footnote or a list marker leaves, the last with
    its task box put back. *)
Lemma classify_sfx :
  forall l,
    match classify l with
    | KQuote rest | KHeading _ rest | KFoot _ rest => is_sfx rest l
    | KList _ _ chk rest => is_sfx (task_literal_rest chk rest) l
    | _ => True
    end.
Proof.
  intros l. unfold classify.
  destruct (is_blank l); [exact I|].
  destruct (quote_prefix l) as [r|] eqn:Eq; [exact (quote_prefix_sfx _ _ Eq)|].
  destruct (heading_open l) as [[lvl r]|] eqn:Eh; [exact (heading_open_sfx _ _ _ Eh)|].
  destruct (fence_open l); [exact I|].
  destruct (div_open l) as [[dn dc]|]; [exact I|].
  destruct (is_thematic l); [exact I|].
  destruct (list_marker l) as [[[[s c] k] r]|] eqn:El; [exact (list_marker_sfx _ _ _ _ _ El)|].
  destruct (attr_open l); [exact I|].
  destruct (foot_open l) as [[fl fr]|] eqn:Ef; [exact (foot_open_sfx _ _ _ Ef)|].
  destruct (ref_open l) as [[rl rv]|]; [exact I|].
  destruct (table_row l); exact I.
Qed.

(* A row line is one `table_row` reads as that row. *)
Lemma classify_row : forall l r, classify l = KRow r -> table_row l = Some r.
Proof.
  intros l r H. unfold classify in H.
  destruct (is_blank l); [discriminate|].
  destruct (quote_prefix l); [discriminate|].
  destruct (heading_open l) as [[lvl r2]|]; [discriminate|].
  destruct (fence_open l); [discriminate|].
  destruct (div_open l) as [[dn dc]|]; [discriminate|].
  destruct (is_thematic l); [discriminate|].
  destruct (list_marker l) as [[[[s0 c0] k0] r0]|]; [discriminate|].
  destruct (attr_open l); [discriminate|].
  destruct (foot_open l) as [[fl fr]|]; [discriminate|].
  destruct (ref_open l) as [[rl rv]|]; [discriminate|].
  destruct (table_row l); [injection H as <-; reflexivity|discriminate].
Qed.

Lemma task_literal_rest_sfx : forall chk rest, is_sfx rest (task_literal_rest chk rest).
Proof.
  intros [m|] rest; [exists (task_marker_source m); reflexivity|apply is_sfx_refl].
Qed.

Lemma caption_open_sfx : forall l rest, caption_open l = Some rest -> is_sfx rest l.
Proof.
  intros l rest H. unfold caption_open in H.
  pose proof (drop_leading_ws_sfx l) as Hd.
  destruct (drop_leading_ws l) as [|c r]; [discriminate|].
  apply (fun x => is_sfx_trans _ _ _ x Hd).
  destruct (negb (Ascii.eqb c "^")); [discriminate|].
  destruct r as [|c' r']; [discriminate|].
  destruct (is_ws c'); [|discriminate]. injection H as <-.
  apply is_sfx_cons, drop_leading_ws_sfx.
Qed.

Lemma callout_header_sfx :
  forall s kind fold title,
    callout_header s = Some (kind, fold, title) -> is_sfx title s.
Proof.
  intros s kind fold title H. unfold callout_header in H.
  destruct s as [|a [|b rest]]; try discriminate.
  destruct (Ascii.eqb a "[" && Ascii.eqb b "!")%bool; [|discriminate].
  apply is_sfx_cons, is_sfx_cons.
  pose proof (take_while_sfx callout_kind_char rest) as Hs.
  destruct (take_while callout_kind_char rest) as [k r]. cbn [snd] in Hs.
  refine (is_sfx_trans _ _ _ _ Hs).
  destruct k as [|k0 k']; [discriminate|].
  destruct r as [|ch tail]; [discriminate|].
  apply is_sfx_cons.
  (* The fold marker, when there is one, is one byte. *)
  assert (Hf : forall t, is_sfx (snd (match t with
              | String "+" more => (Some FoldExpanded, more)
              | String "-" more => (Some FoldCollapsed, more)
              | String _ _ => (None, t)
              | EmptyString => (None, EmptyString)
              end)) t).
  { intros [|x more]; [apply is_sfx_refl|].
    destruct x as [[] [] [] [] [] [] [] []]; cbn [snd];
      first [apply is_sfx_tail|apply is_sfx_refl]. }
  destruct ch as [[] [] [] [] [] [] [] []]; try discriminate H.
  specialize (Hf tail).
  destruct (match tail with
              | String "+" more => (Some FoldExpanded, more)
              | String "-" more => (Some FoldCollapsed, more)
              | String _ _ => (None, tail)
              | EmptyString => (None, EmptyString)
              end) as [fo t2]. cbn [snd] in Hf.
  refine (is_sfx_trans _ _ _ _ Hf).
  destruct t2 as [|c t3]; [injection H as _ _ <-; apply is_sfx_empty|].
  destruct (callout_sep c); [|discriminate].
  injection H as _ _ <-. apply is_sfx_cons, drop_leading_ws_sfx.
Qed.

Local Lemma classify_not_kblank_nonblank :
  forall l, classify l <> KBlank -> is_blank l = false.
Proof.
  intros l H. destruct (is_blank l) eqn:E; [|reflexivity].
  exfalso. apply H, classify_blank, E.
Qed.

Local Lemma classify_ktext :
  forall l,
    is_blank l = false -> quote_prefix l = None -> heading_open l = None ->
    fence_open l = None -> div_open l = None ->
    is_thematic l = false -> list_marker l = None -> attr_open l = None ->
    foot_open l = None ->
    ref_open l = None ->
    table_row l = None ->
    classify l = KText.
Proof.
  intros l Hb Hq Hh Hf Hd Ht Hm Ha Hfoot Hr Hrow. unfold classify.
  rewrite Hb, Hq, Hh, Hf, Hd, Ht, Hm, Ha, Hfoot, Hr, Hrow. reflexivity.
Qed.

(* The canonical thematic-break rendering classifies as one. *)
Lemma classify_canonical_thematic : classify "* * * *" = KThematic.
Proof. reflexivity. Qed.

(* A spec line is one `attr_open` accepts. *)
Lemma classify_attr_open : forall l ap, classify l = KAttr ap -> attr_open l = Some ap.
Proof.
  intros l ap H. unfold classify in H.
  destruct (is_blank l); [discriminate|].
  destruct (quote_prefix l); [discriminate|].
  destruct (heading_open l) as [[? ?]|]; [discriminate|].
  destruct (fence_open l); [discriminate|].
  destruct (div_open l) as [[? ?]|]; [discriminate|].
  destruct (is_thematic l); [discriminate|].
  destruct (list_marker l) as [[[[? ?] ?] ?]|]; [discriminate|].
  destruct (attr_open l); [congruence|].
  repeat match type of H with
         | context [match ?x with _ => _ end] => destruct x
         | context [if ?x then _ else _] => destruct x
         end; discriminate.
Qed.

(* An all-whitespace prefix is invisible to the classifier: every
   recognizer reads through drop_leading_ws, and is_thematic skips
   whitespace anywhere.  So a list item's continuation indent can be
   pushed through: the enclosed line classifies as it would
   unindented. *)
Lemma classify_ws_prefix :
  forall p l, is_blank p = true -> classify (p ++ l) = classify l.
Proof.
  intros p l Hp. unfold classify.
  rewrite (is_blank_ws_prefix p l Hp).
  destruct (is_blank l) eqn:Eb; [reflexivity|].
  unfold quote_prefix, heading_open, fence_open, div_open, list_marker.
  rewrite (drop_leading_ws_ws_prefix p l Hp).
  fold (is_thematic l). rewrite <- (is_thematic_ws_prefix p l Hp).
  rewrite (attr_open_ws_prefix p l Hp), (foot_open_ws_prefix p l Hp),
          (ref_open_ws_prefix p l Hp), (table_row_ws_prefix p l Hp).
  unfold is_thematic. reflexivity.
Qed.

Lemma classify_kfoot :
  forall l lbl rest,
    classify l = KFoot lbl rest -> foot_open l = Some (lbl, rest).
Proof.
  intros l lbl rest H. unfold classify in H.
  destruct (is_blank l); [discriminate|].
  destruct (quote_prefix l); [discriminate|].
  destruct (heading_open l) as [[hl hr]|]; [discriminate|].
  destruct (fence_open l); [discriminate|].
  destruct (div_open l) as [[dn dc]|]; [discriminate|].
  destruct (is_thematic l); [discriminate|].
  destruct (list_marker l) as [[[[s0 c0] k0] r0]|]; [discriminate|].
  destruct (attr_open l); [discriminate|].
  destruct (foot_open l) as [[fl fr]|]; [injection H as <- <-; reflexivity|].
  destruct (ref_open l) as [[rl rv]|]; [discriminate|].
    destruct (table_row l); discriminate.
Qed.

Lemma classify_foot_length :
  forall l lbl rest,
    classify l = KFoot lbl rest -> String.length rest < String.length l.
Proof.
  intros l lbl rest H. apply (foot_open_length l lbl rest).
  exact (classify_kfoot l lbl rest H).
Qed.

(* A KRef classification is `ref_open`'s answer. *)
Lemma classify_kref :
  forall l lbl v, classify l = KRef lbl v -> ref_open l = Some (lbl, v).
Proof.
  intros l lbl v H. unfold classify in H.
  destruct (is_blank l); [discriminate|].
  destruct (quote_prefix l); [discriminate|].
  destruct (heading_open l) as [[hl hr]|]; [discriminate|].
  destruct (fence_open l); [discriminate|].
  destruct (div_open l) as [[dn dc]|]; [discriminate|].
  destruct (is_thematic l); [discriminate|].
  destruct (list_marker l) as [[[[s0 c0] k0] r0]|]; [discriminate|].
  destruct (attr_open l); [discriminate|].
  destruct (foot_open l) as [[fl fr]|]; [discriminate|].
  destruct (ref_open l) as [[rl rv]|]; [|destruct (table_row l); discriminate].
  injection H as <- <-. reflexivity.
Qed.

(* The canonical rendering of a reference definition classifies as one.
   Nothing earlier in the chain can claim the line: every other recognizer
   decides on the first nonblank character, and that is `[`.  The three
   hypotheses are exactly `Render.ref_ok` minus its `no_nl`, which the
   line-level conditions carry instead. *)
Lemma classify_canonical_ref :
  forall label dest,
    no_char "]"%char label = true ->
    is_footnote_label label = false ->
    no_ws dest = true ->
    classify ("[" ++ label ++ "]: " ++ dest) = KRef label dest.
Proof.
  intros label dest Hlbl Hfn Hd.
  assert (Hlab : forall tail,
            no_char "]"%char label = true ->
            ref_label (label ++ String "]" tail) = Some (label, tail)).
  { clear. induction label as [|c lbl IH]; intros tail H; [reflexivity|].
    cbn [no_char] in H. apply andb_true_iff in H as [Hc Hlbl].
    apply negb_true_iff in Hc.
    cbn [append ref_label]. rewrite Hc, (IH tail Hlbl). reflexivity. }
  assert (Hro : ref_open ("[" ++ label ++ "]: " ++ dest) = Some (label, dest)).
  { unfold ref_open. cbn [append drop_leading_ws is_ws Ascii.eqb orb].
    change (is_ws "[") with false. cbn [negb Ascii.eqb].
    rewrite (Hlab (String ":" (String " " dest)) Hlbl).
    cbn [eqb negb Ascii.eqb]. rewrite Hfn. unfold ref_value.
    change (is_ws " ") with true. cbn [drop_leading_ws].
    change (is_ws " ") with true. cbn [andb].
    rewrite (no_ws_drop_leading_ws dest Hd), Hd. reflexivity. }
  assert (Hdrop : drop_leading_ws ("[" ++ label ++ "]: " ++ dest)
                  = "[" ++ label ++ "]: " ++ dest).
  { cbn [append drop_leading_ws]. change (is_ws "[") with false. reflexivity. }
  assert (Hfo : foot_open ("[" ++ label ++ "]: " ++ dest) = None).
  { unfold foot_open. rewrite Hdrop. cbn [append].
    destruct label as [|c [|d rest]].
    - reflexivity.
    - cbn [append ref_label nonempty_str Ascii.eqb negb].
      destruct (Ascii.eqb c "^"); reflexivity.
    - cbn [is_footnote_label] in Hfn.
      destruct (Ascii.eqb c "^") eqn:Ec.
      + apply Ascii.eqb_eq in Ec. subst c. discriminate.
      + cbn [append ref_label nonempty_str Ascii.eqb negb].
        rewrite Ec. reflexivity. }
  unfold classify.
  change (is_blank ("[" ++ label ++ "]: " ++ dest)) with false.
  unfold quote_prefix, heading_open, fence_open, div_open, list_marker,
    attr_open, is_thematic.
  (* `Hro` has to be rewritten before `append` reduces, or its left-hand
     side no longer appears syntactically *)
  rewrite !Hdrop, Hfo, Hro. cbn [append].
  cbn [count_run thematic_count is_marker is_ws is_bullet marker_shape
       Ascii.eqb orb andb Nat.leb eqb negb].
  reflexivity.
Qed.

(* What may follow a definition's colon, in the reference's words:
   whitespace and the URL, or the end of the line (the URL is on the
   next).  The URL chunk has no whitespace, and nothing follows it. *)
Local Lemma ref_value_gap : forall gap dest,
  is_blank gap = true -> no_ws dest = true ->
  (gap = EmptyString -> dest = EmptyString) ->
  ref_value (gap ++ dest) = Some dest.
Proof.
  intros gap dest Hblank Hdest Hbare.
  destruct gap as [|c gap]; [rewrite (Hbare eq_refl); reflexivity|].
  cbn [is_blank] in Hblank. apply andb_true_iff in Hblank as [Hc Hgap].
  unfold ref_value. cbn [append]. rewrite Hc.
  change (String c (gap ++ dest)) with (String c gap ++ dest).
  rewrite (drop_leading_ws_ws_prefix (String c gap) dest)
    by (cbn [is_blank]; rewrite Hc, Hgap; reflexivity).
  rewrite (no_ws_drop_leading_ws dest Hdest), Hdest. reflexivity.
Qed.

Local Lemma ref_open_gap : forall label gap dest,
  no_char "]"%char label = true ->
  is_footnote_label label = false ->
  is_blank gap = true -> no_ws dest = true ->
  (gap = EmptyString -> dest = EmptyString) ->
  ref_open ("[" ++ label ++ "]:" ++ gap ++ dest) = Some (label, dest).
Proof.
  intros label gap dest Hlabel Hfoot Hblank Hdest Hbare.
  assert (Hlab : forall tail,
    ref_label (label ++ String "]" tail) = Some (label, tail)).
  { clear Hfoot Hblank Hdest Hbare.
    induction label as [|c label IH]; [reflexivity|].
    cbn [no_char] in Hlabel. apply andb_true_iff in Hlabel as [Hc Hl].
    cbn [append ref_label]. apply negb_true_iff in Hc.
    intros tail. rewrite Hc, (IH Hl tail). reflexivity. }
  unfold ref_open. cbn [append drop_leading_ws is_ws Ascii.eqb orb].
  change (is_ws "[") with false.
  cbn [drop_leading_ws Ascii.eqb negb]. simpl.
  rewrite (Hlab (String ":" (gap ++ dest))). simpl. rewrite Hfoot.
  rewrite (ref_value_gap gap dest Hblank Hdest Hbare). reflexivity.
Qed.

(** RD1 at the line level: any indentation, the label, the colon, then
    whitespace and a whitespace-free URL chunk, or nothing (the URL
    starts on the next line). *)
Theorem classify_ref_whitespace : forall pre label gap dest,
  no_char "]"%char label = true ->
  is_footnote_label label = false ->
  is_blank pre = true -> is_blank gap = true -> no_ws dest = true ->
  (gap = EmptyString -> dest = EmptyString) ->
  classify (pre ++ "[" ++ label ++ "]:" ++ gap ++ dest) = KRef label dest.
Proof.
  intros pre label gap dest Hlabel Hfoot Hpre Hblank Hdest Hbare.
  rewrite classify_ws_prefix by exact Hpre.
  set (s := "[" ++ label ++ "]:" ++ gap ++ dest).
  assert (Hdrop : drop_leading_ws s = s).
  { unfold s. cbn [append drop_leading_ws].
    change (is_ws "[") with false. reflexivity. }
  assert (Hfo : foot_open s = None).
  { unfold foot_open. rewrite Hdrop. unfold s. cbn [append].
    destruct label as [|c [|d rest]].
    - reflexivity.
    - cbn [append ref_label nonempty_str Ascii.eqb negb].
      destruct (Ascii.eqb c "^"); reflexivity.
    - cbn [is_footnote_label] in Hfoot.
      destruct (Ascii.eqb c "^") eqn:Ec.
      + apply Ascii.eqb_eq in Ec. subst c. discriminate.
      + cbn [append ref_label nonempty_str Ascii.eqb negb].
        rewrite Ec. reflexivity. }
  assert (Hro : ref_open s = Some (label, dest)).
  { unfold s. apply ref_open_gap; assumption. }
  unfold classify.
  change (is_blank s) with false.
  unfold quote_prefix, heading_open, fence_open, div_open, list_marker,
    attr_open, is_thematic.
  rewrite !Hdrop, Hfo, Hro. unfold s. cbn [append].
  cbn [count_run thematic_count is_marker is_ws is_bullet marker_shape
       Ascii.eqb orb andb Nat.leb eqb negb].
  reflexivity.
Qed.

(* Boolean form of `classify l = KText`, so it can sit inside cb_ok. *)
Definition is_text (l : string) : bool :=
  match classify l with KText => true | _ => false end.

Lemma is_text_classify :
  forall l, is_text l = true -> classify l = KText.
Proof.
  intros l H. unfold is_text in H.
  destruct (classify l); (discriminate || reflexivity).
Qed.

(*
Canonical code fences
=====================

The renderer emits backtick fences of length 3; these lemmas say such
lines classify as intended. *)

(* An info string the renderer can emit verbatim and get back. *)
Fixpoint all_info_chars (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => is_info_char c && all_info_chars s'
  end.

(* Decompose the all_info_chars head fact into its three components. *)
Lemma info_char_parts :
  forall c, is_info_char c = true ->
  is_ws c = false /\ Ascii.eqb c "`" = false /\ Ascii.eqb c "010" = false.
Proof.
  intros c H. unfold is_info_char in H. apply negb_true_iff in H.
  apply orb_false_iff in H as [H Hn]. apply orb_false_iff in H as [Hw Hb].
  auto.
Qed.

Local Lemma count_run_info :
  forall info, all_info_chars info = true ->
  count_run "`" info = (O, info).
Proof.
  intros info H. destruct info as [|c info']; [reflexivity|].
  simpl in H. apply andb_true_iff in H as [Hc _].
  apply info_char_parts in Hc as (_ & Hb & _).
  cbn [count_run].
  destruct (Ascii.eqb "`" c) eqn:E; [|reflexivity].
  apply Ascii.eqb_eq in E. subst c.
  rewrite Ascii.eqb_refl in Hb. discriminate.
Qed.

Local Lemma drop_leading_ws_info :
  forall info, all_info_chars info = true ->
  drop_leading_ws info = info.
Proof.
  intros info H. destruct info as [|c info']; [reflexivity|].
  simpl in H. apply andb_true_iff in H as [Hc _].
  apply info_char_parts in Hc as (Hw & _ & _).
  cbn [drop_leading_ws]. rewrite Hw. reflexivity.
Qed.

Local Lemma take_info_all :
  forall info, all_info_chars info = true ->
  take_while is_info_char info = (info, EmptyString).
Proof.
  induction info as [|c info IH]; intros H; [reflexivity|].
  simpl in H. apply andb_true_iff in H as [Hc Hinfo].
  cbn [take_while]. rewrite Hc, (IH Hinfo). reflexivity.
Qed.

Local Lemma drop_head_nonws :
  forall c s, is_ws c = false -> drop_leading_ws (String c s) = String c s.
Proof. intros c s H. cbn [drop_leading_ws]. rewrite H. reflexivity. Qed.

(* The renderer's "```INFO" opener classifies as intended. *)
Local Lemma fence_open_backtick :
  forall info, all_info_chars info = true ->
  fence_open ("```" ++ info) = Some (Fence "`" 3 info).
Proof.
  intros info H.
  assert (E3 : count_run "`"
                 (String "`" (String "`" (String "`" info))) = (3, info)).
  { cbn [count_run Ascii.eqb]. rewrite (count_run_info info H). reflexivity. }
  unfold fence_open.
  change ("```" ++ info) with (String "`" (String "`" (String "`" info))).
  rewrite drop_head_nonws by reflexivity.
  cbn [Ascii.eqb orb].
  rewrite E3.
  cbn [Nat.leb].
  rewrite (drop_leading_ws_info info H), (take_info_all info H).
  reflexivity.
Qed.

Lemma classify_backtick_fence :
  forall info, all_info_chars info = true ->
  classify ("```" ++ info) = KFence (Fence "`" 3 info).
Proof.
  intros info H. unfold classify.
  change (is_blank ("```" ++ info)) with false.
  change (quote_prefix ("```" ++ info)) with (@None string).
  change (heading_open ("```" ++ info)) with (@None (nat * string)).
  rewrite (fence_open_backtick info H). reflexivity.
Qed.

(* A backtick fence as the syntax reference spells it: any indentation,
   three or more backticks, optional whitespace, an optional info string,
   and trailing whitespace. *)

Local Lemma take_info_app :
  forall info post, all_info_chars info = true -> is_blank post = true ->
  take_while is_info_char (info ++ post) = (info, post).
Proof.
  induction info as [|c info IH]; intros post Hinfo Hpost.
  - destruct post as [|w post]; [reflexivity|].
    cbn [is_blank] in Hpost. apply andb_true_iff in Hpost as [Hw _].
    cbn [append take_while]. unfold is_info_char. rewrite Hw. reflexivity.
  - cbn [all_info_chars] in Hinfo. apply andb_true_iff in Hinfo as [Hc Hinfo].
    cbn [append take_while]. rewrite Hc, (IH post Hinfo Hpost). reflexivity.
Qed.

Local Lemma fence_open_backticks : forall n gap info post,
  is_blank gap = true -> all_info_chars info = true -> is_blank post = true ->
  fence_open (char_run "`" (3 + n) ++ gap ++ info ++ post) =
    Some (Fence "`" (3 + n) info).
Proof.
  intros n gap info post Hgap Hinfo Hpost.
  (* the run ends where the backticks do: whatever follows is whitespace,
     an info character, or nothing *)
  assert (Hrun : count_run "`" (gap ++ info ++ post) = (O, gap ++ info ++ post)).
  { destruct gap as [|w gap].
    - destruct info as [|c info].
      + destruct post as [|w post]; [reflexivity|].
        cbn [is_blank] in Hpost. apply andb_true_iff in Hpost as [Hw _].
        cbn [append count_run]. destruct (Ascii.eqb "`" w) eqn:E; [|reflexivity].
        apply Ascii.eqb_eq in E. subst w. discriminate.
      + cbn [all_info_chars] in Hinfo. apply andb_true_iff in Hinfo as [Hc _].
        apply info_char_parts in Hc as (_ & Hb & _).
        cbn [append count_run]. rewrite Ascii.eqb_sym, Hb. reflexivity.
    - cbn [is_blank] in Hgap. apply andb_true_iff in Hgap as [Hw _].
      cbn [append count_run]. destruct (Ascii.eqb "`" w) eqn:E; [|reflexivity].
      apply Ascii.eqb_eq in E. subst w. discriminate. }
  unfold fence_open.
  cbn [char_run append drop_leading_ws is_ws Ascii.eqb orb]. simpl.
  rewrite (count_char_run "`" n _ Hrun), (drop_leading_ws_ws_prefix gap _ Hgap).
  destruct info as [|c info'].
  - cbn [append]. rewrite (drop_leading_ws_blank post Hpost). reflexivity.
  - assert (Hc : is_ws c = false).
    { cbn [all_info_chars] in Hinfo. apply andb_true_iff in Hinfo as [Hc _].
      apply info_char_parts in Hc as (Hw & _ & _). exact Hw. }
    cbn [append drop_leading_ws]. rewrite Hc.
    change (String c (info' ++ post)) with (String c info' ++ post).
    rewrite (take_info_app _ post Hinfo Hpost), Hpost. reflexivity.
Qed.

Theorem classify_backtick_fences : forall pre n gap info post,
  is_blank pre = true -> is_blank gap = true ->
  all_info_chars info = true -> is_blank post = true ->
  classify (pre ++ char_run "`" (3 + n) ++ gap ++ info ++ post) =
    KFence (Fence "`" (3 + n) info).
Proof.
  intros pre n gap info post Hpre Hgap Hinfo Hpost.
  rewrite classify_ws_prefix by exact Hpre. unfold classify.
  change (is_blank (char_run "`" (3 + n) ++ gap ++ info ++ post)) with false.
  change (quote_prefix (char_run "`" (3 + n) ++ gap ++ info ++ post))
    with (@None string).
  change (heading_open (char_run "`" (3 + n) ++ gap ++ info ++ post))
    with (@None (nat * string)).
  rewrite (fence_open_backticks n gap info post Hgap Hinfo Hpost). reflexivity.
Qed.

(* CB2 at the line level: a line closes a backtick fence exactly when it
   is a run of backticks at least as long as the opener's, with nothing
   but whitespace around it. *)
Theorem fence_close_backticks : forall n info l,
  fence_close (Fence "`" n info) l = true <->
  exists pre m post, is_blank pre = true /\ is_blank post = true /\ n <= m /\
    l = pre ++ char_run "`" m ++ post.
Proof.
  intros n info l. unfold fence_close. cbn [f_ch f_len]. split.
  - destruct (drop_leading_ws_split l) as (pre & Hpre & Hl).
    destruct (count_run "`" (drop_leading_ws l)) as [m r] eqn:E.
    intros H. apply andb_true_iff in H as [Hn Hr]. apply Nat.leb_le in Hn.
    apply count_run_split in E.
    exists pre, m, r. rewrite <- E. auto.
  - intros (pre & m & post & Hpre & Hpost & Hn & ->).
    rewrite (drop_leading_ws_ws_prefix pre _ Hpre).
    destruct m as [|m].
    + cbn [char_run append]. rewrite (drop_leading_ws_blank post Hpost).
      assert (n = 0) as -> by lia. reflexivity.
    + rewrite drop_leading_ws_run by (reflexivity || lia).
      rewrite count_char_run by (apply count_run_blank; reflexivity || exact Hpost).
      rewrite Hpost, andb_true_r. apply Nat.leb_le, Hn.
Qed.

(*
Div fences over every spelling
------------------------------
*)

Local Lemma take_while_app : forall p a b,
  str_forallb p a = true ->
  (b = EmptyString \/ exists c b', b = String c b' /\ p c = false) ->
  take_while p (a ++ b) = (a, b).
Proof.
  intros p a b Ha Hb. induction a as [|c a IH].
  - destruct Hb as [->|(c & b' & -> & Hc)]; cbn; [reflexivity|rewrite Hc; reflexivity].
  - cbn [str_forallb] in Ha. apply andb_true_iff in Ha as [Hc Ha].
    cbn [append take_while]. rewrite Hc, (IH Ha). reflexivity.
Qed.

Local Lemma take_while_split : forall p s a b,
  take_while p s = (a, b) -> s = a ++ b /\ str_forallb p a = true.
Proof.
  intros p s. induction s as [|c s IH]; intros a b H.
  - injection H as <- <-. split; reflexivity.
  - cbn [take_while] in H. destruct (p c) eqn:Ec.
    + destruct (take_while p s) as [a' b'] eqn:E. injection H as <- <-.
      destruct (IH a' b' eq_refl) as [-> Ha]. split; [reflexivity|].
      cbn [str_forallb]. rewrite Ec, Ha. reflexivity.
    + injection H as <- <-. split; reflexivity.
Qed.

Local Lemma class_char_not_ws : forall c, is_class_char c = true -> is_ws c = false.
Proof.
  intros c H. destruct (is_ws c) eqn:E; [|reflexivity].
  unfold is_ws in E. repeat (apply orb_true_iff in E as [E|E]);
    apply Ascii.eqb_eq in E; subst c; discriminate.
Qed.

Local Lemma class_char_not_colon :
  forall c, is_class_char c = true -> Ascii.eqb ":" c = false.
Proof.
  intros c H. destruct (Ascii.eqb ":" c) eqn:E; [|reflexivity].
  apply Ascii.eqb_eq in E. subst c. discriminate.
Qed.

(* Where the class token stops: a blank rest starts with no class
   character. *)
Local Lemma blank_head : forall s, is_blank s = true ->
  s = EmptyString \/ exists c s', s = String c s' /\ is_class_char c = false.
Proof.
  intros [|c s] H; [left; reflexivity|right]. exists c, s. split; [reflexivity|].
  cbn [is_blank] in H. apply andb_true_iff in H as [Hc _].
  destruct (is_class_char c) eqn:E; [|reflexivity].
  rewrite (class_char_not_ws c E) in Hc. discriminate.
Qed.

Local Lemma div_open_colons : forall n gap cls post,
  is_blank gap = true -> str_forallb is_class_char cls = true ->
  is_blank post = true ->
  div_open (char_run ":" (3 + n) ++ gap ++ cls ++ post) = Some (3 + n, cls).
Proof.
  intros n gap cls post Hgap Hcls Hpost.
  (* the run ends where the colons do *)
  assert (Hrun : count_run ":" (gap ++ cls ++ post) = (O, gap ++ cls ++ post)).
  { destruct gap as [|w gap].
    - destruct cls as [|c cls].
      + apply count_run_blank; [reflexivity|exact Hpost].
      + cbn [str_forallb] in Hcls. apply andb_true_iff in Hcls as [Hc _].
        cbn [append count_run]. rewrite (class_char_not_colon c Hc). reflexivity.
    - cbn [is_blank] in Hgap. apply andb_true_iff in Hgap as [Hw _].
      cbn [append count_run]. destruct (Ascii.eqb ":" w) eqn:E; [|reflexivity].
      apply Ascii.eqb_eq in E. subst w. discriminate. }
  unfold div_open. rewrite drop_leading_ws_run by (reflexivity || lia).
  change (char_run ":" (3 + n)) with (String ":" (char_run ":" (2 + n))).
  cbn [append Ascii.eqb Ascii.ascii_dec]. simpl.
  change (String ":" (char_run ":" (2 + n) ++ gap ++ cls ++ post))
    with (char_run ":" (3 + n) ++ gap ++ cls ++ post).
  rewrite (count_char_run _ _ _ Hrun).
  rewrite (drop_leading_ws_ws_prefix gap _ Hgap).
  destruct cls as [|c cls'].
  - cbn [append]. rewrite (drop_leading_ws_blank post Hpost). reflexivity.
  - assert (Hc : is_ws c = false).
    { cbn [str_forallb] in Hcls. apply andb_true_iff in Hcls as [Hc _].
      exact (class_char_not_ws c Hc). }
    cbn [append drop_leading_ws]. rewrite Hc.
    change (String c (cls' ++ post)) with (String c cls' ++ post).
    rewrite (take_while_app _ _ _ Hcls (blank_head post Hpost)), Hpost. reflexivity.
Qed.

(* DV1: a div opener is an indent, three or more colons, optional
   whitespace, a class token of `is_class_char`, and trailing whitespace;
   nothing else classifies as one.  The whitespace before the class may
   be empty: `:::foo` opens a div, as in djot.js. *)
Theorem classify_div_fences : forall l n cls,
  classify l = KDiv n cls <->
  exists pre gap post,
    is_blank pre = true /\ is_blank gap = true /\ is_blank post = true /\
    3 <= n /\ str_forallb is_class_char cls = true /\
    l = pre ++ char_run ":" n ++ gap ++ cls ++ post.
Proof.
  intros l n cls. split.
  - intros H.
    assert (Hd : div_open l = Some (n, cls)).
    { unfold classify in H. destruct (is_blank l); [discriminate|].
      destruct (quote_prefix l); [discriminate|].
      destruct (heading_open l) as [[? ?]|]; [discriminate|].
      destruct (fence_open l); [discriminate|].
      destruct (div_open l) as [[? ?]|]; [congruence|].
      repeat match type of H with
             | context [match ?x with _ => _ end] => destruct x
             | context [if ?x then _ else _] => destruct x
             end; discriminate. }
    clear H. unfold div_open in Hd.
    destruct (drop_leading_ws_split l) as (pre & Hpre & Hl).
    destruct (drop_leading_ws l) as [|c s] eqn:Ed; [discriminate|].
    destruct (Ascii.eqb c ":") eqn:Ec; [|discriminate].
    destruct (count_run ":" (String c s)) as [m r] eqn:Er.
    destruct (Nat.leb 3 m) eqn:Em; [|discriminate].
    destruct (drop_leading_ws_split r) as (gap & Hgap & Hr).
    destruct (take_while is_class_char (drop_leading_ws r)) as [a b] eqn:Et.
    destruct (is_blank b) eqn:Eb; [|discriminate].
    injection Hd as <- <-.
    apply count_run_split in Er.
    apply take_while_split in Et as [Et Ha].
    exists pre, gap, b. repeat split; try assumption.
    + apply Nat.leb_le, Em.
    + rewrite Hl, Er, Hr, Et. reflexivity.
  - intros (pre & gap & post & Hpre & Hgap & Hpost & Hn & Hcls & ->).
    rewrite classify_ws_prefix by exact Hpre.
    replace n with (3 + (n - 3)) by lia.
    unfold classify.
    change (is_blank (char_run ":" (3 + (n - 3)) ++ gap ++ cls ++ post)) with false.
    change (quote_prefix (char_run ":" (3 + (n - 3)) ++ gap ++ cls ++ post))
      with (@None string).
    change (heading_open (char_run ":" (3 + (n - 3)) ++ gap ++ cls ++ post))
      with (@None (nat * string)).
    change (fence_open (char_run ":" (3 + (n - 3)) ++ gap ++ cls ++ post))
      with (@None fence).
    rewrite (div_open_colons _ _ _ _ Hgap Hcls Hpost). reflexivity.
Qed.

(* DV2 at the line level: a div opened with `len` colons is closed by a
   run of at least `len` (and at least three) colons with only
   whitespace around it.  No class: `::: foo` never closes. *)
Theorem div_close_colons : forall len l,
  div_close len l = true <->
  exists pre m post, is_blank pre = true /\ is_blank post = true /\
    len <= m /\ 3 <= m /\ l = pre ++ char_run ":" m ++ post.
Proof.
  intros len l. unfold div_close. split.
  - destruct (drop_leading_ws_split l) as (pre & Hpre & Hl).
    destruct (count_run ":" (drop_leading_ws l)) as [m r] eqn:E.
    intros H. apply andb_true_iff in H as [H Hr]. apply andb_true_iff in H as [Hn H3].
    apply Nat.leb_le in Hn, H3.
    apply count_run_split in E.
    exists pre, m, r. rewrite <- E. auto.
  - intros (pre & m & post & Hpre & Hpost & Hn & H3 & ->).
    rewrite (drop_leading_ws_ws_prefix pre _ Hpre).
    rewrite drop_leading_ws_run by (reflexivity || lia).
    rewrite count_char_run by (apply count_run_blank; reflexivity || exact Hpost).
    rewrite Hpost, andb_true_r. apply andb_true_iff; split; apply Nat.leb_le; assumption.
Qed.

(* Canonical block-quote prefixing: "> " in front of every line, blank
   ones included.  Defined here rather than in Render so that the parser
   can name its width: both containers descend by two columns, and
   `String.length quote_open` says which one a proof means where a bare
   `2` would not. *)
Definition quote_open : string := "> ".
Definition quote_line (l : string) : string := quote_open ++ l.

(* The column a quote's contents start at.  Definitionally 2, and named
   so that it cannot be confused with `item_pad`. *)
Definition quote_pad : nat := String.length quote_open.

Local Lemma quote_prefix_canonical :
  forall l, quote_prefix ("> " ++ l) = Some l.
Proof. reflexivity. Qed.

Lemma classify_canonical_quote :
  forall l, classify ("> " ++ l) = KQuote l.
Proof.
  intros l. unfold classify.
  change (is_blank ("> " ++ l)) with false.
  rewrite quote_prefix_canonical. reflexivity.
Qed.

(* The same through an all-whitespace pad.  The extracted content is
   exactly `l`, so a quote nested in a list item ignores the item's
   indent. *)
Lemma classify_canonical_quote_pad :
  forall pad l, is_blank pad = true -> classify (pad ++ "> " ++ l) = KQuote l.
Proof.
  intros pad l Hpad. rewrite classify_ws_prefix by exact Hpad.
  apply classify_canonical_quote.
Qed.

(* BQ1 over every spelling: a quote line is an all-whitespace indent, a
   `>`, then the end of the line or one whitespace character.  Nothing
   else is one (`>x` is not).  The reference says "a space"; a tab or CR
   also counts, as in djot.js. *)
Theorem classify_quote_marker : forall l r,
  classify l = KQuote r <->
  exists pre, is_blank pre = true /\
    (l = pre ++ ">" /\ r = EmptyString
     \/ exists c, is_ws c = true /\ l = pre ++ String ">" (String c r)).
Proof.
  intros l r. split.
  - unfold classify. intros H.
    destruct (is_blank l); [discriminate|].
    destruct (quote_prefix l) as [r'|] eqn:Eq;
      [|repeat match type of H with
               | context [match ?x with _ => _ end] => destruct x
               end; discriminate].
    injection H as <-.
    unfold quote_prefix in Eq.
    destruct (drop_leading_ws_split l) as (pre & Hpre & Hl).
    exists pre. split; [exact Hpre|].
    destruct (drop_leading_ws l) as [|c rest]; [discriminate|].
    destruct (Ascii.eqb c ">") eqn:Ec; [|discriminate].
    apply Ascii.eqb_eq in Ec. subst c.
    destruct rest as [|c' rest'].
    + injection Eq as <-. left. split; [exact Hl|reflexivity].
    + destruct (is_ws c') eqn:Ew; [|discriminate].
      injection Eq as <-. right. exists c'. split; [exact Ew|exact Hl].
  - intros (pre & Hpre & [[-> ->] | (c & Hc & ->)]);
      rewrite classify_ws_prefix by exact Hpre; unfold classify.
    + reflexivity.
    + change (is_blank (String ">" (String c r))) with false.
      unfold quote_prefix. cbn [drop_leading_ws].
      change (is_ws ">") with false. cbn - [is_ws]. rewrite Hc. reflexivity.
Qed.

(*
Canonical headings
==================

The renderer prefixes every line of a heading with its hashes and one
space, so a multi-line heading reparses line by line as continuations of
itself, as a block quote does, without the reclassification. *)

Fixpoint hashes (n : nat) : string :=
  match n with O => EmptyString | S n' => "#" ++ hashes n' end.

Definition heading_line (lvl : nat) (l : string) : string :=
  hashes lvl ++ " " ++ l.

(* The hashes are consumed exactly: the renderer's space stops the run,
   so the level comes back out unchanged however long the text is. *)
Local Lemma count_run_hashes_space :
  forall n l, count_run "#" (hashes n ++ " " ++ l) = (n, " " ++ l).
Proof.
  induction n as [|n IH]; intros l; [reflexivity|].
  cbn [hashes]. rewrite append_assoc.
  change ("#" ++ (hashes n ++ " " ++ l))%string
    with (String "#" (hashes n ++ " " ++ l))%string.
  cbn [count_run]. rewrite IH. reflexivity.
Qed.

Lemma drop_leading_ws_hashes :
  forall n l, 1 <= n -> drop_leading_ws (hashes n ++ " " ++ l) = (hashes n ++ " " ++ l).
Proof.
  intros n l H. destruct n as [|n']; [lia|].
  cbn [hashes]. rewrite append_assoc.
  change ("#" ++ (hashes n' ++ " " ++ l))%string
    with (String "#" (hashes n' ++ " " ++ l))%string.
  apply drop_head_nonws. reflexivity.
Qed.

Local Lemma no_nl_hashes : forall n, no_nl (hashes n) = true.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [hashes]. change ("#" ++ hashes n)%string with (String "#" (hashes n)).
  cbn [no_nl]. exact IH.
Qed.

Lemma heading_line_no_nl :
  forall lvl l, no_nl (heading_line lvl l) = no_nl l.
Proof.
  intros lvl l. unfold heading_line.
  rewrite !no_nl_append, no_nl_hashes. reflexivity.
Qed.

Lemma heading_line_nonempty :
  forall lvl l, 1 <= lvl -> heading_line lvl l <> EmptyString.
Proof.
  intros lvl l H. unfold heading_line.
  destruct lvl as [|n]; [lia|].
  cbn [hashes]. rewrite append_assoc. discriminate.
Qed.

Lemma classify_canonical_heading :
  forall lvl l, 1 <= lvl -> classify (heading_line lvl l) = KHeading lvl l.
Proof.
  intros lvl l H. unfold classify, heading_line.
  assert (Hb : is_blank (hashes lvl ++ " " ++ l) = false).
  { destruct lvl as [|n]; [lia|]. reflexivity. }
  assert (Hq : quote_prefix (hashes lvl ++ " " ++ l) = None).
  { unfold quote_prefix. rewrite drop_leading_ws_hashes by exact H.
    destruct lvl as [|n]; [lia | reflexivity]. }
  rewrite Hb, Hq.
  unfold heading_open. rewrite drop_leading_ws_hashes by exact H.
  rewrite count_run_hashes_space.
  destruct lvl as [|n]; [lia|]. reflexivity.
Qed.

Lemma fence_close_canonical :
  forall info, fence_close (Fence "`" 3 info) "```" = true.
Proof. reflexivity. Qed.

(*
Canonical fenced divs
=====================

The renderer emits the shortest fence, classless, at both ends, as it
does for code.  A div whose contents contain a `:::` line cannot be
rendered, and `cb_ok` excludes it. *)

Definition div_fence : string := ":::".

Lemma classify_canonical_div : classify div_fence = KDiv 3 EmptyString.
Proof. reflexivity. Qed.

Lemma div_close_canonical : div_close 3 div_fence = true.
Proof. reflexivity. Qed.

(* A blank line never closes a div: the `3 <=` conjunct fails on an empty
   colon run. *)
Lemma div_close_blank :
  forall len l, is_blank l = true -> div_close len l = false.
Proof.
  intros len l H. unfold div_close.
  rewrite (drop_leading_ws_blank l H).
  cbn [count_run]. rewrite Bool.andb_false_r. reflexivity.
Qed.

(* Whitespace before a div's closer is invisible to it.  Not a case of
   `classify_ws_prefix`: `div_close` is applied by the open div, never
   through `classify`. *)
Lemma div_close_ws_prefix :
  forall p len l, is_blank p = true -> div_close len (p ++ l) = div_close len l.
Proof.
  intros p len l Hp. unfold div_close.
  rewrite (drop_leading_ws_ws_prefix p l Hp). reflexivity.
Qed.

(* A line of colons classifies as a div opener, so no text line closes a
   div. *)
Lemma classify_text_div_close :
  forall len l, classify l = KText -> div_close len l = false.
Proof.
  intros len l H. unfold div_close.
  destruct (count_run ":" (drop_leading_ws l)) as [n r] eqn:Ec.
  destruct (Nat.leb len n && Nat.leb 3 n && is_blank r)%bool eqn:Eb; [|reflexivity].
  exfalso. apply andb_true_iff in Eb as [Eb Hr]. apply andb_true_iff in Eb as [_ Hn].
  apply Nat.leb_le in Hn.
  unfold classify, quote_prefix, heading_open, fence_open, div_open in H.
  destruct (is_blank l); [discriminate|].
  destruct (drop_leading_ws l) as [|c s] eqn:Ed; [cbn in Ec; injection Ec as <- _; lia|].
  cbn [count_run] in Ec. destruct (Ascii.eqb ":" c) eqn:Ecol; [|injection Ec as <- _; lia].
  apply Ascii.eqb_eq in Ecol. subst c.
  cbn [count_run Ascii.eqb Ascii.ascii_dec Bool.eqb andb orb] in H.
  destruct (count_run ":" s) as [m r0] eqn:Em. injection Ec as <- <-.
  rewrite (drop_leading_ws_blank r0 Hr) in H.
  replace (3 <=? S m)%nat with true in H by (symmetry; apply Nat.leb_le; lia).
  cbn in H. discriminate H.
Qed.

(* A quote prefix, as a container writes it. *)
Lemma classify_quote_space : forall x, classify ("> " ++ x) = KQuote x.
Proof. intros x. reflexivity. Qed.

Lemma div_close_quote_space : forall len x, div_close len ("> " ++ x) = false.
Proof. intros len x. unfold div_close. cbn. rewrite andb_false_r. reflexivity. Qed.

(* classify_canonical_heading through an all-whitespace pad. *)
Lemma classify_canonical_heading_pad :
  forall pad lvl l, is_blank pad = true -> 1 <= lvl ->
  classify (pad ++ heading_line lvl l) = KHeading lvl l.
Proof.
  intros pad lvl l Hpad Hlvl. rewrite classify_ws_prefix by exact Hpad.
  apply classify_canonical_heading, Hlvl.
Qed.

(** The syntax reference: "A line containing three or more `*` or `-`
    characters, and nothing else (except spaces or tabs) is treated is a
    thematic break", at any indentation.  That is `is_thematic`, and no
    recognizer `classify` tries first claims such a line. *)
Lemma classify_thematic :
  forall l, is_thematic l = true -> classify l = KThematic.
Proof.
  intros l. unfold is_thematic.
  induction l as [|c l IH]; intros H; [discriminate|].
  cbn [thematic_count] in H.
  destruct (is_marker c) eqn:Em.
  - (* the first marker: nothing before `is_thematic` starts with one *)
    unfold is_marker in Em.
    apply orb_true_iff in Em as [E|E]; apply Ascii.eqb_eq in E; subst c;
      unfold classify;
      cbn [is_blank drop_leading_ws is_ws quote_prefix heading_open fence_open
           div_open count_run Ascii.eqb Bool.eqb andb orb].
    all: cbn [Nat.leb]; unfold is_thematic; cbn [thematic_count];
      replace (is_marker _) with true by reflexivity; rewrite H; reflexivity.
  - (* leading whitespace *)
    destruct (is_ws c) eqn:Ew; [|discriminate].
    change (String c l) with (String c "" ++ l)%string.
    rewrite classify_ws_prefix by (cbn [is_blank]; rewrite Ew; reflexivity).
    apply IH, H.
Qed.

(** The syntax reference: "A heading starts with a sequence of one or
    more `#` characters, followed by whitespace.  The number of `#`
    characters defines the heading level."  At any indentation, and
    whatever the whitespace is. *)
Lemma classify_heading_ws :
  forall pad lvl c rest,
    is_blank pad = true -> 1 <= lvl -> is_ws c = true ->
    classify (pad ++ hashes lvl ++ String c rest) = KHeading lvl rest.
Proof.
  intros pad lvl c rest Hpad Hlvl Hc. rewrite classify_ws_prefix by exact Hpad.
  (* the run stops at the whitespace *)
  assert (Hcr : forall n,
    count_run "#" (hashes n ++ String c rest) = (n, String c rest)).
  { induction n as [|n IH].
    - cbn [hashes append count_run].
      destruct (Ascii.eqb "#" c) eqn:E;
        [apply Ascii.eqb_eq in E; subst c; discriminate|reflexivity].
    - cbn [hashes]. rewrite append_assoc.
      change ("#" ++ (hashes n ++ String c rest))%string
        with (String "#" (hashes n ++ String c rest))%string.
      cbn [count_run]. rewrite IH. reflexivity. }
  destruct lvl as [|n]; [lia|].
  assert (Hs : (hashes (S n) ++ String c rest)%string
               = String "#" (hashes n ++ String c rest)).
  { cbn [hashes]. rewrite append_assoc. reflexivity. }
  assert (Hd : drop_leading_ws (String "#" (hashes n ++ String c rest))
               = String "#" (hashes n ++ String c rest))
    by (apply drop_head_nonws; reflexivity).
  unfold classify. rewrite Hs.
  cbn [is_blank]. replace (is_ws "#") with false by reflexivity. cbn [andb].
  unfold quote_prefix. rewrite Hd. cbn [Ascii.eqb Bool.eqb].
  unfold heading_open. rewrite Hd. cbn [count_run].
  replace (Ascii.eqb "#" "#") with true by reflexivity.
  rewrite Hcr. cbn [Nat.leb]. rewrite Hc. reflexivity.
Qed.

(*
Canonical bullet lists
=======================

The renderer marks an item's first line with its marker and every later
line with plain indent of the marker's width.  The indent is whitespace,
so `classify_ws_prefix` carries every recognizer through it: a construct
starting on a continuation line classifies as it would unindented. *)

(* A run of spaces, the continuation indent's shape.  Ordered markers
   differ from bullets only in how long this is. *)
Fixpoint blanks (n : nat) : string :=
  match n with O => EmptyString | S k => String " " (blanks k) end.

Lemma blanks_blank : forall n, is_blank (blanks n) = true.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [blanks is_blank]. exact IH. Qed.

Lemma blanks_length : forall n, String.length (blanks n) = n.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [blanks String.length]. rewrite IH. reflexivity. Qed.

(* A list marker as the renderer writes it.  Shaped after `list_marker`'s
   two branches, so every fact below is a case analysis the classifier
   already performs: a bullet is one character, an ordered marker an
   alphanumeric core inside a delimiter.

   There is no width field.  `mk_pad` is derived, and no continuation rule
   reads it: a continuation line only has to be indented past the
   marker's column, so a wider marker changes nothing. *)
Inductive marker : Type :=
  | MBullet (c : ascii)
  | MTask (c : ascii) (chk : task_status)
  | MOrd (core : string) (d : ordered_list_delim).

Definition mk_open (m : marker) : string :=
  match m with
  | MBullet c => String c " "
  | MTask c Complete => String c " [x] "
  | MTask c Incomplete => String c " [ ] "
  | MOrd core RightPeriod => core ++ ". "
  | MOrd core RightParen => core ++ ") "
  | MOrd core LeftRightParen => "(" ++ core ++ ") "
  end.

Definition mk_pad (m : marker) : nat := String.length (mk_open m).
Definition mk_cont (m : marker) : string := blanks (mk_pad m).

(* The candidate styles and the numeral the classifier reads off this
   marker.  For a bullet the core is empty, which is what `style_start`
   turns into the default start of 1. *)
Definition mk_sty (m : marker) : list lstyle :=
  match m with
  | MBullet c => [SBullet c]
  | MTask c _ => [STask c]
  | MOrd core d => styles_of_core core d
  end.

Definition mk_core (m : marker) : string :=
  match m with MBullet _ | MTask _ _ => EmptyString | MOrd core _ => core end.

Definition mk_check (m : marker) : task_status :=
  match m with MTask _ chk => chk | _ => Incomplete end.

Definition mk_task_marker (m : marker) : option task_marker :=
  match m with
  | MTask _ chk => Some (canonical_task_marker chk)
  | _ => None
  end.

Definition marker_tasks_ok (enabled : bool) (m : marker) : bool :=
  match m with MTask _ _ => enabled | _ => true end.

(* Which markers the classifier actually recognizes.  An ordered core has
   to be alphanumeric (so `marker_shape` scans exactly it) and has to name
   at least one style (so `list_marker` does not reject it). *)
Definition marker_ok (m : marker) : bool :=
  match m with
  | MBullet c => is_bullet c
  | MTask c _ => is_task_bullet c
  | MOrd core d =>
      (nonempty_str core && str_forallb is_alnum core
       && nonempty (styles_of_core core d))%bool
  end.

Definition bullet : marker := MBullet "-".

(* Notations, not definitions: the list chain below is stated over an
   abstract marker, and these names have to be *syntactically* its
   instantiation for those statements to rewrite against a canonical
   rendering. *)
Notation bullet_open := (mk_open bullet).
Notation bullet_cont := (mk_cont bullet).

(* The column an item's contents start at.  Definitionally 2 for every
   bullet, and distinct from `quote_pad`: an ordered marker separates
   them. *)
Notation item_pad := (mk_pad bullet).

Lemma bullet_ok : marker_ok bullet = true.
Proof. reflexivity. Qed.

(* The other two bullet characters.  djot starts a new list when the
   style changes, so these are different lists, and
   `OrderedList.star_uniformity` and `plus_uniformity` reach them by
   instantiation. *)
Definition star : marker := MBullet "*".
Definition plus : marker := MBullet "+".

Lemma star_ok : marker_ok star = true.
Proof. reflexivity. Qed.

Lemma plus_ok : marker_ok plus = true.
Proof. reflexivity. Qed.

(* The definition-list marker.  A bullet like the others, differing only
   in what the list closes to (`Step.styles_list`), so every list theorem
   reaches it by instantiation. *)
Definition colon : marker := MBullet ":".

Lemma colon_ok : marker_ok colon = true.
Proof. reflexivity. Qed.

Lemma marker_cont_blank : forall m, is_blank (mk_cont m) = true.
Proof. intros m. apply blanks_blank. Qed.

Local Lemma bullet_cont_blank : is_blank bullet_cont = true.
Proof. reflexivity. Qed.

Lemma classify_marker_cont :
  forall m l, classify (mk_cont m ++ l) = classify l.
Proof. intros m l. apply classify_ws_prefix, marker_cont_blank. Qed.

Lemma indent_of_marker_cont :
  forall m l, indent_of (mk_cont m ++ l) = mk_pad m + indent_of l.
Proof.
  intros m l. rewrite indent_of_ws_prefix by apply marker_cont_blank.
  unfold mk_cont. rewrite blanks_length. reflexivity.
Qed.

Local Lemma classify_bullet_cont :
  forall l, classify (bullet_cont ++ l) = classify l.
Proof. intros l. apply classify_marker_cont. Qed.

Local Lemma indent_of_bullet_cont :
  forall l, indent_of (bullet_cont ++ l) = item_pad + indent_of l.
Proof. intros l. apply indent_of_marker_cont. Qed.

(* The four bullet styles, enumerated: `is_bullet` is a disjunction of
   character tests, so every fact about a recognized marker reduces to
   four concrete cases. *)
Local Lemma is_bullet_cases :
  forall c, is_bullet c = true ->
    c = "-"%char \/ c = "*"%char \/ c = "+"%char \/ c = ":"%char.
Proof.
  intros c H. unfold is_bullet in H.
  destruct (Ascii.eqb c "-") eqn:E1; [left; apply Ascii.eqb_eq, E1|].
  destruct (Ascii.eqb c "*") eqn:E2; [right; left; apply Ascii.eqb_eq, E2|].
  destruct (Ascii.eqb c "+") eqn:E3;
    [right; right; left; apply Ascii.eqb_eq, E3|].
  destruct (Ascii.eqb c ":") eqn:E4;
    [right; right; right; apply Ascii.eqb_eq, E4|].
  cbn in H. discriminate.
Qed.

Local Lemma is_task_bullet_cases :
  forall c, is_task_bullet c = true ->
    c = "-"%char \/ c = "*"%char \/ c = "+"%char.
Proof.
  intros c H. unfold is_task_bullet in H.
  destruct (Ascii.eqb c "-") eqn:E1; [left; apply Ascii.eqb_eq, E1|].
  destruct (Ascii.eqb c "*") eqn:E2; [right; left; apply Ascii.eqb_eq, E2|].
  destruct (Ascii.eqb c "+") eqn:E3;
    [right; right; apply Ascii.eqb_eq, E3|].
  cbn in H. discriminate.
Qed.

(* A run of `p` characters followed by one that is not comes off whole,
   leaving the rest untouched: an ordered marker's core in `marker_shape`,
   a callout's kind in `callout_header`. *)
Local Lemma take_while_all_app :
  forall p s rest,
    str_forallb p s = true ->
    match rest with String c _ => p c = false | EmptyString => True end ->
    take_while p (s ++ rest) = (s, rest).
Proof.
  intros p. induction s as [|c s IH]; intros rest Hs Hrest.
  - destruct rest as [|c r]; [reflexivity|].
    cbn [take_while append]. rewrite Hrest. reflexivity.
  - cbn [str_forallb] in Hs. apply andb_true_iff in Hs as [Hc Hs].
    change ((String c s) ++ rest)%string with (String c (s ++ rest))%string.
    cbn [take_while]. rewrite Hc, (IH rest Hs Hrest). reflexivity.
Qed.

(* The canonical callout header: the fold marker directly after `]`, then
   one space before a nonempty title. *)
Definition callout_kind_ok (kind : string) : bool :=
  (nonempty_str kind && str_forallb callout_kind_char kind)%bool.

Definition callout_fold_marker (fold : option callout_fold) : string :=
  match fold with
  | None => ""
  | Some FoldExpanded => "+"
  | Some FoldCollapsed => "-"
  end.

Definition callout_header_line
  (kind : string) (fold : option callout_fold) (title : string) : string :=
  "[!" ++ kind ++ "]" ++ callout_fold_marker fold
  ++ match title with EmptyString => "" | _ => " " ++ title end.

Lemma callout_header_line_inv :
  forall kind fold title,
    callout_kind_ok kind = true -> drop_leading_ws title = title ->
    callout_header (callout_header_line kind fold title)
    = Some (kind, fold, title).
Proof.
  intros kind fold title Hk Ht.
  unfold callout_kind_ok in Hk. apply andb_true_iff in Hk as [Hne Hk].
  unfold callout_header_line, callout_header. cbn [append Ascii.eqb Bool.eqb andb].
  rewrite (take_while_all_app callout_kind_char kind (String "]" _) Hk eq_refl).
  destruct kind as [|c k]; [discriminate Hne|].
  destruct fold as [[|]|]; cbn [callout_fold_marker append];
    destruct title as [|t title]; cbn [callout_sep Ascii.eqb Bool.eqb orb];
    rewrite ?Ht; reflexivity.
Qed.

Lemma callout_header_line_no_nl :
  forall kind fold title,
    callout_kind_ok kind = true -> no_nl title = true ->
    no_nl (callout_header_line kind fold title) = true.
Proof.
  intros kind fold title Hk Ht.
  unfold callout_kind_ok in Hk. apply andb_true_iff in Hk as [_ Hk].
  assert (Hkind : no_nl kind = true).
  { induction kind as [|c k IH]; [reflexivity|].
    cbn [str_forallb] in Hk. apply andb_true_iff in Hk as [Hc Hk].
    cbn [no_nl]. rewrite (IH Hk), andb_true_r.
    destruct (Ascii.eqb c "010") eqn:E; [|reflexivity].
    apply Ascii.eqb_eq in E. subst c. discriminate Hc. }
  unfold callout_header_line.
  rewrite !no_nl_append. cbn [no_nl Ascii.eqb Bool.eqb negb andb].
  rewrite Hkind.
  destruct fold as [[|]|]; destruct title as [|t title];
    cbn [callout_fold_marker no_nl append Ascii.eqb Bool.eqb negb andb];
    try reflexivity; exact Ht.
Qed.

(* An alphanumeric character is none of the characters the recognizers
   ahead of `list_marker` look for. *)
Local Lemma is_alnum_not_bullet :
  forall c, is_alnum c = true -> is_bullet c = false.
Proof.
  intros c H. destruct (is_bullet c) eqn:E; [|reflexivity].
  destruct (is_bullet_cases c E) as [F|[F|[F|F]]]; subst c; discriminate H.
Qed.

Lemma is_digit_alnum : forall c, is_digit c = true -> is_alnum c = true.
Proof. intros c H. unfold is_alnum. rewrite H. reflexivity. Qed.

Lemma str_digits_alnum :
  forall s, str_forallb is_digit s = true -> str_forallb is_alnum s = true.
Proof.
  induction s as [|c s IH]; intros H; [reflexivity|].
  cbn [str_forallb] in *. apply andb_true_iff in H as [Hc Hs].
  rewrite (is_digit_alnum c Hc), (IH Hs). reflexivity.
Qed.

Lemma is_alnum_not_marker : forall c, is_alnum c = true -> is_marker c = false.
Proof.
  intros c H. unfold is_marker.
  destruct (Ascii.eqb c "-") eqn:E1;
    [apply Ascii.eqb_eq in E1; subst c; discriminate H|].
  destruct (Ascii.eqb c "*") eqn:E2;
    [apply Ascii.eqb_eq in E2; subst c; discriminate H|].
  reflexivity.
Qed.

(* A line whose first character is neither a thematic marker nor
   whitespace is not a thematic break, whatever follows. *)
Lemma thematic_first_char :
  forall c s, is_marker c = false -> is_ws c = false ->
    is_thematic (String c s) = false.
Proof.
  intros c s Hm Hw. unfold is_thematic. cbn [thematic_count].
  rewrite Hm, Hw. reflexivity.
Qed.

Local Lemma is_alnum_not_paren :
  forall c, is_alnum c = true -> Ascii.eqb c "(" = false.
Proof.
  intros c H. destruct (Ascii.eqb c "(") eqn:E; [|reflexivity].
  apply Ascii.eqb_eq in E. subst c. discriminate H.
Qed.

Lemma is_alnum_not_special :
  forall c, is_alnum c = true ->
    is_ws c = false /\ Ascii.eqb c ">" = false /\ Ascii.eqb c "#" = false
    /\ Ascii.eqb c "`" = false /\ Ascii.eqb c "~" = false
    /\ Ascii.eqb c ":" = false.
Proof.
  intros c H.
  assert (Hne : forall d, Ascii.eqb c d = true -> is_alnum d = true).
  { intros d Hd. apply Ascii.eqb_eq in Hd. subst d. exact H. }
  repeat split.
  all: try (destruct (is_ws c) eqn:E; [|reflexivity];
            unfold is_ws in E; apply orb_true_iff in E as [E|E];
            [apply orb_true_iff in E as [E|E]|];
            apply Hne in E; discriminate E).
  all: match goal with
       | |- (?x =? ?d) = false =>
           destruct (Ascii.eqb x d) eqn:E; [apply Hne in E; discriminate E|reflexivity]
       end.
Qed.

(* A line whose first character is not a colon opens no div. *)
Local Lemma div_open_not_colon :
  forall c r, is_ws c = false -> Ascii.eqb c ":" = false ->
    div_open (String c r) = None.
Proof.
  intros c r Hws Hcol. unfold div_open. cbn [drop_leading_ws].
  rewrite Hws, Hcol. reflexivity.
Qed.

(* A marker opener is never blank and never starts with whitespace, so
   the recognizers `classify` runs before `list_marker` all see its first
   character and all reject it. *)
Local Lemma marker_open_shape :
  forall m l, marker_ok m = true ->
    drop_leading_ws (mk_open m ++ l) = (mk_open m ++ l)%string /\
    is_blank (mk_open m ++ l) = false /\
    quote_prefix (mk_open m ++ l) = None /\
    heading_open (mk_open m ++ l) = None /\
    fence_open (mk_open m ++ l) = None /\
    div_open (mk_open m ++ l) = None /\
    indent_of (mk_open m ++ l) = 0.
Proof.
  intros m l Hm.
  (* Every case begins with an alphanumeric character, "(", or a bullet:
     not whitespace, ">", "#", "`" or "~".  The colon is a bullet too, so
     the div opener is ruled out by what follows it: an opener is one
     character and a space, and `:::` needs three. *)
  assert (Hhd : exists c r, (mk_open m ++ l)%string = String c r
                            /\ is_ws c = false
                            /\ Ascii.eqb c ">" = false /\ Ascii.eqb c "#" = false
                            /\ Ascii.eqb c "`" = false /\ Ascii.eqb c "~" = false
                            /\ div_open (String c r) = None).
  { destruct m as [c|c chk|core d].
    - cbn [marker_ok] in Hm.
      destruct (is_bullet_cases c Hm) as [E|[E|[E|E]]]; subst c;
        eexists; eexists; repeat split; reflexivity.
    - cbn [marker_ok] in Hm.
      destruct (is_task_bullet_cases c Hm) as [E|[E|E]]; subst c;
        destruct chk; eexists; eexists; repeat split; reflexivity.
    - cbn [marker_ok] in Hm.
      apply andb_true_iff in Hm as [Hm _]. apply andb_true_iff in Hm as [Hne Hal].
      destruct d; cbn [mk_open];
        [ destruct core as [|c core'] eqn:Ec; [discriminate Hne|]
        | destruct core as [|c core'] eqn:Ec; [discriminate Hne|]
        | exists "("%char; eexists; repeat split; reflexivity ];
        (cbn [str_forallb] in Hal; apply andb_true_iff in Hal as [Hc _];
         destruct (is_alnum_not_special c Hc) as (H1 & H2 & H3 & H4 & H5 & H6);
         exists c; eexists; repeat split; try assumption;
         apply div_open_not_colon; assumption). }
  destruct Hhd as (c & r & Heq & Hws & Hgt & Hhash & Hbq & Htil & Hcol).
  rewrite Heq.
  repeat split.
  - cbn [drop_leading_ws]. rewrite Hws. reflexivity.
  - cbn [is_blank]. rewrite Hws. reflexivity.
  - unfold quote_prefix. cbn [drop_leading_ws]. rewrite Hws, Hgt. reflexivity.
  - unfold heading_open. cbn [drop_leading_ws]. rewrite Hws.
    cbn [count_run]. rewrite (Ascii.eqb_sym "#" c), Hhash. reflexivity.
  - unfold fence_open. cbn [drop_leading_ws]. rewrite Hws, Hbq, Htil. reflexivity.
  - exact Hcol.
  - cbn [indent_of]. rewrite Hws. reflexivity.
Qed.

(* A bullet opener followed by a checkbox is a task marker instead, so an
   item's first line has to be one the marker survives. *)
Definition task_shadow (m : marker) (l : string) : bool :=
  match m with
  | MBullet _ => match task_check l with Some _ => true | None => false end
  | _ => false
  end.

(* The same test without the marker.  `item_ok` asks this rather than
   `task_shadow`, so that its dependence on the marker stays the
   thematic-break test alone (`OrderedList.item_ok_thematic_indep`).  The
   stronger condition costs nothing canonical: a canonical `Str` escapes
   its brackets. *)
Definition task_start (l : string) : bool :=
  match task_check l with Some _ => true | None => false end.

Lemma task_start_shadow :
  forall m l, task_start l = false -> task_shadow m l = false.
Proof.
  intros [c|c chk|core d] l H; [|reflexivity|reflexivity].
  unfold task_start in H. cbn [task_shadow].
  destruct (task_check l); [discriminate H|reflexivity].
Qed.

Local Lemma list_marker_open :
  forall m l, marker_ok m = true -> task_shadow m l = false ->
    list_marker (mk_open m ++ l) =
      Some (mk_sty m, mk_core m,
              match m with
              | MTask _ chk => Some (canonical_task_marker chk)
              | _ => None
              end, l).
Proof.
  intros m l Hm Hts.
  destruct (marker_open_shape m l Hm) as (Hdrop & _ & _ & _ & _ & _ & _).
  unfold list_marker. rewrite Hdrop.
  destruct m as [c|c chk|core d].
  - cbn [marker_ok] in Hm. cbn [mk_open mk_sty mk_core].
    change (String c " " ++ l)%string with (String c (String " " l)).
    cbn beta iota. rewrite Hm.
    cbn [task_shadow] in Hts.
    destruct (is_task_bullet c);
      [ destruct (task_check l) as [[st r]|]; [discriminate Hts|reflexivity]
      | reflexivity ].
  - cbn [marker_ok] in Hm.
    destruct (is_task_bullet_cases c Hm) as [E|[E|E]]; subst c;
      destruct chk; reflexivity.
  - cbn [marker_ok] in Hm.
    apply andb_true_iff in Hm as [Hm Hsty].
    apply andb_true_iff in Hm as [Hne Hal].
    cbn [mk_sty mk_core mk_open].
    (* The two suffix forms share a script: expose the core's first
       character so `marker_shape` takes its non-paren branch, then let
       `take_while_all_app` hand the core back whole.  The enclosed
       form starts with "(" and takes the other branch, where the core is
       already positioned for the same lemma. *)
    destruct d; rewrite append_assoc.
    + destruct core as [|c0 core'] eqn:Ec; [discriminate Hne|].
      cbn [str_forallb] in Hal. apply andb_true_iff in Hal as [Hc0 Hal'].
      change (String c0 core' ++ ". " ++ l)%string
        with (String c0 (core' ++ ". " ++ l))%string.
      cbn beta iota. rewrite (is_alnum_not_bullet c0 Hc0).
      cbn [marker_shape]. rewrite (is_alnum_not_paren c0 Hc0).
      change (String c0 (core' ++ ". " ++ l))%string
        with ((String c0 core') ++ (String "." (String " " l)))%string.
      rewrite (take_while_all_app is_alnum (String c0 core') (String "." (String " " l))
                 (ltac:(cbn [str_forallb]; rewrite Hc0, Hal'; reflexivity)) eq_refl).
      cbn beta iota. rewrite ?Ascii.eqb_refl. cbn beta iota match.
      destruct (styles_of_core (String c0 core') RightPeriod) eqn:Es;
        [cbn [nonempty] in Hsty; discriminate Hsty|].
      cbn [is_ws]. reflexivity.
    + destruct core as [|c0 core'] eqn:Ec; [discriminate Hne|].
      cbn [str_forallb] in Hal. apply andb_true_iff in Hal as [Hc0 Hal'].
      change (String c0 core' ++ ") " ++ l)%string
        with (String c0 (core' ++ ") " ++ l))%string.
      cbn beta iota. rewrite (is_alnum_not_bullet c0 Hc0).
      cbn [marker_shape]. rewrite (is_alnum_not_paren c0 Hc0).
      change (String c0 (core' ++ ") " ++ l))%string
        with ((String c0 core') ++ (String ")" (String " " l)))%string.
      rewrite (take_while_all_app is_alnum (String c0 core') (String ")" (String " " l))
                 (ltac:(cbn [str_forallb]; rewrite Hc0, Hal'; reflexivity)) eq_refl).
      cbn beta iota.
      change ((")" =? ".")%char) with false. rewrite ?Ascii.eqb_refl.
      cbn beta iota match.
      destruct (styles_of_core (String c0 core') RightParen) eqn:Es;
        [cbn [nonempty] in Hsty; discriminate Hsty|].
      cbn [is_ws]. reflexivity.
    + rewrite (append_assoc core ") " l).
      change ("(" ++ core ++ ") " ++ l)%string
        with (String "(" (core ++ String ")" (String " " l)))%string.
      cbn beta iota.
      change (is_bullet "(") with false.
      cbn beta iota match.
      cbn [marker_shape].
      change (("(" =? "(")%char) with true.
      cbn beta iota match.
      rewrite (take_while_all_app is_alnum core (String ")" (String " " l)) Hal eq_refl).
      cbn beta iota.
      change ((")" =? ")")%char) with true.
      cbn beta iota match.
      destruct (styles_of_core core LeftRightParen) eqn:Es;
        [cbn [nonempty] in Hsty; discriminate Hsty|].
      cbn [is_ws]. reflexivity.
Qed.

(* An opener classifies as its own marker, with the item's line as the
   residue.  The marker and the line together must not look like a
   thematic break ("- - -"), which `classify` tests first, and must not
   start a checkbox. *)
Lemma classify_marker_open :
  forall m l, marker_ok m = true -> is_thematic (mk_open m ++ l) = false ->
  task_shadow m l = false ->
  classify (mk_open m ++ l) =
    KList (mk_sty m) (mk_core m)
      (mk_task_marker m) l.
Proof.
  intros m l Hm Hth Hts.
  destruct (marker_open_shape m l Hm) as (_ & Hb & Hq & Hh & Hf & Hd & _).
  unfold classify. rewrite Hb, Hq, Hh, Hf, Hd, Hth.
  rewrite (list_marker_open m l Hm Hts). reflexivity.
Qed.

Local Lemma classify_bullet_open :
  forall l, is_thematic (bullet_open ++ l) = false ->
  task_shadow bullet l = false ->
  classify (bullet_open ++ l) = KList [SBullet "-"%char] EmptyString None l.
Proof.
  intros l Hth Hts. exact (classify_marker_open bullet l eq_refl Hth Hts).
Qed.

Lemma indent_of_marker_open :
  forall m l, marker_ok m = true -> indent_of (mk_open m ++ l) = 0.
Proof.
  intros m l Hm.
  destruct (marker_open_shape m l Hm) as (_ & _ & _ & _ & _ & _ & Hi).
  exact Hi.
Qed.

(* A recognized marker names at least one style, so a sibling's
   narrowing can land on a nonempty set. *)
Lemma mk_sty_cons :
  forall m, marker_ok m = true -> exists s ss, mk_sty m = s :: ss.
Proof.
  intros m Hm. destruct m as [c|c chk|core d].
  - exists (SBullet c), []. reflexivity.
  - exists (STask c), []. reflexivity.
  - cbn [marker_ok] in Hm. apply andb_true_iff in Hm as [_ Hsty].
    cbn [mk_sty]. destruct (styles_of_core core d) as [|s ss];
      [discriminate Hsty|]. exists s, ss. reflexivity.
Qed.

Lemma lstyle_eqb_eq : forall a b, lstyle_eqb a b = true -> a = b.
Proof.
  intros [c|c|n d] [c'|c'|n' d'] H; cbn [lstyle_eqb] in H; try discriminate.
  - apply Ascii.eqb_eq in H. subst c'. reflexivity.
  - apply Ascii.eqb_eq in H. subst c'. reflexivity.
  - apply andb_true_iff in H as [Hn Hd].
    destruct n, n'; try discriminate; destruct d, d'; try discriminate;
      reflexivity.
Qed.

Lemma mk_cont_length : forall m, String.length (mk_cont m) = mk_pad m.
Proof. intros m. unfold mk_cont. apply blanks_length. Qed.

(* A recognized marker has positive width, so an item's continuation
   indent is deeper than its marker column. *)
Lemma mk_pad_pos : forall m, marker_ok m = true -> 0 < mk_pad m.
Proof.
  intros m Hm. unfold mk_pad. destruct m as [c|c chk|core d].
  - cbn [mk_open String.length]. lia.
  - destruct chk; cbn [mk_open String.length]; lia.
  - cbn [marker_ok] in Hm.
    apply andb_true_iff in Hm as [Hm _]. apply andb_true_iff in Hm as [Hne _].
    destruct d; cbn [mk_open]; rewrite !length_append;
      cbn [String.length]; lia.
Qed.

(* The opener and the pad are one line's worth of text: newline-free and
   nonempty. *)
Lemma mk_open_nonempty : forall m, marker_ok m = true -> mk_open m <> EmptyString.
Proof.
  intros m Hm. pose proof (mk_pad_pos m Hm) as Hpos. unfold mk_pad in Hpos.
  destruct (mk_open m); [cbn in Hpos; lia | discriminate].
Qed.

Lemma mk_cont_nonempty : forall m, marker_ok m = true -> mk_cont m <> EmptyString.
Proof.
  intros m Hm. pose proof (mk_pad_pos m Hm) as Hpos.
  unfold mk_cont. destruct (mk_pad m); [lia | discriminate].
Qed.

Local Lemma blanks_no_nl : forall n, no_nl (blanks n) = true.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [blanks no_nl]. exact IH. Qed.

Lemma mk_cont_no_nl : forall m, no_nl (mk_cont m) = true.
Proof. intros m. unfold mk_cont. apply blanks_no_nl. Qed.

Local Lemma is_alnum_no_nl : forall c, is_alnum c = true -> negb (Ascii.eqb c "010") = true.
Proof.
  intros c H. destruct (Ascii.eqb c "010") eqn:E; [|reflexivity].
  apply Ascii.eqb_eq in E. subst c. discriminate H.
Qed.

Lemma mk_open_no_nl : forall m, marker_ok m = true -> no_nl (mk_open m) = true.
Proof.
  intros m Hm. destruct m as [c|c chk|core d].
  - cbn [marker_ok] in Hm.
    apply is_bullet_cases in Hm as [E|[E|[E|E]]]; rewrite E; reflexivity.
  - cbn [marker_ok] in Hm.
    apply is_task_bullet_cases in Hm as [E|[E|E]]; rewrite E;
      destruct chk; reflexivity.
  - cbn [marker_ok] in Hm.
    apply andb_true_iff in Hm as [Hm _]. apply andb_true_iff in Hm as [_ Halnum].
    assert (Hcore : no_nl core = true).
    { clear d. induction core as [|c rest IH]; [reflexivity|].
      cbn [str_forallb] in Halnum. apply andb_true_iff in Halnum as [Hc Hrest].
      cbn [no_nl]. rewrite (is_alnum_no_nl c Hc). cbn [andb]. apply IH, Hrest. }
    destruct d; cbn [mk_open]; rewrite ?no_nl_append, Hcore; reflexivity.
Qed.

Local Lemma indent_of_bullet_open : forall l, indent_of (bullet_open ++ l) = 0.
Proof. reflexivity. Qed.
