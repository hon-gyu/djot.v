(* ai-disclosure: autonomous *)

(* Line classification: the prefix-determinism seam.

   Block structure in djot is a function of what each line looks like
   (spec: "blocks can be parsed line by line ... the contribution a line
   makes to block-level structure never depends on a future line").  This
   module gives each line its kind; the parser consumes kinds, and the
   classifier is the single place a new block construct's start syntax is
   added.  Renderability (Render.v) is phrased as "each rendered line
   classifies as intended", which is what makes roundtrip proofs local. *)

From Stdlib Require Import String Ascii List Bool PeanoNat Lia.
Import ListNotations.
From DjotV Require Import Strings Ast Attributes.

Local Open Scope string_scope.
Local Open Scope char_scope.

(* An opened code fence: its character (` or ~), length, and info string
   (language, or =FORMAT for raw blocks). *)
Record fence : Type := Fence
  { f_ch : ascii; f_len : nat; f_info : string }.

(* A list style: `getListStyles`' return element, typed.  The ordered
   half reuses `Ast`'s pair, since that is what the `OrderedList` node
   carries and nothing is gained by translating between two spellings.

   A marker yields a *set* of these — see "List markers" below. *)
Inductive lstyle : Type :=
  | SBullet (c : ascii)
  | SOrd (n : ordered_list_style) (d : ordered_list_delim).

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
  | SOrd n d, SOrd n' d' => (ols_eqb n n' && old_eqb d d')%bool
  | _, _ => false
  end.

Inductive line_kind : Type :=
  | KBlank                 (* only whitespace *)
  | KThematic              (* thematic break: 3+ of - or * (mixed ok), ws between *)
  | KFence (f : fence)     (* code fence opener *)
  | KDiv (len : nat) (cls : string)    (* fenced-div opener, with its class *)
  | KQuote (rest : string) (* block-quote prefix, with the line it encloses *)
  | KHeading (level : nat) (rest : string)   (* #+ then ws, with its text *)
  (* A list marker: its candidate styles, its numeral core (empty for a
     bullet), and the content after it. *)
  | KList (sty : list lstyle) (core : string) (rest : string)
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
  | KText.                 (* anything else: paragraph text *)

(*
Recognizers
===========
*)

(* A thematic-break marker character. *)
Definition is_marker (c : ascii) : bool :=
  Ascii.eqb c "-" || Ascii.eqb c "*".

(* djot.js pattThematicBreak: markers and whitespace only, >= 3 markers.
   (Indentation is allowed; leading ws goes through the ws branch.) *)

Fixpoint thematic_count (s : string) (count : nat) : bool :=
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
Lemma is_ws_not_marker : forall c, is_ws c = true -> is_marker c = false.
Proof.
  intros c H. unfold is_marker.
  destruct (Ascii.eqb c "-") eqn:E1.
  - apply Ascii.eqb_eq in E1. subst c. discriminate H.
  - destruct (Ascii.eqb c "*") eqn:E2; [|reflexivity].
    apply Ascii.eqb_eq in E2. subst c. discriminate H.
Qed.

Lemma thematic_count_ws_prefix :
  forall p l n, is_blank p = true -> thematic_count (p ++ l) n = thematic_count l n.
Proof.
  induction p as [|c p IH]; intros l n H; [reflexivity|].
  cbn [is_blank] in H. apply andb_true_iff in H as [Hc Hp].
  change (String c p ++ l) with (String c (p ++ l)).
  cbn [thematic_count]. rewrite (is_ws_not_marker c Hc), Hc. apply IH, Hp.
Qed.

Lemma is_thematic_ws_prefix :
  forall p l, is_blank p = true -> is_thematic (p ++ l) = is_thematic l.
Proof. intros p l H. unfold is_thematic. apply thematic_count_ws_prefix, H. Qed.

(* Code fences, per djot.js pattCodeFence:
   3+ of a uniform fence char (` or ~), optional ws, one info token
   containing neither whitespace nor backticks, optional trailing ws.
   The fence may be indented.  A close line is the same char, at least
   the open length, and nothing else but whitespace. *)

(* Length of the leading run of c, and the rest of the string. *)
Fixpoint count_run (c : ascii) (s : string) : nat * string :=
  match s with
  | String c' s' =>
      if Ascii.eqb c c'
      then let (n, r) := count_run c s' in (S n, r)
      else (O, s)
  | EmptyString => (O, s)
  end.

(* Characters admissible in a fence info string. *)
Definition is_info_char (c : ascii) : bool :=
  negb (is_ws c || Ascii.eqb c "`" || Ascii.eqb c "010").

(* Split off the leading info token from the rest of the line. *)
Fixpoint take_info (s : string) : string * string :=
  match s with
  | String c s' =>
      if is_info_char c
      then let (info, r) := take_info s' in (String c info, r)
      else (EmptyString, s)
  | EmptyString => (EmptyString, s)
  end.

(* Does this line open a fence, and if so which one? *)
Definition fence_open (l : string) : option fence :=
  match drop_leading_ws l with
  | String c _ as l' =>
      if Ascii.eqb c "`" || Ascii.eqb c "~"
      then
        let (n, r) := count_run c l' in
        if Nat.leb 3 n
        then
          let (info, r') := take_info (drop_leading_ws r) in
          if is_blank r' then Some (Fence c n info) else None
        else None
      else None
  | EmptyString => None
  end.

(* Does this line close the given open fence?  Note this is the *only*
   test applied to a line inside a fence — content is never classified. *)
Definition fence_close (f : fence) (l : string) : bool :=
  let (n, r) := count_run (f_ch f) (drop_leading_ws l) in
  Nat.leb (f_len f) n && is_blank r.

(* Fenced divs.  Two recognizers, not one, because the opener and the
   closer are different patterns in djot.js: `pattDivFenceStart` plus
   `pattDivFenceEnd` (block.ts:55-56) lets the opener carry a class,
   while `pattDivFence` (block.ts:54) does not, so `::: foo` opens a div
   but never closes one.

   The close is applied by the *open div* to every line, the way
   `fence_close` is, and never by `classify` — which is why there is no
   `KDivClose`.  A bare `:::` is both a legal opener and a legal closer;
   djot.js resolves that by running the container's `continue` before any
   opener is tried, and `step`'s PDiv branch does the same. *)

(* djot.js's class token is `[\w_-]*` — narrower than a code fence's info
   string, and the difference is observable: `:::a!` opens no div at all,
   because the pattern must match through end of line. *)
Definition is_class_char (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (Nat.leb 48 n && Nat.leb n 57)      (* 0-9 *)
  || (Nat.leb 65 n && Nat.leb n 90)   (* A-Z *)
  || (Nat.leb 97 n && Nat.leb n 122)  (* a-z *)
  || Ascii.eqb c "_" || Ascii.eqb c "-".

Fixpoint take_class (s : string) : string * string :=
  match s with
  | String c s' =>
      if is_class_char c
      then let (cls, r) := take_class s' in (String c cls, r)
      else (EmptyString, s)
  | EmptyString => (EmptyString, s)
  end.

Definition div_open (l : string) : option (nat * string) :=
  match drop_leading_ws l with
  | String c _ as l' =>
      if Ascii.eqb c ":"
      then
        let (n, r) := count_run ":" l' in
        if Nat.leb 3 n
        then let (cls, r') := take_class (drop_leading_ws r) in
             if is_blank r' then Some (n, cls) else None
        else None
      else None
  | EmptyString => None
  end.

(* Closes a div opened with `len` colons: at least that many, then only
   whitespace.  Shaped exactly like `fence_close`, and applied the same
   way — but note the leading `drop_leading_ws`, which is what makes a
   div's closer visible through any amount of indentation and therefore
   through any nesting.  That asymmetry with `quote_prefix` (whose '>' is
   non-whitespace and so blocks the scan) is the whole content of
   `div_uniformity`'s side condition. *)
Definition div_close (len : nat) (l : string) : bool :=
  let (n, r) := count_run ":" (drop_leading_ws l) in
  Nat.leb len n && Nat.leb 3 n && is_blank r.

(* The enclosed content of a div is the line itself, unshortened, so
   unlike quote_prefix there is no length lemma to prove: a div's descent
   drops a container from the state rather than shortening the line, the
   same measure a list item's contents use. *)

(* Block quotes, per djot.js pattBlockquotePrefix (`[>][ \t\r\n]`): a
   '>' that is followed by whitespace or ends the line.  The prefix is
   the '>' plus at most one whitespace character; what remains is the
   enclosed line, which the parser classifies again (so nesting and
   uniformity both come from re-entering `classify`).

   `>x` is *not* a quote — the whitespace is required.  Indentation
   before the '>' is allowed. *)
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
Lemma quote_prefix_length :
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

(* Headings, per djot.js's `pattBangs` plus a whitespace test: one or
   more '#' followed by whitespace or end of line.  Shaped exactly like
   quote_prefix — marker, then at most one whitespace character — but the
   text that follows is *not* reclassified: a heading's content is
   inline, so `# > q` is a heading containing "> q", not a quote. *)
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

djot.js's `pattListMarker` (block.ts:59) followed by `getListStyles`
(block.ts:9-31).  Two facts about that pair shape everything here.

First, `getListStyles` normalizes the numeral *out* of the marker: `3.`
and `4.` both yield the style `1.`.  The container stack therefore
compares styles and never numbers — a list carries no counter.  The
numeral survives only as the marker's `core`, which the list's `start`
is decoded from once, at close, by `list_start` in Parser.v.

Second, a marker may be *ambiguous*: `i.` is both roman and alpha, so a
marker yields a candidate *set*, which siblings intersect (`narrow` in
Parser.v).  An empty intersection ends the list.

Definition lists (`:`) and task-list checkboxes are still out; they are
the other two members of djot.js's single list spec. *)

(* `-x` is not a marker, and `* * *` is a thematic break — `classify`
   tests thematic first, matching djot.js's spec order. *)
Definition is_bullet (c : ascii) : bool :=
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

(* The roman digits, djot.js's `romanDigits` domain (parse.ts:63-78). *)
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

(* The longest prefix of `s` satisfying `p`, and what is left. *)
Fixpoint take_while (p : ascii -> bool) (s : string) : string * string :=
  match s with
  | String c s' =>
      if p c
      then let (a, b) := take_while p s' in (String c a, b)
      else (EmptyString, s)
  | EmptyString => (EmptyString, s)
  end.

Lemma take_while_length :
  forall p s, String.length (snd (take_while p s)) <= String.length s.
Proof.
  intros p s. induction s as [|c s' IH]; [reflexivity|].
  cbn [take_while]. destruct (p c); [|reflexivity].
  destruct (take_while p s') as [a b]. cbn [snd String.length] in *. lia.
Qed.

(*
Marker shape and candidate styles
---------------------------------
*)

(* An ordered marker's two halves: an alphanumeric `core` and a
   delimiter shape.  `(` forces the enclosed form, which is why this is
   one function rather than a delimiter test after a scan. *)
Definition marker_shape (s : string)
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

Lemma marker_shape_length :
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

(* `getListStyles`, on a core that `marker_shape` has already split off.
   The single-character roman cases come before the multi-character ones
   because they are the ambiguous ones: `i.` is roman *or* alpha, while
   `ix.` can only be roman.  An empty core is not a marker — `().` — so
   it is excluded before the `str_forallb`s, which would otherwise
   accept it vacuously. *)
Definition styles_of_core (core : string) (d : ordered_list_delim)
  : list lstyle :=
  match core with
  | EmptyString => []
  | String c rest =>
      if str_forallb is_digit core then [SOrd Decimal d]
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

(* A list marker: its candidate styles, its numeral core (empty for a
   bullet, which has no number), and the content after it.  Same
   marker-then-at-most-one-space shape as quotes and headings. *)
Definition list_marker (l : string)
  : option (list lstyle * string * string) :=
  match drop_leading_ws l with
  | EmptyString => None
  | String c rest =>
      if is_bullet c
      then match rest with
           | EmptyString => Some ([SBullet c], EmptyString, EmptyString)
           | String c' rest' =>
               if is_ws c' then Some ([SBullet c], EmptyString, rest') else None
           end
      else
        match marker_shape (String c rest) with
        | None => None
        | Some (core, d, r) =>
            match styles_of_core core d with
            | [] => None
            | sty =>
                match r with
                | EmptyString => Some (sty, core, EmptyString)
                | String c' r' =>
                    if is_ws c' then Some (sty, core, r') else None
                end
            end
        end
  end.

(* Like quote_prefix_length: the content after a list marker is strictly
   shorter than the line, which is what makes the parser's descent into
   a list item terminate. *)
Lemma list_marker_length :
  forall l sty core rest,
    list_marker l = Some (sty, core, rest) ->
    String.length rest < String.length l.
Proof.
  intros l sty core rest H. unfold list_marker in H.
  pose proof (drop_leading_ws_length l) as Hle.
  destruct (drop_leading_ws l) as [|c r] eqn:E; [discriminate|].
  destruct (is_bullet c).
  - simpl in Hle.
    destruct r as [|c' r'].
    + injection H as _ _ <-. simpl. lia.
    + destruct (is_ws c'); [|discriminate].
      injection H as _ _ <-. simpl in *. lia.
  - pose proof (marker_shape_length (String c r)) as Hms.
    destruct (marker_shape (String c r)) as [[[core' d] r0]|] eqn:Em;
      [|discriminate].
    specialize (Hms _ _ _ eq_refl).
    destruct (styles_of_core core' d) as [|s0 ss] eqn:Es; [discriminate|].
    destruct r0 as [|c' r0'].
    + injection H as _ _ <-. simpl in *. lia.
    + destruct (is_ws c'); [|discriminate].
      injection H as _ _ <-. simpl in *. lia.
Qed.

(*
Reference definitions
=====================

`[label]: destination`, djot.js's `pattReferenceDefinition`
(block.ts:57) — a block-level construct producing no block of its own,
only an entry in the document's reference map.  Its destination may be
continued on the following indented lines, which is why it opens a
container state (Step.PRef) rather than emitting on sight.
*)

(* The label: everything up to the first `]`, and the line after it.
   djot.js's `[^\]\r\n]*` excludes only the bracket, so `[a[b]: u` is a
   definition of `a[b`. *)
Fixpoint ref_label (s : string) : option (string * string) :=
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
   whitespace-free run to end of line.  Both halves of that are load
   bearing — `[a]:u` and `[a]: u ` are neither of them definitions
   (checked against djot.js), because the pattern demands the space
   before the destination and the end of line right after it. *)
Definition ref_value (s : string) : option string :=
  match s with
  | EmptyString => Some EmptyString
  | String c _ =>
      if is_ws c
      then let t := drop_leading_ws s in
           if no_ws t then Some t else None
      else None
  end.

(* A label claimed by the footnote container, which djot.js tries first
   (block.ts:264 before :301): `^` and at least one more character.
   `[^]: u` is not one, and is a reference definition of the label `^`. *)
Definition is_footnote_label (lbl : string) : bool :=
  match lbl with
  | String "^"%char (String _ _) => true
  | _ => false
  end.

(* `[^label]: body`, djot.js's `pattFootnoteStart`.  Unlike a reference
   definition, the body is ordinary block content and may contain spaces;
   only the single whitespace byte claimed by the opener is removed. *)
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

Lemma foot_open_ws_prefix :
  forall p l, is_blank p = true -> foot_open (p ++ l) = foot_open l.
Proof.
  intros p l Hp. unfold foot_open.
  rewrite (drop_leading_ws_ws_prefix p l Hp). reflexivity.
Qed.

Lemma foot_open_label_ok :
  forall l lbl rest,
    foot_open l = Some (lbl, rest) ->
    (nonempty_str lbl && no_char "]"%char lbl)%bool = true.
Proof.
  assert (Hlabel : forall s lbl tail,
    ref_label s = Some (lbl, tail) -> no_char "]"%char lbl = true).
  { induction s as [|c s IH]; intros lbl tail H; [discriminate|].
    cbn [ref_label] in H. destruct (Ascii.eqb c "]") eqn:E.
    - injection H as <- _. reflexivity.
    - destruct (ref_label s) as [[lbl' tail']|] eqn:Er; [|discriminate].
      injection H as <- _. cbn [no_char]. rewrite E.
      apply (IH lbl' tail' eq_refl). }
  intros l lbl body H. unfold foot_open in H.
  destruct (drop_leading_ws l) as [|c [|h s]]; try discriminate.
  destruct (Ascii.eqb c "["); cbn [negb] in H; [|discriminate].
  destruct (Ascii.eqb h "^"); cbn [negb] in H; [|discriminate].
  destruct (ref_label s) as [[lbl' [|col after]]|] eqn:Er; try discriminate.
  destruct (Ascii.eqb col ":"); cbn [negb] in H; [|discriminate].
  destruct (nonempty_str lbl') eqn:Hne; cbn [negb] in H; [|discriminate].
  destruct after as [|w tail].
  - injection H as <- <-. rewrite Hne, andb_true_l.
    apply (Hlabel s lbl' _ Er).
  - destruct (is_ws w); [|discriminate].
    injection H as <- <-. rewrite Hne, andb_true_l.
    apply (Hlabel s lbl' _ Er).
Qed.

Lemma ref_label_tail_length :
  forall s lbl tail,
    ref_label s = Some (lbl, tail) -> String.length tail < String.length s.
Proof.
  induction s as [|c s IH]; intros lbl tail H; [discriminate|].
  cbn [ref_label] in H. destruct (Ascii.eqb c "]").
  - injection H as _ <-. cbn. lia.
  - destruct (ref_label s) as [[lbl' tail']|] eqn:E; [|discriminate].
    injection H as _ <-. specialize (IH lbl' tail' eq_refl). cbn. lia.
Qed.

Lemma foot_open_length :
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

(* The two facts the parser's output needs about a label: it can be
   written back between brackets, and it is not a footnote's. *)
Lemma ref_label_no_bracket :
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
Lemma ref_open_ws_prefix :
  forall p l, is_blank p = true -> ref_open (p ++ l) = ref_open l.
Proof.
  intros p l Hp. unfold ref_open. rewrite (drop_leading_ws_ws_prefix p l Hp).
  reflexivity.
Qed.

(* The classifier: one line in, one kind out, no lookahead.  Blank first,
   then block quotes, headings, fences, thematic breaks, list markers;
   anything unrecognized falls through to paragraph text, so KText is the
   catch-all.  Adding a block construct starts by adding a case here. *)
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
                            | Some (sty, core, rest) => KList sty core rest
                            | None =>
                                match attr_open l with
                                | Some p => KAttr p
                                | None =>
                                    match foot_open l with
                                    | Some (lbl, rest) => KFoot lbl rest
                                    | None =>
                                        match ref_open l with
                                        | Some (lbl, v) => KRef lbl v
                                        | None => KText
                                        end
                                    end
                                end
                            end
                   end
               end
           end
       end.

(* Headings always have a level, which is what wf_block requires of the
   `Heading` it builds. *)
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
    destruct (list_marker l) as [[[s0 c0] r0]|]; [discriminate|].
    destruct (attr_open l); [discriminate|].
    destruct (foot_open l) as [[fl fr]|]; [discriminate|].
    destruct (ref_open l) as [[rl rv]|]; discriminate.
  - destruct (fence_open l); [discriminate|].
  destruct (div_open l) as [[dn dc]|]; [discriminate|].
    destruct (is_thematic l); [discriminate|].
    destruct (list_marker l) as [[[s0 c0] r0]|]; [discriminate|].
    destruct (attr_open l); [discriminate|].
    destruct (foot_open l) as [[fl fr]|]; [discriminate|].
    destruct (ref_open l) as [[rl rv]|]; discriminate.
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
  destruct (list_marker l) as [[[s0 c0] r0]|]; [discriminate|].
  destruct (attr_open l); [discriminate|].
  destruct (foot_open l) as [[fl fr]|]; [discriminate|].
    destruct (ref_open l) as [[rl rv]|]; discriminate.
Qed.

(* The measure fact, restated at the classifier: the parser only ever
   sees KQuote, never quote_prefix directly. *)
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
    destruct (list_marker l) as [[[s0 c0] r0]|]; [discriminate|].
    destruct (attr_open l); [discriminate|].
    destruct (foot_open l) as [[fl fr]|]; [discriminate|].
    destruct (ref_open l) as [[rl rv]|]; discriminate.
Qed.

Lemma classify_list_length :
  forall l sty core rest,
    classify l = KList sty core rest ->
    String.length rest < String.length l.
Proof.
  intros l sty core rest H. apply (list_marker_length l sty core).
  unfold classify in H.
  destruct (is_blank l); [discriminate|].
  destruct (quote_prefix l); [discriminate|].
  destruct (heading_open l) as [[lvl r2]|]; [discriminate|].
  destruct (fence_open l); [discriminate|].
  destruct (div_open l) as [[dn dc]|]; [discriminate|].
  destruct (is_thematic l); [discriminate|].
  destruct (list_marker l) as [[[s' c'] r']|];
    [|destruct (attr_open l); [discriminate|];
      destruct (foot_open l) as [[fl fr]|]; [discriminate|];
      destruct (ref_open l) as [[rl rv]|]; discriminate].
  injection H as <- <- <-. reflexivity.
Qed.

Lemma classify_not_kblank_nonblank :
  forall l, classify l <> KBlank -> is_blank l = false.
Proof.
  intros l H. destruct (is_blank l) eqn:E; [|reflexivity].
  exfalso. apply H, classify_blank, E.
Qed.

Lemma classify_ktext :
  forall l,
    is_blank l = false -> quote_prefix l = None -> heading_open l = None ->
    fence_open l = None -> div_open l = None ->
    is_thematic l = false -> list_marker l = None -> attr_open l = None ->
    foot_open l = None ->
    ref_open l = None ->
    classify l = KText.
Proof.
  intros l Hb Hq Hh Hf Hd Ht Hm Ha Hfoot Hr. unfold classify.
  rewrite Hb, Hq, Hh, Hf, Hd, Ht, Hm, Ha, Hfoot, Hr. reflexivity.
Qed.

(* The canonical thematic-break rendering classifies as one. *)
Lemma classify_canonical_thematic : classify "* * * *" = KThematic.
Proof. reflexivity. Qed.

(* An all-whitespace prefix is invisible to the classifier: every
   recognizer either routes through drop_leading_ws (quote/heading/fence/
   list markers) or, for is_thematic, treats whitespace as skippable
   throughout, not just leading (Strings.drop_leading_ws_ws_prefix,
   is_thematic_ws_prefix).  This is what lets a list item's "  "
   continuation indent be pushed straight through: the enclosed line
   reclassifies exactly as it would unindented. *)
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
          (ref_open_ws_prefix p l Hp).
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
  destruct (list_marker l) as [[[s0 c0] r0]|]; [discriminate|].
  destruct (attr_open l); [discriminate|].
  destruct (foot_open l) as [[fl fr]|]; [injection H as <- <-; reflexivity|].
  destruct (ref_open l) as [[rl rv]|]; discriminate.
Qed.

Lemma classify_foot_length :
  forall l lbl rest,
    classify l = KFoot lbl rest -> String.length rest < String.length l.
Proof.
  intros l lbl rest H. apply (foot_open_length l lbl rest).
  exact (classify_kfoot l lbl rest H).
Qed.

(* A KRef classification is `ref_open`'s answer, which is what carries
   the label and destination conditions to Wf.v. *)
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
  destruct (list_marker l) as [[[s0 c0] r0]|]; [discriminate|].
  destruct (attr_open l); [discriminate|].
  destruct (foot_open l) as [[fl fr]|]; [discriminate|].
  destruct (ref_open l) as [[rl rv]|]; [|discriminate].
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

Lemma count_run_info :
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

Lemma drop_leading_ws_info :
  forall info, all_info_chars info = true ->
  drop_leading_ws info = info.
Proof.
  intros info H. destruct info as [|c info']; [reflexivity|].
  simpl in H. apply andb_true_iff in H as [Hc _].
  apply info_char_parts in Hc as (Hw & _ & _).
  cbn [drop_leading_ws]. rewrite Hw. reflexivity.
Qed.

Lemma take_info_all :
  forall info, all_info_chars info = true ->
  take_info info = (info, EmptyString).
Proof.
  induction info as [|c info IH]; intros H; [reflexivity|].
  simpl in H. apply andb_true_iff in H as [Hc Hinfo].
  cbn [take_info]. rewrite Hc, (IH Hinfo). reflexivity.
Qed.

Lemma drop_head_nonws :
  forall c s, is_ws c = false -> drop_leading_ws (String c s) = String c s.
Proof. intros c s H. cbn [drop_leading_ws]. rewrite H. reflexivity. Qed.

(* The two facts the roundtrip proof actually consumes: the renderer's
   "```INFO" opener and "```" closer behave as intended. *)
Lemma fence_open_backtick :
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

(* Canonical block-quote prefixing, the renderer's spelling: "> " in
   front of every line, including blank ones.

   `quote_open` lives here rather than in Render because Parser needs to
   name its width.  Both containers descend by two columns, so a bare `2`
   in a parser proof does not say which one it means; `String.length
   quote_open` and `String.length bullet_cont` do. *)
Definition quote_open : string := "> ".
Definition quote_line (l : string) : string := quote_open ++ l.

(* The column a quote's contents start at.  Definitionally 2, and named
   so that a parser proof mentioning it cannot be confused with
   `item_pad`, which is also 2 and means something else. *)
Definition quote_pad : nat := String.length quote_open.

Lemma quote_prefix_canonical :
  forall l, quote_prefix ("> " ++ l) = Some l.
Proof. reflexivity. Qed.

Lemma classify_canonical_quote :
  forall l, classify ("> " ++ l) = KQuote l.
Proof.
  intros l. unfold classify.
  change (is_blank ("> " ++ l)) with false.
  rewrite quote_prefix_canonical. reflexivity.
Qed.

(* Same, seen through an all-whitespace pad: a quote's own prefix is
   detected identically regardless of what ambient indentation precedes
   it, and the extracted content is exactly `l` with no pad residue —
   this is what lets a quote nested inside a list item ignore the
   item's indent entirely.  A nested list does not get the same free
   ride: `ls_indent` is read off the raw line, so the item's pad shifts
   it.  That is a shift, not a difference in outcome, and
   `Parser.run_lines_pad_shift` is where it is discharged. *)
Lemma classify_canonical_quote_pad :
  forall pad l, is_blank pad = true -> classify (pad ++ "> " ++ l) = KQuote l.
Proof.
  intros pad l Hpad. rewrite classify_ws_prefix by exact Hpad.
  apply classify_canonical_quote.
Qed.

(*
Canonical headings
==================

The renderer prefixes every line of a heading with its hashes and one
space, so a multi-line heading reparses line by line as continuations of
itself — the same trick as block quotes, without the reclassification. *)

Fixpoint hashes (n : nat) : string :=
  match n with O => EmptyString | S n' => "#" ++ hashes n' end.

Definition heading_line (lvl : nat) (l : string) : string :=
  hashes lvl ++ " " ++ l.

(* The hashes are consumed exactly: the renderer's space stops the run,
   so the level comes back out unchanged however long the text is. *)
Lemma count_run_hashes_space :
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

Lemma no_nl_hashes : forall n, no_nl (hashes n) = true.
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

The renderer emits the shortest legal fence, classless, for both ends —
the same choice `code_open`/`code_close` make, and it carries the same
cost: a div whose contents contain a `:::` line cannot be rendered, so
`cb_ok` excludes it rather than growing the fence. *)

Definition div_fence : string := ":::".

Lemma classify_canonical_div : classify div_fence = KDiv 3 EmptyString.
Proof. reflexivity. Qed.

Lemma div_close_canonical : div_close 3 div_fence = true.
Proof. reflexivity. Qed.

(* Whitespace in front of a div's closer is invisible to it, which is
   what `classify_ws_prefix` does *not* give us: `div_close` is applied
   by the open div directly, never through `classify`, so it needs its
   own statement.  This is the lemma the indented-close counterexample
   turns on. *)
(* A blank line never closes a div, whatever fence length is open: the
   `3 <=` conjunct fails on the empty colon run.  This is what lets a
   blank inside a div behave exactly as it does at top level. *)
Lemma drop_leading_ws_blank :
  forall s, is_blank s = true -> drop_leading_ws s = EmptyString.
Proof.
  induction s as [|c s IH]; [reflexivity|].
  cbn [is_blank drop_leading_ws]. destruct (is_ws c) eqn:E; [exact IH|discriminate].
Qed.

Lemma div_close_blank :
  forall len l, is_blank l = true -> div_close len l = false.
Proof.
  intros len l H. unfold div_close.
  rewrite (drop_leading_ws_blank l H).
  cbn [count_run]. rewrite Bool.andb_false_r. reflexivity.
Qed.

Lemma div_close_ws_prefix :
  forall p len l, is_blank p = true -> div_close len (p ++ l) = div_close len l.
Proof.
  intros p len l Hp. unfold div_close.
  rewrite (drop_leading_ws_ws_prefix p l Hp). reflexivity.
Qed.

(* classify_canonical_heading, seen through an all-whitespace pad — same
   free ride as classify_canonical_quote_pad. *)
Lemma classify_canonical_heading_pad :
  forall pad lvl l, is_blank pad = true -> 1 <= lvl ->
  classify (pad ++ heading_line lvl l) = KHeading lvl l.
Proof.
  intros pad lvl l Hpad Hlvl. rewrite classify_ws_prefix by exact Hpad.
  apply classify_canonical_heading, Hlvl.
Qed.

(*
Canonical bullet lists
=======================

The renderer marks an item's first line with "- " and every later line
(whether a continuation of that first block or the start of a later one)
with two spaces of plain indent — the same shape djot.js's own
`this.indent > container.extra.indent` test expects, since `bullet_open`
puts the marker at column 0 and everything after it at column 2.  Unlike
quote_line, the marker is not repeated on every line: `bullet_cont` is
whitespace, so `classify_ws_prefix` carries every recognizer through it
for free — a nested construct starting on a continuation line reclassifies
exactly as it would unindented. *)

(* A run of spaces, the continuation indent's shape.  Ordered markers
   differ from bullets only in how long this is. *)
Fixpoint blanks (n : nat) : string :=
  match n with O => EmptyString | S k => String " " (blanks k) end.

Lemma blanks_blank : forall n, is_blank (blanks n) = true.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [blanks is_blank]. exact IH. Qed.

Lemma blanks_length : forall n, String.length (blanks n) = n.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [blanks String.length]. rewrite IH. reflexivity. Qed.

(* A list marker, as the renderer and the classifier jointly see it.
   Shaped after `list_marker`'s own two branches rather than after the
   string it produces, so that every fact below is a case analysis the
   classifier already performs: a bullet is one character, an ordered
   marker is an alphanumeric core inside a delimiter.

   Everything the uniformity chain needs about a marker is here, which is
   what lets `list_uniformity` quantify over it.  Note what is *not*
   here: a width.  `mk_pad` is derived, and no continuation rule reads
   it — djot.js tests `indent > marker column`, so a wider marker moves
   nothing. *)
Inductive marker : Type :=
  | MBullet (c : ascii)
  | MOrd (core : string) (d : ordered_list_delim).

Definition mk_open (m : marker) : string :=
  match m with
  | MBullet c => String c " "
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
  | MOrd core d => styles_of_core core d
  end.

Definition mk_core (m : marker) : string :=
  match m with MBullet _ => EmptyString | MOrd core _ => core end.

(* Which markers the classifier actually recognizes.  An ordered core has
   to be alphanumeric (so `marker_shape` scans exactly it) and has to name
   at least one style (so `list_marker` does not reject it). *)
Definition marker_ok (m : marker) : bool :=
  match m with
  | MBullet c => is_bullet c
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

(* The other two bullet styles djot recognizes.  They exist here so the
   generalization above is exercised rather than merely available: djot
   starts a new list when the style changes, so these are genuinely
   different lists, and nothing in the chain below is proved twice. *)
Definition star : marker := MBullet "*".
Definition plus : marker := MBullet "+".

Lemma star_ok : marker_ok star = true.
Proof. reflexivity. Qed.

Lemma plus_ok : marker_ok plus = true.
Proof. reflexivity. Qed.

Lemma marker_cont_blank : forall m, is_blank (mk_cont m) = true.
Proof. intros m. apply blanks_blank. Qed.

Lemma bullet_cont_blank : is_blank bullet_cont = true.
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

Lemma classify_bullet_cont :
  forall l, classify (bullet_cont ++ l) = classify l.
Proof. intros l. apply classify_marker_cont. Qed.

Lemma indent_of_bullet_cont :
  forall l, indent_of (bullet_cont ++ l) = item_pad + indent_of l.
Proof. intros l. apply indent_of_marker_cont. Qed.

(* The three bullet styles, enumerated: `is_bullet` is a disjunction of
   character tests, so every fact about a recognized marker reduces to
   three concrete cases. *)
Lemma is_bullet_cases :
  forall c, is_bullet c = true ->
    c = "-"%char \/ c = "*"%char \/ c = "+"%char.
Proof.
  intros c H. unfold is_bullet in H.
  destruct (Ascii.eqb c "-") eqn:E1; [left; apply Ascii.eqb_eq, E1|].
  destruct (Ascii.eqb c "*") eqn:E2; [right; left; apply Ascii.eqb_eq, E2|].
  destruct (Ascii.eqb c "+") eqn:E3; [right; right; apply Ascii.eqb_eq, E3|].
  cbn in H. discriminate.
Qed.

(* The marker line's classification needs one extra hypothesis quotes and
   headings don't: the marker plus the item's own first line must not
   itself look like a thematic break ("- - -"), since `classify` tests
   thematic breaks before list markers.  A canonical item's cb_ok carries
   this. *)
(* An alphanumeric run followed by something that is not: exactly what
   `marker_shape` scans, so an ordered marker's core comes off whole and
   the rest of the line survives untouched. *)
Lemma take_while_alnum_app :
  forall core rest,
    str_forallb is_alnum core = true ->
    match rest with String c _ => is_alnum c = false | EmptyString => True end ->
    take_while is_alnum (core ++ rest) = (core, rest).
Proof.
  induction core as [|c core IH]; intros rest Hcore Hrest.
  - destruct rest as [|c r]; [reflexivity|].
    cbn [take_while append]. rewrite Hrest. reflexivity.
  - cbn [str_forallb] in Hcore. apply andb_true_iff in Hcore as [Hc Hcore].
    change ((String c core) ++ rest)%string with (String c (core ++ rest))%string.
    cbn [take_while]. rewrite Hc, (IH rest Hcore Hrest). reflexivity.
Qed.

(* An alphanumeric character is none of the characters the recognizers
   ahead of `list_marker` look for. *)
Lemma is_alnum_not_bullet :
  forall c, is_alnum c = true -> is_bullet c = false.
Proof.
  intros c H. destruct (is_bullet c) eqn:E; [|reflexivity].
  destruct (is_bullet_cases c E) as [F|[F|F]]; subst c; discriminate H.
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

Lemma is_alnum_not_paren :
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

(* A marker opener is never blank and never starts with whitespace, so
   the recognizers `classify` runs before `list_marker` all see its first
   character and all reject it. *)
Lemma marker_open_shape :
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
  (* Every case begins with a character that is alphanumeric, "(", or a
     bullet — none of them whitespace, ">", "#", "`", "~" or ":". *)
  assert (Hhd : exists c r, (mk_open m ++ l)%string = String c r
                            /\ is_ws c = false
                            /\ Ascii.eqb c ">" = false /\ Ascii.eqb c "#" = false
                            /\ Ascii.eqb c "`" = false /\ Ascii.eqb c "~" = false
                            /\ Ascii.eqb c ":" = false).
  { destruct m as [c|core d].
    - cbn [marker_ok] in Hm.
      destruct (is_bullet_cases c Hm) as [E|[E|E]]; subst c;
        eexists; eexists; repeat split; reflexivity.
    - cbn [marker_ok] in Hm.
      apply andb_true_iff in Hm as [Hm _]. apply andb_true_iff in Hm as [Hne Hal].
      destruct d; cbn [mk_open];
        [ destruct core as [|c core'] eqn:Ec; [discriminate Hne|]
        | destruct core as [|c core'] eqn:Ec; [discriminate Hne|]
        | exists "("%char; eexists; repeat split; reflexivity ];
        (cbn [str_forallb] in Hal; apply andb_true_iff in Hal as [Hc _];
         destruct (is_alnum_not_special c Hc) as (H1 & H2 & H3 & H4 & H5 & H6);
         exists c; eexists; repeat split; assumption). }
  destruct Hhd as (c & r & Heq & Hws & Hgt & Hhash & Hbq & Htil & Hcol).
  rewrite Heq.
  repeat split.
  - cbn [drop_leading_ws]. rewrite Hws. reflexivity.
  - cbn [is_blank]. rewrite Hws. reflexivity.
  - unfold quote_prefix. cbn [drop_leading_ws]. rewrite Hws, Hgt. reflexivity.
  - unfold heading_open. cbn [drop_leading_ws]. rewrite Hws.
    cbn [count_run]. rewrite (Ascii.eqb_sym "#" c), Hhash. reflexivity.
  - unfold fence_open. cbn [drop_leading_ws]. rewrite Hws, Hbq, Htil. reflexivity.
  - unfold div_open. cbn [drop_leading_ws]. rewrite Hws.
    cbn [count_run]. rewrite (Ascii.eqb_sym ":" c), Hcol. reflexivity.
  - cbn [indent_of]. rewrite Hws. reflexivity.
Qed.

(* An opener really does classify as its own marker, with the item's line
   as the residue.  One extra hypothesis quotes and headings do not need:
   the marker plus the item's own first line must not itself look like a
   thematic break ("- - -"), since `classify` tests thematic breaks
   before list markers.  A canonical item's `cb_ok` carries this. *)
Lemma list_marker_open :
  forall m l, marker_ok m = true ->
    list_marker (mk_open m ++ l) = Some (mk_sty m, mk_core m, l).
Proof.
  intros m l Hm.
  destruct (marker_open_shape m l Hm) as (Hdrop & _ & _ & _ & _ & _ & _).
  unfold list_marker. rewrite Hdrop.
  destruct m as [c|core d].
  - cbn [marker_ok] in Hm. cbn [mk_open mk_sty mk_core].
    change (String c " " ++ l)%string with (String c (String " " l)).
    cbn beta iota. rewrite Hm. reflexivity.
  - cbn [marker_ok] in Hm.
    apply andb_true_iff in Hm as [Hm Hsty].
    apply andb_true_iff in Hm as [Hne Hal].
    cbn [mk_sty mk_core mk_open].
    (* The two suffix forms share a script: expose the core's first
       character so `marker_shape` takes its non-paren branch, then let
       `take_while_alnum_app` hand the core back whole.  The enclosed
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
      rewrite (take_while_alnum_app (String c0 core') (String "." (String " " l))
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
      rewrite (take_while_alnum_app (String c0 core') (String ")" (String " " l))
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
      rewrite (take_while_alnum_app core (String ")" (String " " l)) Hal eq_refl).
      cbn beta iota.
      change ((")" =? ")")%char) with true.
      cbn beta iota match.
      destruct (styles_of_core core LeftRightParen) eqn:Es;
        [cbn [nonempty] in Hsty; discriminate Hsty|].
      cbn [is_ws]. reflexivity.
Qed.

Lemma classify_marker_open :
  forall m l, marker_ok m = true -> is_thematic (mk_open m ++ l) = false ->
  classify (mk_open m ++ l) = KList (mk_sty m) (mk_core m) l.
Proof.
  intros m l Hm Hth.
  destruct (marker_open_shape m l Hm) as (_ & Hb & Hq & Hh & Hf & Hd & _).
  unfold classify. rewrite Hb, Hq, Hh, Hf, Hd, Hth.
  rewrite (list_marker_open m l Hm). reflexivity.
Qed.

Lemma classify_bullet_open :
  forall l, is_thematic (bullet_open ++ l) = false ->
  classify (bullet_open ++ l) = KList [SBullet "-"%char] EmptyString l.
Proof. intros l Hth. exact (classify_marker_open bullet l eq_refl Hth). Qed.

Lemma indent_of_marker_open :
  forall m l, marker_ok m = true -> indent_of (mk_open m ++ l) = 0.
Proof.
  intros m l Hm.
  destruct (marker_open_shape m l Hm) as (_ & _ & _ & _ & _ & _ & Hi).
  exact Hi.
Qed.

(* A recognized marker is at least two characters wide, which is what
   makes an item's continuation indent strictly deeper than its marker
   column.  With one bullet marker this was the literal 2; an ordered
   marker makes it a fact. *)
(* A recognized marker names at least one style, which is what lets a
   sibling's narrowing land on a nonempty set. *)
Lemma mk_sty_cons :
  forall m, marker_ok m = true -> exists s ss, mk_sty m = s :: ss.
Proof.
  intros m Hm. destruct m as [c|core d].
  - exists (SBullet c), []. reflexivity.
  - cbn [marker_ok] in Hm. apply andb_true_iff in Hm as [_ Hsty].
    cbn [mk_sty]. destruct (styles_of_core core d) as [|s ss];
      [discriminate Hsty|]. exists s, ss. reflexivity.
Qed.

Lemma lstyle_eqb_eq : forall a b, lstyle_eqb a b = true -> a = b.
Proof.
  intros [c|n d] [c'|n' d'] H; cbn [lstyle_eqb] in H; try discriminate.
  - apply Ascii.eqb_eq in H. subst c'. reflexivity.
  - apply andb_true_iff in H as [Hn Hd].
    destruct n, n'; try discriminate; destruct d, d'; try discriminate;
      reflexivity.
Qed.

Lemma mk_cont_length : forall m, String.length (mk_cont m) = mk_pad m.
Proof. intros m. unfold mk_cont. apply blanks_length. Qed.

Lemma mk_pad_pos : forall m, marker_ok m = true -> 0 < mk_pad m.
Proof.
  intros m Hm. unfold mk_pad. destruct m as [c|core d].
  - cbn [mk_open String.length]. lia.
  - cbn [marker_ok] in Hm.
    apply andb_true_iff in Hm as [Hm _]. apply andb_true_iff in Hm as [Hne _].
    destruct d; cbn [mk_open]; rewrite !length_append;
      cbn [String.length]; lia.
Qed.

(* The opener and the pad are one line's worth of text: newline-free and
   nonempty.  What the roundtrip's `lines_ok` asks of every prefix it
   puts on an item, and the only place a marker's *characters* (rather
   than its width or its styles) are constrained. *)
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

Lemma blanks_no_nl : forall n, no_nl (blanks n) = true.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [blanks no_nl]. exact IH. Qed.

Lemma mk_cont_no_nl : forall m, no_nl (mk_cont m) = true.
Proof. intros m. unfold mk_cont. apply blanks_no_nl. Qed.

Lemma is_alnum_no_nl : forall c, is_alnum c = true -> negb (Ascii.eqb c "010") = true.
Proof.
  intros c H. destruct (Ascii.eqb c "010") eqn:E; [|reflexivity].
  apply Ascii.eqb_eq in E. subst c. discriminate H.
Qed.

Lemma mk_open_no_nl : forall m, marker_ok m = true -> no_nl (mk_open m) = true.
Proof.
  intros m Hm. destruct m as [c|core d].
  - cbn [marker_ok] in Hm.
    apply is_bullet_cases in Hm as [E|[E|E]]; rewrite E; reflexivity.
  - cbn [marker_ok] in Hm.
    apply andb_true_iff in Hm as [Hm _]. apply andb_true_iff in Hm as [_ Halnum].
    assert (Hcore : no_nl core = true).
    { clear d. induction core as [|c rest IH]; [reflexivity|].
      cbn [str_forallb] in Halnum. apply andb_true_iff in Halnum as [Hc Hrest].
      cbn [no_nl]. rewrite (is_alnum_no_nl c Hc). cbn [andb]. apply IH, Hrest. }
    destruct d; cbn [mk_open]; rewrite ?no_nl_append, Hcore; reflexivity.
Qed.

Lemma indent_of_bullet_open : forall l, indent_of (bullet_open ++ l) = 0.
Proof. reflexivity. Qed.
