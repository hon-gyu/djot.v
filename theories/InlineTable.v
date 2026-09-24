(* ai-disclosure: autonomous *)

(* The delimiter table: the characters the scanner claims, the table of
   delimiter rows as a parameter, its admissibility condition, and the
   checked row updates.  The class `dtable` packages an admissible table. *)

From Stdlib Require Import String Ascii List Bool Lia Wf_nat Arith.
From DjotV Require Import Config Strings Ast Attributes.
Import ListNotations.

Local Open Scope string_scope.

(*
Escapes
=======

A backslash escape is not a construct: `\*` and a bare `*` in a position
where nothing opens both parse to `Str "*"`, so the AST cannot tell them
apart and `cinline` gains no constructor.  What an escape is, is the
*spelling* a `CIStr` needs so that its text comes back unchanged, which
makes this a pair of string functions and one theorem relating them. *)

(* The ASCII punctuation blocks: the set a backslash may escape, wider
   than the set that ever needs escaping. *)
Definition is_punct (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((Nat.leb 33 n && Nat.leb n 47) || (Nat.leb 58 n && Nat.leb n 64)
   || (Nat.leb 91 n && Nat.leb n 96) || (Nat.leb 123 n && Nat.leb n 126))%bool.

(* Both are what an escape dispatches on, and they do not overlap: every
   punctuation range starts at 33 and every whitespace byte is below it. *)
Lemma is_punct_not_ws : forall c, is_punct c = true -> is_ws c = false.
Proof.
  intros c H. unfold is_ws.
  destruct (Ascii.eqb c " "%char) eqn:E1;
    [apply Ascii.eqb_eq in E1; subst c; vm_compute in H; discriminate|].
  destruct (Ascii.eqb c "009"%char) eqn:E2;
    [apply Ascii.eqb_eq in E2; subst c; vm_compute in H; discriminate|].
  destruct (Ascii.eqb c "013"%char) eqn:E3;
    [apply Ascii.eqb_eq in E3; subst c; vm_compute in H; discriminate|].
  reflexivity.
Qed.

Definition tick : ascii := "`"%char.
Definition is_tick (c : ascii) : bool := Ascii.eqb c tick.

(* The escape character (`Attributes.bslash`), as opposed to the set of
   characters that need escaping.  The scanner must test *this* to detect a pending
   escape: `needs_escape` contains the backtick, and testing it here
   would make a bare backtick set the escape flag instead of opening a
   verbatim span. *)
Definition is_bslash (c : ascii) : bool := Ascii.eqb c bslash.

Local Lemma is_tick_bslash : is_tick bslash = false.
Proof. reflexivity. Qed.

Lemma is_bslash_bslash : is_bslash bslash = true.
Proof. reflexivity. Qed.

(* The braces.  `{` forces a delimiter open or begins an attribute spec;
   `}` forces one closed or ends a spec. *)
Definition lbrace : ascii := "{"%char.
Definition rbrace : ascii := "}"%char.

Definition one (c : ascii) : string := String c EmptyString.

(* The math prefix.  Reserved rather than a table row: it is not a
   delimiter, it changes what the verbatim after it means. *)
Definition dollar : ascii := "$"%char.

(* The quote characters and the hyphen, which `dopens_after` tests. *)
Definition sqchar : ascii := "'"%char.
Definition dqchar : ascii := """"%char.
Definition hyphen : ascii := "-"%char.

(* The ellipsis character.  Not a delimiter either: three periods are one
   character of output, and any other run is text. *)
Definition period : ascii := "."%char.

(* The bracket family.  `!`, `[` and `]` are dispatched in text mode and
   claimed by `needs_escape`; the parens are dispatched only inside a
   destination and claimed by `needs_escape_dest`. *)
Definition bang : ascii := "!"%char.
Definition lbrack : ascii := "["%char.
Definition rbrack : ascii := "]"%char.
Definition lparen : ascii := "("%char.
Definition rparen : ascii := ")"%char.

(* A wikilink's alias separator.  Not dispatched in text mode. *)
Definition vbar : ascii := "|"%char.

(* The footnote marker.  It is the superscript row's character, and only
   a `^` immediately inside a `[` marks a note, so the table may keep
   claiming it.  `[^` is spelled with this rather than `dchar DSuper`, so
   that a table moving the superscript row does not move the footnote
   marker. *)
Definition hat : ascii := "^"%char.

(* An autolink's brackets.  Only `<` is reserved: the scanner dispatches
   on it in text mode, while `>` is text unless a candidate is open. *)
Definition lt : ascii := "<"%char.
Definition gt : ascii := ">"%char.

(* `ibreak` writes a break into a destination as `nl`, and the
   reconstruction reads it back byte by byte, so the two are the same
   character. *)
Definition nl_char : ascii := "010"%char.

(* The characters the scanner claims for itself, before it consults the
   table at all: the escape, the verbatim fence, the two braces that
   force a delimiter, the three the bracket family dispatches on, the
   math prefix, the period, symbol colon, and the autolink's `<`.
   A row may not use one of these: `ilead` would never reach the lookup.
   `dconfig_ok` checks this condition. *)
Definition dreserved (c : ascii) : bool :=
  (is_bslash c || is_tick c
   || Ascii.eqb c lbrace || Ascii.eqb c rbrace
   || Ascii.eqb c lbrack || Ascii.eqb c rbrack
   || Ascii.eqb c bang || Ascii.eqb c dollar
   || Ascii.eqb c lt || Ascii.eqb c ":"%char
   (* the period is not a delimiter and opens nothing, but the scanner
      dispatches on it for the ellipsis, which is enough to reserve it:
      no row may be spelled with it, and a canonical `Str` holding one
      escapes it so that `...` cannot come back as an ellipsis. *)
   || Ascii.eqb c period)%bool.

(*
The delimiter table
-------------------

One row per delimiter character; djot has nine.  A table rather than
nine branches, so that the scanner keeps one recursive call and decides
what to do by lookup: with a recursive call per branch, a general lemma
about the scanner becomes unprovable while every `Compute` stays fast
(`.project/project-engineering-lessons.md`).

The two quote rows also carry smart quotes, and the hyphen smart dashes;
those constructs are separate from the rows. *)

Inductive dstyle : Type :=
  | DEmph | DStrong | DSuper | DSub | DMark | DInsert | DDelete
  (* The smart quotes.  Rows like the rest, except that an unmatched one
     is a curly quote rather than literal text, and which curly quote
     depends on the markers around it. *)
  | DSQuote | DDQuote.

(* How a row may be written.  `DBraced`: only as `{x ... x}`, because the
   bare character is too common in prose to claim.  `DBare`: bare, with
   the braces an optional override.  `DOff` removes the row, so which
   containers exist is a setting rather than a fixed list. *)
Inductive dsyntax : Type :=
  | DOff | DBraced | DBare
  (* Bare, but a bare opener only where an apostrophe cannot be meant: at
     the start of the line, or after whitespace, a quote character, a
     hyphen, an open paren or an open bracket.  So `can't` is an
     apostrophe and not an open quote. *)
  | DBareAfterBreak.

(* What a token that opens nothing and closes nothing leaves behind.
   Every row but the quotes leaves its own source text.  A quote leaves a
   curly character, and which one depends on the markers around it: an
   open marker chooses the left form, a close marker the right one, and
   with neither the row's default applies. *)
Inductive ddecay : Type :=
  | DDSelf
  | DDPair (left_by_default : bool) (left right : string).

(* The delimiter table, as a parameter.  Every row carries the character
   it is written with and how it may be written; a configuration is a
   choice of both for each row, and djot is one such choice.  Reading the
   character out of the table rather than fixing it per constructor is
   what lets emphasis and strong swap characters. *)
Record dconfig : Type := DConfig {
  dc_char : dstyle -> ascii;
  dc_width : dstyle -> nat;
  dc_syntax : dstyle -> dsyntax;
  dc_decay : dstyle -> ddecay;
  dc_smart_typography : bool;
  dc_raw_inline : bool;
  (* Does a `$` or `$$` before a verbatim make the span math?  When false the
     dollars are ordinary text and the verbatim is ordinary code. *)
  dc_math : bool;
  (* Do `{...}` specs attach attributes, and does `]{`  open a span?  When
     false both are literal text.  The braced delimiter rows are a separate
     decision: they are reached from the same `{` but are rows in this very
     table. *)
  dc_attrs : bool;
  (* Does `[^label]` make a footnote reference?  The other half of the
     capability is `Step.bfootnotes`; `Profile.with_footnotes` moves both. *)
  dc_footnotes : bool;
  (* Does `[[target|alias]]` make a wikilink?  Off in djot's own table. *)
  dc_wikilinks : bool
}.

Definition djot_dchar (k : dstyle) : ascii :=
  match k with
  | DEmph => "_"%char | DStrong => "*"%char
  | DSuper => "^"%char | DSub => "~"%char
  | DMark => "="%char | DInsert => "+"%char
  | DDelete => "-"%char
  | DSQuote => "'"%char | DDQuote => """"%char
  end.

Definition djot_dsyntax (k : dstyle) : dsyntax :=
  match k with
  | DMark | DInsert | DDelete => DBraced
  | DSQuote => DBareAfterBreak
  | _ => DBare
  end.

(* The curly quotes, as UTF-8.  Strings here are bytes, so each is three
   of them; nothing downstream looks inside. *)
Definition lsquo : string :=
  String "226"%char (String "128"%char (String "152"%char EmptyString)).
Definition rsquo : string :=
  String "226"%char (String "128"%char (String "153"%char EmptyString)).
Definition ldquo : string :=
  String "226"%char (String "128"%char (String "156"%char EmptyString)).
Definition rdquo : string :=
  String "226"%char (String "128"%char (String "157"%char EmptyString)).

(* An unmatched single quote is an apostrophe (the right form), while an
   unmatched double quote opens. *)
Definition djot_ddecay (k : dstyle) : ddecay :=
  match k with
  | DSQuote => DDPair false lsquo rsquo
  | DDQuote => DDPair true ldquo rdquo
  | _ => DDSelf
  end.

(* Every djot row is one character wide.  A wider row is what spells a
   doubled delimiter, and because a character belongs to exactly one row
   its width is fixed rather than negotiated: a run of the character is
   cut into tokens of that width and any remainder is literal. *)
Definition djot_dwidth (_ : dstyle) : nat := 1.

Definition djot_config : dconfig :=
  DConfig djot_dchar djot_dwidth djot_dsyntax djot_ddecay true true true true
    true false.

Fixpoint chars (c : ascii) (n : nat) : string :=
  match n with O => EmptyString | S m => String c (chars c m) end.

Local Definition dstyles : list dstyle :=
  [DEmph; DStrong; DSuper; DSub; DMark; DInsert; DDelete;
   DSQuote; DDQuote].

Definition dstyle_eq (a b : dstyle) : bool :=
  match a, b with
  | DEmph, DEmph | DStrong, DStrong | DSuper, DSuper
  | DSub, DSub | DMark, DMark | DInsert, DInsert
  | DDelete, DDelete | DSQuote, DSQuote | DDQuote, DDQuote => true
  | _, _ => false
  end.

Local Lemma dstyle_eq_true : forall a b, dstyle_eq a b = true -> a = b.
Proof. intros [] []; first [reflexivity | discriminate]. Qed.

Definition denabled (C : dconfig) (k : dstyle) : bool :=
  match dc_syntax C k with DOff => false | _ => true end.

Local Lemma dstyles_complete : forall k, In k dstyles.
Proof. intros []; cbn; tauto. Qed.

(* Look a character up in the table rather than repeating it, which is
   what makes `dstyle_of_dchar` below a fact about the search rather than
   a coincidence between two spellings.  A row switched off is not found,
   so `DOff` removes the character from the scanner entirely. *)
Definition dstyle_at (C : dconfig) (c : ascii) : option dstyle :=
  find (fun k => denabled C k && Ascii.eqb (dc_char C k) c)%bool dstyles.

(* A row's decay leaves something behind, so no token vanishes. *)
Definition ddecay_ok (d : ddecay) : bool :=
  match d with
  | DDSelf => true
  | DDPair _ l r => (nonempty_str l && nonempty_str r)%bool
  end.

(* Is the row read from the source directly, rather than from inside a
   `{...}` pair?  The hyphen condition below is asked of the bare
   spellings only, because a braced row is reached from the brace and
   never from `ilead`. *)
Definition dsyntax_bare (s : dsyntax) : bool :=
  match s with DBare | DBareAfterBreak => true | _ => false end.

(* An admissible table: what the scanner and the renderer assume of it.
   Decidable, so a configuration is checked rather than trusted.

   1. Unambiguous (`dconfig_distinct`): no two enabled rows claim the
      same character.
   2. Written: a row has nonzero width, so its delimiter is nonempty.
   3. Escapable: a row's character is punctuation, so a backslash can
      escape it (`needs_escape_punct`).
   4. Free: a row's character is not `dreserved`.  `ilead` dispatches the
      reserved characters before it consults the table, so such a row
      would never be reached.
   5. Leaves something: an unmatched token's decay is nonempty.
   6. A bare row is not spelled with the hyphen.

   Conditions 2 to 6 are asked of every row, enabled or not.  A disabled
   row must still be spelled admissibly; in exchange, "has a token" and
   "is not a backtick" hold unconditionally rather than under "this row
   exists", which only `dstyle_of` needs. *)
Definition drow_ok (C : dconfig) (k : dstyle) : bool :=
  (negb (Nat.eqb (dc_width C k) 0)
   && is_punct (dc_char C k)
   && negb (dreserved (dc_char C k))
   && ddecay_ok (dc_decay C k)
   && negb (dsyntax_bare (dc_syntax C k) && Ascii.eqb (dc_char C k) hyphen))%bool.

Local Definition dconfig_distinct (C : dconfig) : bool :=
  forallb
    (fun k => forallb
       (fun k' => implb (denabled C k && denabled C k'
                         && Ascii.eqb (dc_char C k) (dc_char C k'))%bool
                        (dstyle_eq k k'))
       dstyles)
    dstyles.

Local Definition dconfig_rows_ok (C : dconfig) : bool :=
  forallb (drow_ok C) dstyles.

Definition dconfig_ok (C : dconfig) : bool :=
  (dconfig_distinct C && dconfig_rows_ok C)%bool.

Definition delimiter_admissible : invariant dconfig :=
  fun C => dconfig_ok C = true.

(* A replacement row, checked for compatibility as a unit. *)
Record dentry : Type := DEntry {
  de_char : ascii;
  de_width : nat;
  de_syntax : dsyntax;
  de_decay : ddecay
}.

Local Definition dentry_of (C : dconfig) (k : dstyle) : dentry :=
  DEntry (dc_char C k) (dc_width C k) (dc_syntax C k) (dc_decay C k).

Definition update_drow
  (target : dstyle) (e : dentry) (C : dconfig) : dconfig :=
  DConfig
    (fun k => if dstyle_eq k target then de_char e else dc_char C k)
    (fun k => if dstyle_eq k target then de_width e else dc_width C k)
    (fun k => if dstyle_eq k target then de_syntax e else dc_syntax C k)
    (fun k => if dstyle_eq k target then de_decay e else dc_decay C k)
    (dc_smart_typography C) (dc_raw_inline C) (dc_math C) (dc_attrs C)
    (dc_footnotes C) (dc_wikilinks C).

(* Smart dashes and ellipses are scanner capabilities rather than delimiter
   rows.  This field-local knob leaves every row unchanged. *)
Definition with_smart_typography (enabled : bool) (C : dconfig) : dconfig :=
  DConfig (dc_char C) (dc_width C) (dc_syntax C) (dc_decay C) enabled
    (dc_raw_inline C) (dc_math C) (dc_attrs C) (dc_footnotes C)
    (dc_wikilinks C).

Theorem with_smart_typography_preserves_admissible :
  forall enabled, preserves (with_smart_typography enabled) delimiter_admissible.
Proof. intros enabled C H. exact H. Qed.

Definition with_raw_inline (enabled : bool) (C : dconfig) : dconfig :=
  DConfig (dc_char C) (dc_width C) (dc_syntax C) (dc_decay C)
    (dc_smart_typography C) enabled (dc_math C) (dc_attrs C)
    (dc_footnotes C) (dc_wikilinks C).

Theorem with_raw_inline_preserves_admissible :
  forall enabled, preserves (with_raw_inline enabled) delimiter_admissible.
Proof. intros enabled C H. exact H. Qed.

(* Math is the dollar prefix on a verbatim, not a row: it has its own
   character, which no table may claim, and its own scanner state. *)
Definition with_math (enabled : bool) (C : dconfig) : dconfig :=
  DConfig (dc_char C) (dc_width C) (dc_syntax C) (dc_decay C)
    (dc_smart_typography C) (dc_raw_inline C) enabled (dc_attrs C)
    (dc_footnotes C) (dc_wikilinks C).

Theorem with_math_preserves_admissible :
  forall enabled, preserves (with_math enabled) delimiter_admissible.
Proof. intros enabled C H. exact H. Qed.

(* Inline attributes and spans.  The rows keep their own switches: a table
   whose delete row is on still reads `{-` as a delete opener here. *)
Definition with_inline_attrs (enabled : bool) (C : dconfig) : dconfig :=
  DConfig (dc_char C) (dc_width C) (dc_syntax C) (dc_decay C)
    (dc_smart_typography C) (dc_raw_inline C) (dc_math C) enabled
    (dc_footnotes C) (dc_wikilinks C).

Theorem with_inline_attrs_preserves_admissible :
  forall enabled, preserves (with_inline_attrs enabled) delimiter_admissible.
Proof. intros enabled C H. exact H. Qed.

(* Exported, but `Profile.with_footnotes` is what a caller should reach
   for: this half alone leaves definitions nothing can reference. *)
Definition with_inline_footnotes (enabled : bool) (C : dconfig) : dconfig :=
  DConfig (dc_char C) (dc_width C) (dc_syntax C) (dc_decay C)
    (dc_smart_typography C) (dc_raw_inline C) (dc_math C) (dc_attrs C)
    enabled (dc_wikilinks C).

Theorem with_inline_footnotes_preserves_admissible :
  forall enabled,
    preserves (with_inline_footnotes enabled) delimiter_admissible.
Proof. intros enabled C H. exact H. Qed.

(* Wikilinks are an inline capability only: no block construct takes part. *)
Definition with_wikilinks (enabled : bool) (C : dconfig) : dconfig :=
  DConfig (dc_char C) (dc_width C) (dc_syntax C) (dc_decay C)
    (dc_smart_typography C) (dc_raw_inline C) (dc_math C) (dc_attrs C)
    (dc_footnotes C) enabled.

Theorem with_wikilinks_preserves_admissible :
  forall enabled, preserves (with_wikilinks enabled) delimiter_admissible.
Proof. intros enabled C H. exact H. Qed.

Local Definition drow_trigger_compatible
  (C : dconfig) (target : dstyle) (e : dentry) : bool :=
  let C' := update_drow target e C in
  forallb
    (fun k =>
       implb
         (negb (dstyle_eq k target)
          && denabled C' k && denabled C' target)%bool
         (negb (Ascii.eqb (dc_char C' k) (dc_char C' target))))
    dstyles.

(* The replacement must be a valid row, and its enabled character must
   differ from every other enabled row's.  Everything else is inherited
   from an admissible input table. *)
Definition drow_update_compatible
  (C : dconfig) (target : dstyle) (e : dentry) : bool :=
  (drow_ok (update_drow target e C) target
   && drow_trigger_compatible C target e)%bool.

Local Lemma denabled_update_drow_other :
  forall C target e k,
    dstyle_eq k target = false ->
    denabled (update_drow target e C) k = denabled C k.
Proof.
  intros C target e k H. unfold update_drow, denabled. cbn.
  rewrite H. reflexivity.
Qed.

Local Lemma denabled_update_drow_target :
  forall C target e,
    denabled (update_drow target e C) target =
    match de_syntax e with DOff => false | _ => true end.
Proof.
  intros C [] e; unfold denabled, update_drow; cbn;
    destruct (de_syntax e); reflexivity.
Qed.

Local Lemma dchar_update_drow_other :
  forall C target e k,
    dstyle_eq k target = false ->
    dc_char (update_drow target e C) k = dc_char C k.
Proof.
  intros C target e k H. unfold update_drow. cbn.
  rewrite H. reflexivity.
Qed.

Local Lemma dchar_update_drow_target :
  forall C target e,
    dc_char (update_drow target e C) target = de_char e.
Proof. intros C [] e; reflexivity. Qed.

Local Lemma no_trigger_collision :
  forall a b same conclusion,
    implb (a && b) (negb same) = true ->
    implb (a && b && same) conclusion = true.
Proof. intros [] [] [] []; reflexivity || discriminate. Qed.

Local Lemma no_trigger_collision_sym :
  forall a b same conclusion,
    implb (a && b) (negb same) = true ->
    implb (b && a && same) conclusion = true.
Proof. intros [] [] [] []; reflexivity || discriminate. Qed.

Local Lemma dconfig_distinct_update_drow :
  forall C target e,
    dconfig_distinct C = true ->
    drow_trigger_compatible C target e = true ->
    dconfig_distinct (update_drow target e C) = true.
Proof.
  intros C target e Hbase Hlocal.
  unfold dconfig_distinct in Hbase |- *.
  rewrite forallb_forall in Hbase |- *.
  unfold drow_trigger_compatible in Hlocal.
  rewrite forallb_forall in Hlocal.
  intros k Hk. specialize (Hbase k Hk).
  rewrite forallb_forall in Hbase |- *.
  intros k' Hk'. specialize (Hbase k' Hk').
  pose proof (Hlocal k Hk) as Hlocal_k.
  pose proof (Hlocal k' Hk') as Hlocal_k'.
  unfold implb in Hbase, Hlocal_k, Hlocal_k' |- *.
  destruct (dstyle_eq k target) eqn:Ek.
  - apply dstyle_eq_true in Ek. subst k.
    destruct (dstyle_eq k' target) eqn:Ek'.
    + apply dstyle_eq_true in Ek'. subst k'.
      rewrite !denabled_update_drow_target, !dchar_update_drow_target,
        Ascii.eqb_refl.
      assert (Etarget : dstyle_eq target target = true)
        by (destruct target; reflexivity).
      rewrite Etarget. destruct (de_syntax e); reflexivity.
    + rewrite denabled_update_drow_other in Hlocal_k' by exact Ek'.
      rewrite denabled_update_drow_target in Hlocal_k'.
      rewrite dchar_update_drow_other in Hlocal_k' by exact Ek'.
      rewrite dchar_update_drow_target in Hlocal_k'.
      rewrite denabled_update_drow_target,
        denabled_update_drow_other by exact Ek'.
      rewrite dchar_update_drow_target,
        dchar_update_drow_other by exact Ek'.
      rewrite Ascii.eqb_sym.
      exact (no_trigger_collision_sym _ _ _ _ Hlocal_k').
  - destruct (dstyle_eq k' target) eqn:Ek'.
    + apply dstyle_eq_true in Ek'. subst k'.
      rewrite denabled_update_drow_other in Hlocal_k by exact Ek.
      rewrite denabled_update_drow_target in Hlocal_k.
      rewrite dchar_update_drow_other in Hlocal_k by exact Ek.
      rewrite dchar_update_drow_target in Hlocal_k.
      rewrite denabled_update_drow_other by exact Ek.
      rewrite denabled_update_drow_target.
      rewrite dchar_update_drow_other by exact Ek.
      rewrite dchar_update_drow_target.
      exact (no_trigger_collision _ _ _ _ Hlocal_k).
    + rewrite !denabled_update_drow_other by assumption.
      rewrite !dchar_update_drow_other by assumption.
      exact Hbase.
Qed.

Local Lemma drow_ok_update_drow_other :
  forall C target e k,
    dstyle_eq k target = false ->
    drow_ok (update_drow target e C) k = drow_ok C k.
Proof.
  intros C target e k H. unfold drow_ok, update_drow. cbn.
  rewrite H. reflexivity.
Qed.

Local Lemma drow_ok_update_drow_target :
  forall C target e,
    drow_ok (update_drow target e C) target =
    (negb (Nat.eqb (de_width e) 0) && is_punct (de_char e)
     && negb (dreserved (de_char e)) && ddecay_ok (de_decay e)
     && negb (dsyntax_bare (de_syntax e) && Ascii.eqb (de_char e) hyphen))%bool.
Proof. intros C [] e; reflexivity. Qed.

Theorem update_drow_preserves_admissible :
  forall target e,
    preserves_when
      (fun C => drow_update_compatible C target e = true)
      (update_drow target e)
      delimiter_admissible.
Proof.
  intros target e C Hcompat HC.
  unfold drow_update_compatible in Hcompat.
  apply andb_true_iff in Hcompat as [Htarget Htrigger].
  unfold delimiter_admissible, dconfig_ok in HC |- *.
  apply andb_true_iff in HC as [Hdistinct Hrows].
  apply andb_true_iff. split.
  - exact (dconfig_distinct_update_drow C target e Hdistinct Htrigger).
  - unfold dconfig_rows_ok in Hrows |- *.
    rewrite forallb_forall in Hrows |- *.
    intros k Hk.
    destruct (dstyle_eq k target) eqn:Hsame.
    + apply dstyle_eq_true in Hsame. subst k. exact Htarget.
    + rewrite drow_ok_update_drow_other by exact Hsame.
      exact (Hrows k Hk).
Qed.

(* Markdown's `**` spelling for strong, as one checked row update, with
   djot's semantics everywhere else.  A single `*` is literal because the
   row has one fixed width: there is no run-length disambiguation or
   flanking rule. *)
Definition markdown_strong_entry : dentry :=
  DEntry "*"%char 2 DBare DDSelf.

(* The Markdown-like table is djot's with that one row changed.  Every
   other capability stays on: the profile extends djot rather than
   removing from it, and each capability remains a knob of its own. *)
Definition markdown_like_config : dconfig :=
  update_drow DStrong markdown_strong_entry djot_config.

(* Executable witnesses for each part of the compatibility boundary. *)
Example markdown_strong_compatible :
  drow_update_compatible djot_config DStrong markdown_strong_entry = true.
Proof. vm_compute. reflexivity. Qed.

Example clashing_strong_incompatible :
  drow_update_compatible djot_config DStrong
    (DEntry "_"%char 2 DBare DDSelf) = false.
Proof. vm_compute. reflexivity. Qed.

Example reserved_strong_incompatible :
  drow_update_compatible djot_config DStrong
    (DEntry bslash 2 DBare DDSelf) = false.
Proof. vm_compute. reflexivity. Qed.

Example empty_strong_incompatible :
  drow_update_compatible djot_config DStrong
    (DEntry "*"%char 0 DBare DDSelf) = false.
Proof. vm_compute. reflexivity. Qed.

(* The hyphen condition.  `ilead` claims a hyphen before it consults the
   table, so a bare row spelled `-` would be read only in its braced
   spelling: `{-x-}` marks the span and `-x-` is a smart dash.  A row that
   does not do what its syntax says is not admissible. *)
Example bare_hyphen_incompatible :
  drow_update_compatible djot_config DEmph
    (DEntry hyphen 1 DBare DDSelf) = false.
Proof. vm_compute. reflexivity. Qed.

(* A braced row is reached from the brace, so the condition does not
   touch it.  djot's own delete row is braced. *)
Example braced_hyphen_row_ok :
  drow_ok (update_drow DEmph (DEntry hyphen 1 DBraced DDSelf) djot_config)
    DEmph = true.
Proof. vm_compute. reflexivity. Qed.

(* Disabling a row changes only its syntax field; the row stays valid
   while switched off. *)
Local Definition disable_entry (C : dconfig) (target : dstyle) : dentry :=
  DEntry (dc_char C target) (dc_width C target) DOff (dc_decay C target).

Definition disable_row (target : dstyle) (C : dconfig) : dconfig :=
  update_drow target (disable_entry C target) C.

(* Disabling can only make a row more admissible: it keeps every field
   but the syntax, and a switched-off row is not a bare one, so the
   hyphen condition is discharged rather than carried. *)
Local Lemma drow_ok_disable_row :
  forall C target k,
    drow_ok C k = true -> drow_ok (disable_row target C) k = true.
Proof.
  intros C target k H. destruct target, k; cbn - [dreserved is_punct] in H |- *;
    try exact H;
    repeat (apply andb_true_iff in H as [H ?]);
    repeat (apply andb_true_iff; split); try assumption; reflexivity.
Qed.

Local Lemma disable_row_compatible :
  forall C target,
    delimiter_admissible C ->
    drow_update_compatible C target (disable_entry C target) = true.
Proof.
  intros C target H.
  unfold drow_update_compatible.
  change ((drow_ok (disable_row target C) target
           && drow_trigger_compatible C target
                (disable_entry C target))%bool = true).
  apply andb_true_iff. split.
  - apply drow_ok_disable_row.
    unfold delimiter_admissible, dconfig_ok in H.
    apply andb_true_iff in H as [_ Hrows].
    unfold dconfig_rows_ok in Hrows. rewrite forallb_forall in Hrows.
    exact (Hrows target (dstyles_complete target)).
  - unfold drow_trigger_compatible.
    rewrite forallb_forall. intros k Hk.
    unfold implb. rewrite denabled_update_drow_target.
    unfold disable_entry. cbn. rewrite andb_false_r. reflexivity.
Qed.

Theorem disable_row_preserves_admissible :
  forall target, preserves (disable_row target) delimiter_admissible.
Proof.
  intros target C H.
  apply (update_drow_preserves_admissible target (disable_entry C target) C).
  - exact (disable_row_compatible C target H).
  - exact H.
Qed.

(* Switch off several rows by composing the same proved row operation.
   The order does not affect behaviour. *)
Fixpoint disable_rows (targets : list dstyle) (C : dconfig) : dconfig :=
  match targets with
  | [] => C
  | target :: rest => disable_rows rest (disable_row target C)
  end.

Theorem disable_rows_preserves_admissible :
  forall targets, preserves (disable_rows targets) delimiter_admissible.
Proof.
  induction targets as [|target rest IH]; intros C H; cbn.
  - exact H.
  - apply IH. exact (disable_row_preserves_admissible target C H).
Qed.

Local Lemma dconfig_ok_distinct :
  forall C, dconfig_ok C = true -> dconfig_distinct C = true.
Proof. intros C H. apply andb_true_iff in H as [H _]. exact H. Qed.

(* What the row conditions buy, one row at a time. *)
Lemma dconfig_ok_row :
  forall C k, dconfig_ok C = true -> drow_ok C k = true.
Proof.
  intros C k H. apply andb_true_iff in H as [_ H].
  unfold dconfig_rows_ok in H. rewrite forallb_forall in H.
  exact (H k (dstyles_complete k)).
Qed.

(* What the side condition buys: a row's own character finds that row
   again. *)
Lemma dstyle_at_dchar :
  forall C k,
    dconfig_ok C = true -> denabled C k = true ->
    dstyle_at C (dc_char C k) = Some k.
Proof.
  intros C k Hok Hen. unfold dstyle_at.
  destruct (find (fun k' => denabled C k' && Ascii.eqb (dc_char C k') (dc_char C k))%bool
              dstyles) as [k'|] eqn:E.
  - apply find_some in E as [Hin Hp].
    apply andb_true_iff in Hp as [Hen' Hc].
    f_equal. symmetry. apply dstyle_eq_true.
    apply dconfig_ok_distinct in Hok.
    unfold dconfig_distinct in Hok. rewrite forallb_forall in Hok.
    specialize (Hok k (dstyles_complete k)). rewrite forallb_forall in Hok.
    specialize (Hok k' (dstyles_complete k')).
    rewrite Hen, Hen' in Hok. apply Ascii.eqb_eq in Hc. rewrite Hc in Hok.
    rewrite Ascii.eqb_refl in Hok. exact Hok.
  - exfalso. eapply find_none in E; [|apply (dstyles_complete k)].
    rewrite Hen, Ascii.eqb_refl in E. discriminate.
Qed.

(* The node a closed bracket builds: a lookup on image-ness, not a branch
   in the scanner. *)
Definition bnode (image : bool) (ns : inlines) (tgt : target) : inline :=
  if image then Image ns tgt else Link ns tgt.

Definition dnode (k : dstyle) (ns : inlines) : inline :=
  match k with
  | DEmph => Emph ns | DStrong => Strong ns
  | DSuper => Superscript ns | DSub => Subscript ns
  | DMark => Highlight ns | DInsert => Insert ns
  | DDelete => Delete ns
  | DSQuote => Quoted SingleQuotes ns | DDQuote => Quoted DoubleQuotes ns
  end.

(* A wikilink's display text: the alias if there is one, else the target. *)
Definition wiki_display (target : string) (alias : option string) : string :=
  match alias with Some d => d | None => target end.

(* The ordinary link a wikilink renders as. *)
Definition wiki_desugar (embed : bool) (target : string) (alias : option string)
  : inline :=
  let ils := [mk (Str (wiki_display target alias))] in
  if embed then Image ils (Direct target) else Link ils (Direct target).

(* The label an empty reference (`[text][]`) supplies: the string content
   of the first bracket.  Computed in the inline layer, so classification
   does not consult either reference map. *)
Fixpoint reference_text (il : inline) : string :=
  let go :=
    fix go (ns : inlines) : string :=
      match ns with
      | [] => EmptyString
      | n :: rest => reference_text (node_contents n) ++ go rest
      end in
  match il with
  | Str s | Verbatim s | Math _ s | RawInline _ s => s
  | SoftBreak | HardBreak => nl
  | Emph ns | Strong ns | Highlight ns | Insert ns | Delete ns
  | Superscript ns | Subscript ns | Span ns | Link ns _ | Image ns _
  | Quoted _ ns => go ns
  | Wikilink _ t al => wiki_display t al
  | FootnoteReference _ | Symbol _ | UrlLink _ | EmailLink _
  | NonBreakingSpace => EmptyString
  end.

Definition reference_inlines_text (ns : inlines) : string :=
  String.concat EmptyString (map (fun n => reference_text (node_contents n)) ns).

(* Djot's table is admissible, checked rather than assumed. *)
Example djot_config_ok : dconfig_ok djot_config = true.
Proof. vm_compute. reflexivity. Qed.

Example markdown_like_config_ok : dconfig_ok markdown_like_config = true.
Proof. vm_compute. reflexivity. Qed.

(* And a table that is not admissible, so the condition is known to have
   teeth: giving strong the emphasis character makes `_` ambiguous. *)
Example clashing_config_not_ok :
  dconfig_ok (DConfig (fun k => match k with
                                | DStrong => "_"%char | _ => djot_dchar k
                                end)
                      djot_dwidth djot_dsyntax djot_ddecay true true true
                      true true false)
  = false.
Proof. vm_compute. reflexivity. Qed.

(* Switching a row off frees its character, so the clash disappears
   without changing any other row. *)
Example clashing_config_ok_when_off :
  dconfig_ok (DConfig (fun k => match k with
                                | DStrong => "_"%char | _ => djot_dchar k
                                end)
                      djot_dwidth
                      (fun k => match k with
                                | DEmph => DOff | _ => djot_dsyntax k
                                end)
                      djot_ddecay true true true true true false) = true.
Proof. vm_compute. reflexivity. Qed.


(* The table in force: an admissible configuration together with its
   proof.  Everything below is stated for an arbitrary one, so the
   roundtrip theorems are about the family rather than about djot.

   A class, so that the argument stays implicit.  Another table is named
   explicitly (`@parse_inline_line markdown_like_table`). *)
Class dtable : Type := DTable {
  cfg : dconfig;
  cfg_ok : dconfig_ok cfg = true
}.
