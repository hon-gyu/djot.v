(* ai-disclosure: autonomous *)

(** * Single-pass inline parsing

   The inline layer is the parser's pass over a paragraph's text, and the
   canonical (renderable) view it inverts.

   The same two-sided shape as the block layer, one level down.  There,
   `Line.v` classifies a line and `Step.v` folds lines into blocks, while
   `Render.v`'s `cblock` describes the parser's image by the source data
   that determines it.  Here `para_inlines` is the pass, `cinline` is the
   image, and the two meet in `para_inlines_ci_para`.

   The pass recognizes escapes, verbatim spans, and the delimiter table
   in `.project/260811.inline-parser.md`.  Brackets remain the next
   extension point for the state and canonical view.

   The scan threads through line breaks rather than restarting at each
   one, because a span may cross a break.  The canonical view stays
   line-local, `cblock` describing a paragraph as a list of lines, and
   `iscan_cis_closed` is what reconciles the two: a canonical line always
   leaves the scan owing nothing to the next.

   Parser and renderer share the file because at this size a split would
   be three files of twenty lines.  It splits the way the block parser
   did once a side outgrows the other. *)

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

(* djot.js `pattPunctuation` (inline.ts:84): the ASCII punctuation
   blocks.  This is the set a backslash may escape, and it is deliberately
   wider than the set that ever *needs* escaping. *)
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

(* The characters a `CIStr` must escape to survive reparsing.  Today only
   the backslash: nothing else has inline meaning yet.  Every construct
   that claims a delimiter character adds it here, and the two
   obligations below are what it has to keep true.

   The alternative, escaping every punctuation character unconditionally,
   would keep this constant and needs no obligation, at the cost of
   rendering `a, b` as `a\, b`.  djot.js escapes selectively (it renders
   `\,` back as a bare `,`), and matching that costs only the two lemmas. *)
Definition tick : ascii := "`"%char.
Definition is_tick (c : ascii) : bool := Ascii.eqb c tick.

(* The escape character itself, as opposed to the set of characters that
   need escaping.  The scanner must test *this* to detect a pending
   escape: `needs_escape` contains the backtick, and testing it here
   would make a bare backtick set the escape flag instead of opening a
   verbatim span. *)
Definition bslash : ascii := "\"%char.
Definition is_bslash (c : ascii) : bool := Ascii.eqb c bslash.

Lemma is_tick_bslash : is_tick bslash = false.
Proof. reflexivity. Qed.

Lemma is_bslash_bslash : is_bslash bslash = true.
Proof. reflexivity. Qed.

(* The braces that force a delimiter open or closed.  `{` also begins an
   attribute, which is not implemented; until it is, a `{` that is not an
   open marker is literal text, matching what the scanner did before. *)
Definition lbrace : ascii := "{"%char.
Definition rbrace : ascii := "}"%char.

(* The bracket family's characters.  The three the scanner dispatches on
   in text mode -- `!`, `[`, `]` -- are in `needs_escape`; the parens are
   dispatched only inside a destination, so they are claimed by
   `needs_escape_dest` instead. *)
(* The quote characters and the hyphen, named because `dopens_after`
   tests them and a bare literal would need escaping in a comment. *)
Definition one (c : ascii) : string := String c EmptyString.

(* The math prefix.  Reserved rather than a table row: it is not a
   delimiter, it retroactively changes what the run after it means. *)
Definition dollar : ascii := "$"%char.

Definition sqchar : ascii := "'"%char.
Definition dqchar : ascii := """"%char.
Definition hyphen : ascii := "-"%char.

Definition bang : ascii := "!"%char.

(* The ellipsis.  Like the dollar it is not a delimiter: three of them
   are one character of output and any other run is text. *)
Definition period : ascii := "."%char.

Definition lbrack : ascii := "["%char.
Definition rbrack : ascii := "]"%char.

(* The footnote marker.  Not reserved and not looked up in the table: it
   is the superscript row's character, and which of the two it means is
   decided by position -- only a `^` immediately inside a `[` marks a
   note.  So the table may keep claiming it, and `[^` is spelled with
   this rather than with `dchar DSuper`, since a table that moved the
   superscript row elsewhere must not move the footnote marker. *)
Definition hat : ascii := "^"%char.
Definition lparen : ascii := "("%char.
Definition rparen : ascii := ")"%char.

(* An autolink's brackets.  Only the `<` is reserved: the scanner
   dispatches on it in text mode, while a `>` is text unless a candidate
   is open, so a row may be spelled with `>` and none may with `<`. *)
Definition lt : ascii := "<"%char.
Definition gt : ascii := ">"%char.

(* `ibreak` writes the break into a destination as `nl` and the
   reconstruction reads it back byte by byte, so the two spellings have
   to be the same character. *)
Definition nl_char : ascii := "010"%char.

(* The characters the scanner claims for itself, before it consults the
   table at all: the escape, the verbatim fence, the two braces that
   force a delimiter, the three the bracket family dispatches on, the
   math prefix, the period and the autolink's `<`.  A row may not be
   written with one of
   these -- `ilead` would never reach the lookup -- which is one of the
   conditions `dconfig_ok` checks. *)
Definition dreserved (c : ascii) : bool :=
  (is_bslash c || is_tick c
   || Ascii.eqb c lbrace || Ascii.eqb c rbrace
   || Ascii.eqb c lbrack || Ascii.eqb c rbrack
   || Ascii.eqb c bang || Ascii.eqb c dollar
   || Ascii.eqb c lt
   (* the period is not a delimiter and opens nothing, but the scanner
      dispatches on it for the ellipsis, which is enough to reserve it:
      no row may be spelled with it, and a canonical `Str` holding one
      escapes it so that `...` cannot come back as an ellipsis. *)
   || Ascii.eqb c period)%bool.

(*
The delimiter table
-------------------

djot.js instantiates one function, `betweenMatched(c, annotation,
defaultmatch, opentest)` (`inline.ts:103`), at nine characters, so the
table is a transcription rather than a generalization of ours.  It is a
table and not nine branches for the reason
`.project/project-engineering-lessons.md` gives under "A hanging `Qed`":
the scanner must keep one recursive call and decide what to do by lookup,
or a general lemma about it becomes unprovable while every `Compute`
stays fast.

Nine rows here, which is every `betweenMatched` row upstream.  Three of
the characters carry a second construct as well -- the two quotes carry
smart quotes, and the hyphen carries smart dashes -- and in each case the
row and the construct are separate work, since a row is a table entry and
a construct is not. *)

Inductive dstyle : Type :=
  | DEmph | DStrong | DSuper | DSub | DMark | DInsert | DDelete
  (* The smart quotes.  They are `betweenMatched` rows like the rest,
     with one difference the table has to carry: an unmatched one is not
     literal text but a curly quote, and which curly quote depends on the
     markers around it. *)
  | DSQuote | DDQuote.

(* How a row may be written.  `DBraced` is djot.js's `opentest = hasBrace`
   -- the row exists only as `{x ... x}`, because the bare character is
   too common in prose to claim -- and `DBare` is `alwaysTrue`, where the
   braces are an optional override.  `DOff` is the third value the table
   needs but djot never uses: it removes the row, which is what makes
   "which containers exist" a setting rather than a fixed list. *)
Inductive dsyntax : Type :=
  | DOff | DBraced | DBare
  (* djot's single quote: bare, but a bare *opener* only where an
     apostrophe cannot be meant -- at the start of the line, or after a
     space, tab, carriage return, newline, either quote character, a
     hyphen, an open paren or an open bracket (`inline.ts:296-312`).
     This is the reason `can't` is an apostrophe and not an open quote,
     and it is `opentest` again: a third value of the slot `DBraced`
     already uses. *)
  | DBareAfterBreak.

(* The delimiter table, as a parameter.  Every row carries the character
   it is written with and how it may be written; a configuration is a
   choice of both for each row, and djot is one such choice.  Reading the
   character out of the table rather than fixing it per constructor is
   what lets emphasis and strong swap characters. *)
(* What a token that opens nothing and closes nothing leaves behind.
   Every row but the quotes leaves its own source text; a quote leaves a
   curly character, and *which* one is decided by the markers around it:
   djot.js records a `defaultmatch` per row and flips it, an open marker
   choosing the left form and a close marker the right one
   (`inline.ts:118-136`). *)
Inductive ddecay : Type :=
  | DDSelf
  | DDPair (left_by_default : bool) (left right : string).

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
  dc_footnotes : bool
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

(* An unmatched single quote is an apostrophe -- the right form -- while
   an unmatched double quote opens rather than closes.  Both were read
   off djot.js (`right_single_quote`, `left_double_quote`) and checked
   against it. *)
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
    true.

Fixpoint chars (c : ascii) (n : nat) : string :=
  match n with O => EmptyString | S m => String c (chars c m) end.

Definition dstyles : list dstyle :=
  [DEmph; DStrong; DSuper; DSub; DMark; DInsert; DDelete;
   DSQuote; DDQuote].

Definition dstyle_eq (a b : dstyle) : bool :=
  match a, b with
  | DEmph, DEmph | DStrong, DStrong | DSuper, DSuper
  | DSub, DSub | DMark, DMark | DInsert, DInsert
  | DDelete, DDelete | DSQuote, DSQuote | DDQuote, DDQuote => true
  | _, _ => false
  end.

Lemma dstyle_eq_true : forall a b, dstyle_eq a b = true -> a = b.
Proof. intros [] []; first [reflexivity | discriminate]. Qed.

Definition denabled (C : dconfig) (k : dstyle) : bool :=
  match dc_syntax C k with DOff => false | _ => true end.

Lemma dstyles_complete : forall k, In k dstyles.
Proof. intros []; cbn; tauto. Qed.

(* Look a character up in the table rather than repeating it, which is
   what makes `dstyle_of_dchar` below a fact about the search rather than
   a coincidence between two spellings.  A row switched off is not found,
   so `DOff` removes the character from the scanner entirely. *)
Definition dstyle_at (C : dconfig) (c : ascii) : option dstyle :=
  find (fun k => denabled C k && Ascii.eqb (dc_char C k) c)%bool dstyles.

(* An admissible table.  Four conditions, and between them they are
   everything the scanner and the renderer assume about it -- which is
   what makes the table a parameter rather than six constructors.  It is
   decidable and closed, so a configuration is checked rather than
   trusted.

   1. *Unambiguous*: no two rows that are switched on claim the same
      character.  The general form of "emphasis and strong emphasis must
      use different characters", stated over the table rather than over
      one pair.
   2. *Written*: a row has a nonzero width, so its delimiter is a
      nonempty string.  A width of zero would spell a delimiter as `""`,
      which nothing could scan and nothing could close.
   3. *Escapable*: a row's character is punctuation, so a backslash can
      escape it.  This is what `needs_escape_punct` needs -- the decoder
      only accepts an escape of punctuation.
   4. *Free*: a row's character is not one the scanner claims for itself.
      `ilead` dispatches the reserved characters before it consults the
      table, so a row spelled with one would never be reached.
   5. *Leaves something*: what an unmatched token decays to is nonempty,
      so no token can vanish.

   Conditions 2 to 4 are asked of *every* row, not only the switched-on
   ones.  A switched-off row's character is never looked up, so the tax
   is that a table must spell even a row it does not use with something
   admissible -- and what it buys is that "has a token" and "is not a
   backtick" hold unconditionally, instead of every lemma about scanning
   a delimiter carrying "this row exists".  Only `dstyle_of` itself needs
   that, since a switched-off row is genuinely not found. *)
(* A row's decay leaves something behind: an empty one would let a token
   vanish, so a document could hold a delimiter run that reaches neither
   a node nor the text. *)
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

Definition drow_ok (C : dconfig) (k : dstyle) : bool :=
  (negb (Nat.eqb (dc_width C k) 0)
   && is_punct (dc_char C k)
   && negb (dreserved (dc_char C k))
   && ddecay_ok (dc_decay C k)
   && negb (dsyntax_bare (dc_syntax C k) && Ascii.eqb (dc_char C k) hyphen))%bool.

Definition dconfig_distinct (C : dconfig) : bool :=
  forallb
    (fun k => forallb
       (fun k' => implb (denabled C k && denabled C k'
                         && Ascii.eqb (dc_char C k) (dc_char C k'))%bool
                        (dstyle_eq k k'))
       dstyles)
    dstyles.

Definition dconfig_rows_ok (C : dconfig) : bool :=
  forallb (drow_ok C) dstyles.

Definition dconfig_ok (C : dconfig) : bool :=
  (dconfig_distinct C && dconfig_rows_ok C)%bool.

Definition delimiter_admissible : invariant dconfig :=
  fun C => dconfig_ok C = true.

(* A row update is the local edit Phase 4's table knobs make.  Keeping the
   payload together matters: compatibility is checked of the replacement row
   as a unit rather than as four unrelated function updates. *)
Record dentry : Type := DEntry {
  de_char : ascii;
  de_width : nat;
  de_syntax : dsyntax;
  de_decay : ddecay
}.

Definition dentry_of (C : dconfig) (k : dstyle) : dentry :=
  DEntry (dc_char C k) (dc_width C k) (dc_syntax C k) (dc_decay C k).

Definition update_drow
  (target : dstyle) (e : dentry) (C : dconfig) : dconfig :=
  DConfig
    (fun k => if dstyle_eq k target then de_char e else dc_char C k)
    (fun k => if dstyle_eq k target then de_width e else dc_width C k)
    (fun k => if dstyle_eq k target then de_syntax e else dc_syntax C k)
    (fun k => if dstyle_eq k target then de_decay e else dc_decay C k)
    (dc_smart_typography C) (dc_raw_inline C) (dc_math C) (dc_attrs C)
    (dc_footnotes C).

(* Smart dashes and ellipses are scanner capabilities rather than delimiter
   rows.  This field-local knob leaves every row unchanged. *)
Definition with_smart_typography (enabled : bool) (C : dconfig) : dconfig :=
  DConfig (dc_char C) (dc_width C) (dc_syntax C) (dc_decay C) enabled
    (dc_raw_inline C) (dc_math C) (dc_attrs C) (dc_footnotes C).

Theorem with_smart_typography_preserves_admissible :
  forall enabled, preserves (with_smart_typography enabled) delimiter_admissible.
Proof. intros enabled C H. exact H. Qed.

Definition with_raw_inline (enabled : bool) (C : dconfig) : dconfig :=
  DConfig (dc_char C) (dc_width C) (dc_syntax C) (dc_decay C)
    (dc_smart_typography C) enabled (dc_math C) (dc_attrs C)
    (dc_footnotes C).

Theorem with_raw_inline_preserves_admissible :
  forall enabled, preserves (with_raw_inline enabled) delimiter_admissible.
Proof. intros enabled C H. exact H. Qed.

(* Math is the dollar prefix on a verbatim, not a row: it has its own
   character, which no table may claim, and its own scanner state. *)
Definition with_math (enabled : bool) (C : dconfig) : dconfig :=
  DConfig (dc_char C) (dc_width C) (dc_syntax C) (dc_decay C)
    (dc_smart_typography C) (dc_raw_inline C) enabled (dc_attrs C)
    (dc_footnotes C).

Theorem with_math_preserves_admissible :
  forall enabled, preserves (with_math enabled) delimiter_admissible.
Proof. intros enabled C H. exact H. Qed.

(* Inline attributes and spans.  The rows keep their own switches: a table
   whose delete row is on still reads `{-` as a delete opener here. *)
Definition with_inline_attrs (enabled : bool) (C : dconfig) : dconfig :=
  DConfig (dc_char C) (dc_width C) (dc_syntax C) (dc_decay C)
    (dc_smart_typography C) (dc_raw_inline C) (dc_math C) enabled
    (dc_footnotes C).

Theorem with_inline_attrs_preserves_admissible :
  forall enabled, preserves (with_inline_attrs enabled) delimiter_admissible.
Proof. intros enabled C H. exact H. Qed.

(* Exported, but `Profile.with_footnotes` is what a caller should reach
   for: this half alone leaves definitions nothing can reference. *)
Definition with_inline_footnotes (enabled : bool) (C : dconfig) : dconfig :=
  DConfig (dc_char C) (dc_width C) (dc_syntax C) (dc_decay C)
    (dc_smart_typography C) (dc_raw_inline C) (dc_math C) (dc_attrs C)
    enabled.

Theorem with_inline_footnotes_preserves_admissible :
  forall enabled,
    preserves (with_inline_footnotes enabled) delimiter_admissible.
Proof. intros enabled C H. exact H. Qed.

Definition drow_trigger_compatible
  (C : dconfig) (target : dstyle) (e : dentry) : bool :=
  let C' := update_drow target e C in
  forallb
    (fun k =>
       implb
         (negb (dstyle_eq k target)
          && denabled C' k && denabled C' target)%bool
         (negb (Ascii.eqb (dc_char C' k) (dc_char C' target))))
    dstyles.

(* The replacement has to be a valid row, and its enabled trigger must differ
   from every unchanged enabled row.  Those are precisely the two facts not
   inherited from an admissible input table; no whole-table recheck is part of
   this compatibility predicate. *)
Definition drow_update_compatible
  (C : dconfig) (target : dstyle) (e : dentry) : bool :=
  (drow_ok (update_drow target e C) target
   && drow_trigger_compatible C target e)%bool.

Lemma denabled_update_drow_other :
  forall C target e k,
    dstyle_eq k target = false ->
    denabled (update_drow target e C) k = denabled C k.
Proof.
  intros C target e k H. unfold update_drow, denabled. cbn.
  rewrite H. reflexivity.
Qed.

Lemma denabled_update_drow_target :
  forall C target e,
    denabled (update_drow target e C) target =
    match de_syntax e with DOff => false | _ => true end.
Proof.
  intros C [] e; unfold denabled, update_drow; cbn;
    destruct (de_syntax e); reflexivity.
Qed.

Lemma dchar_update_drow_other :
  forall C target e k,
    dstyle_eq k target = false ->
    dc_char (update_drow target e C) k = dc_char C k.
Proof.
  intros C target e k H. unfold update_drow. cbn.
  rewrite H. reflexivity.
Qed.

Lemma dchar_update_drow_target :
  forall C target e,
    dc_char (update_drow target e C) target = de_char e.
Proof. intros C [] e; reflexivity. Qed.

Lemma no_trigger_collision :
  forall a b same conclusion,
    implb (a && b) (negb same) = true ->
    implb (a && b && same) conclusion = true.
Proof. intros [] [] [] []; reflexivity || discriminate. Qed.

Lemma no_trigger_collision_sym :
  forall a b same conclusion,
    implb (a && b) (negb same) = true ->
    implb (b && a && same) conclusion = true.
Proof. intros [] [] [] []; reflexivity || discriminate. Qed.

Lemma dconfig_distinct_update_drow :
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

Lemma drow_ok_update_drow_other :
  forall C target e k,
    dstyle_eq k target = false ->
    drow_ok (update_drow target e C) k = drow_ok C k.
Proof.
  intros C target e k H. unfold drow_ok, update_drow. cbn.
  rewrite H. reflexivity.
Qed.

Lemma drow_ok_update_drow_target :
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

(* The second table this development ships is now one checked row update:
   Markdown's `**` spelling for strong, with djot's semantics everywhere
   else.  A single `*` is literal because the row has one fixed width; there
   is no run-length disambiguation or flanking rule. *)
Definition markdown_strong_entry : dentry :=
  DEntry "*"%char 2 DBare DDSelf.

Definition markdown_config : dconfig :=
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

(* The hyphen is condition 4's remaining case, and it is the one the
   character alone does not settle.  `ilead` claims a hyphen before it
   consults the table, so a row declaring itself bare and spelled `-`
   would be read in its braced spelling and in no other: `{-x-}` marks
   the span and `-x-` is a smart dash.  A row that does not do what its
   syntax says is not admissible. *)
Example bare_hyphen_incompatible :
  drow_update_compatible djot_config DEmph
    (DEntry hyphen 1 DBare DDSelf) = false.
Proof. vm_compute. reflexivity. Qed.

(* The braced spelling is reached from the brace, so the condition does
   not touch it -- which is what keeps djot's own delete row legal. *)
Example braced_hyphen_row_ok :
  drow_ok (update_drow DEmph (DEntry hyphen 1 DBraced DDSelf) djot_config)
    DEmph = true.
Proof. vm_compute. reflexivity. Qed.

(* Disabling is the first specialization.  It changes only the syntax field;
   the row remains intrinsically valid even while switched off. *)
Definition disable_entry (C : dconfig) (target : dstyle) : dentry :=
  DEntry (dc_char C target) (dc_width C target) DOff (dc_decay C target).

Definition disable_row (target : dstyle) (C : dconfig) : dconfig :=
  update_drow target (disable_entry C target) C.

(* Disabling can only make a row more admissible: it keeps every field
   but the syntax, and a switched-off row is not a bare one, so the
   hyphen condition is discharged rather than carried. *)
Lemma drow_ok_disable_row :
  forall C target k,
    drow_ok C k = true -> drow_ok (disable_row target C) k = true.
Proof.
  intros C target k H. destruct target, k; cbn - [dreserved is_punct] in H |- *;
    try exact H;
    repeat (apply andb_true_iff in H as [H ?]);
    repeat (apply andb_true_iff; split); try assumption; reflexivity.
Qed.

Lemma disable_row_compatible :
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

(* Profiles switch off several independent containers by composing the same
   proved row operation.  The order is immaterial to behaviour, but keeping it
   as an explicit list makes the profile's surface syntax reviewable. *)
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

(* CommonMark has only emphasis and strong among these delimiter containers.
   This is intentionally called Markdown-like rather than CommonMark: the
   scanner still uses djot's simpler opening and closing rules. *)
Definition markdown_like_disabled_rows : list dstyle :=
  [DSuper; DSub; DMark; DInsert; DDelete; DSQuote; DDQuote].

Definition markdown_like_config : dconfig :=
  with_inline_attrs false
    (with_math false
      (with_raw_inline false
        (with_smart_typography false
          (disable_rows markdown_like_disabled_rows markdown_config)))).

Example markdown_like_config_ok : dconfig_ok markdown_like_config = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dconfig_ok_distinct :
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
   again.  Every later fact about the scanner needs this and nothing else
   about the table, which is why the condition is worth isolating. *)
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

(* The node a closed bracket builds, and the one place image-ness is
   consulted.  Kept beside `dnode` for the same reason: it is a lookup,
   not a branch in the scanner. *)
Definition bnode (image : bool) (ns : inlines) (tgt : target) : inline :=
  if image then Image ns tgt else Link ns tgt.

(* The label supplied by an empty reference (`[text][]`) is the string
   content of the first bracket.  This is djot.js's `getStringContent`,
   kept local to the inline layer so classification still does not consult
   either reference map. *)
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
  | FootnoteReference _ | Symbol _ | UrlLink _ | EmailLink _
  | NonBreakingSpace => EmptyString
  end.

Definition reference_inlines_text (ns : inlines) : string :=
  String.concat EmptyString (map (fun n => reference_text (node_contents n)) ns).

Definition dnode (k : dstyle) (ns : inlines) : inline :=
  match k with
  | DEmph => Emph ns | DStrong => Strong ns
  | DSuper => Superscript ns | DSub => Subscript ns
  | DMark => Highlight ns | DInsert => Insert ns
  | DDelete => Delete ns
  | DSQuote => Quoted SingleQuotes ns | DDQuote => Quoted DoubleQuotes ns
  end.

(* Djot's table satisfies the side condition: its six characters are
   distinct.  Checked rather than assumed. *)
Example djot_config_ok : dconfig_ok djot_config = true.
Proof. vm_compute. reflexivity. Qed.

Example markdown_config_ok : dconfig_ok markdown_config = true.
Proof. vm_compute. reflexivity. Qed.

(* And a table that is not admissible, so the condition is known to have
   teeth: giving strong the emphasis character makes `_` ambiguous. *)
Example clashing_config_not_ok :
  dconfig_ok (DConfig (fun k => match k with
                                | DStrong => "_"%char | _ => djot_dchar k
                                end)
                      djot_dwidth djot_dsyntax djot_ddecay true true true
                      true true)
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
                      djot_ddecay true true true true true) = true.
Proof. vm_compute. reflexivity. Qed.


(* The table in force, as a parameter.

   A `dtable` is an admissible configuration: a table together with the
   proof that it satisfies `dconfig_ok`.  Everything below is stated for
   an arbitrary one, so `roundtrip_blocks` and its neighbours are
   theorems about the family rather than about djot -- and a second
   configuration is a second instance rather than a second build.

   It is a class so that the argument stays implicit: the instance in
   scope is the one meant, and naming another (`@parse_inline_line
   markdown_table`) is how the other table is spoken of. *)
Class dtable : Type := DTable {
  cfg : dconfig;
  cfg_ok : dconfig_ok cfg = true
}.

Section WithTable.
Context {T : dtable}.

Definition dchar (k : dstyle) : ascii := dc_char cfg k.

Definition dsyntax_of (k : dstyle) : dsyntax := dc_syntax cfg k.

Definition dwidth (k : dstyle) : nat := dc_width cfg k.

Definition smart_typography : bool := dc_smart_typography cfg.

Definition raw_inline_enabled : bool := dc_raw_inline cfg.

Definition math_enabled : bool := dc_math cfg.

Definition inline_attrs_enabled : bool := dc_attrs cfg.

Definition notes_enabled : bool := dc_footnotes cfg.

(* Whether the row exists at all in the table in force. *)
Definition denabled_of (k : dstyle) : bool := denabled cfg k.

Definition dstyle_of (c : ascii) : option dstyle := dstyle_at cfg c.

(* A row's delimiter as it is written: `dwidth` copies of its character.
   The scanner cuts a run of that character into these and leaves any
   remainder as text, which is why a width is enough and a general string
   is not needed -- the character belongs to one row, so there is nothing
   to disambiguate. *)
Definition dtoken (k : dstyle) : string := chars (dchar k) (dwidth k).

(* djot.js `pattNonspace` (inline.ts:80).  `can_open` and `can_close` are
   each one test of one neighbouring byte against this. *)
Definition is_space (c : ascii) : bool :=
  (Ascii.eqb c " "%char || Ascii.eqb c "009"%char
   || Ascii.eqb c "013"%char || Ascii.eqb c "010"%char)%bool.

Definition nonspace_at (p : option ascii) : bool :=
  match p with None => false | Some c => negb (is_space c) end.

(* The bytes after which djot's single quote may open: the start of the
   line, whitespace, either quote, a hyphen, or an opening paren or
   bracket (`inline.ts:296-312`).  Everything else is a word or a mark
   that an apostrophe could follow. *)
Definition dopens_after (c : option ascii) : bool :=
  match c with
  | None => true
  | Some ch =>
      (is_space ch || Ascii.eqb ch sqchar || Ascii.eqb ch dqchar
       || Ascii.eqb ch hyphen || Ascii.eqb ch lparen || Ascii.eqb ch lbrack)%bool
  end.

(* What an unmatched token leaves behind.  The two markers are djot.js's
   `has_open_marker` and `has_close_marker` (`inline.ts:118-136`), and
   they decide two separate things.

   *How far the token reaches.*  An ordinary row leaves its own source,
   and a marker's brace is part of it -- but only the one djot.js
   actually consumed: `endcloser` moves past the `}` only when there is
   no open marker, so `*}` is two characters of text and `{*}` is `{*`
   with the `}` still to come.

   *Which side a smart quote takes.*  The flip is directional.  An open
   marker can only turn a right default into a left one and a close
   marker only the reverse, so on the one token that carries both the
   row's own default decides which of them applies.  The double quote
   defaults left, so a braced open double quote with a `}` after it takes
   the right form; the single quote defaults right, and `{'` with a `}`
   after it takes the left. *)
Definition ddecay_str (k : dstyle) (openmark closemark : bool) : string :=
  match dc_decay cfg k with
  | DDSelf =>
      ((if openmark then one lbrace else EmptyString)
       ++ dtoken k
       ++ (if (closemark && negb openmark)%bool
           then one rbrace else EmptyString))%string
  | DDPair dfl l r =>
      if dfl then (if closemark then r else l)
      else (if openmark then l else r)
  end.

(* Whether an unbraced delimiter may open a span here.  Closing never
   asks this -- djot's `opentest` gates opening alone -- so a quote may
   close from anywhere its neighbour is nonspace. *)
Definition dbare (k : dstyle) (before : option ascii) : bool :=
  match dsyntax_of k with
  | DBare => true
  | DBareAfterBreak => dopens_after before
  | _ => false
  end.

Definition is_delim (c : ascii) : bool :=
  match dstyle_of c with Some _ => true | None => false end.

(* The table's coherence obligation, alongside the `needs_escape` ones
   below: a row's character must look the row up again.  A new row that
   reuses a character silently shadows an old one without it. *)
(* Whether the row exists at all in the table in force. *)

(* Everything the scanner and the renderer assume about the table is
   derived from the instance's own side condition, so an instance is
   admissible or it does not exist. *)
Lemma drow_ok_of : forall k, drow_ok cfg k = true.
Proof. intros k. exact (dconfig_ok_row cfg k cfg_ok). Qed.

(* An enabled row has a token to write.  A width of zero would spell a
   delimiter as the empty string, which nothing could scan and nothing
   could close. *)
Lemma dwidth_nonzero : forall k, dwidth k <> 0.
Proof.
  intros k. pose proof (drow_ok_of k) as H.
  unfold drow_ok in H. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _]. apply negb_true_iff in H.
  unfold dwidth. destruct (dc_width cfg k); [discriminate|]. discriminate.
Qed.

(* Hence a row's token is a nonempty string: what a delimiter decays to
   always has something in it. *)
Lemma dtoken_nonempty : forall k, nonempty_str (dtoken k) = true.
Proof.
  intros k. unfold dtoken.
  destruct (dwidth k) as [|w] eqn:E; [destruct (dwidth_nonzero k E)|reflexivity].
Qed.

(* Its character is punctuation, so a backslash escapes it... *)
Lemma dchar_punct : forall k, is_punct (dchar k) = true.
Proof.
  intros k. pose proof (drow_ok_of k) as H.
  unfold drow_ok in H. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [_ H]. exact H.
Qed.

(* ...and it is not one the scanner claims, so `ilead` reaches the
   lookup at all. *)
Lemma dchar_free : forall k, dreserved (dchar k) = false.
Proof.
  intros k. pose proof (drow_ok_of k) as H.
  unfold drow_ok in H. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [_ H]. apply negb_true_iff in H. exact H.
Qed.

(* And a bare row's character is not the hyphen.  `ilead` claims that
   character before the lookup, so a row declaring itself bare and
   spelled with it would be read in its braced spelling and in no other.
   A braced row may be spelled with it, which is where djot's delete row
   lives. *)
Lemma dchar_bare_free :
  forall k,
    dsyntax_bare (dsyntax_of k) = true ->
    Ascii.eqb (dchar k) hyphen = false.
Proof.
  intros k H. pose proof (drow_ok_of k) as Hr.
  unfold drow_ok in Hr. apply andb_true_iff in Hr as [_ Hr].
  apply negb_true_iff, andb_false_iff in Hr as [Hr|Hr];
    [unfold dsyntax_of in H; rewrite H in Hr; discriminate|exact Hr].
Qed.

(* What condition 5 buys, in the form the scanner uses it. *)
Lemma ddecay_str_nonempty :
  forall k om cm, nonempty_str (ddecay_str k om cm) = true.
Proof.
  intros k om cm. pose proof (drow_ok_of k) as H.
  unfold drow_ok in H. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [_ H].
  unfold ddecay_str. destruct (dc_decay cfg k) as [|dfl l r] eqn:E.
  - pose proof (dtoken_nonempty k) as Ht.
    destruct om; [reflexivity|].
    destruct (dtoken k); [discriminate|reflexivity].
  - cbn [ddecay_ok] in H. apply andb_true_iff in H as [Hl Hr].
    destruct dfl; [destruct cm; [exact Hr|exact Hl]|].
    destruct om; [exact Hl|exact Hr].
Qed.

Lemma dreserved_false :
  forall c,
    dreserved c = false ->
    is_bslash c = false /\ is_tick c = false
    /\ Ascii.eqb c lbrace = false /\ Ascii.eqb c rbrace = false
    /\ Ascii.eqb c lbrack = false /\ Ascii.eqb c rbrack = false
    /\ Ascii.eqb c bang = false /\ Ascii.eqb c dollar = false
    /\ Ascii.eqb c period = false /\ Ascii.eqb c lt = false.
Proof.
  intros c H. unfold dreserved in H.
  repeat (apply orb_false_iff in H as [H ?]). tauto.
Qed.

(* The lookup is by character, so a row it finds is spelled with the
   character that found it. *)
Lemma dstyle_of_char :
  forall c k, dstyle_of c = Some k -> dchar k = c.
Proof.
  intros c k H. unfold dstyle_of, dstyle_at in H.
  apply find_some in H as [_ H]. apply andb_true_iff in H as [_ H].
  apply Ascii.eqb_eq in H. exact H.
Qed.

(* And it only ever finds a row that is switched on. *)
Lemma dstyle_of_enabled :
  forall c k, dstyle_of c = Some k -> denabled_of k = true.
Proof.
  intros c k H. unfold dstyle_of, dstyle_at in H.
  apply find_some in H as [_ H]. apply andb_true_iff in H as [H _]. exact H.
Qed.

Lemma dstyle_of_dchar :
  forall k, denabled_of k = true -> dstyle_of (dchar k) = Some k.
Proof.
  intros k H. exact (dstyle_at_dchar cfg k cfg_ok H).
Qed.


Lemma nl_one_char : nl = one nl_char.
Proof. reflexivity. Qed.

(* The braced spelling of a delimiter, which is the canonical one: it
   opens and closes on sight, so it needs no neighbouring byte to be read
   as a delimiter.  Both the renderer and the scanner inversion speak of
   it, and both go through `dtoken`, so a row wider than one character is
   written the way it is read. *)
Definition marked_open (k : dstyle) : string := (one lbrace ++ dtoken k)%string.

Definition marked_close (k : dstyle) (tail : string) : string :=
  (dtoken k ++ one rbrace ++ tail)%string.

(* The tail is what follows the close, so a close with nothing after it
   absorbs whatever text comes next.  This is the join the roundtrip
   rewrites with: `ci_src` closes on `EmptyString` and the scan wants the
   rest of the line in its place. *)
Lemma marked_close_app :
  forall k tail, (marked_close k EmptyString ++ tail)%string = marked_close k tail.
Proof.
  intros k tail. unfold marked_close.
  rewrite !append_assoc. reflexivity.
Qed.

(* The claimed characters: the ones the scanner reserves, the ones the
   table hands out, and the punctuation claimed independently below.

   `^` is listed on its own because it is the one character that is both.
   It marks a footnote after a `[`, so canonical text must escape it; but
   it is also the superscript row's character, so it cannot join
   `dreserved`, which is precisely the set no row may claim.  A table
   that hands `^` to no row escapes it anyway, which costs an escape of a
   punctuation character and decodes back to itself. *)
(* The hyphen is here for the same reason as `hat` and not for `hat`'s
   reason.  It cannot be `dreserved`, because djot's delete row is
   spelled with it and a row's character may not be reserved; but the
   scanner dispatches on it for smart dashes whatever the table says, so
   a canonical `Str` must escape it under *every* table -- otherwise
   `iscan_escape` is false for a table whose rows avoid the hyphen. *)
Definition needs_escape (c : ascii) : bool :=
  (dreserved c || is_delim c || Ascii.eqb c hat || Ascii.eqb c hyphen
   || Ascii.eqb c ":"%char)%bool.

(* Obligation 1: an escaped character must be one the decoder accepts.
   The fixed characters are punctuation by computation; the table's
   characters satisfy the obligation because an admissible row is
   spelled with punctuation. *)
Lemma dreserved_punct : forall c, dreserved c = true -> is_punct c = true.
Proof.
  intros [b0 b1 b2 b3 b4 b5 b6 b7] H.
  destruct b0, b1, b2, b3, b4, b5, b6, b7;
    vm_compute in H |- *; first [reflexivity | discriminate].
Qed.

Lemma needs_escape_punct : forall c, needs_escape c = true -> is_punct c = true.
Proof.
  intros c H. apply orb_true_iff in H as [H|H];
    [|apply Ascii.eqb_eq in H; subst c; reflexivity].
  apply orb_true_iff in H as [H|H];
    [|apply Ascii.eqb_eq in H; subst c; reflexivity].
  apply orb_true_iff in H as [H|H];
    [|apply Ascii.eqb_eq in H; subst c; reflexivity].
  apply orb_true_iff in H as [H|H]; [apply dreserved_punct, H|].
  unfold is_delim in H. destruct (dstyle_of c) as [k|] eqn:E; [|discriminate].
  rewrite <- (dstyle_of_char c k E). apply dchar_punct.
Qed.

(* Obligation 2: the escape character escapes itself, or a text ending in
   a backslash would decode as an escape of whatever followed. *)
Lemma needs_escape_backslash : needs_escape "\"%char = true.
Proof. reflexivity. Qed.

(* Obligation 3: a backtick in a `Str` must not reach the scanner bare,
   or it would open a verbatim span instead of standing for itself.  This
   is the obligation every delimiter character will add. *)
Lemma needs_escape_tick : forall c, is_tick c = true -> needs_escape c = true.
Proof.
  intros c H. unfold needs_escape, dreserved. rewrite H.
  rewrite orb_true_r, !orb_true_l. reflexivity.
Qed.

(* Obligation 4, the same for every delimiter the table claims, and for
   the braces that force one open or closed. *)
Lemma needs_escape_delim : forall c, is_delim c = true -> needs_escape c = true.
Proof.
  intros c H. unfold needs_escape. rewrite H.
  rewrite orb_true_r, orb_true_l. reflexivity.
Qed.

(* And the hyphen, which no table can decline: `ilead` dispatches it
   before the lookup. *)
Lemma needs_escape_hyphen : needs_escape hyphen = true.
Proof. unfold needs_escape. rewrite orb_true_r. reflexivity. Qed.

(* The footnote marker, for the same reason the brackets are here: `[^`
   is a construct, so a `^` after a `[` must not reach the scanner
   bare. *)
Lemma needs_escape_hat : needs_escape hat = true.
Proof. unfold needs_escape. rewrite orb_true_r. reflexivity. Qed.

Lemma needs_escape_lbrace : needs_escape lbrace = true.
Proof. reflexivity. Qed.

Lemma needs_escape_rbrace : needs_escape rbrace = true.
Proof. reflexivity. Qed.

(* And the same for the brackets, on which the scanner dispatches: a `[`
   in a `Str` would open a scope, and a `]` would close one that a later
   construct opened. *)
Lemma needs_escape_lbrack : needs_escape lbrack = true.
Proof. reflexivity. Qed.

Lemma needs_escape_rbrack : needs_escape rbrack = true.
Proof. reflexivity. Qed.

(* The `!` an image opens on.  Escaping it unconditionally is what lets a
   `Str` ending in `!` sit before a link without turning it into an
   image, which is exactly the reading djot.js gives `\![a](u)`. *)
Lemma needs_escape_bang : needs_escape bang = true.
Proof. reflexivity. Qed.

(* A literal colon must not become a key connective when its line opens
   a paragraph.  Escaping it in the shared inline spelling also protects
   labels, and works with keys off: the inline decoder reads [\:] as [:]
   in either mode.  Like the other escapes, it is emitted on every line,
   so rendering does not need a block setting or a first-line variant. *)
Lemma needs_escape_colon : needs_escape ":"%char = true.
Proof. unfold needs_escape. rewrite orb_true_r. reflexivity. Qed.

(* Inside a destination the scanner dispatches on two more characters,
   the parentheses that move its depth counter, and on none of the
   delimiters -- but escaping those too is harmless (an escape decodes to
   the character in either mode) and keeps one predicate ordered above
   the other. *)
Definition needs_escape_dest (c : ascii) : bool :=
  (needs_escape c || Ascii.eqb c lparen || Ascii.eqb c rparen)%bool.

Lemma needs_escape_dest_punct :
  forall c, needs_escape_dest c = true -> is_punct c = true.
Proof.
  intros c H. unfold needs_escape_dest in H.
  apply orb_true_iff in H as [H|H].
  - apply orb_true_iff in H as [H|H]; [apply needs_escape_punct, H|].
    apply Ascii.eqb_eq in H. subst c. reflexivity.
  - apply Ascii.eqb_eq in H. subst c. reflexivity.
Qed.

Fixpoint escape_str (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if needs_escape c
      then String "\"%char (String c (escape_str rest))
      else String c (escape_str rest)
  end.

Fixpoint escape_dest (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if needs_escape_dest c
      then String "\"%char (String c (escape_dest rest))
      else String c (escape_dest rest)
  end.

(* Verbatim delimiters use the least positive backtick-run length that
   does not occur in the content, matching djot.js `verbatimDelim`. *)
Fixpoint tick_runs_from (run : nat) (s : string) : list nat :=
  match s with
  | EmptyString => if Nat.eqb run 0 then [] else [run]
  | String c rest =>
      if is_tick c then tick_runs_from (S run) rest
      else if Nat.eqb run 0
           then tick_runs_from 0 rest
           else run :: tick_runs_from 0 rest
  end.

Definition tick_runs (s : string) : list nat := tick_runs_from 0 s.

Fixpoint first_missing (fuel candidate : nat) (runs : list nat) : nat :=
  match fuel with
  | 0 => candidate
  | S fuel' =>
      if existsb (Nat.eqb candidate) runs
      then first_missing fuel' (S candidate) runs
      else candidate
  end.

Definition verb_ticks (s : string) : nat :=
  first_missing (S (String.length s)) 1 (tick_runs s).

Lemma first_missing_nonzero :
  forall fuel n runs, n <> 0 -> first_missing fuel n runs <> 0.
Proof.
  induction fuel as [|fuel IH]; intros n runs Hn; cbn [first_missing].
  - exact Hn.
  - destruct (existsb (Nat.eqb n) runs); [apply IH; discriminate|exact Hn].
Qed.

Lemma verb_ticks_nonzero : forall s, verb_ticks s <> 0.
Proof. intros s. unfold verb_ticks. apply first_missing_nonzero. discriminate. Qed.

Definition starts_tick (s : string) : bool :=
  match s with String c _ => is_tick c | _ => false end.

Definition ends_tick (s : string) : bool := starts_tick (rev_string s).

Lemma starts_tick_app_l :
  forall a b, nonempty_str a = true -> starts_tick (a ++ b) = starts_tick a.
Proof. intros [|c a] b H; [discriminate|reflexivity]. Qed.

Lemma rev_nonempty_str :
  forall s, nonempty_str (rev_string s) = nonempty_str s.
Proof.
  intros [|c s]; [reflexivity|].
  rewrite rev_string_cons. destruct (rev_string s); reflexivity.
Qed.

Lemma ends_tick_cons_nonempty :
  forall c d s, ends_tick (String c (String d s)) = ends_tick (String d s).
Proof.
  intros c d s. unfold ends_tick. rewrite rev_string_cons.
  apply starts_tick_app_l. rewrite rev_nonempty_str. reflexivity.
Qed.

Lemma ends_tick_app_r :
  forall a b, nonempty_str b = true -> ends_tick (a ++ b) = ends_tick b.
Proof.
  intros a b Hb. unfold ends_tick. rewrite rev_string_app.
  apply starts_tick_app_l. rewrite rev_nonempty_str. exact Hb.
Qed.

Definition pad_verb (s : string) : string :=
  let left := if starts_tick s then " " else EmptyString in
  let right := if ends_tick s then " " else EmptyString in
  (left ++ s ++ right)%string.

Lemma pad_verb_nonempty :
  forall s, nonempty_str s = true -> nonempty_str (pad_verb s) = true.
Proof.
  intros s H. unfold pad_verb. destruct (starts_tick s); cbn [append];
    [reflexivity|]. destruct s; [discriminate|reflexivity].
Qed.

Lemma pad_verb_starts_nontick :
  forall s, nonempty_str s = true -> starts_tick (pad_verb s) = false.
Proof.
  intros s H. unfold pad_verb. destruct (starts_tick s) eqn:Hs;
    destruct (ends_tick s); cbn [append starts_tick]; try reflexivity.
  all: rewrite starts_tick_app_l by exact H; exact Hs.
Qed.

Lemma pad_verb_ends_nontick :
  forall s, nonempty_str s = true -> ends_tick (pad_verb s) = false.
Proof.
  intros s H. unfold pad_verb. destruct (starts_tick s);
    destruct (ends_tick s) eqn:He; cbn [append].
  - change (ends_tick (" " ++ (s ++ " ")) = false).
    rewrite ends_tick_app_r by (destruct s; [discriminate|reflexivity]).
    rewrite ends_tick_app_r by reflexivity. reflexivity.
  - rewrite append_empty_r. change (ends_tick (" " ++ s) = false).
    rewrite ends_tick_app_r by exact H. exact He.
  - rewrite ends_tick_app_r by reflexivity. reflexivity.
  - rewrite append_empty_r. exact He.
Qed.

Fixpoint ticks (n : nat) : string :=
  match n with 0 => EmptyString | S k => String tick (ticks k) end.

Lemma ticks_succ_r :
  forall n, ticks (S n) = (ticks n ++ String tick EmptyString)%string.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [ticks append]. rewrite <- IH. reflexivity.
Qed.

Definition verb_text (s : string) : string :=
  let d := ticks (verb_ticks s) in (d ++ pad_verb s ++ d)%string.

Fixpoint verb_safe_from (n run : nat) (s : string) : bool :=
  match s with
  | EmptyString => negb (Nat.eqb run n)
  | String c rest =>
      if is_tick c then verb_safe_from n (S run) rest
      else (negb (Nat.eqb run n) && verb_safe_from n 0 rest)%bool
  end.

Definition verb_safe (n : nat) (s : string) : bool :=
  verb_safe_from n 0 s.

Definition starts_space_tick (s : string) : bool :=
  match s with
  | String c (String d _) => (Ascii.eqb c " "%char && is_tick d)%bool
  | _ => false
  end.

(* Exactly the strings `trim_verb` can emit. *)
Definition verb_content_ok (s : string) : bool :=
  (no_nl s && negb (starts_space_tick s)
   && negb (starts_space_tick (rev_string s))
   && verb_safe (verb_ticks s) (pad_verb s))%bool.

(*
Canonical inlines
=================
*)

(* A bracket's own source: the `[`, with the `!` of an image.  Both the
   canonical rendering and the literal fallback put it back. *)
Definition bracket_open (image : bool) : string :=
  if image then String bang (one lbrack) else one lbrack.

(* A link's closing half: the `](`, the escaped destination, and the `)`,
   with whatever follows.  Written with a tail for the same reason
   `marked_close` is -- the scanner inversion needs to speak of the
   closer and its continuation as one string. *)
Definition link_close (dst tail : string) : string :=
  String rbrack (String lparen (escape_dest dst ++ String rparen tail)).

(* A reference link's closing half: the `]`, then `[`, the label and `]`.
   The label is not escaped -- the scanner's reference mode accumulates
   bytes literally until a `]` -- so `ci_ok` has to keep `]` out of it
   rather than escape it. *)
Definition ref_close (label tail : string) : string :=
  String rbrack (String lbrack (label ++ String rbrack tail)).

(* A footnote reference is a leaf: its label is source rather than inline
   content, so there is no child canonical view to reconstruct. *)
Definition note_text (label : string) : string :=
  String lbrack (String hat (label ++ one rbrack)).

(* An unescaped `]` would end the label early, while an odd trailing run
   of backslashes would protect the reference's closing bracket. *)
Fixpoint note_label_safe_from (esc : bool) (label : string) : bool :=
  match label with
  | EmptyString => negb esc
  | String c rest =>
      if esc then note_label_safe_from false rest
      else if Ascii.eqb c rbrack then false
      else note_label_safe_from (is_bslash c) rest
  end.

Definition note_label_safe : string -> bool := note_label_safe_from false.

(*
Autolinks
---------

`<...>` is a link to its own text, and which kind it is the region
decides: djot.js runs two regexes over the captured bytes
(`inline.ts:270-276`), the email test first.  Both are "somewhere in the
region", not anchored, so they are searches rather than shapes -- which
is why an autolink is decided by two predicates and not by a parser. *)

(* `/[^:]@/`: an `@` with a character before it that is not a colon.  The
   leading position cannot match, so `<@x>` is not an email. *)
Fixpoint auto_email_from (prev : option ascii) (s : string) : bool :=
  match s with
  | EmptyString => false
  | String c rest =>
      match prev with
      | Some p =>
          if (Ascii.eqb c "@"%char && negb (Ascii.eqb p ":"%char))%bool
          then true else auto_email_from (Some c) rest
      | None => auto_email_from (Some c) rest
      end
  end.

Definition auto_email (s : string) : bool := auto_email_from None s.

(* `/[a-zA-Z]:/`: a letter immediately followed by a colon, anywhere.
   Not a scheme in the URI sense -- `<a:b>` is a link to `a:b` -- and the
   name says only what it tests. *)
Definition is_alpha (c : ascii) : bool :=
  ((Ascii.leb "a"%char c && Ascii.leb c "z"%char)
   || (Ascii.leb "A"%char c && Ascii.leb c "Z"%char))%bool.

Fixpoint auto_scheme (s : string) : bool :=
  match s with
  | String c ((String d _) as rest) =>
      if (is_alpha c && Ascii.eqb d ":"%char)%bool then true
      else auto_scheme rest
  | _ => false
  end.

(* The two tests, in djot.js's order.  A region failing both is not an
   autolink at all and the brackets are literal. *)
Definition auto_node (s : string) : inline :=
  if auto_email s then EmailLink s else UrlLink s.

Definition auto_kind_ok (s : string) : bool :=
  (auto_email s || auto_scheme s)%bool.

(* An autolink is its own source, brackets included. *)
Definition auto_text (s : string) : string :=
  String lt (s ++ one gt).

(* What the region may hold and still come back: the pattern is
   `[^<>\s]+`, so nonempty and free of its own brackets and of
   whitespace.  Nothing inside is escaped -- the scanner accumulates the
   region byte for byte -- so this excludes rather than escapes, as a
   reference label does.

   Split in two because the nonemptiness is a fact about the whole
   region and the exclusions are a fact about every byte: the scan
   inversion consumes the region a byte at a time, and its tail is not
   nonempty. *)
Definition auto_region (s : string) : bool :=
  (no_ws s && no_char lt s && no_char gt s)%bool.

Definition auto_body_ok (s : string) : bool :=
  (nonempty_str s && auto_region s)%bool.

(*
Raw inline
----------

A verbatim span whose closing run is followed immediately by `{=format}`
is raw content in that format rather than code.  djot.js decides it at
the closer with a second lookahead, `pattRawAttribute`
(`inline.ts:94`, used at :849), and only for a span that is verbatim
rather than math -- `` $`x`{=html} `` stays math.

The pattern is `\{=[^\s{}`]+\}`, so the format is nonempty and free of
whitespace, either brace and the backtick.  It is *not* attribute
syntax: the raw check runs first and a spec that fails it can never
parse as attributes either, since no attribute spec begins with `=`.
That is what lets one mode decide the question, and it is also what
makes `` `x`{=html=} `` raw with format `html=` rather than the
highlight row the same bytes would be anywhere else. *)

(* The source after the `{`, which the mode accumulates.  A format is
   what follows an `=`, so a spec that does not begin with one has
   already failed. *)
Definition eqchar : ascii := "="%char.

Definition raw_spec_ok (spec : string) : bool :=
  match spec with
  | String c rest => (Ascii.eqb c eqchar && nonempty_str rest)%bool
  | EmptyString => false
  end.

(* The same conditions on the format alone, which is what the canonical
   view has in hand.  `raw_spec_ok (String eqchar fmt)` is this, and the
   scan inversion is where the two meet. *)
Definition raw_fmt_ok (fmt : string) : bool :=
  (nonempty_str fmt && no_ws fmt && no_char lbrace fmt
   && no_char rbrace fmt && no_char tick fmt)%bool.

Definition raw_format (spec : string) : string :=
  match spec with String _ rest => rest | EmptyString => EmptyString end.

(* The bytes the pattern's character class excludes.  A `}` is not among
   them: it ends the spec, successfully or not. *)
Definition raw_stop (c : ascii) : bool :=
  (is_ws c || is_tick c || Ascii.eqb c lbrace)%bool.

(* What may follow a verbatim's closing run.  The `{` of a canonical
   delimiter may -- every one of them is spelled brace-first -- but a `{=`
   may not, since that is the raw spec and the verbatim would come back
   as raw content instead.  A `{` at the very end is excluded too: with
   nothing after it the scan is left in the raw mode rather than in the
   brace one, and the two states are equal only from the *next* byte on.
   Canonical source cannot spell one, since `escape_str` claims the
   brace. *)
Definition after_verb_next (s : string) : bool :=
  match s with
  | String c rest =>
      if Ascii.eqb c lbrace
      then match rest with
           | String d _ => negb (Ascii.eqb d eqchar)
           | EmptyString => false
           end
      else true
  | EmptyString => true
  end.

(* A raw span's own source: the verbatim, then the spec. *)
Definition raw_text (fmt s : string) : string :=
  (verb_text s ++ String lbrace (String "="%char (fmt ++ one rbrace)))%string.

(* One line's inline content, described by the source that determines it.
   One constructor per inline construct the roundtrip covers, exactly as
   `cblock` carries one per block construct. *)
Inductive cinline : Type :=
  | CIStr (s : string)
  | CIVerb (s : string)
  | CIDelim (k : dstyle) (kids : list cinline)
  (* a direct link or image: its label, and the destination it resolves
     to.  The label may be empty -- `[](u)` is a link in djot -- which is
     the one way this differs from a delimiter. *)
  | CILink (img : bool) (kids : list cinline) (dst : string)
  (* a reference link or image: its text and the label it resolves
     against.  The explicit spelling `[text][label]` is the canonical one
     because it is context-free: the collapsed `[text][]` reads its label
     off the text, so it cannot express a label the text does not spell. *)
  | CIRef (img : bool) (kids : list cinline) (label : string)
  | CINote (label : string)
  (* an autolink: its region, which is both its source and its target.
     A leaf for the reason a footnote reference is one -- the region is
     raw source rather than inline content -- and the kind is not a field
     because `auto_node` computes it from the region, exactly as the
     scanner does. *)
  | CIAuto (s : string)
  (* raw content in a named format, which is a verbatim plus its spec.
     The format is a field because it is source the scanner reads, not
     something computed from the content -- the one way this differs from
     `CIAuto`. *)
  | CIRaw (fmt s : string).

Fixpoint ci_size (ci : cinline) : nat :=
  let go :=
    fix go (cis : list cinline) : nat :=
      match cis with
      | [] => 0
      | c :: rest => ci_size c + go rest
      end in
  match ci with
  | CIStr _ | CIVerb _ | CINote _ | CIAuto _ | CIRaw _ _ => 1
  | CIDelim _ kids | CILink _ kids _ | CIRef _ kids _ => S (go kids)
  end.

Fixpoint cis_size (cis : list cinline) : nat :=
  match cis with [] => 0 | c :: rest => ci_size c + cis_size rest end.

Lemma ci_size_delim :
  forall k kids, ci_size (CIDelim k kids) = S (cis_size kids).
Proof.
  intros k kids.
  assert (H : forall xs,
    (fix go (cis : list cinline) : nat :=
       match cis with
       | [] => 0
       | c :: rest => ci_size c + go rest
       end) xs = cis_size xs).
  { induction xs as [|c rest IH]; cbn [cis_size]; [reflexivity|].
    rewrite IH. reflexivity. }
  cbn [ci_size]. rewrite H. reflexivity.
Qed.

Lemma ci_size_link :
  forall img kids dst, ci_size (CILink img kids dst) = S (cis_size kids).
Proof.
  intros img kids dst. exact (ci_size_delim DEmph kids).
Qed.

Lemma ci_size_ref :
  forall img kids label, ci_size (CIRef img kids label) = S (cis_size kids).
Proof.
  intros img kids label. exact (ci_size_delim DEmph kids).
Qed.

Lemma ci_size_pos : forall ci, 0 < ci_size ci.
Proof.
  intros [s|s|k kids|img kids dst|img kids label|label|s|f s]; cbn [ci_size]; lia.
Qed.

(* The last byte of `s`, or `prev` when `s` is empty. *)
Fixpoint str_last (s : string) (prev : option ascii) : option ascii :=
  match s with
  | EmptyString => prev
  | String c rest => str_last rest (Some c)
  end.

(* Source text, threading the byte to the left of what is being emitted
   (`None` at the start of a line).

   Not `concat (map ...)`: a delimiter's spelling depends on its
   neighbours, so `Emph [CIStr "b"]` renders `_b_` at a line start but
   `{_b_}` inside `a_b_c`, and a context-free per-element function
   cannot say which.  One byte on each side is the whole of the context
   any djot rule consults, since `can_open` and `can_close` each test a
   single neighbouring character (djot.js `inline.ts:110-112`); the byte
   to the right is available from the unconsumed tail. *)
Fixpoint ci_src (ci : cinline) : string :=
  let go :=
    fix go (cis : list cinline) : string :=
      match cis with
      | [] => EmptyString
      | c :: rest => (ci_src c ++ go rest)%string
      end in
  match ci with
  | CIStr s => escape_str s
  | CIVerb s => verb_text s
  | CIDelim k kids =>
      (marked_open k ++ (go kids ++ marked_close k EmptyString))%string
  | CILink img kids dst =>
      (bracket_open img ++ (go kids ++ link_close dst EmptyString))%string
  | CIRef img kids label =>
      (bracket_open img ++ (go kids ++ ref_close label EmptyString))%string
  | CINote label => note_text label
  | CIAuto s => auto_text s
  | CIRaw fmt s => raw_text fmt s
  end.

Fixpoint ci_text (cis : list cinline) : string :=
  match cis with
  | [] => EmptyString
  | ci :: rest => (ci_src ci ++ ci_text rest)%string
  end.

Definition ci_line (cis : list cinline) : string := ci_text cis.

Lemma ci_src_delim :
  forall k kids,
    ci_src (CIDelim k kids)
    = (marked_open k ++ (ci_text kids ++ marked_close k EmptyString))%string.
Proof.
  intros k kids.
  assert (H : forall xs,
    (fix go (cis : list cinline) : string :=
       match cis with
       | [] => EmptyString
       | c :: rest => (ci_src c ++ go rest)%string
       end) xs = ci_text xs).
  { induction xs as [|c rest IH]; cbn [ci_text]; [reflexivity|].
    rewrite IH. reflexivity. }
  cbn [ci_src]. rewrite H. reflexivity.
Qed.

Lemma ci_src_link :
  forall img kids dst,
    ci_src (CILink img kids dst)
    = (bracket_open img ++ (ci_text kids ++ link_close dst EmptyString))%string.
Proof.
  intros img kids dst.
  assert (H : forall xs,
    (fix go (cis : list cinline) : string :=
       match cis with
       | [] => EmptyString
       | c :: rest => (ci_src c ++ go rest)%string
       end) xs = ci_text xs).
  { induction xs as [|c rest IH]; cbn [ci_text]; [reflexivity|].
    rewrite IH. reflexivity. }
  cbn [ci_src]. rewrite H. reflexivity.
Qed.

Lemma ci_src_ref :
  forall img kids label,
    ci_src (CIRef img kids label)
    = (bracket_open img ++ (ci_text kids ++ ref_close label EmptyString))%string.
Proof.
  intros img kids label.
  assert (H : forall xs,
    (fix go (cis : list cinline) : string :=
       match cis with
       | [] => EmptyString
       | c :: rest => (ci_src c ++ go rest)%string
       end) xs = ci_text xs).
  { induction xs as [|c rest IH]; cbn [ci_text]; [reflexivity|].
    rewrite IH. reflexivity. }
  cbn [ci_src]. rewrite H. reflexivity.
Qed.

(* ...and the AST the parser builds from that text. *)
Fixpoint ci_ast (ci : cinline) : node inline :=
  let go :=
    fix go (cis : list cinline) : inlines :=
      match cis with
      | [] => []
      | c :: rest => ci_ast c :: go rest
      end in
  match ci with
  | CIStr s => mk (Str s)
  | CIVerb s => mk (Verbatim s)
  | CIDelim k kids => mk (dnode k (go kids))
  | CILink img kids dst => mk (bnode img (go kids) (Direct dst))
  | CIRef img kids label => mk (bnode img (go kids) (Reference label))
  | CINote label => mk (FootnoteReference label)
  | CIAuto s => mk (auto_node s)
  | CIRaw fmt s => mk (RawInline fmt s)
  end.

Definition ci_inlines (cis : list cinline) : inlines := map ci_ast cis.

Lemma ci_ast_delim :
  forall k kids, ci_ast (CIDelim k kids) = mk (dnode k (ci_inlines kids)).
Proof.
  intros k kids.
  assert (H : forall xs,
    (fix go (cis : list cinline) : inlines :=
       match cis with
       | [] => []
       | c :: rest => ci_ast c :: go rest
       end) xs = ci_inlines xs).
  { induction xs as [|c rest IH]; cbn [ci_inlines map]; [reflexivity|].
    rewrite IH. reflexivity. }
  cbn [ci_ast]. rewrite H. reflexivity.
Qed.

Lemma ci_ast_link :
  forall img kids dst,
    ci_ast (CILink img kids dst)
    = mk (bnode img (ci_inlines kids) (Direct dst)).
Proof.
  intros img kids dst.
  assert (H : forall xs,
    (fix go (cis : list cinline) : inlines :=
       match cis with
       | [] => []
       | c :: rest => ci_ast c :: go rest
       end) xs = ci_inlines xs).
  { induction xs as [|c rest IH]; cbn [ci_inlines map]; [reflexivity|].
    rewrite IH. reflexivity. }
  cbn [ci_ast]. rewrite H. reflexivity.
Qed.

Lemma ci_ast_ref :
  forall img kids label,
    ci_ast (CIRef img kids label)
    = mk (bnode img (ci_inlines kids) (Reference label)).
Proof.
  intros img kids label.
  assert (H : forall xs,
    (fix go (cis : list cinline) : inlines :=
       match cis with
       | [] => []
       | c :: rest => ci_ast c :: go rest
       end) xs = ci_inlines xs).
  { induction xs as [|c rest IH]; cbn [ci_inlines map]; [reflexivity|].
    rewrite IH. reflexivity. }
  cbn [ci_ast]. rewrite H. reflexivity.
Qed.

Lemma ci_line_nil : ci_line [] = EmptyString.
Proof. reflexivity. Qed.

Lemma ci_line_str : forall s, ci_line [CIStr s] = escape_str s.
Proof. intros s. unfold ci_line. cbn [ci_text]. apply append_empty_r. Qed.

(*
Renderability
-------------
*)

(* A `Str` carrying no text would not have been emitted, and one carrying
   a newline is not within-line content.

   An *empty* verbatim is excluded outright, which narrows the view by a
   document the parser can reach.  Its canonical source is two adjacent
   delimiter runs and nothing between, so it is closed only by what
   follows it: at the end of a paragraph the scan closes it, and anywhere
   else the runs merge and swallow the next byte -- across a line break
   included, since spans cross breaks.  Representing it would take a
   condition on the *paragraph*, which is one level above anything
   `cinline` knows about.  `Verbatim ""` in a one-line paragraph does
   round-trip; it is simply outside the view. *)
(* A `!` before a link's `[` would make it an image, and there is no
   pair rule for that: `needs_escape` claims the `!`, so a `Str` ending
   in one renders as `\!` and djot.js reads that as a link too. *)
(* A verbatim before a delimiter spelled with `=` is the third
   adjacency, and the raw spec is why: `` `x`{=a=} `` is the source of a
   verbatim beside a highlight, and both parsers read it as raw content
   in format `a=`.  The exclusion is on the row's *character*, not on the
   row, since the table is a parameter -- and it is the whole cost the
   raw construct puts on the canonical view. *)
Definition ci_pair_ok (a b : cinline) : bool :=
  match a, b with
  | CIStr _, CIStr _ => false
  | CIVerb _, CIVerb _ => false
  | CIVerb _, CIDelim k _ => negb (Ascii.eqb (dchar k) eqchar)
  (* raw content opens with a backtick run of its own, so it merges with
     a verbatim before it exactly as a second verbatim would *)
  | CIVerb _, CIRaw _ _ => false
  | _, _ => true
  end.

Fixpoint ci_ok (ci : cinline) : bool :=
  let go :=
    fix go (cis : list cinline) : bool :=
      match cis with
      | [] => true
      | c :: rest => (ci_ok c && go rest)%bool
      end in
  let sep :=
    fix sep (cis : list cinline) : bool :=
      match cis with
      | a :: ((b :: _) as rest) => ci_pair_ok a b && sep rest
      | _ => true
      end in
  match ci with
  | CIStr s => nonempty_str s && no_nl s
  | CIVerb s => nonempty_str s && verb_content_ok s
  (* The row has to be one the table in force actually has: `ci_src`
     spells a switched-off row exactly as a switched-on one, and the
     scanner would read it back as text.  This is what makes "which
     containers exist" a setting rather than a fixed list -- turning a
     row off removes it from the canonical view too. *)
  | CIDelim k kids =>
      (denabled_of k && nonempty kids && go kids && sep kids)%bool
  (* A destination holding a line break cannot round-trip: the scanner
     drops the break rather than recording it, so the rendering would
     come back shorter.  Everything else the scanner dispatches on is
     escaped by `escape_dest`. *)
  | CILink _ kids dst => (no_nl dst && go kids && sep kids)%bool
  (* A label reaches the AST normalized, so only an already-normalized one
     round-trips; `]` would end it early, and an empty one is the
     collapsed spelling, whose label comes from the text instead. *)
  | CIRef _ kids label =>
      (nonempty_str label && no_char rbrack label
       && String.eqb (normalize_label label) label
       && go kids && sep kids)%bool
  | CINote label =>
      (notes_enabled && note_label_safe label
       && String.eqb (normalize_label label) label)%bool
  (* The region has to be one the pattern accepts and one of the two
     tests claims: a region that fails them is not an autolink but the
     literal text of its own brackets, which is a `CIStr` instead. *)
  | CIAuto s => (auto_body_ok s && auto_kind_ok s)%bool
  (* The content is a verbatim's, spelled by the same machinery and so
     under the same conditions.  The format is what `pattRawAttribute`
     accepts: nonempty and free of whitespace, either brace and the
     backtick -- and unescapable, since the mode reads it raw. *)
  | CIRaw fmt s =>
      (raw_inline_enabled && nonempty_str s
       && verb_content_ok s && raw_fmt_ok fmt)%bool
  end.

Lemma ci_ok_raw :
  forall fmt s,
    ci_ok (CIRaw fmt s)
    = (raw_inline_enabled && nonempty_str s
       && verb_content_ok s && raw_fmt_ok fmt)%bool.
Proof. reflexivity. Qed.

Lemma ci_ok_auto :
  forall s, ci_ok (CIAuto s) = (auto_body_ok s && auto_kind_ok s)%bool.
Proof. reflexivity. Qed.

Lemma ci_ok_note :
  forall label,
    ci_ok (CINote label)
    = (notes_enabled && note_label_safe label
       && String.eqb (normalize_label label) label)%bool.
Proof. reflexivity. Qed.

(* Pairwise source separation: adjacent strings merge, and adjacent
   verbatim spans merge their delimiter runs. *)
Fixpoint ci_sep_ok (cis : list cinline) : bool :=
  match cis with
  | a :: ((b :: _) as rest) => ci_pair_ok a b && ci_sep_ok rest
  | _ => true
  end.

Definition cis_ok (cis : list cinline) : bool :=
  forallb ci_ok cis && ci_sep_ok cis.

Lemma ci_ok_delim :
  forall k kids,
    ci_ok (CIDelim k kids)
    = (denabled_of k && nonempty kids && cis_ok kids)%bool.
Proof.
  intros k kids.
  assert (Hg : forall xs,
    (fix go (cis : list cinline) : bool :=
       match cis with
       | [] => true
       | c :: rest => (ci_ok c && go rest)%bool
       end) xs = forallb ci_ok xs).
  { induction xs as [|c rest IH]; cbn [forallb]; [reflexivity|].
    rewrite IH. reflexivity. }
  assert (Hs : forall xs,
    (fix sep (cis : list cinline) : bool :=
       match cis with
       | a :: ((b :: _) as rest) => ci_pair_ok a b && sep rest
       | _ => true
       end) xs = ci_sep_ok xs).
  { induction xs as [|a [|b rest] IH]; cbn [ci_sep_ok]; [reflexivity..|].
    rewrite IH. reflexivity. }
  cbn [ci_ok]. rewrite Hg, Hs. unfold cis_ok.
  repeat rewrite andb_assoc. reflexivity.
Qed.

Lemma ci_ok_link :
  forall img kids dst,
    ci_ok (CILink img kids dst) = (no_nl dst && cis_ok kids)%bool.
Proof.
  intros img kids dst.
  assert (Hg : forall xs,
    (fix go (cis : list cinline) : bool :=
       match cis with
       | [] => true
       | c :: rest => (ci_ok c && go rest)%bool
       end) xs = forallb ci_ok xs).
  { induction xs as [|c rest IH]; cbn [forallb]; [reflexivity|].
    rewrite IH. reflexivity. }
  assert (Hs : forall xs,
    (fix sep (cis : list cinline) : bool :=
       match cis with
       | a :: ((b :: _) as rest) => ci_pair_ok a b && sep rest
       | _ => true
       end) xs = ci_sep_ok xs).
  { induction xs as [|a [|b rest] IH]; cbn [ci_sep_ok]; [reflexivity..|].
    rewrite IH. reflexivity. }
  cbn [ci_ok]. rewrite Hg, Hs. unfold cis_ok.
  repeat rewrite andb_assoc. reflexivity.
Qed.

Lemma ci_ok_ref :
  forall img kids label,
    ci_ok (CIRef img kids label)
    = (nonempty_str label && no_char rbrack label
       && String.eqb (normalize_label label) label && cis_ok kids)%bool.
Proof.
  intros img kids label.
  assert (Hg : forall xs,
    (fix go (cis : list cinline) : bool :=
       match cis with
       | [] => true
       | c :: rest => (ci_ok c && go rest)%bool
       end) xs = forallb ci_ok xs).
  { induction xs as [|c rest IH]; cbn [forallb]; [reflexivity|].
    rewrite IH. reflexivity. }
  assert (Hs : forall xs,
    (fix sep (cis : list cinline) : bool :=
       match cis with
       | a :: ((b :: _) as rest) => ci_pair_ok a b && sep rest
       | _ => true
       end) xs = ci_sep_ok xs).
  { induction xs as [|a [|b rest] IH]; cbn [ci_sep_ok]; [reflexivity..|].
    rewrite IH. reflexivity. }
  cbn [ci_ok]. rewrite Hg, Hs. unfold cis_ok.
  repeat rewrite andb_assoc. reflexivity.
Qed.

(* Nonemptiness of a line's content is not a separate obligation: the
   block layer already asks that a paragraph's rendered lines are
   nonblank, and only `[]` renders blank. *)
Lemma cis_nonempty_of_line :
  forall cis, nonempty_str (ci_line cis) = true -> nonempty cis = true.
Proof.
  intros [|c rest] H; [rewrite ci_line_nil in H; discriminate | reflexivity].
Qed.

(* The form the block layer supplies it in: `para_ok` and `heading_ok`
   both carry `forallb line_ok` over the rendered lines. *)
Lemma cis_nonempty_of_lines :
  forall lss,
    forallb line_ok (map ci_line lss) = true ->
    forallb nonempty lss = true.
Proof.
  induction lss as [|cis rest IH]; [reflexivity|].
  cbn [map forallb]. intros H. apply andb_true_iff in H as [Hl Hr].
  rewrite (cis_nonempty_of_line cis
             (nonblank_nonempty _ (line_ok_nonblank _ Hl))).
  exact (IH Hr).
Qed.

(*
The inline pass
===============
*)

(* Verbatim content is trimmed of one padding space at each end, but only
   where it sits against a backtick (djot.js `trimVerbatim`, parse.ts:57).
   A space not adjacent to a backtick is content: `` ` a ` `` really is
   " a ".  Reversed, "ends with a backtick then a space" is "starts with a
   space then a backtick", so one function does both ends. *)

Definition strip_pad (s : string) : string :=
  match s with
  | String c rest =>
      if (Ascii.eqb c " "%char && starts_tick rest)%bool then rest else s
  | EmptyString => s
  end.

Definition trim_verb (s : string) : string :=
  rev_string (strip_pad (rev_string (strip_pad s))).

Lemma strip_pad_added :
  forall s, starts_tick s = true -> strip_pad (" " ++ s) = s.
Proof.
  intros [|c s] H; [discriminate|].
  cbn [starts_tick] in H. cbn [strip_pad append starts_tick].
  rewrite H. reflexivity.
Qed.

Lemma strip_pad_stable :
  forall s, negb (starts_space_tick s) = true -> strip_pad s = s.
Proof.
  intros [|c s] H; [reflexivity|]. destruct s as [|d s].
  - cbn [strip_pad starts_tick]. destruct (Ascii.eqb c " "%char); reflexivity.
  - cbn [starts_space_tick strip_pad] in H |- *.
    destruct (Ascii.eqb c " "%char) eqn:Hc; [|reflexivity].
    destruct (is_tick d) eqn:Hd; [discriminate|].
    cbn [starts_tick]. rewrite Hd. reflexivity.
Qed.

Lemma strip_pad_pad_verb :
  forall s, negb (starts_space_tick s) = true ->
    strip_pad (pad_verb s)
    = (s ++ if ends_tick s then " " else EmptyString)%string.
Proof.
  intros [|c [|d s]] H; unfold pad_verb;
    cbn [starts_tick starts_space_tick append] in H |- *.
  - reflexivity.
  - destruct (is_tick c) eqn:Hc;
      destruct (ends_tick (String c EmptyString)) eqn:He;
      cbn [append strip_pad starts_tick].
    + rewrite Hc. reflexivity.
    + rewrite Hc. reflexivity.
    + unfold ends_tick, rev_string, starts_tick in He.
      cbn [rev_string_aux] in He. rewrite Hc in He. discriminate.
    + destruct (Ascii.eqb c " "%char); reflexivity.
  - destruct (is_tick c) eqn:Hc;
      destruct (ends_tick (String c (String d s))) eqn:He;
      cbn [append strip_pad starts_tick].
    + rewrite Hc. reflexivity.
    + rewrite Hc. reflexivity.
    + apply negb_true_iff in H. rewrite H. reflexivity.
    + apply negb_true_iff in H. rewrite H. reflexivity.
Qed.

Lemma trim_verb_pad :
  forall s, verb_content_ok s = true -> trim_verb (pad_verb s) = s.
Proof.
  intros s H. unfold verb_content_ok in H.
  repeat rewrite andb_true_iff in H.
  destruct H as [[[Hnl Hleft] Hright] Hsafe].
  unfold trim_verb. rewrite strip_pad_pad_verb by exact Hleft.
  destruct (ends_tick s) eqn:He.
  - rewrite rev_string_app. cbn [rev_string rev_string_aux append].
    change (rev_string (strip_pad (" " ++ rev_string s)) = s).
    rewrite strip_pad_added.
    + apply rev_string_involutive.
    + exact He.
  - rewrite append_empty_r. rewrite strip_pad_stable by exact Hright.
    apply rev_string_involutive.
Qed.

(*
The scanner
-----------

One character at a time, structurally recursive on the remaining input.
That makes the current outer scan's source consumption structural: it
never re-feeds a source position through tokenization.  The project's
no-backtracking interpretation (see `.project/no-backtracking.md`) also
permits retroactive scope-stack changes and compound states whose
alternatives advance together.  This structure is not a linear-time
claim: resolving one byte may still walk the opener stack.  It also
matches djot.js's ordinary `feed`, which is a position-at-a-time loop over
a mode flag.

A verbatim closer is a run of *exactly* the opening width, so a run
cannot be resolved until the character after it arrives; that is why
`IVerb` carries a pending run count rather than closing eagerly.  A run
of the wrong width is content, which is how `` ` `` ` `` holds two
backticks inside a one-backtick fence. *)

Lemma nat_eqb_refl : forall n, Nat.eqb n n = true.
Proof. induction n; [reflexivity|exact IHn]. Qed.

(*
The scope stack
---------------

djot.js keeps a flat event list and rewrites it: an opener leaves a
placeholder `str` match, closing splices the real annotation over it, and
`clearOpeners` discards the openers a completed match spanned.  We keep a
stack of open scopes instead, each carrying its own accumulated inlines.
The two are equivalent -- probed against djot.js over the corpus and
~580k generated strings before any of this was written, see
`.project/260811.inline-parser.md` §2.2 -- and the stack is what the
proofs can induct on.

Three dispositions, of the four the probe found.  *Close* pops the
scope and emits its node.  *Abandon* replaces a scope by literal text:
its opener's spelling, then its content, spliced into the level below,
which is what `clearOpeners` plus the placeholder amount to.  The
remaining two, *discard* and closing below the top, belong to brackets
and are not reachable from this table. *)

(* What a scope accumulates.  A finished node, or an attribute spec
   whose target is not settled yet.

   djot.js attaches a spec in a pass over the *resolved* match stream, so
   by the time it asks "what is before this?" an opener that never closed
   is already text.  Asking during the scan gives a different answer --
   `a *b{.c}o` attaches to `b` rather than `*b` -- and no answer
   available at the `}` is the right one, since whether the `*` closes is
   not yet known.  So the spec waits here and `oresolve` settles it when
   the scope does.  The spec's source is not kept: nothing takes it
   back, since a spec with nothing to attach to is dropped. *)
Inductive oitem : Type :=
  | OIn (n : node inline)
  | OMark (a : attr) (spec : span) (word_start : option spot).

Definition oitems : Type := list oitem.

Inductive frame_kind : Type :=
  (* `closemark` is a `}` immediately after a marked opener.  It does not
     stop the token opening -- upstream's `has_open_marker` branch forces
     `can_open`, and the `}` stays as text -- and it does not change which
     closers reach the scope, so the bit reaches `fr_src` and nothing
     else.  A marked double quote with a `}` after it opens a scope whose
     abandoned spelling is the *right* curly quote, which is upstream
     flipping `defaultmatch` a second time (`inline.ts:126-136`). *)
  | FKDelim (style : dstyle) (closemark : bool)
  (* `image` records the `!` before the `[`, which djot.js instead reads
     back off the subject at the close (`inline.ts:475`).  We cannot: the
     text before the bracket has been flushed by then, and an escaped
     `\!` is indistinguishable from a bare one once it is in the buffer. *)
  | FKBracket (image : bool)
  (* The scope an unterminated destination decays into.  `](` does not
     end the bracket construct upstream: the `[` opener stays on the
     stack until the balanced `)` resolves it, so the destination's
     source is scanned as ordinary content that only becomes literal at
     the close (`inline.ts:470`).  This frame is that opener, still open,
     with the label and the `](` already inside it as text -- which is
     why its decay is the bracket's own byte and not the whole region.

     It differs from `FKBracket` in one way, and it is the one
     `inline.ts:150` states: a delimiter closer inside a destination may
     not reach an opener from outside the link construct, so this frame
     stops the walk that `FKBracket` lets through.  `[u](a ]{.c}`, where
     upstream re-enters the bracket, is not matched: `bclose_go` still
     stops here.  See `.project/exact-html-gaps.md`. *)
  | FKDest (image : bool).

Record frame : Type := Frame {
  fr_kind : frame_kind;
  fr_marked : bool;          (* delimiter opened as `{d`; false for `[` *)
  fr_open : span;            (* the opener token, for the node it closes *)
  fr_out : oitems            (* this scope's items, reversed *)
}.

(* The opener's source text, which is what it decays to when abandoned. *)
Definition fr_src (f : frame) : string :=
  match fr_kind f with
  | FKDelim k cm => ddecay_str k (fr_marked f) cm
  | FKBracket image | FKDest image => bracket_open image
  end.

(* Whether a closer's search out through the open scopes stops here
   rather than abandoning this one and carrying on. *)
Definition fr_barrier (f : frame) : bool :=
  match fr_kind f with
  | FKDest _ => true
  | FKDelim _ _ | FKBracket _ => false
  end.

Record ostate : Type := OState {
  os_out : oitems;           (* the outermost scope, reversed *)
  os_stk : list frame;       (* open scopes, innermost first *)
  os_word_start : option spot
}.

Definition ostart : ostate := OState [] [] None.

(* Which of two points is further into the source. *)
Definition spot_later (a b : spot) : spot :=
  if Nat.ltb (spot_line a) (spot_line b) then b
  else if Nat.ltb (spot_line b) (spot_line a) then a
  else if Nat.ltb (spot_rem a) (spot_rem b) then a else b.

(* Where a node's source ends, for the text that follows it: its own stop,
   or the end of the authored syntax it carries but does not cover -- an
   attribute spec sits after the node it attaches to and is not part of
   its range (`RAttrSpec`, section 4.4 of the plan). *)
Definition roles_stop (p : provenance) : spot :=
  fold_left (fun acc e => spot_later acc (span_stop (snd e)))
    (syntax_spans p) (span_stop (node_span p)).

Definition node_stop (fallback : spot) (n : node inline) : spot :=
  match node_provenance n with
  | Some p => roles_stop p
  | None => fallback
  end.

Fixpoint items_stop (fallback : spot) (l : oitems) : spot :=
  match l with
  | [] => fallback
  | OIn n :: _ => node_stop fallback n
  | OMark _ spec _ :: _ => span_stop spec
  end.

Definition text_start `{InlineCursor} (o : ostate) : spot :=
  match os_stk o with
  | [] => items_stop cursor_origin (os_out o)
  | f :: _ => items_stop (span_stop (fr_open f)) (fr_out f)
  end.

Definition remember_word_start `{PosPolicy} `{InlineCursor}
  (c : ascii) (o : ostate) : ostate :=
  if pos_records && is_ws c then
    OState (os_out o) (os_stk o) (Some cursor_stop)
  else o.

(* A line break ends the pending word: the spot after this line's last
   whitespace byte names no start on the next one, and the text node the
   break separates begins there. *)
Definition oword_reset (o : ostate) : ostate :=
  OState (os_out o) (os_stk o) None.

Definition inline_prov (start stop : spot) : provenance :=
  prov_at (SrcSpan start stop).

Definition imk `{PosPolicy} (start stop : spot) (x : inline) : node inline :=
  if pos_records
  then posnode (inline_prov start stop) x
  else mk x.

Lemma imk_semantic : forall start stop x,
  @imk semantic_pos start stop x = mk x.
Proof. reflexivity. Qed.

Lemma remember_word_start_semantic : forall c o,
  @remember_word_start semantic_pos semantic_inline_cursor c o = o.
Proof. reflexivity. Qed.

Definition imk_here `{PosPolicy} `{InlineCursor} (x : inline) : node inline :=
  imk cursor_start cursor_stop x.

(* An abandoned opener, put back as text.  It covers the source the
   opener was written in, which is not the length of what the decay
   spells: a smart quote is written `'` and decays to `â`. *)
Definition fr_lit `{PosPolicy} (f : frame) : node inline :=
  imk (span_start (fr_open f)) (span_stop (fr_open f)) (Str (fr_src f)).

Lemma fr_lit_semantic : forall f,
  @fr_lit semantic_pos f = mk (Str (fr_src f)).
Proof. reflexivity. Qed.

Lemma imk_here_semantic : forall x,
  @imk_here semantic_pos semantic_inline_cursor x = mk x.
Proof. reflexivity. Qed.

Definition add_inline_role `{PosPolicy} (role : syntax_role) (r : span)
  (n : node inline) : node inline := add_roles [(role, r)] n.

Lemma add_inline_role_semantic : forall role r n,
  @add_inline_role semantic_pos role r n = n.
Proof. reflexivity. Qed.

(* The scope emissions land in: the innermost open one, or the bottom. *)
Definition ocur (o : ostate) : oitems :=
  match os_stk o with [] => os_out o | f :: _ => fr_out f end.

(* ...and the same scope, written back.  Only attachment needs it: every
   other writer pushes rather than replaces. *)
Definition oset_cur (l : oitems) (o : ostate) : ostate :=
  match os_stk o with
  | [] => OState l [] (os_word_start o)
  | f :: rest =>
      OState (os_out o)
        (Frame (fr_kind f) (fr_marked f) (fr_open f) l :: rest)
        (os_word_start o)
  end.

Definition dstyle_eqb (a b : dstyle) : bool :=
  match a, b with
  | DEmph, DEmph | DStrong, DStrong | DSuper, DSuper
  | DSub, DSub | DMark, DMark | DInsert, DInsert
  | DDelete, DDelete | DSQuote, DSQuote | DDQuote, DDQuote => true
  | _, _ => false
  end.

(* A closer matches an opener when the character *and* the marking agree:
   djot.js keys its opener map by `{d` or `d`, so `{_a_` does not close
   and neither does `_a_}`. *)
Definition dmatch (k : dstyle) (m : bool) (f : frame) : bool :=
  match fr_kind f with
  | FKDelim k' _ => (dstyle_eqb k k' && Bool.eqb m (fr_marked f))%bool
  | FKBracket _ | FKDest _ => false
  end.

(* Reversed-list splices that merge a `Str` seam, so `no_adjacent_str`
   survives an abandoned opener becoming text next to its neighbours. *)
(* An attribute-less `Str` -- the kind a neighbour merges with. *)
Definition plain_str (n : node inline) : bool :=
  match n with Node _ [] (Str _) => true | _ => false end.

(* No two of them adjacent.  `Wf.no_adjacent_str` is this predicate; it
   lives here because `oresolve` is the identity exactly on lists that
   satisfy it, and the equational lemmas about closing a scope need to
   say so. *)
Fixpoint no_adjacent_str (ns : list (node inline)) : bool :=
  match ns with
  | n1 :: ((n2 :: _) as rest) =>
      negb (plain_str n1 && plain_str n2) && no_adjacent_str rest
  | _ => true
  end.

(* The same merge over resolved nodes, which is where it now does the
   real work: `oresolve` rebuilds a scope's list and this is what keeps
   two plain `Str`s from ending up adjacent in it. *)
Definition merge_text_pos (left right : pos) : pos :=
  match left, right with
  | SomePos p, SomePos q =>
      SomePos (Provenance
        (SrcSpan (span_start (node_span p)) (span_stop (node_span q)))
        (syntax_spans p ++ syntax_spans q)%list PNone)
  | _, _ => left
  end.

Definition isnoc (n : node inline) (out : inlines) : inlines :=
  match out, n with
  | Node p [] (Str t) :: rest, Node q [] (Str s) =>
      (Node (merge_text_pos p q) [] (Str (t ++ s)) :: rest)%list
  | _, _ => (n :: out)%list
  end.

(* The same question `starts_str` asks, of a resolved list. *)
Definition istarts_str (out : inlines) : bool :=
  match out with Node _ [] (Str _) :: _ => true | _ => false end.

(* `base_ok` of a resolved list: what a previous line always looks like
   once it is settled. *)
Definition ibase_ok (out : inlines) : bool :=
  match out with
  | [] => true
  | Node _ _ SoftBreak :: _ => true
  | _ => false
  end.

Lemma ibase_ok_starts_str :
  forall out, ibase_ok out = true -> istarts_str out = false.
Proof.
  intros [|[p [|kv a] v] out] H; try reflexivity.
  destruct v; try reflexivity. discriminate.
Qed.

Lemma isnoc_nonstr :
  forall n out, istarts_str out = false -> isnoc n out = (n :: out)%list.
Proof.
  intros n [|[a [|x xs] i] out'] H; try reflexivity.
  cbn [istarts_str] in H. destruct i; try reflexivity.
  destruct n as [c [|y ys] j]; try reflexivity.
  destruct j; try reflexivity. discriminate.
Qed.

Lemma isnoc_nonplain :
  forall n out, plain_str n = false -> isnoc n out = (n :: out)%list.
Proof.
  intros [p a v] out H. unfold isnoc.
  destruct out as [|[q [|kv b] w] l]; try reflexivity.
  destruct w; try reflexivity.
  unfold plain_str in H. destruct a; [|reflexivity].
  destruct v; try reflexivity. discriminate.
Qed.

Lemma isnoc_app :
  forall n out base,
    istarts_str base = false ->
    isnoc n (out ++ base)%list = (isnoc n out ++ base)%list.
Proof.
  intros n [|x out] base H; cbn [app]; [apply isnoc_nonstr, H|].
  unfold isnoc. destruct x as [p [|kv a] v]; [|reflexivity].
  destruct v; try reflexivity.
  destruct n as [q [|lv b] w]; [|reflexivity].
  destruct w; reflexivity.
Qed.

Definition osnoc (n : oitem) (out : oitems) : oitems :=
  match out, n with
  | OIn (Node p [] (Str t)) :: rest, OIn (Node q [] (Str s)) =>
      (OIn (Node (merge_text_pos p q) [] (Str (t ++ s))) :: rest)%list
  | _, _ => (n :: out)%list
  end.

(* Whether the seam could merge: exactly `Wf.plain_str` of the head, and
   the same notion `no_adjacent_str` is stated over.  A `Str` carrying
   attributes is a node in its own right and never merges. *)
Definition starts_str (out : oitems) : bool :=
  match out with OIn (Node _ [] (Str _)) :: _ => true | _ => false end.

Fixpoint oapp (cur out : oitems) : oitems :=
  match cur with
  | [] => out
  | [n] => osnoc n out
  | n :: rest => n :: oapp rest out
  end.

Definition oemit (n : node inline) (o : ostate) : ostate :=
  let word := os_word_start o in
  match os_stk o with
  | [] => OState (OIn n :: os_out o) [] word
  | f :: rest =>
      OState (os_out o)
        (Frame (fr_kind f) (fr_marked f) (fr_open f)
           (OIn n :: fr_out f) :: rest)
        word
  end.

(* A spec waiting for its target, emitted the same way. *)
Definition omark (a : attr) (spec : span) (o : ostate) : ostate :=
  match os_stk o with
  | [] => OState (OMark a spec (os_word_start o) :: os_out o) [] None
  | f :: rest =>
      OState (os_out o)
        (Frame (fr_kind f) (fr_marked f) (fr_open f)
           (OMark a spec (os_word_start o) :: fr_out f) :: rest)
        None
  end.

(* Emit in source order while merging a plain-`Str` seam.  Ordinary
   scanner emission keeps the seam obligation explicit in `iscan_wf`;
   reconstruction paths (abandoned frames and bracket literal fallback)
   already know they are splicing source fragments and need the merge by
   construction. *)
Definition oemit_merge (n : node inline) (o : ostate) : ostate :=
  match os_stk o with
  | [] => OState (osnoc (OIn n) (os_out o)) [] (os_word_start o)
  | f :: rest =>
      OState (os_out o)
        (Frame (fr_kind f) (fr_marked f) (fr_open f)
           (osnoc (OIn n) (fr_out f)) :: rest)
        (os_word_start o)
  end.

Fixpoint oemit_all_merge (ns : inlines) (o : ostate) : ostate :=
  match ns with
  | [] => o
  | n :: rest => oemit_all_merge rest (oemit_merge n o)
  end.

Fixpoint oemit_all (ns : inlines) (o : ostate) : ostate :=
  match ns with
  | [] => o
  | n :: rest => oemit_all rest (oemit n o)
  end.

Definition flush_text_at `{PosPolicy} `{InlineCursor}
  (txt : string) (o : ostate) : ostate :=
  if nonempty_str txt
  then oemit (imk (text_start o) cursor_start (Str txt)) o
  else o.

Definition flush_text_to_at `{PosPolicy} `{InlineCursor}
  (stop : spot) (txt : string) (o : ostate) : ostate :=
  if nonempty_str txt
  then oemit (imk (text_start o) stop (Str txt)) o
  else o.

(* The equational theory below is the semantic scanner's.  Keep its
   familiar names definitionally position-free; the located driver and
   the shared transition use the [_at] forms explicitly. *)
Definition flush_text (txt : string) (o : ostate) : ostate :=
  @flush_text_at semantic_pos semantic_inline_cursor txt o.

Lemma flush_text_at_semantic : forall txt o,
  @flush_text_at semantic_pos semantic_inline_cursor txt o = flush_text txt o.
Proof. reflexivity. Qed.

(* A stop the policy discards is a stop the semantic reading cannot see,
   so at that instance the two flushes are one function. *)
Lemma flush_text_to_at_semantic : forall stop txt o,
  @flush_text_to_at semantic_pos semantic_inline_cursor stop txt o =
  flush_text txt o.
Proof. reflexivity. Qed.

Definition opush_at
  (k : dstyle) (m cm : bool) (open : span) (o : ostate) : ostate :=
  OState (os_out o)
    (Frame (FKDelim k cm) m open [] :: os_stk o)
    (os_word_start o).

Definition previous_spot (p : spot) : spot :=
  Spot (spot_line p) (S (spot_rem p)).

(* How much source a string covers, as (line breaks, bytes before the
   first of them, bytes in all). *)
Fixpoint source_shape (s : string) : nat * nat * nat :=
  match s with
  | EmptyString => (0, 0, 0)
  | String c rest =>
      let '(lines, first, total) := source_shape rest in
      if Ascii.eqb c nl_char
      then (S lines, 0, S total)
      else (lines, S first, S total)
  end.

(* The point [s] bytes to the left of [p].  This is how a construct whose
   role is decided by a later byte recovers where it began: the token's
   own source is in the state, and stepping the cursor back over it is
   the token's first byte -- which is also where the text before it
   stopped.  Sound only for a token that cannot contain a line break,
   which is every construct resolved this way; a verbatim's content can,
   and reads its start off the scope instead (`text_start`). *)
Definition spot_before (p : spot) (s : string) : spot :=
  let '(lines, first, total) := source_shape s in
  if Nat.eqb lines 0
  then Spot (spot_line p) (spot_rem p + total)
  else Spot (spot_line p - lines) first.

(* [n] bytes to the left, on the same line.  The counted form of
   `spot_before`, for a token whose source is known by length. *)
Definition spot_plus (n : nat) (p : spot) : spot :=
  Spot (spot_line p) (spot_rem p + n).

(* Where a delimiter token being resolved began, and so where the text
   before it stopped: the run of the row's character, with the `{` of a
   marked opener in front of it.  The token is complete and the byte
   after it is the one in hand, so the cursor is its end. *)
Definition dtoken_span `{PosPolicy} `{InlineCursor}
  (k : dstyle) (marked : bool) : span :=
  pspan (SrcSpan
    (spot_before cursor_start
       ((if marked then one lbrace else EmptyString) ++ dtoken k)%string)
    cursor_start).

(* The common case: no `}` follows the opener, which is every unmarked
   one and every marked one whose next byte is anything else. *)
Definition opush `{PosPolicy} `{InlineCursor}
  (k : dstyle) (m : bool) (o : ostate) : ostate :=
  opush_at k m false (dtoken_span k m) o.

Definition bpush `{PosPolicy} `{InlineCursor} (image : bool) (o : ostate)
  : ostate :=
  let start := if image then previous_spot cursor_start else cursor_start in
  OState (os_out o)
    (Frame (FKBracket image) false (pspan (SrcSpan start cursor_stop)) []
       :: os_stk o)
    (os_word_start o).

(* The same push for a `](`: the bracket's opener stays open, and what
   goes into it is the label put back as text. *)
Definition dpush (image : bool) (open : span) (o : ostate) : ostate :=
  OState (os_out o)
    (Frame (FKDest image) false open [] :: os_stk o)
    (os_word_start o).

Lemma oemit_all_app :
  forall a b o, oemit_all (a ++ b)%list o = oemit_all b (oemit_all a o).
Proof.
  induction a as [|n a IH]; intros b o; cbn [oemit_all];
    [reflexivity|apply IH].
Qed.

Lemma oemit_all_frame :
  forall ns out kind m open acc stk word,
    oemit_all ns (OState out (Frame kind m open acc :: stk) word)
    = OState out
        (Frame kind m open (List.rev (List.map OIn ns) ++ acc)%list :: stk)
        word.
Proof.
  induction ns as [|n ns IH]; intros out kind m open acc stk word;
    cbn [oemit_all List.map List.rev app]; [reflexivity|].
  change (oemit_all ns
            (OState out (Frame kind m open (OIn n :: acc) :: stk) word)
          = OState out
              (Frame kind m open
                 ((List.rev (List.map OIn ns) ++ [OIn n]) ++ acc)%list
               :: stk) word).
  rewrite IH, <- List.app_assoc. reflexivity.
Qed.

(* The run an attribute spec attaches to when the thing before it is
   pending text: everything after the last whitespace.  djot.js attaches
   to the last *word*, so `foo bar{.a}` attributes only `bar` while
   `a-b{.a}` attributes all of `a-b` -- the split is on whitespace, not
   on word characters.  The result satisfies `s = pre ++ w` with `w`
   whitespace-free, which is why an attributed `Str` can never contain a
   space. *)
Fixpoint last_ws_split (s : string) : string * string :=
  match s with
  | EmptyString => (EmptyString, EmptyString)
  | String c rest =>
      match last_ws_split rest with
      | (EmptyString, w) =>
          if is_ws c then (one c, w) else (EmptyString, String c w)
      | (pre, w) => (String c pre, w)
      end
  end.

(* A last word can only come from text there was. *)
Lemma last_ws_split_nonempty :
  forall s, nonempty_str (snd (last_ws_split s)) = true -> nonempty_str s = true.
Proof. intros [|c s] H; [exact H|reflexivity]. Qed.

(* Where a waiting spec lands, asked of the list the scope has resolved
   so far -- whose head is whatever sits immediately before the spec.
   This is djot.js's `-attributes` handler (`parse.ts:446-506`), and it
   runs where djot.js runs it: after the openers that never closed have
   become text.

   - a plain `Str` before it takes the spec on its last word.  The split
     is on whitespace, not on word characters, so `a-b{.a}` attributes
     all of `a-b`; an empty spec keeps the run whole instead, since
     cutting it would only produce two plain `Str`s.
   - a run ending in whitespace has no last word, and djot.js drops the
     spec there rather than attaching it across the gap
     (`endsWithSpace`).
   - any other node takes it, which is what `*e*{.a}`, `[l](u){}` and
     `x{.a}{.b}` need.
   - nothing before it drops the spec, and so does a `SoftBreak`, which
     is nothing as far as attachment is concerned.  djot.js reaches the
     second by attaching to the break node, where the spec renders as
     nothing; dropping is the same observation and keeps the two arms
     one case.  They have to move together: the head below a spec is a
     `SoftBreak` exactly when an `oout_app` splice put a previous line
     there, so an arm that distinguished the empty scope from the
     spliced one would make attachment see the splice, and every `_app`
     lemma rests on it not seeing it. *)
Definition split_text_pos (p : pos) (word_start : option spot)
  : pos * pos :=
  match p, word_start with
  | SomePos pr, Some w =>
      (SomePos (prov_at (SrcSpan (span_start (node_span pr)) w)),
       SomePos (prov_at (SrcSpan w (span_stop (node_span pr)))))
  | _, _ => (p, p)
  end.

Definition oattach_list `{PosPolicy}
  (a : attr) (spec : span) (word_start : option spot) (out : inlines)
  : inlines :=
  match out with
  | Node p [] (Str s) :: rest =>
      let '(pre, w) := last_ws_split s in
      if nonempty_str w
      then match a with
           | [] => out
           | _ =>
               let '(pp, wp) := split_text_pos p word_start in
               let out1 := if nonempty_str pre
                           then isnoc (Node pp [] (Str pre)) rest else rest in
               isnoc (add_inline_role RAttrSpec spec (Node wp a (Str w))) out1
           end
      else out
  | Node _ _ SoftBreak :: _ | [] => out
  | n :: rest => add_inline_role RAttrSpec spec
                   (match n with
                    | Node p a' v => Node p (attr_merge a a') v
                    end) :: rest
  end.

(* A scope's items, settled.  Walking the tail first is what puts the
   already-resolved neighbours in front of each spec.

   The boolean is why the merge is not simply applied to every node: a
   spec that resolves to nothing leaves the run it sat between split in
   two, and only *there* do the neighbours have to be rejoined.  Merging
   unconditionally would be just as correct and would cost every
   equation of the form "a scope closes back to what was emitted into it"
   a `no_adjacent_str` side condition, since resolution would no longer
   be the identity on a settled list.  Carrying one bit keeps it the
   identity definitionally. *)
Fixpoint oresolve_go (l : oitems) : inlines * bool :=
  match l with
  | [] => ([], false)
  | OIn n :: rest =>
      let '(out, m) := oresolve_go rest in
      ((if m then isnoc n out else (n :: out)%list), false)
  | OMark a spec word_start :: rest =>
      let '(out, _) := oresolve_go rest in
      let out' := oattach_list a spec word_start out in
      (out', istarts_str out')
  end.

Definition oresolve (l : oitems) : inlines := fst (oresolve_go l).

(* Nothing waiting: resolution gives the list back, with no side
   condition. *)
Lemma oresolve_go_map :
  forall ns, oresolve_go (List.map OIn ns) = (ns, false).
Proof.
  induction ns as [|n ns IH]; [reflexivity|].
  cbn [List.map oresolve_go]. rewrite IH. reflexivity.
Qed.

(* A node that cannot merge is simply put in front. *)
Lemma oresolve_cons_nonplain :
  forall n l,
    plain_str n = false -> oresolve (OIn n :: l)%list = (n :: oresolve l)%list.
Proof.
  intros n l H. unfold oresolve; cbn [oresolve_go].
  destruct (oresolve_go l) as [out m]; cbn [fst].
  destruct m; [apply isnoc_nonplain, H|reflexivity].
Qed.

Lemma oresolve_map :
  forall ns, oresolve (List.map OIn ns) = ns.
Proof. intros ns. unfold oresolve. rewrite oresolve_go_map. reflexivity. Qed.

Lemma oresolve_map_rev :
  forall ns, oresolve (List.rev (List.map OIn ns)) = List.rev ns.
Proof.
  intros ns. rewrite <- List.map_rev. apply oresolve_map.
Qed.

(* Walk out through the open scopes looking for one this closer matches,
   abandoning each scope it passes.  `pend` carries what those abandoned
   scopes contributed, ready to splice into the next level down.

   The empty-span exclusion (`opener.endpos !== pos - 1`, inline.ts:148)
   stops the walk rather than continuing it.  djot.js keeps one opener
   stack per delimiter character and looks at its *top* only
   (`openers[openers.length - 1]`, inline.ts:145); when that opener is
   empty it falls through to "didn't match an opener", which leaves the
   opener where it is and lets the closer become an opener instead.  So a
   matching-but-empty scope is a failure to close, not a scope to abandon
   -- abandoning it would dissolve the opener into text and keep
   searching, which is what made `___a___` come out `<em>_</em>a<em>_</em>`
   instead of three nested spans, and `____` come out `<em>_</em>_`
   instead of literal.

   The test is on the items, not on what they resolve to, which is
   djot.js's order too: a scope holding nothing but an attribute spec
   with nothing to attach to closes, and closes onto nothing.  That is
   the one place an empty delimiter node comes from, and `wf_inline`
   admits it for that reason. *)
Fixpoint oclose_go `{PosPolicy} (k : dstyle) (m : bool) (pend : oitems)
  (stk : list frame)
  : option (oitems * span * list frame) :=
  match stk with
  | [] => None
  | f :: rest =>
      let content := oapp pend (fr_out f) in
      if dmatch k m f
      then (if nonempty content then Some (content, fr_open f, rest) else None)
      else if fr_barrier f then None
      else oclose_go k m (oapp content [OIn (fr_lit f)]) rest
  end.

(* Whether the search above stopped at a barrier with a scope this closer
   would otherwise have matched below it.  Upstream distinguishes the two
   failures: an opener barred by a destination makes the token *text*
   and returns (`inline.ts:155-158`), where no opener at all lets it
   become one. *)
Fixpoint oclose_barred_go (k : dstyle) (m : bool) (past : bool)
  (stk : list frame) : bool :=
  match stk with
  | [] => false
  | f :: rest =>
      if dmatch k m f then past
      else oclose_barred_go k m (past || fr_barrier f)%bool rest
  end.

Definition oclose_barred (k : dstyle) (m : bool) (o : ostate) : bool :=
  oclose_barred_go k m false (os_stk o).

(* The node runs from the opener the search matched to the end of the
   closing token, which the caller has in hand: the closer is complete
   and its last byte is either the one before the cursor or, for a marked
   close, the `}` in it. *)
Definition oclose `{PosPolicy} (k : dstyle) (m : bool) (stop : spot)
  (o : ostate) : option ostate :=
  match oclose_go k m [] (os_stk o) with
  | None => None
  | Some (content, open, rest) =>
      Some (oemit
              (imk (span_start open) stop
                 (dnode k (List.rev (oresolve content))))
              (OState (os_out o) rest (os_word_start o)))
  end.

(* The semantic reading of a close: the node is `mk`-wrapped whatever
   span it is handed, so the canonical scan lemmas below are stated
   without one. *)
Definition sclose (k : dstyle) (m : bool) (o : ostate) : option ostate :=
  @oclose semantic_pos k m (Spot 0 0) o.

Lemma oclose_semantic : forall k m stop o,
  @oclose semantic_pos k m stop o = sclose k m o.
Proof. reflexivity. Qed.

(* Unfolding a generic definition at the semantic instances leaves the
   [_at] spellings, which [rewrite] and [destruct] do not match against
   the names the equational theory is stated in. *)
Ltac sem_flush :=
  try change (@flush_text_at semantic_pos semantic_inline_cursor)
    with flush_text;
  repeat match goal with
  | |- context [@flush_text_to_at semantic_pos semantic_inline_cursor
                  ?stop ?txt ?o] =>
      change (@flush_text_to_at semantic_pos semantic_inline_cursor
                stop txt o)
        with (flush_text txt o)
  end;
  (* the same for a close, whose node the semantic policy builds without
     reading the span it is handed *)
  repeat match goal with
  | |- context [@oclose semantic_pos ?k ?m ?stop ?o] =>
      change (@oclose semantic_pos k m stop o) with (sclose k m o)
  end.

Lemma oclose_oemit_all_marked :
  forall `{P : PosPolicy} k cm ns open stop base,
    nonempty ns = true ->
    oclose k true stop (oemit_all ns (opush_at k true cm open base))
    = Some (oemit (imk (span_start open) stop (dnode k ns)) base).
Proof.
  intros P k cm ns open stop [out stk] Hne. unfold opush_at.
  rewrite oemit_all_frame.
  unfold oclose. cbn [os_stk os_out oclose_go oapp dmatch fr_kind
    fr_marked fr_out]. rewrite !app_nil_r.
  assert (Hrev : nonempty (List.rev (List.map OIn ns)) = true).
  { destruct ns as [|n rest]; [discriminate|].
    cbn [List.map List.rev]. destruct (List.rev (List.map OIn rest));
      reflexivity. }
  rewrite Hrev. destruct k;
    cbn [dmatch dstyle_eqb fr_kind fr_marked andb_true_l].
  all: cbn -[oresolve List.rev List.map];
       rewrite oresolve_map_rev, List.rev_involutive; reflexivity.
Qed.

(* Brackets share the ordered scope stack with delimiters.  Finding a
   bracket abandons any delimiter frames above it, just as djot.js closes
   the bracketed construct before `clearOpeners` removes openers inside
   it.  Unlike a delimiter close this only extracts the label content:
   the following byte still decides link, reference, span, or literal
   brackets. *)
Fixpoint bclose_go `{PosPolicy} (pend : oitems) (stk : list frame)
  : option (oitems * bool * span * list frame) :=
  match stk with
  | [] => None
  | f :: rest =>
      let content := oapp pend (fr_out f) in
      match fr_kind f with
      | FKBracket image => Some (content, image, fr_open f, rest)
      (* the destination's own opener is not offered back yet; see the
         constructor's comment *)
      | FKDest _ => None
      | FKDelim _ _ =>
          bclose_go (oapp content [OIn (fr_lit f)]) rest
      end
  end.

Definition bclose `{PosPolicy} (o : ostate)
  : option (inlines * bool * span * ostate) :=
  match bclose_go [] (os_stk o) with
  | None => None
  | Some (content, image, open, rest) =>
      Some (List.rev (oresolve content), image, open,
              OState (os_out o) rest (os_word_start o))
  end.

(* Take back a bracket the previous byte pushed.  Only a frame that is a
   bracket *and* still empty can be taken back, which is exactly the
   shape a `[` leaves behind and nothing else does, so a caller may ask
   without knowing what is on the stack.  That totality is what keeps the
   footnote marker free of any invariant relating `prev` to the frames,
   and `bunpush o = None` is what every lemma about a row's token gets
   for free -- a marked close has a *delimiter* frame on top. *)
Definition bunpush (o : ostate) : option (bool * span * ostate) :=
  match os_stk o with
  | Frame (FKBracket image) _ open [] :: rest =>
      Some (image, open, OState (os_out o) rest (os_word_start o))
  | _ => None
  end.

Lemma bunpush_opush :
  forall k m o, bunpush (opush k m o) = None.
Proof. intros k m [out stk word]. reflexivity. Qed.

Lemma bunpush_bpush :
  forall image o,
    bunpush (bpush image o) =
      Some (image,
        null_span, o).
Proof. intros image [out stk word]. destruct image; reflexivity. Qed.

Lemma bclose_oemit_all :
  forall ns image base,
    bclose (oemit_all ns (bpush image base)) =
      Some (ns, image,
        null_span, base).
Proof.
  intros ns image [out stk word]. unfold bpush. rewrite oemit_all_frame.
  unfold bclose. cbn [os_stk os_out bclose_go fr_out fr_kind oapp].
  rewrite app_nil_r, oresolve_map_rev, List.rev_involutive.
  destruct image; reflexivity.
Qed.

(*
Putting a bracket back as text
------------------------------

A bracket's role is decided long after its label is scanned, so the
literal fallback has to reconstruct source from children that are
already classified.  Three operations do it, and between them they keep
the two invariants the text states carry: pending text never sits on a
`Str`, and no two `Str` nodes are adjacent.

None of the three re-reads a byte.  They rewrite state that is already
built, which is the same family as abandoning a scope. *)

(* Undoing a flush.  The text before a `[` was flushed into the current
   scope when the bracket opened; if the bracket decays to text that
   `Str` has to come back out, or the reconstructed text would flush on
   top of it. *)
Definition opop_str (o : ostate) : string * ostate :=
  match os_stk o with
  | [] =>
      match os_out o with
      | OIn (Node _ [] (Str s)) :: rest =>
          (s, OState rest [] (os_word_start o))
      | _ => (EmptyString, o)
      end
  | f :: fs =>
      match fr_out f with
      | OIn (Node _ [] (Str s)) :: rest =>
          (s, OState (os_out o)
                (Frame (fr_kind f) (fr_marked f) (fr_open f) rest :: fs)
                (os_word_start o))
      | _ => (EmptyString, o)
      end
  end.

(* Children back into the buffer.  A plain `Str` child is text and joins
   it; anything else is emitted, flushing the buffer first.  So emissions
   alternate `Str` and non-`Str` and the seam obligation holds by
   construction -- this is why the fallback needs no merging emission. *)
Fixpoint bflat `{PosPolicy} `{InlineCursor}
  (kids : inlines) (txt : string) (o : ostate) : string * ostate :=
  match kids with
  | [] => (txt, o)
  | Node _ [] (Str s) :: rest => bflat rest (txt ++ s)%string o
  | n :: rest => bflat rest EmptyString (oemit n (flush_text_at txt o))
  end.

(* Text that spans a line break.  A `SoftBreak` is a node, so such text
   cannot go back into the buffer whole.  The three buffers that survive
   `ibreak` need it: a destination, and either kind of attribute spec. *)
Fixpoint bsplit_nl `{PosPolicy} `{InlineCursor}
  (s txt : string) (o : ostate) : string * ostate :=
  match s with
  | EmptyString => (txt, o)
  | String c rest =>
      if Ascii.eqb c nl_char
      then bsplit_nl rest EmptyString
             (oemit (imk_here SoftBreak)
               (flush_text_at txt o))
      else bsplit_nl rest (txt ++ one c)%string o
  end.

(* A closed bracket that turns out to be literal: `[`, the label, `]`. *)
Definition bclosed_lit `{PosPolicy} `{InlineCursor}
  (kids : inlines) (image : bool) (o : ostate)
  : string * ostate :=
  let '(pre, o1) := opop_str o in
  let '(txt, o2) := bflat kids (pre ++ bracket_open image)%string o1 in
  ((txt ++ one rbrack)%string, o2).

(* A span whose spec failed, or that ran out of paragraph: the bracket's
   own literal text, then the `{` and everything the machine read,
   breaks included. *)
Definition bspan_lit `{PosPolicy} `{InlineCursor}
  (kids : inlines) (image : bool) (src : string)
  (o : ostate) : string * ostate :=
  let '(txt, o') := bclosed_lit kids image o in
  bsplit_nl src (txt ++ one lbrace) o'.

(* The same for a spec with no bracket before it, where the pending text
   the spec would have attached to is the buffer it goes back into. *)
Definition battr_lit `{PosPolicy} `{InlineCursor}
  (src txt : string) (o : ostate) : string * ostate :=
  bsplit_nl src (txt ++ one lbrace) o.

(* The byte to the left of the one being dispatched, when a construct
   hands back what it ate as text.  Every fallback puts back a fragment
   headed by the construct's own opening byte, so an empty residue means
   `bsplit_nl` cut the fragment at a newline and that newline is the byte
   in question. *)
Definition blit_prev (t : string) : option ascii := str_last t (Some nl_char).

Definition bref_lit `{PosPolicy} `{InlineCursor}
  (kids : inlines) (image : bool) (label : string)
  (o : ostate) : string * ostate :=
  let '(txt, o') := bclosed_lit kids image o in
  ((txt ++ one lbrack ++ label)%string, o').

(* The destination itself drops the breaks (`parse.ts:612`), which is why
   they are kept as characters until it is known to close. *)
Fixpoint drop_nl (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if Ascii.eqb c nl_char then drop_nl rest else String c (drop_nl rest)
  end.

(* Everything still open when the paragraph ends is abandoned. *)
Fixpoint oflatten `{PosPolicy} (pend : oitems) (stk : list frame)
  (bottom : oitems) : oitems :=
  match stk with
  | [] => oapp pend bottom
  | f :: rest =>
      oflatten (oapp (oapp pend (fr_out f)) [OIn (fr_lit f)])
        rest bottom
  end.

(* Everything a state holds, as items: the open scopes abandoned into the
   one below, with each opener's spelling put back as text.  Splitting
   this out of `ofinish` is what lets a line boundary name the state it
   leaves without resolving it -- a spec may still be waiting. *)
Definition oitems_of `{PosPolicy} (o : ostate) : oitems :=
  oflatten [] (os_stk o) (os_out o).

Definition ofinish `{PosPolicy} (o : ostate) : inlines :=
  oresolve (oitems_of o).

(* What a backtick run closes into.  djot.js keeps this in
   `verbatimType` and decides it retroactively when the closing run
   arrives; we decide it at the opening run, which is the same thing
   because the prefix is already read by then. *)
Inductive vkind : Type := VVerb | VMath (style : math_style).

Definition vnode (vk : vkind) (s : string) : inline :=
  match vk with VVerb => Verbatim s | VMath st => Math st s end.

(* Only a verbatim may take a raw format: djot.js guards the lookahead
   with `verbatimType === "verbatim"` (`inline.ts:850`), so
   `` $`x`{=html} `` is math followed by literal text. *)
Definition vkind_verb (vk : vkind) : bool :=
  match vk with VVerb => true | VMath _ => false end.

(* Every state below that carries pending text carries `prev` with it, and
   `prev` is *the last byte of the source read so far*: `None` at the start
   of a paragraph or of a line, and otherwise the byte the writer typed.

   It is not the last byte of `txt`, which is where a scan would naturally
   look for it.  The buffer holds what will be rendered, and three
   constructs put bytes in it that were never in the source -- an
   unmatched smart quote, an ellipsis and a dash -- so after one of those
   the two differ.  `can_open` and `can_close` read the source
   (`inline.ts:110-112`), so `'` after `a''` opens where a curly quote
   would not, which is what `decay_does_not_hide_the_source_byte` pins.
   Each construct that rewrites the buffer therefore names the byte it
   consumed; the states that hold an undecided prefix (`IBrace`,
   `IDollar`, `IPeriod`, `IDash`, `IBang`) carry the byte from before the
   prefix and name the prefix's own last byte when it resolves. *)
Inductive iscan : Type :=
  (* accumulating literal text; `esc` is a pending backslash *)
  | IText (esc : bool) (txt : string) (prev : option ascii) (o : ostate)
  (* a backslash followed by a run of spaces and tabs, whose role the
     next byte decides: the end of the line makes the whole run a hard
     break, and anything else makes the first byte a non-breaking space
     (or, if it was a tab, a literal backslash).  `ws` is that run, never
     empty.  It has to be a state for the same reason `IDollar` does --
     the decision needs a byte the buffer has not seen yet -- and the run
     is kept rather than counted because only its *first* byte decides,
     while the rest is ordinary text. *)
  | IEscWs (ws : string) (txt : string) (prev : option ascii) (o : ostate)
  (* a `{` whose role the next byte decides: open marker, or text *)
  | IBrace (txt : string) (prev : option ascii) (o : ostate)
  (* a delimiter being spelled; `before` is the byte to its left, which
     is what decides whether it may close, and -- for a row whose bare
     opener needs a word boundary -- whether it may open.  Kept as the
     byte rather than as a predicate of it, because two rows can ask two
     different questions of it.  `extra` counts the row's characters that
     have arrived
     *after* the first, so the token so far is `S extra` of them: while
     that is short of `dwidth` the token is still being spelled, and once
     it reaches `dwidth` the token is complete and the next byte decides
     its role.  Counting from the second character rather than the first
     is what keeps the state from holding an empty token.

     `marked` says the token is the one after a `{`.  Its *role* needs no
     byte after it -- upstream forces `can_open` and blocks `can_close`
     -- but the side its decay would take does need one, because a `}`
     right after it flips the row's default.  So a complete marked token
     waits here too, and the byte that arrives pushes the scope and is
     then dispatched into it; only `fr_src` ever learns which side it
     chose.  What such a state decays to keeps the `{`. *)
  | IDelim (k : dstyle) (extra : nat) (txt : string) (before : option ascii)
           (marked : bool) (o : ostate)
  (* counting an opening backtick run.  `vk` is what the run will close
     into: a `$` or `$$` immediately before it makes the span math
     instead of verbatim, which is djot.js's `verbatimType`
     (`inline.ts:196-210`) and the reason math is a mode rather than a
     construct of its own. *)
  | IOpen (n : nat) (vk : vkind) (o : ostate)
  (* inside a width-`n` verbatim, with `run` unresolved trailing ticks *)
  | IVerb (n run : nat) (txt : string) (vk : vkind) (o : ostate)
  (* one or two dollars whose role the next byte decides: a backtick run
     makes them a math prefix, anything else makes them text.  A state
     rather than a look-back into the buffer, because an *escaped* `$`
     must not count and the buffer cannot tell the two apart -- the same
     reason `!` has `IBang`. *)
  | IDollar (two : bool) (txt : string) (prev : option ascii) (o : ostate)
  (* one or two periods whose role the next byte decides: a third makes
     the three an ellipsis, anything else makes them text.  `IDollar`'s
     shape exactly, and for `IDollar`'s reason -- an escaped `\.` must not
     count towards the run, and the text buffer cannot tell it from a
     bare one. *)
  | IPeriod (two : bool) (txt : string) (prev : option ascii) (o : ostate)
  (* a run of `n` hyphens whose cut into dashes the next byte decides.
     Unlike `IPeriod` the run is unbounded, and unlike every other run in
     this scanner it is not a delimiter token: `dashes` cuts it by
     arithmetic and the result is text.  The one byte that is not just
     the run's end is `}`, which takes the last hyphen back for a delete
     closer -- djot.js's `hyphens--` (`inline.ts:520`). *)
  | IDash (n : nat) (txt : string) (prev : option ascii) (o : ostate)
  (* a `!` whose role the next byte decides: `[` opens an image, and
     anything else makes it text.  An *escaped* `!` never reaches here,
     which is what keeps `\![a](u)` a link. *)
  | IBang (txt : string) (prev : option ascii) (o : ostate)
  (* a `]` whose role the next byte decides: `(` enters a destination,
     `[` a reference, `{` a span, and anything else leaves the `]` as
     text with the bracket scope still open, so a later `]` can close it
     -- `[u]b](c)` is a link labelled `u]b` (`inline.ts:401-440`, where
     every other byte returns null).  Nothing is closed here, then:
     `txt` is the text pending when the `]` arrived, still unflushed, and
     `o` is the scope stack untouched. *)
  | IClosed (txt : string) (o : ostate)
  (* inside the second bracket of `[text][label]`.  The label is source
     text, not inline content: upstream's `strMatches` retroactively
     flattens everything in this region before building the reference. *)
  (* A closed bracket followed by `{`: a span, if the spec parses.  The
     spec is read with the same machine block attributes use, fed a byte
     at a time; `src` is what it has eaten, kept so the whole region can
     be put back as text when the machine fails.  `image` is carried only
     for that reconstruction -- a span ignores it, so `![x]{.a}` is a `!`
     followed by a span. *)
  | ISpan (kids : inlines) (image : bool) (open : span)
          (p : aparser) (src : string)
          (o : ostate)
  (* An attribute spec, which attaches to whatever precedes it.  `txt` is
     the text pending when the `{` arrived and, on success, the thing the
     spec attaches to.  `sh` is the ordinary interpretation of the same
     source, advanced with attribute recognition off and selected if the
     candidate never closes. *)
  | IAttr (p : aparser) (src : string) (txt : string) (prev : option ascii)
          (sh : iscan) (o : ostate)
  | IReference (kids : inlines) (image : bool) (open : span)
          (label : string) (o : ostate)
  (* inside a `[^`.  The label is raw source, not inline content: djot.js
     decides note-ness at the `]` and then destroys every match made
     inside the brackets (`inline.ts:363-372`), which is the *discard*
     disposition [[260811.inline-parser]] §2.2 named.  Reading the label
     as source from the start is the same thing arrived at one byte
     earlier, and it is the only way we can spell it -- we do not keep
     source text beside classified nodes.
     `esc` is a pending backslash, which protects a `]` without being
     decoded: `[^a\]b]` labels `a\]b`.  `image` is what the bracket this
     took back was opened with, kept only to spell the literal
     fallback. *)
  | INote (esc image : bool) (label : string) (open : span) (o : ostate)
  (* inside a `](`.  `depth` counts unclosed inner parentheses, `dst`
     accumulates the destination with its escapes decoded, and `esc` is a
     pending backslash, as in text mode.  A destination survives a line
     break, so this is the second state `ibreak` carries across one.

     Two readings of the same bytes run here, because upstream keeps only
     one and decides between them at the end.  `kids`, `dst` and `o` are
     the destination reading, used by the balanced `)` and nothing else.
     `sh` is the ordinary one -- the same scanner, fed the same bytes,
     inside the `FKDest` scope this state opened -- and it is what the
     end of the paragraph keeps, since upstream turns the region literal
     only *at* the close (`inline.ts:470`).  Neither is a replay of the
     other: both advance on each byte, and the byte that ends the state
     picks one. *)
  | IDest (kids : inlines) (image : bool) (open : span)
          (esc : bool) (depth : nat) (dst : string)
          (sh : iscan) (o : ostate)
  (* inside a `<`, holding the region read so far.  The region is raw
     source, so a backtick or a
     delimiter inside a *successful* autolink is content
     (`<a:b`c>` links to ``a:b`c``), which is only true because nothing
     in here is dispatched.

     `txt` is the text pending when the `<` arrived, kept because a
     candidate that fails is put back as literal text.  djot.js instead
     scans a failed candidate as ordinary inline content.  The current
     state does not reproduce that recovery, but an ordinary-inline
     shadow could do so without replay; see `.project/no-backtracking.md`. *)
  | IAuto (src txt : string) (o : ostate)
  (* a verbatim span that closed onto a `{`, holding its content and the
     spec source read since.  The `Verbatim` node is deliberately *not*
     emitted yet: which node this is -- `Verbatim` or `RawInline` -- is
     what the spec decides, and carrying the text is cheaper than
     emitting one and rewriting it.

     Only a verbatim reaches here, never math: djot.js tests
     `verbatimType` at the closer (`inline.ts:850`) and so does the arm
     that builds this. *)
  | IRaw (spec txt : string) (o : ostate).

(* The one position in which the table does not get the byte: right
   inside a bracket that has just opened, where a `^` marks a footnote
   rather than a superscript. *)
Definition note_pos (txt : string) (prev : option ascii) : bool :=
  (negb (nonempty_str txt)
   && match prev with Some p => Ascii.eqb p lbrack | None => false end)%bool.

(* One byte in text mode.  The delimiter arm is a lookup, not six
   branches, for the reason the table's own comment gives.

   `prev` is the byte to the left of `c` *as the source spells it*, which
   is what `can_open` and `can_close` read (`inline.ts:110-112`).  It is
   not the last byte of `txt`: a decayed quote, an ellipsis and a dash
   put characters into the buffer that were never in the source, and
   after one of those `dopens_after` has to see the `'` or the `-` that
   was written rather than the `’` or the `–` that will be rendered.
   Every state carrying pending text keeps this field to the same rule --
   see `iscan`. *)
Definition ilead `{PosPolicy} `{InlineCursor}
  (c : ascii) (txt : string) (prev : option ascii) (o : ostate)
  : iscan :=
  if is_bslash c then IText true txt (Some c) o
  else if is_tick c then IOpen 1 VVerb (flush_text_at txt o)
  else if Ascii.eqb c dollar then IDollar false txt prev o
  else if Ascii.eqb c period then IPeriod false txt prev o
  (* The hyphen, like the footnote marker, is claimed by position rather
     than by the table: a run of them is smart dashes whatever row the
     table spells with `-`, and the delete row is reached from `{` on the
     left (through `IBrace`) or from `}` on the right (through `IDash`).
     `needs_escape` claims it unconditionally for exactly this reason. *)
  else if Ascii.eqb c hyphen then IDash 1 txt prev o
  else if Ascii.eqb c lbrace then IBrace txt prev o
  (* A `[` opens a scope on the same stack the delimiters use, so their
     relative order is kept and the label needs no second parser.  A `]`
     decides nothing on its own -- it hands the pending text to
     `IClosed`, which closes the innermost bracket scope only if the byte
     after it makes a construct. *)
  else if Ascii.eqb c bang then IBang txt prev o
  (* A `<` opens an autolink candidate, which is neither a scope nor a
     lookahead: it accumulates the region and decides at the `>`.  The
     pending text stays pending, since a candidate that fails hands it
     back with the `<` on the end. *)
  else if Ascii.eqb c lt then IAuto EmptyString txt o
  else if Ascii.eqb c lbrack
  then IText false EmptyString (Some lbrack)
         (bpush false (flush_text_at txt o))
  else if Ascii.eqb c rbrack then IClosed txt o
  (* A `^` right inside a bracket that has just opened marks a footnote.
     djot.js reads the byte after the opener when the `]` arrives
     (`inline.ts:361`) and then discards every match made in between, so
     taking the bracket back here and reading the label as source is the
     same verdict one byte earlier -- and it is the only way we can spell
     the label, since we keep no source beside classified nodes.
     Written as a guard on `bunpush` rather than as a claim about the
     stack, so a `^` anywhere else falls through to the table, where it
     is the superscript row as it always was. *)
  else match (if (Ascii.eqb c hat && note_pos txt prev && notes_enabled)%bool
              then bunpush o else None) with
       | Some (image, open, o') => INote false image EmptyString open o'
       | None =>
           match dstyle_of c with
           | Some k => IDelim k 0 txt prev false o
           | None =>
               IText false (txt ++ one c)%string (Some c)
                 (remember_word_start c o)
           end
       end.

(* The ordinary reading of a `](`, as a state.  The bracket's opener is
   pushed back -- as `FKDest`, so a delimiter closer cannot reach past it
   -- and the label goes into it as text, through `bflat`, which keeps a
   classified child classified and merges the `Str` seam by
   construction.  The two bytes that opened the destination are the head
   of the buffer, so a spec that attaches here attaches to `[u](a` whole,
   as upstream's does.

   `fr_src` supplies the `[` at the flatten, not this, which is why the
   frame is pushed rather than the byte written. *)
Definition idest_open `{PosPolicy} `{InlineCursor}
  (kids : inlines) (image : bool) (open : span)
  (o : ostate) : iscan :=
  let '(txt, o') := bflat kids EmptyString (dpush image open o) in
  IText false (txt ++ one rbrack ++ one lparen)%string (Some lparen) o'.

Definition null {A} (l : list A) : bool :=
  match l with [] => true | _ => false end.

(* The ellipsis and the two dashes, as UTF-8.  Three bytes each, like the
   curly quotes, and nothing downstream looks inside. *)
Definition ellipsis : string :=
  String "226"%char (String "128"%char (String "166"%char EmptyString)).
Definition endash : string :=
  String "226"%char (String "128"%char (String "147"%char EmptyString)).
Definition emdash : string :=
  String "226"%char (String "128"%char (String "148"%char EmptyString)).

Definition periods (two : bool) : string :=
  if two then String period (one period) else one period.

Definition typography_ellipsis : string :=
  if smart_typography then ellipsis else chars period 3.

Fixpoint srep (s : string) (n : nat) : string :=
  match n with O => EmptyString | S m => (s ++ srep s m)%string end.

(* How djot.js cuts a run of `n` hyphens (`inline.ts:526-550`): a run
   divisible by three is all em dashes and an even one is all en dashes,
   and otherwise it takes em dashes greedily and finishes with one or two
   en dashes.  A lone hyphen is literal.

   djot.js spells this as a loop with the recursive step duplicated
   across four branches.  Here it is the arithmetic that loop computes,
   for the reason [[project-engineering-lessons#A hang or a sudden
   slowdown is the definition's shape, not the proof]] gives: a
   four-branch recursion has no normal form at an unknown `n`, so every
   `Compute` would pass while every general lemma stayed unprovable. *)
Definition dash_counts (n : nat) : nat * nat * nat :=
  if Nat.eqb (Nat.modulo n 3) 0 then (Nat.div n 3, 0, 0)
  else if Nat.eqb (Nat.modulo n 2) 0 then (0, Nat.div n 2, 0)
  else if Nat.eqb n 1 then (0, 0, 1)
  else if Nat.eqb (Nat.modulo n 6) 5 then (Nat.div (n - 2) 3, 1, 0)
  else (Nat.div (n - 4) 3, 2, 0).

Definition dashes (n : nat) : string :=
  let '(em, en, lit) := dash_counts n in
  (srep emdash em ++ srep endash en ++ chars hyphen lit)%string.

Definition typography_dashes (n : nat) : string :=
  if smart_typography then dashes n else chars hyphen n.

(* The counts pinned on the runs that decide the arithmetic: the two
   homogeneous cases, the two remainders, and the lone hyphen. *)
Example dashes_1 : dashes 1 = one hyphen. Proof. reflexivity. Qed.
Example dashes_2 : dashes 2 = endash. Proof. reflexivity. Qed.
Example dashes_3 : dashes 3 = emdash. Proof. reflexivity. Qed.
Example dashes_4 : dashes 4 = (endash ++ endash)%string. Proof. reflexivity. Qed.
Example dashes_5 : dashes 5 = (emdash ++ endash)%string. Proof. reflexivity. Qed.
Example dashes_7 :
  dashes 7 = (emdash ++ endash ++ endash)%string. Proof. reflexivity. Qed.
Example dashes_13 :
  dashes 13 = (emdash ++ emdash ++ emdash ++ endash ++ endash)%string.
Proof. reflexivity. Qed.

(* The dollars a pending prefix is holding, when they turn out to be
   text. *)
Definition dollars (two : bool) : string :=
  if two then (one dollar ++ one dollar)%string else one dollar.

(* A candidate that failed is its own source: the `<`, what it ate, and
   whatever pended before it.  One string rather than a state, because
   the byte that killed it still has to be dispatched. *)
Definition auto_lit (src txt : string) : string :=
  (txt ++ String lt src)%string.

(* A slice boundary in the ordinary reading of a candidate's region.
   djot.js re-feeds that region on failure, cut into slices ending at
   every byte of `reSpecial` (`inline.ts:67`), so a matcher whose loop is
   bounded by the slice end cannot see past the byte it starts on: a run
   of `-` or `.` never reaches the length that would make it a dash or an
   ellipsis, a `{` never marks the delimiter after it, a `]` never finds
   its destination, an autolink's region never reaches the `>` that would
   resolve it, and a `\\` escapes nothing.  (`IEscWs`
   is not here because it cannot arise: the escape it continues has been
   settled at the boundary before it.)  What crosses the boundary is what
   lives in the parser rather than in the slice -- an open delimiter, a
   verbatim, a math prefix that peeks at the byte after it -- which is why
   `IDelim`, `IOpen`, `IVerb` and `IDollar` are not here.
   `IBang` is not either: `!` is not one of the special bytes, so it is
   never the byte a slice ends on. *)
Definition islice_end (st : iscan) : iscan :=
  match st with
  | IText true txt _ o => IText false (txt ++ one bslash)%string (Some bslash) o
  | IBrace txt _ o => IText false (txt ++ one lbrace)%string (Some lbrace) o
  | IPeriod two txt _ o =>
      IText false (txt ++ periods two)%string (Some period) o
  | IDash n txt _ o =>
      IText false (txt ++ typography_dashes n)%string (Some hyphen) o
  | IClosed txt o => IText false (txt ++ one rbrack)%string (Some rbrack) o
  | IAuto src txt o =>
      IText false (auto_lit src txt) (blit_prev (auto_lit src txt)) o
  | _ => st
  end.

(* Where a finished spec goes: into the scope, as a marker, with the
   pending text flushed in front of it so that the run it will attach to
   is the item immediately below.  `oresolve` settles it -- see
   `oattach_list` for the rule and for the one case we do not follow
   djot.js on. *)
Definition iattr_mark `{PosPolicy} `{InlineCursor}
  (src : string) (a : attr) (txt : string) (o : ostate) : iscan :=
  let spec_start := spot_before cursor_start (String lbrace src) in
  let spec := pspan (SrcSpan spec_start cursor_stop) in
  IText false EmptyString (Some rbrace)
    (omark a spec (flush_text_to_at spec_start txt o)).

(* One byte of an inline attribute spec, read with the machine block
   attributes use.  `sh` has already consumed the same byte as ordinary
   inline input.  Failure selects it; success discards it; otherwise both
   readings remain live -- and the one kept is stored at a slice
   boundary, since the byte it has just read is where its slice ends. *)
Definition iattr_feed `{PosPolicy} `{InlineCursor}
  (c : ascii) (p : aparser) (src txt : string)
  (prev : option ascii) (sh : iscan) (o : ostate) : iscan :=
  let p' := astep p c in
  if ap_failed p'
  then sh
  else if ap_done p'
  then iattr_mark src (ap_attrs p') txt o
  else IAttr p' (src ++ one c)%string txt prev (islice_end sh) o.

(* A marked open with `S extra` characters of its token in hand.  Its
   role is not in doubt -- djot.js forces `can_open` and blocks
   `can_close` for a marked delimiter -- but its *spelling when abandoned*
   is, because a `}` right after it flips the row's decay side.  So the
   push waits for one byte whatever the width, and `istep` and `iresolve`
   are where it happens.  `before` is `None` throughout: the branch that
   would read it is the one this never reaches. *)
Definition idelim_marked (k : dstyle) (extra : nat) (txt : string)
  (o : ostate) : iscan := IDelim k extra txt None true o.

(* The push itself, once the byte after a completed marked opener is
   known (or known not to exist). *)
Definition oopen_marked `{PosPolicy} `{InlineCursor}
  (k : dstyle) (cm : bool) (txt : string)
  (o : ostate) : ostate :=
  let open := dtoken_span k true in
  opush_at k true cm open (flush_text_to_at (span_start open) txt o).

Definition idelim_open_marked `{PosPolicy} `{InlineCursor}
  (k : dstyle) (cm : bool) (txt : string)
  (o : ostate) : iscan :=
  IText false EmptyString (Some (dchar k)) (oopen_marked k cm txt o).

(* What a token that never finished decays to: the row's characters
   received so far, with the `{` of a marked open back in front of
   them. *)
Definition idelim_run (k : dstyle) (extra : nat) (marked : bool) : string :=
  ((if marked then one lbrace else EmptyString)
     ++ chars (dchar k) (S extra))%string.

Lemma idelim_run_nonempty :
  forall k extra marked, nonempty_str (idelim_run k extra marked) = true.
Proof. intros k extra []; reflexivity. Qed.

(* Resolving a `{`: an open marker if a delimiter follows, an attribute
   candidate if that capability is enabled, and ordinary text otherwise. *)
Definition ibrace_step_at `{PosPolicy} `{InlineCursor}
  (attrs_enabled : bool) (c : ascii) (txt : string)
  (prev : option ascii) (o : ostate) : iscan :=
  match dstyle_of c with
  | Some k => idelim_marked k 0 txt o
  | None =>
      if attrs_enabled
      then iattr_feed c ap_init EmptyString txt prev
             (ilead c (txt ++ one lbrace)%string (Some lbrace) o) o
      (* The spec's own immediate-failure path, taken before the first
         byte is read: `{` goes back into the text and this byte is
         dispatched afresh. *)
      else let '(t, o') := battr_lit EmptyString txt o in
           ilead c t (blit_prev t) o'
  end.

Definition ibrace_step `{PosPolicy} `{InlineCursor}
  (c : ascii) (txt : string) (prev : option ascii)
  (o : ostate) : iscan :=
  ibrace_step_at inline_attrs_enabled c txt prev o.

(* A span ignores the image marker: `![x]{.a}` is a literal `!` followed
   by a span.  The `!` was never flushed -- the bracket frame records it
   and `fr_src` puts it back on the literal path -- so the span path
   has to emit it here, and it merges with any `Str` already at the tip
   the same way, since `flush_text` alone would leave two adjacent. *)
Definition ospan_bang `{PosPolicy} `{InlineCursor}
  (image : bool) (o : ostate) : ostate :=
  if image
  then let '(pre, o1) := opop_str o in
       flush_text_at (pre ++ one bang)%string o1
  else o.

(* One byte into an open span's spec.  `ADone` arrives on the `}`, so the
   node is built here with no byte left over.  On `AFail` the region up to
   but not including the failing byte becomes text and that byte is
   dispatched afresh: djot.js resumes its scan there, so `[s]{bad*x*y` is
   `[s]{bad`, a strong `x`, and `y`. *)
Definition ispan_feed `{PosPolicy} `{InlineCursor}
  (c : ascii) (kids : inlines) (image : bool) (open : span)
  (p : aparser) (src : string) (o : ostate) : iscan :=
  let p' := astep p c in
  if ap_failed p'
  then let '(txt, o') := bspan_lit kids image src o in
       ilead c txt (blit_prev txt) o'
  else if ap_done p'
  then let spec_start := spot_before cursor_start (String lbrace src) in
       let spec := SrcSpan spec_start cursor_stop in
       IText false EmptyString (Some rbrace)
         (oemit
           (add_inline_role RAttrSpec spec
             (Node (mkpos (inline_prov (span_start open) spec_start))
               (ap_attrs p') (Span kids)))
           (ospan_bang image o))
  else ISpan kids image open p' (src ++ one c)%string o.

(* Resolving a `!`: an image opener if a `[` follows, text otherwise.
   The `!` is *not* flushed with the text before it -- it is the opener's
   own source, and `fr_src` puts it back if the bracket decays. *)
(* One byte of a footnote label.  The `]` is the only byte with a role,
   and a backslash defers it once -- without being decoded, since the
   label is source and djot.js labels `[^a\]b]` with the backslash still
   in it. *)
Definition inote_step `{PosPolicy} `{InlineCursor}
  (c : ascii) (esc image : bool) (label : string) (open : span)
  (o : ostate) : iscan :=
  if esc then INote false image (label ++ one bslash ++ one c)%string open o
  else if is_bslash c then INote true image label open o
  else if Ascii.eqb c rbrack
  then IText false EmptyString (Some rbrack)
         (oemit (imk (span_start open) cursor_stop
                    (FootnoteReference (normalize_label label)))
            (ospan_bang image o))
  else INote false image (label ++ one c)%string open o.

(* One byte of an autolink candidate.  Three bytes end it: the `>` that
   may resolve it, and the whitespace or second `<` that the region may
   not contain.  Everything else is region, raw -- no escape is decoded
   and no construct is dispatched, which is what makes the region of a
   *successful* autolink literal.

   The `>` of a failed candidate is dispatched rather than appended, so
   that this arm has one exit for every byte that is not region.

   `auto_body_ok` asks more than the `>` has to: the three exclusions
   are invariants of the mode, since a byte that breaks one leaves it.
   It is spelled in full so that the test *is* `ci_ok`'s, which is what
   makes the scan inversion a rewrite rather than an argument. *)
Definition iauto_step `{PosPolicy} `{InlineCursor}
  (c : ascii) (src txt : string) (o : ostate) : iscan :=
  if (Ascii.eqb c gt && auto_body_ok src && auto_kind_ok src)%bool
  then let start := spot_before cursor_start (String lt src) in
       IText false EmptyString (Some gt)
         (oemit (imk start cursor_stop (auto_node src))
           (flush_text_to_at start txt o))
  else if (Ascii.eqb c gt || is_ws c || Ascii.eqb c lt)%bool
  then ilead c (auto_lit src txt) (blit_prev (auto_lit src txt)) o
  else IAuto (src ++ one c)%string txt o.

(* One byte of a raw-format spec.  The `}` decides it; the pattern's
   excluded bytes end it; anything else is spec.

   A failed spec is put back with the verbatim it followed, and there the
   two cases differ.  With nothing read yet the `{` had no `=` after it,
   so the ordinary attribute path is what should have run and does --
   this is exactly the state the closer built before raw existed.  With
   an `=` read the region cannot parse as attributes at all, so it is
   text. *)
Definition iraw_lit (spec : string) : string :=
  (String lbrace spec)%string.

Definition iraw_step_at `{PosPolicy} `{InlineCursor}
  (attrs_enabled : bool) (c : ascii) (spec txt : string)
  (o : ostate) : iscan :=
  let vstop := spot_before cursor_start (String lbrace spec) in
  if (Ascii.eqb c rbrace && raw_spec_ok spec)%bool
  then if raw_inline_enabled
       then IText false EmptyString (Some rbrace)
              (oemit (imk (text_start o) cursor_stop
                        (RawInline (raw_format spec) txt)) o)
       else ilead c (iraw_lit spec) (blit_prev (iraw_lit spec))
              (oemit (imk (text_start o) vstop (Verbatim txt)) o)
  else if (match spec with
           (* the `=` is the pattern's second character, so anything else
              here is not a candidate at all -- and must behave exactly
              as the `{` did before raw existed, since every canonical
              delimiter is spelled `{`-first *)
           | EmptyString => negb (Ascii.eqb c eqchar)
           | _ => (Ascii.eqb c rbrace || raw_stop c)%bool
           end)
  then let closed := oemit (imk (text_start o) vstop (Verbatim txt)) o in
       match spec with
       | EmptyString =>
           ibrace_step_at attrs_enabled c EmptyString (Some tick) closed
       | _ => ilead c (iraw_lit spec) (blit_prev (iraw_lit spec)) closed
       end
  else IRaw (spec ++ one c)%string txt o.

Definition iraw_step `{PosPolicy} `{InlineCursor}
  (c : ascii) (spec txt : string) (o : ostate) : iscan :=
  iraw_step_at inline_attrs_enabled c spec txt o.

(* A label that never closed is its own source: the bracket it took back,
   the marker, and what it had eaten.  `opop_str` reabsorbs the `Str`
   that the bracket's own `flush_text` emitted, so the reconstruction is
   one run and `no_adjacent_str` survives -- the move `bclosed_lit`
   makes, for the same reason. *)
Definition bnote_lit `{PosPolicy} `{InlineCursor}
  (esc image : bool) (label : string) (o : ostate)
  : string * ostate :=
  let '(pre, o1) := opop_str o in
  ((pre ++ bracket_open image ++ one hat ++ label
       ++ (if esc then one bslash else EmptyString))%string, o1).

Definition ibang_step `{PosPolicy} `{InlineCursor}
  (c : ascii) (txt : string) (prev : option ascii)
  (o : ostate) : iscan :=
  if Ascii.eqb c lbrack
  then IText false EmptyString (Some lbrack)
         (bpush true
            (flush_text_to_at (previous_spot cursor_start) txt o))
  else ilead c (txt ++ one bang)%string (Some bang) o.

(* Resolving an unbraced delimiter, once the byte after it has arrived
   (or not, at the end of a line: `inone`).  Closing wins over opening,
   as in djot.js, and a `}` immediately after forces the close. *)
Definition idelim_lit (k : dstyle) (txt : string) (marker : bool) : string :=
  (txt ++ ddecay_str k false marker)%string.

(* And the source byte it ends on, which `ddecay_str` does not spell for a
   smart quote: `'` is written and `’` is what lands in the buffer. *)
Definition idelim_lit_prev (k : dstyle) (marker : bool) : option ascii :=
  Some (if marker then rbrace else dchar k).

Definition idelim_done `{PosPolicy} `{InlineCursor}
  (k : dstyle) (txt : string) (before : option ascii)
  (marker : bool) (next : option ascii) (o : ostate) : iscan :=
  if (dbare k before && negb marker && nonspace_at next)%bool
  then IText false EmptyString (Some (dchar k))
         (opush k false
            (flush_text_to_at (span_start (dtoken_span k false)) txt o))
  else IText false (idelim_lit k txt marker) (idelim_lit_prev k marker) o.

Definition idelim_resolve `{PosPolicy} `{InlineCursor}
  (k : dstyle) (txt : string) (before : option ascii)
  (marker : bool) (next : option ascii) (o : ostate) : iscan :=
  if (nonspace_at before || marker)%bool
  then match oclose k marker (if marker then cursor_stop else cursor_start)
              (flush_text_to_at (span_start (dtoken_span k false)) txt o) with
       | Some o' =>
           IText false EmptyString
             (Some (if marker then rbrace else dchar k)) o'
       (* a barred opener is the one failure that does not offer the
          token as an opener in its turn *)
       | None =>
           if oclose_barred k marker o
           then IText false (idelim_lit k txt marker) (idelim_lit_prev k marker) o
           else idelim_done k txt before marker next o
       end
  else idelim_done k txt before marker next o.

(* Resolving a `$`: another `$` widens the prefix to display math, a
   backtick run opens the span it prefixes, and anything else makes the
   dollars text.  A third `$` keeps the last two, which is djot.js
   popping exactly two matches, so the extra one is flushed here.

   With math off the backtick takes the same exit as any other byte: the
   dollars join the pending text and `ilead` opens the verbatim they were
   about to prefix.  So a disabled prefix is not dropped and not
   announced -- it is the code span it sits on, with its dollars as
   literal text before it. *)
Definition idollar_step `{PosPolicy} `{InlineCursor}
  (c : ascii) (two : bool) (txt : string)
  (prev : option ascii) (o : ostate) : iscan :=
  if Ascii.eqb c dollar
  then (if two then IDollar true (txt ++ one dollar)%string prev o
        else IDollar true txt prev o)
  else if (is_tick c && math_enabled)%bool
  then IOpen 1 (VMath (if two then DisplayMath else InlineMath))
         (flush_text_to_at (spot_before cursor_start (dollars two)) txt o)
  else ilead c (txt ++ dollars two)%string (Some dollar) o.

(* Three periods are one ellipsis and any other run is literal, so the
   state counts to two and the third byte decides (`inline.ts:343`).  A
   run of four is an ellipsis and a period, which falls out of resolving
   at the third and starting again. *)
Definition iperiod_step `{PosPolicy} `{InlineCursor}
  (c : ascii) (two : bool) (txt : string)
  (prev : option ascii) (o : ostate) : iscan :=
  if Ascii.eqb c period
  then (if two then
          IText false
            (txt ++ typography_ellipsis)%string
            (Some c) o
        else IPeriod true txt prev o)
  else ilead c (txt ++ periods two)%string (Some period) o.

(* A run of hyphens ends at the first byte that is not one.  A `}` is the
   exception, and the only place the dash rule and the delete row meet:
   the run gives its last hyphen back to be a close marker, and what is
   left is cut into dashes.  When no row is spelled with a hyphen there
   is nothing to close and the two bytes are text, which is djot.js's
   `hyphens === 0` branch. *)
Definition idash_step `{PosPolicy} `{InlineCursor}
  (c : ascii) (n : nat) (txt : string)
  (prev : option ascii) (o : ostate) : iscan :=
  if Ascii.eqb c hyphen then IDash (S n) txt prev o
  else if Ascii.eqb c rbrace
  then match dstyle_of hyphen with
       | Some k =>
           (* the row takes its whole token back, not one hyphen: djot's
              rows are all one character wide, but the table is a
              parameter and `iscan_marked_close_step` is stated for every
              row, so the arithmetic has to be the row's *)
           if Nat.leb (dwidth k) n
           then idelim_resolve k
                  (txt ++ typography_dashes (n - dwidth k))%string
                  None true (Some c) o
           else IText false (txt ++ typography_dashes n ++ one rbrace)%string
                  (Some rbrace) o
       | None => IText false (txt ++ typography_dashes n ++ one rbrace)%string
                   (Some rbrace) o
       end
  else ilead c (txt ++ typography_dashes n)%string (Some hyphen) o.

(* No byte follows: the end of a line or of the paragraph.  `IBrace` and
   `IDelim` are the only states this changes, and after it neither
   remains, which is what lets `ibreak` and `ifinish` match on the rest. *)
Definition iresolve `{PosPolicy} `{InlineCursor} (st : iscan) : iscan :=
  match st with
  | IBrace txt _ o => IText false (txt ++ one lbrace)%string (Some lbrace) o
  | IDollar two txt _ o =>
      IText false (txt ++ dollars two)%string (Some dollar) o
  | IPeriod two txt _ o =>
      IText false (txt ++ periods two)%string (Some period) o
  | IDash n txt _ o =>
      IText false (txt ++ typography_dashes n)%string (Some hyphen) o
  | IBang txt _ o => IText false (txt ++ one bang)%string (Some bang) o
  (* A token still being spelled is text: the run ended before the row's
     width was reached. *)
  | IDelim k extra txt before marked o =>
      if Nat.ltb (S extra) (dwidth k)
      then IText false (txt ++ idelim_run k extra marked)%string
             (Some (dchar k)) o
      else if marked then idelim_open_marked k false txt o
      else idelim_resolve k txt before false None o
  (* The newline is an ordinary byte to djot.js, and none of the three
     that make a construct, so `[a]` at the end of a line leaves the `]`
     as text and the scope open. *)
  | IClosed txt o => IText false (txt ++ one rbrack)%string (Some rbrack) o
  | _ => st
  end.

(* What a backslash and a whitespace run decay to when the line does not
   end after them.  djot.js tests the byte after the backslash for a
   space and for nothing else (`inline.ts:250`), so a tab leaves the
   backslash literal; either way the decision consumes only the first
   byte of the run and the rest is ordinary text. *)
Definition iescws_resolve `{PosPolicy} `{InlineCursor}
  (ws txt : string) (prev : option ascii)
  (o : ostate) : string * option ascii * ostate :=
  match ws with
  | String c rest =>
      if Ascii.eqb c " "%char
      then (rest, str_last rest (Some c),
            oemit
              (imk (spot_before cursor_start ws)
                 (spot_before cursor_start rest) NonBreakingSpace)
              (flush_text_to_at
                 (spot_before cursor_start (one bslash ++ ws)%string) txt o))
      else ((txt ++ one bslash ++ ws)%string, str_last ws prev, o)
  (* unreachable: `IEscWs` is only ever built with a byte in hand.  Spelt
     as the bare backslash anyway, so the state's own source survives on
     every path out of it. *)
  | EmptyString => ((txt ++ one bslash)%string, Some bslash, o)
  end.

(* The line ended after the backslash.  djot.js trims the whitespace that
   preceded it off the last `str` match (`inline.ts:222-237`); the run
   pending here is that match, so the trim is local. *)
Definition iesc_hard `{PosPolicy} `{InlineCursor}
  (ws txt : string) (o : ostate) : ostate :=
  let kept := strip_trailing_ws txt in
  (* the source between the text and the line end: the whitespace the
     trim dropped, the backslash, and the run after it.  Two lengths per
     hard break, which is per line at worst -- the rule that matters is
     that no `String.length` runs per scanned byte (plan section 8). *)
  let over := S (String.length ws
                 + (String.length txt - String.length kept)) in
  oemit (imk_here HardBreak)
    (flush_text_to_at (spot_plus over cursor_start) kept o).

(* Recursive in exactly one place: a destination advances the ordinary
   reading of its own region, which is this same scanner one scope in. *)
Fixpoint istep_at `{PosPolicy} `{InlineCursor}
  (attrs_enabled : bool) (c : ascii) (st : iscan) : iscan :=
  match st with
  | IText true txt prev o =>
      if is_ws c then IEscWs (one c) txt prev o
      else IText false (txt ++ (if is_punct c then one c
                                else String "\"%char (one c)))%string (Some c) o
  | IEscWs ws txt prev o =>
      if is_ws c then IEscWs (ws ++ one c)%string txt prev o
      else let '(txt', prev', o') := iescws_resolve ws txt prev o in
           ilead c txt' prev' o'
  | IText false txt prev o => ilead c txt prev o
  | IBrace txt prev o => ibrace_step_at attrs_enabled c txt prev o
  | IBang txt prev o => ibang_step c txt prev o
  | IDelim k extra txt before marked o =>
      if Nat.ltb (S extra) (dwidth k)
      then (* still spelling the token: another of the row's characters
              continues it -- and completes a marked one, which opens
              without waiting -- while anything else makes the partial
              run text *)
        (if Ascii.eqb c (dchar k)
         then (if marked then idelim_marked k (S extra) txt o
               else IDelim k (S extra) txt before false o)
         else ilead c (txt ++ idelim_run k extra marked)%string
                (Some (dchar k)) o)
      else if marked
      then (* a completed marked opener: it opens whatever comes next, and
              this byte only chooses the side its decay takes, so it is
              still dispatched *)
        ilead c EmptyString (Some (dchar k))
          (oopen_marked k (Ascii.eqb c rbrace) txt o)
      else
      let marker := Ascii.eqb c rbrace in
      let st' := idelim_resolve k txt before marker (Some c) o in
      (* the `}` of a close marker is consumed with the delimiter; any
         other byte still has to be dispatched *)
      if marker then st'
      else match st' with
           | IText false txt' prev' o' => ilead c txt' prev' o'
           | other => other
           end
  | IDollar two txt prev o => idollar_step c two txt prev o
  | IPeriod two txt prev o => iperiod_step c two txt prev o
  | IDash n txt prev o => idash_step c n txt prev o
  | IOpen n vk o =>
      if is_tick c then IOpen (S n) vk o else IVerb n 0 (one c) vk o
  | IVerb n run txt vk o =>
      if is_tick c then IVerb n (S run) txt vk o
      else if Nat.eqb run n
      (* the byte after the closing run decides whether a raw spec
         follows, which is where djot.js asks it too -- and it asks only
         of a verbatim, so math takes the ordinary path *)
      then (if (Ascii.eqb c lbrace && vkind_verb vk)%bool
            then IRaw EmptyString (trim_verb txt) o
            else ilead c EmptyString (Some tick)
                   (oemit (imk (text_start o) cursor_start
                             (vnode vk (trim_verb txt))) o))
      else IVerb n 0 (txt ++ ticks run ++ one c)%string vk o
  (* The three bytes that make a construct of the bracket close it; every
     other one leaves the scope alone and the `]` in the buffer, which is
     why `bclose` runs here rather than at the `]`.  Its `None` is the
     same fall-through: no bracket was open, so the `]` was text. *)
  | IClosed txt o =>
      match (if (Ascii.eqb c lparen || Ascii.eqb c lbrack
                 || (Ascii.eqb c lbrace && attrs_enabled))%bool
             then bclose (flush_text_to_at (previous_spot cursor_start) txt o)
             else None) with
      | Some (kids, image, open, o') =>
          if Ascii.eqb c lparen
          then IDest kids image open false 0 EmptyString
                 (idest_open kids image open o') o'
          else if Ascii.eqb c lbrack
               then IReference kids image open EmptyString o'
               else ISpan kids image open ap_init EmptyString o'
      | None => ilead c (txt ++ one rbrack)%string (Some rbrack) o
      end
  | ISpan kids image open p src o =>
      ispan_feed c kids image open p src o
  | IAttr p src txt prev sh o =>
      (* The failing byte is not part of the candidate's source, so it
         arrives in the ordinary reading after that source's last slice
         boundary -- which `iattr_feed` has already applied.  This is what
         keeps `{...` three literal periods rather than one ellipsis. *)
      if ap_failed (astep p c)
      then istep_at false c sh
      else iattr_feed c p src txt prev (istep_at false c sh) o
  | INote esc image label open o => inote_step c esc image label open o
  | IAuto src txt o => iauto_step c src txt o
  | IRaw spec txt o => iraw_step_at attrs_enabled c spec txt o
  | IReference kids image open label o =>
      if Ascii.eqb c rbrack
      then let key := match label with
                      | EmptyString => reference_inlines_text kids
                      | _ => label
                      end in
           IText false EmptyString (Some rbrack)
             (oemit (imk (span_start open) cursor_stop
                       (bnode image kids (Reference (normalize_label key)))) o)
      else IReference kids image open (label ++ one c)%string o
  | IDest kids image open true depth dst sh o =>
      IDest kids image open false depth
        (dst ++ (if is_punct c then one c
                 else String bslash (one c)))%string (istep_at attrs_enabled c sh) o
  | IDest kids image open false depth dst sh o =>
      if is_bslash c then IDest kids image open true depth dst
                             (istep_at attrs_enabled c sh) o
      else if Ascii.eqb c lparen
      then IDest kids image open false (S depth) (dst ++ one lparen)%string
             (istep_at attrs_enabled c sh) o
      else if Ascii.eqb c rparen
      then match depth with
           | O =>
               (* the balanced close: the one byte that builds the node,
                  and the one that discards the ordinary reading *)
               IText false EmptyString (Some rparen)
                 (oemit (imk (span_start open) cursor_stop
                           (bnode image kids (Direct (drop_nl dst)))) o)
           | S d => IDest kids image open false d (dst ++ one rparen)%string
                      (istep_at attrs_enabled c sh) o
           end
      else IDest kids image open false depth (dst ++ one c)%string
             (istep_at attrs_enabled c sh) o
  end.

Definition istep `{PosPolicy} `{InlineCursor}
  (c : ascii) (st : iscan) : iscan :=
  istep_at inline_attrs_enabled c st.

(* End of line.  An unclosed verbatim closes here, as djot.js does in
   `getMatches`.  A pending backslash is a hard break, djot.js's reading;
   djoths keeps a literal backslash, a logged disagreement
   (`escapes.test:30`).  It cannot arise from a canonical rendering,
   since `escape_str` never emits a backslash that is not followed by
   punctuation. *)
Definition ifinish_ostate_flat `{PosPolicy} `{InlineCursor}
  (st : iscan) : ostate :=
  match st with
  | IText true txt _ o => iesc_hard EmptyString txt o
  | IEscWs ws txt _ o => iesc_hard ws txt o
  | IText false txt _ o => flush_text_at txt o
  | IOpen n vk o =>
      oemit (imk (text_start o) cursor_start (vnode vk EmptyString)) o
  | IVerb n run txt vk o =>
      oemit (imk (text_start o) cursor_start
               (vnode vk (trim_verb
                  (if Nat.eqb run n then txt else txt ++ ticks run)%string))) o
  (* unreachable: `ifinish_ostate` takes a destination's shadow before it
     gets here, and `iresolve` builds no `IDest` *)
  | IDest _ _ _ _ _ _ _ o => o
  | INote esc image label _ o =>
      let '(txt, o') := bnote_lit esc image label o in flush_text_at txt o'
  (* a candidate the line ended inside is literal: the region may not
     contain a break, so the `>` it wanted can never arrive *)
  | IAuto src txt o => flush_text_at (auto_lit src txt) o
  (* a spec the line ended inside never closed: the verbatim stands and
     the spec source is text after it *)
  | IRaw spec txt o =>
      let spec_start := spot_before cursor_start (String lbrace spec) in
      flush_text_at (iraw_lit spec)
        (oemit (imk (text_start o) spec_start (Verbatim txt)) o)
  | IReference kids image _ label o =>
      let '(txt, o') := bref_lit kids image label o in flush_text_at txt o'
  (* an unclosed span is literal too: there is no next line for its spec
     to close on, and the breaks it did cross are in the source *)
  | ISpan kids image _ _ src o =>
      let '(txt, o') := bspan_lit kids image src o in flush_text_at txt o'
  (* a spec the paragraph ended inside never closed, and its source is
     text: the brace, then what the machine has read since *)
  | IAttr _ src txt _ _ o =>
      let '(t, o') := battr_lit src txt o in flush_text_at t o'
  (* unreachable: `iresolve` leaves no `IBrace`, `IBang`,
     `IDollar`, `IDelim` or `IClosed` *)
  | IBrace _ _ o | IBang _ _ o | IDollar _ _ _ o
  | IPeriod _ _ _ o | IDash _ _ _ o
  | IDelim _ _ _ _ _ o | IClosed _ o => o
  end.

(* An unclosed destination is not literal: upstream turns the region into
   source at the *close*, so a region that never closes keeps the reading
   the ordinary scan gave it, and the `[` and `](` come back out of the
   `FKDest` frame when `oflatten` abandons it. *)
Fixpoint ifinish_ostate `{PosPolicy} `{InlineCursor} (st : iscan) : ostate :=
  match st with
  | IAttr _ _ _ _ sh _ => ifinish_ostate sh
  | IDest _ _ _ _ _ _ sh _ => ifinish_ostate sh
  | _ => ifinish_ostate_flat (iresolve st)
  end.

Definition ifinish_items `{PosPolicy} `{InlineCursor} (st : iscan) : oitems :=
  oitems_of (ifinish_ostate st).

Definition ifinish_rev `{PosPolicy} `{InlineCursor} (st : iscan) : inlines :=
  ofinish (ifinish_ostate st).

Lemma ifinish_rev_items :
  forall st, ifinish_rev st = oresolve (ifinish_items st).
Proof. reflexivity. Qed.

Definition ifinish `{PosPolicy} `{InlineCursor} (st : iscan) : inlines :=
  List.rev (ifinish_rev st).

(* A line boundary inside a paragraph.
   djot.js scans the newline as an ordinary character of the subject, and
   tests it *before* the verbatim mode (`inline.ts:832`), so a span may
   cross a break: `` `a `` / `` b` `` is one code span containing a
   newline, and the same will hold of the delimiter family.  A paragraph
   is therefore one scan with this between its lines, not a scan per
   line.

   Only `IText` ends the line.  Inside a verbatim the newline is content,
   which is why it arrives here as `one nl` rather than closing anything;
   a resolved closing run (`run = n`) is the one case where the span ends
   *at* the break and the newline is the soft break after it. *)
Definition ibreak_flat `{PosPolicy} `{InlineCursor} (st : iscan) : iscan :=
  match st with
  (* A hard break replaces the soft one: it is the break, rendered. *)
  | IText true txt _ o =>
      IText false EmptyString None (oword_reset (iesc_hard EmptyString txt o))
  | IEscWs ws txt _ o =>
      IText false EmptyString None (oword_reset (iesc_hard ws txt o))
  | IText false txt _ o =>
      IText false EmptyString None
        (oword_reset
          (oemit (imk_here SoftBreak)
            (flush_text_at txt o)))
  | IOpen n vk o => IVerb n 0 nl vk o
  | IVerb n run txt vk o =>
      if Nat.eqb run n
      then IText false EmptyString None
             (oword_reset
                (oemit (imk_here SoftBreak)
                  (oemit (imk (text_start o) cursor_start
                            (vnode vk (trim_verb txt))) o)))
      else IVerb n 0 (txt ++ ticks run ++ nl)%string vk o
  (* unreachable, as in `ifinish_ostate_flat` *)
  | IDest _ _ _ _ _ _ _ _ as st' => st'
  (* A label crosses a break and the newline is whitespace to
     `normalize_label`, so `[^a` / `b]` is one reference to `a b`. *)
  | INote esc image label open o =>
      INote false image
        (label ++ (if esc then one bslash else EmptyString) ++ nl)%string open o
  | IReference kids image open label o =>
      IReference kids image open (label ++ nl)%string o
  (* and the break itself is the soft one, exactly as it is for the text
     the candidate decays to *)
  | IAuto src txt o =>
      IText false EmptyString None
        (oword_reset
          (oemit (imk_here SoftBreak)
            (flush_text_at (auto_lit src txt) o)))
  (* nor does a raw spec: the pattern excludes whitespace, so a break
     ends the candidate exactly as `ifinish` does *)
  | IRaw spec txt o =>
      let spec_start := spot_before cursor_start (String lbrace spec) in
      IText false EmptyString None
        (oword_reset
          (oemit (imk_here SoftBreak)
             (flush_text_at (iraw_lit spec)
               (oemit (imk (text_start o) spec_start (Verbatim txt)) o))))
  (* A span's spec crosses the break too, and the newline is whitespace to
     the machine: `[s]{.a` / `.b}` is one span whose classes merge.  It is
     fed rather than accumulated because the machine is what decides
     whether the break separates two tokens. *)
  | ISpan kids image open p src o =>
      ispan_feed nl_char kids image open p src o
  (* and so does a bare spec, on the same reading: `hi{#i .c` / `k="v"}`
     attaches to `hi`.  No `SoftBreak` is emitted -- the break is inside
     the spec's source, and djot.js's `attributeSlices` swallow it the
     same way. *)
  | IAttr p src txt prev sh o =>
      (* unreachable: `ibreak_at` advances the ordinary reading too *)
      iattr_feed nl_char p src txt prev sh o
  (* unreachable, as in `ifinish_ostate` *)
  | (IBrace _ _ _ | IBang _ _ _ | IDollar _ _ _ _
    | IPeriod _ _ _ _ | IDash _ _ _ _
    | IDelim _ _ _ _ _ _ | IClosed _ _) as st' => st'
  end.

(* A destination crosses the break: djot.js keeps scanning and strips the
   newline from the destination text at the close, so the byte is
   accumulated and dropped later rather than dropped here.  The ordinary
   reading takes the break as the soft one it is, which is why it is
   `ibreak` and not `istep nl` that the shadow gets. *)
Fixpoint ibreak_at `{PosPolicy} `{InlineCursor}
  (attrs_enabled : bool) (st : iscan) : iscan :=
  match st with
  | IAttr p src txt prev sh o =>
      iattr_feed nl_char p src txt prev
        (ibreak_at false sh) o
  | IDest kids image open esc depth dst sh o =>
      IDest kids image open false depth
        (dst ++ (if esc then one bslash else EmptyString) ++ nl)%string
        (ibreak_at attrs_enabled sh) o
  | _ => ibreak_flat (iresolve st)
  end.


Definition ibreak `{PosPolicy} `{InlineCursor} (st : iscan) : iscan :=
  ibreak_at inline_attrs_enabled st.

(* A state that owes nothing to the next line: every construct it has
   seen is resolved, so the boundary just ends the line and `ibreak`
   agrees with `ifinish` on what was emitted.  What fails it is a span
   still open across the break -- an unterminated backtick run, a
   verbatim whose closer has not arrived, or any open scope. *)
Definition iclosed_at (st : iscan) : bool :=
  match st with
  (* a pending backslash is not closed: it owes the *next* byte a hard
     break or a literal, so the line does not end with a soft one *)
  | IText esc _ _ o => (negb esc && null (os_stk o))%bool
  | IEscWs _ _ _ _ => false
  | IOpen _ _ _ => false
  | IVerb n run _ _ o => (Nat.eqb run n && null (os_stk o))%bool
  (* an open destination or an unclosed spec owes the next line;
     `IClosed` cannot appear, since `iresolve` has just turned it into
     text *)
  | IBrace _ _ _ | IAttr _ _ _ _ _ _ | IBang _ _ _ | IDollar _ _ _ _
  | IPeriod _ _ _ _ | IDash _ _ _ _
  | IDelim _ _ _ _ _ _ | IClosed _ _ | ISpan _ _ _ _ _ _
  | INote _ _ _ _ _ | IReference _ _ _ _ _
  | IDest _ _ _ _ _ _ _ _ => false
  (* an autolink candidate owes the next line nothing: the region may not
     hold a break, so the candidate dies at the boundary and what it ate
     is text on this line *)
  | IAuto _ _ o | IRaw _ _ o => null (os_stk o)
  end.

Definition iscan_closed `{PosPolicy} `{InlineCursor} (st : iscan) : bool :=
  iclosed_at (iresolve st).

(* `iresolve` is the end-of-line disposition.  When a byte is known to
   follow, only `IDelim` answers differently, and only about opening:
   `idelim_done` consults that byte and `iresolve` passes `None`, so a
   run that cannot close settles as text at the end of a line and opens
   in the middle of one. *)
Definition iresolve_next `{PosPolicy} `{InlineCursor}
  (c : ascii) (st : iscan) : iscan :=
  match st with
  | IDelim k extra txt before marked o =>
      if Nat.ltb (S extra) (dwidth k)
      then IText false (txt ++ idelim_run k extra marked)%string
             (Some (dchar k)) o
      else if marked then idelim_open_marked k (Ascii.eqb c rbrace) txt o
      else idelim_resolve k txt before false (Some c) o
  | _ => iresolve st
  end.

(* "Nothing is open, and nothing is waiting on what comes after `c`".
   Strictly stronger than `iscan_closed`, and the two differ exactly on
   a delimiter run that would open: `a*` is closed at a line's end and
   an opener before a colon, which is why the split test asks this one.
   See `.project/keyed-blocks.md` 9.1. *)
Definition iscan_settled `{PosPolicy} `{InlineCursor}
  (c : ascii) (st : iscan) : bool :=
  iclosed_at (iresolve_next c st).

(* The two recursive definitions above take their own branch on a state
   carrying an alternative scan and go through `iresolve` on everything
   else.  Every lemma
   below that reasons by cases on the resolved state wants the second
   half, and a state with an unresolved alternative is one none of them is
   about -- `iclosed_at` and `iscan_wf`'s obligations both exclude it. *)
Definition is_compound (st : iscan) : bool :=
  match st with
  | IAttr _ _ _ _ _ _ | IDest _ _ _ _ _ _ _ _ => true
  | _ => false
  end.

Lemma ibreak_flat_state :
  forall `{PosPolicy} `{InlineCursor} st,
    is_compound st = false -> ibreak st = ibreak_flat (iresolve st).
Proof. intros P C st H. destruct st; try reflexivity; discriminate H. Qed.

Lemma ibreak_at_flat_state :
  forall `{PosPolicy} `{InlineCursor} attrs_enabled st,
    is_compound st = false -> ibreak_at attrs_enabled st = ibreak st.
Proof. intros P C attrs_enabled st H. destruct st; try reflexivity; discriminate H. Qed.

Lemma ifinish_ostate_flat_state :
  forall `{PosPolicy} `{InlineCursor} st,
    is_compound st = false ->
    ifinish_ostate st = ifinish_ostate_flat (iresolve st).
Proof. intros P C st H. destruct st; try reflexivity; discriminate H. Qed.

Lemma ibreak_closed :
  forall `{PosPolicy} `{InlineCursor} st,
    iscan_closed st = true ->
    ibreak st = IText false EmptyString None
                  (OState
                    (OIn (imk_here SoftBreak)
                       :: ifinish_items st) [] None).
Proof.
  intros P C st H.
  assert (Hd : is_compound st = false)
    by (destruct st; try reflexivity; cbn in H; discriminate H).
  rewrite (ibreak_flat_state st Hd).
  unfold ifinish_items, oitems_of.
  rewrite (ifinish_ostate_flat_state st Hd).
  unfold iscan_closed, iclosed_at, ibreak_flat, ifinish_ostate_flat in *.
  destruct (iresolve st) as [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|cltxt clob|kids img open sp ssrc sob|ap asrc atxt aprev ash aob|kids img open label ob|nesc nimg nlab open nob|kids img open esc depth dst sh ob|asrc atxt aob|rspec rtxt rob];
    try discriminate.
  - destruct o as [out [|f stk] word]; [|discriminate].
    unfold flush_text_at, oemit; cbn [os_stk os_out oflatten oapp].
    destruct (nonempty_str txt); reflexivity.
  - apply andb_true_iff in H as [Hr Hs]. rewrite Hr.
    destruct o as [out [|f stk] word]; [|discriminate].
    unfold oemit; cbn [os_stk os_out oflatten oapp]. reflexivity.
  (* the candidate decays to text and the boundary is the soft break
     after it, which is the text case with `auto_lit` in the buffer *)
  - destruct aob as [out [|f stk] word]; [|discriminate].
    unfold flush_text_at, oemit; cbn [os_stk os_out oflatten oapp].
    destruct (nonempty_str (auto_lit asrc atxt)); reflexivity.
  (* the same, with the verbatim the spec did not claim underneath *)
  - destruct rob as [out [|f stk] word]; [|discriminate].
    unfold flush_text_at, oemit; cbn [os_stk os_out oflatten oapp].
    destruct (nonempty_str (iraw_lit rspec)); reflexivity.
Qed.

Fixpoint iscan_str (s : string) (st : iscan) : iscan :=
  match s with
  | EmptyString => st
  | String c rest =>
      iscan_str rest (@istep semantic_pos semantic_inline_cursor c st)
  end.

(* An executable certificate for this outer scan's source dispatch.  One
   unit of fuel authorizes dispatching one source byte;
   state rewrites such as closing or abandoning a scope spend no source
   fuel and never feed that byte back to the scanner.  This deliberately
   says nothing about the internal cost of a dispatch -- `oclose` may walk
   the opener stack -- so it is not a linear-time theorem.

   djot.js's `reparseAttributes` does backtrack: it buffers slices fed to
   the attribute machine and, when a spec dies, replays them through the
   inline scanner with attributes switched off.  The current state does
   not reproduce that recovery, as recorded at
   `attr_unclosed_spec_is_not_rescanned`.  This lemma is not an
   impossibility result: an ordinary-inline shadow can advance with
   the attribute candidate and preserve this fuel discipline.  See
   `.project/no-backtracking.md`. *)
Fixpoint iscan_str_fuel (fuel : nat) (s : string) (st : iscan)
  : option iscan :=
  match s with
  | EmptyString => Some st
  | String c rest =>
      match fuel with
      | O => None
      | S fuel' =>
          iscan_str_fuel fuel' rest
            (@istep semantic_pos semantic_inline_cursor c st)
      end
  end.

Lemma iscan_str_no_reread :
  forall s st,
    iscan_str_fuel (String.length s) s st = Some (iscan_str s st).
Proof.
  induction s as [|c rest IH]; intros st; cbn [String.length iscan_str_fuel
    iscan_str]; [reflexivity|apply IH].
Qed.

Lemma iscan_str_fuel_short :
  forall s fuel st,
    fuel < String.length s -> iscan_str_fuel fuel s st = None.
Proof.
  induction s as [|c rest IH]; intros fuel st Hlt.
  - cbn [String.length] in Hlt. lia.
  - destruct fuel as [|fuel']; [reflexivity|].
    cbn [String.length iscan_str_fuel] in Hlt |- *.
    apply IH. lia.
Qed.

(* A paragraph's lines, in order.  Trailing whitespace is stripped from
   the last line only -- djot.js's `getMatches` drops the final soft
   break and the spaces before it, and does so whatever state the scan is
   in, so `` `a  `` closes on the trimmed content.  Interior lines keep
   their trailing spaces, which is observable inside a verbatim. *)
Fixpoint iscan_lines (l : list string) (st : iscan) : iscan :=
  match l with
  | [] => st
  | [x] => iscan_str (strip_trailing_ws x) st
  | x :: rest =>
      iscan_lines rest
        (@ibreak semantic_pos semantic_inline_cursor (iscan_str x st))
  end.

(* The same scan with attribute recognition switched off.  A block
   attribute spec that fails hands its lines back to the paragraph, and
   djot.js re-reads exactly those lines with `allowAttributes` false
   (`block.ts:592`, `inline.ts:651`). *)
Fixpoint iscan_str_off (s : string) (st : iscan) : iscan :=
  match s with
  | EmptyString => st
  | String c rest =>
      iscan_str_off rest
        (@istep_at semantic_pos semantic_inline_cursor false c st)
  end.

(* `k` leading lines of a paragraph read with attributes off, the rest as
   usual.  The region is whole lines because `block.ts:552` records one
   slice per line, so the inline shadow's `islice_end` disposition has no
   counterpart here: what is cut inside a line there is not cut at all
   here.  The break that ends each off line is off too, since a slice
   runs to and includes its newline.

   `k = 0` is `iscan_lines`, definitionally, which is what leaves every
   existing statement about a paragraph's scan unconditioned. *)
Fixpoint iscan_lines_off (k : nat) (l : list string) (st : iscan) : iscan :=
  match k with
  | O => iscan_lines l st
  | S k' =>
      match l with
      | [] => st
      | [x] => iscan_str_off (strip_trailing_ws x) st
      | x :: rest =>
          iscan_lines_off k' rest
            (@ibreak_at semantic_pos semantic_inline_cursor false
              (iscan_str_off x st))
      end
  end.

(*
The located scan
----------------

The same transition, driven so that each byte arrives with its own
`spot`s installed.  Nothing here decides anything: at `semantic_pos`
every use of the cursor is behind `pos_records`, so this is `iscan_lines`
with an argument the scanner ignores.

Coordinates are counted, never measured.  Extracted `String.length`
allocates a unary `nat` per byte, so calling it per byte would make a
line quadratic; `rem` starts at one length per line and a predecessor
carries it down.  That count is the distance to the end of the *source*
line because a stored line is a suffix of its line with nothing trimmed
from the end (`.project/260916.plan.source-locations.md`, F2).
*)

Definition cursor_in (k rem origin : nat) : InlineCursor :=
  CursorAt (Spot k rem) (Spot k (pred rem)) (Spot k origin).

Fixpoint iscan_str_located `{PosPolicy} (allow : bool) (k origin rem : nat)
  (s : string) (st : iscan) : iscan :=
  match s with
  | EmptyString => st
  | String c rest =>
      iscan_str_located allow k origin (pred rem) rest
        (@istep_at _ (cursor_in k rem origin) allow c st)
  end.

(* Where a line's stored text begins, and where a paragraph's content
   ends: its last line stripped, since `iscan_lines` scans it stripped. *)
Definition lines_start (l : list (nat * string)) : spot :=
  match l with
  | [] => Spot 0 0
  | (k, x) :: _ => Spot k (String.length x)
  end.

Fixpoint lines_stop (l : list (nat * string)) : spot :=
  match l with
  | [] => Spot 0 0
  | [(k, x)] => Spot k (String.length x - String.length (strip_trailing_ws x))
  | _ :: rest => lines_stop rest
  end.

(* Attributes are off for the leading lines a failed block spec handed
   back, as in `iscan_lines_off`, and off for the break that ends one. *)
Definition allow_attrs (off : nat) : bool :=
  match off with O => inline_attrs_enabled | S _ => false end.

(* A break runs from the end of its line to the start of the next one,
   so the text after it starts where that line's content does: the stop
   of the `SoftBreak` is what `text_start` reads.  Container prefixes are
   why this is not the byte after the terminator. *)
Fixpoint iscan_lines_located `{PosPolicy} (off : nat)
  (l : list (nat * string)) (st : iscan) : iscan :=
  match l with
  | [] => st
  | [(k, x)] =>
      iscan_str_located (allow_attrs off) k (String.length x)
        (String.length x) (strip_trailing_ws x) st
  | (k, x) :: rest =>
      iscan_lines_located (pred off) rest
        (@ibreak_at _
           (CursorAt (Spot k 0) (lines_start rest) (Spot k (String.length x)))
           (allow_attrs off)
           (iscan_str_located (allow_attrs off) k (String.length x)
              (String.length x) x st))
  end.

(* The paragraph ends where its last line's content does, and a text run
   with nothing before it starts at the first line's first byte. *)
Definition ifinish_located `{PosPolicy} (l : list (nat * string))
  (st : iscan) : inlines :=
  @ifinish _ (CursorAt (lines_stop l) (lines_stop l) (lines_start l)) st.

(*
Erasure of a scan
-----------------

What the located scan and the semantic one have to agree on: the tree,
once the coordinates are dropped.  One function serves both sides,
because `iscan` is the same type at every policy -- and because a policy
that records nothing stores no coordinates at all (`imk`, `pspan`,
`remember_word_start` each ask it first), a semantic state is its own
erasure, so the refinement is one equation rather than an equation and
an invariant over the state.
*)

Definition erase_oitem (i : oitem) : oitem :=
  match i with
  | OIn n => OIn (erase_inode n)
  | OMark a _ _ => OMark a null_span None
  end.

Fixpoint erase_oitems (l : oitems) : oitems :=
  match l with
  | [] => []
  | i :: rest => erase_oitem i :: erase_oitems rest
  end.

Lemma erase_oitems_map : forall l, erase_oitems l = map erase_oitem l.
Proof. induction l as [|i l IH]; cbn [erase_oitems map]; congruence. Qed.

Definition erase_frame (f : frame) : frame :=
  Frame (fr_kind f) (fr_marked f) null_span (erase_oitems (fr_out f)).

Definition erase_ostate (o : ostate) : ostate :=
  OState (erase_oitems (os_out o)) (map erase_frame (os_stk o)) None.

Fixpoint erase_iscan (st : iscan) : iscan :=
  match st with
  | IText esc txt prev o => IText esc txt prev (erase_ostate o)
  | IEscWs ws txt prev o => IEscWs ws txt prev (erase_ostate o)
  | IBrace txt prev o => IBrace txt prev (erase_ostate o)
  | IDelim k extra txt before marked o =>
      IDelim k extra txt before marked (erase_ostate o)
  | IOpen n vk o => IOpen n vk (erase_ostate o)
  | IVerb n run txt vk o => IVerb n run txt vk (erase_ostate o)
  | IDollar two txt prev o => IDollar two txt prev (erase_ostate o)
  | IPeriod two txt prev o => IPeriod two txt prev (erase_ostate o)
  | IDash n txt prev o => IDash n txt prev (erase_ostate o)
  | IBang txt prev o => IBang txt prev (erase_ostate o)
  | IClosed txt o => IClosed txt (erase_ostate o)
  | ISpan kids image _ p src o =>
      ISpan (erase_inlines kids) image null_span p src (erase_ostate o)
  | IAttr p src txt prev sh o =>
      IAttr p src txt prev (erase_iscan sh) (erase_ostate o)
  | IReference kids image _ label o =>
      IReference (erase_inlines kids) image null_span label (erase_ostate o)
  | INote esc image label _ o =>
      INote esc image label null_span (erase_ostate o)
  | IDest kids image _ esc depth dst sh o =>
      IDest (erase_inlines kids) image null_span esc depth dst
        (erase_iscan sh) (erase_ostate o)
  | IAuto src txt o => IAuto src txt (erase_ostate o)
  | IRaw spec txt o => IRaw spec txt (erase_ostate o)
  end.

(* A node the policy built: its payload survives, its provenance does
   not, and the roles a spec attached to it are provenance. *)
Lemma erase_imk : forall `{P : PosPolicy} start stop x,
  erase_inode (@imk P start stop x) = mk (erase_inline x).
Proof.
  intros P start stop x. unfold imk, posnode, mk, erase_inode.
  destruct pos_records; reflexivity.
Qed.

Lemma erase_add_inline_role : forall `{P : PosPolicy} role r n,
  erase_inode (@add_inline_role P role r n) = erase_inode n.
Proof.
  intros P role r [p a x]. unfold add_inline_role, add_roles.
  destruct pos_records; [destruct p|]; reflexivity.
Qed.

Lemma erase_osnoc : forall n l,
  erase_oitems (osnoc n l) = osnoc (erase_oitem n) (erase_oitems l).
Proof.
  intros [n|a sp w] [|[m|b sq w'] l]; try reflexivity;
    destruct m as [q [|lv b'] u]; try reflexivity;
    destruct u; try reflexivity;
    destruct n as [p [|kv a'] v]; try reflexivity;
    destruct v; reflexivity.
Qed.

Lemma erase_oapp : forall cur out,
  erase_oitems (oapp cur out) = oapp (erase_oitems cur) (erase_oitems out).
Proof.
  induction cur as [|n cur IH]; intros out; [reflexivity|].
  destruct cur as [|n' cur']; cbn [oapp].
  - apply erase_osnoc.
  - change (erase_oitems (n :: n' :: cur')%list)
      with (erase_oitem n :: erase_oitems (n' :: cur')%list)%list.
    cbn [oapp]. rewrite <- IH. reflexivity.
Qed.

Lemma erase_oemit : forall n o,
  erase_ostate (oemit n o) = oemit (erase_inode n) (erase_ostate o).
Proof. intros n [out [|f stk] word]; [reflexivity|destruct f; reflexivity]. Qed.

Lemma erase_oemit_node : forall p a x o,
  oemit (Node NoPos a (erase_inline x)) (erase_ostate o) =
  erase_ostate (oemit (Node p a x) o).
Proof. intros p a x o. rewrite erase_oemit. reflexivity. Qed.

Lemma erase_imk_here : forall `{P : PosPolicy} `{C : InlineCursor} x,
  erase_inode (@imk_here P C x) =
  @imk_here semantic_pos semantic_inline_cursor (erase_inline x).
Proof. intros P C x. unfold imk_here. rewrite erase_imk. reflexivity. Qed.

Lemma erase_oemit_merge : forall n o,
  erase_ostate (oemit_merge n o) =
  oemit_merge (erase_inode n) (erase_ostate o).
Proof.
  intros n [out [|f stk] word]; [|destruct f];
    unfold oemit_merge, erase_ostate, erase_frame;
    cbn [os_stk os_out os_word_start fr_kind fr_marked fr_out map];
    rewrite (erase_osnoc (OIn n)); reflexivity.
Qed.

Lemma erase_omark : forall a spec o,
  erase_ostate (omark a spec o) = omark a null_span (erase_ostate o).
Proof. intros a spec [out [|f stk] word]; [reflexivity|destruct f; reflexivity]. Qed.

Lemma erase_oemit_all : forall ns o,
  erase_ostate (oemit_all ns o) = oemit_all (erase_inlines ns) (erase_ostate o).
Proof.
  induction ns as [|n ns IH]; intros o; [reflexivity|].
  cbn [oemit_all]. rewrite IH, erase_oemit. reflexivity.
Qed.

Lemma erase_oemit_all_merge : forall ns o,
  erase_ostate (oemit_all_merge ns o) =
  oemit_all_merge (erase_inlines ns) (erase_ostate o).
Proof.
  induction ns as [|n ns IH]; intros o; [reflexivity|].
  cbn [oemit_all_merge]. rewrite IH, erase_oemit_merge. reflexivity.
Qed.

Lemma erase_oset_cur : forall l o,
  erase_ostate (oset_cur l o) = oset_cur (erase_oitems l) (erase_ostate o).
Proof. intros l [out [|f stk] word]; [reflexivity|destruct f; reflexivity]. Qed.

Lemma erase_oword_reset : forall o,
  erase_ostate (oword_reset o) = oword_reset (erase_ostate o).
Proof. intros [out stk word]; reflexivity. Qed.

Lemma erase_remember_word_start : forall `{P : PosPolicy} `{C : InlineCursor} c o,
  erase_ostate (@remember_word_start P C c o) = erase_ostate o.
Proof.
  intros P C c [out stk word]. unfold remember_word_start.
  destruct (pos_records && is_ws c)%bool; reflexivity.
Qed.

Lemma erase_flush_text_at : forall `{P : PosPolicy} `{C : InlineCursor} txt o,
  erase_ostate (@flush_text_at P C txt o) = flush_text txt (erase_ostate o).
Proof.
  intros P C txt o. unfold flush_text; unfold flush_text_at.
  destruct (nonempty_str txt); [|reflexivity].
  rewrite erase_oemit, erase_imk. reflexivity.
Qed.

Lemma erase_flush_text_to_at :
  forall `{P : PosPolicy} `{C : InlineCursor} stop txt o,
  erase_ostate (@flush_text_to_at P C stop txt o) =
  flush_text txt (erase_ostate o).
Proof.
  intros P C stop txt o. unfold flush_text; unfold flush_text_to_at, flush_text_at.
  destruct (nonempty_str txt); [|reflexivity].
  rewrite !erase_oemit, !erase_imk. reflexivity.
Qed.

Lemma erase_opush_at : forall k m cm open o,
  erase_ostate (opush_at k m cm open o) =
  opush_at k m cm null_span (erase_ostate o).
Proof. intros k m cm open [out stk word]; reflexivity. Qed.

Lemma erase_opush : forall `{P : PosPolicy} `{C : InlineCursor} k m o,
  erase_ostate (@opush P C k m o) =
  @opush semantic_pos semantic_inline_cursor k m (erase_ostate o).
Proof.
  intros P C k m o. unfold opush, dtoken_span, pspan.
  rewrite erase_opush_at. destruct (@pos_records P); reflexivity.
Qed.

Lemma erase_bpush : forall `{P : PosPolicy} `{C : InlineCursor} image o,
  erase_ostate (@bpush P C image o) =
  @bpush semantic_pos semantic_inline_cursor image (erase_ostate o).
Proof.
  intros P C image [out stk word]. unfold bpush, pspan.
  destruct (@pos_records P); reflexivity.
Qed.

Lemma erase_dpush : forall image open o,
  erase_ostate (dpush image open o) =
  dpush image null_span (erase_ostate o).
Proof. intros image open [out stk word]; reflexivity. Qed.

Lemma erase_isnoc : forall n l,
  erase_inlines (isnoc n l) = isnoc (erase_inode n) (erase_inlines l).
Proof.
  intros n [|m l]; [reflexivity|].
  destruct m as [q [|lv b'] u]; try reflexivity;
    destruct u; try reflexivity;
    destruct n as [p [|kv a'] v]; try reflexivity;
    destruct v; reflexivity.
Qed.

Lemma erase_fr_src : forall f, fr_src (erase_frame f) = fr_src f.
Proof. intros [k m open out]; destruct k; reflexivity. Qed.

Lemma erase_fr_lit : forall `{P : PosPolicy} f,
  @fr_lit semantic_pos (erase_frame f) = erase_inode (@fr_lit P f).
Proof.
  intros P f. unfold fr_lit. rewrite erase_imk, erase_fr_src. reflexivity.
Qed.

Lemma erase_nonempty : forall l, nonempty (erase_oitems l) = nonempty l.
Proof. intros [|i l]; reflexivity. Qed.

Lemma erase_dmatch : forall k m f, dmatch k m (erase_frame f) = dmatch k m f.
Proof. intros k m [[?|?|?] ? ? ?]; reflexivity. Qed.

Lemma erase_fr_barrier : forall f, fr_barrier (erase_frame f) = fr_barrier f.
Proof. intros [[?|?|?] ? ? ?]; reflexivity. Qed.

Lemma erase_istarts_str : forall l,
  istarts_str (erase_inlines l) = istarts_str l.
Proof.
  intros [|[p [|kv a] v] l]; try reflexivity; destruct v; reflexivity.
Qed.

Lemma erase_oattach_list : forall `{P : PosPolicy} a spec w out,
  erase_inlines (@oattach_list P a spec w out) =
  @oattach_list semantic_pos a null_span None (erase_inlines out).
Proof.
  intros P a spec w [|[p a' v] out]; [reflexivity|].
  destruct v;
    try (destruct a' as [|kv a'];
         cbn [erase_inlines erase_inode oattach_list];
         rewrite ?erase_add_inline_role; reflexivity).
  destruct a' as [|kv a'];
    [|cbn [erase_inlines erase_inode oattach_list];
      rewrite erase_add_inline_role; reflexivity].
  cbn [erase_inlines erase_inode erase_inline oattach_list].
  destruct (last_ws_split s) as [pre w0].
  destruct (nonempty_str w0); [|reflexivity].
  destruct a as [|kv a]; [reflexivity|].
  destruct (split_text_pos p w) as [pp wp]. cbn [split_text_pos].
  rewrite erase_isnoc, erase_add_inline_role. cbn [erase_inode].
  destruct (nonempty_str pre); [rewrite erase_isnoc|]; reflexivity.
Qed.

(* Resolution is the ambient policy's: `oresolve_go` opens no policy
   context, so the spec a scope settles attaches without a role.  Erasure
   commutes with it for the same reason it commutes with `oattach_list`,
   which is that the pass moves attributes and not coordinates. *)
Lemma erase_oresolve_go : forall l,
  oresolve_go (erase_oitems l) =
  (erase_inlines (fst (oresolve_go l)), snd (oresolve_go l)).
Proof.
  induction l as [|[n|a spec w] l IH]; [reflexivity| |];
    cbn [erase_oitems erase_oitem oresolve_go];
    rewrite IH; destruct (oresolve_go l) as [out m]; cbn [fst snd].
  - destruct m; [rewrite erase_isnoc|]; reflexivity.
  - rewrite <- (erase_istarts_str (oattach_list a spec w out)).
    rewrite erase_oattach_list. reflexivity.
Qed.

Lemma erase_oresolve : forall l,
  erase_inlines (oresolve l) = oresolve (erase_oitems l).
Proof.
  intros l. unfold oresolve. rewrite erase_oresolve_go. reflexivity.
Qed.

Lemma erase_oclose_go : forall `{P : PosPolicy} k m pend stk,
  @oclose_go semantic_pos k m (erase_oitems pend) (map erase_frame stk) =
  match @oclose_go P k m pend stk with
  | None => None
  | Some (content, open, rest) =>
      Some (erase_oitems content, null_span, map erase_frame rest)
  end.
Proof.
  intros P k m pend stk. revert pend.
  induction stk as [|f stk IH]; intros pend; [reflexivity|].
  cbn [map oclose_go]. rewrite erase_dmatch, erase_fr_barrier.
  change (fr_out (erase_frame f)) with (erase_oitems (fr_out f)).
  rewrite <- erase_oapp.
  destruct (dmatch k m f).
  - rewrite erase_nonempty.
    destruct (nonempty (oapp pend (fr_out f)));
      cbn [erase_frame fr_open]; reflexivity.
  - destruct (fr_barrier f); [reflexivity|].
    rewrite (erase_fr_lit f).
    specialize (IH (oapp (oapp pend (fr_out f)) [OIn (@fr_lit P f)])).
    rewrite !erase_oapp in IH. cbn [erase_oitems erase_oitem] in IH.
    rewrite <- erase_oapp in IH. exact IH.
Qed.

Lemma erase_dnode : forall k ns,
  erase_inline (dnode k ns) = dnode k (erase_inlines ns).
Proof.
  intros k ns. destruct k; cbn [dnode erase_inline];
    rewrite erase_inline_children; reflexivity.
Qed.

Lemma erase_bnode : forall image ns tgt,
  erase_inline (bnode image ns tgt) = bnode image (erase_inlines ns) tgt.
Proof.
  intros image ns tgt. destruct image; cbn [bnode erase_inline];
    rewrite erase_inline_children; reflexivity.
Qed.

Lemma erase_span_node : forall ns,
  erase_inline (Span ns) = Span (erase_inlines ns).
Proof.
  intros ns. cbn [erase_inline]. rewrite erase_inline_children. reflexivity.
Qed.

(* An empty reference's label is the string content of its first
   bracket, which is payload and so survives erasure. *)
Lemma erase_reference_text : forall i,
  reference_text (erase_inline i) = reference_text i.
Proof.
  refine (inline_ind2
    (fun i => reference_text (erase_inline i) = reference_text i)
    (fun ils => reference_text (Emph (erase_inlines ils)) =
                reference_text (Emph ils))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
    intros;
    cbn [erase_inline erase_inlines erase_inode reference_text
      node_contents] in *;
    rewrite ?erase_inline_children in *; congruence.
Qed.

Lemma erase_reference_inlines_text : forall ns,
  reference_inlines_text (erase_inlines ns) = reference_inlines_text ns.
Proof.
  intros ns. unfold reference_inlines_text. f_equal.
  rewrite erase_inlines_map, map_map. apply map_ext.
  intros [p a x]; cbn [node_contents erase_inode]. apply erase_reference_text.
Qed.

Lemma erase_auto_node : forall s, erase_inline (auto_node s) = auto_node s.
Proof. intros s. unfold auto_node. destruct (auto_email s); reflexivity. Qed.

Lemma erase_vnode : forall vk s, erase_inline (vnode vk s) = vnode vk s.
Proof. intros [|st] s; reflexivity. Qed.

Lemma erase_oclose : forall `{P : PosPolicy} k m stop o,
  sclose k m (erase_ostate o) =
  option_map erase_ostate (@oclose P k m stop o).
Proof.
  intros P k m stop o. unfold sclose, oclose.
  change (os_stk (erase_ostate o)) with (map erase_frame (os_stk o)).
  change (@nil oitem) with (erase_oitems []) at 1.
  rewrite erase_oclose_go.
  destruct (@oclose_go P k m [] (os_stk o)) as [[[content open] rest]|];
    [|reflexivity].
  cbn [option_map].
  rewrite erase_oemit, erase_imk, erase_dnode, erase_inlines_rev,
    erase_oresolve.
  destruct o as [out stk word]; reflexivity.
Qed.

Lemma erase_bclose_go : forall `{P : PosPolicy} pend stk,
  @bclose_go semantic_pos (erase_oitems pend) (map erase_frame stk) =
  match @bclose_go P pend stk with
  | None => None
  | Some (content, image, open, rest) =>
      Some (erase_oitems content, image, null_span, map erase_frame rest)
  end.
Proof.
  intros P pend stk. revert pend.
  induction stk as [|f stk IH]; intros pend; [reflexivity|].
  cbn [map bclose_go].
  change (fr_kind (erase_frame f)) with (fr_kind f).
  change (fr_out (erase_frame f)) with (erase_oitems (fr_out f)).
  rewrite <- erase_oapp.
  destruct (fr_kind f) eqn:Ek; [| |reflexivity].
  - rewrite (erase_fr_lit f).
    specialize (IH (oapp (oapp pend (fr_out f)) [OIn (@fr_lit P f)])).
    rewrite !erase_oapp in IH. cbn [erase_oitems erase_oitem] in IH.
    rewrite <- erase_oapp in IH. exact IH.
  - cbn [erase_frame fr_open]. reflexivity.
Qed.

Lemma erase_bclose : forall `{P : PosPolicy} o,
  @bclose semantic_pos (erase_ostate o) =
  match @bclose P o with
  | None => None
  | Some (kids, image, open, o') =>
      Some (erase_inlines kids, image, null_span, erase_ostate o')
  end.
Proof.
  intros P o. unfold bclose.
  change (os_stk (erase_ostate o)) with (map erase_frame (os_stk o)).
  change (@nil oitem) with (erase_oitems []) at 1.
  rewrite erase_bclose_go.
  destruct (@bclose_go P [] (os_stk o)) as [[[[content image] open] rest]|];
    [|reflexivity].
  rewrite <- erase_oresolve, <- erase_inlines_rev.
  destruct o as [out stk word]; reflexivity.
Qed.

Lemma erase_bunpush : forall o,
  bunpush (erase_ostate o) =
  match bunpush o with
  | None => None
  | Some (image, open, o') => Some (image, null_span, erase_ostate o')
  end.
Proof.
  intros [out [|[[image| |] marked open [|i l]] stk] word]; reflexivity.
Qed.

Lemma erase_opop_str : forall o,
  opop_str (erase_ostate o) =
  (fst (opop_str o), erase_ostate (snd (opop_str o))).
Proof.
  intros [out [|f stk] word].
  - destruct out as [|[[p a v]|b sp w] out]; try reflexivity.
    destruct a as [|kv a]; [destruct v; reflexivity|reflexivity].
  - destruct f as [k marked open [|[[p a v]|b sp w] l]]; try reflexivity.
    destruct a as [|kv a]; [destruct v; reflexivity|reflexivity].
Qed.

Lemma erase_bflat : forall `{P : PosPolicy} `{C : InlineCursor} kids txt o,
  @bflat semantic_pos semantic_inline_cursor (erase_inlines kids) txt
    (erase_ostate o)
  = (fst (@bflat P C kids txt o), erase_ostate (snd (@bflat P C kids txt o))).
Proof.
  intros P C kids. induction kids as [|[p a x] kids IH]; intros txt o;
    [reflexivity|].
  rewrite erase_inlines_cons. unfold erase_inode at 1.
  destruct a as [|kv a];
    [destruct x; try (cbn [erase_inline bflat]; apply IH)|];
    cbn [bflat]; sem_flush;
    rewrite <- erase_flush_text_at, (erase_oemit_node p); apply IH.
Qed.

Lemma erase_bsplit_nl : forall `{P : PosPolicy} `{C : InlineCursor} s txt o,
  @bsplit_nl semantic_pos semantic_inline_cursor s txt (erase_ostate o)
  = (fst (@bsplit_nl P C s txt o),
     erase_ostate (snd (@bsplit_nl P C s txt o))).
Proof.
  intros P C s. induction s as [|c s IH]; intros txt o; [reflexivity|].
  cbn [bsplit_nl]. destruct (Ascii.eqb c nl_char); [|apply IH].
  sem_flush. rewrite <- erase_flush_text_at.
  change (@imk_here semantic_pos semantic_inline_cursor SoftBreak)
    with (@imk_here semantic_pos semantic_inline_cursor
            (erase_inline SoftBreak)).
  rewrite <- erase_imk_here, <- erase_oemit. apply IH.
Qed.

Lemma erase_oclose_barred : forall k m o,
  oclose_barred k m (erase_ostate o) = oclose_barred k m o.
Proof.
  intros k m o. unfold oclose_barred.
  change (os_stk (erase_ostate o)) with (map erase_frame (os_stk o)).
  generalize false. generalize (os_stk o) as stk.
  induction stk as [|f stk IH]; intros past; [reflexivity|].
  cbn [map oclose_barred_go]. rewrite erase_dmatch, erase_fr_barrier.
  destruct (dmatch k m f); [reflexivity|apply IH].
Qed.

Lemma erase_bclosed_lit : forall `{P : PosPolicy} `{C : InlineCursor}
  kids image o,
  @bclosed_lit semantic_pos semantic_inline_cursor (erase_inlines kids) image
    (erase_ostate o)
  = (fst (@bclosed_lit P C kids image o),
     erase_ostate (snd (@bclosed_lit P C kids image o))).
Proof.
  intros P C kids image o. unfold bclosed_lit.
  rewrite erase_opop_str.
  destruct (opop_str o) as [pre o1]; cbn [fst snd].
  rewrite erase_bflat.
  destruct (@bflat P C kids (pre ++ bracket_open image) o1) as [txt o2];
    reflexivity.
Qed.

Lemma erase_bspan_lit : forall `{P : PosPolicy} `{C : InlineCursor}
  kids image src o,
  @bspan_lit semantic_pos semantic_inline_cursor (erase_inlines kids) image
    src (erase_ostate o)
  = (fst (@bspan_lit P C kids image src o),
     erase_ostate (snd (@bspan_lit P C kids image src o))).
Proof.
  intros P C kids image src o. unfold bspan_lit.
  rewrite erase_bclosed_lit.
  destruct (@bclosed_lit P C kids image o) as [txt o']; cbn [fst snd].
  apply erase_bsplit_nl.
Qed.

Lemma erase_battr_lit : forall `{P : PosPolicy} `{C : InlineCursor} src txt o,
  @battr_lit semantic_pos semantic_inline_cursor src txt (erase_ostate o)
  = (fst (@battr_lit P C src txt o),
     erase_ostate (snd (@battr_lit P C src txt o))).
Proof. intros P C src txt o. apply erase_bsplit_nl. Qed.

Lemma erase_bref_lit : forall `{P : PosPolicy} `{C : InlineCursor}
  kids image label o,
  @bref_lit semantic_pos semantic_inline_cursor (erase_inlines kids) image
    label (erase_ostate o)
  = (fst (@bref_lit P C kids image label o),
     erase_ostate (snd (@bref_lit P C kids image label o))).
Proof.
  intros P C kids image label o. unfold bref_lit.
  rewrite erase_bclosed_lit.
  destruct (@bclosed_lit P C kids image o) as [txt o']; reflexivity.
Qed.

Lemma erase_bnote_lit : forall `{P : PosPolicy} `{C : InlineCursor}
  esc image label o,
  @bnote_lit semantic_pos semantic_inline_cursor esc image label
    (erase_ostate o)
  = (fst (@bnote_lit P C esc image label o),
     erase_ostate (snd (@bnote_lit P C esc image label o))).
Proof.
  intros P C esc image label o. unfold bnote_lit.
  rewrite erase_opop_str.
  destruct (opop_str o) as [pre o1]; reflexivity.
Qed.

Lemma erase_ospan_bang : forall `{P : PosPolicy} `{C : InlineCursor} image o,
  erase_ostate (@ospan_bang P C image o) =
  @ospan_bang semantic_pos semantic_inline_cursor image (erase_ostate o).
Proof.
  intros P C image o. unfold ospan_bang. destruct image; [|reflexivity].
  rewrite erase_opop_str. destruct (opop_str o) as [pre o1]; cbn [fst snd].
  apply erase_flush_text_at.
Qed.

Lemma erase_ilead : forall `{P : PosPolicy} `{C : InlineCursor} c txt prev o,
  erase_iscan (@ilead P C c txt prev o) =
  @ilead semantic_pos semantic_inline_cursor c txt prev (erase_ostate o).
Proof.
  intros P C c txt prev o. unfold ilead.
  destruct (is_bslash c); [reflexivity|].
  destruct (is_tick c);
    [cbn [erase_iscan]; rewrite erase_flush_text_at; reflexivity|].
  destruct (Ascii.eqb c dollar); [reflexivity|].
  destruct (Ascii.eqb c period); [reflexivity|].
  destruct (Ascii.eqb c hyphen); [reflexivity|].
  destruct (Ascii.eqb c lbrace); [reflexivity|].
  destruct (Ascii.eqb c bang); [reflexivity|].
  destruct (Ascii.eqb c lt); [reflexivity|].
  destruct (Ascii.eqb c lbrack);
    [cbn [erase_iscan]; rewrite erase_bpush, erase_flush_text_at; reflexivity|].
  destruct (Ascii.eqb c rbrack); [reflexivity|].
  destruct (Ascii.eqb c hat && note_pos txt prev && notes_enabled)%bool;
    [rewrite erase_bunpush; destruct (bunpush o) as [[[image open] o']|];
      [reflexivity|]|];
    destruct (dstyle_of c); cbn [erase_iscan];
    rewrite ?erase_remember_word_start; reflexivity.
Qed.

Lemma erase_idest_open : forall `{P : PosPolicy} `{C : InlineCursor}
  kids image open o,
  erase_iscan (@idest_open P C kids image open o) =
  @idest_open semantic_pos semantic_inline_cursor (erase_inlines kids) image
    null_span (erase_ostate o).
Proof.
  intros P C kids image open o. unfold idest_open.
  rewrite <- (erase_dpush image open), erase_bflat.
  destruct (@bflat P C kids EmptyString (dpush image open o)) as [txt o'];
    reflexivity.
Qed.

Lemma erase_oopen_marked : forall `{P : PosPolicy} `{C : InlineCursor}
  k cm txt o,
  erase_ostate (@oopen_marked P C k cm txt o) =
  @oopen_marked semantic_pos semantic_inline_cursor k cm txt (erase_ostate o).
Proof.
  intros P C k cm txt o. unfold oopen_marked.
  rewrite erase_opush_at, erase_flush_text_to_at.
  unfold dtoken_span, pspan. destruct (@pos_records P); reflexivity.
Qed.

Lemma erase_idelim_open_marked : forall `{P : PosPolicy} `{C : InlineCursor}
  k cm txt o,
  erase_iscan (@idelim_open_marked P C k cm txt o) =
  @idelim_open_marked semantic_pos semantic_inline_cursor k cm txt
    (erase_ostate o).
Proof.
  intros P C k cm txt o. unfold idelim_open_marked.
  cbn [erase_iscan]. rewrite erase_oopen_marked. reflexivity.
Qed.

Lemma erase_islice_end : forall st,
  erase_iscan (islice_end st) = islice_end (erase_iscan st).
Proof. intros [| | |k extra txt before marked o| | | | | | | | | | | | | |];
  try reflexivity; destruct esc; reflexivity. Qed.

Lemma erase_iattr_mark : forall `{P : PosPolicy} `{C : InlineCursor}
  src a txt o,
  erase_iscan (@iattr_mark P C src a txt o) =
  @iattr_mark semantic_pos semantic_inline_cursor src a txt (erase_ostate o).
Proof.
  intros P C src a txt o. unfold iattr_mark.
  cbn [erase_iscan]. rewrite erase_omark,
    (erase_flush_text_to_at (spot_before cursor_start (String lbrace src))).
  unfold pspan. destruct (@pos_records P); reflexivity.
Qed.

Lemma erase_iattr_feed : forall `{P : PosPolicy} `{C : InlineCursor}
  c p src txt prev sh o,
  erase_iscan (@iattr_feed P C c p src txt prev sh o) =
  @iattr_feed semantic_pos semantic_inline_cursor c p src txt prev
    (erase_iscan sh) (erase_ostate o).
Proof.
  intros P C c p src txt prev sh o. unfold iattr_feed.
  destruct (ap_failed (astep p c)); [reflexivity|].
  destruct (ap_done (astep p c)); [apply erase_iattr_mark|].
  cbn [erase_iscan]. rewrite erase_islice_end. reflexivity.
Qed.

Lemma erase_ibrace_step_at : forall `{P : PosPolicy} `{C : InlineCursor}
  allow c txt prev o,
  erase_iscan (@ibrace_step_at P C allow c txt prev o) =
  @ibrace_step_at semantic_pos semantic_inline_cursor allow c txt prev
    (erase_ostate o).
Proof.
  intros P C allow c txt prev o. unfold ibrace_step_at.
  destruct (dstyle_of c) as [k|]; [reflexivity|].
  destruct allow.
  - rewrite erase_iattr_feed, erase_ilead. reflexivity.
  - rewrite erase_battr_lit.
    destruct (@battr_lit P C EmptyString txt o) as [t o']; cbn [fst snd].
    apply erase_ilead.
Qed.

Lemma erase_ibang_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c txt prev o,
  erase_iscan (@ibang_step P C c txt prev o) =
  @ibang_step semantic_pos semantic_inline_cursor c txt prev (erase_ostate o).
Proof.
  intros P C c txt prev o. unfold ibang_step.
  destruct (Ascii.eqb c lbrack); [|apply erase_ilead].
  cbn [erase_iscan]. rewrite erase_bpush, erase_flush_text_to_at. reflexivity.
Qed.

Lemma erase_idelim_done : forall `{P : PosPolicy} `{C : InlineCursor}
  k txt before marker next o,
  erase_iscan (@idelim_done P C k txt before marker next o) =
  @idelim_done semantic_pos semantic_inline_cursor k txt before marker next
    (erase_ostate o).
Proof.
  intros P C k txt before marker next o. unfold idelim_done.
  destruct (dbare k before && negb marker && nonspace_at next)%bool;
    [|reflexivity].
  cbn [erase_iscan]. rewrite erase_opush, erase_flush_text_to_at. reflexivity.
Qed.

Lemma erase_idelim_resolve : forall `{P : PosPolicy} `{C : InlineCursor}
  k txt before marker next o,
  erase_iscan (@idelim_resolve P C k txt before marker next o) =
  @idelim_resolve semantic_pos semantic_inline_cursor k txt before marker next
    (erase_ostate o).
Proof.
  intros P C k txt before marker next o. unfold idelim_resolve.
  destruct (nonspace_at before || marker)%bool; [|apply erase_idelim_done].
  sem_flush.
  rewrite <- (erase_flush_text_to_at
                (span_start (@dtoken_span P C k false)) txt o).
  rewrite (erase_oclose k marker
             (if marker then cursor_stop else cursor_start)).
  destruct (@oclose P k marker _ _) as [o'|]; cbn [option_map].
  - reflexivity.
  - rewrite erase_oclose_barred. destruct (oclose_barred k marker o);
      [reflexivity|apply erase_idelim_done].
Qed.

Lemma erase_idollar_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c two txt prev o,
  erase_iscan (@idollar_step P C c two txt prev o) =
  @idollar_step semantic_pos semantic_inline_cursor c two txt prev
    (erase_ostate o).
Proof.
  intros P C c two txt prev o. unfold idollar_step.
  destruct (Ascii.eqb c dollar); [destruct two; reflexivity|].
  destruct (is_tick c && math_enabled)%bool; [|apply erase_ilead].
  cbn [erase_iscan]. rewrite erase_flush_text_to_at. reflexivity.
Qed.

Lemma erase_iperiod_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c two txt prev o,
  erase_iscan (@iperiod_step P C c two txt prev o) =
  @iperiod_step semantic_pos semantic_inline_cursor c two txt prev
    (erase_ostate o).
Proof.
  intros P C c two txt prev o. unfold iperiod_step.
  destruct (Ascii.eqb c period); [destruct two; reflexivity|apply erase_ilead].
Qed.

Lemma erase_idash_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c n txt prev o,
  erase_iscan (@idash_step P C c n txt prev o) =
  @idash_step semantic_pos semantic_inline_cursor c n txt prev
    (erase_ostate o).
Proof.
  intros P C c n txt prev o. unfold idash_step.
  destruct (Ascii.eqb c hyphen); [reflexivity|].
  destruct (Ascii.eqb c rbrace); [|apply erase_ilead].
  destruct (dstyle_of hyphen) as [k|]; [|reflexivity].
  destruct (Nat.leb (dwidth k) n); [apply erase_idelim_resolve|reflexivity].
Qed.

Lemma erase_iresolve : forall `{P : PosPolicy} `{C : InlineCursor} st,
  erase_iscan (@iresolve P C st) =
  @iresolve semantic_pos semantic_inline_cursor (erase_iscan st).
Proof.
  intros P C [| | |k extra txt before marked o| | | | | | | | | | | | | |];
    try reflexivity.
  cbn [erase_iscan iresolve].
  destruct (Nat.ltb (S extra) (dwidth k)); [reflexivity|].
  destruct marked;
    [apply erase_idelim_open_marked|apply erase_idelim_resolve].
Qed.

Lemma erase_iescws_resolve : forall `{P : PosPolicy} `{C : InlineCursor}
  ws txt prev o,
  let '(t, pv, o') := @iescws_resolve P C ws txt prev o in
  @iescws_resolve semantic_pos semantic_inline_cursor ws txt prev
    (erase_ostate o) = (t, pv, erase_ostate o').
Proof.
  intros P C [|c rest] txt prev o; [reflexivity|].
  cbn [iescws_resolve]. destruct (Ascii.eqb c " "%char); [|reflexivity].
  rewrite erase_oemit, erase_imk, erase_flush_text_to_at. reflexivity.
Qed.

Lemma erase_iesc_hard : forall `{P : PosPolicy} `{C : InlineCursor} ws txt o,
  erase_ostate (@iesc_hard P C ws txt o) =
  @iesc_hard semantic_pos semantic_inline_cursor ws txt (erase_ostate o).
Proof.
  intros P C ws txt o. unfold iesc_hard.
  rewrite erase_oemit, erase_flush_text_to_at, erase_imk_here. reflexivity.
Qed.

Lemma erase_ispan_feed : forall `{P : PosPolicy} `{C : InlineCursor}
  c kids image open p src o,
  erase_iscan (@ispan_feed P C c kids image open p src o) =
  @ispan_feed semantic_pos semantic_inline_cursor c (erase_inlines kids) image
    null_span p src (erase_ostate o).
Proof.
  intros P C c kids image open p src o. unfold ispan_feed.
  destruct (ap_failed (astep p c)).
  - rewrite erase_bspan_lit.
    destruct (@bspan_lit P C kids image src o) as [txt o']; cbn [fst snd].
    apply erase_ilead.
  - destruct (ap_done (astep p c)); [|reflexivity].
    cbn [erase_iscan]. rewrite erase_oemit, erase_add_inline_role,
      erase_ospan_bang.
    cbn [erase_inode]. rewrite erase_span_node. reflexivity.
Qed.

Lemma erase_inote_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c esc image label open o,
  erase_iscan (@inote_step P C c esc image label open o) =
  @inote_step semantic_pos semantic_inline_cursor c esc image label null_span
    (erase_ostate o).
Proof.
  intros P C c esc image label open o. unfold inote_step.
  destruct esc; [reflexivity|].
  destruct (is_bslash c); [reflexivity|].
  destruct (Ascii.eqb c rbrack); [|reflexivity].
  cbn [erase_iscan]. rewrite erase_oemit, erase_imk, erase_ospan_bang.
  reflexivity.
Qed.

Lemma erase_iauto_step : forall `{P : PosPolicy} `{C : InlineCursor}
  c src txt o,
  erase_iscan (@iauto_step P C c src txt o) =
  @iauto_step semantic_pos semantic_inline_cursor c src txt (erase_ostate o).
Proof.
  intros P C c src txt o. unfold iauto_step.
  destruct (Ascii.eqb c gt && auto_body_ok src && auto_kind_ok src)%bool.
  - cbn [erase_iscan]. rewrite erase_oemit, erase_imk, erase_auto_node,
      erase_flush_text_to_at. reflexivity.
  - destruct (Ascii.eqb c gt || is_ws c || Ascii.eqb c lt)%bool;
      [apply erase_ilead|reflexivity].
Qed.

Lemma erase_iraw_step_at : forall `{P : PosPolicy} `{C : InlineCursor}
  allow c spec txt o,
  erase_iscan (@iraw_step_at P C allow c spec txt o) =
  @iraw_step_at semantic_pos semantic_inline_cursor allow c spec txt
    (erase_ostate o).
Proof.
  intros P C allow c spec txt o. unfold iraw_step_at.
  destruct (Ascii.eqb c rbrace && raw_spec_ok spec)%bool.
  - destruct raw_inline_enabled.
    + cbn [erase_iscan]. rewrite erase_oemit, erase_imk. reflexivity.
    + rewrite erase_ilead, erase_oemit, erase_imk. reflexivity.
  - destruct (match spec with
              | EmptyString => negb (Ascii.eqb c eqchar)
              | _ => (Ascii.eqb c rbrace || raw_stop c)%bool
              end);
      [|reflexivity].
    destruct spec as [|d spec];
      [rewrite erase_ibrace_step_at|rewrite erase_ilead];
      rewrite erase_oemit, erase_imk; reflexivity.
Qed.

Lemma erase_iscan_attr : forall ap src txt prev sh o,
  erase_iscan (IAttr ap src txt prev sh o) =
  IAttr ap src txt prev (erase_iscan sh) (erase_ostate o).
Proof. reflexivity. Qed.

Lemma erase_iscan_dest : forall kids image open esc depth dst sh o,
  erase_iscan (IDest kids image open esc depth dst sh o) =
  IDest (erase_inlines kids) image null_span esc depth dst
    (erase_iscan sh) (erase_ostate o).
Proof. reflexivity. Qed.

(*
The transition erases
---------------------

The inline half of C2, and uniform in the policy on purpose: at
`located_pos` it says the spans the scan records are all that
distinguishes it from the semantic reading, and at `semantic_pos` the
same statement says the semantic reading is position-free, which is what
the block erasure needs wherever a paragraph is still built by the
ambient instance.  No branch reads a coordinate, so every case closes by
rewriting erasure through the state the branch builds.
*)
Theorem erase_istep_at :
  forall `{P : PosPolicy} `{C : InlineCursor} allow c st,
  erase_iscan (@istep_at P C allow c st) =
  @istep_at semantic_pos semantic_inline_cursor allow c (erase_iscan st).
Proof.
  intros P C allow c st. revert allow c.
  induction st as
    [esc txt prev o | ws txt prev o | txt prev o
    | k extra txt before marked o | n vk o | n run txt vk o
    | two txt prev o | two txt prev o | n txt prev o | txt prev o
    | txt o | kids image open ap src o | ap src txt prev sh IHsh o
    | kids image open label o | esc image label open o
    | kids image open esc depth dst sh IHsh o | src txt o | spec txt o ];
    intros allow c.
  - (* IText *)
    destruct esc; cbn [erase_iscan istep_at].
    + destruct (is_ws c); reflexivity.
    + apply erase_ilead.
  - (* IEscWs *)
    cbn [erase_iscan istep_at]. destruct (is_ws c); [reflexivity|].
    pose proof (erase_iescws_resolve (P:=P) (C:=C) ws txt prev o) as H.
    destruct (@iescws_resolve P C ws txt prev o) as [[t pv] o'].
    rewrite H. apply erase_ilead.
  - (* IBrace *) apply erase_ibrace_step_at.
  - (* IDelim *)
    cbn [erase_iscan istep_at].
    destruct (Nat.ltb (S extra) (dwidth k)).
    { destruct (Ascii.eqb c (dchar k));
        [destruct marked; reflexivity|apply erase_ilead]. }
    destruct marked.
    { rewrite erase_ilead, erase_oopen_marked. reflexivity. }
    pose proof (erase_idelim_resolve (P:=P) (C:=C) k txt before
                  (Ascii.eqb c rbrace) (Some c) o) as Hr.
    destruct (Ascii.eqb c rbrace); [exact Hr|].
    rewrite <- Hr.
    destruct (@idelim_resolve P C k txt before false (Some c) o)
      as [esc' txt' prev' o'| | | | | | | | | | | | | | | | |];
      try reflexivity.
    destruct esc'; [reflexivity|apply erase_ilead].
  - (* IOpen *)
    cbn [erase_iscan istep_at]. destruct (is_tick c); reflexivity.
  - (* IVerb *)
    cbn [erase_iscan istep_at]. destruct (is_tick c); [reflexivity|].
    destruct (Nat.eqb run n); [|reflexivity].
    destruct (Ascii.eqb c lbrace && vkind_verb vk)%bool; [reflexivity|].
    rewrite erase_ilead, erase_oemit, erase_imk, erase_vnode. reflexivity.
  - (* IDollar *) apply erase_idollar_step.
  - (* IPeriod *) apply erase_iperiod_step.
  - (* IDash *) apply erase_idash_step.
  - (* IBang *) apply erase_ibang_step.
  - (* IClosed *)
    cbn [erase_iscan istep_at].
    destruct (Ascii.eqb c lparen || Ascii.eqb c lbrack
              || (Ascii.eqb c lbrace && allow))%bool;
      [|apply erase_ilead].
    sem_flush.
    rewrite <- (erase_flush_text_to_at (previous_spot cursor_start) txt o).
    rewrite erase_bclose.
    destruct (@bclose P (@flush_text_to_at P C
                (previous_spot cursor_start) txt o))
      as [[[[kids image] open] o']|]; [|apply erase_ilead].
    destruct (Ascii.eqb c lparen);
      [cbn [erase_iscan]; rewrite erase_idest_open; reflexivity|].
    destruct (Ascii.eqb c lbrack); reflexivity.
  - (* ISpan *) apply erase_ispan_feed.
  - (* IAttr *)
    rewrite erase_iscan_attr. cbn [istep_at].
    destruct (ap_failed (astep ap c)); [apply IHsh|].
    rewrite erase_iattr_feed, IHsh. reflexivity.
  - (* IReference *)
    cbn [erase_iscan istep_at]. destruct (Ascii.eqb c rbrack); [|reflexivity].
    cbn [erase_iscan]. rewrite erase_oemit, erase_imk, erase_bnode.
    destruct label; [rewrite erase_reference_inlines_text|]; reflexivity.
  - (* INote *) apply erase_inote_step.
  - (* IDest *)
    rewrite erase_iscan_dest. destruct esc; cbn [istep_at].
    + rewrite erase_iscan_dest, IHsh. reflexivity.
    + destruct (is_bslash c);
        [rewrite erase_iscan_dest, IHsh; reflexivity|].
      destruct (Ascii.eqb c lparen);
        [rewrite erase_iscan_dest, IHsh; reflexivity|].
      destruct (Ascii.eqb c rparen);
        [|rewrite erase_iscan_dest, IHsh; reflexivity].
      destruct depth as [|d];
        [|rewrite erase_iscan_dest, IHsh; reflexivity].
      cbn [erase_iscan]. rewrite erase_oemit, erase_imk, erase_bnode.
      reflexivity.
  - (* IAuto *) apply erase_iauto_step.
  - (* IRaw *) apply erase_iraw_step_at.
Qed.

Lemma erase_ifinish_ostate_flat : forall `{P : PosPolicy} `{C : InlineCursor} st,
  erase_ostate (@ifinish_ostate_flat P C st) =
  @ifinish_ostate_flat semantic_pos semantic_inline_cursor (erase_iscan st).
Proof.
  intros P C
    [esc txt prev o | ws txt prev o | txt prev o
    | k extra txt before marked o | n vk o | n run txt vk o
    | two txt prev o | two txt prev o | n txt prev o | txt prev o
    | txt o | kids image open ap src o | ap src txt prev sh o
    | kids image open label o | esc image label open o
    | kids image open esc depth dst sh o | src txt o | spec txt o ];
    cbn [erase_iscan ifinish_ostate_flat];
    try reflexivity.
  - destruct esc; [apply erase_iesc_hard|apply erase_flush_text_at].
  - apply erase_iesc_hard.
  - rewrite erase_oemit, erase_imk, erase_vnode. reflexivity.
  - rewrite erase_oemit, erase_imk, erase_vnode. reflexivity.
  - rewrite erase_bspan_lit.
    destruct (@bspan_lit P C kids image src o) as [t o']; cbn [fst snd].
    apply erase_flush_text_at.
  - rewrite erase_battr_lit.
    destruct (@battr_lit P C src txt o) as [t o']; cbn [fst snd].
    apply erase_flush_text_at.
  - rewrite erase_bref_lit.
    destruct (@bref_lit P C kids image label o) as [t o']; cbn [fst snd].
    apply erase_flush_text_at.
  - rewrite erase_bnote_lit.
    destruct (@bnote_lit P C esc image label o) as [t o']; cbn [fst snd].
    apply erase_flush_text_at.
  - apply erase_flush_text_at.
  - rewrite erase_flush_text_at, erase_oemit, erase_imk. reflexivity.
Qed.

Lemma erase_ifinish_ostate : forall `{P : PosPolicy} `{C : InlineCursor} st,
  erase_ostate (@ifinish_ostate P C st) =
  @ifinish_ostate semantic_pos semantic_inline_cursor (erase_iscan st).
Proof.
  intros P C st. induction st;
    try (cbn [ifinish_ostate];
         rewrite erase_ifinish_ostate_flat, erase_iresolve; reflexivity).
  - rewrite erase_iscan_attr. cbn [ifinish_ostate]. assumption.
  - rewrite erase_iscan_dest. cbn [ifinish_ostate]. assumption.
Qed.

Lemma erase_oflatten : forall `{P : PosPolicy} pend stk bottom,
  erase_oitems (@oflatten P pend stk bottom) =
  @oflatten semantic_pos (erase_oitems pend) (map erase_frame stk)
    (erase_oitems bottom).
Proof.
  intros P pend stk. revert pend.
  induction stk as [|f stk IH]; intros pend bottom; [apply erase_oapp|].
  cbn [map oflatten].
  change (fr_out (erase_frame f)) with (erase_oitems (fr_out f)).
  rewrite (erase_fr_lit f), <- erase_oapp.
  specialize (IH (oapp (oapp pend (fr_out f)) [OIn (@fr_lit P f)]) bottom).
  rewrite !erase_oapp in IH. cbn [erase_oitems erase_oitem] in IH.
  rewrite <- erase_oapp in IH. exact IH.
Qed.

Lemma erase_oitems_of : forall `{P : PosPolicy} o,
  erase_oitems (@oitems_of P o) =
  @oitems_of semantic_pos (erase_ostate o).
Proof.
  intros P o. unfold oitems_of.
  change (os_stk (erase_ostate o)) with (map erase_frame (os_stk o)).
  change (os_out (erase_ostate o)) with (erase_oitems (os_out o)).
  change (@nil oitem) with (erase_oitems []) at 1.
  apply erase_oflatten.
Qed.

Lemma erase_ofinish : forall `{P : PosPolicy} o,
  erase_inlines (@ofinish P o) = @ofinish semantic_pos (erase_ostate o).
Proof.
  intros P o. unfold ofinish.
  rewrite erase_oresolve, erase_oitems_of. reflexivity.
Qed.

Lemma erase_ifinish : forall `{P : PosPolicy} `{C : InlineCursor} st,
  erase_inlines (@ifinish P C st) =
  @ifinish semantic_pos semantic_inline_cursor (erase_iscan st).
Proof.
  intros P C st. unfold ifinish, ifinish_rev.
  rewrite erase_inlines_rev, erase_ofinish, erase_ifinish_ostate. reflexivity.
Qed.

Lemma erase_ibreak_flat : forall `{P : PosPolicy} `{C : InlineCursor} st,
  erase_iscan (@ibreak_flat P C st) =
  @ibreak_flat semantic_pos semantic_inline_cursor (erase_iscan st).
Proof.
  intros P C
    [esc txt prev o | ws txt prev o | txt prev o
    | k extra txt before marked o | n vk o | n run txt vk o
    | two txt prev o | two txt prev o | n txt prev o | txt prev o
    | txt o | kids image open ap src o | ap src txt prev sh o
    | kids image open label o | esc image label open o
    | kids image open esc depth dst sh o | src txt o | spec txt o ];
    cbn [erase_iscan ibreak_flat];
    try reflexivity.
  - destruct esc; cbn [erase_iscan];
      rewrite erase_oword_reset;
      [rewrite erase_iesc_hard; reflexivity|].
    rewrite erase_oemit, erase_imk_here, erase_flush_text_at. reflexivity.
  - cbn [erase_iscan]. rewrite erase_oword_reset, erase_iesc_hard. reflexivity.
  - destruct (Nat.eqb run n); [|reflexivity].
    cbn [erase_iscan]. rewrite erase_oword_reset, erase_oemit, erase_imk_here,
      erase_oemit, erase_imk, erase_vnode. reflexivity.
  - apply erase_ispan_feed.
  - rewrite erase_iattr_feed. reflexivity.
  - cbn [erase_iscan]. rewrite erase_oword_reset, erase_oemit, erase_imk_here,
      erase_flush_text_at. reflexivity.
  - cbn [erase_iscan]. rewrite erase_oword_reset, erase_oemit, erase_imk_here,
      erase_flush_text_at, erase_oemit, erase_imk. reflexivity.
Qed.

Lemma erase_ibreak_at : forall `{P : PosPolicy} `{C : InlineCursor} allow st,
  erase_iscan (@ibreak_at P C allow st) =
  @ibreak_at semantic_pos semantic_inline_cursor allow (erase_iscan st).
Proof.
  intros P C allow st. revert allow. induction st; intros allow;
    try (cbn [ibreak_at];
         rewrite erase_ibreak_flat, erase_iresolve; reflexivity).
  - rewrite erase_iscan_attr. cbn [ibreak_at].
    rewrite erase_iattr_feed, IHst. reflexivity.
  - rewrite erase_iscan_dest. cbn [ibreak_at].
    rewrite erase_iscan_dest, IHst. reflexivity.
Qed.

(* The semantic driver the located one erases to.  `iscan_str` and
   `iscan_str_off` are its two instances; it exists so that one statement
   covers a paragraph whose leading lines a failed block spec handed
   back. *)
Fixpoint iscan_str_at (allow : bool) (s : string) (st : iscan) : iscan :=
  match s with
  | EmptyString => st
  | String c rest =>
      iscan_str_at allow rest
        (@istep_at semantic_pos semantic_inline_cursor allow c st)
  end.

Lemma iscan_str_at_on : forall s st,
  iscan_str_at inline_attrs_enabled s st = iscan_str s st.
Proof. induction s as [|c s IH]; intros st; [reflexivity|apply IH]. Qed.

Lemma iscan_str_at_off : forall s st,
  iscan_str_at false s st = iscan_str_off s st.
Proof. induction s as [|c s IH]; intros st; [reflexivity|apply IH]. Qed.

Lemma erase_iscan_str_located :
  forall `{P : PosPolicy} allow k origin rem s st,
  erase_iscan (@iscan_str_located P allow k origin rem s st) =
  iscan_str_at allow s (erase_iscan st).
Proof.
  intros P allow k origin rem s. revert rem.
  induction s as [|c s IH]; intros rem st; [reflexivity|].
  cbn [iscan_str_located iscan_str_at]. rewrite IH, erase_istep_at.
  reflexivity.
Qed.

(* The driver's two step equations, so that a proof over a paragraph's
   lines rewrites rather than reduces: `cbn` unfolds the recursive call
   as well and loses the name. *)
Lemma iscan_lines_located_one : forall `{P : PosPolicy} off k x st,
  @iscan_lines_located P off [(k, x)] st =
  @iscan_str_located P (allow_attrs off) k (String.length x)
    (String.length x) (strip_trailing_ws x) st.
Proof. reflexivity. Qed.

Lemma iscan_lines_located_cons : forall `{P : PosPolicy} off k x y rest st,
  @iscan_lines_located P off ((k, x) :: y :: rest)%list st =
  @iscan_lines_located P (pred off) (y :: rest)%list
    (@ibreak_at P
       (CursorAt (Spot k 0) (lines_start (y :: rest)%list)
          (Spot k (String.length x)))
       (allow_attrs off)
       (@iscan_str_located P (allow_attrs off) k (String.length x)
          (String.length x) x st)).
Proof. reflexivity. Qed.

Lemma erase_iscan_lines_located : forall `{P : PosPolicy} off l st,
  erase_iscan (@iscan_lines_located P off l st) =
  iscan_lines_off off (map snd l) (erase_iscan st).
Proof.
  intros P off l. revert off.
  induction l as [|[k x] l IH]; intros off st.
  - destruct off; reflexivity.
  - destruct l as [|kx l'].
    + rewrite iscan_lines_located_one, erase_iscan_str_located.
      destruct off as [|off'];
        [cbn [iscan_lines_off iscan_lines map snd]; apply iscan_str_at_on
        |cbn [iscan_lines_off map snd]; apply iscan_str_at_off].
    + rewrite iscan_lines_located_cons, IH, erase_ibreak_at,
        erase_iscan_str_located.
      destruct off as [|off'];
        [cbn [allow_attrs iscan_lines_off iscan_lines map snd];
         rewrite iscan_str_at_on; reflexivity
        |cbn [allow_attrs iscan_lines_off map snd];
         rewrite iscan_str_at_off; reflexivity].
Qed.

(* The same at the ambient instance, which the statement above reads as
   the semantic scan being position-free. *)
Lemma erase_iscan_str_at : forall allow s st,
  erase_iscan (iscan_str_at allow s st) = iscan_str_at allow s (erase_iscan st).
Proof.
  intros allow s. induction s as [|c s IH]; intros st; [reflexivity|].
  cbn [iscan_str_at]. rewrite IH, erase_istep_at. reflexivity.
Qed.

(* The ambient driver's step equations, for the same reason. *)
Lemma iscan_lines_off_O : forall l st, iscan_lines_off 0 l st = iscan_lines l st.
Proof. reflexivity. Qed.

Lemma iscan_lines_last : forall x st,
  iscan_lines [x] st = iscan_str (strip_trailing_ws x) st.
Proof. reflexivity. Qed.

Lemma iscan_lines_step : forall x y rest st,
  iscan_lines (x :: y :: rest)%list st =
  iscan_lines (y :: rest)%list
    (@ibreak semantic_pos semantic_inline_cursor (iscan_str x st)).
Proof. reflexivity. Qed.

Lemma iscan_lines_off_last : forall k x st,
  iscan_lines_off (S k) [x] st = iscan_str_off (strip_trailing_ws x) st.
Proof. reflexivity. Qed.

Lemma iscan_lines_off_step : forall k x y rest st,
  iscan_lines_off (S k) (x :: y :: rest)%list st =
  iscan_lines_off k (y :: rest)%list
    (@ibreak_at semantic_pos semantic_inline_cursor false (iscan_str_off x st)).
Proof. reflexivity. Qed.

Lemma erase_iscan_lines_off : forall off l st,
  erase_iscan (iscan_lines_off off l st) =
  iscan_lines_off off l (erase_iscan st).
Proof.
  intros off l. revert off.
  induction l as [|x l IH]; intros off st.
  - destruct off; reflexivity.
  - destruct l as [|y l'].
    + destruct off as [|off'].
      * rewrite !iscan_lines_off_O, !iscan_lines_last, <- !iscan_str_at_on.
        apply erase_iscan_str_at.
      * rewrite !iscan_lines_off_last, <- !iscan_str_at_off.
        apply erase_iscan_str_at.
    + destruct off as [|off'].
      * rewrite !iscan_lines_off_O, !iscan_lines_step, <- !iscan_lines_off_O,
          IH. unfold ibreak.
        rewrite erase_ibreak_at, <- !iscan_str_at_on, erase_iscan_str_at.
        reflexivity.
      * rewrite !iscan_lines_off_step, IH, erase_ibreak_at,
          <- !iscan_str_at_off, erase_iscan_str_at. reflexivity.
Qed.

Lemma erase_ifinish_located : forall `{P : PosPolicy} l st,
  erase_inlines (@ifinish_located P l st) =
  @ifinish semantic_pos semantic_inline_cursor (erase_iscan st).
Proof. intros P l st. apply erase_ifinish. Qed.

Lemma iscan_str_app :
  forall a b st, iscan_str (a ++ b) st = iscan_str b (iscan_str a st).
Proof.
  induction a as [|c a IH]; intros b st; cbn [iscan_str]; [reflexivity|].
  apply IH.
Qed.

Lemma iscan_open_ticks_more :
  forall k n vk out,
    iscan_str (ticks k) (IOpen n vk out) = IOpen (n + k) vk out.
Proof.
  induction k as [|k IH]; intros n vk out.
  - cbn [ticks iscan_str]. f_equal. lia.
  - cbn [ticks iscan_str istep istep_at]. change
      (iscan_str (ticks k) (IOpen (S n) vk out) = IOpen (n + S k) vk out).
    rewrite IH. f_equal. lia.
Qed.

Lemma iscan_open_ticks :
  forall k txt prev o,
    iscan_str (ticks (S k)) (IText false txt prev o)
    = IOpen (S k) VVerb (flush_text txt o).
Proof.
  intros k txt prev o. cbn [ticks iscan_str istep istep_at ilead]. change
    (iscan_str (ticks k) (IOpen 1 VVerb (flush_text txt o))
     = IOpen (S k) VVerb (flush_text txt o)).
  rewrite iscan_open_ticks_more. f_equal.
Qed.

Lemma iscan_verb_ticks_more :
  forall k n run txt vk out,
    iscan_str (ticks k) (IVerb n run txt vk out) = IVerb n (run + k) txt vk out.
Proof.
  induction k as [|k IH]; intros n run txt vk out.
  - cbn [ticks iscan_str]. f_equal. lia.
  - cbn [ticks iscan_str istep istep_at]. change
      (iscan_str (ticks k) (IVerb n (S run) txt vk out)
       = IVerb n (run + S k) txt vk out).
    rewrite IH. f_equal. lia.
Qed.

Lemma iscan_open_body :
  forall s n vk out,
    nonempty_str s = true -> starts_tick s = false -> n <> 0 ->
    iscan_str s (IOpen n vk out) = iscan_str s (IVerb n 0 EmptyString vk out).
Proof.
  intros [|c s] n vk out Hne Hstart Hn; [discriminate|].
  cbn [starts_tick] in Hstart. cbn [iscan_str istep istep_at]. rewrite Hstart.
  replace (Nat.eqb 0 n) with false.
  - reflexivity.
  - destruct n; [contradiction|reflexivity].
Qed.

Lemma iscan_verb_safe_nonempty :
  forall s n run txt vk out,
    nonempty_str s = true -> ends_tick s = false ->
    verb_safe_from n run s = true ->
    iscan_str s (IVerb n run txt vk out)
    = IVerb n 0 (txt ++ ticks run ++ s) vk out.
Proof.
  induction s as [|c rest IH]; intros n run txt vk out Hne Hend Hsafe;
    [discriminate|].
  cbn [iscan_str verb_safe_from] in Hsafe |- *.
  destruct (is_tick c) eqn:Hc.
  - cbn [istep istep_at]. rewrite Hc. destruct rest as [|d rest'].
    + unfold ends_tick, starts_tick, rev_string in Hend.
      cbn [rev_string_aux] in Hend. rewrite Hc in Hend. discriminate.
    + rewrite ends_tick_cons_nonempty in Hend.
      rewrite (IH n (S run) txt vk out eq_refl Hend Hsafe).
      apply Ascii.eqb_eq in Hc. subst c. f_equal.
      rewrite ticks_succ_r, !append_assoc. reflexivity.
  - apply andb_true_iff in Hsafe as [Hrun Hsafe].
    apply negb_true_iff in Hrun. cbn [istep istep_at]. rewrite Hc, Hrun.
    destruct rest as [|d rest'].
    + cbn [iscan_str]. f_equal.
    + rewrite ends_tick_cons_nonempty in Hend.
      rewrite (IH n 0 (txt ++ ticks run ++ one c) vk out eq_refl Hend Hsafe).
      f_equal. cbn [ticks one]. rewrite !append_assoc. reflexivity.
Qed.

Lemma iscan_verb_text_nonempty :
  forall s txt prev o,
    nonempty_str s = true ->
    verb_safe (verb_ticks s) (pad_verb s) = true ->
    iscan_str (verb_text s) (IText false txt prev o)
    = IVerb (verb_ticks s) (verb_ticks s) (pad_verb s) VVerb (flush_text txt o).
Proof.
  intros s txt prev o Hne Hsafe. unfold verb_text.
  rewrite !iscan_str_app.
  destruct (verb_ticks s) as [|k] eqn:Hn;
    [exfalso; apply (verb_ticks_nonzero s); exact Hn|].
  rewrite iscan_open_ticks.
  unfold verb_safe in Hsafe.
  rewrite (iscan_open_body (pad_verb s) (S k) VVerb (flush_text txt o)
             (pad_verb_nonempty s Hne) (pad_verb_starts_nontick s Hne))
    by discriminate.
  rewrite (iscan_verb_safe_nonempty (pad_verb s) (S k) 0 EmptyString VVerb
             (flush_text txt o) (pad_verb_nonempty s Hne)
             (pad_verb_ends_nontick s Hne) Hsafe).
  change (iscan_str (ticks (S k))
            (IVerb (S k) 0 (pad_verb s) VVerb (flush_text txt o))
          = IVerb (S k) (S k) (pad_verb s) VVerb (flush_text txt o)).
  rewrite iscan_verb_ticks_more. f_equal.
Qed.

(*
The output frame
----------------

Every state carries the inlines emitted so far, in reverse, and every
transition only ever conses onto them.  So a fixed suffix rides through
the whole scan untouched, and `ifinish` reverses it out at the front.
This is what lets a paragraph be assembled one line at a time from a
scan that does not restart: the lines after the first run against a
suffix holding the lines before it. *)

Definition istart : iscan := IText false EmptyString None ostart.

(* Appending at the *bottom* -- `os_out`, the outermost scope -- is what
   makes this commute with every transition: pushing and popping scopes
   only ever touch `os_stk`, so the suffix is out of their reach. *)
Definition oout_app (base : oitems) (o : ostate) : ostate :=
  OState (os_out o ++ base)%list (os_stk o) (os_word_start o).

(* What a suffix always is: empty, or a previous line, whose most recent
   node is the `SoftBreak` that ended it.  Every `_app` lemma below asks
   this of its suffix, and the one caller -- `para_inlines_cons2_closed`
   -- discharges it by `reflexivity`, because it builds the suffix by
   consing that very break.

   The weaker `starts_str base = false` is all the seam merge in
   `osnoc_nonstr` needs, but not enough for attachment, which reads the
   current scope: a scope that has emitted nothing sees the suffix's head
   there, so a suffix headed by anything *else* would make the same query
   answer two ways across a splice.  `oresolve` asks that question of
   that same list, which is why `oattach_list` refuses a `SoftBreak`. *)
Definition base_ok (base : oitems) : bool :=
  match base with
  | [] => true
  | OIn (Node _ _ SoftBreak) :: _ => true
  | _ => false
  end.

Lemma base_ok_starts_str :
  forall base, base_ok base = true -> starts_str base = false.
Proof.
  intros [|[[p [|kv a'] v]|ma] base] H; try reflexivity.
  destruct v; try reflexivity. discriminate.
Qed.

Fixpoint iout_app (base : oitems) (st : iscan) : iscan :=
  match st with
  | IText esc txt prev o => IText esc txt prev (oout_app base o)
  | IEscWs ws txt prev o => IEscWs ws txt prev (oout_app base o)
  | IBrace txt prev o => IBrace txt prev (oout_app base o)
  | IDelim k seen txt cc m o => IDelim k seen txt cc m (oout_app base o)
  | IOpen n vk o => IOpen n vk (oout_app base o)
  | IVerb n run txt vk o => IVerb n run txt vk (oout_app base o)
  | IDollar two txt prev o => IDollar two txt prev (oout_app base o)
  | IBang txt prev o => IBang txt prev (oout_app base o)
  | IPeriod two txt prev o => IPeriod two txt prev (oout_app base o)
  | IDash n txt prev o => IDash n txt prev (oout_app base o)
  | IClosed txt o => IClosed txt (oout_app base o)
  | ISpan kids image open p src o =>
      ISpan kids image open p src (oout_app base o)
  | IAttr p src txt prev sh o =>
      IAttr p src txt prev (iout_app base sh) (oout_app base o)
  | INote esc image label open o =>
      INote esc image label open (oout_app base o)
  | IReference kids image open label o =>
      IReference kids image open label (oout_app base o)
  | IDest kids image open esc depth dst sh o =>
      IDest kids image open esc depth dst
        (iout_app base sh) (oout_app base o)
  | IAuto src txt o => IAuto src txt (oout_app base o)
  | IRaw spec txt o => IRaw spec txt (oout_app base o)
  end.

Lemma oemit_app :
  forall n o base,
    oemit n (oout_app base o) = oout_app base (oemit n o).
Proof.
  intros n [out [|f stk] word] base; reflexivity.
Qed.

Lemma flush_text_app :
  forall txt o base,
    flush_text txt (oout_app base o) = oout_app base (flush_text txt o).
Proof.
  intros txt o base. unfold flush_text, flush_text_at.
  destruct (nonempty_str txt); [apply oemit_app | reflexivity].
Qed.


Lemma opush_at_app :
  forall k m cm open o base,
    opush_at k m cm open (oout_app base o)
    = oout_app base (opush_at k m cm open o).
Proof. intros k m cm open o base. reflexivity. Qed.

Lemma opush_app :
  forall k m o base,
    opush k m (oout_app base o) = oout_app base (opush k m o).
Proof. intros k m o base. reflexivity. Qed.

Lemma oclose_app :
  forall `{P : PosPolicy} k m stop o base,
    oclose k m stop (oout_app base o)
    = option_map (oout_app base) (oclose k m stop o).
Proof.
  intros P k m stop o base. unfold oclose. cbn [oout_app os_stk os_out].
  destruct (oclose_go k m [] (os_stk o)) as [[[content open] rest]|];
    [|reflexivity].
  cbn [option_map].
  rewrite <- (oemit_app
                (imk (span_start open) stop
                   (dnode k (List.rev (oresolve content))))
                (OState (os_out o) rest (os_word_start o)) base).
  reflexivity.
Qed.

Lemma sclose_app :
  forall k m o base,
    sclose k m (oout_app base o) = option_map (oout_app base) (sclose k m o).
Proof. intros k m o base. apply oclose_app. Qed.

Lemma bpush_app :
  forall image o base,
    bpush image (oout_app base o) = oout_app base (bpush image o).
Proof. intros image o base. reflexivity. Qed.

(* Taking a bracket back reads only the stack, which the suffix never
   touches. *)
Lemma bunpush_app :
  forall o base,
    bunpush (oout_app base o)
    = option_map
        (fun p => let '(image, open, o') := p in
                  (image, open, oout_app base o'))
        (bunpush o).
Proof.
  intros [out [|f stk] word] base; [reflexivity|].
  destruct f as [[k|im|im] m open [|n l]]; reflexivity.
Qed.

Lemma bclose_app :
  forall o base,
    bclose (oout_app base o)
    = option_map
        (fun p => let '(kids, image, open, o') := p in
                  (kids, image, open, oout_app base o'))
        (bclose o).
Proof.
  intros o base. unfold bclose. cbn [oout_app os_stk os_out].
  destruct (bclose_go [] (os_stk o))
    as [[[[content image] open] rest]|]; reflexivity.
Qed.

(* The bracket reconstruction is the second place the suffix is not
   inert, and for the same reason as `oflatten`: `opop_str` reads the
   most recent node, and with nothing emitted yet that node comes from
   the suffix.  The hypothesis is the one `ofinish_out_app` already
   carries, and its single caller discharges it the same way -- the
   suffix is a previous line, ending in a `SoftBreak`. *)
Lemma opop_str_app :
  forall o base,
    base_ok base = true ->
    opop_str (oout_app base o)
    = (fst (opop_str o), oout_app base (snd (opop_str o))).
Proof.
  intros [out stk] base Hb. unfold opop_str, oout_app; cbn [os_out os_stk].
  destruct stk as [|f fs].
  - destruct out as [|n rest]; cbn [app].
    + destruct base as [|[[a [|p ps] i]|ma] base']; try reflexivity.
      destruct i; try reflexivity. discriminate.
    + destruct n as [[a [|p ps] i]|ma]; try reflexivity.
      destruct i; reflexivity.
  - destruct (fr_out f) as [|n rest]; [reflexivity|].
    destruct n as [[a [|p ps] i]|ma]; try reflexivity.
    destruct i; reflexivity.
Qed.

Lemma bflat_app :
  forall kids txt o base,
    bflat kids txt (oout_app base o)
    = (fst (bflat kids txt o), oout_app base (snd (bflat kids txt o))).
Proof.
  induction kids as [|[a attrs i] kids IH]; intros txt o base; cbn [bflat].
  - reflexivity.
  - destruct attrs as [|p ps];
      [destruct i; try (rewrite flush_text_app, oemit_app; apply IH); apply IH
      |rewrite flush_text_app, oemit_app; apply IH].
Qed.

Lemma bsplit_nl_app :
  forall s txt o base,
    bsplit_nl s txt (oout_app base o)
    = (fst (bsplit_nl s txt o), oout_app base (snd (bsplit_nl s txt o))).
Proof.
  induction s as [|c s IH]; intros txt o base; cbn [bsplit_nl];
    [reflexivity|].
  destruct (Ascii.eqb c nl_char);
    [rewrite flush_text_app, oemit_app|]; apply IH.
Qed.

Lemma dpush_app :
  forall image open o base,
    dpush image open (oout_app base o) =
    oout_app base (dpush image open o).
Proof. intros image open o base. reflexivity. Qed.

Lemma idest_open_app :
  forall kids image open o base,
    idest_open kids image open (oout_app base o)
    = iout_app base (idest_open kids image open o).
Proof.
  intros kids image open o base. unfold idest_open.
  rewrite dpush_app, bflat_app.
  destruct (bflat kids EmptyString (dpush image open o)) as [txt o1].
  reflexivity.
Qed.

Lemma bclosed_lit_app :
  forall kids image o base,
    base_ok base = true ->
    bclosed_lit kids image (oout_app base o)
    = (fst (bclosed_lit kids image o),
       oout_app base (snd (bclosed_lit kids image o))).
Proof.
  intros kids image o base Hb. unfold bclosed_lit.
  rewrite (opop_str_app o base Hb).
  destruct (opop_str o) as [pre o1]; cbn [fst snd].
  rewrite bflat_app.
  destruct (bflat kids (pre ++ bracket_open image)%string o1) as [txt o2].
  reflexivity.
Qed.

Lemma bref_lit_app :
  forall kids image label o base,
    base_ok base = true ->
    bref_lit kids image label (oout_app base o) =
    let '(txt, o') := bref_lit kids image label o in
    (txt, oout_app base o').
Proof.
  intros kids image label o base Hb. unfold bref_lit.
  rewrite (bclosed_lit_app kids image o base Hb).
  destruct (bclosed_lit kids image o). reflexivity.
Qed.

Lemma bnote_lit_app :
  forall esc image label o base,
    base_ok base = true ->
    bnote_lit esc image label (oout_app base o) =
    let '(txt, o') := bnote_lit esc image label o in
    (txt, oout_app base o').
Proof.
  intros esc image label o base Hb. unfold bnote_lit.
  rewrite (opop_str_app o base Hb).
  destruct (opop_str o) as [pre o1]; cbn [fst snd]. reflexivity.
Qed.

Lemma bspan_lit_app :
  forall kids image src o base,
    base_ok base = true ->
    bspan_lit kids image src (oout_app base o) =
    let '(txt, o') := bspan_lit kids image src o in
    (txt, oout_app base o').
Proof.
  intros kids image src o base Hb. unfold bspan_lit.
  rewrite (bclosed_lit_app kids image o base Hb).
  destruct (bclosed_lit kids image o) as [txt o']; cbn [fst snd].
  rewrite bsplit_nl_app.
  destruct (bsplit_nl src (txt ++ one lbrace)%string o'). reflexivity.
Qed.

Lemma battr_lit_app :
  forall src txt o base,
    battr_lit src txt (oout_app base o) =
    let '(t, o') := battr_lit src txt o in (t, oout_app base o').
Proof.
  intros src txt o base. unfold battr_lit. rewrite bsplit_nl_app.
  destruct (bsplit_nl src (txt ++ one lbrace)%string o). reflexivity.
Qed.

Lemma iescws_resolve_app :
  forall ws txt prev o base,
    base_ok base = true ->
    iescws_resolve ws txt prev (oout_app base o)
    = let '(t, p, o') := iescws_resolve ws txt prev o in (t, p, oout_app base o').
Proof.
  intros [|c ws] txt prev o base Hb; cbn [iescws_resolve]; [reflexivity|].
  destruct (Ascii.eqb c " "%char); [|reflexivity].
  rewrite flush_text_app, oemit_app. reflexivity.
Qed.

Lemma ilead_app :
  forall c txt prev o base,
    ilead c txt prev (oout_app base o) = iout_app base (ilead c txt prev o).
Proof.
  intros c txt prev o base. unfold ilead.
  destruct (is_bslash c); [reflexivity|].
  destruct (is_tick c); [cbn [iout_app]; rewrite flush_text_app; reflexivity|].
  destruct (Ascii.eqb c dollar); [reflexivity|].
  destruct (Ascii.eqb c period); [reflexivity|].
  destruct (Ascii.eqb c hyphen); [reflexivity|].
  destruct (Ascii.eqb c lbrace); [reflexivity|].
  destruct (Ascii.eqb c bang); [reflexivity|].
  destruct (Ascii.eqb c lt); [reflexivity|].
  destruct (Ascii.eqb c lbrack);
    [cbn [iout_app]; rewrite flush_text_app, bpush_app; reflexivity|].
  destruct (Ascii.eqb c rbrack); [reflexivity|].
  destruct (Ascii.eqb c hat && note_pos txt prev && notes_enabled)%bool;
    [rewrite bunpush_app;
     destruct (bunpush o) as [[[image open] o']|]; [reflexivity|]|];
    destruct (dstyle_of c); reflexivity.
Qed.

Lemma ospan_bang_app :
  forall image o base,
    base_ok base = true ->
    ospan_bang image (oout_app base o) = oout_app base (ospan_bang image o).
Proof.
  intros image o base Hb. unfold ospan_bang. destruct image; [|reflexivity].
  rewrite (opop_str_app o base Hb).
  destruct (opop_str o) as [pre o1]; cbn [fst snd].
  apply flush_text_app.
Qed.

Lemma omark_app :
  forall a spec o base,
    omark a spec (oout_app base o) = oout_app base (omark a spec o).
Proof.
  intros a spec [out [|f stk] word] base; reflexivity.
Qed.

Lemma iattr_mark_app :
  forall src a txt o base,
    iattr_mark src a txt (oout_app base o) =
    iout_app base (iattr_mark src a txt o).
Proof.
  intros src a txt o base. unfold iattr_mark.
  cbn [iout_app]. rewrite flush_text_app, omark_app. reflexivity.
Qed.

Lemma islice_end_app :
  forall base st,
    islice_end (iout_app base st) = iout_app base (islice_end st).
Proof.
  intros base [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|cltxt clob|kids img open sp ssrc sob|ap asrc atxt aprev ash aob|kids img open label ob|nesc nimg nlab open nob|kids img open esc depth dst sh ob|asrc atxt aob|rspec rtxt rob];
    reflexivity.
Qed.

Lemma iattr_feed_app :
  forall c p src txt prev sh o base,
    base_ok base = true ->
    iattr_feed c p src txt prev (iout_app base sh) (oout_app base o)
    = iout_app base (iattr_feed c p src txt prev sh o).
Proof.
  intros c p src txt prev sh o base Hb. unfold iattr_feed.
  rewrite islice_end_app.
  destruct (ap_failed (astep p c)); [reflexivity|].
  destruct (ap_done (astep p c)); [apply iattr_mark_app|reflexivity].
Qed.

Lemma ispan_feed_app :
  forall c kids image open p src o base,
    base_ok base = true ->
    ispan_feed c kids image open p src (oout_app base o)
    = iout_app base (ispan_feed c kids image open p src o).
Proof.
  intros c kids image open p src o base Hb. unfold ispan_feed.
  destruct (ap_failed (astep p c)).
  - rewrite (bspan_lit_app kids image src o base Hb).
    destruct (bspan_lit kids image src o) as [txt o']. apply ilead_app.
  - destruct (ap_done (astep p c)); [|reflexivity].
    cbn [iout_app]. rewrite ospan_bang_app by exact Hb.
    rewrite oemit_app. reflexivity.
Qed.

Lemma idelim_resolve_app :
  forall k txt bef marker next o base,
    @idelim_resolve semantic_pos semantic_inline_cursor
      k txt bef marker next (oout_app base o)
    = iout_app base
        (@idelim_resolve semantic_pos semantic_inline_cursor
          k txt bef marker next o).
Proof.
  intros k txt bef marker next o base.
  assert (Hdone : forall o',
    @idelim_done semantic_pos semantic_inline_cursor
      k txt bef marker next (oout_app base o')
    = iout_app base
        (@idelim_done semantic_pos semantic_inline_cursor
          k txt bef marker next o')).
  { intros o'. unfold idelim_done.
    destruct (dbare k bef && negb marker && nonspace_at next)%bool;
      [cbn [iout_app]; rewrite flush_text_app, opush_app|]; reflexivity. }
  unfold idelim_resolve. destruct (nonspace_at bef || marker)%bool; [|apply Hdone].
  sem_flush. rewrite flush_text_app, sclose_app.
  destruct (sclose k marker (flush_text txt o)); [reflexivity|].
  unfold oclose_barred, oout_app; cbn [os_stk].
  destruct (oclose_barred_go k marker false (os_stk o)); [reflexivity|].
  apply Hdone.
Qed.

Lemma idelim_open_marked_out_app :
  forall k cm txt base o,
    idelim_open_marked k cm txt (oout_app base o)
    = iout_app base (idelim_open_marked k cm txt o).
Proof.
  intros k cm txt base o.
  unfold idelim_open_marked, oopen_marked. cbn [iout_app].
  sem_flush. rewrite flush_text_app, opush_at_app. reflexivity.
Qed.

Lemma iresolve_app :
  forall base st,
    base_ok base = true ->
    iresolve (iout_app base st) = iout_app base (iresolve st).
Proof.
  intros base [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|cltxt clob|kids img open sp ssrc sob|ap asrc atxt aprev ash aob|kids img open label ob|nesc nimg nlab open nob|kids img open esc depth dst sh ob|asrc atxt aob|rspec rtxt rob] Hb;
    try reflexivity.
  - cbn [iresolve iout_app]. destruct (Nat.ltb (S seen) (dwidth k));
      [reflexivity|].
    destruct mrk; [apply idelim_open_marked_out_app | apply idelim_resolve_app].
Qed.

Lemma idelim_marked_out_app :
  forall k extra txt base o,
    idelim_marked k extra txt (oout_app base o)
    = iout_app base (idelim_marked k extra txt o).
Proof. intros. reflexivity. Qed.

Lemma istep_at_out_app :
  forall attrs_enabled c base st,
    base_ok base = true ->
    istep_at attrs_enabled c (iout_app base st)
    = iout_app base (istep_at attrs_enabled c st).
Proof.
  intros attrs_enabled c base st. revert attrs_enabled c base.
  induction st as [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|cltxt clob|kids img open sp ssrc sob|ap asrc atxt aprev ash IHash aob|kids img open label ob|nesc nimg nlab open nob|kids img open esc depth dst sh IHsh ob|asrc atxt aob|rspec rtxt rob];
    intros attrs_enabled c base Hb; cbn [iout_app istep_at].
  - destruct (is_ws c); reflexivity.
  - apply ilead_app.
  - destruct (is_ws c); [reflexivity|].
    rewrite iescws_resolve_app by exact Hb.
    destruct (iescws_resolve ews etxt eprev eob) as [[t p] o']; cbn [fst snd].
    apply ilead_app.
  - unfold ibrace_step, ibrace_step_at. destruct (dstyle_of c);
      [apply idelim_marked_out_app|].
    destruct attrs_enabled; [rewrite ilead_app; apply iattr_feed_app, Hb|].
    rewrite battr_lit_app. destruct (battr_lit EmptyString txt o) as [t o'].
    apply ilead_app.
  - destruct (Nat.ltb (S seen) (dwidth k)).
    { destruct (Ascii.eqb c (dchar k)); [|apply ilead_app].
      destruct mrk; [apply idelim_marked_out_app|reflexivity]. }
    destruct mrk.
    { unfold oopen_marked. cbn [iout_app].
      rewrite flush_text_app, opush_at_app. apply ilead_app. }
    rewrite idelim_resolve_app. destruct (Ascii.eqb c rbrace); [reflexivity|].
    destruct (idelim_resolve k txt cc false (Some c) o)
      as [[] txt' prev' o'|? ? ? ?|? ? ?|? ? ? ? ? ?|? ? ?|? ? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ?|? ?|? ? ? ? ?|? ? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ? ? ?|? ? ?|? ? ?]; cbn [iout_app];
      try reflexivity.
    apply ilead_app.
  - destruct (is_tick c); reflexivity.
  - destruct (is_tick c); [reflexivity|].
    destruct (Nat.eqb run n); [|reflexivity].
    destruct (Ascii.eqb c lbrace && vkind_verb vk)%bool; [reflexivity|].
    rewrite ?imk_semantic.
    rewrite (oemit_app (mk (vnode vk (trim_verb txt))) o base).
    apply ilead_app.
  - (* a pending `$` either grows, opens a math span, or is text *)
    unfold idollar_step. destruct (Ascii.eqb c dollar);
      [destruct dtwo; reflexivity|].
    destruct (is_tick c && math_enabled)%bool;
      [cbn [iout_app]; rewrite flush_text_app; reflexivity|].
    apply ilead_app.
  - (* a pending `.` either grows, completes an ellipsis, or is text *)
    unfold iperiod_step. destruct (Ascii.eqb c period);
      [destruct ptwo; reflexivity|].
    apply ilead_app.
  - (* a hyphen run either grows, gives its last back to a close marker,
       or is cut into dashes *)
    unfold idash_step. destruct (Ascii.eqb c hyphen); [reflexivity|].
    destruct (Ascii.eqb c rbrace); [|apply ilead_app].
    destruct (dstyle_of hyphen) as [k|]; [|reflexivity].
    destruct (Nat.leb (dwidth k) dn); [apply idelim_resolve_app|reflexivity].
  - unfold ibang_step. destruct (Ascii.eqb c lbrack);
      [cbn [iout_app]; rewrite flush_text_app, bpush_app; reflexivity
      |apply ilead_app].
  - destruct ((Ascii.eqb c lparen || Ascii.eqb c lbrack
               || (Ascii.eqb c lbrace && attrs_enabled))%bool);
      [|apply ilead_app].
    sem_flush. rewrite flush_text_app, bclose_app.
    destruct (bclose (flush_text cltxt clob))
      as [[[[kids image] open] o']|];
      [|apply ilead_app].
    cbn [option_map].
    destruct (Ascii.eqb c lparen);
      [rewrite idest_open_app; reflexivity|].
    destruct (Ascii.eqb c lbrack); reflexivity.
  - apply ispan_feed_app, Hb.
  - destruct (ap_failed (astep ap c)).
    + apply IHash, Hb.
    + rewrite (IHash false c base Hb). apply iattr_feed_app, Hb.
  - destruct (Ascii.eqb c rbrack); [cbn [iout_app]; rewrite oemit_app|];
      reflexivity.
  - unfold inote_step. destruct nesc; [reflexivity|].
    destruct (is_bslash c); [reflexivity|].
    destruct (Ascii.eqb c rbrack); [|reflexivity].
    cbn [iout_app]. rewrite ospan_bang_app by exact Hb.
    rewrite oemit_app. reflexivity.
  - (* both readings advance, and only the balanced close names one *)
    destruct esc; [cbn [iout_app]; rewrite IHsh by exact Hb; reflexivity|].
    destruct (is_bslash c); [cbn [iout_app]; rewrite IHsh by exact Hb; reflexivity|].
    destruct (Ascii.eqb c lparen); [cbn [iout_app]; rewrite IHsh by exact Hb; reflexivity|].
    destruct (Ascii.eqb c rparen);
      [|cbn [iout_app]; rewrite IHsh by exact Hb; reflexivity].
    destruct depth;
      [cbn [iout_app]; rewrite oemit_app; reflexivity
      |cbn [iout_app]; rewrite IHsh by exact Hb; reflexivity].
  - unfold iauto_step.
    destruct (Ascii.eqb c gt && auto_body_ok asrc && auto_kind_ok asrc)%bool;
      [cbn [iout_app]; rewrite flush_text_app, oemit_app; reflexivity|].
    destruct (Ascii.eqb c gt || is_ws c || Ascii.eqb c lt)%bool;
      [apply ilead_app | reflexivity].
  - unfold iraw_step_at. rewrite ?imk_semantic.
    destruct (Ascii.eqb c rbrace && raw_spec_ok rspec)%bool.
    + destruct raw_inline_enabled.
      * cbn [iout_app]. rewrite oemit_app. reflexivity.
      * rewrite (oemit_app (mk (Verbatim rtxt)) rob base). apply ilead_app.
    + destruct rspec as [|x rspec'].
      * destruct (negb (Ascii.eqb c eqchar)); [|reflexivity].
        rewrite (oemit_app (mk (Verbatim rtxt)) rob base).
        unfold ibrace_step_at; destruct (dstyle_of c);
          [apply idelim_marked_out_app|].
        destruct attrs_enabled;
          [rewrite ilead_app; apply iattr_feed_app, Hb|].
        rewrite battr_lit_app. destruct (battr_lit EmptyString "") as [t o'].
        apply ilead_app.
      * destruct (Ascii.eqb c rbrace || raw_stop c)%bool; [|reflexivity].
        rewrite (oemit_app (mk (Verbatim rtxt)) rob base). apply ilead_app.
Qed.

Lemma istep_out_app :
  forall c base st,
    base_ok base = true ->
    istep c (iout_app base st) = iout_app base (istep c st).
Proof.
  intros c base st Hb. unfold istep. apply istep_at_out_app, Hb.
Qed.

Lemma iscan_str_out_app :
  forall s base st,
    base_ok base = true ->
    iscan_str s (iout_app base st) = iout_app base (iscan_str s st).
Proof.
  induction s as [|c s IH]; intros base st Hb; cbn [iscan_str]; [reflexivity|].
  rewrite istep_out_app by exact Hb. apply IH, Hb.
Qed.

Lemma ibreak_flat_app :
  forall base st,
    base_ok base = true ->
    ibreak_flat (iout_app base st) = iout_app base (ibreak_flat st).
Proof.
  intros base [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|cltxt clob|kids img open sp ssrc sob|ap asrc atxt aprev ash aob|kids img open label ob|nesc nimg nlab open nob|kids img open esc depth dst sh ob|asrc atxt aob|rspec rtxt rob] Hb;
    cbn [iout_app ibreak_flat]; try reflexivity.
  all: try (try unfold iesc_hard;
            rewrite flush_text_app, oemit_app; reflexivity).
  - destruct (Nat.eqb run n); [|reflexivity].
    rewrite !oemit_app. reflexivity.
  - apply ispan_feed_app, Hb.
  - apply iattr_feed_app, Hb.
  - rewrite oemit_app, flush_text_app, oemit_app. reflexivity.
Qed.

Lemma ibreak_flat_state_app :
  forall base st,
    base_ok base = true -> is_compound st = false ->
    ibreak (iout_app base st) = iout_app base (ibreak st).
Proof.
  intros base st Hb Hd.
  assert (Hd' : is_compound (iout_app base st) = false)
    by (destruct st; try reflexivity; discriminate Hd).
  rewrite (ibreak_flat_state _ Hd'), (ibreak_flat_state _ Hd).
  rewrite iresolve_app by exact Hb. apply ibreak_flat_app, Hb.
Qed.

Lemma ibreak_at_out_app :
  forall attrs_enabled base st,
    base_ok base = true ->
    ibreak_at attrs_enabled (iout_app base st)
    = iout_app base (ibreak_at attrs_enabled st).
Proof.
  intros attrs_enabled base st. revert attrs_enabled base.
  induction st as [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|cltxt clob|kids img open sp ssrc sob|ap asrc atxt aprev ash IHash aob|kids img open label ob|nesc nimg nlab open nob|kids img open esc depth dst sh IHsh ob|asrc atxt aob|rspec rtxt rob];
    intros attrs_enabled base Hb;
    try (rewrite (ibreak_at_flat_state attrs_enabled) by reflexivity;
         rewrite (ibreak_at_flat_state attrs_enabled) by reflexivity;
         apply ibreak_flat_state_app; [exact Hb|reflexivity]).
  - cbn [ibreak_at iout_app]. rewrite IHash by exact Hb.
    apply iattr_feed_app, Hb.
  - cbn [ibreak_at iout_app]. rewrite IHsh by exact Hb. reflexivity.
Qed.

Lemma ibreak_out_app :
  forall base st,
    base_ok base = true ->
    ibreak (iout_app base st) = iout_app base (ibreak st).
Proof.
  intros base st Hb. unfold ibreak. apply ibreak_at_out_app, Hb.
Qed.

Lemma iscan_lines_cons2 :
  forall x y rest st,
    iscan_lines (x :: y :: rest) st
    = iscan_lines (y :: rest) (ibreak (iscan_str x st)).
Proof. reflexivity. Qed.

Lemma iscan_lines_out_app :
  forall l base st,
    base_ok base = true ->
    iscan_lines l (iout_app base st) = iout_app base (iscan_lines l st).
Proof.
  induction l as [|x [|y rest] IH]; intros base st Hb; cbn [iscan_lines].
  - reflexivity.
  - apply iscan_str_out_app, Hb.
  - rewrite iscan_str_out_app, ibreak_out_app by exact Hb. apply IH, Hb.
Qed.

(* The one place the suffix is not entirely inert: flattening an
   abandoned scope merges a `Str` seam, and if the suffix began with a
   `Str` the merge would reach across into it.  This is the weakest form
   of what `base_ok` says, and the only consumer that needs no more than
   it; the `_app` lemmas carry the stronger fact because `oresolve` reads
   the head rather than merely declining to merge with it. *)
Lemma osnoc_nonstr :
  forall n out, starts_str out = false -> osnoc n out = (n :: out)%list.
Proof.
  intros n [|[[a [|x xs] i]|ma] out'] H; try reflexivity.
  cbn [starts_str] in H. destruct i; try reflexivity.
  destruct n as [[c [|y ys] j]|na]; try reflexivity.
  destruct j; try reflexivity. discriminate.
Qed.

Lemma oapp_one : forall n out, oapp [n] out = osnoc n out.
Proof. reflexivity. Qed.

Lemma oapp_cons2 :
  forall n m rest out, oapp (n :: m :: rest) out = (n :: oapp (m :: rest) out)%list.
Proof. reflexivity. Qed.

Lemma oapp_app :
  forall cur out base,
    base_ok base = true ->
    oapp cur (out ++ base)%list = (oapp cur out ++ base)%list.
Proof.
  induction cur as [|n cur IH]; intros out base Hb; [reflexivity|].
  destruct cur as [|m cur'].
  - rewrite !oapp_one. destruct out as [|x out']; cbn [app].
    + rewrite (osnoc_nonstr n base (base_ok_starts_str base Hb)). reflexivity.
    + destruct x as [[a [|p ps] i]|xa]; [|reflexivity|reflexivity].
      destruct i; try reflexivity.
      destruct n as [[c [|q qs] j]|na]; [|reflexivity|reflexivity].
      destruct j; reflexivity.
  - rewrite !oapp_cons2. cbn [app]. f_equal. apply (IH out base Hb).
Qed.

Lemma oflatten_app :
  forall stk pend bottom base,
    base_ok base = true ->
    oflatten pend stk (bottom ++ base)%list
    = (oflatten pend stk bottom ++ base)%list.
Proof.
  induction stk as [|f stk IH]; intros pend bottom base Hb;
    cbn [oflatten]; [apply oapp_app, Hb | apply IH, Hb].
Qed.

(* A previous line resolves to something headed by the `SoftBreak` that
   ended it, which is what makes the splice invisible to both the seam
   merge and a waiting spec. *)
Lemma oresolve_base_head :
  forall base,
    base_ok base = true -> ibase_ok (oresolve base) = true.
Proof.
  intros [|[[p a v]|ma] base'] H; try discriminate; [reflexivity|].
  destruct v; try discriminate.
  unfold oresolve; cbn [oresolve_go].
  destruct (oresolve_go base') as [out m]; cbn [fst].
  destruct m; [|destruct a; reflexivity].
  destruct a as [|kv a']; rewrite isnoc_nonplain by reflexivity; reflexivity.
Qed.

(* Resolution distributes over the splice: the suffix is already settled
   and nothing in the prefix can reach into it. *)
Lemma oresolve_go_base :
  forall base, base_ok base = true -> snd (oresolve_go base) = false.
Proof.
  intros [|[[p a v]|ma] base'] H; try discriminate; [reflexivity|].
  cbn [oresolve_go]. destruct (oresolve_go base'); reflexivity.
Qed.


(* A waiting spec reads only the head of what is below it, and `base_ok`
   makes that head a `SoftBreak` -- which it declines exactly as it
   declines an empty scope.  So the splice is invisible to it. *)
Lemma oattach_list_app :
  forall a spec word out base,
    base_ok base = true ->
    oattach_list a spec word (out ++ oresolve base)%list
    = (oattach_list a spec word out ++ oresolve base)%list.
Proof.
  intros a spec word out base Hb.
  pose proof (oresolve_base_head base Hb) as Hbi.
  pose proof (ibase_ok_starts_str _ Hbi) as Hh.
  destruct out as [|[p a' v] out]; cbn [app]; unfold oattach_list.
  - destruct (oresolve base) as [|[q b w] bl] eqn:Eb; [reflexivity|].
    cbn [ibase_ok] in Hbi. destruct w; try discriminate Hbi.
    destruct b; reflexivity.
  - destruct a' as [|kv a'']; destruct v;
      try reflexivity; try (apply isnoc_app, Hh).
    (* the one case left: a plain `Str` head, which the spec splits *)
    destruct (last_ws_split s) as [pre w].
    destruct (nonempty_str w); [|reflexivity].
    destruct a as [|ka a2]; [reflexivity|].
    destruct (split_text_pos p word) as [pp wp].
    destruct (nonempty_str pre);
      [rewrite (isnoc_app (Node pp [] (Str pre)) out (oresolve base))
         by exact Hh|];
      apply isnoc_app, Hh.
Qed.

Lemma oresolve_go_app :
  forall l base,
    base_ok base = true ->
    oresolve_go (l ++ base)%list
    = ((fst (oresolve_go l) ++ oresolve base)%list, snd (oresolve_go l)).
Proof.
  intros l base Hb.
  pose proof (oresolve_base_head base Hb) as Hbi.
  pose proof (ibase_ok_starts_str _ Hbi) as Hh.
  induction l as [|i l IH]; cbn [app oresolve_go].
  - unfold oresolve. rewrite <- (oresolve_go_base base Hb).
    destruct (oresolve_go base); reflexivity.
  - rewrite IH. destruct (oresolve_go l) as [out m]; cbn [fst snd].
    destruct i as [n|a spec word].
    + destruct m; [rewrite isnoc_app by exact Hh|]; reflexivity.
    + rewrite (oattach_list_app a spec word out base Hb). f_equal.
      destruct (oattach_list a spec word out) as [|x xs] eqn:E;
        [exact Hh|reflexivity].
Qed.

Lemma oresolve_app :
  forall l base,
    base_ok base = true ->
    oresolve (l ++ base)%list = (oresolve l ++ oresolve base)%list.
Proof.
  intros l base Hb. unfold oresolve. rewrite (oresolve_go_app l base Hb).
  reflexivity.
Qed.

Lemma ofinish_out_app :
  forall base o,
    base_ok base = true ->
    ofinish (oout_app base o) = (ofinish o ++ oresolve base)%list.
Proof.
  intros base o Hb. unfold ofinish, oitems_of, oout_app;
    cbn [os_out os_stk].
  rewrite oflatten_app by exact Hb. apply oresolve_app, Hb.
Qed.

Lemma ifinish_ostate_flat_app :
  forall base st,
    base_ok base = true ->
    ifinish_ostate_flat (iout_app base st)
    = oout_app base (ifinish_ostate_flat st).
Proof.
  intros base [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|cltxt clob|kids img open sp ssrc sob|ap asrc atxt aprev ash aob|kids img open label ob|nesc nimg nlab open nob|kids img open esc depth dst sh ob|asrc atxt aob|rspec rtxt rob] Hb;
    cbn [iout_app ifinish_ostate_flat].
  1,3: unfold iesc_hard; rewrite flush_text_app, oemit_app; reflexivity.
  1: rewrite flush_text_app; reflexivity.
  1,2: reflexivity.
  1,2: rewrite oemit_app; reflexivity.
  all: try reflexivity.
  - rewrite (bspan_lit_app kids img ssrc sob base Hb).
    destruct (bspan_lit kids img ssrc sob) as [t o']; cbn [fst snd].
    rewrite flush_text_app. reflexivity.
  - rewrite battr_lit_app.
    destruct (battr_lit asrc atxt aob) as [t o']; cbn [fst snd].
    rewrite flush_text_app. reflexivity.
  - rewrite (bref_lit_app kids img label ob base Hb).
    destruct (bref_lit kids img label ob) as [t o']; cbn [fst snd].
    rewrite flush_text_app. reflexivity.
  - rewrite (bnote_lit_app nesc nimg nlab nob base Hb).
    destruct (bnote_lit nesc nimg nlab nob) as [t o']; cbn [fst snd].
    rewrite flush_text_app. reflexivity.
  - rewrite flush_text_app. reflexivity.
  - rewrite oemit_app, flush_text_app. reflexivity.
Qed.

Lemma ifinish_ostate_flat_state_app :
  forall base st,
    base_ok base = true -> is_compound st = false ->
    ifinish_ostate (iout_app base st) = oout_app base (ifinish_ostate st).
Proof.
  intros base st Hb Hd.
  assert (Hd' : is_compound (iout_app base st) = false)
    by (destruct st; try reflexivity; discriminate Hd).
  rewrite (ifinish_ostate_flat_state _ Hd'),
          (ifinish_ostate_flat_state _ Hd).
  rewrite iresolve_app by exact Hb. apply ifinish_ostate_flat_app, Hb.
Qed.

Lemma ifinish_ostate_out_app :
  forall base st,
    base_ok base = true ->
    ifinish_ostate (iout_app base st) = oout_app base (ifinish_ostate st).
Proof.
  intros base st Hb.
  induction st;
    try (apply ifinish_ostate_flat_state_app; [exact Hb|reflexivity]).
  all: cbn [ifinish_ostate iout_app]; exact IHst.
Qed.

Lemma ifinish_rev_out_app :
  forall base st,
    base_ok base = true ->
    ifinish_rev (iout_app base st)
    = (ifinish_rev st ++ oresolve base)%list.
Proof.
  intros base st Hb. unfold ifinish_rev.
  rewrite ifinish_ostate_out_app by exact Hb.
  apply ofinish_out_app, Hb.
Qed.

Lemma ifinish_out_app :
  forall base st,
    base_ok base = true ->
    ifinish (iout_app base st)
    = (List.rev (oresolve base) ++ ifinish st)%list.
Proof.
  intros base st Hb. unfold ifinish.
  rewrite ifinish_rev_out_app by exact Hb.
  rewrite List.rev_app_distr. reflexivity.
Qed.

(* Parse one line's inline content.  Every construct of
   `.project/260811.inline-parser.md` lands here. *)
Definition parse_inline_line (s : string) : inlines := ifinish (iscan_str s istart).

Definition text_sep_ok (txt : string) (cis : list cinline) : bool :=
  match txt, cis with
  | String _ _, CIStr _ :: _ => false
  | _, _ => true
  end.

Lemma ifinish_text :
  forall txt prev out,
    ifinish (IText false txt prev (OState out [] None))
    = List.rev (oresolve (os_out (flush_text txt (OState out [] None)))).
Proof.
  intros txt prev out.
  unfold ifinish, ifinish_rev, ofinish, oitems_of.
  cbn [ifinish_ostate ifinish_ostate_flat iresolve].
  unfold flush_text, flush_text_at, oemit; cbn [os_stk os_out oflatten oapp].
  destruct (nonempty_str txt); reflexivity.
Qed.

(* Canonical text never opens a verbatim: `needs_escape` claims the
   backtick, so `escape_str` emits none bare.  The scanner therefore
   stays in `IText` throughout, and this is the whole of what the
   roundtrip needs from it today. *)
Lemma ilead_plain :
  forall c txt prev o,
    needs_escape c = false ->
    ilead c txt prev o = IText false (txt ++ one c)%string (Some c) o.
Proof.
  intros c txt prev o Hc. unfold needs_escape in Hc.
  apply orb_false_iff in Hc as [Hc Hcolon].
  apply orb_false_iff in Hc as [Hc Hhyp].
  apply orb_false_iff in Hc as [Hc Hhat].
  apply orb_false_iff in Hc as [Hres Hdl].
  destruct (dreserved_false c Hres)
    as [Hbs [Htk [Hlb [Hrb [Hlk [Hrk [Hbg [Hdol [Hpd Hlt]]]]]]]]].
  unfold ilead.
  rewrite Hbs, Htk, Hdol, Hpd, Hhyp, Hlb, Hbg, Hlt, Hlk, Hrk, Hhat.
  cbn [andb].
  destruct (dstyle_of c) eqn:Hd; [|reflexivity].
  unfold is_delim in Hdl. rewrite Hd in Hdl. discriminate.
Qed.

(* Canonical text never leaves `IText`: `needs_escape` claims every
   character the scanner dispatches on -- the backslash, the backtick,
   the six delimiters and the two braces -- so `escape_str` emits none of
   them bare.  This is the whole of what the roundtrip needs from the
   scanner, and it is why adding a table row costs an escape and not a
   proof. *)
Lemma iscan_escape :
  forall s txt prev o,
    iscan_str (escape_str s) (IText false txt prev o)
    = IText false (txt ++ s)%string (str_last s prev) o.
Proof.
  induction s as [|c rest IH]; intros txt prev o.
  - cbn [escape_str iscan_str]. rewrite append_empty_r. reflexivity.
  - cbn [escape_str]. destruct (needs_escape c) eqn:Hc.
    + cbn [iscan_str istep istep_at]. unfold ilead.
      change (is_bslash "\"%char) with true. cbn [iscan_str istep istep_at].
      rewrite (is_punct_not_ws c (needs_escape_punct c Hc)),
              (needs_escape_punct c Hc).
      rewrite IH, append_assoc. reflexivity.
    + cbn [iscan_str istep istep_at]. rewrite (ilead_plain c txt prev o Hc).
      rewrite IH, append_assoc. reflexivity.
Qed.

Lemma iscan_escape_after_verb :
  forall s n body vk o,
    nonempty_str s = true ->
    iscan_str (escape_str s) (IVerb n n body vk o)
    = IText false s (str_last s (Some tick))
        (oemit (mk (vnode vk (trim_verb body))) o).
Proof.
  intros [|c rest] n body vk o Hne; [discriminate|].
  cbn [escape_str]. destruct (needs_escape c) eqn:Hc.
  - cbn [iscan_str istep istep_at].
    change (is_tick "\"%char) with false. rewrite nat_eqb_refl.
    change (Ascii.eqb "\"%char lbrace) with false. cbn [andb].
    unfold ilead at 1. change (is_bslash "\"%char) with true.
  cbn [iscan_str istep istep_at].
    rewrite (is_punct_not_ws c (needs_escape_punct c Hc)),
            (needs_escape_punct c Hc), iscan_escape.
    cbn [append one]. reflexivity.
  - cbn [iscan_str istep istep_at].
    replace (is_tick c) with false
      by (destruct (is_tick c) eqn:Ht;
          [rewrite (needs_escape_tick c Ht) in Hc; discriminate|reflexivity]).
    (* the brace is reserved, so text that needs no escape is not one *)
    replace (Ascii.eqb c lbrace) with false
      by (destruct (Ascii.eqb c lbrace) eqn:Hb;
          [apply Ascii.eqb_eq in Hb; subst c;
           rewrite needs_escape_lbrace in Hc; discriminate|reflexivity]).
    cbn [andb].
    rewrite nat_eqb_refl, (ilead_plain c EmptyString (Some tick) _ Hc).
    rewrite iscan_escape. cbn [one append]. reflexivity.
Qed.

Lemma cis_ok_tail :
  forall c rest, cis_ok (c :: rest) = true -> cis_ok rest = true.
Proof.
  intros c rest H. unfold cis_ok in *. apply andb_true_iff in H as [Ha Hs].
  apply andb_true_iff. split.
  - cbn [forallb] in Ha. apply andb_true_iff in Ha as [_ Ha]. exact Ha.
  - destruct rest as [|r rest']; [reflexivity|].
    cbn [ci_sep_ok] in Hs. apply andb_true_iff in Hs as [_ Hs]. exact Hs.
Qed.

Lemma cis_ok_head :
  forall c rest, cis_ok (c :: rest) = true -> ci_ok c = true.
Proof.
  intros c rest H. unfold cis_ok in H. apply andb_true_iff in H as [H _].
  cbn [forallb] in H. apply andb_true_iff in H as [H _]. exact H.
Qed.

Lemma ci_str_tail_sep :
  forall s rest,
    cis_ok (CIStr s :: rest) = true -> nonempty_str s = true ->
    text_sep_ok s rest = true.
Proof.
  intros s [|r rest] H Hs; [unfold text_sep_ok; destruct s; reflexivity|].
  destruct r as [t|v|k kids|img kids dst|rimg rkids rlabel|label|a|rf rv];
    [|unfold text_sep_ok; destruct s; reflexivity ..].
  unfold cis_ok in H. cbn [ci_sep_ok ci_pair_ok] in H.
  repeat rewrite andb_false_r in H. discriminate.
Qed.

Lemma ci_verb_nonempty :
  forall v rest, cis_ok (CIVerb v :: rest) = true -> nonempty_str v = true.
Proof.
  intros v rest H. pose proof (cis_ok_head (CIVerb v) rest H) as Hv.
  cbn [ci_ok] in Hv. apply andb_true_iff in Hv as [Hv _]. exact Hv.
Qed.

Lemma ci_verb_content_ok :
  forall v rest, cis_ok (CIVerb v :: rest) = true -> verb_content_ok v = true.
Proof.
  intros v rest H. pose proof (cis_ok_head (CIVerb v) rest H) as Hv.
  cbn [ci_ok] in Hv. apply andb_true_iff in Hv as [_ Hv]. exact Hv.
Qed.

Lemma verb_content_safe :
  forall v, verb_content_ok v = true -> verb_safe (verb_ticks v) (pad_verb v) = true.
Proof.
  intros v H. unfold verb_content_ok in H.
  repeat rewrite andb_true_iff in H. destruct H as [[[_ _] _] H]. exact H.
Qed.

(* `ilead` dispatches the reserved characters first, so a row is reached
   at all only because its character is free of them -- and it finds
   itself again because the table is unambiguous.  Both come from
   `config_ok`; neither is a fact about djot. *)
(* The hypothesis the hyphen adds.  `ilead` claims that character before
   it consults the table, so a row spelled with it is reached from `{` or
   from `}` instead -- see `iscan_marked_close_step`, which is where this
   hypothesis stops travelling. *)
Lemma ilead_dchar :
  forall k txt prev o,
    denabled_of k = true ->
    Ascii.eqb (dchar k) hyphen = false ->
    bunpush o = None ->
    ilead (dchar k) txt prev o
    = IDelim k 0 txt prev false o.
Proof.
  intros k txt prev o Hen Hhy Hup.
  destruct (dreserved_false (dchar k) (dchar_free k))
    as [Hb [Ht [Hlb [Hrb [Hlk [Hrk [Hbg [Hdol [Hpd Hlt]]]]]]]]].
  unfold ilead.
  rewrite Hb, Ht, Hdol, Hpd, Hhy, Hlb, Hlt, Hlk, Hrk, Hbg, Hup.
  rewrite (dstyle_of_dchar k Hen). destruct (_ && _)%bool; reflexivity.
Qed.

(* Which is what condition 4 promises, with no hypothesis left over: a
   row that says it is bare is reached from the source in its bare
   spelling.  `ilead_dchar` keeps the hypothesis because
   `iscan_marked_close_step` calls it for a braced row too. *)
Lemma ilead_dchar_bare :
  forall k txt prev o,
    denabled_of k = true ->
    dsyntax_bare (dsyntax_of k) = true ->
    bunpush o = None ->
    ilead (dchar k) txt prev o = IDelim k 0 txt prev false o.
Proof.
  intros k txt prev o Hen Hb Hup.
  exact (ilead_dchar k txt prev o Hen (dchar_bare_free k Hb) Hup).
Qed.

(* Spelling a token, one character at a time: each of the row's
   characters after the first advances the count, and the token is still
   incomplete throughout because the arithmetic says so. *)
Lemma iscan_chars_delim :
  forall n k extra txt bef o,
    S extra + n = dwidth k ->
    iscan_str (chars (dchar k) n) (IDelim k extra txt bef false o)
    = IDelim k (extra + n) txt bef false o.
Proof.
  induction n as [|n IH]; intros k extra txt bef o Hn.
  - cbn [chars iscan_str]. replace (extra + 0) with extra by lia. reflexivity.
  - cbn [chars iscan_str istep istep_at].
    replace (Nat.ltb (S extra) (dwidth k)) with true
      by (symmetry; apply Nat.ltb_lt; lia).
    rewrite Ascii.eqb_refl.
    rewrite (IH k (S extra) txt bef o) by lia.
    f_equal. lia.
Qed.

(* A row's whole token, scanned from text: it leaves the token complete
   and its role undecided, which is the state the next byte resolves.
   This is what `ilead` did in one step when a delimiter was one
   character. *)
Lemma iscan_dtoken :
  forall k txt prev o,
    denabled_of k = true ->
    Ascii.eqb (dchar k) hyphen = false ->
    bunpush o = None ->
    iscan_str (dtoken k) (IText false txt prev o)
    = IDelim k (pred (dwidth k)) txt prev false o.
Proof.
  intros k txt prev o Hen Hhy Hup. unfold dtoken.
  destruct (dwidth k) as [|w] eqn:Ew; [destruct (dwidth_nonzero k Ew)|].
  cbn [chars iscan_str istep istep_at]. rewrite (ilead_dchar k _ _ _ Hen Hhy Hup).
  rewrite (iscan_chars_delim w k 0 txt _ o) by lia.
  cbn [pred]. reflexivity.
Qed.

(* A run of hyphens, scanned from text: `ilead` claims the first and the
   state counts the rest.  This is `iscan_dtoken`'s counterpart for the
   one character the table does not get to dispatch. *)
Lemma iscan_dash_run :
  forall n m txt prev o,
    iscan_str (chars hyphen n) (IDash m txt prev o) = IDash (m + n) txt prev o.
Proof.
  induction n as [|n IH]; intros m txt prev o.
  - cbn [chars iscan_str]. rewrite Nat.add_0_r. reflexivity.
  - cbn [chars iscan_str istep istep_at]. unfold idash_step.
    rewrite Ascii.eqb_refl, (IH (S m) txt prev o). f_equal. lia.
Qed.

Lemma ilead_hyphen :
  forall txt prev o, ilead hyphen txt prev o = IDash 1 txt prev o.
Proof.
  intros txt prev o. unfold ilead.
  change (is_bslash hyphen) with false.
  change (is_tick hyphen) with false.
  change (Ascii.eqb hyphen dollar) with false.
  change (Ascii.eqb hyphen period) with false.
  rewrite Ascii.eqb_refl. reflexivity.
Qed.

Lemma iscan_chars_dash :
  forall n txt prev o,
    iscan_str (chars hyphen (S n)) (IText false txt prev o)
    = IDash (S n) txt prev o.
Proof.
  intros n txt prev o. cbn [chars iscan_str istep istep_at].
  rewrite ilead_hyphen, (iscan_dash_run n 1 txt prev o).
  reflexivity.
Qed.

(* The token then `}`: a marked span closes.  When a delimiter was one
   character this was a single `istep`; the content is the same, and the
   only hypothesis is that a row has a token at all. *)
Lemma iscan_marked_close_step :
  forall k txt prev o o',
    denabled_of k = true ->
    bunpush o = None ->
    sclose k true (flush_text txt o) = Some o' ->
    iscan_str (dtoken k ++ one rbrace) (IText false txt prev o)
    = IText false EmptyString (Some rbrace) o'.
Proof.
  intros k txt prev o o' Hen Hup H.
  pose proof (dwidth_nonzero k) as Hw.
  destruct (Ascii.eqb (dchar k) hyphen) eqn:Hhy.
  { (* the hyphen row: the token was scanned as a run rather than as a
       delimiter, and the `}` gives the whole run back.  Both routes end
       in the same `idelim_resolve`, which is why the hypothesis
       `iscan_dtoken` needed does not travel past this lemma. *)
    apply Ascii.eqb_eq in Hhy.
    destruct (dwidth k) as [|w] eqn:Ew; [lia|].
    unfold dtoken. rewrite Ew, Hhy.
    rewrite iscan_str_app, (iscan_chars_dash w txt prev o).
    unfold one. cbn [iscan_str istep istep_at]. unfold idash_step.
    change (Ascii.eqb rbrace hyphen) with false.
    rewrite Ascii.eqb_refl, <- Hhy, (dstyle_of_dchar k Hen), Ew.
    rewrite Nat.leb_refl, Nat.sub_diag.
    assert (Ezero : typography_dashes 0 = EmptyString).
    { unfold typography_dashes. destruct smart_typography; reflexivity. }
    rewrite Ezero, (append_empty_r txt).
    unfold idelim_resolve. sem_flush.
    rewrite Bool.orb_true_r, H. reflexivity. }
  rewrite iscan_str_app, (iscan_dtoken k txt prev o Hen Hhy Hup).
  unfold one. cbn [iscan_str istep istep_at].
  replace (Nat.ltb (S (pred (dwidth k))) (dwidth k)) with false
    by (symmetry; apply Nat.ltb_ge; lia).
  rewrite Ascii.eqb_refl. unfold idelim_resolve. sem_flush.
  rewrite Bool.orb_true_r, H. reflexivity.
Qed.

(* Where the token lemmas get their hypothesis: a marked close runs with
   the delimiter's own frame on top, which is not a bracket, and nothing
   the close does before the token can turn it into one. *)
Lemma bunpush_oemit_all_opush :
  forall ns k m cm open o,
    bunpush (oemit_all ns (opush_at k m cm open o)) = None.
Proof.
  intros ns k m cm open [out stk word]. unfold opush_at; cbn [os_out os_stk].
  rewrite oemit_all_frame. reflexivity.
Qed.

Lemma bunpush_flush :
  forall txt o, bunpush o = None -> bunpush (flush_text txt o) = None.
Proof.
  intros txt [out [|[[k|im|im] m open [|n l]] stk] word] H;
    unfold flush_text, flush_text_at;
    destruct (nonempty_str txt); solve [exact H | reflexivity | discriminate H].
Qed.

Lemma iscan_marked_flush :
  forall k cm tail txt prev before open base,
    denabled_of k = true ->
    (nonempty before || nonempty_str txt)%bool = true ->
    exists p,
      iscan_str (marked_close k tail)
        (IText false txt prev
           (oemit_all before (opush_at k true cm open base)))
      = iscan_str (marked_close k tail)
          (IText false EmptyString p
            (flush_text txt
               (oemit_all before (opush_at k true cm open base)))).
Proof.
  intros k cm tail txt prev before open base Hen Hne.
  assert (Hclose : exists o',
    sclose k true
      (flush_text txt (oemit_all before (opush_at k true cm open base)))
    = Some o').
  { destruct (nonempty_str txt) eqn:Htxt.
    - exists (oemit (mk (dnode k (before ++ [mk (Str txt)])%list)) base).
      unfold flush_text, flush_text_at. rewrite Htxt.
      change (sclose k true
                (oemit_all [mk (Str txt)]
                  (oemit_all before (opush_at k true cm open base)))
              = Some
                  (oemit (mk (dnode k (before ++ [mk (Str txt)])%list))
                    base)).
      rewrite <- (oemit_all_app before [mk (Str txt)]
                    (opush_at k true cm open base)).
      cbn [oemit_all]. unfold sclose.
      apply (@oclose_oemit_all_marked semantic_pos k cm _ open (Spot 0 0) base).
      destruct before; reflexivity.
    - apply orb_true_iff in Hne as [Hbefore|Htxt']; [|discriminate].
      exists (oemit (mk (dnode k before)) base).
      unfold flush_text, flush_text_at. rewrite Htxt. unfold sclose.
      apply (@oclose_oemit_all_marked semantic_pos k cm before open
               (Spot 0 0) base), Hbefore. }
  destruct Hclose as [o' Hclose]. exists prev.
  unfold marked_close. rewrite <- append_assoc.
  rewrite !(iscan_str_app (dtoken k ++ one rbrace) tail).
  pose proof (bunpush_oemit_all_opush before k true cm open base) as Hup.
  rewrite (iscan_marked_close_step k txt prev
             (oemit_all before (opush_at k true cm open base)) o' Hen Hup Hclose).
  rewrite (iscan_marked_close_step k EmptyString prev
             (flush_text txt (oemit_all before (opush_at k true cm open base))) o' Hen
             (bunpush_flush txt _ Hup)
             ltac:(cbn [flush_text flush_text_at]; exact Hclose)).
  reflexivity.
Qed.

(* The rest of a marked open's token.  The counterpart of
   `iscan_chars_delim`, and it stops one byte earlier than the push does:
   a marked opener's role is settled but the side its decay takes is
   not. *)
Lemma iscan_chars_marked :
  forall n k extra txt o,
    S extra + n = dwidth k ->
    iscan_str (chars (dchar k) n) (idelim_marked k extra txt o)
    = idelim_marked k (extra + n) txt o.
Proof.
  induction n as [|n IH]; intros k extra txt o Hn.
  - cbn [chars iscan_str]. rewrite Nat.add_0_r. reflexivity.
  - unfold idelim_marked at 1.
    cbn [chars iscan_str istep istep_at].
    replace (Nat.ltb (S extra) (dwidth k)) with true
      by (symmetry; apply Nat.ltb_lt; lia).
    rewrite Ascii.eqb_refl.
    rewrite (IH k (S extra) txt o) by lia.
    f_equal. lia.
Qed.

Lemma iscan_marked_open :
  forall d txt prev o,
    denabled_of d = true ->
    iscan_str (marked_open d) (IText false txt prev o)
    = idelim_marked d (pred (dwidth d)) txt o.
Proof.
  intros d txt prev o Hen. unfold marked_open, dtoken.
  destruct (dwidth d) as [|w] eqn:Ew;
    [destruct (dwidth_nonzero d Ew)|].
  unfold one. cbn [chars append iscan_str istep istep_at].
  change (ilead lbrace txt prev o) with (IBrace txt prev o).
  cbn [istep istep_at]. unfold ibrace_step, ibrace_step_at.
  rewrite (dstyle_of_dchar d Hen).
  rewrite (iscan_chars_marked w d 0 txt o) by lia.
  cbn [pred]. reflexivity.
Qed.

(* And the byte that follows it, which is where the push happens: it
   chooses the side the scope's decay would take, and then is dispatched
   into the scope as any byte would be.  A caller whose scope closes never
   learns which side it was, so the bit is existential here -- the only
   thing the chain below needs is that the scope is open. *)
Lemma iscan_marked_open_app :
  forall d s txt prev o,
    denabled_of d = true -> nonempty_str s = true ->
    exists cm open,
      iscan_str (marked_open d ++ s) (IText false txt prev o)
      = iscan_str s
          (IText false EmptyString (Some (dchar d))
            (opush_at d true cm open (flush_text txt o))).
Proof.
  intros d [|c s] txt prev o Hen Hne; [discriminate|].
  exists (Ascii.eqb c rbrace). eexists.
  rewrite iscan_str_app, (iscan_marked_open d txt prev o Hen).
  destruct (dwidth d) as [|w] eqn:Ew; [destruct (dwidth_nonzero d Ew)|].
  unfold idelim_marked. cbn [pred iscan_str istep istep_at].
  rewrite Ew, Nat.ltb_irrefl. unfold oopen_marked. reflexivity.
Qed.

Lemma iscan_marked_close_emit :
  forall d cm tail ns open base p,
    denabled_of d = true ->
    nonempty ns = true ->
    iscan_str (marked_close d tail)
      (IText false EmptyString p
         (oemit_all ns (opush_at d true cm open base)))
    = iscan_str tail
        (IText false EmptyString (Some rbrace)
          (oemit (mk (dnode d ns)) base)).
Proof.
  intros d cm tail ns open base p Hen Hne. unfold marked_close.
  rewrite <- append_assoc, iscan_str_app.
  rewrite (iscan_marked_close_step d EmptyString p
             (oemit_all ns (opush_at d true cm open base))
             (oemit (mk (dnode d ns)) base)
             Hen
             (bunpush_oemit_all_opush ns d true cm open base)
             ltac:(cbn [flush_text flush_text_at];
                   apply (@oclose_oemit_all_marked semantic_pos d cm ns open
                            (Spot 0 0) base), Hne)).
  reflexivity.
Qed.

Lemma iscan_after_verb_nontick :
  forall s n body vk o,
    nonempty_str s = true -> starts_tick s = false ->
    after_verb_next s = true ->
    iscan_str s (IVerb n n body vk o)
    = iscan_str s
        (IText false EmptyString (Some tick)
          (oemit (mk (vnode vk (trim_verb body))) o)).
Proof.
  intros [|c s] n body vk o Hne Htick Hnext; [discriminate|].
  cbn [starts_tick] in Htick. cbn [iscan_str istep istep_at]. rewrite Htick.
  rewrite nat_eqb_refl.
  cbn [after_verb_next] in Hnext.
  destruct (Ascii.eqb c lbrace) eqn:Hb; [|reflexivity].
  (* the raw mode and the brace it stands in for agree from the next byte
     on: the mode's own failure path is `ibrace_step`, which is that
     byte's ordinary dispatch *)
  destruct vk; [|reflexivity].
  destruct s as [|d s]; [discriminate|].
  cbn [iscan_str istep istep_at].
  apply Ascii.eqb_eq in Hb; subst c.
  cbn [vkind_verb andb].
  unfold istep at 1; cbn [istep_at]; unfold iraw_step_at.
  rewrite Hnext, andb_false_r. unfold ilead; cbn. reflexivity.
Qed.

Lemma escape_str_starts_nontick :
  forall s, nonempty_str s = true -> starts_tick (escape_str s) = false.
Proof.
  intros [|c s] H; [discriminate|]. cbn [escape_str].
  destruct (needs_escape c) eqn:Hc; [reflexivity|].
  cbn [starts_tick]. destruct (is_tick c) eqn:Ht; [|reflexivity].
  rewrite (needs_escape_tick c Ht) in Hc. discriminate.
Qed.

(* `after_verb_next` asks about the brace and nothing else, so anything
   that cannot start with one satisfies it outright.  That is every
   canonical constituent but a delimiter, whose brace is its opener. *)
Definition starts_brace (s : string) : bool :=
  match s with String c _ => Ascii.eqb c lbrace | EmptyString => false end.

Lemma after_verb_next_nonbrace :
  forall s, starts_brace s = false -> after_verb_next s = true.
Proof.
  intros [|c s] H; [reflexivity|].
  cbn [after_verb_next starts_brace] in H |- *. rewrite H. reflexivity.
Qed.

Lemma nonempty_str_app_l :
  forall a b, nonempty_str b = true -> nonempty_str (a ++ b)%string = true.
Proof. intros [|x a] b H; [exact H | reflexivity]. Qed.

Lemma nonempty_str_app_r :
  forall a b, nonempty_str a = true -> nonempty_str (a ++ b)%string = true.
Proof. intros [|x a] b H; [discriminate | reflexivity]. Qed.

Lemma starts_brace_app_l :
  forall a b, nonempty_str a = true -> starts_brace (a ++ b) = starts_brace a.
Proof. intros [|c a] b H; [discriminate|reflexivity]. Qed.

Lemma escape_str_starts_nonbrace :
  forall s, starts_brace (escape_str s) = false.
Proof.
  intros [|c s]; [reflexivity|]. cbn [escape_str].
  destruct (needs_escape c) eqn:Hc; [reflexivity|].
  cbn [starts_brace]. destruct (Ascii.eqb c lbrace) eqn:Hb; [|reflexivity].
  apply Ascii.eqb_eq in Hb; subst c.
  rewrite needs_escape_lbrace in Hc. discriminate.
Qed.

Lemma escape_str_nonempty :
  forall s, nonempty_str s = true -> nonempty_str (escape_str s) = true.
Proof.
  intros [|c s] H; [discriminate|]. cbn [escape_str].
  destruct (needs_escape c); reflexivity.
Qed.

(* The two things a closer has to be for the scope machinery: nonempty,
   which is the row having a token, and not starting with a backtick,
   which is its character being free of the ones the scanner claims. *)
Lemma marked_close_nonempty :
  forall k tail, nonempty_str (marked_close k tail) = true.
Proof.
  intros k tail. pose proof (dtoken_nonempty k) as H.
  unfold marked_close. destruct (dtoken k); [discriminate|reflexivity].
Qed.

Lemma marked_close_starts_nontick :
  forall k tail, starts_tick (marked_close k tail) = false.
Proof.
  intros k tail.
  destruct (dreserved_false (dchar k) (dchar_free k)) as [_ [Ht _]].
  unfold marked_close, dtoken.
  destruct (dwidth k) as [|w] eqn:E; [destruct (dwidth_nonzero k E)|].
  cbn [chars append starts_tick]. exact Ht.
Qed.

(* ...and it is not a brace either, since a row's character is not
   reserved -- which is what a verbatim before the closer needs. *)
Lemma marked_close_after_verb :
  forall k tail, after_verb_next (marked_close k tail) = true.
Proof.
  intros k tail. apply after_verb_next_nonbrace.
  unfold marked_close, dtoken.
  destruct (dwidth k) as [|w] eqn:Ew;
    [pose proof (dtoken_nonempty k) as Hn; unfold dtoken in Hn;
     rewrite Ew in Hn; discriminate|].
  cbn [chars append starts_brace].
  destruct (dreserved_false (dchar k) (dchar_free k))
    as [_ [_ [Hlb _]]].
  exact Hlb.
Qed.

(* What a verbatim needs of whatever follows it: a nonempty continuation
   that does not start with a backtick, or its closing run would grow.
   Stated over an arbitrary closer because two constructs now supply one
   -- a marked delimiter and a bracket -- and the proof never looks at
   which. *)
(*
Scanning a link
---------------

The bracket analogues of `iscan_marked_open` and
`iscan_marked_close_emit`.  The close is longer than a delimiter's
because it spans three dispatches -- the `]`, the `(` and the balanced
`)` -- with the destination scanned as escaped text in between. *)

(* One lemma for both openers: the `!` is a separate dispatch, but it
   only decides which frame is pushed. *)
Lemma iscan_bracket_open :
  forall image txt prev o,
    iscan_str (bracket_open image) (IText false txt prev o)
    = IText false EmptyString (Some lbrack) (bpush image (flush_text txt o)).
Proof. intros [] txt prev o; reflexivity. Qed.

Lemma bclose_flush_bpush :
  forall txt image before base,
    bclose (flush_text txt (oemit_all before (bpush image base)))
    = Some (if nonempty_str txt
            then (before ++ [mk (Str txt)])%list else before, image,
            null_span, base).
Proof.
  intros txt image before base. unfold flush_text, flush_text_at.
  destruct (nonempty_str txt).
  - replace (oemit (mk (Str txt)) (oemit_all before (bpush image base)))
      with (oemit_all [mk (Str txt)] (oemit_all before (bpush image base)))
      by reflexivity.
    rewrite <- (oemit_all_app before [mk (Str txt)] (bpush image base)).
    apply bclose_oemit_all.
  - apply bclose_oemit_all.
Qed.

Lemma drop_nl_no_nl : forall s, no_nl s = true -> drop_nl s = s.
Proof.
  induction s as [|c s IH]; intros H; [reflexivity|].
  cbn [no_nl] in H. apply andb_true_iff in H as [Hc H].
  apply negb_true_iff in Hc. cbn [drop_nl].
  change nl_char with "010"%char. rewrite Hc, (IH H). reflexivity.
Qed.

(* The destination is escaped text, and reads back the way escaped text
   does: `needs_escape_dest` claims every byte the mode dispatches on,
   and its escapes decode because each such byte is punctuation. *)
Lemma iscan_dest_escape :
  forall s kids image open depth dst sh o,
    iscan_str (escape_dest s) (IDest kids image open false depth dst sh o)
    = IDest kids image open false depth (dst ++ s)%string
        (iscan_str (escape_dest s) sh) o.
Proof.
  induction s as [|c s IH]; intros kids image open depth dst sh o;
    cbn [escape_dest]; [rewrite append_empty_r; reflexivity|].
  assert (Hsplit : forall t, (dst ++ String c t)%string
                             = ((dst ++ one c) ++ t)%string).
  { intro t. rewrite (append_assoc dst (one c) t). reflexivity. }
  destruct (needs_escape_dest c) eqn:Hc.
  - pose proof (needs_escape_dest_punct c Hc) as Hp.
    cbn [iscan_str istep istep_at]. change (is_bslash "\"%char) with true.
    cbn [istep istep_at]. rewrite Hp, IH, Hsplit. reflexivity.
  - assert (Hbs : is_bslash c = false).
    { destruct (is_bslash c) eqn:E; [|reflexivity].
      unfold needs_escape_dest, needs_escape in Hc.
      apply Ascii.eqb_eq in E. subst c. discriminate. }
    assert (Hlp : Ascii.eqb c lparen = false).
    { destruct (Ascii.eqb c lparen) eqn:E; [|reflexivity].
      unfold needs_escape_dest in Hc. rewrite E in Hc.
      rewrite orb_true_r in Hc. discriminate. }
    assert (Hrp : Ascii.eqb c rparen = false).
    { destruct (Ascii.eqb c rparen) eqn:E; [|reflexivity].
      unfold needs_escape_dest in Hc. rewrite E in Hc.
      rewrite orb_true_r in Hc. discriminate. }
    cbn [iscan_str istep istep_at]. rewrite Hbs, Hlp, Hrp, IH, Hsplit. reflexivity.
Qed.

Lemma istep_rbrack_close :
  forall txt prev o, istep rbrack (IText false txt prev o) = IClosed txt o.
Proof.
  intros txt prev o. cbn [istep istep_at]. unfold ilead.
  change (is_bslash rbrack) with false.
  change (is_tick rbrack) with false.
  change (Ascii.eqb rbrack lbrace) with false.
  change (Ascii.eqb rbrack bang) with false.
  change (Ascii.eqb rbrack lbrack) with false.
  change (Ascii.eqb rbrack rbrack) with true.
  reflexivity.
Qed.

(* ...and the byte after it is what closes the bracket. *)
Lemma istep_lbrack_ref :
  forall txt o kids image open o',
    bclose (flush_text txt o) = Some (kids, image, open, o') ->
    istep lbrack (IClosed txt o) =
      IReference kids image open EmptyString o'.
Proof.
  intros txt o kids image open o' H. cbn [istep istep_at].
  change (Ascii.eqb lbrack lparen) with false.
  change (Ascii.eqb lbrack lbrack) with true. cbn [orb].
  sem_flush. rewrite H. reflexivity.
Qed.

Lemma istep_lparen_dest :
  forall txt o kids image open o',
    bclose (flush_text txt o) = Some (kids, image, open, o') ->
    istep lparen (IClosed txt o)
    = IDest kids image open false 0 EmptyString
        (idest_open kids image open o') o'.
Proof.
  intros txt o kids image open o' H. cbn [istep istep_at].
  change (Ascii.eqb lparen lparen) with true. cbn [orb].
  sem_flush. rewrite H. reflexivity.
Qed.

Lemma iscan_link_close :
  forall dst tail ns image base p,
    no_nl dst = true ->
    iscan_str (link_close dst tail)
      (IText false EmptyString p (oemit_all ns (bpush image base)))
    = iscan_str tail
        (IText false EmptyString (Some rparen)
          (oemit (mk (bnode image ns (Direct dst))) base)).
Proof.
  intros dst tail ns image base p Hnl. unfold link_close.
  cbn [iscan_str]. rewrite (istep_rbrack_close EmptyString p _).
  rewrite (istep_lparen_dest EmptyString _ ns image
             (null_span) base
             (bclose_flush_bpush EmptyString image ns base)).
  rewrite iscan_str_app, iscan_dest_escape.
  change ((EmptyString ++ dst)%string) with dst.
  cbn [iscan_str istep istep_at].
  change (is_bslash rparen) with false.
  change (Ascii.eqb rparen lparen) with false.
  change (Ascii.eqb rparen rparen) with true.
  rewrite (drop_nl_no_nl dst Hnl). reflexivity.
Qed.

(* The bracket's flush law, and it needs no precondition: a `]` closes an
   empty label as happily as a full one, which is what `empty_ok` below
   records and what makes `[](u)` representable. *)
Lemma iscan_bracket_flush :
  forall dst tail txt prev image before base,
    exists p,
      iscan_str (link_close dst tail)
        (IText false txt prev (oemit_all before (bpush image base)))
      = iscan_str (link_close dst tail)
          (IText false EmptyString p
            (flush_text txt (oemit_all before (bpush image base)))).
Proof.
  intros dst tail txt prev image before base. exists (Some lbrack).
  pose (ns := if nonempty_str txt
              then (before ++ [mk (Str txt)])%list else before).
  unfold link_close. cbn [iscan_str].
  rewrite (istep_rbrack_close txt prev _), (istep_rbrack_close EmptyString _ _).
  cbn [iscan_str].
  rewrite (istep_lparen_dest txt _ ns image
             (null_span) base
             (bclose_flush_bpush txt image before base)).
  rewrite (istep_lparen_dest EmptyString _ ns image
             (null_span) base);
    [reflexivity|].
  cbn [flush_text flush_text_at nonempty_str]. rewrite ?imk_semantic.
  apply (bclose_flush_bpush txt image before base).
Qed.

Lemma link_close_app :
  forall dst t, (link_close dst EmptyString ++ t)%string = link_close dst t.
Proof.
  intros dst t. unfold link_close. cbn [append].
  rewrite append_assoc. cbn [append]. reflexivity.
Qed.

(*
Scanning a reference link
-------------------------

The same three dispatches as a direct link's closer, with `[`, the label
and `]` in place of `(`, the destination and `)`.  The label is easier:
the mode escapes nothing and dispatches on nothing but `]`, so the whole
of it goes in one induction.
*)

Lemma iscan_ref_label :
  forall label kids image open acc o,
    no_char rbrack label = true ->
    iscan_str label (IReference kids image open acc o)
    = IReference kids image open (acc ++ label)%string o.
Proof.
  induction label as [|c label IH]; intros kids image open acc o H;
    [rewrite append_empty_r; reflexivity|].
  cbn [no_char] in H. apply andb_true_iff in H as [Hc H].
  apply negb_true_iff in Hc.
  cbn [iscan_str istep istep_at]. rewrite Hc, (IH _ _ _ _ _ H).
  rewrite append_assoc. reflexivity.
Qed.

Lemma iscan_ref_close :
  forall label tail ns image base p,
    nonempty_str label = true ->
    no_char rbrack label = true ->
    iscan_str (ref_close label tail)
      (IText false EmptyString p (oemit_all ns (bpush image base)))
    = iscan_str tail
        (IText false EmptyString (Some rbrack)
          (oemit (mk (bnode image ns (Reference (normalize_label label)))) base)).
Proof.
  intros label tail ns image base p Hne Hbr. unfold ref_close.
  cbn [iscan_str]. rewrite (istep_rbrack_close EmptyString p _).
  rewrite (istep_lbrack_ref EmptyString _ ns image
             (null_span) base
             (bclose_flush_bpush EmptyString image ns base)).
  rewrite iscan_str_app,
    (iscan_ref_label label ns image
      (null_span)
      EmptyString _ Hbr).
  change ((EmptyString ++ label)%string) with label.
  cbn [iscan_str istep istep_at]. change (Ascii.eqb rbrack rbrack) with true.
  destruct label as [|c label']; [discriminate Hne|reflexivity].
Qed.

(* The flush law, as for a direct link and by the same `]` dispatch. *)
Lemma iscan_ref_flush :
  forall label tail txt prev image before base,
    exists p,
      iscan_str (ref_close label tail)
        (IText false txt prev (oemit_all before (bpush image base)))
      = iscan_str (ref_close label tail)
          (IText false EmptyString p
            (flush_text txt (oemit_all before (bpush image base)))).
Proof.
  intros label tail txt prev image before base. exists (Some lbrack).
  pose (ns := if nonempty_str txt
              then (before ++ [mk (Str txt)])%list else before).
  unfold ref_close. cbn [iscan_str].
  rewrite (istep_rbrack_close txt prev _), (istep_rbrack_close EmptyString _ _).
  cbn [iscan_str].
  rewrite (istep_lbrack_ref txt _ ns image
             (null_span) base
             (bclose_flush_bpush txt image before base)).
  rewrite (istep_lbrack_ref EmptyString _ ns image
             (null_span) base);
    [reflexivity|].
  cbn [flush_text flush_text_at nonempty_str]. rewrite ?imk_semantic.
  apply (bclose_flush_bpush txt image before base).
Qed.

(* A canonical note label reaches its closing bracket without leaving an
   escape pending.  Backslashes are consumed in pairs with the following
   byte, and both bytes remain in the label. *)
Lemma iscan_note_label :
  forall label tail esc image acc open o,
    note_label_safe_from esc label = true ->
    iscan_str (label ++ one rbrack ++ tail)
      (INote esc image acc open o)
    = iscan_str tail
        (IText false EmptyString (Some rbrack)
          (oemit (mk (FootnoteReference
            (normalize_label
              (acc ++ (if esc then one bslash else EmptyString) ++ label))))
            (ospan_bang image o))).
Proof.
  induction label as [|c label IH]; intros tail esc image acc open o Hsafe.
  - cbn [note_label_safe_from] in Hsafe. destruct esc; [discriminate|].
    cbn [append iscan_str istep istep_at inote_step].
    change (is_bslash rbrack) with false.
    change (Ascii.eqb rbrack rbrack) with true.
    rewrite !append_empty_r. reflexivity.
  - cbn [note_label_safe_from] in Hsafe.
    cbn [append iscan_str istep istep_at inote_step].
    destruct esc.
    + cbn [inote_step].
      rewrite (IH tail false image (acc ++ one bslash ++ one c)%string open o
                 Hsafe).
      rewrite !append_assoc. reflexivity.
    + destruct (Ascii.eqb c rbrack) eqn:Hclose; [discriminate|].
      destruct (is_bslash c) eqn:Hslash.
      * unfold is_bslash in Hslash. apply Ascii.eqb_eq in Hslash. subst c.
        cbn [inote_step].
        rewrite is_bslash_bslash.
        rewrite (IH tail true image acc open o Hsafe).
        cbn [append]. reflexivity.
      * cbn [inote_step]. rewrite Hslash, Hclose.
        rewrite (IH tail false image (acc ++ one c)%string open o Hsafe).
        rewrite !append_assoc. reflexivity.
Qed.

Lemma iscan_note_text :
  forall label tail txt prev o,
    notes_enabled = true ->
    note_label_safe label = true ->
    iscan_str (note_text label ++ tail)
      (IText false txt prev o)
    = iscan_str tail
        (IText false EmptyString (Some rbrack)
          (oemit (mk (FootnoteReference (normalize_label label)))
            (flush_text txt o))).
Proof.
  intros label tail txt prev o Hnotes Hsafe.
  replace (note_text label ++ tail)%string with
    (bracket_open false ++ (one hat ++ (label ++ one rbrack ++ tail)))%string
    by (unfold note_text, bracket_open; cbn [append];
        rewrite append_assoc; reflexivity).
  rewrite iscan_str_app, iscan_bracket_open.
  rewrite iscan_str_app. cbn [one iscan_str istep istep_at].
  unfold ilead.
  change (is_bslash hat) with false.
  change (is_tick hat) with false.
  change (Ascii.eqb hat dollar) with false.
  change (Ascii.eqb hat period) with false.
  change (Ascii.eqb hat hyphen) with false.
  change (Ascii.eqb hat lbrace) with false.
  change (Ascii.eqb hat bang) with false.
  change (Ascii.eqb hat lt) with false.
  change (Ascii.eqb hat lbrack) with false.
  change (Ascii.eqb hat rbrack) with false.
  change (Ascii.eqb hat hat && note_pos EmptyString (Some lbrack))%bool
    with true.
  rewrite Hnotes. cbn [andb].
  rewrite bunpush_bpush.
  rewrite (iscan_note_label label tail false false EmptyString
             null_span (flush_text txt o) Hsafe).
  reflexivity.
Qed.

(* The region is accumulated and nothing in it is dispatched, which is
   the whole of why a successful autolink's content is literal. *)
Lemma iscan_auto_region :
  forall s acc txt o,
    auto_region s = true ->
    iscan_str s (IAuto acc txt o) = IAuto (acc ++ s)%string txt o.
Proof.
  induction s as [|c s IH]; intros acc txt o Hr.
  - rewrite append_empty_r. reflexivity.
  - unfold auto_region in Hr.
    apply andb_true_iff in Hr as [Hr Hgt].
    apply andb_true_iff in Hr as [Hws Hlt].
    cbn [no_ws no_char] in Hws, Hlt, Hgt.
    apply andb_true_iff in Hws as [Hwsc Hws].
    apply andb_true_iff in Hlt as [Hltc Hlt].
    apply andb_true_iff in Hgt as [Hgtc Hgt].
    apply negb_true_iff in Hwsc, Hltc, Hgtc.
    cbn [iscan_str istep istep_at]. unfold iauto_step.
    rewrite Hgtc. cbn [andb orb].
    unfold is_ws_nl in Hwsc. apply orb_false_iff in Hwsc as [Hwsc _].
    rewrite Hwsc, Hltc. cbn [orb].
    rewrite (IH (acc ++ one c)%string txt o)
      by (unfold auto_region; rewrite Hws, Hlt, Hgt; reflexivity).
    rewrite append_assoc. reflexivity.
Qed.

(* A raw spec accumulates the same way an autolink's region does, and
   under the same kind of condition: the format's own exclusions. *)
Lemma iscan_raw_format :
  forall fmt acc txt o,
    (no_ws fmt && no_char lbrace fmt && no_char rbrace fmt
     && no_char tick fmt)%bool = true ->
    nonempty_str acc = true ->
    iscan_str fmt (IRaw acc txt o) = IRaw (acc ++ fmt)%string txt o.
Proof.
  induction fmt as [|c fmt IH]; intros acc txt o Hf Hacc.
  - rewrite append_empty_r. reflexivity.
  - apply andb_true_iff in Hf as [Hf Htk].
    apply andb_true_iff in Hf as [Hf Hrb].
    apply andb_true_iff in Hf as [Hws Hlb].
    cbn [no_ws no_char] in Hws, Hlb, Hrb, Htk.
    apply andb_true_iff in Hws as [Hwsc Hws].
    apply andb_true_iff in Hlb as [Hlbc Hlb].
    apply andb_true_iff in Hrb as [Hrbc Hrb].
    apply andb_true_iff in Htk as [Htkc Htk].
    apply negb_true_iff in Hwsc. apply negb_true_iff in Hlbc.
    apply negb_true_iff in Hrbc. apply negb_true_iff in Htkc.
    cbn [iscan_str istep istep_at]. unfold iraw_step_at.
    rewrite Hrbc. cbn [andb].
    destruct acc as [|x acc']; [discriminate|].
    unfold raw_stop. rewrite Hlbc.
    replace (is_ws c) with false
      by (unfold is_ws_nl in Hwsc; apply orb_false_iff in Hwsc as [H1 _];
          rewrite H1; reflexivity).
    unfold is_tick. rewrite Htkc. cbn [orb].
    rewrite (IH (String x acc' ++ one c)%string txt o)
      by (first [rewrite Hws, Hlb, Hrb, Htk; reflexivity | reflexivity]).
    rewrite append_assoc. reflexivity.
Qed.

(* ...and the `>` that resolves it, which is the only byte the mode
   treats as anything but region. *)
Lemma iscan_auto_text :
  forall s tail txt prev o,
    auto_body_ok s = true -> auto_kind_ok s = true ->
    iscan_str (auto_text s ++ tail) (IText false txt prev o)
    = iscan_str tail
        (IText false EmptyString (Some gt)
           (oemit (mk (auto_node s)) (flush_text txt o))).
Proof.
  intros s tail txt prev o Hbody Hkind.
  pose proof Hbody as Hregion. unfold auto_body_ok in Hregion.
  apply andb_true_iff in Hregion as [_ Hregion].
  unfold auto_text. cbn [append iscan_str istep istep_at].
  unfold ilead.
  change (is_bslash lt) with false.
  change (is_tick lt) with false.
  change (Ascii.eqb lt dollar) with false.
  change (Ascii.eqb lt period) with false.
  change (Ascii.eqb lt hyphen) with false.
  change (Ascii.eqb lt lbrace) with false.
  change (Ascii.eqb lt bang) with false.
  change (Ascii.eqb lt lt) with true.
  rewrite append_assoc, iscan_str_app.
  rewrite (iscan_auto_region s EmptyString txt o Hregion).
  replace ((EmptyString ++ s)%string) with s by reflexivity.
  cbn [one append iscan_str istep istep_at]. unfold iauto_step.
  change (Ascii.eqb gt gt) with true.
  rewrite Hbody, Hkind. reflexivity.
Qed.

(* The raw span, end to end: the verbatim's own source reaches the
   closing run, the `{` enters the mode, the format accumulates and the
   `}` decides the node.  `verb_content_ok` is what the verbatim half
   needs and `raw_fmt_ok` the spec half; the `=` is where they meet. *)
Lemma iscan_raw_text :
  forall fmt v tail txt prev o,
    raw_inline_enabled = true ->
    nonempty_str v = true -> verb_content_ok v = true ->
    raw_fmt_ok fmt = true ->
    iscan_str (raw_text fmt v ++ tail) (IText false txt prev o)
    = iscan_str tail
        (IText false EmptyString (Some rbrace)
           (oemit (mk (RawInline fmt v)) (flush_text txt o))).
Proof.
  intros fmt v tail txt prev o Hraw Hne Hvok Hfmt.
  unfold raw_fmt_ok in Hfmt.
  apply andb_true_iff in Hfmt as [Hfmt Htk].
  apply andb_true_iff in Hfmt as [Hfmt Hrb].
  apply andb_true_iff in Hfmt as [Hfmt Hlb].
  apply andb_true_iff in Hfmt as [Hfne Hws].
  unfold raw_text. rewrite append_assoc, iscan_str_app.
  rewrite iscan_verb_text_nonempty by auto using verb_content_safe.
  (* the `{` after the closing run enters the mode... *)
  cbn [append iscan_str istep istep_at].
  rewrite nat_eqb_refl. cbn [vkind_verb andb].
  change (Ascii.eqb lbrace lbrace) with true. cbn [andb].
  change (is_tick lbrace) with false. cbn [andb].
  rewrite trim_verb_pad by exact Hvok.
  (* ...the `=` makes it a candidate, the format accumulates... *)
  unfold istep_at at 1. unfold iraw_step_at.
  change (Ascii.eqb "="%char rbrace) with false. cbn [andb].
  change (negb (Ascii.eqb "="%char eqchar)) with false.
  rewrite append_assoc, iscan_str_app.
  change ((EmptyString ++ one "="%char)%string) with (one eqchar).
  rewrite (iscan_raw_format fmt (one eqchar) v (flush_text txt o))
    by (first [rewrite Hws, Hlb, Hrb, Htk; reflexivity | reflexivity]).
  (* ...and the `}` decides the node. *)
  cbn [one iscan_str istep istep_at append]. unfold iraw_step_at.
  change (Ascii.eqb rbrace rbrace) with true.
  unfold raw_spec_ok. cbn [append].
  rewrite Ascii.eqb_refl, Hfne. cbn [andb].
  rewrite Hraw. unfold raw_format. reflexivity.
Qed.

Lemma ref_close_app :
  forall label t, (ref_close label EmptyString ++ t)%string = ref_close label t.
Proof.
  intros label t. unfold ref_close. cbn [append].
  rewrite append_assoc. cbn [append]. reflexivity.
Qed.

Lemma ref_close_nonempty :
  forall label tail, nonempty_str (ref_close label tail) = true.
Proof. intros label tail. reflexivity. Qed.

Lemma ref_close_starts_nontick :
  forall label tail, starts_tick (ref_close label tail) = false.
Proof. intros label tail. reflexivity. Qed.

Lemma link_close_nonempty :
  forall dst tail, nonempty_str (link_close dst tail) = true.
Proof. intros dst tail. reflexivity. Qed.

Lemma link_close_starts_nontick :
  forall dst tail, starts_tick (link_close dst tail) = false.
Proof. intros dst tail. reflexivity. Qed.

Lemma after_verb_source_nontick :
  forall v rest cl,
    cis_ok (CIVerb v :: rest) = true ->
    nonempty_str cl = true -> starts_tick cl = false ->
    after_verb_next cl = true ->
    nonempty_str (ci_text rest ++ cl) = true /\
    starts_tick (ci_text rest ++ cl) = false /\
    after_verb_next (ci_text rest ++ cl) = true.
Proof.
  intros v [|c rest] cl Hok Hcl Hct Hnx.
  - cbn [ci_text append]. split; [assumption|split; assumption].
  - destruct c as [s|w|d kids|img kids dst|rimg rkids rlabel|label|a|rf rv].
    + pose proof (cis_ok_head (CIStr s) rest (cis_ok_tail _ _ Hok)) as Hs.
      cbn [ci_ok] in Hs. apply andb_true_iff in Hs as [Hs _].
      cbn [ci_text ci_src]. split; [|split].
      * destruct (escape_str s) eqn:E;
          [pose proof (escape_str_nonempty s Hs); rewrite E in H; discriminate
          |reflexivity].
      * rewrite starts_tick_app_l.
        -- rewrite starts_tick_app_l.
           ++ apply escape_str_starts_nontick, Hs.
           ++ apply escape_str_nonempty, Hs.
        -- destruct (escape_str s) eqn:E; [|reflexivity].
           pose proof (escape_str_nonempty s Hs). rewrite E in H.
           discriminate.
      * apply after_verb_next_nonbrace.
        rewrite starts_brace_app_l.
        -- rewrite starts_brace_app_l;
             [apply escape_str_starts_nonbrace | apply escape_str_nonempty, Hs].
        -- apply nonempty_str_app_r, escape_str_nonempty, Hs.
    + unfold cis_ok in Hok. cbn [ci_sep_ok ci_pair_ok] in Hok.
      repeat rewrite andb_false_r in Hok. discriminate.
    + (* the one constituent whose source *is* a brace: what may follow it
         is the pair rule, and this is the only place that reads it *)
      unfold cis_ok in Hok. cbn [ci_sep_ok ci_pair_ok] in Hok.
      apply andb_true_iff in Hok as [_ Hok].
      apply andb_true_iff in Hok as [Hpair _].
      cbn [ci_text]. rewrite ci_src_delim.
      cbn [append starts_tick]. split; [reflexivity|split; [reflexivity|]].
      (* the row's token is nonempty, so the byte after the brace is its
         character and the pair rule is exactly the question asked *)
      unfold marked_open, dtoken.
      destruct (dwidth d) as [|w] eqn:Ew;
        [pose proof (dtoken_nonempty d) as Hn; unfold dtoken in Hn;
         rewrite Ew in Hn; discriminate|].
      cbn [chars append one after_verb_next].
      rewrite Ascii.eqb_refl. exact Hpair.
    + cbn [ci_text]. rewrite ci_src_link. unfold bracket_open.
      destruct img; cbn [append starts_tick after_verb_next];
        split; [reflexivity|split; reflexivity|reflexivity|split; reflexivity].
    + cbn [ci_text]. rewrite ci_src_ref. unfold bracket_open.
      destruct rimg; cbn [append starts_tick after_verb_next];
        split; [reflexivity|split; reflexivity|reflexivity|split; reflexivity].
    + cbn [ci_text ci_src note_text append starts_tick after_verb_next].
      split; [reflexivity|split; reflexivity].
    + cbn [ci_text ci_src auto_text append starts_tick after_verb_next].
      split; [reflexivity|split; reflexivity].
    + (* raw content opens with a backtick run, and the pair rule is what
         keeps it away from a verbatim *)
      unfold cis_ok in Hok. cbn [ci_sep_ok ci_pair_ok] in Hok.
      repeat rewrite andb_false_r in Hok. discriminate.
Qed.

Lemma after_verb_rest_nontick :
  forall v c rest,
    cis_ok (CIVerb v :: c :: rest) = true ->
    nonempty_str (ci_text (c :: rest)) = true /\
    starts_tick (ci_text (c :: rest)) = false /\
    after_verb_next (ci_text (c :: rest)) = true.
Proof.
  intros v c rest Hok.
  (* any nonempty closer that is not a backtick and not a brace will do,
     and taking one off the table keeps this independent of which rows
     exist *)
  destruct (after_verb_source_nontick v (c :: rest) (one rbrace) Hok
              eq_refl eq_refl eq_refl)
    as [Hne [Htick Hnx]].
  destruct c as [s|w|d kids|img kids dst|rimg rkids rlabel|label|a|rf rv].
  - pose proof (cis_ok_head (CIStr s) rest (cis_ok_tail _ _ Hok)) as Hs.
    cbn [ci_ok] in Hs. apply andb_true_iff in Hs as [Hs _].
    cbn [ci_text ci_src]. split; [|split].
    + destruct (escape_str s) eqn:E;
        [pose proof (escape_str_nonempty s Hs); rewrite E in H; discriminate
        |reflexivity].
    + rewrite starts_tick_app_l;
        [apply escape_str_starts_nontick, Hs|apply escape_str_nonempty, Hs].
    + apply after_verb_next_nonbrace.
      rewrite starts_brace_app_l;
        [apply escape_str_starts_nonbrace | apply escape_str_nonempty, Hs].
  - unfold cis_ok in Hok. cbn [ci_sep_ok ci_pair_ok] in Hok.
    repeat rewrite andb_false_r in Hok. discriminate.
  - unfold cis_ok in Hok. cbn [ci_sep_ok ci_pair_ok] in Hok.
    apply andb_true_iff in Hok as [_ Hok].
    apply andb_true_iff in Hok as [Hpair _].
    cbn [ci_text]. rewrite ci_src_delim. cbn [starts_tick nonempty_str].
    split; [reflexivity|split; [reflexivity|]].
    unfold marked_open, dtoken.
    destruct (dwidth d) as [|w] eqn:Ew;
      [pose proof (dtoken_nonempty d) as Hn; unfold dtoken in Hn;
       rewrite Ew in Hn; discriminate|].
    cbn [chars append one after_verb_next].
    rewrite Ascii.eqb_refl. exact Hpair.
  - cbn [ci_text]. rewrite ci_src_link. unfold bracket_open.
    destruct img;
      cbn [append starts_tick nonempty_str after_verb_next];
      split; [reflexivity|split; reflexivity|reflexivity|split; reflexivity].
  - cbn [ci_text]. rewrite ci_src_ref. unfold bracket_open.
    destruct rimg;
      cbn [append starts_tick nonempty_str after_verb_next];
      split; [reflexivity|split; reflexivity|reflexivity|split; reflexivity].
  - cbn [ci_text ci_src note_text append starts_tick nonempty_str
         after_verb_next].
    split; [reflexivity|split; reflexivity].
  - cbn [ci_text ci_src auto_text append starts_tick nonempty_str
         after_verb_next].
    split; [reflexivity|split; reflexivity].
  - unfold cis_ok in Hok. cbn [ci_sep_ok ci_pair_ok] in Hok.
    repeat rewrite andb_false_r in Hok. discriminate.
Qed.

Lemma orb_false_r_true : forall b, (b || false)%bool = true -> b = true.
Proof. intros [] H; [reflexivity | exact H]. Qed.

(* The scanner inversion, one scope deep.

   Scanning a canonical run of inlines from inside an open scope reaches
   the same state as emitting their nodes.  The scope's *closer* is a
   parameter, because two constructs supply one -- a marked delimiter and
   a bracket -- and the proof needs exactly three things of it: that it
   is nonempty and does not start with a backtick (so a verbatim before
   it resolves), and that scanning it flushes the pending text.  That
   last is the `Hflush` hypothesis, and `empty_ok` is where the two
   differ: `oclose` refuses an empty scope, `bclose` does not, which is
   what makes `[](u)` representable and `{__}` not. *)
Lemma iscan_cis_scope :
  forall cis cl O empty_ok txt prev before,
    nonempty_str cl = true -> starts_tick cl = false ->
    after_verb_next cl = true ->
    (forall txt' prev' before',
       (nonempty before' || nonempty_str txt' || empty_ok)%bool = true ->
       exists p,
         iscan_str cl (IText false txt' prev' (oemit_all before' O))
         = iscan_str cl
             (IText false EmptyString p
               (flush_text txt' (oemit_all before' O)))) ->
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    (nonempty before || nonempty_str txt || nonempty cis || empty_ok)%bool
      = true ->
    exists p,
      iscan_str (ci_text cis ++ cl)
        (IText false txt prev (oemit_all before O))
      = iscan_str cl
          (IText false EmptyString p
            (oemit_all (ci_inlines cis)
              (flush_text txt (oemit_all before O)))).
Proof.
  intro cis. pattern cis.
  apply (well_founded_induction (well_founded_ltof _ cis_size)).
  clear cis.
  intros cis IH cl O empty_ok txt prev before Hcl Hct Hnx Hflush Hok Hsep Hne.
  destruct cis as [|c rest].
  - cbn [ci_text ci_inlines map append nonempty] in Hne |- *.
    apply Hflush. rewrite <- Hne. destruct (nonempty before), (nonempty_str txt);
      reflexivity.
  - destruct c as [s|v|d kids|img kids dst|rimg rkids rlabel|label|a|rf rv].
    + destruct txt as [|x txt']; [|discriminate].
      pose proof (cis_ok_head (CIStr s) rest Hok) as Hsok.
      cbn [ci_ok] in Hsok. apply andb_true_iff in Hsok as [Hs _].
      assert (Hlt : ltof (list cinline) cis_size rest (CIStr s :: rest)).
      { unfold ltof. cbn [cis_size ci_size]. lia. }
      pose proof (IH rest Hlt cl O empty_ok s (str_last s prev) before
        Hcl Hct Hnx Hflush
        (cis_ok_tail _ _ Hok) (ci_str_tail_sep s rest Hok Hs)) as IHr.
      assert (Hnr : nonempty before || nonempty_str s || nonempty rest
                    || empty_ok = true).
      { rewrite Hs, orb_true_r. reflexivity. }
      destruct (IHr Hnr) as [p Ep]. exists p.
      cbn [ci_text ci_src ci_inlines map append].
      rewrite append_assoc, iscan_str_app, iscan_escape.
      change (EmptyString ++ s)%string with s. rewrite Ep.
      unfold flush_text at 1 2. unfold flush_text_at.
      cbn [nonempty_str ci_ast mk oemit_all].
      rewrite Hs. reflexivity.
    + pose proof (ci_verb_nonempty v rest Hok) as Hvne.
      pose proof (ci_verb_content_ok v rest Hok) as Hvok.
      destruct (after_verb_source_nontick v rest cl Hok Hcl Hct Hnx)
        as [Hsrcne [Hsrctick Hsrcnx]].
      assert (Hlt : ltof (list cinline) cis_size rest (CIVerb v :: rest)).
      { unfold ltof. cbn [cis_size ci_size]. lia. }
      assert (Hstep : forall pre,
        nonempty pre = true ->
        exists p,
          iscan_str (ci_text rest ++ cl)
            (IText false EmptyString (Some tick) (oemit_all pre O))
          = iscan_str cl
              (IText false EmptyString p
                (oemit_all (ci_inlines rest)
                  (flush_text EmptyString (oemit_all pre O))))).
      { intros pre Hpre.
        apply (IH rest Hlt cl O empty_ok EmptyString (Some tick) pre
                 Hcl Hct Hnx Hflush (cis_ok_tail _ _ Hok) eq_refl).
        rewrite Hpre. reflexivity. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [mk (Verbatim v)])%list
                    ltac:(destruct before; reflexivity)) as [p Ep].
        exists p.
        cbn [ci_text ci_src ci_inlines map]. rewrite append_assoc, iscan_str_app.
        rewrite iscan_verb_text_nonempty by auto using verb_content_safe.
        cbn [flush_text flush_text_at nonempty_str]. rewrite ?imk_semantic.
        rewrite (iscan_after_verb_nontick _ _ _ _ _ Hsrcne Hsrctick Hsrcnx),
          trim_verb_pad by exact Hvok. cbn [vnode].
        rewrite oemit_all_app in Ep.
        cbn [oemit_all flush_text flush_text_at nonempty_str] in Ep.
        rewrite Ep. cbn [oemit_all ci_ast]. reflexivity.
      * destruct (Hstep (before ++ [mk (Str (String x txt')); mk (Verbatim v)])%list
                    ltac:(destruct before; reflexivity)) as [p Ep].
        exists p.
        cbn [ci_text ci_src ci_inlines map]. rewrite append_assoc, iscan_str_app.
        rewrite iscan_verb_text_nonempty by auto using verb_content_safe.
        cbn [flush_text flush_text_at nonempty_str]. rewrite ?imk_semantic.
        rewrite (iscan_after_verb_nontick _ _ _ _ _ Hsrcne Hsrctick Hsrcnx),
          trim_verb_pad by exact Hvok. cbn [vnode].
        rewrite oemit_all_app in Ep.
        cbn [oemit_all flush_text flush_text_at nonempty_str] in Ep.
        rewrite Ep. cbn [oemit_all ci_ast]. reflexivity.
    + pose proof (cis_ok_head (CIDelim d kids) rest Hok) as Hdk.
      rewrite ci_ok_delim in Hdk. apply andb_true_iff in Hdk as [Hdk Hkidsok].
      apply andb_true_iff in Hdk as [Hden Hkidsne].
      assert (Hkidslt :
        ltof (list cinline) cis_size kids (CIDelim d kids :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_delim. lia. }
      destruct (iscan_marked_open_app d
                  (ci_text kids ++ marked_close d (ci_text rest ++ cl))
                  txt prev (oemit_all before O) Hden
                  (nonempty_str_app_l _ _ (marked_close_nonempty _ _)))
        as [cm [op Eopen]].
      pose proof (IH kids Hkidslt (marked_close d (ci_text rest ++ cl))
        (opush_at d true cm op (flush_text txt (oemit_all before O))) false
        EmptyString (Some (dchar d)) []
        (marked_close_nonempty _ _) (marked_close_starts_nontick _ _)
        (marked_close_after_verb _ _)
        (fun txt' prev' before' e =>
           iscan_marked_flush d cm (ci_text rest ++ cl) txt' prev' before' op
             (flush_text txt (oemit_all before O)) Hden (orb_false_r_true _ e)))
        as IHkids.
      assert (Hkn :
        nonempty (@nil (node inline)) || nonempty_str EmptyString ||
        nonempty kids || false = true).
      { cbn. rewrite orb_false_r. exact Hkidsne. }
      destruct (IHkids Hkidsok eq_refl Hkn) as [pk Ekids].
      assert (Hrestlt :
        ltof (list cinline) cis_size rest (CIDelim d kids :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_delim. lia. }
      assert (Hstep : forall pre,
        nonempty pre = true ->
        exists p,
          iscan_str (ci_text rest ++ cl)
            (IText false EmptyString (Some rbrace) (oemit_all pre O))
          = iscan_str cl
              (IText false EmptyString p
                (oemit_all (ci_inlines rest)
                  (flush_text EmptyString (oemit_all pre O))))).
      { intros pre Hpre.
        apply (IH rest Hrestlt cl O empty_ok EmptyString (Some rbrace) pre
                 Hcl Hct Hnx Hflush (cis_ok_tail _ _ Hok) eq_refl).
        rewrite Hpre. reflexivity. }
      assert (Hsrc : forall t,
        ((marked_open d ++ (ci_text kids ++ marked_close d EmptyString))
           ++ t)%string
        = (marked_open d ++ (ci_text kids ++ marked_close d t))%string).
      { intro t. rewrite !append_assoc, marked_close_app. reflexivity. }
      assert (Hkins : nonempty (ci_inlines kids) = true).
      { destruct kids; [discriminate|reflexivity]. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [ci_ast (CIDelim d kids)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_delim.
        rewrite append_assoc, Hsrc, Eopen.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids |- *.
        rewrite ?imk_semantic in Ekids; rewrite ?imk_semantic. rewrite Ekids.
        rewrite (iscan_marked_close_emit d cm _ (ci_inlines kids) op _ pk Hden
                   Hkins).
        rewrite <- ci_ast_delim. rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text flush_text_at nonempty_str oemit_all].
        rewrite ?imk_semantic. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CIDelim d kids)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_delim.
        rewrite append_assoc, Hsrc, Eopen.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids |- *.
        rewrite ?imk_semantic in Ekids; rewrite ?imk_semantic. rewrite Ekids.
        rewrite (iscan_marked_close_emit d cm _ (ci_inlines kids) op _ pk Hden
                   Hkins).
        rewrite <- ci_ast_delim. rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text flush_text_at nonempty_str oemit_all].
        rewrite ?imk_semantic. reflexivity.
    + pose proof (cis_ok_head (CILink img kids dst) rest Hok) as Hdk.
      rewrite ci_ok_link in Hdk. apply andb_true_iff in Hdk as [Hnl Hkidsok].
      assert (Hkidslt :
        ltof (list cinline) cis_size kids (CILink img kids dst :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_link. lia. }
      pose proof (IH kids Hkidslt (link_close dst (ci_text rest ++ cl))
        (bpush img (flush_text txt (oemit_all before O))) true
        EmptyString (Some lbrack) []
        (link_close_nonempty _ _) (link_close_starts_nontick _ _) eq_refl
        (fun txt' prev' before' _ =>
           iscan_bracket_flush dst (ci_text rest ++ cl) txt' prev' img before'
             (flush_text txt (oemit_all before O)))) as IHkids.
      destruct (IHkids Hkidsok eq_refl (orb_true_r _)) as [pk Ekids].
      assert (Hrestlt :
        ltof (list cinline) cis_size rest (CILink img kids dst :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_link. lia. }
      assert (Hstep : forall pre,
        nonempty pre = true ->
        exists p,
          iscan_str (ci_text rest ++ cl)
            (IText false EmptyString (Some rparen) (oemit_all pre O))
          = iscan_str cl
              (IText false EmptyString p
                (oemit_all (ci_inlines rest)
                  (flush_text EmptyString (oemit_all pre O))))).
      { intros pre Hpre.
        apply (IH rest Hrestlt cl O empty_ok EmptyString (Some rparen) pre
                 Hcl Hct Hnx Hflush (cis_ok_tail _ _ Hok) eq_refl).
        rewrite Hpre. reflexivity. }
      assert (Hsrc : forall t,
        (((bracket_open img ++ (ci_text kids ++ link_close dst EmptyString))
          ++ t))%string
        = (bracket_open img ++ (ci_text kids ++ link_close dst t))%string).
      { intro t. rewrite append_assoc, append_assoc, link_close_app.
        reflexivity. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [ci_ast (CILink img kids dst)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_link.
        rewrite append_assoc, Hsrc, iscan_str_app, iscan_bracket_open.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids |- *.
        rewrite ?imk_semantic in Ekids; rewrite ?imk_semantic. rewrite Ekids.
        rewrite (iscan_link_close dst _ (ci_inlines kids) img _ pk Hnl).
        rewrite <- ci_ast_link. rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text flush_text_at nonempty_str oemit_all].
        rewrite ?imk_semantic. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CILink img kids dst)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_link.
        rewrite append_assoc, Hsrc, iscan_str_app, iscan_bracket_open.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids |- *.
        rewrite ?imk_semantic in Ekids; rewrite ?imk_semantic. rewrite Ekids.
        rewrite (iscan_link_close dst _ (ci_inlines kids) img _ pk Hnl).
        rewrite <- ci_ast_link. rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text flush_text_at nonempty_str oemit_all].
        rewrite ?imk_semantic. reflexivity.
    + (* a reference link: the direct link's case with the other closer *)
      pose proof (cis_ok_head (CIRef rimg rkids rlabel) rest Hok) as Hdk.
      rewrite ci_ok_ref in Hdk.
      apply andb_true_iff in Hdk as [Hlab Hkidsok].
      apply andb_true_iff in Hlab as [Hlab Hnorm].
      apply andb_true_iff in Hlab as [Hne' Hbr].
      apply String.eqb_eq in Hnorm.
      assert (Hkidslt :
        ltof (list cinline) cis_size rkids (CIRef rimg rkids rlabel :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_ref. lia. }
      pose proof (IH rkids Hkidslt (ref_close rlabel (ci_text rest ++ cl))
        (bpush rimg (flush_text txt (oemit_all before O))) true
        EmptyString (Some lbrack) []
        (ref_close_nonempty _ _) (ref_close_starts_nontick _ _) eq_refl
        (fun txt' prev' before' _ =>
           iscan_ref_flush rlabel (ci_text rest ++ cl) txt' prev' rimg before'
             (flush_text txt (oemit_all before O)))) as IHkids.
      destruct (IHkids Hkidsok eq_refl (orb_true_r _)) as [pk Ekids].
      assert (Hrestlt :
        ltof (list cinline) cis_size rest (CIRef rimg rkids rlabel :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_ref. lia. }
      assert (Hstep : forall pre,
        nonempty pre = true ->
        exists p,
          iscan_str (ci_text rest ++ cl)
            (IText false EmptyString (Some rbrack) (oemit_all pre O))
          = iscan_str cl
              (IText false EmptyString p
                (oemit_all (ci_inlines rest)
                  (flush_text EmptyString (oemit_all pre O))))).
      { intros pre Hpre.
        apply (IH rest Hrestlt cl O empty_ok EmptyString (Some rbrack) pre
                 Hcl Hct Hnx Hflush (cis_ok_tail _ _ Hok) eq_refl).
        rewrite Hpre. reflexivity. }
      assert (Hsrc : forall t,
        (((bracket_open rimg ++ (ci_text rkids ++ ref_close rlabel EmptyString))
          ++ t))%string
        = (bracket_open rimg ++ (ci_text rkids ++ ref_close rlabel t))%string).
      { intro t. rewrite append_assoc, append_assoc, ref_close_app.
        reflexivity. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [ci_ast (CIRef rimg rkids rlabel)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_ref.
        rewrite append_assoc, Hsrc, iscan_str_app, iscan_bracket_open.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids |- *.
        rewrite ?imk_semantic in Ekids; rewrite ?imk_semantic. rewrite Ekids.
        rewrite (iscan_ref_close rlabel _ (ci_inlines rkids) rimg _ pk Hne' Hbr),
                Hnorm.
        rewrite <- ci_ast_ref. rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text flush_text_at nonempty_str oemit_all].
        rewrite ?imk_semantic. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CIRef rimg rkids rlabel)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_ref.
        rewrite append_assoc, Hsrc, iscan_str_app, iscan_bracket_open.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids |- *.
        rewrite ?imk_semantic in Ekids; rewrite ?imk_semantic. rewrite Ekids.
        rewrite (iscan_ref_close rlabel _ (ci_inlines rkids) rimg _ pk Hne' Hbr),
                Hnorm.
        rewrite <- ci_ast_ref. rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text flush_text_at nonempty_str oemit_all].
        rewrite ?imk_semantic. reflexivity.
    + pose proof (cis_ok_head (CINote label) rest Hok) as Hnote.
      rewrite ci_ok_note in Hnote.
      apply andb_true_iff in Hnote as [Hnote Hnorm].
      apply andb_true_iff in Hnote as [Hnotes Hsafe].
      apply String.eqb_eq in Hnorm.
      assert (Hrestlt : ltof (list cinline) cis_size rest (CINote label :: rest)).
      { unfold ltof. cbn [cis_size ci_size]. lia. }
      assert (Hstep : forall pre,
        nonempty pre = true ->
        exists p,
          iscan_str (ci_text rest ++ cl)
            (IText false EmptyString (Some rbrack) (oemit_all pre O))
          = iscan_str cl
              (IText false EmptyString p
                (oemit_all (ci_inlines rest)
                  (flush_text EmptyString (oemit_all pre O))))).
      { intros pre Hpre. apply (IH rest Hrestlt cl O empty_ok EmptyString
          (Some rbrack) pre Hcl Hct Hnx Hflush (cis_ok_tail _ _ Hok) eq_refl).
        rewrite Hpre. reflexivity. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [ci_ast (CINote label)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p. cbn [ci_text ci_inlines map].
        change (ci_src (CINote label)) with (note_text label).
        rewrite append_assoc, iscan_note_text by assumption.
        rewrite Hnorm. rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all ci_ast] in Erest |- *.
        rewrite ?imk_semantic in Erest; rewrite ?imk_semantic.
        rewrite Erest. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CINote label)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p. cbn [ci_text ci_inlines map].
        change (ci_src (CINote label)) with (note_text label).
        rewrite append_assoc, iscan_note_text by assumption.
        rewrite Hnorm. rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all ci_ast] in Erest |- *.
        rewrite ?imk_semantic in Erest; rewrite ?imk_semantic.
        rewrite Erest. reflexivity.
    + (* an autolink: the footnote reference's case with the other leaf,
         and no normalization to rewrite through *)
      pose proof (cis_ok_head (CIAuto a) rest Hok) as Hauto.
      rewrite ci_ok_auto in Hauto.
      apply andb_true_iff in Hauto as [Hbody Hkind].
      assert (Hrestlt : ltof (list cinline) cis_size rest (CIAuto a :: rest)).
      { unfold ltof. cbn [cis_size ci_size]. lia. }
      assert (Hstep : forall pre,
        nonempty pre = true ->
        exists p,
          iscan_str (ci_text rest ++ cl)
            (IText false EmptyString (Some gt) (oemit_all pre O))
          = iscan_str cl
              (IText false EmptyString p
                (oemit_all (ci_inlines rest)
                  (flush_text EmptyString (oemit_all pre O))))).
      { intros pre Hpre. apply (IH rest Hrestlt cl O empty_ok EmptyString
          (Some gt) pre Hcl Hct Hnx Hflush (cis_ok_tail _ _ Hok) eq_refl).
        rewrite Hpre. reflexivity. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [ci_ast (CIAuto a)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p. cbn [ci_text ci_inlines map].
        change (ci_src (CIAuto a)) with (auto_text a).
        rewrite append_assoc, iscan_auto_text by assumption.
        rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all ci_ast] in Erest |- *.
        rewrite ?imk_semantic in Erest; rewrite ?imk_semantic.
        rewrite Erest. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CIAuto a)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p. cbn [ci_text ci_inlines map].
        change (ci_src (CIAuto a)) with (auto_text a).
        rewrite append_assoc, iscan_auto_text by assumption.
        rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all ci_ast] in Erest |- *.
        rewrite ?imk_semantic in Erest; rewrite ?imk_semantic.
        rewrite Erest. reflexivity.
    + (* raw content: the same leaf shape again, with the verbatim's own
         conditions in front of the spec's *)
      pose proof (cis_ok_head (CIRaw rf rv) rest Hok) as Hraw.
      rewrite ci_ok_raw in Hraw.
      apply andb_true_iff in Hraw as [Hraw Hfmt].
      apply andb_true_iff in Hraw as [Hraw Hrok].
      apply andb_true_iff in Hraw as [Hcap Hrne].
      assert (Hrestlt :
        ltof (list cinline) cis_size rest (CIRaw rf rv :: rest)).
      { unfold ltof. cbn [cis_size ci_size]. lia. }
      assert (Hstep : forall pre,
        nonempty pre = true ->
        exists p,
          iscan_str (ci_text rest ++ cl)
            (IText false EmptyString (Some rbrace) (oemit_all pre O))
          = iscan_str cl
              (IText false EmptyString p
                (oemit_all (ci_inlines rest)
                  (flush_text EmptyString (oemit_all pre O))))).
      { intros pre Hpre. apply (IH rest Hrestlt cl O empty_ok EmptyString
          (Some rbrace) pre Hcl Hct Hnx Hflush (cis_ok_tail _ _ Hok) eq_refl).
        rewrite Hpre. reflexivity. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [ci_ast (CIRaw rf rv)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p. cbn [ci_text ci_inlines map].
        change (ci_src (CIRaw rf rv)) with (raw_text rf rv).
        rewrite append_assoc, iscan_raw_text by assumption.
        rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all ci_ast] in Erest |- *.
        rewrite ?imk_semantic in Erest; rewrite ?imk_semantic.
        rewrite Erest. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CIRaw rf rv)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p. cbn [ci_text ci_inlines map].
        change (ci_src (CIRaw rf rv)) with (raw_text rf rv).
        rewrite append_assoc, iscan_raw_text by assumption.
        rewrite oemit_all_app in Erest.
        cbn [flush_text flush_text_at nonempty_str oemit_all ci_ast] in Erest |- *.
        rewrite ?imk_semantic in Erest; rewrite ?imk_semantic.
        rewrite Erest. reflexivity.
Qed.

(* The delimiter instance, which is what the two callers below use. *)
Lemma iscan_cis_marked :
  forall cis k cm tail txt prev before open base,
    denabled_of k = true ->
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    (nonempty before || nonempty_str txt || nonempty cis)%bool = true ->
    exists p,
      iscan_str (ci_text cis ++ marked_close k tail)
        (IText false txt prev
           (oemit_all before (opush_at k true cm open base)))
      = iscan_str (marked_close k tail)
          (IText false EmptyString p
            (oemit_all (ci_inlines cis)
              (flush_text txt
                 (oemit_all before (opush_at k true cm open base))))).
Proof.
  intros cis k cm tail txt prev before open base Hden Hok Hsep Hne.
  apply (iscan_cis_scope cis (marked_close k tail)
           (opush_at k true cm open base) false
           txt prev before
           (marked_close_nonempty _ _) (marked_close_starts_nontick _ _)
           (marked_close_after_verb _ _)
           (fun txt' prev' before' e =>
              iscan_marked_flush k cm tail txt' prev' before' open base Hden
                (orb_false_r_true _ e))
           Hok Hsep).
  rewrite orb_false_r. exact Hne.
Qed.

(* And the bracket instance, for a label scanned inside its own scope. *)
Lemma iscan_cis_bracket :
  forall cis dst tail txt prev image before base,
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    exists p,
      iscan_str (ci_text cis ++ link_close dst tail)
        (IText false txt prev (oemit_all before (bpush image base)))
      = iscan_str (link_close dst tail)
          (IText false EmptyString p
            (oemit_all (ci_inlines cis)
              (flush_text txt (oemit_all before (bpush image base))))).
Proof.
  intros cis dst tail txt prev image before base Hok Hsep.
  apply (iscan_cis_scope cis (link_close dst tail) (bpush image base) true
           txt prev before
           (link_close_nonempty _ _) (link_close_starts_nontick _ _)
           eq_refl
           (fun txt' prev' before' _ =>
              iscan_bracket_flush dst tail txt' prev' image before' base)
           Hok Hsep).
  apply orb_true_r.
Qed.

(* And the reference instance, which differs only in the closer. *)
Lemma iscan_cis_ref :
  forall cis label tail txt prev image before base,
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    exists p,
      iscan_str (ci_text cis ++ ref_close label tail)
        (IText false txt prev (oemit_all before (bpush image base)))
      = iscan_str (ref_close label tail)
          (IText false EmptyString p
            (oemit_all (ci_inlines cis)
              (flush_text txt (oemit_all before (bpush image base))))).
Proof.
  intros cis label tail txt prev image before base Hok Hsep.
  apply (iscan_cis_scope cis (ref_close label tail) (bpush image base) true
           txt prev before
           (ref_close_nonempty _ _) (ref_close_starts_nontick _ _)
           eq_refl
           (fun txt' prev' before' _ =>
              iscan_ref_flush label tail txt' prev' image before' base)
           Hok Hsep).
  apply orb_true_r.
Qed.

(* Once a canonical scan has closed every nested delimiter, the output
   state again has an empty scope stack. *)
Definition flush_out (txt : string) (out : inlines) : inlines :=
  if nonempty_str txt then mk (Str txt) :: out else out.

(* The canonical scan never leaves a spec waiting -- `needs_escape`
   claims `{` -- so every state it reaches holds nodes only, and is
   written that way. *)
Lemma flush_text_flat :
  forall txt out,
    flush_text txt (OState (List.map OIn out) [] None)
    = OState (List.map OIn (flush_out txt out)) [] None.
Proof.
  intros txt out. unfold flush_text, flush_text_at, flush_out, oemit; cbn [os_stk].
  destruct (nonempty_str txt); reflexivity.
Qed.

Lemma iscan_cis :
  forall cis prev' txt out,
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    ifinish (iscan_str (ci_text cis)
               (IText false txt prev' (OState (List.map OIn out) [] None)))
    = (List.rev (flush_out txt out) ++ ci_inlines cis)%list.
Proof.
  intro cis. pattern cis.
  apply (well_founded_induction (well_founded_ltof _ cis_size)).
  clear cis. intros cis IH prev' txt out Hok Hsep.
  destruct cis as [|c rest].
  - cbn [ci_text ci_inlines iscan_str]. rewrite app_nil_r.
    rewrite ifinish_text, flush_text_flat; cbn [os_out].
    rewrite oresolve_map. reflexivity.
  - assert (Hrestlt : ltof (list cinline) cis_size rest (c :: rest)).
    { unfold ltof. cbn [cis_size]. pose proof (ci_size_pos c). lia. }
    destruct c as [s|v|d kids|img kids dst|rimg rkids rlabel|label|a|rf rv].
    + destruct txt as [|x txt']; [|discriminate].
      pose proof (cis_ok_head (CIStr s) rest Hok) as Hsok.
      cbn [ci_ok] in Hsok. apply andb_true_iff in Hsok as [Hs _].
      cbn [ci_text ci_src]. rewrite iscan_str_app, iscan_escape.
      cbn [ci_inlines map append].
      rewrite <- ?List.map_cons;
      rewrite (IH rest Hrestlt (str_last s prev') s out).
      * unfold flush_out at 1. rewrite Hs.
        cbn [List.rev nonempty_str ci_ast map].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * apply ci_str_tail_sep; assumption.
    + pose proof (ci_verb_nonempty v rest Hok) as Hvne.
      pose proof (ci_verb_content_ok v rest Hok) as Hvok.
      cbn [ci_text ci_src]. rewrite iscan_str_app.
      rewrite iscan_verb_text_nonempty by auto using verb_content_safe.
      rewrite flush_text_flat.
      destruct rest as [|r rest'].
      * cbn [ci_text ci_inlines map append].
        cbn [iscan_str].
        unfold ifinish, ifinish_rev;
        cbn [ifinish_ostate ifinish_ostate_flat iresolve].
        rewrite nat_eqb_refl, trim_verb_pad by exact Hvok. cbn [vnode].
        unfold oemit, ofinish, oitems_of; cbn [os_stk os_out oflatten oapp].
        rewrite <- ?List.map_cons, oresolve_map. cbn [List.rev ci_ast]. reflexivity.
      * destruct (after_verb_rest_nontick v r rest' Hok) as [Hne [Htick Hnx]].
        rewrite (iscan_after_verb_nontick _ _ _ _ _ Hne Htick Hnx).
        rewrite trim_verb_pad by exact Hvok. cbn [vnode].
        cbn [oemit os_stk os_out os_word_start].
        rewrite <- ?List.map_cons.
        rewrite (IH (r :: rest') Hrestlt (Some tick) EmptyString
          (mk (Verbatim v) :: flush_out txt out)).
        -- cbn [flush_out nonempty_str ci_inlines map ci_ast List.rev].
           rewrite <- List.app_assoc. reflexivity.
        -- exact (cis_ok_tail _ _ Hok).
        -- reflexivity.
    + pose proof (cis_ok_head (CIDelim d kids) rest Hok) as Hdk.
      rewrite ci_ok_delim in Hdk. apply andb_true_iff in Hdk as [Hdk Hkidsok].
      apply andb_true_iff in Hdk as [Hden Hkidsne].
      destruct (iscan_marked_open_app d
                  (ci_text kids ++ marked_close d (ci_text rest))
                  txt prev' (OState (List.map OIn out) [] None) Hden
                  (nonempty_str_app_l _ _ (marked_close_nonempty _ _)))
        as [cm [op Eopen]].
      pose proof (iscan_cis_marked kids d cm (ci_text rest) EmptyString
        (Some (dchar d)) [] op
        (flush_text txt (OState (List.map OIn out) [] None))
        Hden Hkidsok eq_refl) as IHkids.
      assert (Hkn :
        nonempty (@nil (node inline)) || nonempty_str EmptyString ||
        nonempty kids = true).
      { cbn. exact Hkidsne. }
      destruct (IHkids Hkn) as [pk Ekids].
      cbn [ci_text ci_inlines map]. rewrite ci_src_delim.
      assert (Hsrc :
        ((marked_open d ++ (ci_text kids ++ marked_close d EmptyString))
           ++ ci_text rest)%string
        = (marked_open d ++
            (ci_text kids ++ marked_close d (ci_text rest)))%string).
      { rewrite !append_assoc, marked_close_app. reflexivity. }
      rewrite Hsrc, Eopen.
      cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids. rewrite Ekids.
      assert (Hkins : nonempty (ci_inlines kids) = true).
      { destruct kids; [discriminate|reflexivity]. }
      rewrite (iscan_marked_close_emit d cm _ (ci_inlines kids) op _ pk Hden
                 Hkins).
      rewrite <- ci_ast_delim.
      destruct (flush_text txt (OState (List.map OIn out) [] None))
        as [out' stk' word'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk Eword. subst out' stk' word'.
      cbn [oemit os_out os_stk os_word_start].
      rewrite <- ?List.map_cons;
      rewrite (IH rest Hrestlt (Some rbrace) EmptyString
        (ci_ast (CIDelim d kids) :: flush_out txt out)).
      * cbn [flush_out nonempty_str ci_inlines map List.rev].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * reflexivity.
    + pose proof (cis_ok_head (CILink img kids dst) rest Hok) as Hdk.
      rewrite ci_ok_link in Hdk. apply andb_true_iff in Hdk as [Hnl Hkidsok].
      destruct (iscan_cis_bracket kids dst (ci_text rest) EmptyString
        (Some lbrack) img [] (flush_text txt (OState (List.map OIn out) [] None))
        Hkidsok eq_refl) as [pk Ekids].
      cbn [ci_text ci_inlines map]. rewrite ci_src_link.
      assert (Hsrc :
        ((bracket_open img ++ (ci_text kids ++ link_close dst EmptyString)) ++
          ci_text rest)%string
        = (bracket_open img ++
            (ci_text kids ++ link_close dst (ci_text rest)))%string).
      { rewrite append_assoc, append_assoc, link_close_app. reflexivity. }
      rewrite Hsrc, iscan_str_app, iscan_bracket_open.
      cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids. rewrite Ekids.
      rewrite (iscan_link_close dst _ (ci_inlines kids) img _ pk Hnl).
      rewrite <- ci_ast_link.
      destruct (flush_text txt (OState (List.map OIn out) [] None))
        as [out' stk' word'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk Eword. subst out' stk' word'.
      cbn [oemit os_out os_stk os_word_start].
      rewrite <- ?List.map_cons;
      rewrite (IH rest Hrestlt (Some rparen) EmptyString
        (ci_ast (CILink img kids dst) :: flush_out txt out)).
      * cbn [flush_out nonempty_str ci_inlines map List.rev].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * reflexivity.
    + pose proof (cis_ok_head (CIRef rimg rkids rlabel) rest Hok) as Hdk.
      rewrite ci_ok_ref in Hdk.
      apply andb_true_iff in Hdk as [Hlab Hkidsok].
      apply andb_true_iff in Hlab as [Hlab Hnorm].
      apply andb_true_iff in Hlab as [Hne' Hbr].
      apply String.eqb_eq in Hnorm.
      destruct (iscan_cis_ref rkids rlabel (ci_text rest) EmptyString
        (Some lbrack) rimg [] (flush_text txt (OState (List.map OIn out) [] None))
        Hkidsok eq_refl) as [pk Ekids].
      cbn [ci_text ci_inlines map]. rewrite ci_src_ref.
      assert (Hsrc :
        ((bracket_open rimg ++ (ci_text rkids ++ ref_close rlabel EmptyString)) ++
          ci_text rest)%string
        = (bracket_open rimg ++
            (ci_text rkids ++ ref_close rlabel (ci_text rest)))%string).
      { rewrite append_assoc, append_assoc, ref_close_app. reflexivity. }
      rewrite Hsrc, iscan_str_app, iscan_bracket_open.
      cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids. rewrite Ekids.
      rewrite (iscan_ref_close rlabel _ (ci_inlines rkids) rimg _ pk Hne' Hbr),
              Hnorm.
      rewrite <- ci_ast_ref.
      destruct (flush_text txt (OState (List.map OIn out) [] None))
        as [out' stk' word'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk Eword. subst out' stk' word'.
      cbn [oemit os_out os_stk os_word_start].
      rewrite <- ?List.map_cons;
      rewrite (IH rest Hrestlt (Some rbrack) EmptyString
        (ci_ast (CIRef rimg rkids rlabel) :: flush_out txt out)).
      * cbn [flush_out nonempty_str ci_inlines map List.rev].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * reflexivity.
    + pose proof (cis_ok_head (CINote label) rest Hok) as Hnote.
      rewrite ci_ok_note in Hnote.
      apply andb_true_iff in Hnote as [Hnote Hnorm].
      apply andb_true_iff in Hnote as [Hnotes Hsafe].
      apply String.eqb_eq in Hnorm.
      cbn [ci_text ci_inlines map].
      change (ci_src (CINote label)) with (note_text label).
      rewrite (iscan_note_text label (ci_text rest) txt prev'
                 (OState (List.map OIn out) [] None) Hnotes Hsafe), Hnorm.
      destruct (flush_text txt (OState (List.map OIn out) [] None))
        as [out' stk' word'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk Eword. subst out' stk' word'.
      cbn [oemit os_out os_stk os_word_start].
      change (mk (FootnoteReference label)) with (ci_ast (CINote label)).
      rewrite <- ?List.map_cons;
      rewrite (IH rest Hrestlt (Some rbrack) EmptyString
        (ci_ast (CINote label) :: flush_out txt out)).
      * cbn [flush_out nonempty_str ci_ast List.rev].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * reflexivity.
    + pose proof (cis_ok_head (CIAuto a) rest Hok) as Hauto.
      rewrite ci_ok_auto in Hauto.
      apply andb_true_iff in Hauto as [Hbody Hkind].
      cbn [ci_text ci_inlines map].
      change (ci_src (CIAuto a)) with (auto_text a).
      rewrite (iscan_auto_text a (ci_text rest) txt prev'
                 (OState (List.map OIn out) [] None) Hbody Hkind).
      destruct (flush_text txt (OState (List.map OIn out) [] None))
        as [out' stk' word'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk Eword. subst out' stk' word'.
      cbn [oemit os_out os_stk os_word_start].
      change (mk (auto_node a)) with (ci_ast (CIAuto a)).
      rewrite <- ?List.map_cons;
      rewrite (IH rest Hrestlt (Some gt) EmptyString
        (ci_ast (CIAuto a) :: flush_out txt out)).
      * cbn [flush_out nonempty_str ci_ast List.rev].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * reflexivity.
    + pose proof (cis_ok_head (CIRaw rf rv) rest Hok) as Hraw.
      rewrite ci_ok_raw in Hraw.
      apply andb_true_iff in Hraw as [Hraw Hfmt].
      apply andb_true_iff in Hraw as [Hraw Hrok].
      apply andb_true_iff in Hraw as [Hcap Hrne].
      cbn [ci_text ci_inlines map].
      change (ci_src (CIRaw rf rv)) with (raw_text rf rv).
      rewrite (iscan_raw_text rf rv (ci_text rest) txt prev'
                 (OState (List.map OIn out) [] None) Hcap Hrne Hrok Hfmt).
      destruct (flush_text txt (OState (List.map OIn out) [] None))
        as [out' stk' word'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk Eword. subst out' stk' word'.
      cbn [oemit os_out os_stk os_word_start].
      change (mk (RawInline rf rv)) with (ci_ast (CIRaw rf rv)).
      rewrite <- ?List.map_cons;
      rewrite (IH rest Hrestlt (Some rbrace) EmptyString
        (ci_ast (CIRaw rf rv) :: flush_out txt out)).
      * cbn [flush_out nonempty_str ci_ast List.rev].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * reflexivity.
Qed.

(* The other half of what a canonical line owes the paragraph: it leaves
   the scan owing nothing to the next line.  Every canonical constituent
   either stays in `IText` (a string) or resolves its closing run before
   the line ends (a verbatim), which is exactly why the empty verbatim
   had to go: two adjacent runs leave `IOpen`. *)
Lemma iscan_cis_closed :
  forall cis prev' txt out,
    cis_ok cis = true ->
    iscan_closed (iscan_str (ci_text cis)
                    (IText false txt prev' (OState (List.map OIn out) [] None)))
    = true.
Proof.
  intro cis. pattern cis.
  apply (well_founded_induction (well_founded_ltof _ cis_size)).
  clear cis. intros cis IH prev' txt out Hok.
  destruct cis as [|c rest]; [reflexivity|].
  assert (Hrestlt : ltof (list cinline) cis_size rest (c :: rest)).
  { unfold ltof. cbn [cis_size]. pose proof (ci_size_pos c). lia. }
  destruct c as [s|v|d kids|img kids dst|rimg rkids rlabel|label|a|rf rv].
  - cbn [ci_text ci_src]. rewrite iscan_str_app, iscan_escape.
    apply (IH rest Hrestlt), (cis_ok_tail _ _ Hok).
  - pose proof (ci_verb_nonempty v rest Hok) as Hvne.
    pose proof (ci_verb_content_ok v rest Hok) as Hvok.
    cbn [ci_text ci_src]. rewrite iscan_str_app.
    rewrite iscan_verb_text_nonempty by auto using verb_content_safe.
    rewrite flush_text_flat.
    destruct rest as [|r rest'].
    + cbn [ci_text iscan_str iscan_closed iclosed_at iresolve os_stk null].
      rewrite nat_eqb_refl. reflexivity.
    + destruct (after_verb_rest_nontick v r rest' Hok) as [Hne [Htick Hnx]].
      rewrite (iscan_after_verb_nontick _ _ _ _ _ Hne Htick Hnx).
      rewrite trim_verb_pad by exact Hvok. cbn [vnode].
      cbn [oemit os_out os_stk os_word_start].
      rewrite <- ?List.map_cons.
      apply (IH (r :: rest') Hrestlt), (cis_ok_tail _ _ Hok).
  - pose proof (cis_ok_head (CIDelim d kids) rest Hok) as Hdk.
    rewrite ci_ok_delim in Hdk. apply andb_true_iff in Hdk as [Hdk Hkidsok].
    apply andb_true_iff in Hdk as [Hden Hkidsne].
    destruct (iscan_marked_open_app d
                (ci_text kids ++ marked_close d (ci_text rest))
                txt prev' (OState (List.map OIn out) [] None) Hden
                (nonempty_str_app_l _ _ (marked_close_nonempty _ _)))
      as [cm [op Eopen]].
    pose proof (iscan_cis_marked kids d cm (ci_text rest) EmptyString
      (Some (dchar d)) [] op
      (flush_text txt (OState (List.map OIn out) [] None))
      Hden Hkidsok eq_refl) as IHkids.
    assert (Hkn :
      nonempty (@nil (node inline)) || nonempty_str EmptyString ||
      nonempty kids = true).
    { cbn. exact Hkidsne. }
    destruct (IHkids Hkn) as [pk Ekids].
    cbn [ci_text]. rewrite ci_src_delim.
    assert (Hsrc :
      ((marked_open d ++ (ci_text kids ++ marked_close d EmptyString))
         ++ ci_text rest)%string
      = (marked_open d ++
          (ci_text kids ++ marked_close d (ci_text rest)))%string).
    { rewrite !append_assoc, marked_close_app. reflexivity. }
    rewrite Hsrc, Eopen.
    cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids. rewrite Ekids.
    assert (Hkins : nonempty (ci_inlines kids) = true).
    { destruct kids; [discriminate|reflexivity]. }
    rewrite (iscan_marked_close_emit d cm _ (ci_inlines kids) op _ pk Hden Hkins).
    destruct (flush_text txt (OState (List.map OIn out) [] None))
      as [out' stk' word'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk Eword. subst out' stk' word'.
    cbn [oemit os_out os_stk os_word_start]. rewrite <- ?List.map_cons.
    apply (IH rest Hrestlt), (cis_ok_tail _ _ Hok).
  - pose proof (cis_ok_head (CILink img kids dst) rest Hok) as Hdk.
    rewrite ci_ok_link in Hdk. apply andb_true_iff in Hdk as [Hnl Hkidsok].
    destruct (iscan_cis_bracket kids dst (ci_text rest) EmptyString
      (Some lbrack) img [] (flush_text txt (OState (List.map OIn out) [] None))
      Hkidsok eq_refl) as [pk Ekids].
    cbn [ci_text]. rewrite ci_src_link.
    assert (Hsrc :
      ((bracket_open img ++ (ci_text kids ++ link_close dst EmptyString)) ++
        ci_text rest)%string
      = (bracket_open img ++
          (ci_text kids ++ link_close dst (ci_text rest)))%string).
    { rewrite append_assoc, append_assoc, link_close_app. reflexivity. }
    rewrite Hsrc, iscan_str_app, iscan_bracket_open.
    cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids. rewrite Ekids.
    rewrite (iscan_link_close dst _ (ci_inlines kids) img _ pk Hnl).
    destruct (flush_text txt (OState (List.map OIn out) [] None))
      as [out' stk' word'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk Eword. subst out' stk' word'.
    cbn [oemit os_out os_stk os_word_start]. rewrite <- ?List.map_cons.
    apply (IH rest Hrestlt), (cis_ok_tail _ _ Hok).
  - pose proof (cis_ok_head (CIRef rimg rkids rlabel) rest Hok) as Hdk.
    rewrite ci_ok_ref in Hdk.
    apply andb_true_iff in Hdk as [Hlab Hkidsok].
    apply andb_true_iff in Hlab as [Hlab Hnorm].
    apply andb_true_iff in Hlab as [Hne' Hbr].
    destruct (iscan_cis_ref rkids rlabel (ci_text rest) EmptyString
      (Some lbrack) rimg [] (flush_text txt (OState (List.map OIn out) [] None))
      Hkidsok eq_refl) as [pk Ekids].
    cbn [ci_text]. rewrite ci_src_ref.
    assert (Hsrc :
      ((bracket_open rimg ++ (ci_text rkids ++ ref_close rlabel EmptyString)) ++
        ci_text rest)%string
      = (bracket_open rimg ++
          (ci_text rkids ++ ref_close rlabel (ci_text rest)))%string).
    { rewrite append_assoc, append_assoc, ref_close_app. reflexivity. }
    rewrite Hsrc, iscan_str_app, iscan_bracket_open.
    cbn [flush_text flush_text_at nonempty_str oemit_all] in Ekids. rewrite Ekids.
    rewrite (iscan_ref_close rlabel _ (ci_inlines rkids) rimg _ pk Hne' Hbr).
    destruct (flush_text txt (OState (List.map OIn out) [] None))
      as [out' stk' word'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk Eword. subst out' stk' word'.
    cbn [oemit os_out os_stk os_word_start]. rewrite <- ?List.map_cons.
    apply (IH rest Hrestlt), (cis_ok_tail _ _ Hok).
  - pose proof (cis_ok_head (CINote label) rest Hok) as Hnote.
    rewrite ci_ok_note in Hnote.
    apply andb_true_iff in Hnote as [Hnote Hnorm].
    apply andb_true_iff in Hnote as [Hnotes Hsafe].
    cbn [ci_text]. change (ci_src (CINote label)) with (note_text label).
    rewrite (iscan_note_text label (ci_text rest) txt prev'
               (OState (List.map OIn out) [] None) Hnotes Hsafe).
    destruct (flush_text txt (OState (List.map OIn out) [] None))
      as [out' stk' word'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk Eword. subst out' stk' word'.
    cbn [oemit os_out os_stk os_word_start]. rewrite <- ?List.map_cons.
    apply (IH rest Hrestlt), (cis_ok_tail _ _ Hok).
  - pose proof (cis_ok_head (CIAuto a) rest Hok) as Hauto.
    rewrite ci_ok_auto in Hauto.
    apply andb_true_iff in Hauto as [Hbody Hkind].
    cbn [ci_text]. change (ci_src (CIAuto a)) with (auto_text a).
    rewrite (iscan_auto_text a (ci_text rest) txt prev'
               (OState (List.map OIn out) [] None) Hbody Hkind).
    destruct (flush_text txt (OState (List.map OIn out) [] None))
      as [out' stk' word'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk Eword. subst out' stk' word'.
    cbn [oemit os_out os_stk os_word_start]. rewrite <- ?List.map_cons.
    apply (IH rest Hrestlt), (cis_ok_tail _ _ Hok).
  - pose proof (cis_ok_head (CIRaw rf rv) rest Hok) as Hraw.
    rewrite ci_ok_raw in Hraw.
    apply andb_true_iff in Hraw as [Hraw Hfmt].
    apply andb_true_iff in Hraw as [Hraw Hrok].
    apply andb_true_iff in Hraw as [Hcap Hrne].
    cbn [ci_text]. change (ci_src (CIRaw rf rv)) with (raw_text rf rv).
    rewrite (iscan_raw_text rf rv (ci_text rest) txt prev'
               (OState (List.map OIn out) [] None) Hcap Hrne Hrok Hfmt).
    destruct (flush_text txt (OState (List.map OIn out) [] None))
      as [out' stk' word'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk Eword. subst out' stk' word'.
    cbn [oemit os_out os_stk os_word_start]. rewrite <- ?List.map_cons.
    apply (IH rest Hrestlt), (cis_ok_tail _ _ Hok).
Qed.

(* Every way a pending delimiter can resolve lands back in text mode:
   closing, opening and decaying to literal text all do.  So after
   `iresolve` there is no `IBrace` and no `IDelim` left, which is what
   makes the catch-all arms of `ibreak` and `ifinish_ostate` dead. *)
Lemma idelim_done_text :
  forall k txt bef marker next o,
    exists txt' prev' o',
      idelim_done k txt bef marker next o = IText false txt' prev' o'.
Proof.
  intros k txt bef marker next o. unfold idelim_done.
  destruct (dbare k bef && negb marker && nonspace_at next)%bool; eauto.
Qed.

Lemma idelim_resolve_text :
  forall k txt bef marker next o,
    exists txt' prev' o',
      idelim_resolve k txt bef marker next o = IText false txt' prev' o'.
Proof.
  intros k txt bef marker next o. unfold idelim_resolve.
  destruct (nonspace_at bef || marker)%bool; [|apply idelim_done_text].
  sem_flush. destruct (sclose k marker (flush_text txt o)); [eauto|].
  destruct (oclose_barred k marker o); [eauto | apply idelim_done_text].
Qed.

Lemma iresolve_resolved :
  forall st,
    match iresolve st with
    | IBrace _ _ _ | IBang _ _ _ | IDollar _ _ _ _
    | IPeriod _ _ _ _ | IDash _ _ _ _
    | IDelim _ _ _ _ _ _ | IClosed _ _ => False
    | _ => True
    end.
Proof.
  intros [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|cltxt clob|kids img sp ssrc sob|ap asrc atxt aprev ash aob|kids img label ob|nesc nimg nlab nob|kids img esc depth dst sh ob|asrc atxt aob|rspec rtxt rob];
    cbn [iresolve]; try exact I.
  - destruct (Nat.ltb (S seen) (dwidth k)); [exact I|].
    destruct mrk; [exact I|].
    destruct (idelim_resolve_text k txt cc false None o) as [txt' [prev' [o' E]]].
    rewrite E. exact I.
Qed.

Lemma parse_inline_line_escape :
  forall s, nonempty_str s = true ->
  parse_inline_line (escape_str s) = [mk (Str s)].
Proof.
  intros s H. unfold parse_inline_line, istart. rewrite iscan_escape.
  change (EmptyString ++ s)%string with s.
  unfold ifinish, ifinish_rev.
  cbn [ifinish_ostate ifinish_ostate_flat iresolve]. unfold flush_text, flush_text_at.
  rewrite H. reflexivity.
Qed.

(* A paragraph's lines, in order, into inlines: one scan, with `ibreak`
   between lines.  It was a scan per line joined by `SoftBreak` until
   spans were allowed to cross a break; the two agree exactly when no
   line leaves the scan mid-span, which is what the canonical view
   guarantees and `para_inlines_cons2_closed` states. *)
Definition para_inlines (l : list string) : inlines :=
  ifinish (iscan_lines l istart).

(* A paragraph whose first `k` lines came from a block attribute spec
   that failed.  Those lines are re-read with attributes off and the rest
   of the paragraph is read as usual, which is what `reparseAttributes`
   followed by `this.pos = lastpos + 1` does (`block.ts:592-595`). *)
Definition para_inlines_off (k : nat) (l : list string) : inlines :=
  ifinish (iscan_lines_off k l istart).

Lemma para_inlines_off_0 :
  forall l, para_inlines_off 0 l = para_inlines l.
Proof. reflexivity. Qed.

(* A paragraph's lines with their source line indices, scanned so that
   every node records where it came from.  `off` is `para_inlines_off`'s:
   how many leading lines are read with attributes off. *)
Definition para_inlines_located `{PosPolicy} (off : nat)
  (l : list (nat * string)) : inlines :=
  ifinish_located l (iscan_lines_located off l istart).

(* The one entry the block layer calls.  It asks the policy before it
   looks at the lines, so at `semantic_pos` it *is* `para_inlines_off` of
   their texts, by conversion: a paragraph the located parse builds and
   one the semantic parse builds differ in what the nodes carry and in
   nothing else, and no statement about the latter has to mention this.
   (`.project/project-engineering-lessons.md`, on a conversion identity
   being free.) *)
Definition para_inlines_at `{PosPolicy} (off : nat)
  (l : list (nat * string)) : inlines :=
  if pos_records
  then para_inlines_located off l
  else para_inlines_off off (map snd l).

Lemma para_inlines_at_semantic : forall off l,
  @para_inlines_at semantic_pos off l = para_inlines_off off (map snd l).
Proof. reflexivity. Qed.

Lemma erase_istart : erase_iscan istart = istart.
Proof. reflexivity. Qed.

Lemma erase_para_inlines_located : forall `{P : PosPolicy} off l,
  erase_inlines (@para_inlines_located P off l) =
  para_inlines_off off (map snd l).
Proof.
  intros P off l. unfold para_inlines_located, para_inlines_off.
  rewrite erase_ifinish_located, erase_iscan_lines_located, erase_istart.
  reflexivity.
Qed.

(* The same statement at the ambient instance, which is what a block
   built by it needs: a paragraph the semantic scan produced is already
   position-free. *)
Lemma erase_inlines_para_inlines_off : forall off l,
  erase_inlines (para_inlines_off off l) = para_inlines_off off l.
Proof.
  intros off l. unfold para_inlines_off.
  rewrite erase_ifinish, erase_iscan_lines_off, erase_istart. reflexivity.
Qed.

Lemma erase_inlines_para_inlines : forall l,
  erase_inlines (para_inlines l) = para_inlines l.
Proof. intros l. apply (erase_inlines_para_inlines_off 0). Qed.

(* The inline half of C2.  Uniform in the policy on purpose: at
   `located_pos` it says the spans the scan records are all that
   distinguishes it from the semantic reading; at `semantic_pos` the same
   statement says the semantic reading is position-free, which is what
   the block erasure needs wherever a paragraph is still built by the
   ambient instance. *)
Theorem para_inlines_at_erase : forall `{P : PosPolicy} off l,
  erase_inlines (@para_inlines_at P off l) =
  para_inlines_off off (map snd l).
Proof.
  intros P off l. unfold para_inlines_at.
  destruct (@pos_records P);
    [apply erase_para_inlines_located|apply erase_inlines_para_inlines_off].
Qed.

(* Classification sees the source and nothing else.  The environment is
   named here before brackets arrive so their parser can produce
   unresolved `Reference` and `FootnoteReference` nodes without consulting
   either side table; a later resolution pass may fill targets but may not
   change this tree. *)
Record inline_env : Type := InlineEnv {
  inline_notes : note_map;
  inline_references : reference_map;
  inline_auto_references : reference_map
}.

Definition classify_inlines (_ : inline_env) (l : list string) : inlines :=
  para_inlines l.

Theorem classify_inlines_locality :
  forall a b l, classify_inlines a l = classify_inlines b l.
Proof. reflexivity. Qed.

Lemma para_inlines_one :
  forall x, para_inlines [x] = parse_inline_line (strip_trailing_ws x).
Proof. reflexivity. Qed.

(* The old defining equation, now conditional: a line that leaves the
   scan mid-span does not contribute a separable run of inlines, because
   the span it opened is finished by a later line. *)
Lemma para_inlines_cons2_closed :
  forall x y rest,
    iscan_closed (iscan_str x istart) = true ->
    para_inlines (x :: y :: rest) =
    (parse_inline_line x ++ mk SoftBreak :: para_inlines (y :: rest))%list.
Proof.
  intros x y rest Hcl. unfold para_inlines, parse_inline_line.
  rewrite iscan_lines_cons2, (ibreak_closed _ Hcl), ?imk_here_semantic.
  change (IText false EmptyString None
            (OState (OIn (mk SoftBreak) :: ifinish_items (iscan_str x istart))
               [] None))
    with (iout_app (OIn (mk SoftBreak) :: ifinish_items (iscan_str x istart))
            istart).
  rewrite iscan_lines_out_app, ifinish_out_app by reflexivity.
  rewrite oresolve_cons_nonplain by reflexivity.
  rewrite <- (ifinish_rev_items (iscan_str x istart)).
  cbn [List.rev]. rewrite <- List.app_assoc. reflexivity.
Qed.

(*
The key connective
==================

Where a colon on a line pairs a label with what follows it, which is
`.project/keyed-blocks.md` sections 3.1 and 3.2.  The block layer asks
this of a line that would otherwise open a paragraph; both questions it
has to answer are inline ones -- what the scan still has open at a byte,
and how many nodes the text before that byte resolves to -- which is why
the test lives here and not beside the other line recognizers in
`Line.v`.
*)

(* The colon sits against its label: the byte before it is not
   whitespace, and a line-initial colon has no label at all. *)
Definition key_before (prev : option ascii) : bool :=
  match prev with None => false | Some c => negb (is_ws c) end.

(* And a space or the end of the line follows it.  A tab is neither, so
   this is spelled out rather than reusing `is_space`, which admits one. *)
Definition key_after (rest : string) : bool :=
  match rest with
  | EmptyString => true
  | String c _ => Ascii.eqb c " "%char
  end.

(* The line's split point: the label's source and the value's.  One
   left-to-right pass with the scan state carried alongside, so no byte
   is read twice and no candidate needs a lookahead.  `iscan_closed` is
   the "nothing open" test: a colon the scan is unsure about is not a
   split point and the pass goes on to the next, which is what sends
   `x{title="a: b"}y: z` to its second colon.

   An escaped colon is declined by that same test, a pending backslash
   being an open state, so `foo\: bar` needs no case of its own. *)
Fixpoint key_scan (s lbl : string) (prev : option ascii) (st : iscan)
  : option (string * string) :=
  match s with
  | EmptyString => None
  | String c rest =>
      if (Ascii.eqb c ":"%char && key_before prev && key_after rest
          && iscan_settled c st)%bool
      then Some (rev_string lbl, drop_leading_ws rest)
      else key_scan rest (String c lbl) (Some c) (istep c st)
  end.

(* The line is normalised first, which is what makes the answer
   independent of the indentation a container prefix leaves behind. *)
Definition key_point (l : string) : option (string * string) :=
  key_scan (drop_leading_ws l) EmptyString None istart.

(* Is the label one inline?  A fact about the *resolved* list, so it
   turns on the merge in `oresolve`: `it's` and `foo\: bar` are one run
   because of it, and ``x`y` `` is two because a verbatim span cannot
   merge with the text beside it. *)
Definition key_label_ok (lbl : string) : bool :=
  match para_inlines [lbl] with [_] => true | _ => false end.

(* The split, when the line is a key.  Only the first split point is
   tried: a label already two elements cannot come back to one, since
   collapsing two settled elements would take a construct opening before
   both, and that would have left the earlier point unsettled. *)
Definition key_split (l : string) : option (string * string) :=
  match key_point l with
  | Some (lbl, v) => if key_label_ok lbl then Some (lbl, v) else None
  | None => None
  end.

(* Leading whitespace is dropped before the scan, so a pad is invisible
   to the whole test.  `step_fuel_pad` is what needs it: a padded line
   and a shifted offset are the same descent, and a key opened by one
   has to be the key opened by the other. *)
Lemma key_point_ws_prefix :
  forall p l, is_blank p = true -> key_point (p ++ l) = key_point l.
Proof.
  intros p l Hp. unfold key_point.
  rewrite (drop_leading_ws_ws_prefix p l Hp). reflexivity.
Qed.

(* A label is never blank: the split rule asks the byte before the colon
   not to be whitespace, so the accumulator is headed by that byte.  The
   invariant is what the recursion has to carry, since the character is
   `prev` at the split and the head of the accumulator one step later. *)
Lemma key_scan_label_nonblank :
  forall s acc prev st r v,
    (forall c, prev = Some c -> is_ws c = false -> is_blank acc = false) ->
    key_scan s acc prev st = Some (r, v) -> nonblank r = true.
Proof.
  induction s as [|c rest IH]; intros acc prev st r v Hinv H; [discriminate|].
  cbn [key_scan] in H.
  destruct (Ascii.eqb c ":"%char && key_before prev && key_after rest
            && iscan_settled c st)%bool eqn:E; [|apply (IH (String c acc) (Some c)
      (istep c st) r v); [|exact H];
      intros c0 Hc0 Hws; injection Hc0 as <-;
      rewrite is_blank_cons, Hws; reflexivity].
  injection H as <- _.
  apply andb_true_iff in E as [E _]. apply andb_true_iff in E as [E _].
  apply andb_true_iff in E as [_ E].
  unfold key_before in E. destruct prev as [c0|]; [|discriminate].
  apply negb_true_iff in E.
  unfold nonblank. rewrite rev_blank, (Hinv c0 eq_refl E). reflexivity.
Qed.

Lemma key_point_label_nonblank :
  forall l lbl v, key_point l = Some (lbl, v) -> nonblank lbl = true.
Proof.
  intros l lbl v H. unfold key_point in H.
  refine (key_scan_label_nonblank _ _ _ _ _ _ _ H).
  intros c Hc. discriminate Hc.
Qed.

Lemma key_split_label_nonblank :
  forall l lbl v, key_split l = Some (lbl, v) -> nonblank lbl = true.
Proof.
  intros l lbl v H. unfold key_split in H.
  destruct (key_point l) as [[lbl0 v0]|] eqn:E; [|discriminate].
  destruct (key_label_ok lbl0); [|discriminate]. injection H as <- <-.
  exact (key_point_label_nonblank _ _ _ E).
Qed.

(* The state carried by [key_scan] is exactly the scan of the reversed
   accumulator it returns as the label.  This is the bridge between the
   test performed during the one-pass search and a statement about the
   returned label itself. *)
Lemma key_scan_label_settled :
  forall s acc prev st lbl v,
    st = iscan_str (rev_string acc) istart ->
    key_scan s acc prev st = Some (lbl, v) ->
    iscan_settled ":"%char (iscan_str lbl istart) = true.
Proof.
  induction s as [|c rest IH]; intros acc prev st lbl v Hst Hsplit.
  - discriminate.
  - cbn [key_scan] in Hsplit.
    destruct (Ascii.eqb c ":"%char && key_before prev && key_after rest
              && iscan_settled c st)%bool eqn:E.
    + apply andb_true_iff in E as [E Hsettled].
      apply andb_true_iff in E as [E _].
      apply andb_true_iff in E as [Ec _].
      apply Ascii.eqb_eq in Ec. subst c.
      injection Hsplit as <- _.
      rewrite <- Hst. exact Hsettled.
    + apply (IH (String c acc) (Some c) (istep c st) lbl v).
      * subst st. rewrite rev_string_cons, iscan_str_app.
        cbn [one iscan_str]. reflexivity.
      * exact Hsplit.
Qed.

Lemma key_point_label_settled :
  forall l lbl v,
    key_point l = Some (lbl, v) ->
    iscan_settled ":"%char (iscan_str lbl istart) = true.
Proof.
  intros l lbl v H. unfold key_point in H.
  eapply key_scan_label_settled; [reflexivity|exact H].
Qed.

Lemma key_split_label_settled :
  forall l lbl v,
    key_split l = Some (lbl, v) ->
    iscan_settled ":"%char (iscan_str lbl istart) = true.
Proof.
  intros l lbl v H. unfold key_split in H.
  destruct (key_point l) as [[lbl0 v0]|] eqn:E; [|discriminate].
  destruct (key_label_ok lbl0); [|discriminate].
  injection H as <- <-. eapply key_point_label_settled; exact E.
Qed.

Lemma key_split_label_one :
  forall l lbl v,
    key_split l = Some (lbl, v) ->
    exists x, para_inlines [lbl] = [x].
Proof.
  intros l lbl v H. unfold key_split in H.
  destruct (key_point l) as [[lbl0 v0]|] eqn:E; [|discriminate].
  destruct (key_label_ok lbl0) eqn:Hok; [|discriminate].
  injection H as <- <-. unfold key_label_ok in Hok.
  destruct (para_inlines [lbl0]) as [|x xs] eqn:Hils; [discriminate|].
  destruct xs as [|y ys]; [exists x; reflexivity|discriminate].
Qed.

(** A successful key split has one nonblank resolved label, and the scan
    of that label is settled with the connective colon known as the next
    byte.  Thus the block layer consumes only split points for which the
    inline layer has no open or undecided construct. *)
Theorem key_split_contract :
  forall l lbl v,
    key_split l = Some (lbl, v) ->
    nonblank lbl = true /\
    (exists x, para_inlines [lbl] = [x]) /\
    iscan_settled ":"%char (iscan_str lbl istart) = true.
Proof.
  intros l lbl v H. split.
  - exact (key_split_label_nonblank _ _ _ H).
  - split.
    + exact (key_split_label_one _ _ _ H).
    + exact (key_split_label_settled _ _ _ H).
Qed.

(* The same fact in the form the block layer wants: `open_kind` hands
   the arm the line already normalized. *)
Lemma key_point_drop_leading_ws :
  forall l, key_point (drop_leading_ws l) = key_point l.
Proof.
  intros l. unfold key_point. rewrite drop_leading_ws_idem. reflexivity.
Qed.

Lemma key_split_drop_leading_ws :
  forall l, key_split (drop_leading_ws l) = key_split l.
Proof.
  intros l. unfold key_split. rewrite key_point_drop_leading_ws. reflexivity.
Qed.

Lemma key_split_ws_prefix :
  forall p l, is_blank p = true -> key_split (p ++ l) = key_split l.
Proof.
  intros p l Hp. unfold key_split. rewrite (key_point_ws_prefix p l Hp).
  reflexivity.
Qed.

(* The canonical view's paragraph, laid out the same way. *)
Fixpoint ci_para (lss : list (list cinline)) : inlines :=
  match lss with
  | [] => []
  | [cis] => ci_inlines cis
  | cis :: rest => (ci_inlines cis ++ mk SoftBreak :: ci_para rest)%list
  end.

Lemma ci_para_one : forall cis, ci_para [cis] = ci_inlines cis.
Proof. reflexivity. Qed.

Lemma ci_para_cons2 :
  forall cis cis2 rest,
    ci_para (cis :: cis2 :: rest)
    = (ci_inlines cis ++ mk SoftBreak :: ci_para (cis2 :: rest))%list.
Proof. reflexivity. Qed.

(*
The pass inverts the view
=========================
*)

(** Parsing a canonical line's text gives back its inlines.  Nothing is
    asked of the list but `cis_ok`: the empty line is the empty scan, which
    is what lets a table cell be empty. *)
Lemma parse_inline_line_ci :
  forall cis, cis_ok cis = true ->
  parse_inline_line (ci_line cis) = ci_inlines cis.
Proof.
  intros cis Hok.
  unfold parse_inline_line, istart, ostart, ci_line.
  change (@nil oitem) with (List.map OIn (@nil (node inline))).
  rewrite (iscan_cis cis None EmptyString []).
  - reflexivity.
  - exact Hok.
  - reflexivity.
Qed.

(** The same, a paragraph at a time.  The last hypothesis is `para_ok`'s
    trailing-whitespace conjunct: `para_inlines` strips the final line,
    so the two agree exactly when there is nothing to strip. *)
Lemma para_inlines_ci_para :
  forall lss,
    forallb cis_ok lss = true ->
    forallb nonempty lss = true ->
    strip_trailing_ws (last (map ci_line lss) EmptyString)
      = last (map ci_line lss) EmptyString ->
    para_inlines (map ci_line lss) = ci_para lss.
Proof.
  induction lss as [|cis rest IH]; intros Hok Hne Hlast; [reflexivity|].
  cbn [forallb] in Hok, Hne.
  apply andb_true_iff in Hok as [Hc Hr].
  apply andb_true_iff in Hne as [Hn Hnr].
  destruct rest as [|cis2 rest'].
  - cbn [map last] in Hlast |- *.
    rewrite para_inlines_one, Hlast.
    change (parse_inline_line (ci_line cis) = ci_para [cis]).
    rewrite ci_para_one. apply parse_inline_line_ci; assumption.
  - cbn [map] in *.
    rewrite para_inlines_cons2_closed
      by (unfold ci_line, istart, ostart;
          change (@nil oitem) with (List.map OIn (@nil (node inline)));
          apply iscan_cis_closed, Hc).
    rewrite ci_para_cons2, (parse_inline_line_ci cis Hc).
    f_equal. f_equal.
    apply IH; [exact Hr | exact Hnr |].
    rewrite last_cons_nonnil in Hlast by discriminate. exact Hlast.
Qed.

(*
The renderer
============
*)

Fixpoint inline_text (il : inline) : string :=
  let go :=
    fix go (ns : inlines) : string :=
      match ns with
      | [] => EmptyString
      | Node _ _ x :: rest => (inline_text x ++ go rest)%string
      end in
  let marked (k : dstyle) (ns : inlines) :=
    (marked_open k ++ (go ns ++ marked_close k EmptyString))%string in
  match il with
  | Str s => escape_str s
  | Verbatim s => verb_text s
  | Emph ns => marked DEmph ns
  | Strong ns => marked DStrong ns
  | Superscript ns => marked DSuper ns
  | Subscript ns => marked DSub ns
  | Highlight ns => marked DMark ns
  | Insert ns => marked DInsert ns
  | Delete ns => marked DDelete ns
  | Quoted SingleQuotes ns => marked DSQuote ns
  | Quoted DoubleQuotes ns => marked DDQuote ns
  | Link ns (Direct dst) =>
      (bracket_open false ++ (go ns ++ link_close dst EmptyString))%string
  | Image ns (Direct dst) =>
      (bracket_open true ++ (go ns ++ link_close dst EmptyString))%string
  | Link ns (Reference label) =>
      (bracket_open false ++ (go ns ++ ref_close label EmptyString))%string
  | Image ns (Reference label) =>
      (bracket_open true ++ (go ns ++ ref_close label EmptyString))%string
  | FootnoteReference label => note_text label
  (* both kinds render as their own region: which one it is was computed
     from that region and is recovered by computing it again *)
  | UrlLink s | EmailLink s => auto_text s
  (* raw content is its verbatim plus the spec that named its format *)
  | RawInline fmt s => raw_text fmt s
  | _ => EmptyString
  end.

Lemma inline_text_ci_ast : forall ci, inline_text (node_contents (ci_ast ci)) = ci_src ci.
Proof.
  fix IH 1. intro ci.
  destruct ci as [s|s|k kids|img kids dst|rimg rkids rlabel|label|a|rf rv];
    [reflexivity|reflexivity| | | |reflexivity
    |cbn [ci_ast ci_src]; unfold auto_node;
     destruct (auto_email a); reflexivity
    |cbn [ci_ast ci_src node_contents mk inline_text]; reflexivity].
  - destruct k; cbn [ci_ast ci_src dnode node_contents inline_text].
    all: cbn [inline_text node_contents mk]; f_equal; f_equal; f_equal;
      induction kids as [|c rest IHkids]; [reflexivity|]; cbn;
      destruct (ci_ast c) as [p a x] eqn:E;
      pose proof (IH c) as Hc; rewrite E in Hc;
      cbn [node_contents] in Hc; rewrite Hc, IHkids; reflexivity.
  - cbn [ci_ast ci_src node_contents inline_text mk bnode].
    destruct img;
      (cbn [bnode inline_text]; f_equal; f_equal;
       induction kids as [|c rest IHkids]; [reflexivity|]; cbn;
       destruct (ci_ast c) as [p a x] eqn:E;
       pose proof (IH c) as Hc; rewrite E in Hc;
       cbn [node_contents] in Hc; rewrite Hc, IHkids; reflexivity).
  - cbn [ci_ast ci_src node_contents inline_text mk bnode].
    destruct rimg;
      (cbn [bnode inline_text]; f_equal; f_equal;
       induction rkids as [|c rest IHkids]; [reflexivity|]; cbn;
       destruct (ci_ast c) as [p a x] eqn:E;
       pose proof (IH c) as Hc; rewrite E in Hc;
       cbn [node_contents] in Hc; rewrite Hc, IHkids; reflexivity).
Qed.

(* Recover the lines of a paragraph from its inlines: `Str` extends the
   current line, `SoftBreak` ends it. *)
Fixpoint inline_lines (ils : inlines) (cur : string) : list string :=
  match ils with
  | [] => [cur]
  | Node _ _ SoftBreak :: rest => cur :: inline_lines rest EmptyString
  | Node _ _ il :: rest => inline_lines rest (cur ++ inline_text il)
  end.

Lemma inline_lines_softbreak :
  forall rest cur,
    inline_lines (mk SoftBreak :: rest) cur = cur :: inline_lines rest EmptyString.
Proof. reflexivity. Qed.

Lemma inline_lines_ci_ast :
  forall ci rest cur,
    inline_lines (ci_ast ci :: rest) cur
    = inline_lines rest (cur ++ ci_src ci).
Proof.
  intros ci rest cur.
  destruct ci as [s|s|k kids|img kids dst|rimg rkids rlabel|label|a|rf rv];
    [reflexivity|reflexivity| | | |reflexivity
    |cbn [ci_ast ci_src]; unfold auto_node;
     destruct (auto_email a); reflexivity
    |cbn [ci_ast ci_src node_contents mk inline_text]; reflexivity].
  - rewrite ci_ast_delim, <- inline_text_ci_ast.
    destruct k; reflexivity.
  - rewrite ci_ast_link, <- inline_text_ci_ast, ci_ast_link.
    destruct img; reflexivity.
  - rewrite ci_ast_ref, <- inline_text_ci_ast, ci_ast_ref.
    destruct rimg; reflexivity.
Qed.

(** Rendering a canonical line's inlines appends its text and consumes
    nothing else, which is what makes the paragraph case an induction. *)
Lemma inline_lines_ci_inlines :
  forall cis cur rest,
    inline_lines (ci_inlines cis ++ rest)%list cur
    = inline_lines rest (cur ++ ci_line cis).
Proof.
  intros cis cur rest.
  induction cis as [|c cs IH] in cur |- *.
  - cbn [ci_inlines ci_line ci_text app inline_lines].
    rewrite append_empty_r. reflexivity.
  - cbn [ci_inlines map app]. rewrite inline_lines_ci_ast, IH.
    cbn [ci_line ci_text]. rewrite append_assoc. reflexivity.
Qed.

Lemma inline_lines_ci_para :
  forall rest cis cur,
    forallb cis_ok (cis :: rest) = true ->
    forallb nonempty (cis :: rest) = true ->
    inline_lines (ci_para (cis :: rest)) cur
    = (cur ++ ci_line cis) :: map ci_line rest.
Proof.
  induction rest as [|cis2 rest' IH]; intros cis cur Hok Hne;
    cbn [forallb] in Hok, Hne;
    apply andb_true_iff in Hok as [Hc Hr];
    apply andb_true_iff in Hne as [Hn Hnr].
  - rewrite ci_para_one. cbn [map].
    rewrite <- (app_nil_r (ci_inlines cis)).
    rewrite inline_lines_ci_inlines.
    reflexivity.
  - rewrite ci_para_cons2.
    rewrite inline_lines_ci_inlines.
    rewrite inline_lines_softbreak.
    rewrite IH by assumption.
    reflexivity.
Qed.

(** The renderer emits exactly the canonical lines. *)
Corollary inline_lines_ci :
  forall lss,
    forallb cis_ok lss = true -> forallb nonempty lss = true ->
    nonempty lss = true ->
    inline_lines (ci_para lss) EmptyString = map ci_line lss.
Proof.
  intros [|cis rest] Hok Hne Hlss; [discriminate|].
  rewrite inline_lines_ci_para by assumption. reflexivity.
Qed.

(*
Escapes, pinned
===============
*)

(* The scanner accepts any punctuation after a backslash... *)
End WithTable.

(*
Djot's instance
---------------

The table in force for everything downstream: the harness, the corpus,
and the examples below.  A second one lives in `dev/check/Markdown.v`, which
names it explicitly rather than putting it in scope -- two instances of
one class in one scope is how the wrong table gets inferred.
*)

#[export] Instance djot_table : dtable :=
  DTable djot_config eq_refl.

(* The Markdown-like table, as an instance but deliberately *not* an
   `Instance`: it is named where it is wanted (`dev/check/Markdown.v`) so
   that inference in this development always means djot's. *)
Definition markdown_table : dtable :=
  DTable markdown_config eq_refl.

(* The narrower profile keeps Markdown spelling and switches off every
   djot-only delimiter container. *)
Definition markdown_like_table : dtable :=
  DTable markdown_like_config eq_refl.

Example escaped_punct_literal : parse_inline_line "\*" = [mk (Str "*")].
Proof. reflexivity. Qed.

(* ...and leaves a backslash before anything else alone. *)
Example escaped_nonpunct_literal : parse_inline_line "\a" = [mk (Str "\a")].
Proof. reflexivity. Qed.

(* Whitespace is the exception to that: a space becomes a non-breaking
   one, and the end of the line becomes a hard break. *)
Example escaped_space_is_nbsp :
  parse_inline_line "a\ b"
  = [mk (Str "a"); mk NonBreakingSpace; mk (Str "b")].
Proof. vm_compute. reflexivity. Qed.

(* Only the first byte of the run is claimed; the rest is text. *)
Example escaped_space_claims_one :
  parse_inline_line "a\  b"
  = [mk (Str "a"); mk NonBreakingSpace; mk (Str " b")].
Proof. vm_compute. reflexivity. Qed.

(* A tab is not a space, so djot.js leaves the backslash literal. *)
Example escaped_tab_is_literal :
  parse_inline_line (String "\"%char (String "009"%char "b"))
  = [mk (Str (String "\"%char (String "009"%char "b")))].
Proof. vm_compute. reflexivity. Qed.

Example escaped_eol_is_hard_break :
  parse_inline_line "para\" = [mk (Str "para"); mk HardBreak].
Proof. vm_compute. reflexivity. Qed.

(* The hard break replaces the soft one, and the whitespace on either
   side of the backslash goes with it. *)
Example escaped_eol_replaces_soft_break :
  para_inlines ["ab \  "; "c"]
  = [mk (Str "ab"); mk HardBreak; mk (Str "c")].
Proof. vm_compute. reflexivity. Qed.

(* A backtick in a `Str` is escaped, so it does not open a verbatim... *)
Example escaped_tick_literal : parse_inline_line "\`a\`" = [mk (Str "`a`")].
Proof. reflexivity. Qed.

(* ...while a bare one does, and a run of the wrong width is content. *)
Example verbatim_basic : parse_inline_line "`a`" = [mk (Verbatim "a")].
Proof. reflexivity. Qed.

Example verbatim_wrong_width_is_content :
  parse_inline_line "` `` `" = [mk (Verbatim "``")].
Proof. reflexivity. Qed.

Example verbatim_unclosed_closes_at_eol :
  parse_inline_line "`a" = [mk (Verbatim "a")].
Proof. reflexivity. Qed.

(* The encoder emits only what `needs_escape` names, which is why a
   comma renders bare where a backslash does not.  Matching djot.js,
   which renders `\,` back as `,`. *)
Example escape_backslash : escape_str "a\b" = "a\\b".
Proof. reflexivity. Qed.

Example escape_leaves_punct : escape_str "a,b" = "a,b".
Proof. reflexivity. Qed.

(* ...but a delimiter the table claims is escaped, like the backtick. *)
Example escape_delims : escape_str "a*b_c{d}" = "a\*b\_c\{d\}".
Proof. reflexivity. Qed.

(*
Canonical verbatim, pinned
==========================
*)

Example verb_ticks_examples :
  (verb_ticks "a", verb_ticks "`", verb_ticks "``", verb_ticks "` ``")
  = (1, 2, 1, 3).
Proof. vm_compute. reflexivity. Qed.

Example verbatim_render_tick : ci_line [CIVerb "`"] = "`` ` ``".
Proof. vm_compute. reflexivity. Qed.

Example verbatim_mixed_roundtrip :
  parse_inline_line (ci_line [CIStr "a"; CIVerb "`"; CIStr "*"])
  = ci_inlines [CIStr "a"; CIVerb "`"; CIStr "*"].
Proof. vm_compute. reflexivity. Qed.

(* The byte after a delayed closer is dispatched normally: here it is
   the backslash that protects a literal backtick. *)
Example verbatim_then_escaped_tick :
  parse_inline_line (ci_line [CIVerb "v"; CIStr "`"])
  = ci_inlines [CIVerb "v"; CIStr "`"].
Proof. vm_compute. reflexivity. Qed.

(* The empty verbatim is outside the view: its two runs are separated by
   nothing, so only the end of the paragraph closes it. *)
Example empty_verbatim_not_canonical : ci_ok (CIVerb EmptyString) = false.
Proof. reflexivity. Qed.

(*
Spans cross a line break
========================
*)

(* A verbatim opened on one line closes on the next, with the break as
   content -- matching djot.js, which scans the newline as an ordinary
   character.  It was two spans and a stray empty one before the scan was
   threaded through the paragraph. *)
Example verbatim_crosses_break :
  para_inlines ["`a"; "b`"] = [mk (Verbatim "a
b")].
Proof. vm_compute. reflexivity. Qed.

(* And the ordinary case still splits at the break. *)
Example text_breaks_at_line_end :
  para_inlines ["a"; "b"] = [mk (Str "a"); mk SoftBreak; mk (Str "b")].
Proof. vm_compute. reflexivity. Qed.

(* The block-attribute recovery, which is what `para_inlines_off` is for.
   With attributes on, a `{%` on the first line opens a comment that the
   `%}` closes, and the spec attaches to nothing and is dropped, so the
   whole paragraph vanishes.  With the first line off, nothing opens. *)
Example para_off_comment_spans_paragraph :
  para_inlines ["{%"; "c"; "%}"] = [].
Proof. vm_compute. reflexivity. Qed.

Example para_off_one_frozen_line :
  para_inlines_off 1 ["{%"; "c"; "%}"]
  = [mk (Str "{%"); mk SoftBreak; mk (Str "c");
     mk SoftBreak; mk (Str "%}")].
Proof. vm_compute. reflexivity. Qed.

(* Two of them, which is what an indented continuation line gives. *)
Example para_off_two_frozen_lines :
  para_inlines_off 2 ["{%"; "c"; "%}"]
  = [mk (Str "{%"); mk SoftBreak; mk (Str "c");
     mk SoftBreak; mk (Str "%}")].
Proof. vm_compute. reflexivity. Qed.

(* An id spec is the same story with a different machine state. *)
Example para_off_id_spec :
  para_inlines_off 1 ["{#i"; "%}"]
  = [mk (Str "{#i"); mk SoftBreak; mk (Str "%}")].
Proof. vm_compute. reflexivity. Qed.

(* A delimiter span crosses one too. *)
Example emph_crosses_break :
  para_inlines ["_a"; "b_"]
  = [mk (Emph [mk (Str "a"); mk SoftBreak; mk (Str "b")])].
Proof. vm_compute. reflexivity. Qed.

(*
The delimiter family, pinned
============================

Every one of these was checked against djot.js before it was written.
*)

Example canonical_emph_source :
  ci_line [CIDelim DEmph [CIStr "a"]] = "{_a_}".
Proof. reflexivity. Qed.

Example canonical_nested_delimiter_roundtrip :
  parse_inline_line
    (ci_line [CIDelim DEmph
      [CIStr "a"; CIDelim DStrong [CIStr "b"]]])
  = ci_inlines [CIDelim DEmph
      [CIStr "a"; CIDelim DStrong [CIStr "b"]]].
Proof. vm_compute. reflexivity. Qed.

(* Bare and braced spell the same span... *)
Example emph_bare : parse_inline_line "_a_" = [mk (Emph [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example emph_braced : parse_inline_line "{_a_}" = [mk (Emph [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

(* ...but the marking is part of the key, so a braced opener is not
   closed by a bare delimiter, and the whole thing decays to text. *)
Example emph_marked_needs_marked_closer :
  parse_inline_line "{_a_" = [mk (Str "{_a_")].
Proof. vm_compute. reflexivity. Qed.

(* `can_open` is a nonspace to the right, `can_close` a nonspace to the
   left, so a delimiter against a space is literal. *)
Example emph_open_needs_nonspace :
  parse_inline_line "_ a_" = [mk (Str "_ a_")].
Proof. vm_compute. reflexivity. Qed.

(* ...and the brace overrides both, which is the point of the marker. *)
Example braced_keeps_the_space :
  parse_inline_line "{_ a_}" = [mk (Emph [mk (Str " a")])].
Proof. vm_compute. reflexivity. Qed.

(* Doubling is nesting, not a second construct.  This is the fact that
   makes `__` for strong a *different table*, not an extension of this
   one (`.project/260811.inline-parser.md` §0.1). *)
Example doubled_is_nested :
  parse_inline_line "__a__" = [mk (Emph [mk (Emph [mk (Str "a")])])].
Proof. vm_compute. reflexivity. Qed.

(* An opener the closer spans is abandoned: its source becomes text, and
   its content splices into the scope that closed.  This is the stack's
   half of djot.js's `clearOpeners`. *)
Example abandoned_opener_becomes_text :
  parse_inline_line "_a*b_" = [mk (Emph [mk (Str "a*b")])].
Proof. vm_compute. reflexivity. Qed.

(* An opener that never closes decays the same way, merging with the text
   on both sides so no two `Str` nodes end up adjacent. *)
Example unclosed_opener_merges :
  parse_inline_line "a*b" = [mk (Str "a*b")].
Proof. vm_compute. reflexivity. Qed.

(* The three rows that only exist braced: a bare `=`, `+` or `-` is
   text.  The hyphen is the one that has to be braced for a reason
   beyond frequency -- an unbraced `-` is where smart dashes live. *)
Example mark_needs_braces :
  (parse_inline_line "=a=", parse_inline_line "{=a=}")
  = ([mk (Str "=a=")], [mk (Highlight [mk (Str "a")])]).
Proof. vm_compute. reflexivity. Qed.

Example delete_needs_braces :
  (parse_inline_line "-a-", parse_inline_line "{-a-}")
  = ([mk (Str "-a-")], [mk (Delete [mk (Str "a")])]).
Proof. vm_compute. reflexivity. Qed.

(* Its content is scanned like any other row's, and the braces belong to
   the delimiter rather than to the text. *)
Example delete_nests :
  parse_inline_line "{-a _b_-}"
  = [mk (Delete [mk (Str "a "); mk (Emph [mk (Str "b")])])].
Proof. vm_compute. reflexivity. Qed.

(* And the row round-trips through the canonical view like the others.
   `-` is now a delimiter character, so a canonical `Str` holding one
   spells it escaped -- which is what keeps `{-a-}` from reappearing out
   of text that only looked like it. *)
Example delete_ci_roundtrip :
  (ci_src (CIDelim DDelete [CIStr "a"]),
   parse_inline_line (ci_src (CIDelim DDelete [CIStr "a"])))
  = ("{-a-}", [ci_ast (CIDelim DDelete [CIStr "a"])]).
Proof. vm_compute. reflexivity. Qed.

Example hyphen_in_str_is_escaped :
  (ci_src (CIStr "a-b"), parse_inline_line (ci_src (CIStr "a-b")))
  = ("a\-b", [mk (Str "a-b")]).
Proof. vm_compute. reflexivity. Qed.

(* An empty span is not a span: djot.js excludes a closer that sits
   immediately after its opener. *)
Example empty_span_is_text :
  parse_inline_line "{__}" = [mk (Str "{__}")].
Proof. vm_compute. reflexivity. Qed.

(* Smart punctuation on the two characters that are not delimiters.
   Three periods are one ellipsis and a fourth is itself; a run of
   hyphens is cut by `dashes`; and both are text, so they merge with the
   text around them rather than becoming nodes. *)
Example ellipsis_and_remainder :
  (parse_inline_line "a...b", parse_inline_line "a....b")
  = ([mk (Str ("a" ++ ellipsis ++ "b"))],
     [mk (Str ("a" ++ ellipsis ++ ".b"))]).
Proof. vm_compute. reflexivity. Qed.

Example two_periods_are_text :
  parse_inline_line "a..b" = [mk (Str "a..b")].
Proof. vm_compute. reflexivity. Qed.

Example dash_runs :
  (parse_inline_line "a-b", parse_inline_line "a--b", parse_inline_line "a---b")
  = ([mk (Str "a-b")],
     [mk (Str ("a" ++ endash ++ "b"))],
     [mk (Str ("a" ++ emdash ++ "b"))]).
Proof. vm_compute. reflexivity. Qed.

(* Where the run meets the delete row, which is the one place the two
   rules interact: the closer takes the last hyphen back and the rest of
   the run is cut. *)
Example dash_run_gives_back_its_closer :
  parse_inline_line "{-a---}"
  = [mk (Delete [mk (Str ("a" ++ endash))])].
Proof. vm_compute. reflexivity. Qed.

(* With nothing open, `-}` is what is left over, exactly as djot.js
   emits it: two literal characters, and the run before them cut. *)
Example dash_run_without_an_opener :
  parse_inline_line "a---}" = [mk (Str ("a" ++ endash ++ "-}"))].
Proof. vm_compute. reflexivity. Qed.

(* Escaping is what keeps canonical text out of both rules. *)
Example escaped_runs_are_literal :
  (parse_inline_line (escape_str "a---b"), parse_inline_line (escape_str "a...b"))
  = ([mk (Str "a---b")], [mk (Str "a...b")]).
Proof. vm_compute. reflexivity. Qed.

(* Verbatim is a mode, not a row: while one is open the table is
   suppressed entirely. *)
Example verbatim_suppresses_delimiters :
  parse_inline_line "`_a_`" = [mk (Verbatim "_a_")].
Proof. vm_compute. reflexivity. Qed.

(*
Math
----

`$` and `$$` before a backtick run make the span math instead of
verbatim -- djot.js's `verbatimType`, decided retroactively there and at
the opening run here.  Every reading below was taken from the oracle.
*)

Example math_inline :
  parse_inline_line "$`x`" = [mk (Math InlineMath "x")].
Proof. vm_compute. reflexivity. Qed.

Example math_display :
  parse_inline_line "$$`x`" = [mk (Math DisplayMath "x")].
Proof. vm_compute. reflexivity. Qed.

(* An unclosed run still closes at the end of the line, and it is still
   math. *)
Example math_unclosed :
  parse_inline_line "$`x" = [mk (Math InlineMath "x")].
Proof. vm_compute. reflexivity. Qed.

(* A third dollar is text: djot.js pops exactly two matches, so the
   prefix is the last two and the extra one is flushed. *)
Example math_three_dollars :
  parse_inline_line "$$$`x`" = [mk (Str "$"); mk (Math DisplayMath "x")].
Proof. vm_compute. reflexivity. Qed.

(* The prefix has to be adjacent, and an escaped dollar is not a prefix
   at all -- which is why `IDollar` is a state rather than a look back
   into the text buffer, where the two would be indistinguishable. *)
Example math_needs_adjacency :
  parse_inline_line "$ `x`" = [mk (Str "$ "); mk (Verbatim "x")].
Proof. vm_compute. reflexivity. Qed.

Example math_escaped_dollar_is_verbatim :
  parse_inline_line "\$`x`" = [mk (Str "$"); mk (Verbatim "x")].
Proof. vm_compute. reflexivity. Qed.

(* Inside a run the dollar is content, as every other character is. *)
Example math_dollar_inside_verbatim :
  parse_inline_line "`$x`" = [mk (Verbatim "$x")].
Proof. vm_compute. reflexivity. Qed.

(* A dollar with no run after it is text, and canonical text escapes it,
   since `dreserved` claims it. *)
Example math_lone_dollar : parse_inline_line "$" = [mk (Str "$")].
Proof. vm_compute. reflexivity. Qed.

Example math_dollar_escapes : ci_line [CIStr "a$b"] = "a\$b".
Proof. vm_compute. reflexivity. Qed.

(*
Smart quotes
------------

Two more table rows, and every reading below was taken from djot.js
first.  What the rows needed beyond a character and a width is the
*decay*: an unmatched quote is a curly character rather than its own
source, and the markers choose the side.
*)

Example squote_pair :
  parse_inline_line "'a'" = [mk (Quoted SingleQuotes [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example dquote_pair :
  parse_inline_line """a""" = [mk (Quoted DoubleQuotes [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

(* An apostrophe cannot open, so it decays -- this is `DBareAfterBreak`,
   djot's `opentest` for the single quote, and the reason the row needed
   a third syntax value rather than a fourth field. *)
Example apostrophe_is_not_an_opener :
  parse_inline_line "can't" = [mk (Str ("can" ++ rsquo ++ "t"))].
Proof. vm_compute. reflexivity. Qed.

Example decade_is_an_apostrophe :
  parse_inline_line "the '70s" = [mk (Str ("the " ++ rsquo ++ "70s"))].
Proof. vm_compute. reflexivity. Qed.

(* An unmatched opener decays too: to the *right* form for the single
   quote and the *left* for the double one.  The side is a property of
   the row, not of the position. *)
Example unmatched_squote_is_right :
  parse_inline_line "'a" = [mk (Str (rsquo ++ "a"))].
Proof. vm_compute. reflexivity. Qed.

Example unmatched_dquote_is_left :
  parse_inline_line "a""" = [mk (Str ("a" ++ ldquo))].
Proof. vm_compute. reflexivity. Qed.

(* And the byte a decay leaves in the buffer is not the byte the next
   quote's open rule reads.  A quote that decays writes `rsquo`; the
   source said `'`, and `dopens_after` accepts a quote and not a curly
   one, so the second `'` here opens and the third closes it.  `ilead`
   takes the source byte from `prev` for exactly this. *)
Example decay_does_not_hide_the_source_byte :
  parse_inline_line "a''b'"
  = [mk (Str ("a" ++ rsquo)); mk (Quoted SingleQuotes [mk (Str "b")])].
Proof. vm_compute. reflexivity. Qed.

(* The dashes rewrite the buffer the same way, and cost the same. *)
Example dash_does_not_hide_the_source_byte :
  parse_inline_line "a--'b'"
  = [mk (Str ("a" ++ endash)); mk (Quoted SingleQuotes [mk (Str "b")])].
Proof. vm_compute. reflexivity. Qed.

(* A marker overrides both the open rule and the side: a braced opener
   opens where an apostrophe would otherwise be meant, and an abandoned
   one decays to the left form. *)
Example marked_squote_opens :
  parse_inline_line "{'a'}" = [mk (Quoted SingleQuotes [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example marked_squote_abandoned_is_left :
  parse_inline_line "{'a" = [mk (Str (lsquo ++ "a"))].
Proof. vm_compute. reflexivity. Qed.

(* Both markers at once, which is the one token whose two flips compete.
   The row's own default decides: the single quote defaults right, so the
   open marker is the flip that applies and the `}` changes nothing,
   while the double quote defaults left and the close marker wins.  The
   `}` is not consumed either way -- upstream moves `endcloser` past it
   only when there is no open marker -- so the token still opens a scope
   and the brace is text after it. *)
Example marked_squote_with_close_marker_is_left :
  parse_inline_line "{'}a" = [mk (Str (lsquo ++ "}a"))].
Proof. vm_compute. reflexivity. Qed.

Example marked_dquote_with_close_marker_is_right :
  parse_inline_line "{""}a" = [mk (Str (rdquo ++ "}a"))].
Proof. vm_compute. reflexivity. Qed.

(* And it is still an opener, so a closer later in the line reaches it
   and the decay is never asked for. *)
Example marked_dquote_with_close_marker_still_opens :
  parse_inline_line "{""}a""}"
  = [mk (Quoted DoubleQuotes [mk (Str "}a")])].
Proof. vm_compute. reflexivity. Qed.

(* An ordinary row's decay is its source, and there the `}` is the one
   the token did not take: `{*}` is three characters of text, not four. *)
Example marked_strong_with_close_marker_keeps_one_brace :
  parse_inline_line "{*}" = [mk (Str "{*}")].
Proof. vm_compute. reflexivity. Qed.

(* And an escape still wins, which is what keeps a canonical `Str`
   containing a quote round-tripping: the rows joined `is_delim`, so
   `needs_escape` grew by two characters without being edited. *)
Example escaped_quotes_are_literal :
  parse_inline_line "\'a\'" = [mk (Str "'a'")].
Proof. vm_compute. reflexivity. Qed.

Example quotes_escape_in_canonical_text :
  ci_line [CIStr "it's a ""quote"""] = "it\'s a \""quote\""".
Proof. vm_compute. reflexivity. Qed.

Example canonical_squote_source :
  ci_line [CIDelim DSQuote [CIStr "a"]] = "{'a'}".
Proof. vm_compute. reflexivity. Qed.

Example canonical_squote_roundtrip :
  parse_inline_line (ci_line [CIDelim DSQuote [CIStr "a"]])
  = ci_inlines [CIDelim DSQuote [CIStr "a"]].
Proof. vm_compute. reflexivity. Qed.

(*
Direct links
------------

Every reading below was taken from djot.js first. *)

Definition bkids : inlines := [mk (Str "a")].

Example link_basic : parse_inline_line "[a](b)" = [mk (Link bkids (Direct "b"))].
Proof. vm_compute. reflexivity. Qed.

Example link_balanced_parens :
  parse_inline_line "[a](b(c)d)" = [mk (Link bkids (Direct "b(c)d"))].
Proof. vm_compute. reflexivity. Qed.

Example link_escaped_paren :
  parse_inline_line "[a](b\)c)" = [mk (Link bkids (Direct "b)c"))].
Proof. vm_compute. reflexivity. Qed.

(* Without a destination the brackets are text, and they merge with the
   text on both sides: `opop_str` takes back what the `[` had flushed. *)
Example bracket_literal_merges :
  parse_inline_line "z[a]x" = [mk (Str "z[a]x")].
Proof. vm_compute. reflexivity. Qed.

(* A label's non-text children stay classified when the brackets do not
   become a link, which is why the fallback cannot work from source. *)
Example bracket_literal_keeps_children :
  parse_inline_line "[_a_]x"
  = [mk (Str "["); mk (Emph [mk (Str "a")]); mk (Str "]x")].
Proof. vm_compute. reflexivity. Qed.

(* An unterminated destination is not literal source: upstream turns the
   region literal only at the balanced `)`, so a region that never gets
   one keeps what the ordinary scan made of it.  The `[` and the `](`
   come back out of the `FKDest` scope the state opened. *)
Example dest_unterminated_is_scanned :
  para_inlines ["[unclosed](hello *a"; "b*"]
  = [mk (Str "[unclosed](hello ");
     mk (Strong [mk (Str "a"); mk SoftBreak; mk (Str "b")])].
Proof. vm_compute. reflexivity. Qed.

(* The scope is a barrier as well as a container: `inline.ts:150` refuses
   a closer inside a destination an opener from before the `[`, which is
   what `fr_barrier` stops `oclose_go` for. *)
Example dest_bars_an_outer_opener :
  parse_inline_line "*x [u](a* b" = [mk (Str "*x [u](a* b")].
Proof. vm_compute. reflexivity. Qed.

(* ...and only that: a delimiter opened *inside* the region closes there,
   around a link that closed inside it. *)
Example dest_inner_matching_is_ordinary :
  parse_inline_line "[u](a *b* c"
  = [mk (Str "[u](a "); mk (Strong [mk (Str "b")]); mk (Str " c")].
Proof. vm_compute. reflexivity. Qed.

(* A delimiter opened inside a label is abandoned by the close, since the
   label is a scope and the delimiter did not close inside it. *)
Example link_label_abandons_opener :
  parse_inline_line "[_a](b)_"
  = [mk (Link [mk (Str "_a")] (Direct "b")); mk (Str "_")].
Proof. vm_compute. reflexivity. Qed.

(* ...but only a `]` that *closes* abandons anything.  One whose next
   byte makes no construct is text, and its opener is still on the stack
   for a later `]` to close -- so the label runs to the second one and
   the delimiter opened before the first still closes inside it. *)
Example rbrack_without_a_construct_keeps_the_opener :
  parse_inline_line "[u]b](c)" = [mk (Link [mk (Str "u]b")] (Direct "c"))].
Proof. vm_compute. reflexivity. Qed.

Example rbrack_without_a_construct_keeps_the_scope :
  parse_inline_line "[_u]b_](c)"
  = [mk (Link [mk (Emph [mk (Str "u]b")])] (Direct "c"))].
Proof. vm_compute. reflexivity. Qed.

(* A destination crosses a line break and drops it; an unterminated one
   keeps it, since the break is then an ordinary soft break.  A `]` at a
   break is already literal: the `(` has to be the very next byte. *)
Example dest_crosses_break :
  para_inlines ["[a](b"; "c)"] = [mk (Link bkids (Direct "bc"))].
Proof. vm_compute. reflexivity. Qed.

Example dest_unterminated_keeps_break :
  para_inlines ["[a](b"; "c"]
  = [mk (Str "[a](b"); mk SoftBreak; mk (Str "c")].
Proof. vm_compute. reflexivity. Qed.

Example bracket_needs_paren_on_the_same_line :
  para_inlines ["[a]"; "(b)"]
  = [mk (Str "[a]"); mk SoftBreak; mk (Str "(b)")].
Proof. vm_compute. reflexivity. Qed.

(* The canonical spelling, and what it excludes.  An empty label is
   canonical, which is the one place a link differs from a delimiter. *)
(* Images are the bracket family's second member, and the `!` is a
   lookbehind djot.js takes off the subject at the close; we cannot, so
   the scanner has a mode for it and the frame records the answer. *)
Example image_basic :
  parse_inline_line "![a](u)" = [mk (Image bkids (Direct "u"))].
Proof. vm_compute. reflexivity. Qed.

Example image_escaped_bang_is_a_link :
  parse_inline_line "\![a](u)" = [mk (Str "!"); mk (Link bkids (Direct "u"))].
Proof. vm_compute. reflexivity. Qed.

Example image_needs_the_bracket :
  parse_inline_line "!x" = [mk (Str "!x")].
Proof. vm_compute. reflexivity. Qed.

Example image_bang_before_image :
  parse_inline_line "!![a](u)"
  = [mk (Str "!"); mk (Image bkids (Direct "u"))].
Proof. vm_compute. reflexivity. Qed.

Example image_without_destination_is_text :
  parse_inline_line "![a]" = [mk (Str "![a]")].
Proof. vm_compute. reflexivity. Qed.

Example canonical_link_source :
  ci_line [CIStr "x"; CILink false [CIStr "a"] "b"; CIStr "y"] = "x[a](b)y".
Proof. vm_compute. reflexivity. Qed.

Example canonical_image_source :
  ci_line [CILink true [CIStr "a"] "u"] = "![a](u)".
Proof. vm_compute. reflexivity. Qed.

Example canonical_link_empty_label : ci_line [CILink false [] "u"] = "[](u)".
Proof. vm_compute. reflexivity. Qed.

Example reference_link_explicit :
  parse_inline_line "[foobar][1]" =
  [mk (Link [mk (Str "foobar")] (Reference "1"))].
Proof. vm_compute. reflexivity. Qed.

Example reference_link_collapsed :
  parse_inline_line "[link][]" =
  [mk (Link [mk (Str "link")] (Reference "link"))].
Proof. vm_compute. reflexivity. Qed.

Example reference_link_multiline_label :
  para_inlines ["[link][a and"; "b]"] =
  [mk (Link [mk (Str "link")] (Reference "a and b"))].
Proof. vm_compute. reflexivity. Qed.

Example reference_image :
  parse_inline_line "![alt][img]" =
  [mk (Image [mk (Str "alt")] (Reference "img"))].
Proof. vm_compute. reflexivity. Qed.

Example unclosed_reference_is_literal :
  parse_inline_line "[link][open" = [mk (Str "[link][open")].
Proof. vm_compute. reflexivity. Qed.

Example canonical_link_escapes_destination :
  ci_line [CILink false [CIDelim DEmph [CIStr "a"]] "u(v)\"]
  = "[{_a_}](u\(v\)\\)".
Proof. vm_compute. reflexivity. Qed.

Example canonical_link_roundtrip :
  parse_inline_line (ci_line [CILink false [CIDelim DEmph [CIStr "a"]] "u(v)\"])
  = ci_inlines [CILink false [CIDelim DEmph [CIStr "a"]] "u(v)\"].
Proof. vm_compute. reflexivity. Qed.

(* A `!` before a link is escaped, so both parsers read the rendering as
   a link rather than one of them reading an image. *)
Example bang_before_link_escaped :
  ci_line [CIStr "a!"; CILink false [CIStr "b"] "u"] = "a\![b](u)".
Proof. vm_compute. reflexivity. Qed.

Example bang_before_link_roundtrip :
  parse_inline_line (ci_line [CIStr "a!"; CILink false [CIStr "b"] "u"])
  = ci_inlines [CIStr "a!"; CILink false [CIStr "b"] "u"].
Proof. vm_compute. reflexivity. Qed.

(* Excluded: a destination that spans a line cannot come back. *)
Example link_destination_with_break_not_canonical :
  ci_ok (CILink false [CIStr "a"] "u
v") = false.
Proof. vm_compute. reflexivity. Qed.

(* The canonical reference spelling is the explicit one, and it survives
   a nested delimiter in the text exactly as a direct link does. *)
Example canonical_reference_source :
  ci_line [CIStr "x"; CIRef false [CIStr "a"] "lab"] = "x[a][lab]".
Proof. vm_compute. reflexivity. Qed.

Example canonical_reference_image_source :
  ci_line [CIRef true [CIStr "a"] "lab"] = "![a][lab]".
Proof. vm_compute. reflexivity. Qed.

Example canonical_reference_roundtrip :
  parse_inline_line (ci_line [CIRef false [CIDelim DEmph [CIStr "a"]] "lab"])
  = ci_inlines [CIRef false [CIDelim DEmph [CIStr "a"]] "lab"].
Proof. vm_compute. reflexivity. Qed.

(* Excluded, and each for its own reason: an empty label is the collapsed
   spelling, whose label comes from the text rather than the source; a
   `]` would end the label early; and a label the parser would normalize
   comes back as something else. *)
Example reference_empty_label_not_canonical :
  ci_ok (CIRef false [CIStr "a"] "") = false.
Proof. vm_compute. reflexivity. Qed.

Example reference_bracket_label_not_canonical :
  ci_ok (CIRef false [CIStr "a"] "a]b") = false.
Proof. vm_compute. reflexivity. Qed.

Example reference_unnormalized_label_not_canonical :
  ci_ok (CIRef false [CIStr "a"] "a  b") = false.
Proof. vm_compute. reflexivity. Qed.

(*
Spans
=====

`[...]` followed immediately by an attribute spec.  Each of these was
pinned against djot.js before the mode was written; they are the mode's
dispositions read back off the scanner.
*)

Example span_simple :
  parse_inline_line "[s]{.a}"
  = [Node NoPos [("class", "a")] (Span [mk (Str "s")])].
Proof. vm_compute. reflexivity. Qed.

(* An empty spec still builds the node, and so does an empty label --
   `wf_inline` exempts a span from `nonempty` for exactly this reason. *)
Example span_empty_spec :
  parse_inline_line "[s]{}" = [mk (Span [mk (Str "s")])].
Proof. vm_compute. reflexivity. Qed.

Example span_empty_label :
  parse_inline_line "[]{.a}" = [Node NoPos [("class", "a")] (Span [])].
Proof. vm_compute. reflexivity. Qed.

(* The brace must be adjacent: a space between it and the `]` leaves an
   ordinary bracket, and the spec then has nothing to attach to -- the
   pending text ends in whitespace -- so it is dropped. *)
Example span_needs_adjacent_brace :
  parse_inline_line "[s] {.a}" = [mk (Str "[s] ")].
Proof. vm_compute. reflexivity. Qed.

(* A failed spec puts the region back as text and resumes the scan at the
   byte that failed, so the `*` still opens a delimiter run. *)
Example span_failed_spec_resumes :
  parse_inline_line "[s]{bad*x*y"
  = [mk (Str "[s]{bad"); mk (Strong [mk (Str "x")]); mk (Str "y")].
Proof. vm_compute. reflexivity. Qed.

(* `!` is not part of a span: the image opener decays to text. *)
Example span_ignores_image_marker :
  parse_inline_line "![x]{.a}"
  = [mk (Str "!"); Node NoPos [("class", "a")] (Span [mk (Str "x")])].
Proof. vm_compute. reflexivity. Qed.

(* And it merges with the text before it rather than leaving two
   adjacent `Str` nodes, which `wf_inlines` forbids. *)
Example span_image_marker_merges :
  parse_inline_line "a![x]{.a}"
  = [mk (Str "a!"); Node NoPos [("class", "a")] (Span [mk (Str "x")])].
Proof. vm_compute. reflexivity. Qed.

(* A second spec belongs to the span too, and classes accumulate where
   other keys overwrite: `attr_merge` is the same rule the block layer
   uses.  There is no pending text when the second `{` arrives, so
   `oattach_list` finds the span node itself. *)
Example span_stacked_specs :
  parse_inline_line "[s]{.a}{.b}"
  = [Node NoPos [("class", "a b")] (Span [mk (Str "s")])].
Proof. vm_compute. reflexivity. Qed.

(*
Footnote references
===================

The label is source, trimmed and whitespace-collapsed by
`normalize_label`, and everything the brackets would have held is
discarded.  Every one of these was read from `djot.js` before it was
written.
*)

Example note_basic :
  parse_inline_line "[^a]" = [mk (FootnoteReference "a")].
Proof. vm_compute. reflexivity. Qed.

(* The discard disposition: `*x*` is destroyed, not flattened. *)
Example note_label_is_source :
  parse_inline_line "[^*x*]" = [mk (FootnoteReference "*x*")].
Proof. vm_compute. reflexivity. Qed.

Example note_label_normalized :
  parse_inline_line "[^ a  b ]" = [mk (FootnoteReference "a b")].
Proof. vm_compute. reflexivity. Qed.

(* A label crosses a line break, and the newline is whitespace. *)
Example note_label_crosses_break :
  para_inlines ["[^a"; "b]"] = [mk (FootnoteReference "a b")].
Proof. vm_compute. reflexivity. Qed.

Example note_empty_label : parse_inline_line "[^]" = [mk (FootnoteReference "")].
Proof. vm_compute. reflexivity. Qed.

(* The verdict is final at the `]`: no destination, reference or span
   mode follows, so what comes after is ordinary text.  This is where a
   footnote reference differs from every other bracket. *)
Example note_beats_destination :
  parse_inline_line "[^a](url)"
  = [mk (FootnoteReference "a"); mk (Str "(url)")].
Proof. vm_compute. reflexivity. Qed.

Example note_beats_reference :
  parse_inline_line "[^a][b]"
  = [mk (FootnoteReference "a"); mk (Str "[b]")].
Proof. vm_compute. reflexivity. Qed.

(* A spec still attaches, because the reference is a node and
   `oattach_list` takes the last one resolved. *)
Example note_takes_attributes :
  parse_inline_line "[^a]{.c}"
  = [Node NoPos [("class", "c")] (FootnoteReference "a")].
Proof. vm_compute. reflexivity. Qed.

(* The image marker decays: `!` is text and the note is its own node. *)
Example note_after_bang :
  parse_inline_line "![^a]" = [mk (Str "!"); mk (FootnoteReference "a")].
Proof. vm_compute. reflexivity. Qed.

(* Only a `^` *immediately* inside the bracket marks one. *)
Example note_marker_must_be_first :
  parse_inline_line "[x^a]" = [mk (Str "[x^a]")].
Proof. vm_compute. reflexivity. Qed.

Example note_escaped_bracket_is_text :
  parse_inline_line "\[^a]" = [mk (Str "[^a]")].
Proof. vm_compute. reflexivity. Qed.

(* An escape defers the `]` without being decoded: the label is source. *)
Example note_escaped_close :
  parse_inline_line "[^a\]b]" = [mk (FootnoteReference "a\]b")].
Proof. vm_compute. reflexivity. Qed.

(* Unclosed, the whole region is its own source. *)
Example note_unclosed_is_text :
  parse_inline_line "[^a" = [mk (Str "[^a")].
Proof. vm_compute. reflexivity. Qed.

Example note_unclosed_after_bang_is_text :
  parse_inline_line "x![^a" = [mk (Str "x![^a")].
Proof. vm_compute. reflexivity. Qed.

(* The innermost bracket wins, as it does for links. *)
Example note_inside_brackets :
  parse_inline_line "x[y[^a]z]w"
  = [mk (Str "x[y"); mk (FootnoteReference "a"); mk (Str "z]w")].
Proof. vm_compute. reflexivity. Qed.

(* ...and a note inside a link label survives into the link. *)
Example note_inside_link :
  parse_inline_line "[a[^b]c](u)"
  = [mk (Link [mk (Str "a"); mk (FootnoteReference "b"); mk (Str "c")]
          (Direct "u"))].
Proof. vm_compute. reflexivity. Qed.

(* Canonical text escapes the marker, so a `Str` can never spell one. *)
Example note_marker_escaped_in_canonical_text :
  ci_line [CIStr "[^a]"] = "\[\^a\]".
Proof. vm_compute. reflexivity. Qed.

(* The canonical leaf is the converse direction: its source deliberately
   leaves the marker structural and its AST is the reference node. *)
Example note_canonical_leaf :
  ci_line [CINote "a"] = "[^a]" /\
  ci_inlines [CINote "a"] = [mk (FootnoteReference "a")].
Proof. vm_compute. split; reflexivity. Qed.

Example note_canonical_empty_label : ci_ok (CINote "") = true.
Proof. vm_compute. reflexivity. Qed.

(* One trailing backslash protects the would-be closer; two are consumed
   as a pair and leave the closer structural. *)
Example note_canonical_backslash_boundary :
  ci_ok (CINote "a\") = false /\ ci_ok (CINote "a\\") = true.
Proof. vm_compute. split; reflexivity. Qed.

Example note_canonical_escaped_close :
  ci_ok (CINote "a\]b") = true /\
  parse_inline_line (ci_line [CINote "a\]b"])
    = ci_inlines [CINote "a\]b"].
Proof. vm_compute. split; reflexivity. Qed.

Example note_canonical_normalized_only : ci_ok (CINote " a  b ") = false.
Proof. vm_compute. reflexivity. Qed.

Example note_canonical_roundtrip_nested :
  parse_inline_line
    (ci_line [CILink false [CIStr "a"; CINote "b"; CIStr "c"] "u"])
  = ci_inlines [CILink false [CIStr "a"; CINote "b"; CIStr "c"] "u"].
Proof. apply parse_inline_line_ci; vm_compute; reflexivity. Qed.

(*
Autolinks
=========

`<...>` with no whitespace inside, which is a link to its own text.  Each
of these was read off djot.js before it was written down; the last two
are the divergence, logged in [[oracle-disagreements]].
*)

Example auto_url :
  parse_inline_line "<http://x.com>" = [mk (UrlLink "http://x.com")].
Proof. vm_compute. reflexivity. Qed.

Example auto_email_addr :
  parse_inline_line "<me@example.com>" = [mk (EmailLink "me@example.com")].
Proof. vm_compute. reflexivity. Qed.

(* The two tests are searches, not shapes: any letter-colon anywhere is a
   url, and the email test wins when both match. *)
Example auto_scheme_is_a_search :
  parse_inline_line "<a:b>" = [mk (UrlLink "a:b")].
Proof. vm_compute. reflexivity. Qed.

Example auto_email_beats_url :
  parse_inline_line "<a:b@c>" = [mk (EmailLink "a:b@c")].
Proof. vm_compute. reflexivity. Qed.

(* An `@` in the leading position has no character before it, so
   `/[^:]@/` cannot match and the region fails both tests. *)
Example auto_leading_at_is_not_email :
  parse_inline_line "<@x>" = [mk (Str "<@x>")].
Proof. vm_compute. reflexivity. Qed.

(* Neither test matches, so the brackets are literal -- as they are for
   an empty region, which the `+` in the pattern excludes. *)
Example auto_no_scheme_is_text :
  parse_inline_line "<div>" = [mk (Str "<div>")].
Proof. vm_compute. reflexivity. Qed.

Example auto_empty_is_text :
  parse_inline_line "<>" = [mk (Str "<>")].
Proof. vm_compute. reflexivity. Qed.

(* Whitespace ends the candidate where it stands, and a second `<` starts
   a new one -- which is what the regex does by failing at the first `<`
   and being retried one byte later. *)
Example auto_space_is_text :
  parse_inline_line "<a b>" = [mk (Str "<a b>")].
Proof. vm_compute. reflexivity. Qed.

Example auto_second_bracket_restarts :
  parse_inline_line "<a<b:c>" = [mk (Str "<a"); mk (UrlLink "b:c")].
Proof. vm_compute. reflexivity. Qed.

(* Nothing in the region is dispatched, which is what makes a backtick
   inside a *successful* autolink content rather than a verbatim opener. *)
Example auto_region_is_literal :
  parse_inline_line "<a:b`c>" = [mk (UrlLink "a:b`c")].
Proof. vm_compute. reflexivity. Qed.

(* A candidate that never closes decays to the text it ate, and the scan
   resumes -- so the `<` is not a mode the rest of the line is stuck in. *)
Example auto_unclosed_decays :
  parse_inline_line "x <a:b" = [mk (Str "x <a:b")].
Proof. vm_compute. reflexivity. Qed.

(* The open divergence.  djot.js decides with a regex lookahead and, when
   it fails, scans the region as ordinary inline content: `<_a_>` is
   `&lt;<em>a</em>&gt;` there and `&lt;_a_&gt;` here.  The current state
   does not keep that interpretation, but a shadow can do so
   without replay.  The canonical view cannot produce the shape because
   `escape_str` claims the `<`; see `.project/no-backtracking.md`. *)
Example auto_failed_region_is_flat :
  parse_inline_line "<_a_>" = [mk (Str "<_a_>")].
Proof. vm_compute. reflexivity. Qed.

Example auto_failed_region_keeps_escapes :
  parse_inline_line "<a\*b>" = [mk (Str "<a\*b>")].
Proof. vm_compute. reflexivity. Qed.

(* Canonical text escapes the `<`, so a `Str` can never spell one. *)
Example auto_bracket_escaped_in_canonical_text :
  ci_line [CIStr "<a:b>"] = "\<a\:b>".
Proof. vm_compute. reflexivity. Qed.

(* The canonical leaf: one constructor for both kinds, since the kind is
   computed from the region by the same function the scanner uses. *)
Example auto_canonical_leaf :
  ci_line [CIAuto "a:b"] = "<a:b>" /\
  ci_inlines [CIAuto "a:b"] = [mk (UrlLink "a:b")] /\
  ci_inlines [CIAuto "a@b"] = [mk (EmailLink "a@b")].
Proof. vm_compute. repeat split; reflexivity. Qed.

Example auto_canonical_needs_a_kind :
  ci_ok (CIAuto "div") = false /\ ci_ok (CIAuto "a:b") = true.
Proof. vm_compute. split; reflexivity. Qed.

Example auto_canonical_excludes_region_bytes :
  ci_ok (CIAuto "") = false /\ ci_ok (CIAuto "a: b") = false /\
  ci_ok (CIAuto "a:>b") = false.
Proof. vm_compute. repeat split; reflexivity. Qed.

Example auto_canonical_roundtrip_nested :
  parse_inline_line
    (ci_line [CIDelim DEmph [CIStr "a"; CIAuto "u:v"; CIStr "b"]])
  = ci_inlines [CIDelim DEmph [CIStr "a"; CIAuto "u:v"; CIStr "b"]].
Proof. apply parse_inline_line_ci; vm_compute; reflexivity. Qed.

(*
Raw inline
==========

A verbatim whose closer is followed immediately by `{=format}`.  Every
line here was read off djot.js first.
*)

Example raw_simple :
  parse_inline_line "`<a>`{=html}" = [mk (RawInline "html" "<a>")].
Proof. vm_compute. reflexivity. Qed.

(* The run length is the verbatim's business, not the spec's. *)
Example raw_wide_fence :
  parse_inline_line "``x``{=html}" = [mk (RawInline "html" "x")].
Proof. vm_compute. reflexivity. Qed.

(* The spec preempts the delimiter row spelled with the same character:
   `{=a=}` is a highlight anywhere else, and raw content in format `a=`
   here.  This is the one place the two constructs meet, and it is why
   `ci_pair_ok` excludes the pair. *)
Example raw_beats_the_row :
  parse_inline_line "`x`{=a=}" = [mk (RawInline "a=" "x")] /\
  parse_inline_line "{=a=}" = [mk (Highlight [mk (Str "a")])].
Proof. vm_compute. split; reflexivity. Qed.

(* Only a verbatim takes one.  djot.js guards the lookahead with
   `verbatimType`, so math keeps its node and the spec is text. *)
Example raw_not_after_math :
  parse_inline_line "$`x`{=html}"
  = [mk (Math InlineMath "x"); mk (Str "{=html}")].
Proof. vm_compute. reflexivity. Qed.

(* The `{` must be adjacent, and the format nonempty. *)
Example raw_needs_adjacency :
  parse_inline_line "`x` {=html}"
  = [mk (Verbatim "x"); mk (Str " {=html}")].
Proof. vm_compute. reflexivity. Qed.

Example raw_needs_a_format :
  parse_inline_line "`x`{=}" = [mk (Verbatim "x"); mk (Str "{=}")].
Proof. vm_compute. reflexivity. Qed.

(* A spec that is not a candidate at all leaves the `{` to the ordinary
   attribute path, which is what every canonical delimiter after a
   verbatim depends on. *)
Example raw_non_candidate_is_a_delimiter :
  parse_inline_line "`x`{_a_}"
  = [mk (Verbatim "x"); mk (Emph [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example raw_non_candidate_is_an_attribute :
  parse_inline_line "`x`{.c}"
  = [Node NoPos [("class", "c")] (Verbatim "x")].
Proof. vm_compute. reflexivity. Qed.

(* A candidate that fails puts back what it read and dispatches the byte
   that failed it, so a construct inside the region still parses -- which
   is what djot.js's rescan does, and the reason raw needs no divergence
   entry where the autolink did. *)
Example raw_failed_spec_resumes_the_scan :
  parse_inline_line "`x`{=a`b`}"
  = [mk (Verbatim "x"); mk (Str "{=a"); mk (Verbatim "b"); mk (Str "}")].
Proof. vm_compute. reflexivity. Qed.

(* A spec the line ends inside never closes; so does a bare `{`, which is
   the state the mode stands in for. *)
Example raw_unclosed_is_text :
  parse_inline_line "`x`{=htm" = [mk (Verbatim "x"); mk (Str "{=htm")] /\
  parse_inline_line "`x`{" = [mk (Verbatim "x"); mk (Str "{")].
Proof. vm_compute. split; reflexivity. Qed.

(* The exclusion the construct costs the canonical view: a verbatim may
   not be followed by the row spelled `=`, because that source is raw.
   Every other row is unaffected. *)
Example raw_pair_exclusion :
  ci_sep_ok [CIVerb "x"; CIDelim DMark [CIStr "a"]] = false /\
  ci_sep_ok [CIVerb "x"; CIDelim DEmph [CIStr "a"]] = true.
Proof. vm_compute. split; reflexivity. Qed.

(* The canonical leaf.  Unlike the autolink's, the format is a field: the
   scanner reads it as source rather than computing it from the
   content. *)
Example raw_canonical_leaf :
  ci_line [CIRaw "html" "<br>"] = "`<br>`{=html}" /\
  ci_inlines [CIRaw "html" "<br>"] = [mk (RawInline "html" "<br>")].
Proof. vm_compute. split; reflexivity. Qed.

(* The verbatim half is spelled by the verbatim machinery, so content
   that would close its own fence widens it -- and the spec still lands
   on the closing run. *)
Example raw_canonical_widens_its_fence :
  ci_line [CIRaw "html" "a`b"] = "``a`b``{=html}" /\
  parse_inline_line (ci_line [CIRaw "html" "a`b"])
    = ci_inlines [CIRaw "html" "a`b"].
Proof. vm_compute. split; reflexivity. Qed.

(* The format is read raw, so what it may not hold it may not escape
   either. *)
Example raw_canonical_format_conditions :
  ci_ok (CIRaw "" "x") = false /\
  ci_ok (CIRaw "a b" "x") = false /\
  ci_ok (CIRaw "a}b" "x") = false /\
  ci_ok (CIRaw "a`b" "x") = false /\
  ci_ok (CIRaw "html" "x") = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* And it merges with a verbatim before it exactly as a second verbatim
   would, which is the second pair the construct costs. *)
Example raw_pair_after_verbatim :
  ci_sep_ok [CIVerb "x"; CIRaw "html" "y"] = false /\
  ci_sep_ok [CIRaw "html" "y"; CIVerb "x"] = true.
Proof. vm_compute. split; reflexivity. Qed.

Example raw_canonical_roundtrip_nested :
  parse_inline_line
    (ci_line [CIDelim DEmph [CIStr "a"; CIRaw "html" "<br>"]])
  = ci_inlines [CIDelim DEmph [CIStr "a"; CIRaw "html" "<br>"]].
Proof. apply parse_inline_line_ci; vm_compute; reflexivity. Qed.

(*
The empty-span exclusion
========================

djot.js looks at the *top* of the opener stack for a delimiter character
and nowhere else (inline.ts:145).  When that opener is empty it declines
to close and the closer becomes an opener, so a run of n identical
delimiters around content nests n deep, and a bare run is literal.  These
are the rows of the baseline table in .project/extension-decisions.md,
which the configurable delimiter table has to keep reproducing.
*)

Example emph_run_two : parse_inline_line "__a__"
  = [mk (Emph [mk (Emph [mk (Str "a")])])].
Proof. vm_compute. reflexivity. Qed.

Example emph_run_three : parse_inline_line "___a___"
  = [mk (Emph [mk (Emph [mk (Emph [mk (Str "a")])])])].
Proof. vm_compute. reflexivity. Qed.

(* The case flagged to check first: a fourth level is still just nesting,
   so the exclusion does generalize to longer runs of one character.  It
   is what a multi-character delimiter has to be stated against. *)
Example emph_run_four : parse_inline_line "____a____"
  = [mk (Emph [mk (Emph [mk (Emph [mk (Emph [mk (Str "a")])])])])].
Proof. vm_compute. reflexivity. Qed.

(* Bare runs are literal, at every length: each closer finds an empty
   opener on top, declines, and becomes an opener that is never closed. *)
Example emph_run_bare_two : parse_inline_line "__" = [mk (Str "__")].
Proof. vm_compute. reflexivity. Qed.

Example emph_run_bare_four : parse_inline_line "____" = [mk (Str "____")].
Proof. vm_compute. reflexivity. Qed.

(* Unbalanced runs: the surplus stays literal on the side that has it. *)
Example emph_run_unbalanced_left : parse_inline_line "__a_"
  = [mk (Str "_"); mk (Emph [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example emph_run_unbalanced_right : parse_inline_line "_a__"
  = [mk (Emph [mk (Str "a")]); mk (Str "_")].
Proof. vm_compute. reflexivity. Qed.

(*
Inline attributes
=================

A spec attaches to the run of text before it.  The table in
.project/260811.inline-parser.md is the measured source for these.
*)

Example attr_on_word :
  parse_inline_line "foo{.a}"
  = [Node NoPos [("class", "a")] (Str "foo")].
Proof. vm_compute. reflexivity. Qed.

(* The split is at the last whitespace, so only the final word takes the
   spec -- and an attributed `Str` therefore never contains a space. *)
Example attr_splits_at_last_space :
  parse_inline_line "foo bar{.a}"
  = [mk (Str "foo "); Node NoPos [("class", "a")] (Str "bar")].
Proof. vm_compute. reflexivity. Qed.

Example attr_punctuation_does_not_split :
  parse_inline_line "a-b{.a}"
  = [Node NoPos [("class", "a")] (Str "a-b")].
Proof. vm_compute. reflexivity. Qed.

(* Parentheses are not a span: the spec still lands on the last word. *)
Example attr_parens_are_not_a_span :
  parse_inline_line "(some text){.attr}"
  = [mk (Str "(some "); Node NoPos [("class", "attr")] (Str "text)")].
Proof. vm_compute. reflexivity. Qed.

(* Adjacency: a space before the brace means there is no last word, and
   the spec is dropped. *)
Example attr_needs_adjacency :
  parse_inline_line "foo {.a}" = [mk (Str "foo ")].
Proof. vm_compute. reflexivity. Qed.

(* An empty spec attaches nothing.  djot.js cuts the text in two here;
   both halves are plain, so one run is the same HTML and keeps us inside
   `no_adjacent_str`. *)
Example attr_empty_spec :
  parse_inline_line "foo{}bar" = [mk (Str "foobar")].
Proof. vm_compute. reflexivity. Qed.

(* `{` before a delimiter character is a braced delimiter, never a spec:
   djot.js resolves the ambiguity that way even when the contents would
   have parsed as attributes. *)
Example attr_brace_delimiter_wins :
  parse_inline_line "a{_x=y_}"
  = [mk (Str "a"); mk (Emph [mk (Str "x=y")])].
Proof. vm_compute. reflexivity. Qed.

(* A failed spec resumes the scan at the byte that failed, as a span
   does. *)
Example attr_failed_spec_resumes :
  parse_inline_line "x{bad*y*z"
  = [mk (Str "x{bad"); mk (Strong [mk (Str "y")]); mk (Str "z")].
Proof. vm_compute. reflexivity. Qed.

(* With no pending text the spec decorates the node just emitted. *)
Example attr_on_node :
  parse_inline_line "*e*{.a}"
  = [Node NoPos [("class", "a")] (Strong [mk (Str "e")])].
Proof. vm_compute. reflexivity. Qed.

(* The immediately preceding *node*, not the innermost one: a byte of
   text after the close puts the word back in the way. *)
Example attr_on_node_loses_to_text :
  parse_inline_line "*e*w{.a}"
  = [mk (Strong [mk (Str "e")]); Node NoPos [("class", "a")] (Str "w")].
Proof. vm_compute. reflexivity. Qed.

(* An empty spec builds no wrapper but still vanishes, which is what
   `[l](u){}` needs. *)
Example attr_empty_spec_on_node :
  parse_inline_line "[l](u){}"
  = [mk (Link [mk (Str "l")] (Direct "u"))].
Proof. vm_compute. reflexivity. Qed.

(* Nothing at all before it and the spec is gone, source included.  A
   line that is nothing else resolves to no inlines at all, which is why
   `para_block` may answer with no block. *)
Example attr_with_nothing_before_vanishes :
  parse_inline_line "{#i} x"
  = [mk (Str " x")].
Proof. vm_compute. reflexivity. Qed.

Example attr_alone_leaves_nothing :
  parse_inline_line "{#i}" = [].
Proof. vm_compute. reflexivity. Qed.

(* A scope holding nothing else closes onto nothing, which is djot.js's
   `<strong></strong>`: the empty-scope test runs on the items, before
   attachment. *)
Example attr_alone_in_scope_closes_empty :
  parse_inline_line "*{#i}*" = [mk (Strong [])].
Proof. vm_compute. reflexivity. Qed.

(* An opener that never closed is text by the time the spec attaches, so
   the last word reaches back over it.  This is the whole point of
   deferring: at the `}` the `*` is still an open scope and the answer is
   not yet available. *)
Example attr_reaches_over_an_unclosed_opener :
  parse_inline_line "a *b{.c}o"
  = [mk (Str "a "); Node NoPos [("class", "c")] (Str "*b"); mk (Str "o")].
Proof. vm_compute. reflexivity. Qed.

(* And over text flushed before that opener was even pushed, which is
   what rules out repairing this locally when the scope is abandoned. *)
Example attr_reaches_past_the_scope :
  parse_inline_line "az*b{.c}o"
  = [Node NoPos [("class", "c")] (Str "az*b"); mk (Str "o")].
Proof. vm_compute. reflexivity. Qed.

(* Two of them, and a bracket, decay the same way. *)
Example attr_reaches_over_nested_openers :
  parse_inline_line "a *_b{.c}o"
  = [mk (Str "a "); Node NoPos [("class", "c")] (Str "*_b"); mk (Str "o")].
Proof. vm_compute. reflexivity. Qed.

Example attr_reaches_over_a_bracket :
  parse_inline_line "a [x{.c}o"
  = [mk (Str "a "); Node NoPos [("class", "c")] (Str "[x"); mk (Str "o")].
Proof. vm_compute. reflexivity. Qed.

(* When the opener *does* close it is a node, and the spec stops there --
   which is what the scan always did, and what deferring must not
   change. *)
Example attr_stops_at_a_closed_opener :
  parse_inline_line "a b*c*d{.e}f"
  = [mk (Str "a b"); mk (Strong [mk (Str "c")]);
     Node NoPos [("class", "e")] (Str "d"); mk (Str "f")].
Proof. vm_compute. reflexivity. Qed.

Example attr_inside_a_closed_opener :
  parse_inline_line "a *b{.c}o*"
  = [mk (Str "a ");
     mk (Strong [Node NoPos [("class", "c")] (Str "b"); mk (Str "o")])].
Proof. vm_compute. reflexivity. Qed.

(* An empty spec still resolves to nothing, and the run it sat between is
   rejoined: `oresolve_go`'s flag is what stops the two halves ending up
   adjacent. *)
Example attr_empty_spec_rejoins :
  parse_inline_line "foo{}bar" = [mk (Str "foobar")].
Proof. vm_compute. reflexivity. Qed.

(* A spec first inside a scope that closes: the scope's tip is empty, the
   spec goes, and the scope keeps the rest. *)
Example attr_first_in_a_closing_scope :
  parse_inline_line "a *{.c}b*"
  = [mk (Str "a "); mk (Strong [mk (Str "b")])].
Proof. vm_compute. reflexivity. Qed.

Example attr_alone_in_a_closing_scope :
  parse_inline_line "a *{.c}*"
  = [mk (Str "a "); mk (Strong [])].
Proof. vm_compute. reflexivity. Qed.

(* A spec inside a bracket that decays.  Nothing resolves at the `]`
   here: the byte after it is not one of the three that close a bracket,
   so the scope stays open and `oflatten` abandons it at the end of the
   paragraph, merging the opener's `[` into the `Str` the spec then
   attaches to.  djot.js reads it the same way. *)
Example attr_inside_a_decaying_bracket :
  parse_inline_line "[a{.c}b] c"
  = [Node NoPos [("class", "c")] (Str "[a"); mk (Str "b] c")].
Proof. vm_compute. reflexivity. Qed.

(* The break is a byte of the spec, so the machine is fed it and the
   spec closes on the next line.  Nothing separates the two lines in the
   output: the break was inside the spec's source, and djot.js's
   `attributeSlices` swallow it the same way. *)
Example attr_spec_crosses_a_break :
  para_inlines ["hi{#id .class"; "key=""value""}"]
  = [Node NoPos [("id", "id"); ("class", "class"); ("key", "value")]
       (Str "hi")].
Proof. vm_compute. reflexivity. Qed.

(* A comment is a spec that commits nothing, so a multi-line one is a
   spec that attaches nothing -- and the text before it ends in a space,
   which is where a spec is dropped rather than attached. *)
Example attr_comment_crosses_a_break :
  para_inlines ["Foo bar {% This is a comment, spanning"; "multiple lines %} baz."]
  = [mk (Str "Foo bar  baz.")].
Proof. vm_compute. reflexivity. Qed.

(* A spec the paragraph ended inside is its own source, and the breaks it
   spanned come back as `SoftBreak`s: a `Str` holding a newline renders
   the same but does not survive a reparse, so the buffer cannot go back
   whole.  This is `bsplit_nl`, the destination's rule. *)
Example attr_unclosed_spec_keeps_its_breaks :
  para_inlines ["{a=x"; "hello"]
  = [mk (Str "{a=x"); mk SoftBreak; mk (Str "hello")].
Proof. vm_compute. reflexivity. Qed.

(* A failed attribute candidate keeps an ordinary-inline interpretation
   current beside the spec, with attribute recognition disabled there.
   Choosing that interpretation at the end makes the quote smart and lets
   the delimiter pair interact normally, without replaying any source. *)
Example attr_unclosed_spec_keeps_ordinary_scan :
  parse_inline_line "x{a=""*b*"""
  = [mk (Str "x{a=");
     mk (Quoted DoubleQuotes [mk (Strong [mk (Str "b")])])].
Proof. vm_compute. reflexivity. Qed.

(* And it is cut at the slice boundaries djot.js re-feeds that source on,
   so a run inside the candidate never grows into one token: `-` and `-`
   are two hyphens rather than an en dash, where the same two bytes
   outside a candidate are one. *)
Example attr_failed_spec_cuts_a_run :
  parse_inline_line "x{a--" = [mk (Str "x{a--")].
Proof. vm_compute. reflexivity. Qed.

(*
The key connective, pinned
==========================

The three tables of `.project/keyed-blocks.md` section 3, one example
per row.  `key_point` is the split rule of 3.1, `key_label_ok` the
one-inline rule of 3.2, and `key_split` the two together, which is what
the block layer asks.
*)

(* 3.1, the split rule *)

Example key_first_colon : key_point "foo: bar" = Some ("foo", "bar").
Proof. vm_compute. reflexivity. Qed.

(* Nothing is decided by whether the run closes: an unclosed one runs to
   the end of the line, so the colon is inside the span either way. *)
Example key_inside_verbatim :
  key_point "`a: b` is how you write it" = None.
Proof. vm_compute. reflexivity. Qed.

Example key_after_verbatim :
  key_point "`code`: a description" = Some ("`code`", "a description").
Proof. vm_compute. reflexivity. Qed.

Example key_inside_link : key_point "[see: here](x) is the reference" = None.
Proof. vm_compute. reflexivity. Qed.

Example key_after_link :
  key_point "[see](x): the reference" = Some ("[see](x)", "the reference").
Proof. vm_compute. reflexivity. Qed.

Example key_after_brace :
  key_point "foo{#my-foo}: bar" = Some ("foo{#my-foo}", "bar").
Proof. vm_compute. reflexivity. Qed.

(* The first colon reads as part of a title, so the scan goes on. *)
Example key_after_quoted_value :
  key_point "x{title=""a: b""}y: z" = Some ("x{title=""a: b""}y", "z").
Proof. vm_compute. reflexivity. Qed.

(* A quotation mark pairs like any other delimiter, so these two are the
   same construct open and closed. *)
Example key_inside_quotation : key_point """foo: bar"" and more" = None.
Proof. vm_compute. reflexivity. Qed.

Example key_after_quotation :
  key_point """foo"": bar" = Some ("""foo""", "bar").
Proof. vm_compute. reflexivity. Qed.

(* Declined although splitting would have been harmless: the `_` is
   unmatched, but at the colon the scan cannot know that yet. *)
Example key_inside_emphasis : key_point "_a: b_" = None.
Proof. vm_compute. reflexivity. Qed.

(* 9.1.  A delimiter run against the colon is undecided rather than
   open: settling it needs the byte the colon occupies, and it settles
   as an opener there and as literal text at a line's end.  Alone the
   label would be `a*`; in place the `*` opens the span that swallows
   the colon.  A run that *closes* consults no following byte, which is
   why `key_after_quotation` is unaffected. *)
Example key_pending_delimiter :
  (key_point "a*: b*", key_point "a_: b_", key_point "a^: b^",
   key_point "a~: b~", key_point "a"": b""")
  = (None, None, None, None, None).
Proof. vm_compute. reflexivity. Qed.

Example key_needs_adjacency : key_point "foo : bar" = None.
Proof. vm_compute. reflexivity. Qed.

Example key_needs_space_after : key_point "foo:bar" = None.
Proof. vm_compute. reflexivity. Qed.

Example key_tab_is_not_a_space : key_point "foo:	bar" = None.
Proof. vm_compute. reflexivity. Qed.

(* The value may be empty, which is the two-line spelling's key line. *)
Example key_line_final : key_point "foo:" = Some ("foo", "").
Proof. vm_compute. reflexivity. Qed.

(* One split per line: what follows is the value's text, colons and all. *)
Example key_one_per_line : key_point "foo: bar: baz" = Some ("foo", "bar: baz").
Proof. vm_compute. reflexivity. Qed.

(* An escaped colon is text, and a pending backslash is not a closed
   state, so the rule needs no case for it. *)
Example key_escaped_colon : key_point "foo\: bar:" = Some ("foo\: bar", "").
Proof. vm_compute. reflexivity. Qed.

Example key_empty_label : key_point ":" = None.
Proof. vm_compute. reflexivity. Qed.

Example key_leading_colon : key_point ": term" = None.
Proof. vm_compute. reflexivity. Qed.

(* The line is normalised, so a container prefix's indentation cannot
   change the answer. *)
Example key_ignores_indentation : key_point "    foo: bar" = key_point "foo: bar".
Proof. vm_compute. reflexivity. Qed.

(* 3.2, the one-inline rule.  The counts are of the resolved list, which
   is why the first five are one node and not two or three. *)

Example key_label_run : key_label_ok "foo" = true.
Proof. vm_compute. reflexivity. Qed.

Example key_label_phrase : key_label_ok "foo bar baz" = true.
Proof. vm_compute. reflexivity. Qed.

Example key_label_apostrophe : key_label_ok "it's" = true.
Proof. vm_compute. reflexivity. Qed.

Example key_label_dash : key_label_ok "a -- b" = true.
Proof. vm_compute. reflexivity. Qed.

Example key_label_escape : key_label_ok "foo\: bar" = true.
Proof. vm_compute. reflexivity. Qed.

Example key_label_verbatim : key_label_ok "`code`" = true.
Proof. vm_compute. reflexivity. Qed.

Example key_label_link : key_label_ok "[see](x)" = true.
Proof. vm_compute. reflexivity. Qed.

Example key_label_quotation : key_label_ok """foo""" = true.
Proof. vm_compute. reflexivity. Qed.

Example key_label_strong : key_label_ok "*bold*" = true.
Proof. vm_compute. reflexivity. Qed.

(* An attribute is not a second element: it rides on the element in
   front of it. *)
Example key_label_attributed : key_label_ok "x{title=""a""}" = true.
Proof. vm_compute. reflexivity. Qed.

Example key_label_two_kinds : key_label_ok "x`y`" = false.
Proof. vm_compute. reflexivity. Qed.

(* Two runs, and they cannot merge: only one carries the title. *)
Example key_label_split_attribute : key_label_ok "x{title=""a: b""}y" = false.
Proof. vm_compute. reflexivity. Qed.

Example key_label_embedded_markup : key_label_ok "the `--flag` option" = false.
Proof. vm_compute. reflexivity. Qed.

(* An attribute spec that finds nothing to decorate vanishes, and its
   neighbours merge, so the label is the one run they make. *)
Example key_label_vanished_spec : key_label_ok "a {#i}b" = true.
Proof. vm_compute. reflexivity. Qed.

(* 3.6, where a line does not read as it looks *)

Example key_prose_colon :
  key_split "Note: this matters." = Some ("Note", "this matters.").
Proof. vm_compute. reflexivity. Qed.

Example key_declines_embedded_markup :
  key_split "the `--flag` option: what it does" = None.
Proof. vm_compute. reflexivity. Qed.

Example key_declines_split_attribute :
  key_split "x{title=""a: b""}y: z" = None.
Proof. vm_compute. reflexivity. Qed.

Example key_second_colon_splits :
  key_split "see http://x: it works" = Some ("see http://x", "it works").
Proof. vm_compute. reflexivity. Qed.

(* A spec with nothing before it leaves no inline at all, so a label that
   is nothing else is not one inline and the line is not a key.  This is
   `key_label_ok` doing the work: 3.2's advice -- an attribute meant for
   the keyed node goes on its own line above -- now has a mechanism
   behind it rather than an accident of spelling. *)
Example key_leading_brace_is_no_key :
  key_split "{#i}: bar" = None.
Proof. vm_compute. reflexivity. Qed.

(* With something after it the spec attaches and the label is that. *)
Example key_leading_brace_attaches :
  key_split "{#i}foo: bar" = Some ("{#i}foo", "bar").
Proof. vm_compute. reflexivity. Qed.
