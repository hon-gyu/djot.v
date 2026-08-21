(* ai-disclosure: autonomous *)

(* The inline layer: the parser's pass over a paragraph's text, and the
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
From DjotV Require Import Strings Ast Attributes.
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
  dc_decay : dstyle -> ddecay
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
  DConfig djot_dchar djot_dwidth djot_dsyntax djot_ddecay.

(* The second table this development intends to ship: Markdown's
   spelling, with djot's rules.  `_` stays emphasis and `**` becomes
   strong, which is what a reader coming from Markdown expects; a single
   `*` is then not a delimiter at all, since a row's width is fixed and a
   run shorter than it is literal.

   Markdown-*like*, not CommonMark: the delimiters do not disambiguate by
   run length or flanking, because there is nothing to disambiguate --
   one character, one row, one width.  That is djot's property, and
   keeping it is the point of spelling the extension as a table rather
   than as rules. *)
Definition markdown_config : dconfig :=
  DConfig (fun k => match k with DStrong => "*"%char | _ => djot_dchar k end)
          (fun k => match k with DStrong => 2 | _ => 1 end)
          djot_dsyntax djot_ddecay.

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
   vanish, and `iscan_productive` -- the statement that every state owes
   the output something -- would be false. *)
Definition ddecay_ok (d : ddecay) : bool :=
  match d with
  | DDSelf => true
  | DDPair _ l r => (nonempty_str l && nonempty_str r)%bool
  end.

Definition drow_ok (C : dconfig) (k : dstyle) : bool :=
  (negb (Nat.eqb (dc_width C k) 0)
   && is_punct (dc_char C k)
   && negb (dreserved (dc_char C k))
   && ddecay_ok (dc_decay C k))%bool.

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

(* Look a character up in the table rather than repeating it: the two
   spellings used to be written out separately and kept in step by
   `dstyle_of_dchar` below, which is now a fact about the search instead
   of a coincidence to maintain.  A row switched off is not found, so
   `DOff` removes the character from the scanner entirely. *)

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
                      djot_dwidth djot_dsyntax djot_ddecay) = false.
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
                      djot_ddecay) = true.
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

(* What an unmatched token leaves behind.  An ordinary row leaves its own
   source, braces and all; a smart quote leaves a curly character, and
   the markers choose the side -- an open marker takes the left form and
   a close marker the right, which is djot.js flipping its
   `defaultmatch` (`inline.ts:118-136`). *)
Definition ddecay_str (k : dstyle) (openmark closemark : bool) : string :=
  match dc_decay cfg k with
  | DDSelf =>
      ((if openmark then one lbrace else EmptyString)
       ++ dtoken k
       ++ (if closemark then one rbrace else EmptyString))%string
  | DDPair dfl l r =>
      if openmark then l
      else if closemark then r
      else if dfl then l else r
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
  apply andb_true_iff in H as [_ H]. exact H.
Qed.

(* ...and it is not one the scanner claims, so `ilead` reaches the
   lookup at all. *)
Lemma dchar_free : forall k, dreserved (dchar k) = false.
Proof.
  intros k. pose proof (drow_ok_of k) as H.
  unfold drow_ok in H. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [_ H]. apply negb_true_iff in H. exact H.
Qed.

(* What condition 5 buys, in the form the scanner uses it. *)
Lemma ddecay_str_nonempty :
  forall k om cm, nonempty_str (ddecay_str k om cm) = true.
Proof.
  intros k om cm. pose proof (drow_ok_of k) as H.
  unfold drow_ok in H. apply andb_true_iff in H as [_ H].
  unfold ddecay_str. destruct (dc_decay cfg k) as [|dfl l r] eqn:E.
  - pose proof (dtoken_nonempty k) as Ht.
    destruct om; [reflexivity|].
    destruct (dtoken k); [discriminate|reflexivity].
  - cbn [ddecay_ok] in H. apply andb_true_iff in H as [Hl Hr].
    destruct om; [exact Hl|]. destruct cm; [exact Hr|].
    destruct dfl; [exact Hl|exact Hr].
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
   table hands out, and `^`.

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
  (dreserved c || is_delim c || Ascii.eqb c hat || Ascii.eqb c hyphen)%bool.

(* Obligation 1: an escaped character must be one the decoder accepts.
   Half of it is the seven reserved characters, which are punctuation by
   computation; the other half is the table's, and holds because an
   admissible row is spelled with punctuation. *)
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

(* And the same for the brackets, now that the scanner dispatches on
   them: a `[` in a `Str` would open a scope, and a `]` would close one
   that a later construct opened. *)
Lemma needs_escape_lbrack : needs_escape lbrack = true.
Proof. reflexivity. Qed.

Lemma needs_escape_rbrack : needs_escape rbrack = true.
Proof. reflexivity. Qed.

(* The `!` an image opens on.  Escaping it unconditionally is what lets a
   `Str` ending in `!` sit before a link without turning it into an
   image, which is exactly the reading djot.js gives `\![a](u)`. *)
Lemma needs_escape_bang : needs_escape bang = true.
Proof. reflexivity. Qed.

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
  | CIAuto (s : string).

Fixpoint ci_size (ci : cinline) : nat :=
  let go :=
    fix go (cis : list cinline) : nat :=
      match cis with
      | [] => 0
      | c :: rest => ci_size c + go rest
      end in
  match ci with
  | CIStr _ | CIVerb _ | CINote _ | CIAuto _ => 1
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
  intros [s|s|k kids|img kids dst|img kids label|label|s]; cbn [ci_size]; lia.
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
Definition ci_pair_ok (a b : cinline) : bool :=
  match a, b with
  | CIStr _, CIStr _ => false
  | CIVerb _, CIVerb _ => false
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
      (note_label_safe label && String.eqb (normalize_label label) label)%bool
  (* The region has to be one the pattern accepts and one of the two
     tests claims: a region that fails them is not an autolink but the
     literal text of its own brackets, which is a `CIStr` instead. *)
  | CIAuto s => (auto_body_ok s && auto_kind_ok s)%bool
  end.

Lemma ci_ok_auto :
  forall s, ci_ok (CIAuto s) = (auto_body_ok s && auto_kind_ok s)%bool.
Proof. reflexivity. Qed.

Lemma ci_ok_note :
  forall label,
    ci_ok (CINote label)
    = (note_label_safe label && String.eqb (normalize_label label) label)%bool.
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
That is not an accident of style: it makes "the scanner never re-feeds a
source position through tokenization" structural, which is the project's
precise no-backtracking claim (see `.project/260811.inline-parser.md`
§2.4).  It does not forbid retroactive scope-stack changes, and it is not
a linear-time claim: resolving one byte may still walk the opener stack.
It also matches djot.js's `feed`, which is a position-at-a-time loop over
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

Inductive frame_kind : Type :=
  | FKDelim (style : dstyle)
  (* `image` records the `!` before the `[`, which djot.js instead reads
     back off the subject at the close (`inline.ts:475`).  We cannot: the
     text before the bracket has been flushed by then, and an escaped
     `\!` is indistinguishable from a bare one once it is in the buffer. *)
  | FKBracket (image : bool).

Record frame : Type := Frame {
  fr_kind : frame_kind;
  fr_marked : bool;          (* delimiter opened as `{d`; false for `[` *)
  fr_out : inlines           (* this scope's inlines, reversed *)
}.

(* The opener's source text, which is what it decays to when abandoned. *)
Definition fr_src (f : frame) : string :=
  match fr_kind f with
  | FKDelim k => ddecay_str k (fr_marked f) false
  | FKBracket image => bracket_open image
  end.

Record ostate : Type := OState {
  os_out : inlines;          (* the outermost scope, reversed *)
  os_stk : list frame        (* open scopes, innermost first *)
}.

Definition ostart : ostate := OState [] [].

(* The scope emissions land in: the innermost open one, or the bottom. *)
Definition ocur (o : ostate) : inlines :=
  match os_stk o with [] => os_out o | f :: _ => fr_out f end.

(* ...and the same scope, written back.  Only `oattach` needs it: every
   other writer pushes rather than replaces. *)
Definition oset_cur (l : inlines) (o : ostate) : ostate :=
  match os_stk o with
  | [] => OState l []
  | f :: rest => OState (os_out o) (Frame (fr_kind f) (fr_marked f) l :: rest)
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
  | FKDelim k' => (dstyle_eqb k k' && Bool.eqb m (fr_marked f))%bool
  | FKBracket _ => false
  end.

(* Reversed-list splices that merge a `Str` seam, so `no_adjacent_str`
   survives an abandoned opener becoming text next to its neighbours. *)
Definition osnoc (n : node inline) (out : inlines) : inlines :=
  match out, n with
  | Node p [] (Str t) :: rest, Node _ [] (Str s) =>
      (Node p [] (Str (t ++ s)) :: rest)%list
  | _, _ => (n :: out)%list
  end.

(* Whether the seam could merge: exactly `Wf.plain_str` of the head, and
   the same notion `no_adjacent_str` is stated over.  A `Str` carrying
   attributes is a node in its own right and never merges. *)
Definition starts_str (out : inlines) : bool :=
  match out with Node _ [] (Str _) :: _ => true | _ => false end.

Fixpoint oapp (cur out : inlines) : inlines :=
  match cur with
  | [] => out
  | [n] => osnoc n out
  | n :: rest => n :: oapp rest out
  end.

Definition oemit (n : node inline) (o : ostate) : ostate :=
  match os_stk o with
  | [] => OState (n :: os_out o) []
  | f :: rest =>
      OState (os_out o) (Frame (fr_kind f) (fr_marked f) (n :: fr_out f) :: rest)
  end.

(* Emit in source order while merging a plain-`Str` seam.  Ordinary
   scanner emission keeps the seam obligation explicit in `iscan_wf`;
   reconstruction paths (abandoned frames and bracket literal fallback)
   already know they are splicing source fragments and need the merge by
   construction. *)
Definition oemit_merge (n : node inline) (o : ostate) : ostate :=
  match os_stk o with
  | [] => OState (osnoc n (os_out o)) []
  | f :: rest =>
      OState (os_out o)
        (Frame (fr_kind f) (fr_marked f) (osnoc n (fr_out f)) :: rest)
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

Definition flush_text (txt : string) (o : ostate) : ostate :=
  if nonempty_str txt then oemit (mk (Str txt)) o else o.

Definition opush (k : dstyle) (m : bool) (o : ostate) : ostate :=
  OState (os_out o) (Frame (FKDelim k) m [] :: os_stk o).

Definition bpush (image : bool) (o : ostate) : ostate :=
  OState (os_out o) (Frame (FKBracket image) false [] :: os_stk o).

Lemma oemit_all_app :
  forall a b o, oemit_all (a ++ b)%list o = oemit_all b (oemit_all a o).
Proof.
  induction a as [|n a IH]; intros b o; cbn [oemit_all];
    [reflexivity|apply IH].
Qed.

Lemma oemit_all_frame :
  forall ns out kind m acc stk,
    oemit_all ns (OState out (Frame kind m acc :: stk))
    = OState out (Frame kind m (List.rev ns ++ acc)%list :: stk).
Proof.
  induction ns as [|n ns IH]; intros out kind m acc stk;
    cbn [oemit_all List.rev app]; [reflexivity|].
  change (oemit_all ns (OState out (Frame kind m (n :: acc) :: stk))
          = OState out
              (Frame kind m ((List.rev ns ++ [n]) ++ acc)%list :: stk)).
  rewrite IH, <- List.app_assoc. reflexivity.
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
   instead of literal. *)
Fixpoint oclose_go (k : dstyle) (m : bool) (pend : inlines) (stk : list frame)
  : option (inlines * list frame) :=
  match stk with
  | [] => None
  | f :: rest =>
      let content := oapp pend (fr_out f) in
      if dmatch k m f
      then (if nonempty content then Some (content, rest) else None)
      else oclose_go k m (oapp content [mk (Str (fr_src f))]) rest
  end.

Definition oclose (k : dstyle) (m : bool) (o : ostate) : option ostate :=
  match oclose_go k m [] (os_stk o) with
  | None => None
  | Some (content, rest) =>
      Some (oemit (mk (dnode k (List.rev content))) (OState (os_out o) rest))
  end.

Lemma oclose_oemit_all_marked :
  forall k ns base,
    nonempty ns = true ->
    oclose k true (oemit_all ns (opush k true base))
    = Some (oemit (mk (dnode k ns)) base).
Proof.
  intros k ns [out stk] Hne. unfold opush. rewrite oemit_all_frame.
  unfold oclose. cbn [os_stk os_out oclose_go oapp dmatch fr_kind
    fr_marked fr_out]. rewrite !app_nil_r.
  assert (Hrev : nonempty (List.rev ns) = true).
  { destruct ns as [|n rest]; [discriminate|].
    cbn [List.rev]. destruct (List.rev rest); reflexivity. }
  rewrite Hrev. destruct k;
    cbn [dmatch dstyle_eqb fr_kind fr_marked andb_true_l].
  all: cbn; rewrite List.rev_involutive; reflexivity.
Qed.

(* Brackets share the ordered scope stack with delimiters.  Finding a
   bracket abandons any delimiter frames above it, just as djot.js closes
   the bracketed construct before `clearOpeners` removes openers inside
   it.  Unlike a delimiter close this only extracts the label content:
   the following byte still decides link, reference, span, or literal
   brackets. *)
Fixpoint bclose_go (pend : inlines) (stk : list frame)
  : option (inlines * bool * list frame) :=
  match stk with
  | [] => None
  | f :: rest =>
      let content := oapp pend (fr_out f) in
      match fr_kind f with
      | FKBracket image => Some (content, image, rest)
      | FKDelim _ =>
          bclose_go (oapp content [mk (Str (fr_src f))]) rest
      end
  end.

Definition bclose (o : ostate) : option (inlines * bool * ostate) :=
  match bclose_go [] (os_stk o) with
  | None => None
  | Some (content, image, rest) =>
      Some (List.rev content, image, OState (os_out o) rest)
  end.

(* Take back a bracket the previous byte pushed.  Only a frame that is a
   bracket *and* still empty can be taken back, which is exactly the
   shape a `[` leaves behind and nothing else does, so a caller may ask
   without knowing what is on the stack.  That totality is what keeps the
   footnote marker free of any invariant relating `prev` to the frames,
   and `bunpush o = None` is what every lemma about a row's token gets
   for free -- a marked close has a *delimiter* frame on top. *)
Definition bunpush (o : ostate) : option (bool * ostate) :=
  match os_stk o with
  | Frame (FKBracket image) _ [] :: rest => Some (image, OState (os_out o) rest)
  | _ => None
  end.

Lemma bunpush_opush :
  forall k m o, bunpush (opush k m o) = None.
Proof. intros k m [out stk]. reflexivity. Qed.

Lemma bunpush_bpush :
  forall image o, bunpush (bpush image o) = Some (image, o).
Proof. intros image [out stk]. reflexivity. Qed.

Lemma bclose_oemit_all :
  forall ns image base,
    bclose (oemit_all ns (bpush image base)) = Some (ns, image, base).
Proof.
  intros ns image [out stk]. unfold bpush. rewrite oemit_all_frame.
  unfold bclose. cbn [os_stk os_out bclose_go fr_out fr_kind oapp].
  rewrite app_nil_r, List.rev_involutive. reflexivity.
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
      | Node _ [] (Str s) :: rest => (s, OState rest [])
      | _ => (EmptyString, o)
      end
  | f :: fs =>
      match fr_out f with
      | Node _ [] (Str s) :: rest =>
          (s, OState (os_out o) (Frame (fr_kind f) (fr_marked f) rest :: fs))
      | _ => (EmptyString, o)
      end
  end.

(* Children back into the buffer.  A plain `Str` child is text and joins
   it; anything else is emitted, flushing the buffer first.  So emissions
   alternate `Str` and non-`Str` and the seam obligation holds by
   construction -- this is why the fallback needs no merging emission. *)
Fixpoint bflat (kids : inlines) (txt : string) (o : ostate) : string * ostate :=
  match kids with
  | [] => (txt, o)
  | Node _ [] (Str s) :: rest => bflat rest (txt ++ s)%string o
  | n :: rest => bflat rest EmptyString (oemit n (flush_text txt o))
  end.

(* Text that spans a line break.  A `SoftBreak` is a node, so such text
   cannot go back into the buffer whole.  Only a destination needs this:
   it is the one buffer that survives `ibreak`. *)
Fixpoint bsplit_nl (s txt : string) (o : ostate) : string * ostate :=
  match s with
  | EmptyString => (txt, o)
  | String c rest =>
      if Ascii.eqb c nl_char
      then bsplit_nl rest EmptyString (oemit (mk SoftBreak) (flush_text txt o))
      else bsplit_nl rest (txt ++ one c)%string o
  end.

(* A closed bracket that turns out to be literal: `[`, the label, `]`. *)
Definition bclosed_lit (kids : inlines) (image : bool) (o : ostate)
  : string * ostate :=
  let '(pre, o1) := opop_str o in
  let '(txt, o2) := bflat kids (pre ++ bracket_open image)%string o1 in
  ((txt ++ one rbrack)%string, o2).

(* A span whose spec failed, or that ran out of line: the bracket's own
   literal text, then the `{` and everything the machine read. *)
Definition bspan_lit (kids : inlines) (image : bool) (src : string)
  (o : ostate) : string * ostate :=
  let '(txt, o') := bclosed_lit kids image o in
  ((txt ++ one lbrace ++ src)%string, o').

Definition bref_lit (kids : inlines) (image : bool) (label : string)
  (o : ostate) : string * ostate :=
  let '(txt, o') := bclosed_lit kids image o in
  ((txt ++ one lbrack ++ label)%string, o').

(* A destination that never closed: the above, then `(` and what the
   destination had accumulated, including the breaks it spanned. *)
Definition bdest_lit (kids : inlines) (image esc : bool) (dst : string)
  (o : ostate) : string * ostate :=
  let '(txt, o') := bclosed_lit kids image o in
  bsplit_nl (if esc then (dst ++ one bslash)%string else dst)
            (txt ++ one lparen)%string o'.

(* The destination itself drops the breaks (`parse.ts:612`), which is why
   they are kept as characters until it is known to close. *)
Fixpoint drop_nl (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if Ascii.eqb c nl_char then drop_nl rest else String c (drop_nl rest)
  end.

(* Everything still open when the paragraph ends is abandoned. *)
Fixpoint oflatten (pend : inlines) (stk : list frame) (bottom : inlines)
  : inlines :=
  match stk with
  | [] => oapp pend bottom
  | f :: rest =>
      oflatten (oapp (oapp pend (fr_out f)) [mk (Str (fr_src f))]) rest bottom
  end.

Definition ofinish (o : ostate) : inlines :=
  oflatten [] (os_stk o) (os_out o).

(* What a backtick run closes into.  djot.js keeps this in
   `verbatimType` and decides it retroactively when the closing run
   arrives; we decide it at the opening run, which is the same thing
   because the prefix is already read by then. *)
Inductive vkind : Type := VVerb | VMath (style : math_style).

Definition vnode (vk : vkind) (s : string) : inline :=
  match vk with VVerb => Verbatim s | VMath st => Math st s end.

Inductive iscan : Type :=
  (* accumulating literal text; `esc` is a pending backslash, and `prev`
     is the byte before `txt` (`None` at the start of a paragraph or of a
     line), which is what `can_close` consults when `txt` is empty *)
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
     is what keeps every state productive -- there is no state holding an
     empty token.

     `marked` says the token is the one after a `{`, which needs no byte
     after it: it opens on sight, so `idelim_marked` pushes the scope the
     moment the width is reached and a marked state is therefore never a
     *complete* token.  What it still owes is the rest of its own token,
     and what it decays to keeps the `{`. *)
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
     anything else makes the brackets literal.  `kids` is the label,
     already classified and in source order, `image` is what its opener
     was, and `o` is the state the bracket opened in, restored by
     `bclose`. *)
  | IClosed (kids : inlines) (image : bool) (o : ostate)
  (* inside the second bracket of `[text][label]`.  The label is source
     text, not inline content: upstream's `strMatches` retroactively
     flattens everything in this region before building the reference. *)
  (* A closed bracket followed by `{`: a span, if the spec parses.  The
     spec is read with the same machine block attributes use, fed a byte
     at a time; `src` is what it has eaten, kept so the whole region can
     be put back as text when the machine fails.  `image` is carried only
     for that reconstruction -- a span ignores it, so `![x]{.a}` is a `!`
     followed by a span. *)
  | ISpan (kids : inlines) (image : bool) (p : aparser) (src : string)
          (o : ostate)
  (* An attribute spec, which attaches to whatever precedes it.  `txt` is
     the text pending when the `{` arrived: it is both the literal
     fallback and, on success, the thing the spec attaches to. *)
  | IAttr (p : aparser) (src : string) (txt : string) (prev : option ascii)
          (o : ostate)
  | IReference (kids : inlines) (image : bool) (label : string) (o : ostate)
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
  | INote (esc image : bool) (label : string) (o : ostate)
  (* inside a `](`.  `depth` counts unclosed inner parentheses, `dst`
     accumulates the destination with its escapes decoded, and `esc` is a
     pending backslash, as in text mode.  A destination survives a line
     break, so this is the second state `ibreak` carries across one. *)
  | IDest (kids : inlines) (image esc : bool) (depth : nat) (dst : string)
          (o : ostate)
  (* inside a `<`, holding the region read so far.  Not a scope and not a
     parallel parse: the region is raw source, so a backtick or a
     delimiter inside a *successful* autolink is content
     (`<a:b`c>` links to ``a:b`c``), which is only true because nothing
     in here is dispatched.

     `txt` is the text pending when the `<` arrived, kept because a
     candidate that fails is put back as literal text -- and there
     [[260811.inline-parser]] logs a divergence: djot.js decides with a
     regex lookahead and rescans the region as inline content when the
     lookahead fails, which a scanner that re-reads no byte cannot do. *)
  | IAuto (src txt : string) (o : ostate).

(* The one position in which the table does not get the byte: right
   inside a bracket that has just opened, where a `^` marks a footnote
   rather than a superscript. *)
Definition note_pos (txt : string) (prev : option ascii) : bool :=
  (negb (nonempty_str txt)
   && match prev with Some p => Ascii.eqb p lbrack | None => false end)%bool.

(* One byte in text mode.  The delimiter arm is a lookup, not six
   branches, for the reason the table's own comment gives. *)
Definition ilead (c : ascii) (txt : string) (prev : option ascii) (o : ostate)
  : iscan :=
  if is_bslash c then IText true txt prev o
  else if is_tick c then IOpen 1 VVerb (flush_text txt o)
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
     closes the innermost bracket scope, abandoning any delimiter scopes
     opened inside it, and hands the label to `IClosed`; with no bracket
     open it is ordinary text. *)
  else if Ascii.eqb c bang then IBang txt prev o
  (* A `<` opens an autolink candidate, which is neither a scope nor a
     lookahead: it accumulates the region and decides at the `>`.  The
     pending text stays pending, since a candidate that fails hands it
     back with the `<` on the end. *)
  else if Ascii.eqb c lt then IAuto EmptyString txt o
  else if Ascii.eqb c lbrack
  then IText false EmptyString (Some lbrack) (bpush false (flush_text txt o))
  else if Ascii.eqb c rbrack
  then match bclose (flush_text txt o) with
       | Some (kids, image, o') => IClosed kids image o'
       | None => IText false (txt ++ one rbrack)%string prev o
       end
  (* A `^` right inside a bracket that has just opened marks a footnote.
     djot.js reads the byte after the opener when the `]` arrives
     (`inline.ts:361`) and then discards every match made in between, so
     taking the bracket back here and reading the label as source is the
     same verdict one byte earlier -- and it is the only way we can spell
     the label, since we keep no source beside classified nodes.
     Written as a guard on `bunpush` rather than as a claim about the
     stack, so a `^` anywhere else falls through to the table, where it
     is the superscript row as it always was. *)
  else match (if (Ascii.eqb c hat && note_pos txt prev)%bool
              then bunpush o else None) with
       | Some (image, o') => INote false image EmptyString o'
       | None =>
           match dstyle_of c with
           | Some k => IDelim k 0 txt (str_last txt prev) false o
           | None => IText false (txt ++ one c)%string prev o
           end
       end.

Definition null {A} (l : list A) : bool :=
  match l with [] => true | _ => false end.

(* Has the scan produced anything here?  An open scope counts: it is
   abandoned at the end and its opener becomes text. *)
Definition ostate_nonempty (o : ostate) : bool :=
  (nonempty (os_out o) || negb (null (os_stk o)))%bool.


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

(* The node a spec decorates when no pending text takes it: the last one
   emitted into the current scope, which is djot.js's `getTip()`
   (`parse.ts:452`).

   A `SoftBreak` is not one, and that exclusion is what makes the
   question askable at all.  `oout_app` splices a previous line's output
   *underneath* the current scope, so a scope that has emitted nothing
   sees that line's last node here instead of nothing -- and a previous
   line always ends in the `SoftBreak` that ended it (the same fact
   `osnoc_nonstr` relies on).  Refusing that one constructor therefore
   makes the answer the same on both sides of a splice, which is what
   `iattr_attach_app` needs.  It is also right on its own terms: djot.js
   attaches to the break node and renders it identically, since a break
   has no tag to carry attributes on. *)
Definition oattach (a : attr) (o : ostate) : option ostate :=
  match ocur o with
  | Node _ _ SoftBreak :: _ | [] => None
  | Node p a' v :: rest => Some (oset_cur (Node p (attr_merge a a') v :: rest) o)
  end.

(* It found a node, so the scope it wrote back to still holds one. *)
Lemma oattach_nonempty :
  forall a o o', oattach a o = Some o' -> ostate_nonempty o' = true.
Proof.
  intros a o o' H. unfold oattach in H.
  destruct (ocur o) as [|[p a' v] rest]; [discriminate|].
  destruct v; try discriminate; injection H as <-;
    unfold ostate_nonempty, oset_cur; destruct (os_stk o);
    cbn [os_out os_stk null negb]; solve [reflexivity | apply orb_true_r].
Qed.

(* Where a finished spec lands.  One question, asked of the two places an
   answer can live, in djot.js's order (`parse.ts:446-506`):

   - pending text takes it on its last word.  The split is on whitespace,
     not on word characters, so `a-b{.a}` attributes all of `a-b`; an
     empty spec keeps the run whole instead, since cutting it would only
     produce two plain `Str`s and break `no_adjacent_str`.
   - text ending in whitespace has no last word, and djot.js drops the
     spec there rather than attaching it across the gap (`endsWithSpace`).
   - with nothing pending, the last node emitted into this scope takes
     it, which is what makes `*e*{.a}`, `[l](u){}` and `x{.a}{.b}` work.

   Nothing at all to attach to is the one case we do not follow djot.js
   on.  It drops the spec, leaving `# {#i}` an empty heading; `wf_block`
   excludes those and `parse_inline_line_nonempty` denies them, so we
   keep the source as text instead and log the divergence.  It is
   confined to a spec with no scope output and no pending text before
   it. *)
Definition iattr_attach (a : attr) (src txt : string) (prev : option ascii)
  (o : ostate) : iscan :=
  let '(pre, w) := last_ws_split txt in
  if nonempty_str w
  then match a with
       | [] => IText false txt prev o
       | _ => IText false EmptyString (Some rbrace)
                (oemit (Node NoPos a (Str w)) (flush_text pre o))
       end
  else if nonempty_str txt
  then IText false txt prev o
  else match oattach a o with
       | Some o' => IText false EmptyString (Some rbrace) o'
       | None => IText false (one lbrace ++ src)%string prev o
       end.

(* One byte of an inline attribute spec, read with the machine block
   attributes use.  Failure hands the byte back to `ilead` with the text
   restored, as a span's does. *)
Definition iattr_feed (c : ascii) (p : aparser) (src txt : string)
  (prev : option ascii) (o : ostate) : iscan :=
  let p' := astep p c in
  if ap_failed p'
  then ilead c (txt ++ one lbrace ++ src)%string prev o
  else if ap_done p'
  then iattr_attach (ap_attrs p') (src ++ one c)%string txt prev o
  else IAttr p' (src ++ one c)%string txt prev o.

(* A marked open with `S extra` characters of its token in hand.  It
   needs no byte after it -- djot.js forces `can_open` and blocks
   `can_close` for a marked delimiter -- so reaching the row's width
   pushes the scope there and then, and only a token still short of it
   waits.  `before` is `None` throughout: the branch that would read it
   is the one this never reaches. *)
Definition idelim_marked (k : dstyle) (extra : nat) (txt : string)
  (o : ostate) : iscan :=
  if Nat.ltb (S extra) (dwidth k)
  then IDelim k extra txt None true o
  else IText false EmptyString (Some (dchar k)) (opush k true (flush_text txt o)).

(* What a token that never finished decays to: the row's characters
   received so far, with the `{` of a marked open back in front of
   them. *)
Definition idelim_run (k : dstyle) (extra : nat) (marked : bool) : string :=
  ((if marked then one lbrace else EmptyString)
     ++ chars (dchar k) (S extra))%string.

Lemma idelim_run_nonempty :
  forall k extra marked, nonempty_str (idelim_run k extra marked) = true.
Proof. intros k extra []; reflexivity. Qed.

(* Resolving a `{`: an open marker if a delimiter follows, text
   otherwise.

   An attribute also begins with `{`, and is not implemented; until it is,
   every other `{` is text, which is what the scanner did before. *)
Definition ibrace_step (c : ascii) (txt : string) (prev : option ascii)
  (o : ostate) : iscan :=
  match dstyle_of c with
  | Some k => idelim_marked k 0 txt o
  | None => iattr_feed c ap_init EmptyString txt prev o
  end.

(* A span ignores the image marker: `![x]{.a}` is a literal `!` followed
   by a span.  The `!` was never flushed -- `IClosed` records it in a flag
   and `bclosed_lit` puts it back on the literal path -- so the span path
   has to emit it here, and it merges with any `Str` already at the tip
   the same way, since `flush_text` alone would leave two adjacent. *)
Definition ospan_bang (image : bool) (o : ostate) : ostate :=
  if image
  then let '(pre, o1) := opop_str o in flush_text (pre ++ one bang)%string o1
  else o.

(* One byte into an open span's spec.  `ADone` arrives on the `}`, so the
   node is built here with no byte left over.  On `AFail` the region up to
   but not including the failing byte becomes text and that byte is
   dispatched afresh: djot.js resumes its scan there, so `[s]{bad*x*y` is
   `[s]{bad`, a strong `x`, and `y`. *)
Definition ispan_feed (c : ascii) (kids : inlines) (image : bool)
  (p : aparser) (src : string) (o : ostate) : iscan :=
  let p' := astep p c in
  if ap_failed p'
  then let '(txt, o') := bspan_lit kids image src o in ilead c txt None o'
  else if ap_done p'
  then IText false EmptyString (Some rbrace)
         (oemit (Node NoPos (ap_attrs p') (Span kids)) (ospan_bang image o))
  else ISpan kids image p' (src ++ one c)%string o.

(* Resolving a `!`: an image opener if a `[` follows, text otherwise.
   The `!` is *not* flushed with the text before it -- it is the opener's
   own source, and `fr_src` puts it back if the bracket decays. *)
(* One byte of a footnote label.  The `]` is the only byte with a role,
   and a backslash defers it once -- without being decoded, since the
   label is source and djot.js labels `[^a\]b]` with the backslash still
   in it. *)
Definition inote_step (c : ascii) (esc image : bool) (label : string)
  (o : ostate) : iscan :=
  if esc then INote false image (label ++ one bslash ++ one c)%string o
  else if is_bslash c then INote true image label o
  else if Ascii.eqb c rbrack
  then IText false EmptyString (Some rbrack)
         (oemit (mk (FootnoteReference (normalize_label label)))
            (ospan_bang image o))
  else INote false image (label ++ one c)%string o.

(* A candidate that failed is its own source: the `<`, what it ate, and
   whatever pended before it.  One string rather than a state, because
   the byte that killed it still has to be dispatched. *)
Definition auto_lit (src txt : string) : string :=
  (txt ++ String lt src)%string.

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
Definition iauto_step (c : ascii) (src txt : string) (o : ostate) : iscan :=
  if (Ascii.eqb c gt && auto_body_ok src && auto_kind_ok src)%bool
  then IText false EmptyString (Some gt)
         (oemit (mk (auto_node src)) (flush_text txt o))
  else if (Ascii.eqb c gt || is_ws c || Ascii.eqb c lt)%bool
  then ilead c (auto_lit src txt) None o
  else IAuto (src ++ one c)%string txt o.

(* A label that never closed is its own source: the bracket it took back,
   the marker, and what it had eaten.  `opop_str` reabsorbs the `Str`
   that the bracket's own `flush_text` emitted, so the reconstruction is
   one run and `no_adjacent_str` survives -- the move `bclosed_lit`
   makes, for the same reason. *)
Definition bnote_lit (esc image : bool) (label : string) (o : ostate)
  : string * ostate :=
  let '(pre, o1) := opop_str o in
  ((pre ++ bracket_open image ++ one hat ++ label
       ++ (if esc then one bslash else EmptyString))%string, o1).

Definition ibang_step (c : ascii) (txt : string) (prev : option ascii)
  (o : ostate) : iscan :=
  if Ascii.eqb c lbrack
  then IText false EmptyString (Some lbrack) (bpush true (flush_text txt o))
  else ilead c (txt ++ one bang)%string prev o.

(* Resolving an unbraced delimiter, once the byte after it has arrived
   (or not, at the end of a line: `inone`).  Closing wins over opening,
   as in djot.js, and a `}` immediately after forces the close. *)
Definition idelim_lit (k : dstyle) (txt : string) (marker : bool) : string :=
  (txt ++ ddecay_str k false marker)%string.

Definition idelim_done (k : dstyle) (txt : string) (before : option ascii)
  (marker : bool) (next : option ascii) (o : ostate) : iscan :=
  if (dbare k before && negb marker && nonspace_at next)%bool
  then IText false EmptyString (Some (dchar k)) (opush k false (flush_text txt o))
  else IText false (idelim_lit k txt marker) None o.

Definition idelim_resolve (k : dstyle) (txt : string) (before : option ascii)
  (marker : bool) (next : option ascii) (o : ostate) : iscan :=
  if (nonspace_at before || marker)%bool
  then match oclose k marker (flush_text txt o) with
       | Some o' =>
           IText false EmptyString
             (Some (if marker then rbrace else dchar k)) o'
       | None => idelim_done k txt before marker next o
       end
  else idelim_done k txt before marker next o.

(* No byte follows: the end of a line or of the paragraph.  `IBrace` and
   `IDelim` are the only states this changes, and after it neither
   remains, which is what lets `ibreak` and `ifinish` match on the rest. *)
(* The dollars a pending prefix is holding, when they turn out to be
   text. *)
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

Definition dollars (two : bool) : string :=
  if two then (one dollar ++ one dollar)%string else one dollar.

(* Resolving a `$`: another `$` widens the prefix to display math, a
   backtick run opens the span it prefixes, and anything else makes the
   dollars text.  A third `$` keeps the last two, which is djot.js
   popping exactly two matches, so the extra one is flushed here. *)
Definition idollar_step (c : ascii) (two : bool) (txt : string)
  (prev : option ascii) (o : ostate) : iscan :=
  if Ascii.eqb c dollar
  then (if two then IDollar true (txt ++ one dollar)%string prev o
        else IDollar true txt prev o)
  else if is_tick c
  then IOpen 1 (VMath (if two then DisplayMath else InlineMath))
         (flush_text txt o)
  else ilead c (txt ++ dollars two)%string prev o.

(* Three periods are one ellipsis and any other run is literal, so the
   state counts to two and the third byte decides (`inline.ts:343`).  A
   run of four is an ellipsis and a period, which falls out of resolving
   at the third and starting again. *)
Definition iperiod_step (c : ascii) (two : bool) (txt : string)
  (prev : option ascii) (o : ostate) : iscan :=
  if Ascii.eqb c period
  then (if two then IText false (txt ++ ellipsis)%string (Some c) o
        else IPeriod true txt prev o)
  else ilead c (txt ++ periods two)%string prev o.

(* A run of hyphens ends at the first byte that is not one.  A `}` is the
   exception, and the only place the dash rule and the delete row meet:
   the run gives its last hyphen back to be a close marker, and what is
   left is cut into dashes.  When no row is spelled with a hyphen there
   is nothing to close and the two bytes are text, which is djot.js's
   `hyphens === 0` branch. *)
Definition idash_step (c : ascii) (n : nat) (txt : string)
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
           then idelim_resolve k (txt ++ dashes (n - dwidth k))%string
                  None true (Some c) o
           else IText false (txt ++ dashes n ++ one rbrace)%string None o
       | None => IText false (txt ++ dashes n ++ one rbrace)%string None o
       end
  else ilead c (txt ++ dashes n)%string prev o.

Definition iresolve (st : iscan) : iscan :=
  match st with
  | IBrace txt prev o => IText false (txt ++ one lbrace)%string prev o
  | IDollar two txt prev o => IText false (txt ++ dollars two)%string prev o
  | IPeriod two txt prev o => IText false (txt ++ periods two)%string prev o
  | IDash n txt prev o => IText false (txt ++ dashes n)%string prev o
  | IAttr _ src txt prev o =>
      IText false (txt ++ one lbrace ++ src)%string prev o
  | IBang txt prev o => IText false (txt ++ one bang)%string prev o
  (* A token still being spelled is text: the run ended before the row's
     width was reached. *)
  | IDelim k extra txt before marked o =>
      if Nat.ltb (S extra) (dwidth k)
      then IText false (txt ++ idelim_run k extra marked)%string None o
      else idelim_resolve k txt before false None o
  (* `[a]` at the end of a line is literal: djot.js scans the newline as
     an ordinary byte, and a `(` after it is not a destination. *)
  | IClosed kids image o =>
      let '(txt, o') := bclosed_lit kids image o in IText false txt None o'
  | _ => st
  end.

(* What a backslash and a whitespace run decay to when the line does not
   end after them.  djot.js tests the byte after the backslash for a
   space and for nothing else (`inline.ts:250`), so a tab leaves the
   backslash literal; either way the decision consumes only the first
   byte of the run and the rest is ordinary text. *)
Definition iescws_resolve (ws txt : string) (prev : option ascii)
  (o : ostate) : string * option ascii * ostate :=
  match ws with
  | String c rest =>
      if Ascii.eqb c " "%char
      then (rest, Some c, oemit (mk NonBreakingSpace) (flush_text txt o))
      else ((txt ++ one bslash ++ ws)%string, prev, o)
  (* unreachable: `IEscWs` is only ever built with a byte in hand.  Spelt
     as the bare backslash anyway, so that every `IEscWs` owes something
     and `iscan_productive` needs no side condition. *)
  | EmptyString => ((txt ++ one bslash)%string, prev, o)
  end.

(* The line ended after the backslash.  djot.js trims the whitespace that
   preceded it off the last `str` match (`inline.ts:222-237`); the run
   pending here is that match, so the trim is local. *)
Definition iesc_hard (txt : string) (o : ostate) : ostate :=
  oemit (mk HardBreak) (flush_text (strip_trailing_ws txt) o).

Definition istep (c : ascii) (st : iscan) : iscan :=
  match st with
  | IText true txt prev o =>
      if is_ws c then IEscWs (one c) txt prev o
      else IText false (txt ++ (if is_punct c then one c
                                else String "\"%char (one c)))%string prev o
  | IEscWs ws txt prev o =>
      if is_ws c then IEscWs (ws ++ one c)%string txt prev o
      else let '(txt', prev', o') := iescws_resolve ws txt prev o in
           ilead c txt' prev' o'
  | IText false txt prev o => ilead c txt prev o
  | IBrace txt prev o => ibrace_step c txt prev o
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
         else ilead c (txt ++ idelim_run k extra marked)%string None o)
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
      then ilead c EmptyString (Some tick)
             (oemit (mk (vnode vk (trim_verb txt))) o)
      else IVerb n 0 (txt ++ ticks run ++ one c)%string vk o
  (* The two bracket modes.  Nothing enters them yet: `[` and `]` are not
     dispatched, so `bclose` has no caller and these arms are dead.  They
     are written first because every state-parametric invariant below
     must say what they do, and landing that separately from the dispatch
     is what keeps a missed case from hiding behind a behaviour diff. *)
  | IClosed kids image o =>
      if Ascii.eqb c lparen then IDest kids image false 0 EmptyString o
      else if Ascii.eqb c lbrack then IReference kids image EmptyString o
      else if Ascii.eqb c lbrace
      then ISpan kids image ap_init EmptyString o
      else let '(txt, o') := bclosed_lit kids image o in ilead c txt None o'
  | ISpan kids image p src o => ispan_feed c kids image p src o
  | IAttr p src txt prev o => iattr_feed c p src txt prev o
  | INote esc image label o => inote_step c esc image label o
  | IAuto src txt o => iauto_step c src txt o
  | IReference kids image label o =>
      if Ascii.eqb c rbrack
      then let key := match label with
                      | EmptyString => reference_inlines_text kids
                      | _ => label
                      end in
           IText false EmptyString (Some rbrack)
             (oemit (mk (bnode image kids (Reference (normalize_label key)))) o)
      else IReference kids image (label ++ one c)%string o
  | IDest kids image true depth dst o =>
      IDest kids image false depth
        (dst ++ (if is_punct c then one c
                 else String bslash (one c)))%string o
  | IDest kids image false depth dst o =>
      if is_bslash c then IDest kids image true depth dst o
      else if Ascii.eqb c lparen
      then IDest kids image false (S depth) (dst ++ one lparen)%string o
      else if Ascii.eqb c rparen
      then match depth with
           | O =>
               (* the balanced close: the one byte that builds the node *)
               IText false EmptyString (Some rparen)
                 (oemit (mk (bnode image kids (Direct (drop_nl dst)))) o)
           | S d => IDest kids image false d (dst ++ one rparen)%string o
           end
      else IDest kids image false depth (dst ++ one c)%string o
  end.

(* End of line.  An unclosed verbatim closes here, as djot.js does in
   `getMatches`.  A pending backslash is a hard break, djot.js's reading;
   djoths keeps a literal backslash, a logged disagreement
   (`escapes.test:30`).  It cannot arise from a canonical rendering,
   since `escape_str` never emits a backslash that is not followed by
   punctuation. *)
Definition ifinish_ostate (st : iscan) : ostate :=
  match iresolve st with
  | IText true txt _ o => iesc_hard txt o
  | IEscWs _ txt _ o => iesc_hard txt o
  | IText false txt _ o => flush_text txt o
  | IOpen _ vk o => oemit (mk (vnode vk EmptyString)) o
  | IVerb n run txt vk o =>
      oemit (mk (vnode vk (trim_verb
                   (if Nat.eqb run n then txt else txt ++ ticks run)%string))) o
  (* an unclosed destination is literal, breaks and all *)
  | IDest kids image esc _ dst o =>
      let '(txt, o') := bdest_lit kids image esc dst o in flush_text txt o'
  | INote esc image label o =>
      let '(txt, o') := bnote_lit esc image label o in flush_text txt o'
  (* a candidate the line ended inside is literal: the region may not
     contain a break, so the `>` it wanted can never arrive *)
  | IAuto src txt o => flush_text (auto_lit src txt) o
  | IReference kids image label o =>
      let '(txt, o') := bref_lit kids image label o in flush_text txt o'
  (* an unclosed span is literal too: the scan does not cross the break,
     so a spec that would have continued on the next line never closes *)
  | ISpan kids image _ src o =>
      let '(txt, o') := bspan_lit kids image src o in flush_text txt o'
  (* unreachable: `iresolve` leaves no `IBrace`, `IAttr`, `IBang`,
     `IDollar`, `IDelim` or `IClosed` *)
  | IBrace _ _ o | IAttr _ _ _ _ o | IBang _ _ o | IDollar _ _ _ o
  | IPeriod _ _ _ o | IDash _ _ _ o
  | IDelim _ _ _ _ _ o | IClosed _ _ o => o
  end.

Definition ifinish_rev (st : iscan) : inlines := ofinish (ifinish_ostate st).

Definition ifinish (st : iscan) : inlines := List.rev (ifinish_rev st).

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
Definition ibreak (st : iscan) : iscan :=
  match iresolve st with
  (* A hard break replaces the soft one: it is the break, rendered. *)
  | IText true txt _ o => IText false EmptyString None (iesc_hard txt o)
  | IEscWs _ txt _ o => IText false EmptyString None (iesc_hard txt o)
  | IText false txt _ o =>
      IText false EmptyString None (oemit (mk SoftBreak) (flush_text txt o))
  | IOpen n vk o => IVerb n 0 nl vk o
  | IVerb n run txt vk o =>
      if Nat.eqb run n
      then IText false EmptyString None
             (oemit (mk SoftBreak) (oemit (mk (vnode vk (trim_verb txt))) o))
      else IVerb n 0 (txt ++ ticks run ++ nl)%string vk o
  (* A destination crosses the break: djot.js keeps scanning and strips
     the newline from the destination text at the close, so the byte is
     accumulated and dropped later rather than dropped here -- the
     literal fallback still needs it if the destination never closes. *)
  | IDest kids image esc depth dst o =>
      IDest kids image false depth
        (dst ++ (if esc then one bslash else EmptyString) ++ nl)%string o
  (* A label crosses a break and the newline is whitespace to
     `normalize_label`, so `[^a` / `b]` is one reference to `a b`. *)
  | INote esc image label o =>
      INote false image
        (label ++ (if esc then one bslash else EmptyString) ++ nl)%string o
  | IReference kids image label o =>
      IReference kids image (label ++ nl)%string o
  (* and the break itself is the soft one, exactly as it is for the text
     the candidate decays to *)
  | IAuto src txt o =>
      IText false EmptyString None
        (oemit (mk SoftBreak) (flush_text (auto_lit src txt) o))
  (* A span's spec crosses the break too, and the newline is whitespace to
     the machine: `[s]{.a` / `.b}` is one span whose classes merge.  It is
     fed rather than accumulated because the machine is what decides
     whether the break separates two tokens. *)
  | ISpan kids image p src o => ispan_feed nl_char kids image p src o
  (* unreachable, as in `ifinish_ostate` *)
  | (IBrace _ _ _ | IAttr _ _ _ _ _ | IBang _ _ _ | IDollar _ _ _ _
    | IPeriod _ _ _ _ | IDash _ _ _ _
    | IDelim _ _ _ _ _ _ | IClosed _ _ _) as st' => st'
  end.

(* A state that owes nothing to the next line: every construct it has
   seen is resolved, so the boundary just ends the line and `ibreak`
   agrees with `ifinish` on what was emitted.  What fails it is a span
   still open across the break -- an unterminated backtick run, a
   verbatim whose closer has not arrived, or any open scope. *)
Definition iscan_closed (st : iscan) : bool :=
  match iresolve st with
  (* a pending backslash is not closed: it owes the *next* byte a hard
     break or a literal, so the line does not end with a soft one *)
  | IText esc _ _ o => (negb esc && null (os_stk o))%bool
  | IEscWs _ _ _ _ => false
  | IOpen _ _ _ => false
  | IVerb n run _ _ o => (Nat.eqb run n && null (os_stk o))%bool
  (* an open destination owes the next line; `IClosed` cannot appear,
     since `iresolve` has just turned it into text *)
  | IBrace _ _ _ | IAttr _ _ _ _ _ | IBang _ _ _ | IDollar _ _ _ _
  | IPeriod _ _ _ _ | IDash _ _ _ _
  | IDelim _ _ _ _ _ _ | IClosed _ _ _ | ISpan _ _ _ _ _
  | INote _ _ _ _ | IReference _ _ _ _ | IDest _ _ _ _ _ _ => false
  (* an autolink candidate owes the next line nothing: the region may not
     hold a break, so the candidate dies at the boundary and what it ate
     is text on this line *)
  | IAuto _ _ o => null (os_stk o)
  end.

Lemma ibreak_closed :
  forall st,
    iscan_closed st = true ->
    ibreak st = IText false EmptyString None
                  (OState (mk SoftBreak :: ifinish_rev st) []).
Proof.
  intros st H. unfold iscan_closed, ibreak, ifinish_rev, ifinish_ostate in *.
  destruct (iresolve st) as [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|nesc nimg nlab nob|kids img esc depth dst ob|asrc atxt aob];
    try discriminate.
  - destruct o as [out [|f stk]]; [|discriminate].
    unfold flush_text, oemit, ofinish; cbn [os_stk os_out oflatten oapp].
    destruct (nonempty_str txt); reflexivity.
  - apply andb_true_iff in H as [Hr Hs]. rewrite Hr.
    destruct o as [out [|f stk]]; [|discriminate].
    unfold oemit, ofinish; cbn [os_stk os_out oflatten oapp]. reflexivity.
  (* the candidate decays to text and the boundary is the soft break
     after it, which is the text case with `auto_lit` in the buffer *)
  - destruct aob as [out [|f stk]]; [|discriminate].
    unfold flush_text, oemit, ofinish; cbn [os_stk os_out oflatten oapp].
    destruct (nonempty_str (auto_lit asrc atxt)); reflexivity.
Qed.

Fixpoint iscan_str (s : string) (st : iscan) : iscan :=
  match s with
  | EmptyString => st
  | String c rest => iscan_str rest (istep c st)
  end.

(* An executable certificate for the sense in which this scan does not
   backtrack.  One unit of fuel authorizes dispatching one source byte;
   state rewrites such as closing or abandoning a scope spend no source
   fuel and never feed that byte back to the scanner.  This deliberately
   says nothing about the internal cost of a dispatch -- `oclose` may walk
   the opener stack -- so it is not a linear-time theorem.  Bracket
   attribute reparse will be a separate, strictly decreasing call with
   attribute recognition disabled, rather than a relaxation of this
   contract. *)
Fixpoint iscan_str_fuel (fuel : nat) (s : string) (st : iscan)
  : option iscan :=
  match s with
  | EmptyString => Some st
  | String c rest =>
      match fuel with
      | O => None
      | S fuel' => iscan_str_fuel fuel' rest (istep c st)
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
  | x :: rest => iscan_lines rest (ibreak (iscan_str x st))
  end.

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
  - cbn [ticks iscan_str istep]. change
      (iscan_str (ticks k) (IOpen (S n) vk out) = IOpen (n + S k) vk out).
    rewrite IH. f_equal. lia.
Qed.

Lemma iscan_open_ticks :
  forall k txt prev o,
    iscan_str (ticks (S k)) (IText false txt prev o)
    = IOpen (S k) VVerb (flush_text txt o).
Proof.
  intros k txt prev o. cbn [ticks iscan_str istep ilead]. change
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
  - cbn [ticks iscan_str istep]. change
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
  cbn [starts_tick] in Hstart. cbn [iscan_str istep]. rewrite Hstart.
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
  - cbn [istep]. rewrite Hc. destruct rest as [|d rest'].
    + unfold ends_tick, starts_tick, rev_string in Hend.
      cbn [rev_string_aux] in Hend. rewrite Hc in Hend. discriminate.
    + rewrite ends_tick_cons_nonempty in Hend.
      rewrite (IH n (S run) txt vk out eq_refl Hend Hsafe).
      apply Ascii.eqb_eq in Hc. subst c. f_equal.
      rewrite ticks_succ_r, !append_assoc. reflexivity.
  - apply andb_true_iff in Hsafe as [Hrun Hsafe].
    apply negb_true_iff in Hrun. cbn [istep]. rewrite Hc, Hrun.
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
Definition oout_app (base : inlines) (o : ostate) : ostate :=
  OState (os_out o ++ base)%list (os_stk o).

(* What a suffix always is: empty, or a previous line, whose most recent
   node is the `SoftBreak` that ended it.  Every `_app` lemma below asks
   this of its suffix, and the one caller -- `para_inlines_cons2_closed`
   -- discharges it by `reflexivity`, because it builds the suffix by
   consing that very break.

   It used to be spelt as the weaker `starts_str base = false`, which is
   all the seam merge in `osnoc_nonstr` needs.  That was enough until
   `oattach` had to read the current scope: a scope that has emitted
   nothing sees the suffix's head there, so a suffix headed by anything
   *else* would make the same query answer two ways across a splice.
   Carrying the real invariant costs one hypothesis rename and buys the
   query. *)
Definition base_ok (base : inlines) : bool :=
  match base with
  | [] => true
  | Node _ _ SoftBreak :: _ => true
  | _ => false
  end.

Lemma base_ok_starts_str :
  forall base, base_ok base = true -> starts_str base = false.
Proof.
  intros [|[p [|kv a'] v] base] H; try reflexivity.
  destruct v; try reflexivity. discriminate.
Qed.

Definition iout_app (base : inlines) (st : iscan) : iscan :=
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
  | IClosed kids image o => IClosed kids image (oout_app base o)
  | ISpan kids image p src o => ISpan kids image p src (oout_app base o)
  | IAttr p src txt prev o => IAttr p src txt prev (oout_app base o)
  | INote esc image label o => INote esc image label (oout_app base o)
  | IReference kids image label o =>
      IReference kids image label (oout_app base o)
  | IDest kids image esc depth dst o =>
      IDest kids image esc depth dst (oout_app base o)
  | IAuto src txt o => IAuto src txt (oout_app base o)
  end.

Lemma oemit_app :
  forall n o base,
    oemit n (oout_app base o) = oout_app base (oemit n o).
Proof.
  intros n [out [|f stk]] base; reflexivity.
Qed.

Lemma flush_text_app :
  forall txt o base,
    flush_text txt (oout_app base o) = oout_app base (flush_text txt o).
Proof.
  intros txt o base. unfold flush_text.
  destruct (nonempty_str txt); [apply oemit_app | reflexivity].
Qed.

Lemma opush_app :
  forall k m o base,
    opush k m (oout_app base o) = oout_app base (opush k m o).
Proof. intros k m o base. reflexivity. Qed.

Lemma oclose_app :
  forall k m o base,
    oclose k m (oout_app base o)
    = option_map (oout_app base) (oclose k m o).
Proof.
  intros k m o base. unfold oclose. cbn [oout_app os_stk os_out].
  destruct (oclose_go k m [] (os_stk o)) as [[content rest]|]; [|reflexivity].
  cbn [option_map].
  rewrite <- (oemit_app (mk (dnode k (List.rev content)))
                (OState (os_out o) rest) base).
  reflexivity.
Qed.

Lemma bpush_app :
  forall image o base,
    bpush image (oout_app base o) = oout_app base (bpush image o).
Proof. intros image o base. reflexivity. Qed.

(* Taking a bracket back reads only the stack, which the suffix never
   touches. *)
Lemma bunpush_app :
  forall o base,
    bunpush (oout_app base o)
    = option_map (fun p => (fst p, oout_app base (snd p))) (bunpush o).
Proof.
  intros [out [|f stk]] base; [reflexivity|].
  destruct f as [[k|im] m [|n l]]; reflexivity.
Qed.

Lemma bclose_app :
  forall o base,
    bclose (oout_app base o)
    = option_map (fun p => (fst (fst p), snd (fst p),
                            oout_app base (snd p))) (bclose o).
Proof.
  intros o base. unfold bclose. cbn [oout_app os_stk os_out].
  destruct (bclose_go [] (os_stk o)) as [[[content image] rest]|]; reflexivity.
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
    + destruct base as [|[a [|p ps] i] base']; try reflexivity.
      cbn [starts_str] in Hb. destruct i; try reflexivity. discriminate.
    + destruct n as [a [|p ps] i]; try reflexivity.
      destruct i; reflexivity.
  - destruct (fr_out f) as [|n rest]; [reflexivity|].
    destruct n as [a [|p ps] i]; try reflexivity.
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

Lemma bdest_lit_app :
  forall kids image esc dst o base,
    base_ok base = true ->
    bdest_lit kids image esc dst (oout_app base o)
    = (fst (bdest_lit kids image esc dst o),
       oout_app base (snd (bdest_lit kids image esc dst o))).
Proof.
  intros kids image esc dst o base Hb. unfold bdest_lit.
  rewrite (bclosed_lit_app kids image o base Hb).
  destruct (bclosed_lit kids image o) as [txt o']; cbn [fst snd].
  apply bsplit_nl_app.
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
  destruct (bclosed_lit kids image o). reflexivity.
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
  destruct (Ascii.eqb c rbrack);
    [rewrite flush_text_app, bclose_app;
     destruct (bclose (flush_text txt o)) as [[[kids image] o']|]; reflexivity|].
  destruct (Ascii.eqb c hat && note_pos txt prev)%bool;
    [rewrite bunpush_app; destruct (bunpush o) as [[image o']|]; [reflexivity|]|];
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

(* The query that made `base_ok` worth carrying.  With something already
   emitted here the suffix is out of reach, as it is for every other
   transition; with nothing emitted the suffix's head is what `ocur`
   returns, and `base_ok` makes that a `SoftBreak` -- which `oattach`
   declines exactly as it declines an empty scope.  So the two sides
   agree in the one configuration where the splice is visible. *)
Lemma oattach_app :
  forall a o base,
    base_ok base = true ->
    oattach a (oout_app base o) = option_map (oout_app base) (oattach a o).
Proof.
  intros a [out [|f stk]] base Hb;
    unfold oattach, oout_app, ocur, oset_cur; cbn [os_out os_stk].
  - destruct out as [|[p a' v] out']; cbn [app].
    + destruct base as [|[bp ba bv] base']; [reflexivity|].
      destruct bv; try discriminate Hb; reflexivity.
    + destruct v; reflexivity.
  - destruct (fr_out f) as [|[p a' v] rest]; [reflexivity|].
    destruct v; reflexivity.
Qed.

Lemma iattr_attach_app :
  forall a src txt prev o base,
    base_ok base = true ->
    iattr_attach a src txt prev (oout_app base o)
    = iout_app base (iattr_attach a src txt prev o).
Proof.
  intros a src txt prev o base Hb. unfold iattr_attach.
  destruct (last_ws_split txt) as [pre w].
  destruct (nonempty_str w).
  - destruct a as [|kv a']; [reflexivity|].
    cbn [iout_app]. rewrite flush_text_app, oemit_app. reflexivity.
  - destruct (nonempty_str txt); [reflexivity|].
    rewrite (oattach_app a o base Hb).
    destruct (oattach a o) as [o'|]; reflexivity.
Qed.

Lemma iattr_feed_app :
  forall c p src txt prev o base,
    base_ok base = true ->
    iattr_feed c p src txt prev (oout_app base o)
    = iout_app base (iattr_feed c p src txt prev o).
Proof.
  intros c p src txt prev o base Hb. unfold iattr_feed.
  destruct (ap_failed (astep p c)); [apply ilead_app|].
  destruct (ap_done (astep p c)); [apply iattr_attach_app, Hb|reflexivity].
Qed.

Lemma ispan_feed_app :
  forall c kids image p src o base,
    base_ok base = true ->
    ispan_feed c kids image p src (oout_app base o)
    = iout_app base (ispan_feed c kids image p src o).
Proof.
  intros c kids image p src o base Hb. unfold ispan_feed.
  destruct (ap_failed (astep p c)).
  - rewrite (bspan_lit_app kids image src o base Hb).
    destruct (bspan_lit kids image src o) as [txt o']. apply ilead_app.
  - destruct (ap_done (astep p c)); [|reflexivity].
    cbn [iout_app]. rewrite ospan_bang_app by exact Hb.
    rewrite oemit_app. reflexivity.
Qed.

Lemma idelim_resolve_app :
  forall k txt bef marker next o base,
    idelim_resolve k txt bef marker next (oout_app base o)
    = iout_app base (idelim_resolve k txt bef marker next o).
Proof.
  intros k txt bef marker next o base.
  assert (Hdone : forall o', idelim_done k txt bef marker next (oout_app base o')
                             = iout_app base (idelim_done k txt bef marker next o')).
  { intros o'. unfold idelim_done.
    destruct (dbare k bef && negb marker && nonspace_at next)%bool;
      [cbn [iout_app]; rewrite flush_text_app, opush_app|]; reflexivity. }
  unfold idelim_resolve. destruct (nonspace_at bef || marker)%bool; [|apply Hdone].
  rewrite flush_text_app, oclose_app.
  destruct (oclose k marker (flush_text txt o)); [reflexivity | apply Hdone].
Qed.

Lemma iresolve_app :
  forall base st,
    base_ok base = true ->
    iresolve (iout_app base st) = iout_app base (iresolve st).
Proof.
  intros base [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|nesc nimg nlab nob|kids img esc depth dst ob|asrc atxt aob] Hb;
    try reflexivity.
  - cbn [iresolve iout_app]. destruct (Nat.ltb (S seen) (dwidth k));
      [reflexivity | apply idelim_resolve_app].
  - cbn [iresolve iout_app]. rewrite (bclosed_lit_app kids img ob base Hb).
    destruct (bclosed_lit kids img ob) as [txt o']. reflexivity.
Qed.

Lemma idelim_marked_out_app :
  forall k extra txt base o,
    idelim_marked k extra txt (oout_app base o)
    = iout_app base (idelim_marked k extra txt o).
Proof.
  intros k extra txt base o. unfold idelim_marked.
  destruct (Nat.ltb (S extra) (dwidth k)); cbn [iout_app]; [reflexivity|].
  rewrite flush_text_app, opush_app. reflexivity.
Qed.

Lemma istep_out_app :
  forall c base st,
    base_ok base = true ->
    istep c (iout_app base st) = iout_app base (istep c st).
Proof.
  intros c base [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|nesc nimg nlab nob|kids img esc depth dst ob|asrc atxt aob] Hb;
    cbn [iout_app istep].
  - destruct (is_ws c); reflexivity.
  - apply ilead_app.
  - destruct (is_ws c); [reflexivity|].
    rewrite iescws_resolve_app by exact Hb.
    destruct (iescws_resolve ews etxt eprev eob) as [[t p] o']; cbn [fst snd].
    apply ilead_app.
  - unfold ibrace_step. destruct (dstyle_of c);
      [apply idelim_marked_out_app|apply iattr_feed_app, Hb].
  - destruct (Nat.ltb (S seen) (dwidth k)).
    { destruct (Ascii.eqb c (dchar k)); [|apply ilead_app].
      destruct mrk; [apply idelim_marked_out_app|reflexivity]. }
    rewrite idelim_resolve_app. destruct (Ascii.eqb c rbrace); [reflexivity|].
    destruct (idelim_resolve k txt cc false (Some c) o)
      as [[] txt' prev' o'|? ? ? ?|? ? ?|? ? ? ? ? ?|? ? ?|? ? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ?|? ? ?|? ? ?|? ? ? ? ?|? ? ? ? ?|? ? ? ?|? ? ? ?|? ? ? ? ? ?|? ? ?]; cbn [iout_app];
      try reflexivity.
    apply ilead_app.
  - destruct (is_tick c); reflexivity.
  - destruct (is_tick c); [reflexivity|].
    destruct (Nat.eqb run n); [|reflexivity].
    rewrite (oemit_app (mk (vnode vk (trim_verb txt))) o base).
    apply ilead_app.
  - (* a pending `$` either grows, opens a math span, or is text *)
    unfold idollar_step. destruct (Ascii.eqb c dollar);
      [destruct dtwo; reflexivity|].
    destruct (is_tick c); [cbn [iout_app]; rewrite flush_text_app; reflexivity|].
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
  - destruct (Ascii.eqb c lparen); [reflexivity|].
    destruct (Ascii.eqb c lbrack); [reflexivity|].
    destruct (Ascii.eqb c lbrace); [reflexivity|].
    rewrite (bclosed_lit_app kids img ob base Hb).
    destruct (bclosed_lit kids img ob) as [txt o']. apply ilead_app.
  - apply ispan_feed_app, Hb.
  - apply iattr_feed_app, Hb.
  - destruct (Ascii.eqb c rbrack); [cbn [iout_app]; rewrite oemit_app|];
      reflexivity.
  - unfold inote_step. destruct nesc; [reflexivity|].
    destruct (is_bslash c); [reflexivity|].
    destruct (Ascii.eqb c rbrack); [|reflexivity].
    cbn [iout_app]. rewrite ospan_bang_app by exact Hb.
    rewrite oemit_app. reflexivity.
  - destruct esc; [reflexivity|].
    destruct (is_bslash c); [reflexivity|].
    destruct (Ascii.eqb c lparen); [reflexivity|].
    destruct (Ascii.eqb c rparen); [|reflexivity].
    destruct depth; [cbn [iout_app]; rewrite oemit_app|]; reflexivity.
  - unfold iauto_step.
    destruct (Ascii.eqb c gt && auto_body_ok asrc && auto_kind_ok asrc)%bool;
      [cbn [iout_app]; rewrite flush_text_app, oemit_app; reflexivity|].
    destruct (Ascii.eqb c gt || is_ws c || Ascii.eqb c lt)%bool;
      [apply ilead_app | reflexivity].
Qed.

Lemma iscan_str_out_app :
  forall s base st,
    base_ok base = true ->
    iscan_str s (iout_app base st) = iout_app base (iscan_str s st).
Proof.
  induction s as [|c s IH]; intros base st Hb; cbn [iscan_str]; [reflexivity|].
  rewrite istep_out_app by exact Hb. apply IH, Hb.
Qed.

Lemma ibreak_out_app :
  forall base st,
    base_ok base = true ->
    ibreak (iout_app base st) = iout_app base (ibreak st).
Proof.
  intros base st Hb. unfold ibreak. rewrite iresolve_app by exact Hb.
  destruct (iresolve st) as [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|nesc nimg nlab nob|kids img esc depth dst ob|asrc atxt aob];
    cbn [iout_app]; try reflexivity.
  all: try (try unfold iesc_hard;
            rewrite flush_text_app, oemit_app; reflexivity).
  - destruct (Nat.eqb run n); [|reflexivity].
    rewrite !oemit_app. reflexivity.
  - apply ispan_feed_app, Hb.
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
   it; the `_app` lemmas carry the stronger fact because `oattach` reads
   the head rather than merely declining to merge with it. *)
Lemma osnoc_nonstr :
  forall n out, starts_str out = false -> osnoc n out = (n :: out)%list.
Proof.
  intros n [|[a [|x xs] i] out'] H; try reflexivity.
  cbn [starts_str] in H. destruct n as [c [|y ys] j]; destruct i;
    try reflexivity; discriminate.
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
    + destruct x as [a [|p ps] i]; [|reflexivity].
      destruct i; try reflexivity.
      destruct n as [c [|q qs] j]; [|reflexivity]. destruct j; reflexivity.
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

Lemma ofinish_out_app :
  forall base o,
    base_ok base = true ->
    ofinish (oout_app base o) = (ofinish o ++ base)%list.
Proof.
  intros base o Hb. unfold ofinish, oout_app; cbn [os_out os_stk].
  apply oflatten_app, Hb.
Qed.

Lemma ifinish_rev_out_app :
  forall base st,
    base_ok base = true ->
    ifinish_rev (iout_app base st) = (ifinish_rev st ++ base)%list.
Proof.
  intros base st Hb. unfold ifinish_rev, ifinish_ostate.
  rewrite iresolve_app by exact Hb.
  destruct (iresolve st) as [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|nesc nimg nlab nob|kids img esc depth dst ob|asrc atxt aob];
    cbn [iout_app].
  1,3: unfold iesc_hard; rewrite flush_text_app, oemit_app;
       apply ofinish_out_app, Hb.
  1: rewrite flush_text_app; apply ofinish_out_app, Hb.
  1,2: apply ofinish_out_app, Hb.
  1,2: rewrite oemit_app; apply ofinish_out_app, Hb.
  all: try (apply ofinish_out_app, Hb).
  - rewrite (bspan_lit_app kids img ssrc sob base Hb).
    destruct (bspan_lit kids img ssrc sob) as [txt o']; cbn [fst snd].
    rewrite flush_text_app. apply ofinish_out_app, Hb.
  - rewrite (bref_lit_app kids img label ob base Hb).
    destruct (bref_lit kids img label ob) as [txt o']; cbn [fst snd].
    rewrite flush_text_app. apply ofinish_out_app, Hb.
  - rewrite (bnote_lit_app nesc nimg nlab nob base Hb).
    destruct (bnote_lit nesc nimg nlab nob) as [txt o']; cbn [fst snd].
    rewrite flush_text_app. apply ofinish_out_app, Hb.
  - rewrite (bdest_lit_app kids img esc dst ob base Hb).
    destruct (bdest_lit kids img esc dst ob) as [txt o']; cbn [fst snd].
    rewrite flush_text_app. apply ofinish_out_app, Hb.
  - rewrite flush_text_app. apply ofinish_out_app, Hb.
Qed.

Lemma ifinish_out_app :
  forall base st,
    base_ok base = true ->
    ifinish (iout_app base st) = (List.rev base ++ ifinish st)%list.
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
    ifinish (IText false txt prev (OState out []))
    = List.rev (os_out (flush_text txt (OState out []))).
Proof.
  intros txt prev out. unfold ifinish, ifinish_rev, ifinish_ostate, iresolve.
  unfold flush_text, oemit; cbn [os_stk os_out].
  destruct (nonempty_str txt); reflexivity.
Qed.

(* Canonical text never opens a verbatim: `needs_escape` claims the
   backtick, so `escape_str` emits none bare.  The scanner therefore
   stays in `IText` throughout, and this is the whole of what the
   roundtrip needs from it today. *)
Lemma ilead_plain :
  forall c txt prev o,
    needs_escape c = false ->
    ilead c txt prev o = IText false (txt ++ one c)%string prev o.
Proof.
  intros c txt prev o Hc. unfold needs_escape in Hc.
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
    = IText false (txt ++ s)%string prev o.
Proof.
  induction s as [|c rest IH]; intros txt prev o.
  - cbn [escape_str iscan_str]. rewrite append_empty_r. reflexivity.
  - cbn [escape_str]. destruct (needs_escape c) eqn:Hc.
    + cbn [iscan_str istep]. unfold ilead.
      change (is_bslash "\"%char) with true. cbn [iscan_str istep].
      rewrite (is_punct_not_ws c (needs_escape_punct c Hc)),
              (needs_escape_punct c Hc).
      rewrite IH, append_assoc. reflexivity.
    + cbn [iscan_str istep]. rewrite (ilead_plain c txt prev o Hc).
      rewrite IH, append_assoc. reflexivity.
Qed.

Lemma iscan_escape_after_verb :
  forall s n body vk o,
    nonempty_str s = true ->
    iscan_str (escape_str s) (IVerb n n body vk o)
    = IText false s (Some tick) (oemit (mk (vnode vk (trim_verb body))) o).
Proof.
  intros [|c rest] n body vk o Hne; [discriminate|].
  cbn [escape_str]. destruct (needs_escape c) eqn:Hc.
  - cbn [iscan_str istep].
    change (is_tick "\"%char) with false. rewrite nat_eqb_refl.
    unfold ilead at 1. change (is_bslash "\"%char) with true.
    cbn [iscan_str istep].
    rewrite (is_punct_not_ws c (needs_escape_punct c Hc)),
            (needs_escape_punct c Hc), iscan_escape.
    cbn [append one]. reflexivity.
  - cbn [iscan_str istep].
    replace (is_tick c) with false
      by (destruct (is_tick c) eqn:Ht;
          [rewrite (needs_escape_tick c Ht) in Hc; discriminate|reflexivity]).
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
  destruct r as [t|v|k kids|img kids dst|rimg rkids rlabel|label|a];
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
    = IDelim k 0 txt (str_last txt prev) false o.
Proof.
  intros k txt prev o Hen Hhy Hup.
  destruct (dreserved_false (dchar k) (dchar_free k))
    as [Hb [Ht [Hlb [Hrb [Hlk [Hrk [Hbg [Hdol [Hpd Hlt]]]]]]]]].
  unfold ilead.
  rewrite Hb, Ht, Hdol, Hpd, Hhy, Hlb, Hlt, Hlk, Hrk, Hbg, Hup.
  rewrite (dstyle_of_dchar k Hen). destruct (_ && _)%bool; reflexivity.
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
  - cbn [chars iscan_str istep].
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
    = IDelim k (pred (dwidth k)) txt (str_last txt prev) false o.
Proof.
  intros k txt prev o Hen Hhy Hup. unfold dtoken.
  destruct (dwidth k) as [|w] eqn:Ew; [destruct (dwidth_nonzero k Ew)|].
  cbn [chars iscan_str istep]. rewrite (ilead_dchar k _ _ _ Hen Hhy Hup).
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
  - cbn [chars iscan_str istep]. unfold idash_step.
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
  intros n txt prev o. cbn [chars iscan_str istep].
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
    oclose k true (flush_text txt o) = Some o' ->
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
    unfold one. cbn [iscan_str istep]. unfold idash_step.
    change (Ascii.eqb rbrace hyphen) with false.
    rewrite Ascii.eqb_refl, <- Hhy, (dstyle_of_dchar k Hen), Ew.
    rewrite Nat.leb_refl, Nat.sub_diag.
    change (dashes 0) with EmptyString. rewrite (append_empty_r txt).
    unfold idelim_resolve. rewrite Bool.orb_true_r, H. reflexivity. }
  rewrite iscan_str_app, (iscan_dtoken k txt prev o Hen Hhy Hup).
  unfold one. cbn [iscan_str istep].
  replace (Nat.ltb (S (pred (dwidth k))) (dwidth k)) with false
    by (symmetry; apply Nat.ltb_ge; lia).
  rewrite Ascii.eqb_refl. unfold idelim_resolve.
  rewrite Bool.orb_true_r, H. reflexivity.
Qed.

(* Where the token lemmas get their hypothesis: a marked close runs with
   the delimiter's own frame on top, which is not a bracket, and nothing
   the close does before the token can turn it into one. *)
Lemma bunpush_oemit_all_opush :
  forall ns k m o, bunpush (oemit_all ns (opush k m o)) = None.
Proof.
  intros ns k m [out stk]. unfold opush; cbn [os_out os_stk].
  rewrite oemit_all_frame. reflexivity.
Qed.

Lemma bunpush_flush :
  forall txt o, bunpush o = None -> bunpush (flush_text txt o) = None.
Proof.
  intros txt [out [|[[k|im] m [|n l]] stk]] H; unfold flush_text;
    destruct (nonempty_str txt); solve [exact H | reflexivity | discriminate H].
Qed.

Lemma iscan_marked_flush :
  forall k tail txt prev before base,
    denabled_of k = true ->
    (nonempty before || nonempty_str txt)%bool = true ->
    exists p,
      iscan_str (marked_close k tail)
        (IText false txt prev (oemit_all before (opush k true base)))
      = iscan_str (marked_close k tail)
          (IText false EmptyString p
            (flush_text txt (oemit_all before (opush k true base)))).
Proof.
  intros k tail txt prev before base Hen Hne.
  assert (Hclose : exists o',
    oclose k true
      (flush_text txt (oemit_all before (opush k true base))) = Some o').
  { destruct (nonempty_str txt) eqn:Htxt.
    - exists (oemit (mk (dnode k (before ++ [mk (Str txt)])%list)) base).
      unfold flush_text. rewrite Htxt.
      change (oclose k true
                (oemit_all [mk (Str txt)]
                  (oemit_all before (opush k true base)))
              = Some
                  (oemit (mk (dnode k (before ++ [mk (Str txt)])%list))
                    base)).
      rewrite <- (oemit_all_app before [mk (Str txt)] (opush k true base)).
      cbn [oemit_all]. apply oclose_oemit_all_marked. destruct before; reflexivity.
    - apply orb_true_iff in Hne as [Hbefore|Htxt']; [|discriminate].
      exists (oemit (mk (dnode k before)) base).
      unfold flush_text. rewrite Htxt.
      apply oclose_oemit_all_marked, Hbefore. }
  destruct Hclose as [o' Hclose]. exists prev.
  unfold marked_close. rewrite <- append_assoc.
  rewrite !(iscan_str_app (dtoken k ++ one rbrace) tail).
  pose proof (bunpush_oemit_all_opush before k true base) as Hup.
  rewrite (iscan_marked_close_step k txt prev
             (oemit_all before (opush k true base)) o' Hen Hup Hclose).
  rewrite (iscan_marked_close_step k EmptyString prev
             (flush_text txt (oemit_all before (opush k true base))) o' Hen
             (bunpush_flush txt _ Hup)
             ltac:(cbn [flush_text]; exact Hclose)).
  reflexivity.
Qed.

(* The rest of a marked open's token, and the push that ends it.  The
   counterpart of `iscan_chars_delim` for a token that decides its role
   on arrival rather than on the byte after. *)
Lemma iscan_chars_marked :
  forall n k extra txt o,
    S extra + n = dwidth k ->
    iscan_str (chars (dchar k) n) (idelim_marked k extra txt o)
    = IText false EmptyString (Some (dchar k)) (opush k true (flush_text txt o)).
Proof.
  induction n as [|n IH]; intros k extra txt o Hn.
  - cbn [chars iscan_str]. unfold idelim_marked.
    replace (Nat.ltb (S extra) (dwidth k)) with false
      by (symmetry; apply Nat.ltb_ge; lia).
    reflexivity.
  - unfold idelim_marked at 1.
    replace (Nat.ltb (S extra) (dwidth k)) with true
      by (symmetry; apply Nat.ltb_lt; lia).
    cbn [chars iscan_str istep].
    replace (Nat.ltb (S extra) (dwidth k)) with true
      by (symmetry; apply Nat.ltb_lt; lia).
    rewrite Ascii.eqb_refl. apply IH. lia.
Qed.

Lemma iscan_marked_open :
  forall d txt prev o,
    denabled_of d = true ->
    iscan_str (marked_open d) (IText false txt prev o)
    = IText false EmptyString (Some (dchar d))
        (opush d true (flush_text txt o)).
Proof.
  intros d txt prev o Hen. unfold marked_open, dtoken.
  destruct (dwidth d) as [|w] eqn:Ew;
    [destruct (dwidth_nonzero d Ew)|].
  unfold one. cbn [chars append iscan_str istep].
  change (ilead lbrace txt prev o) with (IBrace txt prev o).
  cbn [istep]. unfold ibrace_step. rewrite (dstyle_of_dchar d Hen).
  apply (iscan_chars_marked w d 0 txt o). lia.
Qed.

Lemma iscan_marked_close_emit :
  forall d tail ns base p,
    denabled_of d = true ->
    nonempty ns = true ->
    iscan_str (marked_close d tail)
      (IText false EmptyString p (oemit_all ns (opush d true base)))
    = iscan_str tail
        (IText false EmptyString (Some rbrace)
          (oemit (mk (dnode d ns)) base)).
Proof.
  intros d tail ns base p Hen Hne. unfold marked_close.
  rewrite <- append_assoc, iscan_str_app.
  rewrite (iscan_marked_close_step d EmptyString p
             (oemit_all ns (opush d true base))
             (oemit (mk (dnode d ns)) base)
             Hen
             (bunpush_oemit_all_opush ns d true base)
             ltac:(cbn [flush_text]; apply oclose_oemit_all_marked, Hne)).
  reflexivity.
Qed.

Lemma iscan_after_verb_nontick :
  forall s n body vk o,
    nonempty_str s = true -> starts_tick s = false ->
    iscan_str s (IVerb n n body vk o)
    = iscan_str s
        (IText false EmptyString (Some tick)
          (oemit (mk (vnode vk (trim_verb body))) o)).
Proof.
  intros [|c s] n body vk o Hne Htick; [discriminate|].
  cbn [starts_tick] in Htick. cbn [iscan_str istep]. rewrite Htick.
  rewrite nat_eqb_refl. reflexivity.
Qed.

Lemma escape_str_starts_nontick :
  forall s, nonempty_str s = true -> starts_tick (escape_str s) = false.
Proof.
  intros [|c s] H; [discriminate|]. cbn [escape_str].
  destruct (needs_escape c) eqn:Hc; [reflexivity|].
  cbn [starts_tick]. destruct (is_tick c) eqn:Ht; [|reflexivity].
  rewrite (needs_escape_tick c Ht) in Hc. discriminate.
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
            then (before ++ [mk (Str txt)])%list else before, image, base).
Proof.
  intros txt image before base. unfold flush_text.
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
  forall s kids image depth dst o,
    iscan_str (escape_dest s) (IDest kids image false depth dst o)
    = IDest kids image false depth (dst ++ s)%string o.
Proof.
  induction s as [|c s IH]; intros kids image depth dst o;
    cbn [escape_dest]; [rewrite append_empty_r; reflexivity|].
  assert (Hsplit : forall t, (dst ++ String c t)%string
                             = ((dst ++ one c) ++ t)%string).
  { intro t. rewrite (append_assoc dst (one c) t). reflexivity. }
  destruct (needs_escape_dest c) eqn:Hc.
  - pose proof (needs_escape_dest_punct c Hc) as Hp.
    cbn [iscan_str istep]. change (is_bslash "\"%char) with true.
    cbn [istep]. rewrite Hp, IH, Hsplit. reflexivity.
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
    cbn [iscan_str istep]. rewrite Hbs, Hlp, Hrp, IH, Hsplit. reflexivity.
Qed.

Lemma istep_rbrack_close :
  forall txt prev o kids image o',
    bclose (flush_text txt o) = Some (kids, image, o') ->
    istep rbrack (IText false txt prev o) = IClosed kids image o'.
Proof.
  intros txt prev o kids image o' H. cbn [istep]. unfold ilead.
  change (is_bslash rbrack) with false.
  change (is_tick rbrack) with false.
  change (Ascii.eqb rbrack lbrace) with false.
  change (Ascii.eqb rbrack bang) with false.
  change (Ascii.eqb rbrack lbrack) with false.
  change (Ascii.eqb rbrack rbrack) with true.
  rewrite H. reflexivity.
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
  cbn [iscan_str].
  rewrite (istep_rbrack_close EmptyString p _ ns image base
             (bclose_flush_bpush EmptyString image ns base)).
  cbn [istep]. change (Ascii.eqb lparen lparen) with true.
  rewrite iscan_str_app, iscan_dest_escape.
  change ((EmptyString ++ dst)%string) with dst.
  cbn [iscan_str istep].
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
  rewrite (istep_rbrack_close txt prev _ ns image base
             (bclose_flush_bpush txt image before base)).
  rewrite (istep_rbrack_close EmptyString (Some lbrack)
             (flush_text txt (oemit_all before (bpush image base)))
             ns image base);
    [reflexivity|].
  cbn [flush_text nonempty_str].
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
  forall label kids image acc o,
    no_char rbrack label = true ->
    iscan_str label (IReference kids image acc o)
    = IReference kids image (acc ++ label)%string o.
Proof.
  induction label as [|c label IH]; intros kids image acc o H;
    [rewrite append_empty_r; reflexivity|].
  cbn [no_char] in H. apply andb_true_iff in H as [Hc H].
  apply negb_true_iff in Hc.
  cbn [iscan_str istep]. rewrite Hc, (IH _ _ _ _ H).
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
  cbn [iscan_str].
  rewrite (istep_rbrack_close EmptyString p _ ns image base
             (bclose_flush_bpush EmptyString image ns base)).
  cbn [istep]. change (Ascii.eqb lbrack lparen) with false.
  change (Ascii.eqb lbrack lbrack) with true.
  rewrite iscan_str_app, (iscan_ref_label label ns image EmptyString _ Hbr).
  change ((EmptyString ++ label)%string) with label.
  cbn [iscan_str istep]. change (Ascii.eqb rbrack rbrack) with true.
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
  rewrite (istep_rbrack_close txt prev _ ns image base
             (bclose_flush_bpush txt image before base)).
  rewrite (istep_rbrack_close EmptyString (Some lbrack)
             (flush_text txt (oemit_all before (bpush image base)))
             ns image base);
    [reflexivity|].
  cbn [flush_text nonempty_str].
  apply (bclose_flush_bpush txt image before base).
Qed.

(* A canonical note label reaches its closing bracket without leaving an
   escape pending.  Backslashes are consumed in pairs with the following
   byte, and both bytes remain in the label. *)
Lemma iscan_note_label :
  forall label tail esc image acc o,
    note_label_safe_from esc label = true ->
    iscan_str (label ++ one rbrack ++ tail)
      (INote esc image acc o)
    = iscan_str tail
        (IText false EmptyString (Some rbrack)
          (oemit (mk (FootnoteReference
            (normalize_label
              (acc ++ (if esc then one bslash else EmptyString) ++ label))))
            (ospan_bang image o))).
Proof.
  induction label as [|c label IH]; intros tail esc image acc o Hsafe.
  - cbn [note_label_safe_from] in Hsafe. destruct esc; [discriminate|].
    cbn [append iscan_str istep inote_step].
    change (is_bslash rbrack) with false.
    change (Ascii.eqb rbrack rbrack) with true.
    rewrite !append_empty_r. reflexivity.
  - cbn [note_label_safe_from] in Hsafe.
    cbn [append iscan_str istep inote_step].
    destruct esc.
    + cbn [inote_step].
      rewrite (IH tail false image (acc ++ one bslash ++ one c)%string o
                 Hsafe).
      rewrite !append_assoc. reflexivity.
    + destruct (Ascii.eqb c rbrack) eqn:Hclose; [discriminate|].
      destruct (is_bslash c) eqn:Hslash.
      * unfold is_bslash in Hslash. apply Ascii.eqb_eq in Hslash. subst c.
        cbn [inote_step].
        rewrite is_bslash_bslash.
        rewrite (IH tail true image acc o Hsafe).
        cbn [append]. reflexivity.
      * cbn [inote_step]. rewrite Hslash, Hclose.
        rewrite (IH tail false image (acc ++ one c)%string o Hsafe).
        rewrite !append_assoc. reflexivity.
Qed.

Lemma iscan_note_text :
  forall label tail txt prev o,
    note_label_safe label = true ->
    iscan_str (note_text label ++ tail)
      (IText false txt prev o)
    = iscan_str tail
        (IText false EmptyString (Some rbrack)
          (oemit (mk (FootnoteReference (normalize_label label)))
            (flush_text txt o))).
Proof.
  intros label tail txt prev o Hsafe.
  replace (note_text label ++ tail)%string with
    (bracket_open false ++ (one hat ++ (label ++ one rbrack ++ tail)))%string
    by (unfold note_text, bracket_open; cbn [append];
        rewrite append_assoc; reflexivity).
  rewrite iscan_str_app, iscan_bracket_open.
  rewrite iscan_str_app. cbn [one iscan_str istep].
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
  rewrite bunpush_bpush.
  rewrite (iscan_note_label label tail false false EmptyString
             (flush_text txt o) Hsafe).
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
    cbn [iscan_str istep]. unfold iauto_step.
    rewrite Hgtc. cbn [andb orb].
    unfold is_ws_nl in Hwsc. apply orb_false_iff in Hwsc as [Hwsc _].
    rewrite Hwsc, Hltc. cbn [orb].
    rewrite (IH (acc ++ one c)%string txt o)
      by (unfold auto_region; rewrite Hws, Hlt, Hgt; reflexivity).
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
  unfold auto_text. cbn [append iscan_str istep].
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
  cbn [one append iscan_str istep]. unfold iauto_step.
  change (Ascii.eqb gt gt) with true.
  rewrite Hbody, Hkind. reflexivity.
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
    nonempty_str (ci_text rest ++ cl) = true /\
    starts_tick (ci_text rest ++ cl) = false.
Proof.
  intros v [|c rest] cl Hok Hcl Hct.
  - cbn [ci_text append]. split; assumption.
  - destruct c as [s|w|d kids|img kids dst|rimg rkids rlabel|label|a].
    + pose proof (cis_ok_head (CIStr s) rest (cis_ok_tail _ _ Hok)) as Hs.
      cbn [ci_ok] in Hs. apply andb_true_iff in Hs as [Hs _].
      cbn [ci_text ci_src]. split.
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
    + unfold cis_ok in Hok. cbn [ci_sep_ok ci_pair_ok] in Hok.
      repeat rewrite andb_false_r in Hok. discriminate.
    + cbn [ci_text]. rewrite ci_src_delim.
      cbn [append starts_tick]. split; reflexivity.
    + cbn [ci_text]. rewrite ci_src_link. unfold bracket_open.
      destruct img; cbn [append starts_tick]; split; reflexivity.
    + cbn [ci_text]. rewrite ci_src_ref. unfold bracket_open.
      destruct rimg; cbn [append starts_tick]; split; reflexivity.
    + cbn [ci_text ci_src note_text append starts_tick]. split; reflexivity.
    + cbn [ci_text ci_src auto_text append starts_tick]. split; reflexivity.
Qed.

Lemma after_verb_rest_nontick :
  forall v c rest,
    cis_ok (CIVerb v :: c :: rest) = true ->
    nonempty_str (ci_text (c :: rest)) = true /\
    starts_tick (ci_text (c :: rest)) = false.
Proof.
  intros v c rest Hok.
  (* any nonempty closer that is not a backtick will do, and taking one
     off the table keeps this independent of which rows exist *)
  destruct (after_verb_source_nontick v (c :: rest) (one rbrace) Hok
              eq_refl eq_refl)
    as [Hne Htick].
  destruct c as [s|w|d kids|img kids dst|rimg rkids rlabel|label|a].
  - pose proof (cis_ok_head (CIStr s) rest (cis_ok_tail _ _ Hok)) as Hs.
    cbn [ci_ok] in Hs. apply andb_true_iff in Hs as [Hs _].
    cbn [ci_text ci_src]. split.
    + destruct (escape_str s) eqn:E;
        [pose proof (escape_str_nonempty s Hs); rewrite E in H; discriminate
        |reflexivity].
    + rewrite starts_tick_app_l;
        [apply escape_str_starts_nontick, Hs|apply escape_str_nonempty, Hs].
  - unfold cis_ok in Hok. cbn [ci_sep_ok ci_pair_ok] in Hok.
    repeat rewrite andb_false_r in Hok. discriminate.
  - cbn [ci_text]. rewrite ci_src_delim. cbn [starts_tick nonempty_str].
    split; reflexivity.
  - cbn [ci_text]. rewrite ci_src_link. unfold bracket_open.
    destruct img; cbn [append starts_tick nonempty_str]; split; reflexivity.
  - cbn [ci_text]. rewrite ci_src_ref. unfold bracket_open.
    destruct rimg; cbn [append starts_tick nonempty_str]; split; reflexivity.
  - cbn [ci_text ci_src note_text append starts_tick nonempty_str].
    split; reflexivity.
  - cbn [ci_text ci_src auto_text append starts_tick nonempty_str].
    split; reflexivity.
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
  clear cis. intros cis IH cl O empty_ok txt prev before Hcl Hct Hflush Hok Hsep Hne.
  destruct cis as [|c rest].
  - cbn [ci_text ci_inlines map append nonempty] in Hne |- *.
    apply Hflush. rewrite <- Hne. destruct (nonempty before), (nonempty_str txt);
      reflexivity.
  - destruct c as [s|v|d kids|img kids dst|rimg rkids rlabel|label|a].
    + destruct txt as [|x txt']; [|discriminate].
      pose proof (cis_ok_head (CIStr s) rest Hok) as Hsok.
      cbn [ci_ok] in Hsok. apply andb_true_iff in Hsok as [Hs _].
      assert (Hlt : ltof (list cinline) cis_size rest (CIStr s :: rest)).
      { unfold ltof. cbn [cis_size ci_size]. lia. }
      pose proof (IH rest Hlt cl O empty_ok s prev before Hcl Hct Hflush
        (cis_ok_tail _ _ Hok) (ci_str_tail_sep s rest Hok Hs)) as IHr.
      assert (Hnr : nonempty before || nonempty_str s || nonempty rest
                    || empty_ok = true).
      { rewrite Hs, orb_true_r. reflexivity. }
      destruct (IHr Hnr) as [p Ep]. exists p.
      cbn [ci_text ci_src ci_inlines map append].
      rewrite append_assoc, iscan_str_app, iscan_escape.
      change (EmptyString ++ s)%string with s. rewrite Ep.
      unfold flush_text at 1 2. cbn [nonempty_str ci_ast mk oemit_all].
      rewrite Hs. reflexivity.
    + pose proof (ci_verb_nonempty v rest Hok) as Hvne.
      pose proof (ci_verb_content_ok v rest Hok) as Hvok.
      destruct (after_verb_source_nontick v rest cl Hok Hcl Hct)
        as [Hsrcne Hsrctick].
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
                 Hcl Hct Hflush (cis_ok_tail _ _ Hok) eq_refl).
        rewrite Hpre. reflexivity. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [mk (Verbatim v)])%list
                    ltac:(destruct before; reflexivity)) as [p Ep].
        exists p.
        cbn [ci_text ci_src ci_inlines map]. rewrite append_assoc, iscan_str_app.
        rewrite iscan_verb_text_nonempty by auto using verb_content_safe.
        cbn [flush_text nonempty_str].
        rewrite (iscan_after_verb_nontick _ _ _ _ _ Hsrcne Hsrctick),
          trim_verb_pad by exact Hvok. cbn [vnode].
        rewrite oemit_all_app in Ep.
        cbn [oemit_all flush_text nonempty_str] in Ep.
        rewrite Ep. cbn [oemit_all ci_ast]. reflexivity.
      * destruct (Hstep (before ++ [mk (Str (String x txt')); mk (Verbatim v)])%list
                    ltac:(destruct before; reflexivity)) as [p Ep].
        exists p.
        cbn [ci_text ci_src ci_inlines map]. rewrite append_assoc, iscan_str_app.
        rewrite iscan_verb_text_nonempty by auto using verb_content_safe.
        cbn [flush_text nonempty_str].
        rewrite (iscan_after_verb_nontick _ _ _ _ _ Hsrcne Hsrctick),
          trim_verb_pad by exact Hvok. cbn [vnode].
        rewrite oemit_all_app in Ep.
        cbn [oemit_all flush_text nonempty_str] in Ep.
        rewrite Ep. cbn [oemit_all ci_ast]. reflexivity.
    + pose proof (cis_ok_head (CIDelim d kids) rest Hok) as Hdk.
      rewrite ci_ok_delim in Hdk. apply andb_true_iff in Hdk as [Hdk Hkidsok].
      apply andb_true_iff in Hdk as [Hden Hkidsne].
      assert (Hkidslt :
        ltof (list cinline) cis_size kids (CIDelim d kids :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_delim. lia. }
      pose proof (IH kids Hkidslt (marked_close d (ci_text rest ++ cl))
        (opush d true (flush_text txt (oemit_all before O))) false
        EmptyString (Some (dchar d)) []
        (marked_close_nonempty _ _) (marked_close_starts_nontick _ _)
        (fun txt' prev' before' e =>
           iscan_marked_flush d (ci_text rest ++ cl) txt' prev' before'
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
                 Hcl Hct Hflush (cis_ok_tail _ _ Hok) eq_refl).
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
        rewrite append_assoc, Hsrc, iscan_str_app, (iscan_marked_open _ _ _ _ Hden).
        cbn [flush_text nonempty_str oemit_all] in Ekids |- *. rewrite Ekids.
        rewrite (iscan_marked_close_emit d _ (ci_inlines kids) _ pk Hden Hkins).
        rewrite <- ci_ast_delim. rewrite oemit_all_app in Erest.
        cbn [flush_text nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text nonempty_str oemit_all]. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CIDelim d kids)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_delim.
        rewrite append_assoc, Hsrc, iscan_str_app, (iscan_marked_open _ _ _ _ Hden).
        cbn [flush_text nonempty_str oemit_all] in Ekids |- *. rewrite Ekids.
        rewrite (iscan_marked_close_emit d _ (ci_inlines kids) _ pk Hden Hkins).
        rewrite <- ci_ast_delim. rewrite oemit_all_app in Erest.
        cbn [flush_text nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text nonempty_str oemit_all]. reflexivity.
    + pose proof (cis_ok_head (CILink img kids dst) rest Hok) as Hdk.
      rewrite ci_ok_link in Hdk. apply andb_true_iff in Hdk as [Hnl Hkidsok].
      assert (Hkidslt :
        ltof (list cinline) cis_size kids (CILink img kids dst :: rest)).
      { unfold ltof. cbn [cis_size]. rewrite ci_size_link. lia. }
      pose proof (IH kids Hkidslt (link_close dst (ci_text rest ++ cl))
        (bpush img (flush_text txt (oemit_all before O))) true
        EmptyString (Some lbrack) []
        (link_close_nonempty _ _) (link_close_starts_nontick _ _)
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
                 Hcl Hct Hflush (cis_ok_tail _ _ Hok) eq_refl).
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
        cbn [flush_text nonempty_str oemit_all] in Ekids |- *. rewrite Ekids.
        rewrite (iscan_link_close dst _ (ci_inlines kids) img _ pk Hnl).
        rewrite <- ci_ast_link. rewrite oemit_all_app in Erest.
        cbn [flush_text nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text nonempty_str oemit_all]. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CILink img kids dst)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_link.
        rewrite append_assoc, Hsrc, iscan_str_app, iscan_bracket_open.
        cbn [flush_text nonempty_str oemit_all] in Ekids |- *. rewrite Ekids.
        rewrite (iscan_link_close dst _ (ci_inlines kids) img _ pk Hnl).
        rewrite <- ci_ast_link. rewrite oemit_all_app in Erest.
        cbn [flush_text nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text nonempty_str oemit_all]. reflexivity.
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
        (ref_close_nonempty _ _) (ref_close_starts_nontick _ _)
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
                 Hcl Hct Hflush (cis_ok_tail _ _ Hok) eq_refl).
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
        cbn [flush_text nonempty_str oemit_all] in Ekids |- *. rewrite Ekids.
        rewrite (iscan_ref_close rlabel _ (ci_inlines rkids) rimg _ pk Hne' Hbr),
                Hnorm.
        rewrite <- ci_ast_ref. rewrite oemit_all_app in Erest.
        cbn [flush_text nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text nonempty_str oemit_all]. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CIRef rimg rkids rlabel)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p.
        cbn [ci_text ci_inlines map]. rewrite ci_src_ref.
        rewrite append_assoc, Hsrc, iscan_str_app, iscan_bracket_open.
        cbn [flush_text nonempty_str oemit_all] in Ekids |- *. rewrite Ekids.
        rewrite (iscan_ref_close rlabel _ (ci_inlines rkids) rimg _ pk Hne' Hbr),
                Hnorm.
        rewrite <- ci_ast_ref. rewrite oemit_all_app in Erest.
        cbn [flush_text nonempty_str oemit_all] in Erest.
        rewrite Erest. cbn [flush_text nonempty_str oemit_all]. reflexivity.
    + pose proof (cis_ok_head (CINote label) rest Hok) as Hnote.
      rewrite ci_ok_note in Hnote.
      apply andb_true_iff in Hnote as [Hsafe Hnorm].
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
          (Some rbrack) pre Hcl Hct Hflush (cis_ok_tail _ _ Hok) eq_refl).
        rewrite Hpre. reflexivity. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [ci_ast (CINote label)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p. cbn [ci_text ci_inlines map].
        change (ci_src (CINote label)) with (note_text label).
        rewrite append_assoc, iscan_note_text by assumption.
        rewrite Hnorm. rewrite oemit_all_app in Erest.
        cbn [flush_text nonempty_str oemit_all ci_ast] in Erest |- *.
        rewrite Erest. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CINote label)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p. cbn [ci_text ci_inlines map].
        change (ci_src (CINote label)) with (note_text label).
        rewrite append_assoc, iscan_note_text by assumption.
        rewrite Hnorm. rewrite oemit_all_app in Erest.
        cbn [flush_text nonempty_str oemit_all ci_ast] in Erest |- *.
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
          (Some gt) pre Hcl Hct Hflush (cis_ok_tail _ _ Hok) eq_refl).
        rewrite Hpre. reflexivity. }
      destruct txt as [|x txt'].
      * destruct (Hstep (before ++ [ci_ast (CIAuto a)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p. cbn [ci_text ci_inlines map].
        change (ci_src (CIAuto a)) with (auto_text a).
        rewrite append_assoc, iscan_auto_text by assumption.
        rewrite oemit_all_app in Erest.
        cbn [flush_text nonempty_str oemit_all ci_ast] in Erest |- *.
        rewrite Erest. reflexivity.
      * destruct (Hstep
                    (before ++ [mk (Str (String x txt')); ci_ast (CIAuto a)])%list
                    ltac:(destruct before; reflexivity)) as [p Erest].
        exists p. cbn [ci_text ci_inlines map].
        change (ci_src (CIAuto a)) with (auto_text a).
        rewrite append_assoc, iscan_auto_text by assumption.
        rewrite oemit_all_app in Erest.
        cbn [flush_text nonempty_str oemit_all ci_ast] in Erest |- *.
        rewrite Erest. reflexivity.
Qed.

(* The delimiter instance, which is what the two callers below use. *)
Lemma iscan_cis_marked :
  forall cis k tail txt prev before base,
    denabled_of k = true ->
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    (nonempty before || nonempty_str txt || nonempty cis)%bool = true ->
    exists p,
      iscan_str (ci_text cis ++ marked_close k tail)
        (IText false txt prev (oemit_all before (opush k true base)))
      = iscan_str (marked_close k tail)
          (IText false EmptyString p
            (oemit_all (ci_inlines cis)
              (flush_text txt (oemit_all before (opush k true base))))).
Proof.
  intros cis k tail txt prev before base Hden Hok Hsep Hne.
  apply (iscan_cis_scope cis (marked_close k tail) (opush k true base) false
           txt prev before
           (marked_close_nonempty _ _) (marked_close_starts_nontick _ _)
           (fun txt' prev' before' e =>
              iscan_marked_flush k tail txt' prev' before' base Hden
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
           (fun txt' prev' before' _ =>
              iscan_ref_flush label tail txt' prev' image before' base)
           Hok Hsep).
  apply orb_true_r.
Qed.

(* Once a canonical scan has closed every nested delimiter, the output
   state again has an empty scope stack. *)
Definition flush_out (txt : string) (out : inlines) : inlines :=
  if nonempty_str txt then mk (Str txt) :: out else out.

Lemma flush_text_flat :
  forall txt out, flush_text txt (OState out []) = OState (flush_out txt out) [].
Proof.
  intros txt out. unfold flush_text, flush_out, oemit; cbn [os_stk].
  destruct (nonempty_str txt); reflexivity.
Qed.

Lemma iscan_cis :
  forall cis prev' txt out,
    cis_ok cis = true -> text_sep_ok txt cis = true ->
    ifinish (iscan_str (ci_text cis)
               (IText false txt prev' (OState out [])))
    = (List.rev (flush_out txt out) ++ ci_inlines cis)%list.
Proof.
  intro cis. pattern cis.
  apply (well_founded_induction (well_founded_ltof _ cis_size)).
  clear cis. intros cis IH prev' txt out Hok Hsep.
  destruct cis as [|c rest].
  - cbn [ci_text ci_inlines iscan_str]. rewrite app_nil_r.
    rewrite ifinish_text, flush_text_flat. reflexivity.
  - assert (Hrestlt : ltof (list cinline) cis_size rest (c :: rest)).
    { unfold ltof. cbn [cis_size]. pose proof (ci_size_pos c). lia. }
    destruct c as [s|v|d kids|img kids dst|rimg rkids rlabel|label|a].
    + destruct txt as [|x txt']; [|discriminate].
      pose proof (cis_ok_head (CIStr s) rest Hok) as Hsok.
      cbn [ci_ok] in Hsok. apply andb_true_iff in Hsok as [Hs _].
      cbn [ci_text ci_src]. rewrite iscan_str_app, iscan_escape.
      cbn [ci_inlines map append].
      rewrite (IH rest Hrestlt prev' s out).
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
        unfold ifinish, ifinish_rev, ifinish_ostate, iresolve.
        rewrite nat_eqb_refl, trim_verb_pad by exact Hvok. cbn [vnode].
        unfold oemit, ofinish; cbn [os_stk os_out oflatten oapp].
        cbn [List.rev ci_ast]. reflexivity.
      * destruct (after_verb_rest_nontick v r rest' Hok) as [Hne Htick].
        rewrite (iscan_after_verb_nontick _ _ _ _ _ Hne Htick).
        rewrite trim_verb_pad by exact Hvok. cbn [vnode].
        cbn [oemit os_stk os_out].
        rewrite (IH (r :: rest') Hrestlt (Some tick) EmptyString
          (mk (Verbatim v) :: flush_out txt out)).
        -- cbn [flush_out nonempty_str ci_inlines map ci_ast List.rev].
           rewrite <- List.app_assoc. reflexivity.
        -- exact (cis_ok_tail _ _ Hok).
        -- reflexivity.
    + pose proof (cis_ok_head (CIDelim d kids) rest Hok) as Hdk.
      rewrite ci_ok_delim in Hdk. apply andb_true_iff in Hdk as [Hdk Hkidsok].
      apply andb_true_iff in Hdk as [Hden Hkidsne].
      pose proof (iscan_cis_marked kids d (ci_text rest) EmptyString
        (Some (dchar d)) [] (flush_text txt (OState out []))
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
      rewrite Hsrc, iscan_str_app, (iscan_marked_open _ _ _ _ Hden).
      cbn [flush_text nonempty_str oemit_all] in Ekids. rewrite Ekids.
      assert (Hkins : nonempty (ci_inlines kids) = true).
      { destruct kids; [discriminate|reflexivity]. }
      rewrite (iscan_marked_close_emit d _ (ci_inlines kids) _ pk Hden Hkins).
      rewrite <- ci_ast_delim.
      destruct (flush_text txt (OState out [])) as [out' stk'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk. subst out' stk'.
      cbn [oemit os_out os_stk].
      rewrite (IH rest Hrestlt (Some rbrace) EmptyString
        (ci_ast (CIDelim d kids) :: flush_out txt out)).
      * cbn [flush_out nonempty_str ci_inlines map List.rev].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * reflexivity.
    + pose proof (cis_ok_head (CILink img kids dst) rest Hok) as Hdk.
      rewrite ci_ok_link in Hdk. apply andb_true_iff in Hdk as [Hnl Hkidsok].
      destruct (iscan_cis_bracket kids dst (ci_text rest) EmptyString
        (Some lbrack) img [] (flush_text txt (OState out []))
        Hkidsok eq_refl) as [pk Ekids].
      cbn [ci_text ci_inlines map]. rewrite ci_src_link.
      assert (Hsrc :
        ((bracket_open img ++ (ci_text kids ++ link_close dst EmptyString)) ++
          ci_text rest)%string
        = (bracket_open img ++
            (ci_text kids ++ link_close dst (ci_text rest)))%string).
      { rewrite append_assoc, append_assoc, link_close_app. reflexivity. }
      rewrite Hsrc, iscan_str_app, iscan_bracket_open.
      cbn [flush_text nonempty_str oemit_all] in Ekids. rewrite Ekids.
      rewrite (iscan_link_close dst _ (ci_inlines kids) img _ pk Hnl).
      rewrite <- ci_ast_link.
      destruct (flush_text txt (OState out [])) as [out' stk'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk. subst out' stk'.
      cbn [oemit os_out os_stk].
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
        (Some lbrack) rimg [] (flush_text txt (OState out []))
        Hkidsok eq_refl) as [pk Ekids].
      cbn [ci_text ci_inlines map]. rewrite ci_src_ref.
      assert (Hsrc :
        ((bracket_open rimg ++ (ci_text rkids ++ ref_close rlabel EmptyString)) ++
          ci_text rest)%string
        = (bracket_open rimg ++
            (ci_text rkids ++ ref_close rlabel (ci_text rest)))%string).
      { rewrite append_assoc, append_assoc, ref_close_app. reflexivity. }
      rewrite Hsrc, iscan_str_app, iscan_bracket_open.
      cbn [flush_text nonempty_str oemit_all] in Ekids. rewrite Ekids.
      rewrite (iscan_ref_close rlabel _ (ci_inlines rkids) rimg _ pk Hne' Hbr),
              Hnorm.
      rewrite <- ci_ast_ref.
      destruct (flush_text txt (OState out [])) as [out' stk'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk. subst out' stk'.
      cbn [oemit os_out os_stk].
      rewrite (IH rest Hrestlt (Some rbrack) EmptyString
        (ci_ast (CIRef rimg rkids rlabel) :: flush_out txt out)).
      * cbn [flush_out nonempty_str ci_inlines map List.rev].
        rewrite <- List.app_assoc. reflexivity.
      * exact (cis_ok_tail _ _ Hok).
      * reflexivity.
    + pose proof (cis_ok_head (CINote label) rest Hok) as Hnote.
      rewrite ci_ok_note in Hnote.
      apply andb_true_iff in Hnote as [Hsafe Hnorm].
      apply String.eqb_eq in Hnorm.
      cbn [ci_text ci_inlines map].
      change (ci_src (CINote label)) with (note_text label).
      rewrite (iscan_note_text label (ci_text rest) txt prev'
                 (OState out []) Hsafe), Hnorm.
      destruct (flush_text txt (OState out [])) as [out' stk'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk. subst out' stk'.
      cbn [oemit os_out os_stk].
      change (mk (FootnoteReference label)) with (ci_ast (CINote label)).
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
                 (OState out []) Hbody Hkind).
      destruct (flush_text txt (OState out [])) as [out' stk'] eqn:Eflush.
      pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
      injection Eflat as Eout Estk. subst out' stk'.
      cbn [oemit os_out os_stk].
      change (mk (auto_node a)) with (ci_ast (CIAuto a)).
      rewrite (IH rest Hrestlt (Some gt) EmptyString
        (ci_ast (CIAuto a) :: flush_out txt out)).
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
                    (IText false txt prev' (OState out []))) = true.
Proof.
  intro cis. pattern cis.
  apply (well_founded_induction (well_founded_ltof _ cis_size)).
  clear cis. intros cis IH prev' txt out Hok.
  destruct cis as [|c rest]; [reflexivity|].
  assert (Hrestlt : ltof (list cinline) cis_size rest (c :: rest)).
  { unfold ltof. cbn [cis_size]. pose proof (ci_size_pos c). lia. }
  destruct c as [s|v|d kids|img kids dst|rimg rkids rlabel|label|a].
  - cbn [ci_text ci_src]. rewrite iscan_str_app, iscan_escape.
    apply (IH rest Hrestlt), (cis_ok_tail _ _ Hok).
  - pose proof (ci_verb_nonempty v rest Hok) as Hvne.
    pose proof (ci_verb_content_ok v rest Hok) as Hvok.
    cbn [ci_text ci_src]. rewrite iscan_str_app.
    rewrite iscan_verb_text_nonempty by auto using verb_content_safe.
    rewrite flush_text_flat.
    destruct rest as [|r rest'].
    + cbn [ci_text iscan_str iscan_closed iresolve os_stk null].
      rewrite nat_eqb_refl. reflexivity.
    + destruct (after_verb_rest_nontick v r rest' Hok) as [Hne Htick].
      rewrite (iscan_after_verb_nontick _ _ _ _ _ Hne Htick).
      rewrite trim_verb_pad by exact Hvok. cbn [vnode]. cbn [oemit os_out os_stk].
      apply (IH (r :: rest') Hrestlt), (cis_ok_tail _ _ Hok).
  - pose proof (cis_ok_head (CIDelim d kids) rest Hok) as Hdk.
    rewrite ci_ok_delim in Hdk. apply andb_true_iff in Hdk as [Hdk Hkidsok].
    apply andb_true_iff in Hdk as [Hden Hkidsne].
    pose proof (iscan_cis_marked kids d (ci_text rest) EmptyString
      (Some (dchar d)) [] (flush_text txt (OState out []))
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
    rewrite Hsrc, iscan_str_app, (iscan_marked_open _ _ _ _ Hden).
    cbn [flush_text nonempty_str oemit_all] in Ekids. rewrite Ekids.
    assert (Hkins : nonempty (ci_inlines kids) = true).
    { destruct kids; [discriminate|reflexivity]. }
    rewrite (iscan_marked_close_emit d _ (ci_inlines kids) _ pk Hden Hkins).
    destruct (flush_text txt (OState out [])) as [out' stk'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk. subst out' stk'.
    cbn [oemit os_out os_stk].
    apply (IH rest Hrestlt), (cis_ok_tail _ _ Hok).
  - pose proof (cis_ok_head (CILink img kids dst) rest Hok) as Hdk.
    rewrite ci_ok_link in Hdk. apply andb_true_iff in Hdk as [Hnl Hkidsok].
    destruct (iscan_cis_bracket kids dst (ci_text rest) EmptyString
      (Some lbrack) img [] (flush_text txt (OState out []))
      Hkidsok eq_refl) as [pk Ekids].
    cbn [ci_text]. rewrite ci_src_link.
    assert (Hsrc :
      ((bracket_open img ++ (ci_text kids ++ link_close dst EmptyString)) ++
        ci_text rest)%string
      = (bracket_open img ++
          (ci_text kids ++ link_close dst (ci_text rest)))%string).
    { rewrite append_assoc, append_assoc, link_close_app. reflexivity. }
    rewrite Hsrc, iscan_str_app, iscan_bracket_open.
    cbn [flush_text nonempty_str oemit_all] in Ekids. rewrite Ekids.
    rewrite (iscan_link_close dst _ (ci_inlines kids) img _ pk Hnl).
    destruct (flush_text txt (OState out [])) as [out' stk'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk. subst out' stk'.
    cbn [oemit os_out os_stk].
    apply (IH rest Hrestlt), (cis_ok_tail _ _ Hok).
  - pose proof (cis_ok_head (CIRef rimg rkids rlabel) rest Hok) as Hdk.
    rewrite ci_ok_ref in Hdk.
    apply andb_true_iff in Hdk as [Hlab Hkidsok].
    apply andb_true_iff in Hlab as [Hlab Hnorm].
    apply andb_true_iff in Hlab as [Hne' Hbr].
    destruct (iscan_cis_ref rkids rlabel (ci_text rest) EmptyString
      (Some lbrack) rimg [] (flush_text txt (OState out []))
      Hkidsok eq_refl) as [pk Ekids].
    cbn [ci_text]. rewrite ci_src_ref.
    assert (Hsrc :
      ((bracket_open rimg ++ (ci_text rkids ++ ref_close rlabel EmptyString)) ++
        ci_text rest)%string
      = (bracket_open rimg ++
          (ci_text rkids ++ ref_close rlabel (ci_text rest)))%string).
    { rewrite append_assoc, append_assoc, ref_close_app. reflexivity. }
    rewrite Hsrc, iscan_str_app, iscan_bracket_open.
    cbn [flush_text nonempty_str oemit_all] in Ekids. rewrite Ekids.
    rewrite (iscan_ref_close rlabel _ (ci_inlines rkids) rimg _ pk Hne' Hbr).
    destruct (flush_text txt (OState out [])) as [out' stk'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk. subst out' stk'.
    cbn [oemit os_out os_stk].
    apply (IH rest Hrestlt), (cis_ok_tail _ _ Hok).
  - pose proof (cis_ok_head (CINote label) rest Hok) as Hnote.
    rewrite ci_ok_note in Hnote.
    apply andb_true_iff in Hnote as [Hsafe Hnorm].
    cbn [ci_text]. change (ci_src (CINote label)) with (note_text label).
    rewrite (iscan_note_text label (ci_text rest) txt prev'
               (OState out []) Hsafe).
    destruct (flush_text txt (OState out [])) as [out' stk'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk. subst out' stk'.
    cbn [oemit os_out os_stk].
    apply (IH rest Hrestlt), (cis_ok_tail _ _ Hok).
  - pose proof (cis_ok_head (CIAuto a) rest Hok) as Hauto.
    rewrite ci_ok_auto in Hauto.
    apply andb_true_iff in Hauto as [Hbody Hkind].
    cbn [ci_text]. change (ci_src (CIAuto a)) with (auto_text a).
    rewrite (iscan_auto_text a (ci_text rest) txt prev'
               (OState out []) Hbody Hkind).
    destruct (flush_text txt (OState out [])) as [out' stk'] eqn:Eflush.
    pose proof (flush_text_flat txt out) as Eflat. rewrite Eflush in Eflat.
    injection Eflat as Eout Estk. subst out' stk'.
    cbn [oemit os_out os_stk].
    apply (IH rest Hrestlt), (cis_ok_tail _ _ Hok).
Qed.

(*
The scan is productive
----------------------

`Wf.v` needs that a nonempty line yields at least one inline, which the
old one-`Str`-per-line parser had by construction and a scanner does not.
The initial state is deliberately *un*productive, since empty input must
give no inlines; one character suffices. *)

(* Productive means: whatever follows, at least one inline comes out.
   `IText` with nothing pending and nothing emitted is the one state
   that fails it -- which is the start state, as it must be, since empty
   input yields no inlines.  An open scope counts as productive: it is
   abandoned at the end, and its opener becomes text. *)
Definition iscan_productive (st : iscan) : bool :=
  match st with
  | IText false txt _ o => (nonempty_str txt || ostate_nonempty o)%bool
  (* a hyphen run owes what it has counted, and every way of building one
     counts at least one -- but the type does not say so, so the
     disjunct does *)
  | IDash n txt _ o =>
      (Nat.ltb 0 n || nonempty_str txt || ostate_nonempty o)%bool
  | _ => true
  end.

Lemma nonempty_str_app_l :
  forall a b, nonempty_str b = true -> nonempty_str (a ++ b)%string = true.
Proof. intros [|x a] b H; [exact H | reflexivity]. Qed.

Lemma nonempty_str_app_r :
  forall a b, nonempty_str a = true -> nonempty_str (a ++ b)%string = true.
Proof. intros [|x a] b H; [discriminate | reflexivity]. Qed.

(* Both reconstructions end in a bracket, so the buffer they hand back is
   never empty: a literal bracket always owes at least its own source. *)
Lemma bclosed_lit_nonempty :
  forall kids image o,
    nonempty_str (fst (bclosed_lit kids image o)) = true.
Proof.
  intros kids image o. unfold bclosed_lit.
  destruct (opop_str o) as [pre o1].
  destruct (bflat kids (pre ++ bracket_open image)%string o1) as [txt o2].
  cbn [fst]. apply nonempty_str_app_l. reflexivity.
Qed.

Lemma nonempty_rev : forall (l : inlines), nonempty (List.rev l) = nonempty l.
Proof.
  intros [|n l]; [reflexivity|].
  cbn [List.rev nonempty]. destruct (List.rev l ++ [n])%list eqn:E; [|reflexivity].
  destruct (List.rev l); discriminate.
Qed.

Lemma ostate_nonempty_emit :
  forall n o, ostate_nonempty (oemit n o) = true.
Proof.
  intros n [out [|f stk]]; [reflexivity|].
  unfold ostate_nonempty, oemit; cbn [os_out os_stk null negb].
  apply orb_true_r.
Qed.

Lemma ostate_nonempty_flush :
  forall txt o,
    ostate_nonempty o = true -> ostate_nonempty (flush_text txt o) = true.
Proof.
  intros txt o H. unfold flush_text.
  destruct (nonempty_str txt); [apply ostate_nonempty_emit | exact H].
Qed.

Lemma ostate_nonempty_flush_str :
  forall txt o,
    nonempty_str txt = true -> ostate_nonempty (flush_text txt o) = true.
Proof.
  intros txt o H. unfold flush_text. rewrite H. apply ostate_nonempty_emit.
Qed.

Lemma ostate_nonempty_push :
  forall k m o, ostate_nonempty (opush k m o) = true.
Proof.
  intros k m o. unfold ostate_nonempty, opush; cbn [os_stk].
  rewrite orb_true_r. reflexivity.
Qed.

Lemma ostate_nonempty_bpush :
  forall image o, ostate_nonempty (bpush image o) = true.
Proof.
  intros image o. unfold ostate_nonempty, bpush; cbn [os_stk].
  rewrite orb_true_r. reflexivity.
Qed.

(* Splitting at a break either leaves the text in the buffer or emits a
   `SoftBreak`, so a nonempty destination stays owed either way. *)
Lemma bsplit_nl_productive :
  forall s txt o,
    (nonempty_str txt || ostate_nonempty o)%bool = true ->
    (nonempty_str (fst (bsplit_nl s txt o))
     || ostate_nonempty (snd (bsplit_nl s txt o)))%bool = true.
Proof.
  induction s as [|c s IH]; intros txt o H; cbn [bsplit_nl]; [exact H|].
  destruct (Ascii.eqb c nl_char).
  - apply IH. rewrite ostate_nonempty_emit. apply orb_true_r.
  - apply IH. rewrite nonempty_str_app_l by reflexivity. reflexivity.
Qed.

Lemma bdest_lit_productive :
  forall kids image esc dst o,
    (nonempty_str (fst (bdest_lit kids image esc dst o))
     || ostate_nonempty (snd (bdest_lit kids image esc dst o)))%bool = true.
Proof.
  intros kids image esc dst o. unfold bdest_lit.
  destruct (bclosed_lit kids image o) as [txt o'].
  apply bsplit_nl_productive.
  rewrite nonempty_str_app_l by reflexivity. reflexivity.
Qed.

Lemma bref_lit_productive :
  forall kids image label o,
    (nonempty_str (fst (bref_lit kids image label o))
     || ostate_nonempty (snd (bref_lit kids image label o)))%bool = true.
Proof.
  intros kids image label o. unfold bref_lit.
  destruct (bclosed_lit kids image o) as [txt o']. cbn [fst snd].
  apply orb_true_iff. left. destruct txt; reflexivity.
Qed.

(* A label that never closed still owes its bracket. *)
Lemma bnote_lit_productive :
  forall esc image label o,
    (nonempty_str (fst (bnote_lit esc image label o))
     || ostate_nonempty (snd (bnote_lit esc image label o)))%bool = true.
Proof.
  intros esc image label o. unfold bnote_lit.
  destruct (opop_str o) as [pre o1]. cbn [fst snd].
  apply orb_true_iff. left. apply nonempty_str_app_l.
  destruct image; reflexivity.
Qed.

Lemma dollars_nonempty : forall two, nonempty_str (dollars two) = true.
Proof. intros []; reflexivity. Qed.

Lemma periods_nonempty : forall two, nonempty_str (periods two) = true.
Proof. intros []; reflexivity. Qed.

Lemma srep_nonempty :
  forall s n, nonempty_str s = true -> nonempty_str (srep s (S n)) = true.
Proof. intros s n H. cbn [srep]. apply nonempty_str_app_r, H. Qed.

(* Every run of at least one hyphen leaves something: the arithmetic
   never returns all three counts zero.  Two of the five branches need
   the division to be positive, and the rest compute. *)
Lemma div_pos : forall a b, b <> 0 -> Nat.modulo a b = 0 -> a <> 0 ->
  exists m, Nat.div a b = S m.
Proof.
  intros a b Hb Hm Ha. destruct (Nat.div a b) as [|m] eqn:Ed; [|eauto].
  exfalso. pose proof (Nat.div_mod a b Hb) as Hdm. rewrite Ed, Hm in Hdm. lia.
Qed.

Lemma dashes_nonempty : forall n, nonempty_str (dashes (S n)) = true.
Proof.
  intros n. unfold dashes, dash_counts.
  destruct (Nat.eqb (Nat.modulo (S n) 3) 0) eqn:E3.
  { apply Nat.eqb_eq in E3.
    destruct (div_pos (S n) 3 ltac:(lia) E3 ltac:(lia)) as [m Hm].
    rewrite Hm. apply nonempty_str_app_r, srep_nonempty. reflexivity. }
  destruct (Nat.eqb (Nat.modulo (S n) 2) 0) eqn:E2.
  { apply Nat.eqb_eq in E2.
    destruct (div_pos (S n) 2 ltac:(lia) E2 ltac:(lia)) as [m Hm].
    rewrite Hm. apply nonempty_str_app_l, nonempty_str_app_r.
    apply srep_nonempty. reflexivity. }
  destruct (Nat.eqb (S n) 1) eqn:E1.
  { apply Nat.eqb_eq in E1. assert (Hn : n = 0) by lia. subst n. reflexivity. }
  destruct (Nat.eqb (Nat.modulo (S n) 6) 5);
    (apply nonempty_str_app_l, nonempty_str_app_r;
     apply srep_nonempty; reflexivity).
Qed.

Lemma iscan_productive_lead :
  forall c txt prev o,
    (nonempty_str txt || ostate_nonempty o)%bool = true ->
    iscan_productive (ilead c txt prev o) = true.
Proof.
  intros c txt prev o H. unfold ilead.
  destruct (is_bslash c); [reflexivity|].
  destruct (is_tick c); [reflexivity|].
  destruct (Ascii.eqb c dollar); [reflexivity|].
  destruct (Ascii.eqb c period); [reflexivity|].
  destruct (Ascii.eqb c hyphen); [reflexivity|].
  destruct (Ascii.eqb c lbrace); [reflexivity|].
  destruct (Ascii.eqb c bang); [reflexivity|].
  destruct (Ascii.eqb c lt); [reflexivity|].
  destruct (Ascii.eqb c lbrack);
    [cbn [iscan_productive]; rewrite ostate_nonempty_bpush; apply orb_true_r|].
  destruct (Ascii.eqb c rbrack);
    [destruct (bclose (flush_text txt o)) as [[[kids image] o']|];
     [reflexivity|];
     cbn [iscan_productive];
     rewrite nonempty_str_app_l by reflexivity; reflexivity|].
  destruct (Ascii.eqb c hat && note_pos txt prev)%bool;
    [destruct (bunpush o) as [[image o']|]; [reflexivity|]|];
    (destruct (dstyle_of c); [reflexivity|]);
    cbn [iscan_productive]; apply orb_true_iff; left;
    apply nonempty_str_app_l; reflexivity.
Qed.

Lemma idelim_marked_productive :
  forall k extra txt o, iscan_productive (idelim_marked k extra txt o) = true.
Proof.
  intros k extra txt o. unfold idelim_marked.
  destruct (Nat.ltb (S extra) (dwidth k)); [reflexivity|].
  cbn [iscan_productive]. rewrite ostate_nonempty_push. apply orb_true_r.
Qed.

Lemma idelim_done_productive :
  forall k txt bef marker next o,
    iscan_productive (idelim_done k txt bef marker next o) = true
    /\ forall txt' prev' o',
         idelim_done k txt bef marker next o = IText false txt' prev' o' ->
         (nonempty_str txt' || ostate_nonempty o')%bool = true.
Proof.
  intros k txt bef marker next o. unfold idelim_done.
  destruct (dbare k bef && negb marker && nonspace_at next)%bool.
  - split.
    + cbn [iscan_productive]. rewrite ostate_nonempty_push. apply orb_true_r.
    + intros txt' prev' o' E. injection E as E1 E2. subst txt' o'.
      rewrite ostate_nonempty_push. apply orb_true_r.
  - assert (Hlit : nonempty_str (idelim_lit k txt marker) = true)
      by (unfold idelim_lit; apply nonempty_str_app_l, ddecay_str_nonempty).
    split.
    + cbn [iscan_productive]. rewrite Hlit. reflexivity.
    + intros txt' prev' o' E. injection E as E1 E2 E3. subst txt' o'.
      rewrite Hlit. reflexivity.
Qed.

Lemma idelim_resolve_productive :
  forall k txt bef marker next o,
    iscan_productive (idelim_resolve k txt bef marker next o) = true
    /\ forall txt' prev' o',
         idelim_resolve k txt bef marker next o = IText false txt' prev' o' ->
         (nonempty_str txt' || ostate_nonempty o')%bool = true.
Proof.
  intros k txt bef marker next o. unfold idelim_resolve.
  destruct (nonspace_at bef || marker)%bool; [|apply idelim_done_productive].
  destruct (oclose k marker (flush_text txt o)) as [o'|] eqn:Ec;
    [|apply idelim_done_productive].
  assert (Hne : ostate_nonempty o' = true).
  { unfold oclose in Ec.
    destruct (oclose_go k marker [] (os_stk (flush_text txt o)))
      as [[content rest]|]; [|discriminate].
    injection Ec as <-. apply ostate_nonempty_emit. }
  split.
  - cbn [iscan_productive]. rewrite Hne. apply orb_true_r.
  - intros txt' prev' o'' E. injection E as E1 E2. subst txt' o''.
    rewrite Hne. apply orb_true_r.
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
  destruct (oclose k marker (flush_text txt o));
    [eauto | apply idelim_done_text].
Qed.

Lemma iresolve_resolved :
  forall st,
    match iresolve st with
    | IBrace _ _ _ | IAttr _ _ _ _ _ | IBang _ _ _ | IDollar _ _ _ _
    | IPeriod _ _ _ _ | IDash _ _ _ _
    | IDelim _ _ _ _ _ _ | IClosed _ _ _ => False
    | _ => True
    end.
Proof.
  intros [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|nesc nimg nlab nob|kids img esc depth dst ob|asrc atxt aob];
    cbn [iresolve]; try exact I.
  - destruct (Nat.ltb (S seen) (dwidth k)); [exact I|].
    destruct (idelim_resolve_text k txt cc false None o) as [txt' [prev' [o' E]]].
    rewrite E. exact I.
  - destruct (bclosed_lit kids img ob) as [txt o']. exact I.
Qed.

Lemma iscan_productive_resolve :
  forall st, iscan_productive st = true -> iscan_productive (iresolve st) = true.
Proof.
  intros [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|nesc nimg nlab nob|kids img esc depth dst ob|asrc atxt aob] H;
    cbn [iresolve]; try exact H.
  (* `IBrace`, `IAttr`, `IBang` and `IDollar` all push their own bytes
     into the buffer, so the text they resolve to is nonempty *)
  all: try (cbn [iscan_productive]; apply orb_true_iff; left;
            apply nonempty_str_app_l;
            first [reflexivity | apply dollars_nonempty
                  | apply periods_nonempty]).
  - destruct (Nat.ltb (S seen) (dwidth k)).
    { cbn [iscan_productive]. apply orb_true_iff. left.
      apply nonempty_str_app_l, idelim_run_nonempty. }
    apply idelim_resolve_productive.
  (* a hyphen run: what it counted, cut into dashes *)
  - cbn [iscan_productive] in H |- *. destruct dn as [|dn].
    { cbn [Nat.ltb Nat.leb orb] in H.
      change (dashes 0) with EmptyString.
      rewrite (append_empty_r dtx). exact H. }
    apply orb_true_iff. left.
    apply nonempty_str_app_l, dashes_nonempty.
  - pose proof (bclosed_lit_nonempty kids img ob) as Hne.
    destruct (bclosed_lit kids img ob) as [txt o']; cbn [fst] in Hne.
    cbn [iscan_productive]. rewrite Hne. reflexivity.
Qed.

Lemma bspan_lit_productive :
  forall kids image src o,
    (nonempty_str (fst (bspan_lit kids image src o))
     || ostate_nonempty (snd (bspan_lit kids image src o)))%bool = true.
Proof.
  intros kids image src o. unfold bspan_lit.
  destruct (bclosed_lit kids image o) as [txt o']; cbn [fst snd].
  apply orb_true_iff. left. apply nonempty_str_app_l. reflexivity.
Qed.

(* Every disposition owes something: the literal fallback puts the text
   back with its `{`, an attachment emits a node, and the drop either
   keeps pending text or, when there is none, keeps the source. *)
Lemma iattr_attach_productive :
  forall a src txt prev o,
    iscan_productive (iattr_attach a src txt prev o) = true.
Proof.
  intros a src txt prev o. unfold iattr_attach.
  destruct (last_ws_split txt) as [pre w] eqn:Es.
  destruct (nonempty_str w) eqn:Ew.
  - destruct a as [|kv a'].
    + cbn [iscan_productive]. apply orb_true_iff. left.
      apply last_ws_split_nonempty. rewrite Es. exact Ew.
    + cbn [iscan_productive]. rewrite ostate_nonempty_emit. apply orb_true_r.
  - destruct (nonempty_str txt) eqn:Et;
      [cbn [iscan_productive]; rewrite Et; reflexivity|].
    (* nothing pending: either a node here takes the spec, or its source
       stays as text -- and both leave something behind *)
    destruct (oattach a o) as [o'|] eqn:Ea; cbn [iscan_productive].
    + rewrite (oattach_nonempty a o o' Ea). apply orb_true_r.
    + apply orb_true_iff. left. reflexivity.
Qed.

Lemma iattr_feed_productive :
  forall c p src txt prev o,
    iscan_productive (iattr_feed c p src txt prev o) = true.
Proof.
  intros c p src txt prev o. unfold iattr_feed.
  destruct (ap_failed (astep p c)).
  - apply iscan_productive_lead. apply orb_true_iff. left.
    apply nonempty_str_app_l. reflexivity.
  - destruct (ap_done (astep p c)); [apply iattr_attach_productive|reflexivity].
Qed.

Lemma ispan_feed_productive :
  forall c kids image p src o,
    iscan_productive (ispan_feed c kids image p src o) = true.
Proof.
  intros c kids image p src o. unfold ispan_feed.
  destruct (ap_failed (astep p c)).
  - pose proof (bclosed_lit_nonempty kids image o) as Hne.
    unfold bspan_lit. destruct (bclosed_lit kids image o) as [txt o'];
      cbn [fst] in Hne.
    apply iscan_productive_lead. apply orb_true_iff. left.
    apply nonempty_str_app_l. reflexivity.
  - destruct (ap_done (astep p c)); [|reflexivity].
    cbn [iscan_productive]. rewrite ostate_nonempty_emit. apply orb_true_r.
Qed.

Lemma iescws_resolve_productive :
  forall ws txt prev o,
    let '(t, _, o') := iescws_resolve ws txt prev o in
    (nonempty_str t || ostate_nonempty o')%bool = true.
Proof.
  intros [|c ws] txt prev o; cbn [iescws_resolve].
  - apply orb_true_iff. left. apply nonempty_str_app_l. reflexivity.
  - destruct (Ascii.eqb c " "%char).
    + rewrite ostate_nonempty_emit. apply orb_true_r.
    + apply orb_true_iff. left. apply nonempty_str_app_l. reflexivity.
Qed.

Lemma iscan_productive_step :
  forall c st, iscan_productive st = true -> iscan_productive (istep c st) = true.
Proof.
  intros c [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|nesc nimg nlab nob|kids img esc depth dst ob|asrc atxt aob] H;
    cbn [istep].
  - destruct (is_ws c); [reflexivity|].
    cbn [iscan_productive]. apply orb_true_iff. left.
    apply nonempty_str_app_l. destruct (is_punct c); reflexivity.
  - apply iscan_productive_lead, H.
  - destruct (is_ws c); [reflexivity|].
    pose proof (iescws_resolve_productive ews etxt eprev eob) as Hr.
    destruct (iescws_resolve ews etxt eprev eob) as [[t p] o'].
    apply iscan_productive_lead, Hr.
  - unfold ibrace_step. destruct (dstyle_of c);
      [apply idelim_marked_productive|apply iattr_feed_productive].
  - (* whichever way the pending delimiter resolves, something is owed:
       either a scope is open, or its spelling is in the text buffer *)
    destruct (Nat.ltb (S seen) (dwidth k)).
    { destruct (Ascii.eqb c (dchar k));
        [destruct mrk; [apply idelim_marked_productive|reflexivity]|].
      apply iscan_productive_lead, orb_true_iff. left.
      apply nonempty_str_app_l, idelim_run_nonempty. }
    destruct (Ascii.eqb c rbrace);
      [apply (idelim_resolve_productive k txt cc true (Some c) o)|].
    destruct (idelim_resolve_productive k txt cc false (Some c) o) as [_ Ht].
    destruct (idelim_resolve_text k txt cc false (Some c) o)
      as [txt' [prev' [o' E]]].
    rewrite E. apply iscan_productive_lead, (Ht txt' prev' o' E).
  - destruct (is_tick c); reflexivity.
  - destruct (is_tick c); [reflexivity|].
    destruct (Nat.eqb run n); [|reflexivity].
    apply iscan_productive_lead.
    rewrite ostate_nonempty_emit. apply orb_true_r.
  - (* a pending `$` owes its own dollars, or the span it opens *)
    unfold idollar_step. destruct (Ascii.eqb c dollar);
      [destruct dtwo; reflexivity|].
    destruct (is_tick c); [reflexivity|].
    apply iscan_productive_lead, orb_true_iff. left.
    apply nonempty_str_app_l, dollars_nonempty.
  - (* and a pending `.` owes its own periods, or the ellipsis they make *)
    unfold iperiod_step. destruct (Ascii.eqb c period).
    { destruct ptwo; [|reflexivity].
      cbn [iscan_productive]. apply orb_true_iff. left.
      apply nonempty_str_app_l. reflexivity. }
    apply iscan_productive_lead, orb_true_iff. left.
    apply nonempty_str_app_l, periods_nonempty.
  - (* a hyphen run owes what it has counted *)
    unfold idash_step. destruct (Ascii.eqb c hyphen); [reflexivity|].
    destruct (Ascii.eqb c rbrace).
    { destruct (dstyle_of hyphen) as [k|];
        [destruct (Nat.leb (dwidth k) dn);
           [apply idelim_resolve_productive|]|];
        (cbn [iscan_productive]; apply orb_true_iff; left;
         apply nonempty_str_app_l, nonempty_str_app_l; reflexivity). }
    apply iscan_productive_lead. cbn [iscan_productive] in H.
    destruct dn as [|dn].
    { cbn [Nat.ltb orb] in H. change (dashes 0) with EmptyString.
      rewrite (append_empty_r dtx). exact H. }
    apply orb_true_iff. left. apply nonempty_str_app_l, dashes_nonempty.
  - unfold ibang_step. destruct (Ascii.eqb c lbrack).
    + cbn [iscan_productive]. rewrite ostate_nonempty_bpush. apply orb_true_r.
    + apply iscan_productive_lead. apply orb_true_iff. left.
      apply nonempty_str_app_l. reflexivity.
  - (* a literal bracket owes its own source; a destination owes more *)
    destruct (Ascii.eqb c lparen); [reflexivity|].
    destruct (Ascii.eqb c lbrack); [reflexivity|].
    destruct (Ascii.eqb c lbrace); [reflexivity|].
    pose proof (bclosed_lit_nonempty kids img ob) as Hne.
    destruct (bclosed_lit kids img ob) as [txt o']; cbn [fst] in Hne.
    apply iscan_productive_lead. rewrite Hne. reflexivity.
  - apply ispan_feed_productive.
  - apply iattr_feed_productive.
  - destruct (Ascii.eqb c rbrack); [|reflexivity].
    cbn [iscan_productive]. rewrite ostate_nonempty_emit. apply orb_true_r.
  - unfold inote_step. destruct nesc; [reflexivity|].
    destruct (is_bslash c); [reflexivity|].
    destruct (Ascii.eqb c rbrack); [|reflexivity].
    cbn [iscan_productive]. rewrite ostate_nonempty_emit. apply orb_true_r.
  - destruct esc; [reflexivity|].
    destruct (is_bslash c); [reflexivity|].
    destruct (Ascii.eqb c lparen); [reflexivity|].
    destruct (Ascii.eqb c rparen); [|reflexivity].
    destruct depth; [|reflexivity].
    cbn [iscan_productive]. rewrite ostate_nonempty_emit. apply orb_true_r.
  (* a candidate owes its own `<` whichever way it ends *)
  - unfold iauto_step.
    destruct (Ascii.eqb c gt && auto_body_ok asrc && auto_kind_ok asrc)%bool.
    { cbn [iscan_productive]. rewrite ostate_nonempty_emit. apply orb_true_r. }
    destruct (Ascii.eqb c gt || is_ws c || Ascii.eqb c lt)%bool; [|reflexivity].
    apply iscan_productive_lead, orb_true_iff. left.
    apply nonempty_str_app_l. reflexivity.
Qed.

Lemma iscan_productive_str :
  forall s st, iscan_productive st = true ->
  iscan_productive (iscan_str s st) = true.
Proof.
  induction s as [|c rest IH]; intros st H; [exact H|].
  cbn [iscan_str]. apply IH, iscan_productive_step, H.
Qed.

(* Unconditional: a boundary either pushes a `SoftBreak` or leaves a
   state that is productive by construction, so every paragraph of two
   or more lines is productive whatever its first line held. *)
Lemma iscan_productive_break :
  forall st, iscan_productive (ibreak st) = true.
Proof.
  intros st. unfold ibreak.
  pose proof (iresolve_resolved st) as Hno.
  destruct (iresolve st) as [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|nesc nimg nlab nob|kids img esc depth dst ob|asrc atxt aob];
    try contradiction;
    cbn [iscan_productive]; try reflexivity;
    try apply ispan_feed_productive.
  1,2,3: try unfold iesc_hard;
         rewrite ostate_nonempty_emit; apply orb_true_r.
  destruct (Nat.eqb run n); cbn [iscan_productive]; [|reflexivity].
  { rewrite ostate_nonempty_emit. apply orb_true_r. }
  (* the candidate's own `<` is in the buffer the break flushes *)
  rewrite ostate_nonempty_emit. apply orb_true_r.
Qed.

Lemma iscan_productive_lines :
  forall l st, iscan_productive st = true ->
  iscan_productive (iscan_lines l st) = true.
Proof.
  induction l as [|x [|y rest] IH]; intros st H; cbn [iscan_lines].
  - exact H.
  - apply iscan_productive_str, H.
  - apply IH, iscan_productive_break.
Qed.

Lemma nonempty_oapp :
  forall cur out, nonempty out = true -> nonempty (oapp cur out) = true.
Proof.
  induction cur as [|n cur IH]; intros out H; [exact H|].
  destruct cur as [|m cur']; [|rewrite oapp_cons2; reflexivity].
  rewrite oapp_one. destruct out as [|[a [|p ps] i] out']; [discriminate| |].
  - unfold osnoc. destruct i; try reflexivity.
    destruct n as [c [|q qs] j]; [|reflexivity]. destruct j; reflexivity.
  - unfold osnoc. destruct n as [c d j]; reflexivity.
Qed.

Lemma nonempty_oapp_l :
  forall cur out, nonempty cur = true -> nonempty (oapp cur out) = true.
Proof.
  intros [|x [|y cur']] out H; [discriminate| |rewrite oapp_cons2; reflexivity].
  rewrite oapp_one. destruct out as [|[a [|p ps] i] out']; try reflexivity.
  unfold osnoc. destruct i; try reflexivity.
  destruct x as [c [|q qs] j]; [|reflexivity]. destruct j; reflexivity.
Qed.

Lemma nonempty_oapp_snoc :
  forall cur n, nonempty (oapp cur [n]) = true.
Proof.
  intros cur n. destruct cur as [|x cur']; [reflexivity|].
  apply nonempty_oapp_l. reflexivity.
Qed.

(* Something comes out if anything is owed: content below, an open scope
   whose opener will decay to text, or a pending splice. *)
Lemma nonempty_oflatten :
  forall stk pend bottom,
    (nonempty bottom || negb (null stk) || nonempty pend)%bool = true ->
    nonempty (oflatten pend stk bottom) = true.
Proof.
  induction stk as [|f stk IH]; intros pend bottom H; cbn [oflatten].
  - cbn [null negb] in H. rewrite orb_false_r in H.
    apply orb_true_iff in H as [H|H];
      [apply nonempty_oapp, H | apply nonempty_oapp_l, H].
  - apply IH. rewrite nonempty_oapp_snoc, orb_true_r. reflexivity.
Qed.

Lemma nonempty_ofinish :
  forall o, ostate_nonempty o = true -> nonempty (ofinish o) = true.
Proof.
  intros o H. unfold ofinish. apply nonempty_oflatten.
  unfold ostate_nonempty in H. rewrite H. reflexivity.
Qed.

Lemma iscan_productive_finish :
  forall st, iscan_productive st = true -> nonempty (ifinish st) = true.
Proof.
  intros st H. unfold ifinish. rewrite nonempty_rev.
  unfold ifinish_rev, ifinish_ostate.
  pose proof (iscan_productive_resolve st H) as Hres.
  pose proof (iresolve_resolved st) as Hno.
  destruct (iresolve st) as
    [[] txt prev o|ews etxt eprev eob|txt prev o|k seen txt cc mrk o|n vk o|n run txt vk o|dtwo dtxt dprev dob|ptwo ptxt pprev pob|dn dtx dpv dob2|txb prb ob|kids img ob|kids img sp ssrc sob|ap asrc atxt aprev aob|kids img label ob|nesc nimg nlab nob|kids img esc depth dst ob|asrc atxt aob];
    try contradiction; apply nonempty_ofinish.
  - apply ostate_nonempty_emit.
  - cbn [iscan_productive] in Hres.
    apply orb_true_iff in Hres as [Hres|Hres];
      [apply ostate_nonempty_flush_str, Hres
      |apply ostate_nonempty_flush, Hres].
  - apply ostate_nonempty_emit.
  - apply ostate_nonempty_emit.
  - apply ostate_nonempty_emit.
  - pose proof (bspan_lit_productive kids img ssrc sob) as Hs.
    destruct (bspan_lit kids img ssrc sob) as [txt o']; cbn [fst snd] in Hs.
    apply orb_true_iff in Hs as [Hs|Hs];
      [apply ostate_nonempty_flush_str, Hs | apply ostate_nonempty_flush, Hs].
  - pose proof (bref_lit_productive kids img label ob) as Hr.
    destruct (bref_lit kids img label ob) as [txt o']; cbn [fst snd] in Hr.
    apply orb_true_iff in Hr as [Hr|Hr];
      [apply ostate_nonempty_flush_str, Hr | apply ostate_nonempty_flush, Hr].
  - pose proof (bnote_lit_productive nesc nimg nlab nob) as Hn.
    destruct (bnote_lit nesc nimg nlab nob) as [txt o']; cbn [fst snd] in Hn.
    apply orb_true_iff in Hn as [Hn|Hn];
      [apply ostate_nonempty_flush_str, Hn | apply ostate_nonempty_flush, Hn].
  - pose proof (bdest_lit_productive kids img esc dst ob) as Hd.
    destruct (bdest_lit kids img esc dst ob) as [txt o']; cbn [fst snd] in Hd.
    apply orb_true_iff in Hd as [Hd|Hd];
      [apply ostate_nonempty_flush_str, Hd | apply ostate_nonempty_flush, Hd].
  - apply ostate_nonempty_flush_str, nonempty_str_app_l. reflexivity.
Qed.

Lemma iscan_productive_first :
  forall c, iscan_productive (istep c istart) = true.
Proof.
  intros c. unfold istart. cbn [istep]. unfold ilead.
  destruct (is_bslash c); [reflexivity|].
  destruct (is_tick c); [reflexivity|].
  destruct (Ascii.eqb c dollar); [reflexivity|].
  destruct (Ascii.eqb c period); [reflexivity|].
  destruct (Ascii.eqb c hyphen); [reflexivity|].
  destruct (Ascii.eqb c lbrace); [reflexivity|].
  destruct (Ascii.eqb c bang); [reflexivity|].
  destruct (Ascii.eqb c lt); [reflexivity|].
  destruct (Ascii.eqb c lbrack); [reflexivity|].
  (* nothing is open at the start, so a `]` is text *)
  destruct (Ascii.eqb c rbrack); [reflexivity|].
  (* and nothing is pushed, so a `^` is the superscript row *)
  destruct (Ascii.eqb c hat && note_pos EmptyString None)%bool;
    destruct (dstyle_of c); reflexivity.
Qed.

Lemma parse_inline_line_nonempty :
  forall s, nonempty_str s = true -> nonempty (parse_inline_line s) = true.
Proof.
  intros [|c rest] H; [discriminate|].
  unfold parse_inline_line. cbn [iscan_str].
  apply iscan_productive_finish, iscan_productive_str, iscan_productive_first.
Qed.

Lemma parse_inline_line_escape :
  forall s, nonempty_str s = true ->
  parse_inline_line (escape_str s) = [mk (Str s)].
Proof.
  intros s H. unfold parse_inline_line, istart. rewrite iscan_escape.
  change (EmptyString ++ s)%string with s.
  unfold ifinish, ifinish_rev, ifinish_ostate, iresolve, flush_text.
  rewrite H. reflexivity.
Qed.

(* A paragraph's lines, in order, into inlines: one scan, with `ibreak`
   between lines.  It was a scan per line joined by `SoftBreak` until
   spans were allowed to cross a break; the two agree exactly when no
   line leaves the scan mid-span, which is what the canonical view
   guarantees and `para_inlines_cons2_closed` states. *)
Definition para_inlines (l : list string) : inlines :=
  ifinish (iscan_lines l istart).

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
  rewrite iscan_lines_cons2, (ibreak_closed _ Hcl).
  change (IText false EmptyString None
            (OState (mk SoftBreak :: ifinish_rev (iscan_str x istart)) []))
    with (iout_app (mk SoftBreak :: ifinish_rev (iscan_str x istart)) istart).
  rewrite iscan_lines_out_app, ifinish_out_app by reflexivity.
  cbn [List.rev]. rewrite <- List.app_assoc. reflexivity.
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

(** Parsing a canonical line's text gives back its inlines. *)
Lemma parse_inline_line_ci :
  forall cis, cis_ok cis = true -> nonempty cis = true ->
  parse_inline_line (ci_line cis) = ci_inlines cis.
Proof.
  intros cis Hok Hne.
  unfold parse_inline_line, istart, ostart, ci_line.
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
      by (unfold ci_line, istart; apply iscan_cis_closed, Hc).
    rewrite ci_para_cons2, (parse_inline_line_ci cis Hc Hn).
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
  | _ => EmptyString
  end.

Lemma inline_text_ci_ast : forall ci, inline_text (node_contents (ci_ast ci)) = ci_src ci.
Proof.
  fix IH 1. intro ci.
  destruct ci as [s|s|k kids|img kids dst|rimg rkids rlabel|label|a];
    [reflexivity|reflexivity| | | |reflexivity
    |cbn [ci_ast ci_src]; unfold auto_node;
     destruct (auto_email a); reflexivity].
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
  destruct ci as [s|s|k kids|img kids dst|rimg rkids rlabel|label|a];
    [reflexivity|reflexivity| | | |reflexivity
    |cbn [ci_ast ci_src]; unfold auto_node;
     destruct (auto_email a); reflexivity].
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
    cis_ok cis = true -> nonempty cis = true ->
    inline_lines (ci_inlines cis ++ rest)%list cur
    = inline_lines rest (cur ++ ci_line cis).
Proof.
  intros cis cur rest Hok Hne. clear Hok Hne.
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
    rewrite inline_lines_ci_inlines by assumption.
    reflexivity.
  - rewrite ci_para_cons2.
    rewrite inline_lines_ci_inlines by assumption.
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
and the examples below.  A second one lives in `check/Markdown.v`, which
names it explicitly rather than putting it in scope -- two instances of
one class in one scope is how the wrong table gets inferred.
*)

#[export] Instance djot_table : dtable :=
  DTable djot_config eq_refl.

(* The Markdown-like table, as an instance but deliberately *not* an
   `Instance`: it is named where it is wanted (`check/Markdown.v`) so
   that inference in this development always means djot's. *)
Definition markdown_table : dtable :=
  DTable markdown_config eq_refl.

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

(* A marker overrides both the open rule and the side: a braced opener
   opens where an apostrophe would otherwise be meant, and an abandoned
   one decays to the left form. *)
Example marked_squote_opens :
  parse_inline_line "{'a'}" = [mk (Quoted SingleQuotes [mk (Str "a")])].
Proof. vm_compute. reflexivity. Qed.

Example marked_squote_abandoned_is_left :
  parse_inline_line "{'a" = [mk (Str (lsquo ++ "a"))].
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

(* A delimiter opened inside a label is abandoned by the close, since the
   label is a scope and the delimiter did not close inside it. *)
Example link_label_abandons_opener :
  parse_inline_line "[_a](b)_"
  = [mk (Link [mk (Str "_a")] (Direct "b")); mk (Str "_")].
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
   uses.  This is `oattach` -- there is no pending text when the second
   `{` arrives, so the span node itself is the target. *)
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

(* A spec still attaches, because the reference is a node and `oattach`
   takes the last one emitted. *)
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

(* The divergence.  djot.js decides with a regex lookahead and, when it
   fails, rescans the region as ordinary inline content: `<_a_>` is
   `&lt;<em>a</em>&gt;` there and `&lt;_a_&gt;` here.  A scanner that
   re-reads no byte cannot do the second pass, and the canonical view
   cannot produce the shape -- `escape_str` claims the `<`. *)
Example auto_failed_region_is_flat :
  parse_inline_line "<_a_>" = [mk (Str "<_a_>")].
Proof. vm_compute. reflexivity. Qed.

Example auto_failed_region_keeps_escapes :
  parse_inline_line "<a\*b>" = [mk (Str "<a\*b>")].
Proof. vm_compute. reflexivity. Qed.

(* Canonical text escapes the `<`, so a `Str` can never spell one. *)
Example auto_bracket_escaped_in_canonical_text :
  ci_line [CIStr "<a:b>"] = "\<a:b>".
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

(* Nothing at all before it is the case we do not follow djot.js on: it
   drops the spec, and a heading whose whole content is one would then
   have no children, which `wf_block` excludes.  The source stays. *)
Example attr_with_nothing_before_is_text :
  parse_inline_line "{#i} x"
  = [mk (Str "{#i} x")].
Proof. vm_compute. reflexivity. Qed.
