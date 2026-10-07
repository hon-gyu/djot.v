(* ai-disclosure: autonomous *)

(* The syntax of an attribute specifier (syntax reference, "Inline
   attributes", "Comment", "Block attributes"), stated as a grammar of
   the text between its braces and independent of the machine that reads
   it: the characters, the items, how they are separated, and the
   attributes they give.  `AttrAgree.v` proves the machine of
   `Attributes.v` accepts exactly this grammar, with these attributes.

   Where a spec may begin and what it attaches to are not here: that is
   block and inline structure.

   Where the reference is silent the grammar follows djot.js, and says
   so; each such choice is a `SPEC-GAP` in `djotjs-divergences.md`. *)

From Stdlib Require Import String Ascii Bool List.
From DjotV Require Import Strings Ast.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope char_scope.

(*
Characters
==========
*)

Local Definition code_in (lo hi : nat) (c : ascii) : bool :=
  Nat.leb lo (nat_of_ascii c) && Nat.leb (nat_of_ascii c) hi.

Local Definition one_of (cs : string) (c : ascii) : bool :=
  existsb (Ascii.eqb c) (list_ascii_of_string cs).

Definition ascii_alnum (c : ascii) : bool :=
  code_in 48 57 c || code_in 65 90 c || code_in 97 122 c.

(* The 32 ASCII punctuation characters, `!` to `/`, `:` to `@`, `[` to
   `` ` `` and `{` to `~`. *)
Definition ascii_punct (c : ascii) : bool :=
  code_in 33 47 c || code_in 58 64 c || code_in 91 96 c || code_in 123 126 c.

(* Whitespace: space, tab, line feed, vertical tab, form feed, carriage
   return.  The reference does not say; this is djot.js's `\s` over
   ASCII.  A spec may span lines, so a line feed is whitespace here. *)
Definition attr_space (c : ascii) : bool := code_in 9 13 c || Ascii.eqb c " ".

(* "Quotes are not needed when the value consists entirely of ASCII
   alphanumeric characters or `_` or `:` or `-`". *)
Definition bare_char (c : ascii) : bool := ascii_alnum c || one_of "_:-" c.

(* Keys and class names: the reference does not say.  djot.js takes the
   characters of a bare value. *)
Definition key_char (c : ascii) : bool := bare_char c.
Definition class_char (c : ascii) : bool := bare_char c.

(* Identifiers: the reference does not say.  djot.js takes any byte that
   is not whitespace and not ASCII punctuation, where colon, underscore,
   hyphen, semicolon and the two quote marks do not count as
   punctuation.  Non-ASCII bytes are identifier characters. *)
Definition id_char (c : ascii) : bool :=
  negb (attr_space c) && negb (ascii_punct c && negb (one_of ":_-;'""" c)).

(* A comment runs to the next `%` or to the end of the spec. *)
Definition comment_char (c : ascii) : bool := negb (one_of "%}" c).

Fixpoint all (p : ascii -> bool) (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => p c && all p s'
  end.

Definition key (k : string) : Prop := k <> EmptyString /\ all key_char k = true.

(*
Values
======

"Backslash escapes may be used inside quoted values."  Which characters
a backslash escapes, the reference does not say: djot.js takes ASCII
punctuation except `<`, `>` and `@`, where text escapes take all of it.
A backslash before anything else stands for itself.  After the escapes,
every run of spaces, carriage returns and line feeds is one space, which
is what lets a value span lines; a tab is kept.  The reference does not
say that either. *)

Definition escapable (c : ascii) : bool := ascii_punct c && negb (one_of "<>@" c).

Definition escape (c : ascii) : string :=
  if escapable c then String c EmptyString else String "\" (String c EmptyString).

Local Definition run_char (c : ascii) : bool := one_of (String " " (String "013" (String "010" EmptyString))) c.

(* `in_run`: the previous character was in a run already written. *)
Fixpoint collapse_from (in_run : bool) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
      if run_char c
      then if in_run then collapse_from true s' else String " " (collapse_from true s')
      else String c (collapse_from false s')
  end.

Definition collapse (s : string) : string := collapse_from false s.

(* The text between the quotes, and the characters it stands for before
   whitespace is collapsed.  The byte after a backslash never ends the
   value, so a backslash before a double quote keeps the value open. *)
Inductive quoted : string -> string -> Prop :=
  | QEnd : quoted EmptyString EmptyString
  | QChar : forall c q v, c <> """" -> c <> "\" -> quoted q v ->
      quoted (String c q) (String c v)
  | QEsc : forall c q v, quoted q v ->
      quoted (String "\" (String c q)) (escape c ++ v).

(*
Items
=====
*)

Inductive item : Type :=
  | IId (name : string)           (* `#name`; an empty name sets nothing *)
  | IClass (name : string)        (* `.name`; likewise *)
  | IPair (key value : string)    (* `key=value`, the value as stored *)
  | IComment.                     (* `%...%` *)

Local Definition dq : string := String """" EmptyString.

(* Items that end themselves: a quoted pair and a closed comment. *)
Inductive closed_item : string -> item -> Prop :=
  | CQuoted : forall k q v, key k -> quoted q v ->
      closed_item (k ++ "=" ++ dq ++ q ++ dq) (IPair k (collapse v))
  | CComment : forall t, all comment_char t = true ->
      closed_item ("%" ++ t ++ "%") IComment.

(* Items that must be followed by whitespace or by the closing brace:
   `{.a.b}` and `{.a%c%}` are not specs. *)
Inductive open_item : string -> item -> Prop :=
  | OId : forall n, all id_char n = true -> open_item ("#" ++ n) (IId n)
  | OClass : forall n, all class_char n = true -> open_item ("." ++ n) (IClass n)
  | OBare : forall k v, key k -> v <> EmptyString -> all bare_char v = true ->
      open_item (k ++ "=" ++ v) (IPair k v).

(* The text between `{` and the `}` that ends the spec. *)
Inductive body : string -> list item -> Prop :=
  | BEnd : body EmptyString []
  | BSpace : forall c b is, attr_space c = true -> body b is ->
      body (String c b) is
  | BClosed : forall s i b is, closed_item s i -> body b is ->
      body (s ++ b) (i :: is)
  | BLast : forall s i, open_item s i -> body s [i]
  | BOpen : forall s i c b is, open_item s i -> attr_space c = true -> body b is ->
      body (s ++ String c b) (i :: is)
  (* "`%` begins a comment, which ends with the next `%` or the end of
     the attribute (`}`)". *)
  | BOpenComment : forall t, all comment_char t = true ->
      body ("%" ++ t) [IComment].

(*
Attributes
==========

Read left to right.  "if multiple identifiers are given, the last one is
used"; classes "will be combined"; a key given twice keeps its last
value, which the reference does not say.  A `class` key is a key like
any other: it replaces the classes before it in the same spec, while a
later spec's `class` is combined with them (`Attr.merge`), so
`{.x class="y"}` is not the same as `{.x}{class="y"}` (`SPEC-GAP`). *)

Definition add_item (a : attr) (i : item) : attr :=
  match i with
  | IId n => if String.eqb n EmptyString then a else Attr.set "id" n a
  | IClass n => if String.eqb n EmptyString then a else Attr.add_class n a
  | IPair k v => Attr.set k v a
  | IComment => a
  end.

Definition attrs_of (is : list item) : attr := fold_left add_item is [].

(* A whole specifier. *)
Definition spec (s : string) (is : list item) : Prop :=
  exists b, s = String "{" (b ++ String "}" EmptyString) /\ body b is.
