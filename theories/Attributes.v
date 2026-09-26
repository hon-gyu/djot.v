(* ai-disclosure: autonomous *)

(* Attribute specs, `{#id .class key=value}`, as a character state machine.

   Transcribed from djot.js `src/attributes.ts`, which is already an
   explicit state machine, so the transcription is close to line by line.
   Two deliberate departures, neither of them observable:

   - djot.js records *positions* into the whole document and recovers a
     token's text with `substring`, so a token spanning a line break
     silently picks up the newline and the next line's indentation.  Here
     a token is accumulated character by character and the newline is fed
     explicitly at the end of every line, which yields the same text
     because value collapsing turns any whitespace run into one space.

   - `SCANNING_QUOTED_VALUE_CONTINUATION` and
     `SCANNING_ESCAPED_IN_CONTINUATION` exist only to restart that
     position bookkeeping after a newline.  With an accumulator there is
     nothing to restart, so they are merged into `AQuot` and `AEsc`.

   The machine survives between lines, which is what lets a spec continue
   over an indented line break; `Step.v` carries it in `PAttr`. *)

From Stdlib Require Import String Ascii Bool List.
From DjotV Require Import Strings Ast.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope char_scope.

(*
Character classes
=================
*)

Definition bslash : ascii := "092".
Local Definition dquote : ascii := """".

(* `reKeyChar`: keys, bare values and class names. *)
Local Definition is_key_char (c : ascii) : bool :=
  let n := Ascii.nat_of_ascii c in
  (Nat.leb 97 n && Nat.leb n 122)          (* a-z *)
  || (Nat.leb 65 n && Nat.leb n 90)        (* A-Z *)
  || (Nat.leb 48 n && Nat.leb n 57)        (* 0-9 *)
  || Ascii.eqb c "_" || Ascii.eqb c ":" || Ascii.eqb c "-".

(* Whitespace as the attribute machine sees it: JavaScript's `\s`.  Unlike
   `Strings.is_ws` it includes the line feed, which the machine is fed at
   the end of every line. *)
Definition attr_ws (c : ascii) : bool :=
  is_ws c || Ascii.eqb c "010" || Ascii.eqb c "012" || Ascii.eqb c "011".

(* Identifiers take anything that is neither whitespace nor one of the
   punctuation characters below.  This is djot.js's class, wider than the
   rule the prose spec gives; `{#a<b}` fails because of `<`. *)
Definition is_id_char (c : ascii) : bool :=
  negb (attr_ws c) &&
  negb (List.existsb (Ascii.eqb c)
    ["]"; "["; "~"; "!"; "@"; "#"; "$"; "%"; "^"; "&"; "*"; "("; ")";
     "{"; "}"; "`"; ","; "."; "<"; ">"; bslash; "|"; "="; "+"; "/"; "?"]).

(* Class names are narrower: `\w` plus `:` and `-`, which is exactly the
   key-character class. *)
Local Definition is_attr_class_char (c : ascii) : bool := is_key_char c.

(*
Value normalization
===================

Two rewrites of a value's text before it is stored: whitespace runs
collapse to one space, then backslash escapes of punctuation resolve.
Collapsing first makes a value spanning several indented lines come out
as one line. *)

Local Definition collapse_char (c : ascii) : bool :=
  Ascii.eqb c " " || Ascii.eqb c "013" || Ascii.eqb c "010".

(* `skip` is "the previous character was part of a run already emitted". *)
Local Fixpoint collapse_from (skip : bool) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
      if collapse_char c
      then if skip then collapse_from true s' else String " " (collapse_from true s')
      else String c (collapse_from false s')
  end.

Local Definition collapse_ws (s : string) : string := collapse_from false s.

(* The punctuation a backslash may escape inside a value. *)
Local Definition is_escapable (c : ascii) : bool :=
  List.existsb (Ascii.eqb c)
    ["."; ","; bslash; "/"; "#"; "!"; "$"; "%"; "^"; "&"; "*"; ";"; ":";
     "{"; "}"; "="; "-"; "_"; "`"; "~"; "+"; "["; "]"; "("; ")"; "'";
     dquote; "?"; "|"].

Local Fixpoint unescape (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' =>
      if Ascii.eqb c bslash
      then match s' with
           | EmptyString => String c EmptyString
           | String d s'' =>
               if is_escapable d
               then String d (unescape s'')
               else String c (unescape s')
           end
      else String c (unescape s')
  end.

Local Definition norm_value (s : string) : string := unescape (collapse_ws s).

(*
The machine
===========
*)

Inductive astate : Type :=
  | AScan                (* between attributes *)
  | AId                  (* after '#' *)
  | AClass               (* after '.' *)
  | AKey                 (* accumulating a key, '=' not yet seen *)
  | AVal                 (* just past '=' *)
  | ABare                (* unquoted value *)
  | AQuot                (* inside a double-quoted value *)
  | AEsc                 (* backslash inside a quoted value *)
  | AComment             (* inside %...% *)
  | AFail
  | ADone.

(* `ap_tok` accumulates the current token in reverse; `ap_key` holds the
   key whose value is being scanned; `ap_attrs` is what has been
   committed, in source order. *)
Record aparser : Type := AP
  { ap_st : astate
  ; ap_tok : list ascii
  ; ap_key : string
  ; ap_attrs : attr }.

Definition ap_init : aparser := AP AScan [] EmptyString [].

Definition ap_token (p : aparser) : string := rev_chars (ap_tok p).

Definition ap_push (c : ascii) (p : aparser) : aparser :=
  AP (ap_st p) (c :: ap_tok p) (ap_key p) (ap_attrs p).

Local Definition ap_goto (s : astate) (p : aparser) : aparser :=
  AP s (ap_tok p) (ap_key p) (ap_attrs p).

(* Enter s with a fresh token. *)
Definition ap_begin (s : astate) (p : aparser) : aparser :=
  AP s [] (ap_key p) (ap_attrs p).

(* Commit the accumulated token as an identifier and go to s.  An empty
   token commits nothing, so `{# }` is attribute-free rather than an
   error.  Same for classes. *)
Definition ap_commit_id (s : astate) (p : aparser) : aparser :=
  let t := ap_token p in
  AP s [] (ap_key p)
     (if String.eqb t EmptyString then ap_attrs p else Attr.set "id" t (ap_attrs p)).

Local Definition ap_commit_class (s : astate) (p : aparser) : aparser :=
  let t := ap_token p in
  AP s [] (ap_key p)
     (if String.eqb t EmptyString then ap_attrs p else Attr.add_class t (ap_attrs p)).

(* A value always commits, empty included, so `{a=""}` carries an `a`. *)
Local Definition ap_commit_value (s : astate) (p : aparser) : aparser :=
  AP s [] (ap_key p)
     (Attr.set (ap_key p) (norm_value (ap_token p)) (ap_attrs p)).

Definition astep (p : aparser) (c : ascii) : aparser :=
  match ap_st p with
  | ADone | AFail => p
  | AScan =>
      if attr_ws c then p
      else if Ascii.eqb c "}" then ap_goto ADone p
      else if Ascii.eqb c "#" then ap_begin AId p
      else if Ascii.eqb c "%" then ap_begin AComment p
      else if Ascii.eqb c "." then ap_begin AClass p
      else if is_key_char c then ap_push c (ap_begin AKey p)
      else ap_goto AFail p
  | AId =>
      if is_id_char c then ap_push c p
      else if Ascii.eqb c "}" then ap_commit_id ADone p
      else if attr_ws c then ap_commit_id AScan p
      else ap_goto AFail p
  | AClass =>
      if is_attr_class_char c then ap_push c p
      else if Ascii.eqb c "}" then ap_commit_class ADone p
      else if attr_ws c then ap_commit_class AScan p
      else ap_goto AFail p
  | AKey =>
      if Ascii.eqb c "=" then AP AVal [] (ap_token p) (ap_attrs p)
      else if is_key_char c then ap_push c p
      else ap_goto AFail p
  | AVal =>
      if Ascii.eqb c dquote then ap_begin AQuot p
      else if is_key_char c then ap_push c (ap_begin ABare p)
      else ap_goto AFail p
  | ABare =>
      if is_key_char c then ap_push c p
      else if Ascii.eqb c "}" then ap_commit_value ADone p
      else if attr_ws c then ap_commit_value AScan p
      else ap_goto AFail p
  | AQuot =>
      if Ascii.eqb c dquote then ap_commit_value AScan p
      else if Ascii.eqb c bslash then ap_goto AEsc (ap_push c p)
      else ap_push c p
  | AEsc => ap_goto AQuot (ap_push c p)
  | AComment =>
      if Ascii.eqb c "%" then ap_begin AScan p
      else if Ascii.eqb c "}" then ap_goto ADone p
      else p
  end.

(* Feed a string, stopping at the first terminal state; the second result
   is what was left unread, which is how "the spec ended before the line
   did" is detected. *)
Fixpoint afeed (s : string) (p : aparser) : aparser * string :=
  match s with
  | EmptyString => (p, EmptyString)
  | String c s' =>
      match ap_st p with
      | ADone | AFail => (p, s)
      | _ => afeed s' (astep p c)
      end
  end.

Definition ap_done (p : aparser) : bool :=
  match ap_st p with ADone => true | _ => false end.

Definition ap_failed (p : aparser) : bool :=
  match ap_st p with AFail => true | _ => false end.

(*
The line interface
==================

Both entry points feed the line's content with its indentation dropped,
followed by the newline that ended it.  The newline closes an identifier
or a bare value at end of line, and separates the pieces of a value that
spans lines. *)

Definition attr_nl : string := String "010" EmptyString.

(* Nothing but whitespace, newline included. *)
Fixpoint blank_to_eol (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c s' => attr_ws c && blank_to_eol s'
  end.

(* Whether this line opens a block attribute spec, and in what state.
   `None` when the machine fails or the spec closes with content still on
   the line; either way the line is paragraph text. *)
Definition attr_open (l : string) : option aparser :=
  match drop_leading_ws l with
  | String "{" body =>
      let (p, rest) := afeed (body ++ attr_nl) ap_init in
      if ap_failed p then None
      else if ap_done p && negb (blank_to_eol rest) then None
      else Some p
  | _ => None
  end.

(* A continuation line, already known to be indented past the opener. *)
Definition attr_feed (l : string) (p : aparser) : aparser :=
  fst (afeed (drop_leading_ws l ++ attr_nl) p).

(* Leading whitespace is invisible here, as it is to every other
   recognizer: `attr_open` starts at the first nonblank character. *)
Lemma attr_open_ws_prefix :
  forall p l, is_blank p = true -> attr_open (p ++ l) = attr_open l.
Proof.
  intros p l Hp. unfold attr_open. rewrite (drop_leading_ws_ws_prefix p l Hp).
  reflexivity.
Qed.

(*
Printing
========

A spec that reads back to the attributes it was printed from: `#id` and
`.class` where the characters allow, `key="value"` otherwise.  A value
cannot keep a whitespace run or a line break, which `norm_value`
collapses, so an attribute holding one reads back collapsed. *)

Fixpoint id_chars_ok (id : string) : bool :=
  match id with
  | EmptyString => true
  | String c rest => is_id_char c && id_chars_ok rest
  end.

Definition explicit_id_ok (id : string) : bool :=
  nonempty_str id && id_chars_ok id.

(* A class entry spelled as `.a .b`: words of class characters, one space
   apart. *)
Local Fixpoint class_words_ok (after_space : bool) (s : string) : bool :=
  match s with
  | EmptyString => negb after_space
  | String c rest =>
      if Ascii.eqb c " " then negb after_space && class_words_ok true rest
      else is_attr_class_char c && class_words_ok false rest
  end.

Definition classes_ok (s : string) : bool := nonempty_str s && class_words_ok true s.

(* One class word, which a div fence can carry. *)
Local Fixpoint class_chars_ok (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c rest => is_attr_class_char c && class_chars_ok rest
  end.

Definition class_word_ok (s : string) : bool := nonempty_str s && class_chars_ok s.

Local Fixpoint dot_words (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if Ascii.eqb c " " then String c (String "." (dot_words rest))
      else String c (dot_words rest)
  end.

Local Fixpoint escape_value (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if Ascii.eqb c dquote || Ascii.eqb c bslash
      then String bslash (String c (escape_value rest))
      else String c (escape_value rest)
  end.

Definition attr_part (kv : string * string) : string :=
  let (k, v) := kv in
  if String.eqb k "id" && explicit_id_ok v then String "#" v
  else if String.eqb k "class" && classes_ok v then String "." (dot_words v)
  else (k ++ "=" ++ String dquote (escape_value v ++ String dquote EmptyString))%string.

(* The spec for a nonempty attribute set; the empty set has none. *)
Definition attr_spec (a : attr) : string :=
  match a with
  | [] => EmptyString
  | _ => ("{" ++ String.concat " " (map attr_part a) ++ "}")%string
  end.
