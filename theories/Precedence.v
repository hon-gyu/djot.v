(* ai-disclosure: autonomous *)

(* Inline syntax, stated as a reading of a paragraph's bytes and
   independent of the scanner: the tokens, the readings the reference's
   precedence rules allow (syntax reference, "Precedence"), and the tree
   a reading describes.  Definitions only.
   `PrecedenceFacts.v` proves that exactly one reading is valid,
   `InlinePrecedence.v` that the scanner builds its tree, and
   `PrecedenceGrammar.v` states the rules again as a grammar. *)

From Stdlib Require Import String Ascii List Bool Lia Arith Sorted.
From DjotV Require Import Strings Ast Attributes InlineTable InlineView.
Import ListNotations.

Local Open Scope string_scope.

Section WithTable.
Context {T : dtable}.

(*
Tokens
======

Every row of the table that is on is covered: in djot's, `_ * ^ ~`
written bare or in braces, `= +` written only in braces, and the two
quotes.  An unmatched token of a row is its own text, or for a quote a
curly quote (`delim_lit` below). *)

(* The bytes a line is drawn from: the characters of the rows, the
   braces, the brackets, the backtick, `<`, `!`, `.`, `-` while the row
   spelled with it is one hyphen wide (`hyphen_row_ok`), `:` while tags
   are off, and
   bytes that no row and no other syntax claims, the parens among them.  A paren is not a row's character
   here, since a destination counts parens.  The newline ends the
   line; the `$` is drawn on while dollar math is off, and a hole's `%`
   is not drawn on while holes are on. *)
Definition in_alphabet (c : ascii) : bool :=
  (negb (Ascii.eqb c nl_char)
   && (Ascii.eqb c lbrace || Ascii.eqb c rbrace || Ascii.eqb c lbrack
       || Ascii.eqb c rbrack || is_tick c || Ascii.eqb c lt || Ascii.eqb c bang
       || Ascii.eqb c period
       || (Ascii.eqb c ":"%char && negb tags_enabled)
       || (Ascii.eqb c dollar && negb dollar_math_enabled)
       || (negb (dreserved c) && negb (holes_enabled && Ascii.eqb c percent)))
   && (negb (Ascii.eqb c hyphen) || hyphen_row_ok)
   && match dstyle_of c with
      | Some _ => negb (Ascii.eqb c lparen || Ascii.eqb c rparen)
      | None => true
      end)%bool.

Definition starts_row (s : string) : bool :=
  match s with String d _ => is_delim d | EmptyString => false end.

Definition starts_with (c : ascii) (s : string) : bool :=
  match s with String d _ => Ascii.eqb d c | EmptyString => false end.

(* The format of a raw spec `{=FORMAT}` that `s` begins with (R1): a
   nonempty run of bytes that are not whitespace, a backtick, a brace or
   the newline. *)
Fixpoint fmt_go (s : string) : option string :=
  match s with
  | EmptyString => None
  | String c r =>
      if Ascii.eqb c rbrace then Some EmptyString
      else if (raw_stop c || Ascii.eqb c nl_char)%bool then None
      else option_map (String c) (fmt_go r)
  end.

Definition raw_spec (s : string) : option string :=
  match s with
  | String b (String e r) =>
      if (Ascii.eqb b lbrace && Ascii.eqb e eqchar)%bool
      then match fmt_go r with Some (String c f) => Some (String c f) | _ => None end
      else None
  | _ => None
  end.

(* Whether a byte ends an autolink candidate: the `>`, whitespace, a
   second `<`, or the end of the line (A2). *)
Definition auto_stop (c : ascii) : bool :=
  (Ascii.eqb c gt || is_ws c || Ascii.eqb c lt || Ascii.eqb c nl_char)%bool.

(* The region of an autolink candidate, and the byte that ended it. *)
Fixpoint auto_go (s : string) : string * option ascii :=
  match s with
  | EmptyString => (EmptyString, None)
  | String c r =>
      if auto_stop c then (EmptyString, Some c)
      else let '(src, stop) := auto_go r in (String c src, stop)
  end.

(* The run of symbol characters a string begins with. *)
Fixpoint symbol_run (s : string) : nat :=
  match s with
  | String c r => if symbol_char c then S (symbol_run r) else 0
  | EmptyString => 0
  end.

(* An attribute spec read from after its `{` (AT1): the bytes before the
   `}` that ends it, anywhere in the paragraph, and its attributes.  The
   machine is the one block attributes use (`Attributes.v`), and it reads
   a line break as whitespace, or as a byte of a quoted value, and a
   backslash as an escape in a quoted value. *)
Fixpoint spec_go (p : aparser) (s : string) : option (string * attr) :=
  match s with
  | EmptyString => None
  | String c r =>
      let p' := astep p c in
      if ap_failed p' then None
      else if ap_done p' then Some (EmptyString, ap_attrs p')
      else match spec_go p' r with
           | Some (b, a) => Some (String c b, a)
           | None => None
           end
  end.

(* The spec after a `{`, while inline attributes are on. *)
Definition spec_at (s : string) : option (string * attr) :=
  if inline_attrs_enabled then spec_go ap_init s else None.

(* The label of a footnote reference, read from after its `[^` (F1): the
   bytes before the `]` that ends it, anywhere in the paragraph.  A
   backslash keeps the byte after it from ending the label, and stays in
   it.  A line break in a label is whitespace to `normalize_label`. *)
Fixpoint note_go (esc : bool) (s : string) : option string :=
  match s with
  | EmptyString => None
  | String c r =>
      if esc then option_map (String c) (note_go false r)
      else if is_bslash c then option_map (String c) (note_go true r)
      else if Ascii.eqb c rbrack then Some EmptyString
      else option_map (String c) (note_go false r)
  end.

(* The label after a `[`, while footnotes are on. *)
Definition note_at (s : string) : option string :=
  match s with
  | String c r => if (notes_enabled && Ascii.eqb c hat)%bool then note_go false r else None
  | EmptyString => None
  end.

(* The `)` that balances an open `(`, `i` being the offset of the first
   byte of `s`.  An escaped byte counts no paren. *)
Fixpoint dest_close (esc : bool) (depth i : nat) (s : string) : option nat :=
  match s with
  | EmptyString => None
  | String c rest =>
      if esc then dest_close false depth (S i) rest
      else if is_bslash c then dest_close true depth (S i) rest
      else if Ascii.eqb c lparen then dest_close false (S depth) (S i) rest
      else if Ascii.eqb c rparen
      then match depth with O => Some i | S d => dest_close false d (S i) rest end
      else dest_close false depth (S i) rest
  end.

(* The first `]` not escaped. *)
Fixpoint label_close (esc : bool) (i : nat) (s : string) : option nat :=
  match s with
  | EmptyString => None
  | String c rest =>
      if esc then label_close false (S i) rest
      else if is_bslash c then label_close true (S i) rest
      else if Ascii.eqb c rbrack then Some i
      else label_close false (S i) rest
  end.

(* The run of `c` a string begins with. *)
Fixpoint run_of (c : ascii) (s : string) : nat :=
  match s with
  | String d r => if Ascii.eqb d c then S (run_of c r) else 0
  | EmptyString => 0
  end.

(* What may follow a byte: with wikilinks on, a `[` before a `[`, which
   begins a wikilink, is not drawn on. *)
Definition follow_ok (c : ascii) (rest : string) : bool :=
  negb (Ascii.eqb c lbrack && wikilinks_enabled && starts_with lbrack rest).

(* A backslash escapes the byte after it, whatever that byte is but the
   newline, so the escaped byte is not drawn on the alphabet (O2, O3). *)
Fixpoint over_alphabet (s : string) : bool :=
  match s with
  | EmptyString => true
  | String c rest =>
      if is_bslash c
      then match rest with
           | EmptyString => true
           | String d rest' =>
               negb (Ascii.eqb d nl_char) && over_alphabet rest'
           end
      else (in_alphabet c && follow_ok c rest && over_alphabet rest)%bool
  end.

(* A text token is one byte, so that every token is nonempty.  A marked
   token is an opener `{_` or a closer `_}`, never both.  A break is a
   newline: a soft break in the tree, and whitespace to the delimiters on
   either side of it.  `TOpen` is a `[`, or a `!` and a `[`, which opens
   an image's bracket (I1); a `!` before anything else is text.
   `TClose` is a `]` followed by
   `(` and a destination that closes (`dest`), or by `[` and a reference
   label that closes, with the region's bytes between; a `]` before
   anything else is text.

   A backslash and what follows it are an escape (O2 to O5): before
   whitespace that runs to the end of the line, a hard break (`THard`,
   with that whitespace); before a run of whitespace that does not, the
   run (`TEscWs`), which is a non-breaking space and the rest of the run
   when it begins with a space; before any other byte, that byte as text
   if it is punctuation, and the backslash and the byte otherwise
   (`TEsc`).

   A run of `n` backticks opens a verbatim (V1), which runs to the next
   run of exactly `n` (`closed`) or to the paragraph's end; its body is
   every byte between, backslashes and newlines included (V2, V4).  While
   math is on, a run of `pre` dollars right before it is part of it
   (MA1): one makes inline math, more make display math, and the dollars
   before the last two are text.  Any other run of dollars is text
   (`TDollars`).  A closed verbatim with no dollars before it takes the
   raw spec right after it, while raw inline is on (`raw`, R1).

   A `<`, an address and a `>` are an autolink (A1 to A3); any other `<`
   is text.

   A `:`, a nonempty run of symbol characters and a `:` are a symbol
   (`TSymbol`, Y1); any other `:` is text.

   A `{` before a byte that is no row's character begins an attribute
   spec while inline attributes are on (`TAttr`, with the bytes between
   its braces); when no spec closes there the `{` is text.  A `]` before
   a `{` and a spec that closes may close a span (`TSpan`, N1), whose
   region is the spec.

   A `[`, a `^`, a label and the `]` that ends it are a footnote
   reference while footnotes are on (`TNote`, F1); the `[` opens no
   bracket.

   A run of periods is one token (`TDots`), and so is a run of hyphens
   (`TDash`), which before a `}` leaves its last hyphens to be the
   closer of the row spelled with the hyphen (D1). *)
Inductive token : Type :=
  | TText (c : ascii)
  | TBreak
  | TDelim (k : dstyle) (marked opens closes : bool)
  | TOpen (image : bool)
  | TClose (dest : bool) (region : string)
  | TEsc (c : ascii)
  | TEscWs (ws : string)
  | THard (ws : string)
  | TVerb (pre n : nat) (body : string) (closed : bool) (raw : option string)
  | TDollars (k : nat)
  | TAuto (src : string)
  | TSymbol (alias : string)
  | TAttr (body : string) (a : attr)
  | TSpan (body : string) (a : attr)
  | TNote (label : string)
  | TDots (n : nat)
  | TDash (n : nat).

(* The whitespace a string begins with. *)
Fixpoint ws_run (s : string) : string :=
  match s with
  | String c rest => if is_ws c then String c (ws_run rest) else EmptyString
  | EmptyString => EmptyString
  end.

(* The bytes before the first newline. *)
Fixpoint line_rest (s : string) : string :=
  match s with
  | String c rest => if Ascii.eqb c nl_char then EmptyString else String c (line_rest rest)
  | EmptyString => EmptyString
  end.

Fixpoint tick_run (s : string) : nat :=
  match s with
  | String c r => if is_tick c then S (tick_run r) else 0
  | EmptyString => 0
  end.

(* A verbatim's body, read after its opening run of `n`: its bytes, how
   many bytes it takes with its closing run, and whether it closed.
   `run` counts the backticks pending. *)
Fixpoint verb_go (n run : nat) (s : string) : string * nat * bool :=
  match s with
  | EmptyString => if Nat.eqb run n then (EmptyString, 0, true) else (ticks run, 0, false)
  | String c rest =>
      if is_tick c then let '(b, l, cl) := verb_go n (S run) rest in (b, S l, cl)
      else if Nat.eqb run n then (EmptyString, 0, true)
      else let '(b, l, cl) := verb_go n 0 rest in ((ticks run ++ String c b)%string, S l, cl)
  end.

(* A verbatim that `s` begins with, after `pre` dollars, and its length
   without them. *)
Definition verb_tok (pre : nat) (s : string) : token * nat :=
  let n := tick_run s in
  let '(body, used, closed) := verb_go n 0 (sdrop n s) in
  match (if (closed && Nat.eqb pre 0 && raw_inline_enabled)%bool
         then raw_spec (sdrop (n + used) s) else None) with
  | Some f => (TVerb pre n body closed (Some f), n + used + S (S (S (String.length f))))
  | None => (TVerb pre n body closed None, n + used)
  end.

Fixpoint dollar_run (s : string) : nat :=
  match s with
  | String c r => if Ascii.eqb c dollar then S (dollar_run r) else 0
  | EmptyString => 0
  end.

(* An autolink candidate that `s` begins with, past its `<`. *)
Definition auto_tok (s : string) : token * nat :=
  let '(src, stop) := auto_go s in
  if (match stop with Some c => Ascii.eqb c gt | None => false end
      && auto_body_ok src && auto_kind_ok src)%bool
  then (TAuto src, S (S (String.length src)))
  else (TText lt, 1).

(* A symbol that `s` begins with, past its `:`, or the `:` as text. *)
Definition sym_tok (s : string) : token * nat :=
  let k := symbol_run s in
  if (Nat.ltb 0 k && starts_with ":"%char (sdrop k s))%bool
  then (TSymbol (substring 0 k s), S (S k))
  else (TText ":"%char, 1).

(* A run of dollars that `s` begins with: the math it prefixes, or text. *)
Definition dollar_tok (s : string) : token * nat :=
  let k := dollar_run s in
  let rest := sdrop k s in
  if (math_enabled && starts_with tick rest)%bool
  then let '(t, l) := verb_tok k rest in (t, k + l)
  else (TDollars k, k).

Definition at_rbrace (p : option ascii) : bool :=
  match p with Some b => Ascii.eqb b rbrace | None => false end.

(* An escape that `s` begins with, past its backslash (O2 to O5).  A
   backslash that ends the paragraph is a hard break. *)
Definition esc_tok (s : string) : token * nat :=
  if is_blank (line_rest s)
  then (THard (line_rest s), S (String.length (line_rest s)))
  else match s with
       | String d _ =>
           if is_ws d then (TEscWs (ws_run s), S (String.length (ws_run s)))
           else (TEsc d, 2)
       | EmptyString => (THard EmptyString, 1)
       end.

(* The run of periods that `s` begins with. *)
Definition dots_tok (s : string) : token * nat :=
  let n := run_of period s in (TDots n, n).

(* The run of hyphens that `s` begins with.  Before a `}`, the run's last
   hyphens are the closer of the row spelled with the hyphen, when there
   is one and the run is long enough for its token. *)
Definition dash_tok (s : string) : token * nat :=
  let n := run_of hyphen s in
  match dstyle_of hyphen with
  | Some k =>
      if (starts_with rbrace (sdrop n s) && Nat.leb (dwidth k) n)%bool
      then if Nat.eqb n (dwidth k) then (TDelim k true false true, S n)
           else (TDash (n - dwidth k), n - dwidth k)
      else (TDash n, n)
  | None => (TDash n, n)
  end.

(* What a `!` begins, from what `s` has after it: an image's bracket
   before a `[` (I1), or text.  A `[` that begins a footnote reference
   is the reference's, and the `!` before it text, as both djot.js and
   the scanner read it. *)
Definition bang_tok (s : string) : token * nat :=
  if starts_with lbrack s
  then match note_at (sdrop 1 s) with
       | Some _ => (TText bang, 1)
       | None => (TOpen true, 2)
       end
  else (TText bang, 1).

(* What a `[` begins, from what `s` has after it: a footnote reference
   before a `^` and a label that closes (F1), or a bracket. *)
Definition lbrack_tok (s : string) : token * nat :=
  match note_at s with
  | Some l => (TNote l, S (S (S (String.length l))))
  | None => (TOpen false, 1)
  end.

(* What a `]` is, from what `s` has after it: a closer before a
   destination or a reference label that closes (L1, L4), a span's closer
   before a spec that closes (N1), or text. *)
Definition rbrack_tok (s : string) : token * nat :=
  (match s with
   | String c r =>
       let region dest e := match e with
                            | Some e => TClose dest (substring 0 e r)
                            | None => TText rbrack
                            end in
       if Ascii.eqb c lparen then region true (dest_close false 0 0 r)
       else if Ascii.eqb c lbrack then region false (label_close false 0 r)
       else if Ascii.eqb c lbrace
       then match spec_at r with Some (b, a) => TSpan b a | None => TText rbrack end
       else TText rbrack
   | EmptyString => TText rbrack
   end, 1).

(* What a `{` begins, from what `s` has after it: a marked opener before
   a row's token (P3), an attribute spec that closes before any other
   byte (AT1), or text. *)
Definition lbrace_tok (s : string) : token * nat :=
  match (match s with
         | String d _ => dstyle_of d
         | EmptyString => None
         end) with
  | Some k =>
      if prefix (dtoken k) s
      then (TDelim k true true false, S (dwidth k))
      else (TText lbrace, 1)
  | None =>
      match spec_at s with
      | Some (b, a) => (TAttr b a, S (S (String.length b)))
      | None => (TText lbrace, 1)
      end
  end.

(* The token `s` begins with when its first byte `c` begins none of the
   above; `prev` is the byte before `s`.  A run of a row's character is
   cut, left to right, into tokens of the row's width, and a remainder
   shorter than that is text.  A token with `}` after it is a marked
   closer (P3).  A bare token may open when its row may be written bare
   there (`dbare`: a single quote only at the start of a line or after
   whitespace, a quote, a hyphen, `(` or `[`, where no apostrophe can be
   meant, Q1) and the byte after it is not whitespace, and may close
   when the byte before it is not whitespace (M2).  Any other byte is
   text. *)
Definition delim_tok (prev : option ascii) (c : ascii) (s : string) : token * nat :=
  match dstyle_of c with
  | Some k =>
      if prefix (dtoken k) s
      then if at_rbrace (get (dwidth k) s)
           then (TDelim k true false true, S (dwidth k))
           else (TDelim k false
                   (dbare k prev && nonspace_at (get (dwidth k) s))
                   (nonspace_at prev), dwidth k)
      else (TText c, 1)
  | None => (TText c, 1)
  end.

(* The token `s` begins with, and its length; `prev` is the byte before
   `s`.  The first byte says which kind to try. *)
Definition next_tok (prev : option ascii) (s : string) : option (token * nat) :=
  match s with
  | EmptyString => None
  | String c rest =>
      Some
        (if Ascii.eqb c nl_char then (TBreak, 1)
         else if is_bslash c then esc_tok rest
         else if is_tick c then verb_tok 0 s
         else if Ascii.eqb c dollar then dollar_tok s
         else if Ascii.eqb c lt then auto_tok rest
         else if Ascii.eqb c ":"%char then sym_tok rest
         else if Ascii.eqb c period then dots_tok s
         else if Ascii.eqb c hyphen then dash_tok s
         else if Ascii.eqb c bang then bang_tok rest
         else if Ascii.eqb c lbrack then lbrack_tok rest
         else if Ascii.eqb c rbrack then rbrack_tok rest
         else if Ascii.eqb c lbrace then lbrace_tok rest
         else delim_tok prev c s)
  end.

Definition before (s : string) (p : nat) : option ascii :=
  match p with O => None | S q => get q s end.

(* The token at byte `p`, and its length. *)
Definition tok_at (s : string) (p : nat) : option (token * nat) :=
  next_tok (before s p) (sdrop p s).

Definition tok_of (s : string) (p : nat) : option token :=
  option_map fst (tok_at s p).

(* A paragraph's lines, a newline between two of them, the last read
   without its trailing whitespace, as the paragraph's inlines are. *)
Fixpoint para_string (ls : list string) : string :=
  match ls with
  | [] => EmptyString
  | [x] => strip_trailing_ws x
  | x :: rest => (x ++ String nl_char (para_string rest))%string
  end.

(*
Readings
========

A reading says which role each token takes: a list of pairs of byte
offsets, `(i, j)` pairing the opener at `i` with the closer at `j`, and
the list of the tokens that act as openers.  An opener and a closer
pair when they have the same key: a delimiter's style and marking
("explicitly marked closers can only match explicitly marked openers",
P4), or the bracket.

A `]` that pairs closes its bracket, and what follows is a region of
the link syntax: a destination runs to the `)` that balances its `(`,
a reference label to the next `]`, and a span's spec to its `}`.  A
region is source: the reading's tokens are a chain from the first byte,
each followed by the next or, after a `]` that pairs, by the byte after
its region.  A `]` whose region does not close is text (`rbrack_tok`),
so a destination or a label that never ends leaves no trace: its `[`
stays open and the bytes after it are read as usual. *)

Definition matching : Type := list (nat * nat).

Inductive key : Type := KDelim (k : dstyle) (marked : bool) | KBracket.

Definition key_eq (a b : key) : bool :=
  match a, b with
  | KDelim k m, KDelim k' m' => (dstyle_eq k k' && Bool.eqb m m')%bool
  | KBracket, KBracket => true
  | _, _ => false
  end.

(* A delimiter pair encloses something (M3); a bracket pair need not. *)
Definition needs_content (k : key) : bool :=
  match k with KDelim _ _ => true | KBracket => false end.

Definition opens_as (t : token) : option key :=
  match t with
  | TDelim k mr true _ => Some (KDelim k mr)
  | TOpen _ => Some KBracket
  | _ => None
  end.

Definition closes_as (t : token) : option key :=
  match t with
  | TDelim k mr _ true => Some (KDelim k mr)
  | TClose _ _ | TSpan _ _ => Some KBracket
  | _ => None
  end.

Definition open_key (s : string) (i : nat) : option key :=
  match tok_of s i with Some t => opens_as t | None => None end.

Definition close_key (s : string) (j : nat) : option key :=
  match tok_of s j with Some t => closes_as t | None => None end.

(* The byte after the token at `p`. *)
Definition tok_end (s : string) (p : nat) : nat :=
  match tok_at s p with Some (_, l) => p + l | None => p end.

Definition is_opener (m : matching) (i : nat) : bool :=
  existsb (fun e => Nat.eqb (fst e) i) m.

Definition is_closer (m : matching) (j : nat) : bool :=
  existsb (fun e => Nat.eqb (snd e) j) m.

(* A `]` that pairs is followed by its region, which the chain jumps
   past: the byte that opens the region, its text, and the byte that
   closes it. *)
Definition chain_next (s : string) (m : matching) (p : nat) : option nat :=
  match tok_at s p with
  | Some ((TClose _ b | TSpan b _), l) =>
      if is_closer m p then Some (p + S (S (S (String.length b)))) else Some (p + l)
  | Some (_, l) => Some (p + l)
  | None => None
  end.

(* The tokens a reading reads. *)
Inductive chain (s : string) (m : matching) : nat -> Prop :=
  | chain_start : chain s m 0
  | chain_step : forall p q, chain s m p -> chain_next s m p = Some q -> chain s m q.

Definition closes (m : matching) (j : nat) : Prop := exists i, In (i, j) m.

(* Gone by `j`: closed before it, or inside a pair closed before it.  The
   second is the reference's "any potential openers between the opener
   and the closer get marked as regular text"; reading the pairs in the
   order of their closers is "the first opener that gets closed takes
   precedence". *)
Definition dead (m : matching) (j p : nat) : Prop :=
  (exists j', j' < j /\ In (p, j') m)
  \/ (exists i' j', j' < j /\ In (i', j') m /\ i' < p < j').

Definition reading : Type := (matching * list nat)%type.

(* An opener still open at `j`. *)
Definition live (s : string) (m : matching) (os : list nat)
  (j q : nat) (k : key) : Prop :=
  In q os /\ q < j /\ open_key s q = Some k /\ ~ closes m q /\ ~ dead m j q.

(* "When there are multiple openers that might be matched with a given
   closer, the closest one is used." *)
Definition closest_live (s : string) (m : matching) (os : list nat)
  (j : nat) (k : key) (p : nat) : Prop :=
  live s m os j p k /\ forall q, live s m os j q k -> q <= p.

(* The readings the rules allow.  A pair is a closer on the chain and the
   closest live opener of its key, with something between them for a
   delimiter.  A closer on the chain left unmatched has no live opener
   of its key but a delimiter right before it, with nothing to enclose:
   `__a` pairs nothing, and the second `_` opens in its turn.  A token
   acts as an opener when it may open, is on the chain and does not
   close. *)
Definition valid (s : string) (r : reading) : Prop :=
  let '(m, os) := r in
  (forall i j, In (i, j) m ->
     exists k, close_key s j = Some k /\ chain s m j
       /\ closest_live s m os j k i /\ (needs_content k = true -> tok_end s i < j))
  /\ (forall j k, close_key s j = Some k -> chain s m j -> ~ closes m j ->
        forall p, closest_live s m os j k p -> needs_content k = true /\ tok_end s p = j)
  /\ (forall q, In q os <->
        (exists k, open_key s q = Some k) /\ chain s m q /\ ~ closes m q).

(*
The tree
========

What a matching describes, read along its chain: each pair of
delimiters becomes its row's node around the tokens between, a bracket
pair with a region that ends becomes a link to the region's text, and
every other token is text.  Adjacent text is one `Str`, as the scanner
writes it.

An attribute spec waits, where it stands among the nodes of its pair,
until the pair closes, and then lands on what is before it (`attach`).
Text on either side of a waiting spec is not adjacent: a hard break
trims only the whitespace written right before its backslash. *)

Definition str_snoc (s : string) (out : inlines) : inlines :=
  match out with
  | Node p [] (Str t) :: rest => Node p [] (Str (t ++ s)) :: rest
  | _ => mk (Str s) :: out
  end.

(* An escaped byte as text: the byte if it is punctuation (O2), and the
   backslash and the byte otherwise (O3). *)
Definition esc_text (c : ascii) : string :=
  if is_punct c then one c else String bslash (one c).

(* A token as written. *)
Definition raw_text (raw : option string) : string :=
  match raw with
  | Some f => (String lbrace (String eqchar f) ++ one rbrace)%string
  | None => EmptyString
  end.

Definition tok_text (t : token) : string :=
  match t with
  | TText c => one c
  | TBreak => one nl_char
  | TDelim k false _ _ => dtoken k
  | TDelim k true true _ => (one lbrace ++ dtoken k)%string
  | TDelim k true false _ => (dtoken k ++ one rbrace)%string
  | TOpen im => bracket_open im
  | TClose _ _ => one rbrack
  | TEsc c => String bslash (one c)
  | TEscWs ws => String bslash ws
  | THard ws => String bslash ws
  | TVerb pre n body closed raw =>
      (chars dollar pre ++ ticks n ++ body ++ (if closed then ticks n else EmptyString)
       ++ raw_text raw)%string
  | TDollars k => chars dollar k
  | TAuto src => (String lt src ++ one gt)%string
  | TSymbol a => (String ":"%char a ++ one ":"%char)%string
  | TAttr b _ => (String lbrace b ++ one rbrace)%string
  | TSpan _ _ => one rbrack
  | TNote l => (String lbrack (String hat l) ++ one rbrack)%string
  | TDots n => chars period n
  | TDash n => chars hyphen n
  end.

(* A run escaped by a backslash is a non-breaking space and the rest of
   the run when it begins with a space (O5). *)
Definition nbsp_rest (ws : string) : option string :=
  match ws with
  | String c rest => if Ascii.eqb c " "%char then Some rest else None
  | EmptyString => None
  end.

(* A destination is written without its line breaks. *)
Fixpoint no_nl (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => if Ascii.eqb c nl_char then no_nl rest else String c (no_nl rest)
  end.

(* A destination's bytes with their escapes decoded. *)
Fixpoint dest_text (esc : bool) (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest =>
      if esc then (esc_text c ++ dest_text false rest)%string
      else if is_bslash c then dest_text true rest
      else String c (dest_text false rest)
  end.

(* The text of a region: a destination's with its escapes decoded. *)
Definition region_text (dest : bool) (txt : string) : string :=
  if dest then dest_text false txt else txt.

(* The link a bracket pair and its region make, an image when the
   bracket is an image's (I1): to the destination, or to the label, which
   an empty label takes from the link text (L6). *)
Definition region_node (dest image : bool) (kids : inlines) (txt : string) : inline :=
  bnode image kids
    (if dest then Direct (no_nl txt)
     else Reference (normalize_label
            (match txt with
             | EmptyString => reference_inlines_text kids
             | _ => txt
             end))).

Inductive tkind : Type := TKDelim (k : dstyle) | TKBracket (image : bool).

Definition tk_image (k : tkind) : bool :=
  match k with TKBracket im => im | TKDelim _ => false end.

(* What a pair holds while it is open: a node, or a spec waiting. *)
Inductive titem : Type := TIn (n : node inline) | TMark (a : attr).

(* Text after the content so far: it joins the text right before it. *)
Definition item_snoc (s : string) (out : list titem) : list titem :=
  match out with
  | TIn (Node p [] (Str t)) :: rest => TIn (Node p [] (Str (t ++ s))) :: rest
  | _ => TIn (mk (Str s)) :: out
  end.

(* "Spaces and tab characters before the backslash are ignored" (O4): a
   hard break trims the text right before it. *)
Definition item_trim (out : list titem) : list titem :=
  match out with
  | TIn (Node p [] (Str t)) :: rest =>
      match strip_trailing_ws t with
      | EmptyString => rest
      | t' => TIn (Node p [] (Str t')) :: rest
      end
  | _ => out
  end.

(* The last word of the nodes before a spec, latest first, and the nodes
   before it.  A word runs back over plain text and smart punctuation and
   ends after the last whitespace, so `a'b` is one word.  It is empty when
   the text before the spec ends in whitespace or there is none. *)
Fixpoint word_split (out : inlines) : inlines * inlines :=
  match out with
  | Node p [] (Str s) :: rest =>
      let '(pre, w) := last_ws_split s in
      if nonempty_str w
      then if nonempty_str pre
           then ([Node p [] (Str w)], Node p [] (Str pre) :: rest)
           else let '(ws, before) := word_split rest in
                (Node p [] (Str s) :: ws, before)
      else ([], out)
  | Node p [] (SmartPunctuation src t) :: rest =>
      let '(ws, before) := word_split rest in
      (Node p [] (SmartPunctuation src t) :: ws, before)
  | _ => ([], out)
  end.

(* A word that is one node takes the attributes itself; a longer one is
   put in a span that takes them. *)
Definition word_node (a : attr) (ws : inlines) : node inline :=
  match ws with
  | [Node p _ x] => Node p a x
  | _ => Node NoPos a (Span EmptyString (List.rev ws))
  end.

(* Where a spec lands, given the nodes before it, latest first.  "They
   must immediately follow the inline element to which they are attached
   (with no intervening whitespace)": after plain text that element is
   its last word, and an empty spec leaves the text whole; after any
   other node it is that node, whose attributes the spec is merged into;
   after whitespace, after a break, after a non-breaking space or with
   nothing before it the spec attaches to nothing. *)
Definition attach (a : attr) (out : inlines) : inlines :=
  match word_split out with
  | ((_ :: _) as ws, before) =>
      match a with
      | [] => out
      | _ => word_node a ws :: before
      end
  | ([], _) =>
      match out with
      | Node _ [] (Str _) :: _
      | Node _ _ (SoftBreak | HardBreak | NonBreakingSpace) :: _ | [] => out
      | Node p a' v :: rest => Node p (Attr.merge a a') v :: rest
      end
  end.

(* A node after the nodes before it, plain text merging. *)
Definition push (n : node inline) (out : inlines) : inlines :=
  match n with
  | Node _ [] (Str s) => str_snoc s out
  | _ => n :: out
  end.

(* What a pair holds once it closes: its nodes, each spec attached in
   its turn.  Latest first, as the content is. *)
Fixpoint resolve_rev (acc : list titem) : inlines :=
  match acc with
  | [] => []
  | TIn n :: rest => push n (resolve_rev rest)
  | TMark a :: rest => attach a (resolve_rev rest)
  end.

Definition resolve (acc : list titem) : inlines := List.rev (resolve_rev acc).

(* The frames of the open pairs, innermost first, each with its kind and
   its content reversed, above the reversed top level. *)
Definition tframes : Type := list (tkind * list titem).

Definition temit (n : node inline) (fs : tframes) (top : list titem)
  : tframes * list titem :=
  match fs with
  | [] => ([], TIn n :: top)
  | (k, acc) :: rest => ((k, TIn n :: acc) :: rest, top)
  end.

Definition temit_str (s : string) (fs : tframes) (top : list titem)
  : tframes * list titem :=
  match fs with
  | [] => ([], item_snoc s top)
  | (k, acc) :: rest => ((k, item_snoc s acc) :: rest, top)
  end.

Definition ttrim (fs : tframes) (top : list titem) : tframes * list titem :=
  match fs with
  | [] => ([], item_trim top)
  | (k, acc) :: rest => ((k, item_trim acc) :: rest, top)
  end.

(* A spec, waiting where it stands. *)
Definition tmark (a : attr) (fs : tframes) (top : list titem) : tframes * list titem :=
  match fs with
  | [] => ([], TMark a :: top)
  | (k, acc) :: rest => ((k, TMark a :: acc) :: rest, top)
  end.

Definition is_hard (t : token) : bool := match t with THard _ => true | _ => false end.

(* The node of a verbatim with `pre` dollars before it and its raw
   spec. *)
Definition verb_node (pre : nat) (raw : option string) (body : string) : inline :=
  match raw, pre with
  | Some f, _ => RawInline f (trim_verb body)
  | None, 0 => Verbatim (trim_verb body)
  | None, 1 => Math InlineMath (trim_verb body)
  | None, _ => Math DisplayMath (trim_verb body)
  end.

(* What a row's token reads as when it is text: its source, or for a
   quote the curly quote its row and its braces choose (`ddecay_str`,
   Q1, Q2): a double quote the left one, the right one before a `}`; a
   single quote the right one, an apostrophe, the left one after a `{`.
   `cm` says a `}` comes right after an opener marked with `{`. *)
Definition delim_lit (k : dstyle) (mr op cm : bool) : string :=
  if (mr && op)%bool then ddecay_str k true cm else ddecay_str k false mr.

(* A run of periods (Q4): an ellipsis for every three, left to right,
   and the one or two left over as text.  With smart typography off the
   run is text. *)
Definition dots_items (n : nat) : list inline :=
  if smart_typography
  then (repeat ellipsis_node (Nat.div n 3)
        ++ (if Nat.eqb (Nat.modulo n 3) 0 then []
            else [Str (chars period (Nat.modulo n 3))]))%list
  else [Str (chars period n)].

(* A run of hyphens (Q5): the em and en dashes `dash_counts` cuts it into,
   or text when `dash_run_smart` says it is not cut. *)
Definition dash_items (n : nat) : list inline :=
  if dash_run_smart n
  then let '(em, en, _) := dash_counts n in
       (repeat emdash_node em ++ repeat endash_node en)%list
  else [Str (chars hyphen n)].

(* Nodes after the nodes before them, text merging with text. *)
Definition temit_item (x : inline) (fs : tframes) (top : list titem)
  : tframes * list titem :=
  match x with
  | Str s => temit_str s fs top
  | _ => temit (mk x) fs top
  end.

Fixpoint temit_items (xs : list inline) (fs : tframes) (top : list titem)
  : tframes * list titem :=
  match xs with
  | [] => (fs, top)
  | x :: rest => let '(fs', top') := temit_item x fs top in temit_items rest fs' top'
  end.

(* One token of the chain; `hard` says the token before it was a hard
   break, which a break right after is part of.  A span is no image: the `!` of its bracket is text before it. *)
Definition tstep (s : string) (m : matching) (i : nat) (t : token) (hard : bool)
  (fs : tframes) (top : list titem) : tframes * list titem :=
  match t with
  | TText _ => temit_str (tok_text t) fs top
  | TEsc c => temit_str (esc_text c) fs top
  | TEscWs ws =>
      match nbsp_rest ws with
      | Some rest =>
          let '(fs', top') := temit (mk NonBreakingSpace) fs top in
          if nonempty_str rest then temit_str rest fs' top' else (fs', top')
      | None => temit_str (tok_text t) fs top
      end
  | THard _ => let '(fs', top') := ttrim fs top in temit (mk HardBreak) fs' top'
  | TVerb pre _ body _ raw =>
      let '(fs', top') := if Nat.ltb 2 pre then temit_str (chars dollar (pre - 2)) fs top
                          else (fs, top) in
      temit (mk (verb_node pre raw body)) fs' top'
  | TDollars _ => temit_str (tok_text t) fs top
  | TAuto src => temit (mk (auto_node src)) fs top
  | TSymbol a => temit (mk (Symbol a)) fs top
  | TAttr _ a => tmark a fs top
  | TNote l => temit (mk (FootnoteReference (normalize_label l))) fs top
  | TDots n => temit_items (dots_items n) fs top
  | TDash n => temit_items (dash_items n) fs top
  | TBreak => if hard then (fs, top) else temit (mk SoftBreak) fs top
  | TDelim k mr op _ =>
      if is_opener m i then ((TKDelim k, []) :: fs, top)
      else match is_closer m i, fs with
           | true, (TKDelim k', acc) :: fs0 => temit (mk (dnode k' (resolve acc))) fs0 top
           | _, _ =>
               temit_item (decay_node k (delim_lit k mr op (at_rbrace (get (tok_end s i) s))))
                 fs top
           end
  | TOpen im =>
      if is_opener m i then ((TKBracket im, []) :: fs, top)
      else temit_str (tok_text t) fs top
  | TClose b r =>
      match is_closer m i, fs with
      | true, (k, acc) :: fs0 =>
          temit (mk (region_node b (tk_image k) (resolve acc) (region_text b r))) fs0 top
      | _, _ => temit_str (tok_text t) fs top
      end
  | TSpan _ a =>
      match is_closer m i, fs with
      | true, (k, acc) :: fs0 =>
          let '(fs1, top1) := if tk_image k then temit_str (one bang) fs0 top
                              else (fs0, top) in
          temit (Node NoPos a (Span EmptyString (resolve acc))) fs1 top1
      | _, _ => temit_str (tok_text t) fs top
      end
  end.

Fixpoint tgo (s : string) (m : matching) (fuel i : nat) (hard : bool)
  (fs : tframes) (top : list titem) : tframes * list titem :=
  match fuel with
  | O => (fs, top)
  | S f =>
      match tok_of s i with
      | None => (fs, top)
      | Some t =>
          let '(fs', top') := tstep s m i t hard fs top in
          match chain_next s m i with
          | Some q => tgo s m f q (is_hard t) fs' top'
          | None => (fs', top')
          end
      end
  end.

(* A valid matching closes every pair it opens, so no frame is left at
   the end. *)
Definition tree_of (s : string) (m : matching) : inlines :=
  resolve (snd (tgo s m (S (String.length s)) 0 false [] [])).

(*
The reading, computed
=====================

Not part of the specification: `valid` determines the reading
(`valid_unique`), and `ref_read` is a way to compute it
(`ref_read_valid`).

Along the chain, with the openers still open innermost first.  A closer
takes the closest open opener of its key. *)

Definition litem : Type := (nat * key)%type.

Definition ldesc (lv : list litem) : Prop :=
  StronglySorted (fun a b => fst b < fst a) lv.

Inductive pick_res : Type := PFound (p : nat) (below : list litem) | PNone.

Fixpoint pick (k : key) (lv : list litem) : pick_res :=
  match lv with
  | [] => PNone
  | (p, k') :: rest => if key_eq k k' then PFound p rest else pick k rest
  end.

Record rstate : Type := RState {
  rs_live : list litem;
  rs_pairs : matching;
  rs_os : list nat
}.

Definition ropen (i : nat) (k : key) (op : bool) (st : rstate) : rstate :=
  if op then RState ((i, k) :: rs_live st) (rs_pairs st) (i :: rs_os st) else st.

Definition rstep (s : string) (i : nat) (t : token) (st : rstate) : rstate :=
  match t with
  | TText _ | TBreak | TEsc _ | TEscWs _ | THard _ | TVerb _ _ _ _ _ | TDollars _ | TAuto _
  | TSymbol _ | TAttr _ _ | TNote _ | TDots _ | TDash _ => st
  | TOpen _ => ropen i KBracket true st
  | TDelim k mr op cl =>
      match (if cl then pick (KDelim k mr) (rs_live st) else PNone) with
      | PFound p below =>
          if Nat.ltb (tok_end s p) i
          then RState below ((p, i) :: rs_pairs st) (rs_os st)
          else ropen i (KDelim k mr) op st
      | PNone => ropen i (KDelim k mr) op st
      end
  | TClose _ _ | TSpan _ _ =>
      match pick KBracket (rs_live st) with
      | PFound p below => RState below ((p, i) :: rs_pairs st) (rs_os st)
      | PNone => st
      end
  end.

Fixpoint rgo (s : string) (fuel p : nat) (st : rstate) : rstate :=
  match fuel with
  | O => st
  | S f =>
      match tok_of s p with
      | None => st
      | Some t =>
          let st' := rstep s p t st in
          match chain_next s (rs_pairs st') p with
          | Some q => rgo s f q st'
          | None => st'
          end
      end
  end.

Definition rstart : rstate := RState [] [] [].

Definition ref_read (s : string) : reading :=
  let st := rgo s (S (String.length s)) 0 rstart in (rs_pairs st, rs_os st).

End WithTable.
