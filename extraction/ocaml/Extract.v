(* ai-disclosure: autonomous *)

(* Extraction prelude.  `Separate Extraction` emits one OCaml module per
   Coq module rather than one flat file, so the extracted parser can be
   read against the theory it came from.  The blacklist keeps `String`,
   `List`, `Nat` and `Bool` from shadowing OCaml's own; they land as
   `String0`, `List0`, `Nat0`, `Bool0`.

   `ExtrOcamlNativeString` maps Gallina strings to native OCaml strings,
   so no conversion glue is needed on the OCaml side. *)

From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNativeString.
From Stdlib Require OrdersEx.
From DjotV Require Import Strings Html Step Document Profile ProfileChecks Reparse
  Readable.
From DjotVDev Require Import Fixtures Generate.

Extraction Language OCaml.
Extraction Blacklist String List Nat Bool.
Set Extraction Output Directory ".".

(* Under the native string mapping, a match on [String c s'] copies the
   tail and [String c acc] copies the accumulator, so a recursion over a
   string is quadratic in its length.  Gallina's [List.rev] also extracts
   through append, and [String.length] recursively takes every copied tail.
   These are replaced by native OCaml equal to the Gallina definitions; they
   are trusted, not proved. *)
Extract Constant List.rev => "List.rev".
Extract Inlined Constant String.length => "String.length".

(* [nat] is OCaml's [int], and the [nat] operations the parser uses are
   OCaml's arithmetic.  Unary [nat] made every numeral cost memory
   linear in its value (a nine-digit list start overflowed the stack) and
   every character class test cost a walk up to 255 cells.

   [int] wraps at [max_int], [nat] does not.  The parser's numbers are
   lengths, positions and counts, bounded by the input's size, plus the
   numerals it reads; `Marker.dec_start_bound` bounds the one numeral
   that could grow with the input, a decimal list start.

   [Init.Nat] and [PeanoNat.Nat] each extract their own copy of these
   operations, so both are mapped.  [Nat.sub] truncates at zero, and
   [Nat.div] and [Nat.modulo] by zero return zero and [n]. *)
Extract Inductive nat => int [ "0" "Stdlib.succ" ]
  "(fun fO fS n -> if n = 0 then fO () else fS (n - 1))".

Extract Inlined Constant Init.Nat.add => "( + )".
Extract Inlined Constant Init.Nat.mul => "( * )".
Extract Constant Init.Nat.sub => "fun n m -> Stdlib.max 0 (n - m)".
Extract Constant Init.Nat.pred => "fun n -> Stdlib.max 0 (n - 1)".
Extract Inlined Constant Init.Nat.eqb => "( = )".
Extract Inlined Constant Init.Nat.leb => "( <= )".
Extract Inlined Constant Init.Nat.ltb => "( < )".
Extract Constant Init.Nat.div => "fun n m -> if m = 0 then 0 else n / m".
Extract Constant Init.Nat.modulo => "fun n m -> if m = 0 then n else n mod m".

Extract Inlined Constant PeanoNat.Nat.add => "( + )".
Extract Inlined Constant PeanoNat.Nat.mul => "( * )".
Extract Constant PeanoNat.Nat.sub => "fun n m -> Stdlib.max 0 (n - m)".
Extract Constant PeanoNat.Nat.pred => "fun n -> Stdlib.max 0 (n - 1)".
Extract Inlined Constant PeanoNat.Nat.eqb => "( = )".
Extract Inlined Constant PeanoNat.Nat.leb => "( <= )".
Extract Inlined Constant PeanoNat.Nat.ltb => "( < )".
Extract Constant PeanoNat.Nat.div => "fun n m -> if m = 0 then 0 else n / m".
Extract Constant PeanoNat.Nat.modulo =>
  "fun n m -> if m = 0 then n else n mod m".

(* [ascii_of_nat] keeps the low eight bits, as the Gallina one does. *)
Extract Inlined Constant Ascii.nat_of_ascii => "Char.code".
Extract Constant Ascii.ascii_of_nat => "fun n -> Char.chr (n land 255)".
Extract Constant DjotV.Strings.nat_str => "Stdlib.string_of_int".
(* The HTML escapers are per-character recursions with a tail copy and an
   append per character, quadratic in the length of a text node.
   ([String.concat], which `Html.serialize_flat` joins the document with,
   is already OCaml's under `ExtrOcamlNativeString`.) *)
Extract Constant DjotV.Html.escape =>
  "(fun s ->
     let b = Buffer.create (String.length s) in
     String.iter (function
       | '&' -> Buffer.add_string b ""&amp;""
       | '<' -> Buffer.add_string b ""&lt;""
       | '>' -> Buffer.add_string b ""&gt;""
       | c -> Buffer.add_char b c) s;
     Buffer.contents b)".
Extract Constant DjotV.Html.escape_attr =>
  "(fun s ->
     let b = Buffer.create (String.length s) in
     String.iter (function
       | '&' -> Buffer.add_string b ""&amp;""
       | '<' -> Buffer.add_string b ""&lt;""
       | '>' -> Buffer.add_string b ""&gt;""
       | '""' -> Buffer.add_string b ""&quot;""
       | c -> Buffer.add_char b c) s;
     Buffer.contents b)".
(* String order, for the identifier pass's balanced trees
   (`Document.StrSet`, `Document.StrMap`).  Both Gallina orders are
   lexicographic by character code with a proper prefix first, which is
   OCaml's [String.compare]. *)
Extract Constant String.compare =>
  "(fun a b -> let c = Stdlib.String.compare a b in
     if c = 0 then Datatypes.Eq else if c < 0 then Datatypes.Lt
     else Datatypes.Gt)".
Extract Constant OrdersEx.String_as_OT.compare =>
  "(fun a b -> let c = Stdlib.String.compare a b in
     if c = 0 then Datatypes.Eq else if c < 0 then Datatypes.Lt
     else Datatypes.Gt)".
Extract Constant DjotV.Strings.rev_string =>
  "(fun s -> let n = String.length s in
     String.init n (fun i -> String.get s (n - 1 - i)))".
(* Reversed byte lists are used by label words and attribute tokens. *)
Extract Constant DjotV.Ast.rev_chars =>
  "(fun cs ->
     let n = List.length cs in
     let b = Bytes.create n and i = ref n in
     List.iter (fun c -> decr i; Bytes.set b !i c) cs;
     Bytes.to_string b)".
(* The Gallina tokenizer has a reversed byte accumulator, but destructing
   the input string still copies every native suffix. *)
Extract Constant DjotV.Ast.words =>
  "(fun sep s ->
     let acc = ref [] and word = Buffer.create 32 in
     let flush () =
       if Buffer.length word <> 0 then begin
         acc := Buffer.contents word :: !acc; Buffer.clear word
       end in
     String.iter (fun c -> if sep c then flush () else Buffer.add_char word c) s;
     flush (); List.rev !acc)".
Extract Constant DjotV.Strings.split_lines =>
  "(fun s -> match List.rev (String.split_on_char '\n' s) with
     | """" :: rest -> List.rev rest
     | parts -> List.rev parts)".

(* Destination newlines are removed once the candidate closes.  The
   Gallina structural scan remains the specification; matching native
   strings by [String c rest] would copy every suffix. *)
Extract Constant DjotV.InlineScan.drop_nl =>
  "(fun s ->
     let b = Buffer.create (String.length s) in
     String.iter (fun c -> if c <> '\n' then Buffer.add_char b c) s;
     Buffer.contents b)".

(* Line scans.  Every line goes through `classify`, and a container
   classifies what follows its prefix again.  Matching a native string by
   [String c rest] copies the rest of the line, even when the scan stops
   at the first byte, and a scan through a run recurses once per byte.
   These read by offset, stop at the same byte, and copy only what they
   return.  Extraction may place a realization before the predicates it
   would call, so `is_ws` and its relatives are spelled out. *)
Extract Constant DjotV.Strings.is_blank =>
  "(fun s -> String.for_all (fun c -> c = ' ' || c = '\t' || c = '\r') s)".
Extract Constant DjotV.Strings.indent_of =>
  "(fun s ->
     let ws c = c = ' ' || c = '\t' || c = '\r' in
     let n = String.length s in
     let rec go i = if i < n && ws s.[i] then go (i + 1) else i in
     go 0)".
Extract Constant DjotV.Strings.drop_leading_ws =>
  "(fun s ->
     let ws c = c = ' ' || c = '\t' || c = '\r' in
     let n = String.length s in
     let rec go i = if i < n && ws s.[i] then go (i + 1) else i in
     let i = go 0 in if i = 0 then s else String.sub s i (n - i))".
(* Specified by reversing twice; this scans back from the end. *)
Extract Constant DjotV.Strings.strip_trailing_ws =>
  "(fun s ->
     let ws c = c = ' ' || c = '\t' || c = '\r' in
     let n = String.length s in
     let rec go i = if i > 0 && ws s.[i - 1] then go (i - 1) else i in
     let i = go n in if i = n then s else String.sub s 0 i)".
Extract Constant DjotV.Strings.drop_ws_upto =>
  "(fun k s ->
     let ws c = c = ' ' || c = '\t' || c = '\r' in
     let n = Stdlib.min k (String.length s) in
     let rec go i = if i < n && ws s.[i] then go (i + 1) else i in
     let i = go 0 in
     if i = 0 then s else String.sub s i (String.length s - i))".
Extract Constant DjotV.Strings.no_nl =>
  "(fun s -> not (String.contains s '\n'))".
Extract Constant DjotV.Strings.no_char =>
  "(fun c s -> not (String.contains s c))".
Extract Constant DjotV.Strings.no_ws =>
  "(fun s -> not (String.exists (fun c ->
     c = ' ' || c = '\t' || c = '\r' || c = '\n') s))".
Extract Constant DjotV.Line.thematic_count =>
  "(fun s count ->
     let n = String.length s in
     let rec go i k =
       if i >= n then 3 <= k
       else if s.[i] = '-' || s.[i] = '*' then go (i + 1) (k + 1)
       else if s.[i] = ' ' || s.[i] = '\t' || s.[i] = '\r' then go (i + 1) k
       else false in
     go 0 count)".
Extract Constant DjotV.Line.all_char =>
  "(fun c s -> String.for_all (fun a -> a = c) s)".
Extract Constant DjotV.Line.str_forallb =>
  "(fun p s -> String.for_all p s)".
Extract Constant DjotV.Line.all_info_chars =>
  "(fun s -> String.for_all (fun c ->
     not (c = ' ' || c = '\t' || c = '\r' || c = '`' || c = '\n')) s)".
Extract Constant DjotV.Line.take_while =>
  "(fun p s ->
     let n = String.length s in
     let rec go i = if i < n && p s.[i] then go (i + 1) else i in
     let i = go 0 in
     if i = 0 then ("""", s)
     else (String.sub s 0 i, String.sub s i (n - i)))".
Extract Constant DjotV.Line.count_run =>
  "(fun c s ->
     let n = String.length s in
     let rec go i = if i < n && s.[i] = c then go (i + 1) else i in
     let i = go 0 in
     if i = 0 then (0, s) else (i, String.sub s i (n - i)))".

(* Table rows.  The Gallina cell scan grows each cell by consing onto a
   reversed accumulator, and the separator scan re-reads the rest of the
   line per cell.  Here a cell is the slice from just after its bar, and
   `cur`, `row_cell_entry`, `cell_trim`, and `sep_align` are spelled
   out. *)
Extract Constant DjotV.Line.cell_trim_r =>
  "(fun s ->
     let n = String.length s in
     let rec go i last =
       if i >= n then last
       else if s.[i] = '\\' then
         (if i + 1 < n then go (i + 2) (i + 2) else i + 1)
       else if s.[i] = ' ' || s.[i] = '\t' || s.[i] = '\r' then go (i + 1) last
       else go (i + 1) (i + 1) in
     let last = go 0 0 in
     if last = n then s else String.sub s 0 last)".
Extract Constant DjotV.Line.row_cells_trace =>
  "(fun s vb run bs cur acc pos start ->
     let n = String.length s in
     let ws c = c = ' ' || c = '\t' || c = '\r' in
     let vb_step vb run =
       if run = 0 then vb else if vb = 0 then run
       else if vb = run then 0 else vb in
     let rev s =
       let k = String.length s in String.init k (fun i -> s.[k - 1 - i]) in
     let trim_r s =
       let k = String.length s in
       let rec go i last =
         if i >= k then last
         else if s.[i] = '\\' then (if i + 1 < k then go (i + 2) (i + 2) else i + 1)
         else if ws s.[i] then go (i + 1) last
         else go (i + 1) (i + 1) in
       String.sub s 0 (go 0 0) in
     (* the cell's source: the reversed [pre] it started with, then
        [s] from [from] up to [i] *)
     let entry pre from i start stop =
       let raw = rev pre ^ String.sub s from (i - from) in
       let k = String.length raw in
       let rec lead j = if j < k && ws raw.[j] then lead (j + 1) else j in
       let d = lead 0 in
       (((trim_r (String.sub raw d (k - d)), start), stop), start + 1 + d) in
     let rec go i vb run bs pre from acc pos start =
       if i >= n then
         (if bs then None
          else if vb_step vb run = 0 then
            Some (List.rev (entry pre from i start (pos + 1) :: acc))
          else None)
       else
         let c = s.[i] in
         if c = '`' then go (i + 1) vb (run + 1) false pre from acc (pos + 1) start
         else
           let vb' = vb_step vb run in
           if vb' = 0 && c = '\\' then
             (if i + 1 >= n then None
              else go (i + 2) 0 0 (s.[i + 1] = '\\') pre from acc (pos + 2) start)
           else if c = '|' && vb' = 0 && not bs then
             go (i + 1) 0 0 false """" (i + 1)
               (entry pre from i start (pos + 1) :: acc) (pos + 1) pos
           else go (i + 1) vb' 0 (c = '\\') pre from acc (pos + 1) start in
     go 0 vb run bs cur 0 acc pos start)".
Extract Constant DjotV.Line.sep_cells_fuel =>
  "(fun fuel s ->
     let n = String.length s in
     let rec skip_ws i =
       if i < n && (s.[i] = ' ' || s.[i] = '\t' || s.[i] = '\r')
       then skip_ws (i + 1) else i in
     let rec dashes i = if i < n && s.[i] = '-' then dashes (i + 1) else i in
     let rec go fuel i acc =
       if fuel = 0 then None
       else if i >= n then Some (List.rev acc)
       else
         let left = s.[i] = ':' in
         let i = if left then i + 1 else i in
         let j = dashes i in
         if j = i then None
         else
           let right = j < n && s.[j] = ':' in
           let j = skip_ws (if right then j + 1 else j) in
           if j < n && s.[j] = '|' then
             let a = match left, right with
               | true, true -> AlignCenter | true, false -> AlignLeft
               | false, true -> AlignRight | false, false -> AlignDefault in
             go (fuel - 1) (skip_ws (j + 1)) (a :: acc)
           else None in
     go fuel 0 [])".

(* A roman marker's value, read from its reversed numeral. *)
Extract Constant DjotV.Marker.Roman.acc =>
  "(fun s prev total ->
     let digit = function
       | 'i' | 'I' -> 1 | 'v' | 'V' -> 5 | 'x' | 'X' -> 10 | 'l' | 'L' -> 50
       | 'c' | 'C' -> 100 | 'd' | 'D' -> 500 | 'm' | 'M' -> 1000 | _ -> 0 in
     let n = String.length s in
     let rec go i prev total =
       if i >= n then total
       else
         let d = digit s.[i] in
         go (i + 1) d (if d < prev then Stdlib.max 0 (total - d) else total + d) in
     go 0 prev total)".

(* Block attribute lines, fed to the machine one byte at a time, and the
   value normalization run on each committed quoted value. *)
Extract Constant DjotV.Attributes.afeed =>
  "(fun s p ->
     let n = String.length s in
     let rec go i p =
       if i >= n then (p, """")
       else match p.ap_st with
         | ADone | AFail -> (p, if i = 0 then s else String.sub s i (n - i))
         | _ -> go (i + 1) (astep p s.[i]) in
     go 0 p)".
Extract Constant DjotV.Attributes.blank_to_eol =>
  "(fun s -> String.for_all (fun c ->
     c = ' ' || c = '\t' || c = '\r' || c = '\n' || c = '\012' || c = '\011') s)".
Extract Constant DjotV.Attributes.collapse_from =>
  "(fun skip s ->
     let b = Buffer.create (String.length s) in
     let skip = ref skip in
     String.iter (fun c ->
       if c = ' ' || c = '\r' || c = '\n' then
         (if not !skip then Buffer.add_char b ' '; skip := true)
       else (Buffer.add_char b c; skip := false)) s;
     Buffer.contents b)".
Extract Constant DjotV.Attributes.unescape =>
  "(fun s ->
     let n = String.length s in
     let b = Buffer.create n in
     let escapable = function
       | '.' | ',' | '\\' | '/' | '#' | '!' | '$' | '%' | '^' | '&' | '*'
       | ';' | ':' | '{' | '}' | '=' | '-' | '_' | '`' | '~' | '+' | '['
       | ']' | '(' | ')' | '\'' | '""' | '?' | '|' -> true
       | _ -> false in
     let rec go i =
       if i < n then
         if s.[i] = '\\' && i + 1 < n && escapable s.[i + 1]
         then (Buffer.add_char b s.[i + 1]; go (i + 2))
         else (Buffer.add_char b s.[i]; go (i + 1)) in
     go 0; Buffer.contents b)".

(* A line opening with `[` is tried as a reference or footnote definition.
   The label scan stops at the first `]`. *)
Extract Constant DjotV.Line.ref_label =>
  "(fun s -> match String.index_opt s ']' with
     | None -> None
     | Some i ->
       Some (String.sub s 0 i, String.sub s (i + 1) (String.length s - i - 1)))".

(* These two close-time readers retain their recursive Gallina definitions
   for the proofs.  Native string destruction copies each suffix, so the
   extracted readers use offsets and copy only their final result. *)
Extract Constant DjotV.InlineScan.source_shape =>
  "(fun s ->
     let lines = ref 0 and first = ref 0 in
     String.iter (fun c ->
       if c = '\n' then incr lines
       else if !lines = 0 then incr first) s;
     ((!lines, !first), String.length s))".
Extract Constant DjotV.InlineScan.wiki_split =>
  "(fun s ->
     let n = String.length s in
     let rec find i =
       if i >= n then (s, None)
       else if s.[i] = '\\' then find (i + 2)
       else if s.[i] = '|' then
         (String.sub s 0 i, Some (String.sub s (i + 1) (n - i - 1)))
       else find (i + 1)
     in find 0)".

(* An autolink tests its completed body at '>'.  These structural Gallina
   scans copy native suffixes; the offset versions preserve the byte
   predicates and stop at the same first witness. *)
Extract Constant DjotV.InlineView.auto_email =>
  "(fun s ->
     let rec scan i =
       i < String.length s &&
       ((i > 0 && s.[i] = '@' && s.[i-1] <> ':') || scan (i + 1))
     in scan 0)".
Extract Constant DjotV.InlineView.auto_kind_ok =>
  "(fun s ->
     let alpha c =
       (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') in
     let rec scheme i =
       i + 1 < String.length s &&
       ((alpha s.[i] && s.[i+1] = ':') || scheme (i + 1)) in
     auto_email s || scheme 0)".
Extract Constant DjotV.InlineView.auto_body_ok =>
  "(fun s ->
     s <> """" && String.for_all (fun c ->
       c <> ' ' && c <> '\t' && c <> '\r' && c <> '\n' &&
       c <> '<' && c <> '>') s)".
(* Escaped whitespace asks for the last byte of its completed run. *)
Extract Constant DjotV.InlineView.str_last =>
  "(fun s prev ->
     let n = String.length s in if n = 0 then prev else Some s.[n - 1])".

(* The scanner asks which row a byte belongs to for every byte it reads.
   The table's rows are functions, so the Gallina lookup makes up to
   eighteen indirect calls per byte.  This builds the answer for all 256
   bytes once per table, by the same first-match search in the same row
   order (`dstyles`), and keeps the last table's array.  A caller builds
   its table once and the parser never builds one, so the cached table
   is hit for the whole parse; the cache holds an immutable pair, so a
   reader on another domain sees either pair whole. *)
Extract Constant DjotV.InlineTable.dstyle_at_fast =>
  "(let rows = [DEmph; DStrong; DSuper; DSub; DMark; DInsert; DDelete;
               DSQuote; DDQuote] in
    let build c =
      Array.init 256 (fun i ->
        let ch = Char.chr i in
        List.find_opt (fun k ->
          (match c.dc_syntax k with DOff -> false | _ -> true)
          && c.dc_char k = ch) rows) in
    let last = Atomic.make None in
    fun c ch ->
      let tbl = match Atomic.get last with
        | Some (c', tbl) when c' == c -> tbl
        | _ -> let tbl = build c in Atomic.set last (Some (c, tbl)); tbl in
      Array.unsafe_get tbl (Char.code ch))".

(* The Gallina inline drivers recurse through [String c rest].  With native
   OCaml strings that copies the whole remaining line at every byte.  These
   loops read by offset, and run the scanner on the [chunks] buffer, whose
   appends do not copy the pending text: the state is lifted into it at the
   start of the line and read back with [map_text] at the end
   ([InlineBuffer.iscan_str_buf_spec] and its siblings).  In [IText false]
   a run of letters, digits, and spaces that the active delimiter table
   assigns no style is pushed as one chunk; the located loop also
   preserves the last whitespace position.  All other bytes take the
   step.  These realizations are trusted and checked against the previous
   extraction. *)
Extract Constant DjotV.InlineScan.iscan_str =>
  "(fun t s st ->
     let plain c =
       ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
        || (c >= '0' && c <= '9') || c = ' ')
       && dstyle_of t c = None in
     let i = ref 0 and state = ref (lift chunks_text st)
     and n = String.length s in
     while !i < n do
       match !state with
       | IText (false, txt, _, o) when plain s.[!i] ->
           let j = ref !i in
           while !j < n && plain s.[!j] do incr j done;
           state := IText (false, chunks_push txt (String.sub s !i (!j - !i)),
                           Some s.[!j - 1], o);
           i := !j
       | _ ->
           state := istep t chunks_text semantic_pos semantic_inline_cursor s.[!i] !state;
           incr i
     done;
     map_text chunks_text !state)".
Extract Constant DjotV.InlineScan.iscan_str_off =>
  "(fun t s st ->
     let plain c =
       ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
        || (c >= '0' && c <= '9') || c = ' ')
       && dstyle_of t c = None in
     let i = ref 0 and state = ref (lift chunks_text st)
     and n = String.length s in
     while !i < n do
       match !state with
       | IText (false, txt, _, o) when plain s.[!i] ->
           let j = ref !i in
           while !j < n && plain s.[!j] do incr j done;
           state := IText (false, chunks_push txt (String.sub s !i (!j - !i)),
                           Some s.[!j - 1], o);
           i := !j
       | _ ->
           state := istep_at t chunks_text semantic_pos semantic_inline_cursor false s.[!i] !state;
           incr i
     done;
     map_text chunks_text !state)".
Extract Constant DjotV.InlineLocated.iscan_str_located =>
  "(fun t h allow k origin rem s st ->
     let plain c =
       ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')
        || (c >= '0' && c <= '9') || c = ' ')
       && dstyle_of t c = None in
     let cursor r = {
       cursor_start = { spot_line = k; spot_rem = r };
       cursor_stop = { spot_line = k; spot_rem = Stdlib.max 0 (r - 1) };
       cursor_origin = origin } in
     let i = ref 0 and pos = ref rem and state = ref (lift chunks_text st)
     and n = String.length s in
     while !i < n do
       match !state with
       | IText (false, txt, _, o) when plain s.[!i] ->
           let j = ref !i and p = ref !pos and scope = ref o in
           while !j < n && plain s.[!j] do
             let c = s.[!j] in
             if is_ws c then scope := remember_word_start h (cursor !p) c !scope;
             p := Stdlib.max 0 (!p - 1);
             incr j
           done;
           state := IText (false, chunks_push txt (String.sub s !i (!j - !i)),
                           Some s.[!j - 1], !scope);
           i := !j;
           pos := !p
       | _ ->
           state := istep_at t chunks_text h (cursor !pos) allow s.[!i] !state;
           pos := Stdlib.max 0 (!pos - 1);
           incr i
     done;
     map_text chunks_text !state)".

Separate Extraction convert generated lazy_generated accepted rt_lhs rt_rhs render_cb DjotV.Render.render_doc
  DjotV.Document.unsection
  DjotV.Readable.readable_djot DjotV.Readable.readable_doc
  DjotV.Readable.readable_inline_lines
  keyed_accepted keyed_rt_lhs wiki_accepted wiki_rt_lhs
  callout_accepted callout_rt_lhs dollar_accepted dollar_rt_lhs
  tags_accepted tags_rt_lhs
  parse_blocks_located parse_doc_located
  DjotV.Reparse.sem_step DjotV.Reparse.loc_step DjotV.Reparse.pieces
  DjotV.Reparse.pieces_tree DjotV.Reparse.splice DjotV.Reparse.assemble
  line_table resolve_span DjotV.InlineLocated.cursor_in
  DjotV.InlineScan.chunks_text DjotV.InlineScan.map_text DjotV.InlineScan.lift
  DjotV.Profile.djot_options DjotV.Profile.markdown_like_options
  DjotV.Profile.bconfig_of DjotV.ProfileChecks.wrap_safe
  DjotV.ProfileChecks.heading_wrap_safe DjotV.ProfileChecks.quote_uniform
  DjotV.ProfileChecks.lazy_uniform DjotV.ProfileChecks.shape_first
  DjotV.InlineTable.with_inline_footnotes DjotV.InlineTable.with_inline_tags
  DjotV.InlineTable.with_wikilinks DjotV.InlineTable.with_dollar_math
  DjotV.InlineTable.update_drow DjotV.InlineTable.drow_update_compatible
  DjotV.InlineTable.with_smart_typography DjotV.InlineTable.with_raw_inline
  DjotV.InlineTable.with_math DjotV.InlineTable.with_inline_attrs
  DjotV.Step.with_tables DjotV.Step.with_heading_continuation
  DjotV.Step.with_divs DjotV.Step.with_tasks DjotV.Step.with_raw_blocks
  DjotV.Step.with_deflists DjotV.Step.with_block_attrs
  DjotV.Attributes.attr_ok DjotV.Ast.Attr.remove DjotV.Ast.Attr.set_classes.
