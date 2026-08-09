(* ai-disclosure: ai-generated *)

(* Djot rendering (AST -> djot source), modeled on djoths's Djot.hs,
   together with the canonical form it inverts.

   `cblock` is the canonical (renderable) view of a block: the parser's
   image, described by the data that determines it.  Renderability of a
   paragraph is phrased through the line classifier: the first line must
   *classify* as text (so the parse re-opens a paragraph there), interior
   lines merely nonblank (paragraphs cannot be interrupted), the last
   line pre-stripped (the parser strips it, so a roundtripping AST cannot
   carry trailing whitespace).  Each new construct added to Line.v gets a
   cblock constructor, a canonical rendering, and a cb_ok obligation —
   that is the whole roundtrip extension recipe. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Strings Line Ast Parser.
Import ListNotations.

Local Open Scope string_scope.

(*
Block layout
============
*)

(* The renderer's canonical spellings, fixed once so both the rendering
   and the classification lemmas can refer to them. *)
Definition thematic_line : string := "* * * *".
Definition code_close : string := "```".
Definition code_open (info : string) : string := "```" ++ info.
Definition quote_open : string := "> ".
Definition quote_line (l : string) : string := quote_open ++ l.

(* Flatten per-block line lists into one line list, with a single blank
   line between blocks (and none at either end).  This is the layout
   both a document and a block quote's contents use — which is
   uniformity, on the rendering side. *)
Fixpoint sep_lines (lss : list (list string)) : list string :=
  match lss with
  | [] => []
  | [ls] => ls
  | ls :: rest => (ls ++ EmptyString :: sep_lines rest)%list
  end.

Lemma quote_line_empty : quote_line EmptyString = quote_open.
Proof. unfold quote_line. apply append_empty_r. Qed.

(*
Canonical blocks
================
*)

(* A block described by the source data that determines it — a paragraph
   by its lines, a code block by its info string and content lines, a
   quote by the canonical blocks inside it.  One constructor per block
   construct the roundtrip covers.

   The list-valued constructor makes `cblock` a nested inductive, so the
   three projections below use hand-inlined fixpoints (Rocq rejects the
   mutual-recursion spelling) and each gets a `_quote` lemma recovering
   the `map`/`forallb` form the proofs actually use. *)
Inductive cblock : Type :=
  | CPara (ls : list string)
  | CThematic
  | CCode (info : string) (content : list string)
  | CHeading (level : nat) (ls : list string)
  | CQuote (inner : list cblock)
  | CList (sp : list_spacing) (items : list (list cblock)).

(* The two projections a cblock sits between: its source lines... *)
Fixpoint cb_lines (cb : cblock) : list string :=
  let quoted :=
    fix go (cs : list cblock) : list string :=
      match cs with
      | [] => []
      | [c] => map quote_line (cb_lines c)
      | c :: rest => (map quote_line (cb_lines c) ++ quote_open :: go rest)%list
      end in
  let bulleted :=
    fix golist (sp : list_spacing) (iss : list (list cblock)) : list string :=
      match iss with
      | [] => []
      | [it] => indent_lines bullet_open bullet_cont (sep_lines (map cb_lines it))
      | it :: rest =>
          (indent_lines bullet_open bullet_cont (sep_lines (map cb_lines it))
           ++ (match sp with Loose => [EmptyString] | Tight => [] end)
           ++ golist sp rest)%list
      end in
  match cb with
  | CPara ls => ls
  | CThematic => [thematic_line]
  | CCode info content => (code_open info :: content ++ [code_close])%list
  | CHeading lvl ls => map (heading_line lvl) ls
  | CQuote inner => quoted inner
  | CList sp items => bulleted sp items
  end.

(* ...and the AST node the parser builds from those lines.  Roundtrip is
   then: cb_lines, rendered and reparsed, gives back cb_ast. *)
Fixpoint cb_ast (cb : cblock) : node block :=
  let asts :=
    fix go (cs : list cblock) : blocks :=
      match cs with [] => [] | c :: rest => cb_ast c :: go rest end in
  let itemsof :=
    fix goitems (iss : list (list cblock)) : list blocks :=
      match iss with [] => [] | it :: rest => asts it :: goitems rest end in
  match cb with
  | CPara ls => mk (Para (para_inlines ls))
  | CThematic => mk ThematicBreak
  | CCode info content => fence_block (Fence "`"%char 3 info) content
  | CHeading lvl ls => mk (Heading lvl (para_inlines ls))
  | CQuote inner => mk (BlockQuote (asts inner))
  | CList sp items => mk (BulletList sp (itemsof items))
  end.

(* The hand-inlined `asts` above is definitionally `map cb_ast`, one
   fixpoint-unfolding step at a time; spelled out once so the list-of-
   lists lemmas below don't have to re-derive it. *)
Lemma cb_asts_eq :
  forall cs,
    (fix go (cs : list cblock) : blocks :=
       match cs with [] => [] | c :: rest => cb_ast c :: go rest end) cs
    = map cb_ast cs.
Proof. induction cs as [|c rest IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

(* Peel a quote back open, so the inlined fixpoint above has a name the
   telescoping lemma can mention. *)
Definition unquote (n : node block) : blocks :=
  match node_contents n with BlockQuote bs => bs | _ => [] end.

Lemma cb_ast_quote :
  forall inner, cb_ast (CQuote inner) = mk (BlockQuote (map cb_ast inner)).
Proof.
  assert (H : forall cs, unquote (cb_ast (CQuote cs)) = map cb_ast cs).
  { induction cs as [|c rest IH]; [reflexivity|].
    change (unquote (cb_ast (CQuote (c :: rest))))
      with (cb_ast c :: unquote (cb_ast (CQuote rest))).
    rewrite IH. reflexivity. }
  intros inner.
  change (cb_ast (CQuote inner))
    with (mk (BlockQuote (unquote (cb_ast (CQuote inner))))).
  rewrite H. reflexivity.
Qed.

Lemma cb_lines_quote :
  forall inner,
    cb_lines (CQuote inner) = map quote_line (sep_lines (map cb_lines inner)).
Proof.
  induction inner as [|c rest IH]; [reflexivity|].
  destruct rest as [|c2 rest'].
  - reflexivity.
  - change (cb_lines (CQuote (c :: c2 :: rest')))
      with (map quote_line (cb_lines c)
            ++ quote_open :: cb_lines (CQuote (c2 :: rest')))%list.
    rewrite IH.
    cbn [map sep_lines]. rewrite map_app. cbn [map].
    rewrite quote_line_empty. reflexivity.
Qed.

(* Peel a list back open, the same trick as unquote. *)
Definition unlist (n : node block) : list (list (node block)) :=
  match node_contents n with BulletList _ items => items | _ => [] end.

Lemma cb_ast_list :
  forall sp items,
    cb_ast (CList sp items) = mk (BulletList sp (map (map cb_ast) items)).
Proof.
  assert (H : forall sp0 iss, unlist (cb_ast (CList sp0 iss)) = map (map cb_ast) iss).
  { intros sp0 iss. induction iss as [|it rest IH]; [reflexivity|].
    change (unlist (cb_ast (CList sp0 (it :: rest))))
      with ((fix go (cs : list cblock) : blocks :=
               match cs with [] => [] | c :: r => cb_ast c :: go r end) it
            :: unlist (cb_ast (CList sp0 rest))).
    rewrite cb_asts_eq, IH. reflexivity. }
  intros sp items.
  change (cb_ast (CList sp items))
    with (mk (BulletList sp (unlist (cb_ast (CList sp items))))).
  rewrite H. reflexivity.
Qed.

Lemma cb_lines_list :
  forall sp items,
    cb_lines (CList sp items)
    = list_lines sp (map (fun it => indent_lines bullet_open bullet_cont
                                       (sep_lines (map cb_lines it))) items).
Proof.
  intros sp items. induction items as [|it rest IH]; [reflexivity|].
  destruct rest as [|it2 rest'].
  - reflexivity.
  - change (cb_lines (CList sp (it :: it2 :: rest')))
      with (indent_lines bullet_open bullet_cont (sep_lines (map cb_lines it))
            ++ (match sp with Loose => [EmptyString] | Tight => [] end)
            ++ cb_lines (CList sp (it2 :: rest')))%list.
    rewrite IH. cbn [map list_lines]. reflexivity.
Qed.

(* Rocq's generated cblock_ind does not descend into CQuote's list or
   CList's list of lists, so every proof over cblocks needs this
   three-predicate version: P for a block, Q for a list of them (a
   quote's contents, or one list item), R for a list of item lists (a
   whole CList's items) — R just packages "Q holds for every item",
   built from the same Q/golist a quote uses. *)
Definition cblock_ind2
  (P : cblock -> Prop) (Q : list cblock -> Prop) (R : list (list cblock) -> Prop)
  (hpara : forall ls, P (CPara ls))
  (hthem : P CThematic)
  (hcode : forall info content, P (CCode info content))
  (hhead : forall lvl ls, P (CHeading lvl ls))
  (hquote : forall inner, Q inner -> P (CQuote inner))
  (hlist : forall sp items, R items -> P (CList sp items))
  (hnil : Q [])
  (hcons : forall c rest, P c -> Q rest -> Q (c :: rest))
  (hrnil : R [])
  (hrcons : forall item items, Q item -> R items -> R (item :: items))
  : forall cb, P cb :=
  fix go (cb : cblock) : P cb :=
    let golist :=
      fix golist (cs : list cblock) : Q cs :=
        match cs with
        | [] => hnil
        | c :: rest => hcons c rest (go c) (golist rest)
        end in
    match cb with
    | CPara ls => hpara ls
    | CThematic => hthem
    | CCode info content => hcode info content
    | CHeading lvl ls => hhead lvl ls
    | CQuote inner => hquote inner (golist inner)
    | CList sp items =>
        hlist sp items
          ((fix golistlist (iss : list (list cblock)) : R iss :=
              match iss with
              | [] => hrnil
              | it :: rest => hrcons it rest (golist it) (golistlist rest)
              end) items)
    end.

Definition blocks_of_cblocks (cbs : list cblock) : blocks := map cb_ast cbs.

(*
Renderability
-------------
*)

(* A canonical paragraph: nonempty; its first line classifies as text (so
   reparsing opens a paragraph there rather than another block); every
   line is nonblank and newline-free; and the last line already has no
   trailing whitespace, since the parser would strip it. *)
Definition para_ok (ls : list string) : bool :=
  match ls with
  | [] => false
  | a :: _ =>
      is_text a
      && forallb line_ok ls
      && String.eqb (strip_trailing_ws (last ls EmptyString))
           (last ls EmptyString)
  end.

(* A canonical code block: valid info string, and content lines that are
   newline-free and do not close a 3-backtick fence.  Content lines may
   be blank or look like any other construct — fences are verbatim. *)
Definition code_ok (info : string) (content : list string) : bool :=
  all_info_chars info
  && forallb
       (fun l => no_nl l && negb (fence_close (Fence "`"%char 3 info) l))
       content.

(* A canonical heading: a real level, and text lines that are nonblank
   and newline-free with the last one pre-stripped (the parser strips
   it).  Unlike a paragraph there is no first-line classification
   condition — the hashes make every rendered line a heading line, and
   the text is never reclassified.  Nonempty for the same reason a quote
   is: `Heading lvl []` renders to no lines at all. *)
Definition heading_ok (lvl : nat) (ls : list string) : bool :=
  Nat.leb 1 lvl
  && nonempty ls
  && forallb line_ok ls
  && String.eqb (strip_trailing_ws (last ls EmptyString)) (last ls EmptyString).

(* Tight/loose, on the item's lines rather than on its block tree.

   The tree is the wrong domain: a gap loosens the enclosing list unless
   a list claims it -- either the next non-blank line opens one, or one
   is already open where the gap falls -- and the tree does not record
   where blanks sit relative to markers.  Two items of the same shape,
   both a block then a gap then a paragraph, part ways on it: `["- b";
   ""; "t"]` leaves the list tight because the gap is the inner list's
   trailing blank, and `["a"; ""; "t"]` loosens it.

   `Parser.lines_loose` is the rule itself, and it is what
   `Parser.list_uniformity` proves the parser implements. *)
(* An item's own lines, before the marker and the continuation pad go on
   -- what the parser reparses the item as, by Parser.list_uniformity. *)
Definition item_lines (it : list cblock) : list string :=
  sep_lines (map cb_lines it).

Definition item_forces_loose (item : list cblock) : bool :=
  item_loose (item_lines item).

Definition items_force_loose (items : list (list cblock)) : bool :=
  existsb item_forces_loose items.

(* Whether a separator blank in the loose rendering actually reaches the
   list.  It does not when the item before it ends with a nested list:
   the blank is that list's trailing blank, exempt from tightness, and
   `Parser.step` gives it to the inner list.  Mirrors
   `Parser.seps_loosen`, which is what `list_uniformity` carries, and it
   is why a multi-item list is not automatically spellable `Loose`. *)
Definition items_seps_loosen (items : list (list cblock)) : bool :=
  seps_loosen (map item_lines items).

Definition is_clist (cb : cblock) : bool :=
  match cb with CList _ _ => true | _ => false end.

(** Two adjacent canonical lists cannot roundtrip as two AST nodes: the
    separating blank makes the parser continue the first list as loose.
    This is a property of a block sequence, not either block alone. *)
Fixpoint no_adjacent_lists (cbs : list cblock) : bool :=
  match cbs with
  | [] => true
  | c1 :: rest =>
      match rest with
      | [] => true
      | c2 :: _ =>
          negb (is_clist c1 && is_clist c2) && no_adjacent_lists rest
      end
  end.

(* Regression: the recursive call slides by one block, so every adjacent
   pair is tested.  Recursing on the tail *after* c2 instead would test
   pairs 1-2, 3-4, ... and miss the offending pair in the third example.
   Three blocks is the shortest input that tells the two apart. *)
Section NoAdjacentListsTests.
  Let l : cblock := CList Tight [[CPara ["a"]]].
  Let p : cblock := CPara ["p"].

  Example no_adjacent_lists_pair : no_adjacent_lists [l; l] = false.
  Proof. reflexivity. Qed.

  Example no_adjacent_lists_separated : no_adjacent_lists [l; p; l] = true.
  Proof. reflexivity. Qed.

  Example no_adjacent_lists_second_pair : no_adjacent_lists [p; l; l] = false.
  Proof. reflexivity. Qed.

  Example no_adjacent_lists_run : no_adjacent_lists [l; l; l] = false.
  Proof. reflexivity. Qed.

  Example no_adjacent_lists_singleton : no_adjacent_lists [l] = true.
  Proof. reflexivity. Qed.
End NoAdjacentListsTests.

(* An item's rendered lines have to satisfy `Parser.item_ok`, which is
   the hypothesis of `Parser.list_uniformity` -- the theorem that says an
   item's contents parse exactly as they would at top level, whatever
   they are.  Spelled out, it asks that "- " does not turn the item's
   first line into a thematic break (classify tests thematic breaks
   before list markers -- the one condition quotes and headings never
   needed, since "> " and "# " are not marker-shaped), that the item
   neither starts nor ends blank, and that no fence is left open inside
   it.

   Nothing here mentions nesting: a list inside a list item clears these
   exactly as flat content does, which is why the fragment covers it. *)

(* The roundtrip hypothesis: this cblock renders to lines that parse back
   to it.  A new construct adds its obligation here.

   A quote must be nonempty: its rendering is its contents' lines with a
   prefix, so an empty quote would render to nothing at all.  The parser
   *can* build `BlockQuote []` (from a bare ">"), so that one value sits
   outside the canonical view — see cb_ok_quote.  A list's items are each
   held to the same nonempty-and-cb_ok-and-no_adjacent_lists standard as
   a quote's contents (`inner_ok`, reused per item), plus `item_ok` on
   the item's rendering (above) and a spacing
   condition tying `sp` back to what item_forces_loose can prove about
   the *specific* rendering below: tight needs no gap to force looseness
   anywhere; loose needs either two-or-more items (list_lines then always
   inserts a forcing blank itself) or an internal gap to justify the
   single-item case, where no inter-item blank exists at all. *)
Fixpoint cb_ok (cb : cblock) : bool :=
  let inner_ok :=
    fix go (cs : list cblock) : bool :=
      match cs with
      | [] => false                        (* empty quote/item: not renderable *)
      | [c] => cb_ok c
      | c :: rest => (cb_ok c && go rest)%bool
      end in
  let items_ok :=
    fix goitems (iss : list (list cblock)) : bool :=
      match iss with
      | [] => true
      | it :: rest => (inner_ok it && goitems rest)%bool
      end in
  match cb with
  | CPara ls => para_ok ls
  | CThematic => true
  | CCode info content => code_ok info content
  | CHeading lvl ls => heading_ok lvl ls
  | CQuote inner => inner_ok inner && no_adjacent_lists inner
  | CList sp items =>
      nonempty items && items_ok items
      && forallb (fun it => item_ok (item_lines it)) items
      && forallb no_adjacent_lists items
      && match sp with
         | Tight => negb (items_force_loose items)
         | Loose => items_seps_loosen items || items_force_loose items
         end
  end.

(* cb_ok's `inner_ok` helper, spelled out: a quote's contents or a list
   item are renderable exactly when nonempty and every cblock in them is
   cb_ok.  One fact, reused for both cb_ok_quote and cb_ok_list. *)
Lemma inner_ok_eq :
  forall cs,
    (fix go (cs : list cblock) : bool :=
       match cs with
       | [] => false
       | [c] => cb_ok c
       | c :: rest => (cb_ok c && go rest)%bool
       end) cs
    = (nonempty cs && forallb cb_ok cs)%bool.
Proof.
  induction cs as [|c rest IH]; [reflexivity|].
  destruct rest as [|c2 rest'].
  - cbn [forallb nonempty]. rewrite andb_true_r. reflexivity.
  - change ((fix go (cs : list cblock) : bool :=
               match cs with [] => false | [c0] => cb_ok c0
               | c0 :: r => (cb_ok c0 && go r)%bool end) (c :: c2 :: rest'))
      with (cb_ok c &&
            (fix go (cs : list cblock) : bool :=
               match cs with [] => false | [c0] => cb_ok c0
               | c0 :: r => (cb_ok c0 && go r)%bool end) (c2 :: rest'))%bool.
    rewrite IH. cbn [nonempty forallb]. reflexivity.
Qed.

Lemma cb_ok_quote :
  forall inner,
    cb_ok (CQuote inner)
    = (nonempty inner && forallb cb_ok inner && no_adjacent_lists inner)%bool.
Proof. intros inner. unfold cb_ok. rewrite inner_ok_eq. reflexivity. Qed.

Definition cblocks_ok (cbs : list cblock) : bool :=
  (forallb cb_ok cbs && no_adjacent_lists cbs)%bool.

Lemma no_adjacent_after_list :
  forall sp items next rest,
    no_adjacent_lists (CList sp items :: next :: rest) = true ->
    is_clist next = false.
Proof.
  intros sp items next rest H. cbn [no_adjacent_lists is_clist] in H.
  apply andb_true_iff in H as [Hnext _].
  apply negb_true_iff in Hnext. destruct (is_clist next); [discriminate|].
  reflexivity.
Qed.

Lemma cblocks_ok_parts :
  forall cbs, cblocks_ok cbs = true ->
    forallb cb_ok cbs = true /\ no_adjacent_lists cbs = true.
Proof.
  intros cbs H. unfold cblocks_ok in H. apply andb_true_iff in H. exact H.
Qed.

(* cb_ok's `items_ok` helper, spelled out via inner_ok_eq per item. *)
Lemma items_ok_eq :
  forall items,
    (fix goitems (iss : list (list cblock)) : bool :=
       match iss with
       | [] => true
       | it :: rest =>
           ((fix go (cs : list cblock) : bool :=
               match cs with
               | [] => false
               | [c] => cb_ok c
               | c :: r => (cb_ok c && go r)%bool
               end) it && goitems rest)%bool
       end) items
    = forallb (fun it => nonempty it && forallb cb_ok it)%bool items.
Proof.
  induction items as [|it rest IH]; [reflexivity|].
  cbn [forallb]. rewrite <- IH, <- inner_ok_eq. reflexivity.
Qed.

Lemma cb_ok_list :
  forall sp items,
    cb_ok (CList sp items)
    = (nonempty items
       && forallb (fun it => nonempty it && forallb cb_ok it)%bool items
       && forallb (fun it => item_ok (item_lines it)) items
       && forallb no_adjacent_lists items
       && match sp with
          | Tight => negb (items_force_loose items)
          | Loose => items_seps_loosen items || items_force_loose items
          end)%bool.
Proof.
  intros sp items. unfold cb_ok. fold cb_ok. rewrite items_ok_eq. reflexivity.
Qed.

(*
The renderer
============
*)

(* Recover the lines of a paragraph from its inlines: Str extends the
   current line, SoftBreak ends it.  (Other inline constructors don't
   occur in the fragment; they contribute nothing.) *)

Fixpoint inline_lines (ils : inlines) (cur : string) : list string :=
  match ils with
  | [] => [cur]
  | Node _ _ (Str s) :: rest => inline_lines rest (cur ++ s)
  | Node _ _ SoftBreak :: rest => cur :: inline_lines rest EmptyString
  | _ :: rest => inline_lines rest cur
  end.

(* Render one block to its djot source *lines*.  Line-valued rather than
   string-valued because djot's block structure is line structure: a
   quote's rendering is its contents' lines with a prefix on each, which
   a string-valued renderer could only express by re-splitting.

   Same hand-inlined fixpoint as cb_lines, and for the same reason. *)
Fixpoint render_block_lines (b : block) : list string :=
  let quoted :=
    fix go (ns : list (node block)) : list string :=
      match ns with
      | [] => []
      | [Node _ _ x] => map quote_line (render_block_lines x)
      | Node _ _ x :: rest =>
          (map quote_line (render_block_lines x) ++ quote_open :: go rest)%list
      end in
  let bulleted :=
    fix goitems (sp : list_spacing) (items : list blocks) : list string :=
      match items with
      | [] => []
      | [it] =>
          indent_lines bullet_open bullet_cont
            (sep_lines (map (fun n => render_block_lines (node_contents n)) it))
      | it :: rest =>
          (indent_lines bullet_open bullet_cont
             (sep_lines (map (fun n => render_block_lines (node_contents n)) it))
           ++ (match sp with Loose => [EmptyString] | Tight => [] end)
           ++ goitems sp rest)%list
      end in
  match b with
  | Para ils => inline_lines ils EmptyString
  | Heading lvl ils => map (heading_line lvl) (inline_lines ils EmptyString)
  | ThematicBreak => [thematic_line]
  | CodeBlock lang text =>
      (code_open lang :: split_lines text ++ [code_close])%list
  | RawBlock fmt text =>
      (code_open ("=" ++ fmt) :: split_lines text ++ [code_close])%list
  | BlockQuote bs => quoted bs
  | BulletList sp items => bulleted sp items
  | _ => []   (* TODO: extend with the parser, construct by construct *)
  end.

Definition render_blocks_lines (bs : blocks) : list (list string) :=
  map (fun n => render_block_lines (node_contents n)) bs.

Lemma render_block_quote :
  forall bs,
    render_block_lines (BlockQuote bs)
    = map quote_line (sep_lines (render_blocks_lines bs)).
Proof.
  induction bs as [|n rest IH]; [reflexivity|].
  destruct n as [p a x]. destruct rest as [|n2 rest'].
  - reflexivity.
  - change (render_block_lines (BlockQuote (Node p a x :: n2 :: rest')))
      with (map quote_line (render_block_lines x)
            ++ quote_open :: render_block_lines (BlockQuote (n2 :: rest')))%list.
    rewrite IH.
    unfold render_blocks_lines. cbn [map sep_lines].
    rewrite map_app. cbn [map]. rewrite quote_line_empty. reflexivity.
Qed.

Lemma render_bullet_list :
  forall sp items,
    render_block_lines (BulletList sp items)
    = list_lines sp
        (map (fun it => indent_lines bullet_open bullet_cont
                 (sep_lines (render_blocks_lines it))) items).
Proof.
  intros sp items. induction items as [|it rest IH]; [reflexivity|].
  destruct rest as [|it2 rest'].
  - reflexivity.
  - change (render_block_lines (BulletList sp (it :: it2 :: rest')))
      with (indent_lines bullet_open bullet_cont
              (sep_lines (render_blocks_lines it))
            ++ (match sp with Loose => [EmptyString] | Tight => [] end)
            ++ render_block_lines (BulletList sp (it2 :: rest')))%list.
    rewrite IH. cbn [map list_lines]. reflexivity.
Qed.

(* Blocks separated by a blank line — the separator the parser reads back
   as "end the current block". *)
Definition render_djot (bs : blocks) : string :=
  String.concat nl (sep_lines (render_blocks_lines bs)).

(* Rendering is now a single join over one flat line list, so the
   roundtrip's split side is just split/join inversion (Strings.v) —
   there is no separate "paragraph layout" notion to invert. *)
