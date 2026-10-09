(* ai-disclosure: ai-generated *)

(* Throwaway: step 0 of `.project/261009.plan.eager-regions.md`, deleted
   when step 1 lands.  The precedence reading over byte positions, with
   the eager regions as tokens, computed and run against the scanner by
   `test/regions.ml`.  Nothing here is proved. *)

From Stdlib Require Import String Ascii List Bool Arith.
From DjotV Require Import Strings Ast Attributes InlineTable InlineView InlineScan
  Precedence.
Import ListNotations.

Local Open Scope string_scope.

Section WithTable.
Context {T : dtable}.

(*
Tokens
======
*)

(* What a closed verbatim's run is followed by: a raw format, or a raw
   spec that failed, which is text up to the byte that stopped it. *)
Inductive vtail : Type := VTNone | VTRaw (fmt : string) | VTLit (spec : string).

Inductive btoken : Type :=
  | BTok (t : token)
  | BVerb (math : option math_style) (body : string) (tail : vtail)
  | BAuto (src : string) (ok : bool)
  | BSym (alias : string).

Definition sdrop (n : nat) (s : string) : string :=
  substring n (String.length s - n) s.

Fixpoint take_until (stop : ascii -> bool) (s : string) : string :=
  match s with
  | String c r => if stop c then EmptyString else String c (take_until stop r)
  | EmptyString => EmptyString
  end.

Fixpoint tick_run (s : string) : nat :=
  match s with
  | String c r => if is_tick c then S (tick_run r) else 0
  | EmptyString => 0
  end.

(* The body of a width-`n` verbatim, the bytes it uses with its closing
   run, and whether it closed.  `run` counts the ticks pending. *)
Fixpoint verb_go (n run : nat) (s : string) : string * nat * bool :=
  match s with
  | EmptyString =>
      if Nat.eqb run n then (EmptyString, 0, true) else (ticks run, 0, false)
  | String c rest =>
      if is_tick c then
        let '(b, l, cl) := verb_go n (S run) rest in (b, S l, cl)
      else if Nat.eqb run n then (EmptyString, 0, true)
      else let '(b, l, cl) := verb_go n 0 rest in
           ((ticks run ++ String c b)%string, S l, cl)
  end.

Definition raw_end (c : ascii) : bool :=
  (Ascii.eqb c rbrace || raw_stop c || Ascii.eqb c nl_char)%bool.

Definition verb_tail (r : string) : vtail * nat :=
  match r with
  | String b (String e r') =>
      if (Ascii.eqb b lbrace && Ascii.eqb e eqchar)%bool then
        let f := take_until raw_end r' in
        match sdrop (String.length f) r' with
        | String c _ =>
            if (Ascii.eqb c rbrace && nonempty_str f && raw_inline_enabled)%bool
            then (VTRaw f, 3 + String.length f)
            else (VTLit (String eqchar f), 2 + String.length f)
        | EmptyString => (VTLit (String eqchar f), 2 + String.length f)
        end
      else (VTNone, 0)
  | _ => (VTNone, 0)
  end.

(* A verbatim whose opening run starts `s`; `pre` bytes of math prefix
   before it. *)
Definition verb_at (math : option math_style) (pre : nat) (s : string)
  : btoken * nat :=
  let n := tick_run s in
  let '(body, used, closed) := verb_go n 0 (sdrop n s) in
  match math, closed with
  | None, true =>
      let '(tl, k) := verb_tail (sdrop (n + used) s) in
      (BVerb None body tl, pre + n + used + k)
  | _, _ => (BVerb math body VTNone, pre + n + used)
  end.

Definition tok_len (t : token) : nat :=
  match t with
  | TDelim k false _ _ => dwidth k
  | TDelim k true _ _ => S (dwidth k)
  | TEsc _ => 2
  | TEscWs ws | THard ws => S (String.length ws)
  | _ => 1
  end.

Definition starts (c : ascii) (s : string) : bool :=
  match s with String d _ => Ascii.eqb d c | EmptyString => false end.

(* The token at the head of `s`, `prev` the byte before it, and its
   length. *)
Definition bnext (prev : option ascii) (s : string) : option (btoken * nat) :=
  match s with
  | EmptyString => None
  | String c rest =>
      Some
        (if Ascii.eqb c nl_char then (BTok TBreak, 1)
         else if is_bslash c then
           let line := take_until (Ascii.eqb nl_char) rest in
           if is_blank line then (BTok (THard line), S (String.length line))
           else match rest with
                | String d _ =>
                    if is_ws d then let w := ws_run rest in
                                    (BTok (TEscWs w), S (String.length w))
                    else (BTok (TEsc d), 2)
                | EmptyString => (BTok (THard EmptyString), 1)
                end
         else if is_tick c then verb_at None 0 s
         else if (Ascii.eqb c dollar && math_enabled && starts tick rest)%bool
         then verb_at (Some InlineMath) 1 rest
         else if (Ascii.eqb c dollar && math_enabled && starts dollar rest
                  && starts tick (sdrop 1 rest))%bool
         then verb_at (Some DisplayMath) 2 (sdrop 1 rest)
         else if Ascii.eqb c lt then
           let src := take_until (fun d => Ascii.eqb d gt || Ascii.eqb d lt
                                            || is_ws d || Ascii.eqb d nl_char)%bool rest in
           if (starts gt (sdrop (String.length src) rest)
               && auto_body_ok src && auto_kind_ok src)%bool
           then (BAuto src true, 2 + String.length src)
           else (BAuto src false, 1 + String.length src)
         else if Ascii.eqb c ":"%char then
           let a := take_until (fun d => negb (symbol_char d)) rest in
           if (starts ":"%char (sdrop (String.length a) rest) && nonempty_str a)%bool
           then (BSym a, 2 + String.length a)
           else (BTok (TText c), 1)
         else match lex prev 0 s with
              | t :: _ => (BTok t, tok_len t)
              | [] => (BTok (TText c), 1)
              end)
  end.

(*
The alphabet
============

Every token on every chain a reading may take: the bytes of an ordinary
token as stage 1 has them, and a region token whatever it holds. *)

Fixpoint bytes_ok (n : nat) (s : string) : bool :=
  match n, s with
  | S n', String c rest => (in_alphabet c && follow_ok c rest && bytes_ok n' rest)%bool
  | _, _ => true
  end.

Definition tok_ok (t : btoken) (len : nat) (s : string) : bool :=
  match t with
  | BTok (TEsc _ | TEscWs _ | THard _ | TBreak) => true
  | BTok (TText c) =>
      if Ascii.eqb c dollar then negb dollar_math_enabled
      else if Ascii.eqb c ":"%char then negb tags_enabled
      else bytes_ok 1 s
  | BTok _ => bytes_ok len s
  | BVerb _ _ _ | BAuto _ _ => true
  | BSym _ => negb tags_enabled
  end.

(* From the byte after a destination's `(`: the offset of its `)`. *)
Fixpoint dest_end (esc : bool) (depth i : nat) (s : string) : option nat :=
  match s with
  | EmptyString => None
  | String c rest =>
      if esc then dest_end false depth (S i) rest
      else if is_bslash c then dest_end true depth (S i) rest
      else if Ascii.eqb c lparen then dest_end false (S depth) (S i) rest
      else if Ascii.eqb c rparen
      then match depth with O => Some i | S d => dest_end false d (S i) rest end
      else dest_end false depth (S i) rest
  end.

Fixpoint label_end (esc : bool) (i : nat) (s : string) : option nat :=
  match s with
  | EmptyString => None
  | String c rest =>
      if esc then label_end false (S i) rest
      else if is_bslash c then label_end true (S i) rest
      else if Ascii.eqb c rbrack then Some i
      else label_end false (S i) rest
  end.

Definition breg_end (dest : bool) (r : string) : option nat :=
  if dest then dest_end false 0 0 r else label_end false 0 r.

Definition last_byte (len : nat) (s : string) : option ascii := get (pred len) s.

Fixpoint badm (fuel : nat) (prev : option ascii) (s : string) : bool :=
  match fuel with
  | O => true
  | S f =>
      match bnext prev s with
      | None => true
      | Some (t, len) =>
          (tok_ok t len s
           && match t with
              | BTok (TClose b) =>
                  let r := sdrop 2 s in
                  match breg_end b r with
                  | Some e => badm f (get e r) (sdrop (S e) r)
                  | None => true
                  end
              | _ => true
              end
           && badm f (last_byte len s) (sdrop len s))%bool
      end
  end.

(* A paragraph's lines as one string, the last without its trailing
   whitespace. *)
Fixpoint para_string (ls : list string) : string :=
  match ls with
  | [] => EmptyString
  | [x] => strip_trailing_ws x
  | x :: rest => (x ++ nl ++ para_string rest)%string
  end.

Definition proto_adm (ls : list string) : bool :=
  let s := para_string ls in badm (S (String.length s)) None s.

(*
The reading
===========

`ref_read`'s stack, driven along the chain.  A `]` that pairs jumps
the chain past its region. *)

Inductive bitem : Type :=
  | ITok (p : nat) (t : btoken)
  | IReg (dest : bool) (txt : string)
  | ILabelRest (txt : string).

Record bstate : Type := BState {
  b_live : list litem;
  b_pairs : matching;
  b_os : list nat;
  b_items : list bitem
}.

Fixpoint bgo (fuel p : nat) (prev : option ascii) (s : string) (st : bstate) : bstate :=
  match fuel with
  | O => st
  | S f =>
      match bnext prev s with
      | None => st
      | Some (t, len) =>
          let items := ITok p t :: b_items st in
          let next st' := bgo f (p + len) (last_byte len s) (sdrop len s) st' in
          match t with
          | BTok (TClose b) =>
              match pick KBracket (b_live st) with
              | PFound q below =>
                  let pairs := (q, p) :: b_pairs st in
                  let r := sdrop 2 s in
                  match breg_end b r with
                  | Some e =>
                      bgo f (p + 3 + e) (get e r) (sdrop (S e) r)
                        (BState below pairs (b_os st)
                           (IReg b (substring 0 e r) :: items))
                  | None =>
                      if b then next (BState (LBar p :: below) pairs (b_os st) items)
                      else BState below pairs (b_os st) (ILabelRest r :: items)
                  end
              | _ => next (BState (b_live st) (b_pairs st) (b_os st) items)
              end
          (* `rstep`'s, with "something between" read as the opener's
             token ending before the closer *)
          | BTok (TDelim k mr op cl) =>
              let open_it st' :=
                if op then BState (LOpen p (KDelim k mr) :: b_live st') (b_pairs st')
                                  (p :: b_os st') items
                else BState (b_live st') (b_pairs st') (b_os st') items in
              match (if cl then pick (KDelim k mr) (b_live st) else PNone) with
              | PFound q below =>
                  if Nat.ltb (q + (if mr then S (dwidth k) else dwidth k)) p
                  then next (BState below ((q, p) :: b_pairs st) (b_os st) items)
                  else next (open_it st)
              | PBarred => next (BState (b_live st) (b_pairs st) (b_os st) items)
              | PNone => next (open_it st)
              end
          | BTok t0 =>
              let rs := rstep [] p t0 (RState (b_live st) (b_pairs st) (b_os st) RNormal) in
              next (BState (rs_live rs) (rs_pairs rs) (rs_os rs) items)
          | _ => next (BState (b_live st) (b_pairs st) (b_os st) items)
          end
      end
  end.

Definition proto_read (ls : list string) : bstate :=
  let s := para_string ls in bgo (S (String.length s)) 0 None s (BState [] [] [] []).

(*
The tree
========
*)

Fixpoint dest_go (esc : bool) (s : string) : string :=
  match s with
  | String c rest =>
      if esc then (esc_text c ++ dest_go false rest)%string
      else if is_bslash c then dest_go true rest
      else String c (dest_go false rest)
  | EmptyString => if esc then one bslash else EmptyString
  end.

Definition dest_text (s : string) : string := dest_go false s.

Definition vnode_of (math : option math_style) (body : string) : inline :=
  match math with
  | Some st => Math st (trim_verb body)
  | None => Verbatim (trim_verb body)
  end.

Fixpoint btree_go (m : matching) (items : list bitem) (hard : bool)
  (fs : tframes) (top : inlines) : tframes * inlines :=
  match items with
  | [] => (fs, top)
  | ITok p t :: rest =>
      match t with
      | BTok TBreak =>
          if hard then btree_go m rest false fs top
          else let '(fs', top') := temit (mk SoftBreak) fs top in
               btree_go m rest false fs' top'
      | BTok (TClose b) =>
          match is_closer m p, fs with
          | true, (_, acc) :: fs0 =>
              let kids := List.rev acc in
              match rest with
              | IReg b' txt :: rest' =>
                  let txt' := if b' then dest_text txt else txt in
                  let '(fs', top') := temit (mk (region_node b' kids txt')) fs0 top in
                  btree_go m rest' false fs' top'
              | ILabelRest txt :: rest' =>
                  let '(fs', top') :=
                    temit_all (mk (Str (one lbrack)) :: kids
                               ++ [mk (Str (one rbrack ++ one lbrack ++ txt))])%list fs0 top in
                  btree_go m rest' false fs' top'
              | _ =>
                  let '(fs', top') :=
                    temit_all (mk (Str (one lbrack)) :: kids
                               ++ [mk (Str (one rbrack))])%list fs0 top in
                  btree_go m rest false fs' top'
              end
          | _, _ =>
              let '(fs', top') := temit_str (one rbrack) fs top in
              btree_go m rest false fs' top'
          end
      | BTok t0 =>
          let '(fs', top', _) := tstep [] m p t0 (fs, top, TMNormal) in
          btree_go m rest (match t0 with THard _ => true | _ => false end) fs' top'
      | BVerb math body tl =>
          let '(fs', top') :=
            match tl with
            | VTRaw fmt => temit (mk (RawInline fmt (trim_verb body))) fs top
            | VTNone => temit (mk (vnode_of math body)) fs top
            | VTLit spec =>
                let '(fs1, top1) := temit (mk (vnode_of math body)) fs top in
                temit_str (String lbrace spec) fs1 top1
            end in
          btree_go m rest false fs' top'
      | BAuto src ok =>
          let '(fs', top') :=
            if ok then temit (mk (auto_node src)) fs top
            else temit_str (String lt src) fs top in
          btree_go m rest false fs' top'
      | BSym a =>
          let '(fs', top') := temit (mk (Symbol a)) fs top in
          btree_go m rest false fs' top'
      end
  | _ :: rest => btree_go m rest false fs top
  end.

Definition proto_tree (ls : list string) : inlines :=
  let st := proto_read ls in
  List.rev (snd (btree_go (b_pairs st) (List.rev (b_items st)) false [] [])).

End WithTable.
