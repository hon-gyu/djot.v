(* ai-disclosure: autonomous *)

(** * Notes as a site: paths, routes, and the collision a real tree has

   A directory of notes is a map from paths to canonical documents, and
   publishing it is a map from paths to URLs.  Everything an SSG wants
   of that map -- build locality, link closure, a correct rename --
   rests on the routing being *injective on the site*, and the usual
   convention breaks exactly there: with `a/_index.dj` serving `/a/`,
   the sibling `a.dj` wants the same URL and one of the two pages
   silently disappears.

   So the rule is stated with its exclusion rather than beside it.
   `route_collide` says the index/sibling pair is the *only* way two
   paths collide, which is what makes `routes_ok` -- one decidable check
   an SSG can run over the tree -- the whole of the condition. *)

From Stdlib Require Import String Ascii List Bool.
From DjotV Require Import Strings Line Ast Parser Render.
Import ListNotations.

Local Open Scope string_scope.

(* A note's location, extension stripped: `a/b.dj` is ["a"; "b"].  A URL
   is the same shape, rendered with slashes by `url_string`. *)
Definition path : Type := list string.
Definition url : Type := list string.

Definition site : Type := list (path * list cblock).

Definition dom (s : site) : list path := map fst s.

(* The name that makes a file serve its directory rather than sit inside
   it.  Hugo spells it `_index`, Jekyll `index`; the rule is the same
   and only this string changes. *)
Definition index_name : string := "_index".

(* `a/b.dj` publishes at `/a/b/`, and `a/_index.dj` at `/a/` -- the
   index file *is* its directory. *)
Definition route (p : path) : url :=
  match rev p with
  | n :: rest => if String.eqb n index_name then rev rest else p
  | [] => p
  end.

Definition url_string (u : url) : string :=
  fold_right (fun seg acc => "/" ++ seg ++ acc) "/" u.

(*
The collision, and that it is the only one
==========================================
*)

(* Routing either leaves a path alone or drops one trailing `_index`. *)
Lemma route_shape :
  forall p, p = route p \/ p = (route p ++ [index_name])%list.
Proof.
  intros p. unfold route.
  destruct (rev p) as [|n rest] eqn:Erev.
  - left. reflexivity.
  - destruct (String.eqb n index_name) eqn:En; [|left; reflexivity].
    right. apply String.eqb_eq in En. subst n.
    rewrite <- (rev_involutive p), Erev. cbn [rev]. reflexivity.
Qed.

(** Two paths share a URL only if they are the same path, or a directory
    index and the file of the same name beside it.  That is the whole of
    what `routes_ok` has to exclude -- and it is why the rule cannot be
    stated without the exclusion: the two spellings are both natural and
    both name the same page. *)
Theorem route_collide :
  forall p q,
    route p = route q ->
    p = q \/ p = (q ++ [index_name])%list \/ q = (p ++ [index_name])%list.
Proof.
  intros p q H.
  destruct (route_shape p) as [Hp|Hp], (route_shape q) as [Hq|Hq].
  - left. rewrite Hp, Hq, H. reflexivity.
  - right; right. rewrite Hq, <- H, <- Hp. reflexivity.
  - right; left. rewrite Hp, H, <- Hq. reflexivity.
  - left. rewrite Hp, Hq, H. reflexivity.
Qed.

(*
The check an SSG runs
=====================
*)

Definition url_eqb (u v : url) : bool :=
  if list_eq_dec String.string_dec u v then true else false.

Fixpoint no_dup_urls (us : list url) : bool :=
  match us with
  | [] => true
  | u :: rest => negb (existsb (url_eqb u) rest) && no_dup_urls rest
  end.

(* One page per URL.  Decidable, and the first thing to run over a real
   tree, since a tree that fails it loses a page at build time with
   nothing to show for it. *)
Definition routes_ok (s : site) : bool := no_dup_urls (map route (dom s)).

Lemma url_eqb_true : forall u v, url_eqb u v = true -> u = v.
Proof.
  intros u v H. unfold url_eqb in H.
  destruct (list_eq_dec String.string_dec u v); [assumption|discriminate].
Qed.

Lemma url_eqb_refl : forall u, url_eqb u u = true.
Proof.
  intros u. unfold url_eqb. destruct (list_eq_dec String.string_dec u u);
    [reflexivity|contradiction].
Qed.

(** Route injectivity, on the site rather than on all paths: the check
    above is exactly the hypothesis every locality result upstream will
    want, since a site that passes it has one document per published
    URL. *)
Theorem routes_injective :
  forall s p q,
    routes_ok s = true ->
    In p (dom s) -> In q (dom s) ->
    route p = route q -> p = q.
Proof.
  intros s. unfold routes_ok. generalize (dom s). clear s.
  induction l as [|c rest IH]; intros p q Hok Hp Hq Hroute; [destruct Hp|].
  cbn [map no_dup_urls] in Hok. apply andb_true_iff in Hok as [Hfresh Hrest].
  apply negb_true_iff in Hfresh.
  assert (Hnot : forall x, In x rest -> route x <> route c).
  { intros x Hin Heq. rewrite <- Heq in Hfresh.
    assert (Hex : existsb (url_eqb (route x)) (map route rest) = true).
    { apply existsb_exists. exists (route x).
      split; [apply in_map, Hin | apply url_eqb_refl]. }
    rewrite Hex in Hfresh. discriminate. }
  destruct Hp as [<-|Hp]; destruct Hq as [<-|Hq].
  - reflexivity.
  - exfalso. apply (Hnot q Hq). symmetry. exact Hroute.
  - exfalso. apply (Hnot p Hp). exact Hroute.
  - exact (IH p q Hrest Hp Hq Hroute).
Qed.

(*
Building the site
=================

A build is a map over the site, and every page sees the other notes
*only* through an environment of summaries.  That factorization is the
whole content: with it, an edit that preserves a note's summary cannot
reach another note's page, and the statement below says so by naming
the untouched pages through the same map they had before the edit.

`summ` and `render_page` stay parameters.  Nothing here inspects either
-- what a summary holds (title, ids, outgoing links) is the link
checker's business, and pinning it would put that choice in the
locality theorem, where it does no work.
*)

Section Build.
Context {S P : Type}.
Variable summ : list cblock -> S.
Variable render_page : list (path * S) -> path -> list cblock -> P.

Definition env : Type := list (path * S).

Definition env_of (s : site) : env :=
  map (fun pd => (fst pd, summ (snd pd))) s.

Definition page (e : env) (pd : path * list cblock) : url * P :=
  (route (fst pd), render_page e (fst pd) (snd pd)).

Definition build (s : site) : list (url * P) := map (page (env_of s)) s.

Lemma env_of_app :
  forall pre q d post,
    env_of (pre ++ (q, d) :: post)%list
    = (env_of pre ++ (q, summ d) :: env_of post)%list.
Proof.
  intros pre q d post. unfold env_of. rewrite map_app. reflexivity.
Qed.

(** Build locality.  An edit that leaves the note's summary alone leaves
    every other page's rendering *identical as a term*: the environment
    it was rendered against did not move.  The consequence to say out
    loud is conditional -- editing a note's title, ids or outgoing links
    changes its summary and may move `env`, exactly as creating,
    deleting or renaming a note does. *)
Theorem build_local :
  forall pre q d0 d' post,
    summ d' = summ d0 ->
    let s := (pre ++ (q, d0) :: post)%list in
    build (pre ++ (q, d') :: post)%list
    = (map (page (env_of s)) pre
       ++ (route q, render_page (env_of s) q d') :: map (page (env_of s)) post)%list.
Proof.
  intros pre q d0 d' post Hsumm s.
  assert (Henv : env_of (pre ++ (q, d') :: post)%list = env_of s).
  { unfold s. rewrite !env_of_app, Hsumm. reflexivity. }
  unfold build. rewrite Henv, map_app. cbn [map page fst snd]. reflexivity.
Qed.

(* The companion equation, so that the two sides of the theorem above can
   be compared entry by entry: the unedited build has the same shape, with
   the old document in the one place that moved. *)
Lemma build_app :
  forall pre q d post,
    let s := (pre ++ (q, d) :: post)%list in
    build s
    = (map (page (env_of s)) pre
       ++ (route q, render_page (env_of s) q d) :: map (page (env_of s)) post)%list.
Proof.
  intros pre q d post s. unfold build, s. rewrite map_app.
  cbn [map page fst snd]. reflexivity.
Qed.

End Build.

(*
Links between notes
===================

The link checker needs to know what a summary *holds*, and only that:
`s_links` names the projection, so a summary stays whatever an
implementation wants it to be.  Naming the projection rather than the
record is what keeps `build_local` above quantified over any summary
type at all.
*)

Section Links.
Context {S : Type}.
Variable summ : list cblock -> S.
Variable s_links : S -> list path.

Definition path_eqb (p q : path) : bool := url_eqb p q.

(* No broken links, decidable: every note a page points at is a note the
   site has.  Stated over paths rather than URLs, since a path is what an
   author writes and `route` is not injective (`route_collide`). *)
Definition links_closed (s : site) : bool :=
  forallb (fun pd => forallb (fun t => existsb (path_eqb t) (dom s))
                       (s_links (summ (snd pd)))) s.

Theorem links_closed_target :
  forall s p d t,
    links_closed s = true ->
    In (p, d) s -> In t (s_links (summ d)) -> In t (dom s).
Proof.
  intros s p d t Hclosed Hin Ht.
  unfold links_closed in Hclosed.
  rewrite forallb_forall in Hclosed.
  specialize (Hclosed (p, d) Hin). cbn [snd] in Hclosed.
  rewrite forallb_forall in Hclosed.
  specialize (Hclosed t Ht).
  apply existsb_exists in Hclosed as [x [Hx Heq]].
  apply url_eqb_true in Heq. subst x. exact Hx.
Qed.

(* The notes that would have to be rewritten if this one were renamed.
   Computable from the environment alone, which is what makes the
   efficiency claim about rename a corollary of build locality rather
   than a new induction. *)
Definition backlinks (s : site) (p : path) : list path :=
  map fst (filter (fun pd => existsb (path_eqb p) (s_links (summ (snd pd)))) s).

Theorem backlinks_sound :
  forall s p q,
    In q (backlinks s p) ->
    exists d, In (q, d) s /\ In p (s_links (summ d)).
Proof.
  intros s p q H. unfold backlinks in H.
  apply in_map_iff in H as [[q' d] [Heq Hin]]. cbn [fst] in Heq. subst q'.
  apply filter_In in Hin as [Hin Hlink]. cbn [snd] in Hlink.
  apply existsb_exists in Hlink as [x [Hx Heq]].
  apply url_eqb_true in Heq. subst x.
  exists d. split; assumption.
Qed.

(* And a note nobody points at is a note a rename need not touch: this is
   the half of the efficiency claim that says the set is small, and it is
   read off the environment without opening a document. *)
Theorem backlinks_complete :
  forall s p q d,
    In (q, d) s -> In p (s_links (summ d)) -> In q (backlinks s p).
Proof.
  intros s p q d Hin Hlink. unfold backlinks.
  apply in_map_iff. exists (q, d). split; [reflexivity|].
  apply filter_In. split; [exact Hin|]. cbn [snd].
  apply existsb_exists. exists p. split; [exact Hlink | apply url_eqb_refl].
Qed.

End Links.

(*
Worked examples
===============
*)

Example route_index : route ["a"; index_name] = ["a"].
Proof. reflexivity. Qed.

Example route_urls :
  (url_string (route ["a"; "b"]), url_string (route ["a"; index_name]),
   url_string (route []))
  = ("/a/b/", "/a/", "/").
Proof. reflexivity. Qed.

(* The tree a real notes directory grows into, and the reason the rule
   needs its exclusion: both spellings are ordinary, and nothing about
   either one is wrong on its own. *)
Example index_sibling_collides :
  let s : site := [(["a"], []); (["a"; index_name], [])] in
  (route ["a"] = route ["a"; index_name] /\ routes_ok s = false).
Proof. split; reflexivity. Qed.

Example ordinary_tree_ok :
  let s : site := [([index_name], []); (["a"], []); (["a"; "b"], []);
                   (["a"; "c"], []); (["d"; index_name], [])] in
  routes_ok s = true.
Proof. reflexivity. Qed.

(* The link checker, computing.  `demo_links` stands in for a real link
   extractor -- what a note's links *are* needs a link syntax this file
   deliberately does not fix -- and exists only for the two examples
   below: every nonempty note points at `a.dj`. *)
Definition demo_links (d : list cblock) : list path :=
  match d with [] => [] | _ => [["a"]] end.

Example broken_link_detected :
  links_closed demo_links (fun x => x) [(["b"], [cpara ["x"]])] = false.
Proof. reflexivity. Qed.

Example closed_site_and_backlinks :
  let s : site := [(["a"], []); (["b"], [cpara ["x"]])] in
  (links_closed demo_links (fun x => x) s,
   backlinks demo_links (fun x => x) s ["a"])
  = (true, [["b"]]).
Proof. reflexivity. Qed.

(*
Where a note's links live
=========================

A rename has to rewrite the links inside the other notes, so the site
layer needs to see destinations in a canonical document.  Two
recursions do that -- collect them, and map over them -- and one
naturality law relates the pair.  Everything about *what a destination
means* is below this line, in the codec; nothing here knows.

`CIAuto` is deliberately not a destination: an autolink's region is its
source and its target both, so rewriting it would rewrite the visible
text, and `ci_ok` asks `auto_kind_ok` of it -- an email or a scheme --
which no note path spells.
*)

Fixpoint ci_dests (c : cinline) : list string :=
  match c with
  | CIDelim _ kids => flat_map ci_dests kids
  | CIRef _ kids _ => flat_map ci_dests kids
  | CILink _ kids dst => (dst :: flat_map ci_dests kids)%list
  | _ => []
  end.

Fixpoint ci_map_dest (f : string -> string) (c : cinline) : cinline :=
  match c with
  | CIDelim k kids => CIDelim k (map (ci_map_dest f) kids)
  | CILink img kids dst => CILink img (map (ci_map_dest f) kids) (f dst)
  | CIRef img kids label => CIRef img (map (ci_map_dest f) kids) label
  | _ => c
  end.

(* The inline layer's own two-predicate induction: `cinline`'s children
   are a `list cinline`, which the generated principle does not descend
   into.  Same shape as `Render.cblock_ind2`. *)
Definition cinline_ind2
  (P : cinline -> Prop) (Q : list cinline -> Prop)
  (hstr : forall s, P (CIStr s))
  (hverb : forall s, P (CIVerb s))
  (hdelim : forall k kids, Q kids -> P (CIDelim k kids))
  (hlink : forall img kids dst, Q kids -> P (CILink img kids dst))
  (href : forall img kids label, Q kids -> P (CIRef img kids label))
  (hnote : forall label, P (CINote label))
  (hauto : forall s, P (CIAuto s))
  (hraw : forall fmt s, P (CIRaw fmt s))
  (hnil : Q [])
  (hcons : forall c cs, P c -> Q cs -> Q (c :: cs))
  : forall c, P c :=
  fix go (c : cinline) : P c :=
    let golist :=
      fix golist (cs : list cinline) : Q cs :=
        match cs with
        | [] => hnil
        | c :: rest => hcons c rest (go c) (golist rest)
        end in
    match c with
    | CIStr s => hstr s
    | CIVerb s => hverb s
    | CIDelim k kids => hdelim k kids (golist kids)
    | CILink img kids dst => hlink img kids dst (golist kids)
    | CIRef img kids label => href img kids label (golist kids)
    | CINote label => hnote label
    | CIAuto s => hauto s
    | CIRaw fmt s => hraw fmt s
    end.

Lemma ci_dests_map :
  forall f c, ci_dests (ci_map_dest f c) = map f (ci_dests c).
Proof.
  intros f.
  refine (cinline_ind2
            (fun c => ci_dests (ci_map_dest f c) = map f (ci_dests c))
            (fun cs => flat_map ci_dests (map (ci_map_dest f) cs)
                       = map f (flat_map ci_dests cs))
            _ _ _ _ _ _ _ _ _ _); try reflexivity.
  - intros k kids IH. cbn [ci_map_dest ci_dests]. exact IH.
  - intros img kids dst IH. cbn [ci_map_dest ci_dests map]. rewrite IH. reflexivity.
  - intros img kids label IH. cbn [ci_map_dest ci_dests]. exact IH.
  - intros c cs IHc IHcs. cbn [map flat_map].
    rewrite map_app, IHc, IHcs. reflexivity.
Qed.

Definition cis_dests (cs : list cinline) : list string := flat_map ci_dests cs.
Definition css_dests (lss : list (list cinline)) : list string :=
  flat_map cis_dests lss.
Definition cis_map_dest (f : string -> string) (cs : list cinline) : list cinline :=
  map (ci_map_dest f) cs.
Definition css_map_dest (f : string -> string) (lss : list (list cinline))
  : list (list cinline) := map (cis_map_dest f) lss.

Definition ctrow_dests (r : ctrow) : list string := css_dests (ctrow_cells r).
Definition ctrow_map_dest (f : string -> string) (r : ctrow) : ctrow :=
  match r with
  | CTBody cs => CTBody (css_map_dest f cs)
  | CTHead als cs => CTHead als (css_map_dest f cs)
  end.

(* A reference definition's destination counts: `[label]: dest` is where
   a `CIRef` resolves, so a rename rewrites the definition and leaves the
   label alone. *)
Fixpoint cb_dests (cb : cblock) : list string :=
  match cb with
  | CPara ls => css_dests ls
  | CHeading _ ls => css_dests ls
  | CQuote inner => flat_map cb_dests inner
  | CDiv inner => flat_map cb_dests inner
  | CList _ _ items => flat_map (flat_map cb_dests) items
  | CRef _ dest => [dest]
  | CTable rows => flat_map ctrow_dests rows
  | CId _ inner => cb_dests inner
  | _ => []
  end.

Fixpoint cb_map_dest (f : string -> string) (cb : cblock) : cblock :=
  match cb with
  | CPara ls => CPara (css_map_dest f ls)
  | CHeading lvl ls => CHeading lvl (css_map_dest f ls)
  | CQuote inner => CQuote (map (cb_map_dest f) inner)
  | CDiv inner => CDiv (map (cb_map_dest f) inner)
  | CList k sp items => CList k sp (map (map (cb_map_dest f)) items)
  | CRef label dest => CRef label (f dest)
  | CTable rows => CTable (map (ctrow_map_dest f) rows)
  | CId i inner => CId i (cb_map_dest f inner)
  | cb => cb
  end.

Lemma cis_dests_map :
  forall f cs, cis_dests (cis_map_dest f cs) = map f (cis_dests cs).
Proof.
  intros f. induction cs as [|c cs IH]; [reflexivity|].
  unfold cis_dests, cis_map_dest in *. cbn [map flat_map].
  rewrite map_app, ci_dests_map, IH. reflexivity.
Qed.

Lemma css_dests_map :
  forall f lss, css_dests (css_map_dest f lss) = map f (css_dests lss).
Proof.
  intros f. induction lss as [|cs lss IH]; [reflexivity|].
  unfold css_dests, css_map_dest in *. cbn [map flat_map].
  rewrite map_app, cis_dests_map, IH. reflexivity.
Qed.

Lemma ctrow_dests_map :
  forall f r, ctrow_dests (ctrow_map_dest f r) = map f (ctrow_dests r).
Proof.
  intros f [cs|als cs]; unfold ctrow_dests, ctrow_map_dest;
    cbn [ctrow_cells]; apply css_dests_map.
Qed.

(** The naturality law the codec layer is built on: mapping over a
    document's destinations maps over the list of them.  It mentions no
    codec, so it is proved once and every codec-level fact below is list
    reasoning. *)
Lemma cb_dests_map :
  forall f cb, cb_dests (cb_map_dest f cb) = map f (cb_dests cb).
Proof.
  intros f.
  refine (cblock_ind2
            (fun cb => cb_dests (cb_map_dest f cb) = map f (cb_dests cb))
            (fun cbs => flat_map cb_dests (map (cb_map_dest f) cbs)
                        = map f (flat_map cb_dests cbs))
            (fun items => flat_map (flat_map cb_dests)
                            (map (map (cb_map_dest f)) items)
                          = map f (flat_map (flat_map cb_dests) items))
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
    try reflexivity.
  - intros ls. apply css_dests_map.
  - intros lvl ls. apply css_dests_map.
  - intros inner IH. exact IH.
  - intros inner IH. exact IH.
  - intros k sp items IH. exact IH.
  - intros rows. cbn [cb_dests cb_map_dest].
    induction rows as [|r rows IH]; [reflexivity|].
    cbn [map flat_map]. rewrite map_app, ctrow_dests_map, IH. reflexivity.
  - intros i inner IH. exact IH.
  - intros c rest IHc IHrest. cbn [map flat_map].
    rewrite map_app, IHc, IHrest. reflexivity.
  - intros item items IHitem IHitems. cbn [map flat_map].
    rewrite map_app, IHitem, IHitems. reflexivity.
Qed.

Definition doc_dests (d : list cblock) : list string := flat_map cb_dests d.
Definition doc_map_dest (f : string -> string) (d : list cblock) : list cblock :=
  map (cb_map_dest f) d.

Lemma doc_dests_map :
  forall f d, doc_dests (doc_map_dest f d) = map f (doc_dests d).
Proof.
  intros f. induction d as [|cb d IH]; [reflexivity|].
  unfold doc_dests, doc_map_dest in *. cbn [map flat_map].
  rewrite map_app, cb_dests_map, IH. reflexivity.
Qed.

(*
The link codec
==============

What a destination *means* is a convention, not a fact about djot, so it
is a parameter: which paths a convention can name, how one is spelled
from a given note, and which strings spell one.  A site-absolute codec
ignores `self`; a relative one resolves against it; a flat vault names
only top-level notes, which is what `l_ok` is for.

Three conditions, and each has a user below.  The round-trip is what
gives a rewritten link back.  `l_parse_stable` says whether a string
denotes a note does not depend on which note is asking -- only *which*
note it denotes does -- so moving a note cannot turn its prose into a
link.  `l_spell_canonical` says a destination that parses is already
spelled the way this codec spells it, which is what makes re-targeting
the identity where nothing moved; it also hands back `l_ok`, so a
parsed target is one the codec can re-spell.

Two conditions are *not* here, deliberately.  A rename rewrites source,
so the destinations it writes must be ones the canonical view accepts --
`no_nl` for a link (`Inline.ci_ok`) and `no_ws` for a reference
definition (`Render.ref_ok`).  Nothing below uses them, because nothing
below proves the renamed site is still canonical: `cblocks_ok` is
decidable and an implementation runs it, exactly as
`Address.replace_at_id_parse` asks it of the document coming out.  When
that theorem is written, those two conditions are what it will need. *)

Record lcodec : Type := LCodec {
  l_ok : path -> bool;
  l_spell : path -> path -> string;
  l_parse : path -> string -> option path }.

Definition lcodec_ok (L : lcodec) : Prop :=
  (forall self p, l_ok L p = true -> l_parse L self (l_spell L self p) = Some p)
  /\ (forall self self' s, l_parse L self s = None -> l_parse L self' s = None)
  /\ (forall self s t, l_parse L self s = Some t ->
                       l_spell L self t = s /\ l_ok L t = true).

Definition links_of (L : lcodec) (self : path) (d : list cblock) : list path :=
  flat_map (fun s => match l_parse L self s with Some t => [t] | None => [] end)
           (doc_dests d).

(* Re-target a note's links: every destination that denotes a note is
   re-spelled, at the note's new location and through the substitution.
   One function covers both halves of a rename, since the note being
   renamed also has to re-spell its own links from where it now sits. *)
Definition retarget (L : lcodec) (self self' : path) (g : path -> path)
  (d : list cblock) : list cblock :=
  doc_map_dest (fun s => match l_parse L self s with
                         | Some t => l_spell L self' (g t)
                         | None => s
                         end) d.

(** What re-targeting does to a note's links.  The side condition is the
    codec's own: a substitution may only send a nameable path to a
    nameable one, which at a rename is "the new name is one this
    convention can spell". *)
Lemma links_of_retarget :
  forall L self self' g d,
    lcodec_ok L ->
    (forall t, l_ok L t = true -> l_ok L (g t) = true) ->
    links_of L self' (retarget L self self' g d) = map g (links_of L self d).
Proof.
  intros L self self' g d (Hround & Hstable & Hcanon) Hg.
  unfold links_of, retarget. rewrite doc_dests_map.
  induction (doc_dests d) as [|s rest IH]; [reflexivity|].
  cbn [map flat_map]. destruct (l_parse L self s) as [t|] eqn:Es.
  - destruct (Hcanon self s t Es) as [_ Hokt].
    rewrite (Hround self' (g t) (Hg t Hokt)). cbn [app map].
    rewrite IH. reflexivity.
  - rewrite (Hstable self self' s Es). cbn [app]. exact IH.
Qed.

(*
Rename
======
*)

Definition subst_path (p q t : path) : path := if path_eqb t p then q else t.
Definition subst_url (u v x : url) : url := if url_eqb x u then v else x.

Definition rename (L : lcodec) (p q : path) (s : site) : site :=
  map (fun pd => (subst_path p q (fst pd),
                  retarget L (fst pd) (subst_path p q (fst pd))
                    (subst_path p q) (snd pd))) s.

(* The observable a rename is judged against: which URL each page is
   published at, and which URLs it points at.  `render_page` above stays
   abstract, so this is the part of a build a theorem can name. *)
Definition link_build (L : lcodec) (s : site) : list (url * list url) :=
  map (fun pd => (route (fst pd), map route (links_of L (fst pd) (snd pd)))) s.

Definition map_urls (u v : url) (b : list (url * list url))
  : list (url * list url) :=
  map (fun e => (subst_url u v (fst e), map (subst_url u v) (snd e))) b.

(* Substituting a path and substituting its URL are the same operation --
   but only on a site whose routes are injective, which is where
   `routes_ok` earns its place a second time. *)
Lemma route_subst :
  forall s p q x,
    routes_ok s = true -> In p (dom s) -> In x (dom s) ->
    route (subst_path p q x) = subst_url (route p) (route q) (route x).
Proof.
  intros s p q x Hok Hp Hx. unfold subst_path, subst_url.
  destruct (path_eqb x p) eqn:Exp.
  - apply url_eqb_true in Exp. subst x. rewrite url_eqb_refl. reflexivity.
  - destruct (url_eqb (route x) (route p)) eqn:Eroute; [|reflexivity].
    exfalso. apply url_eqb_true in Eroute.
    assert (x = p) by exact (routes_injective s x p Hok Hx Hp Eroute).
    subst x. rewrite url_eqb_refl in Exp. discriminate.
Qed.

Lemma dom_rename :
  forall L p q s, dom (rename L p q s) = map (subst_path p q) (dom s).
Proof.
  intros L p q s. unfold dom, rename. rewrite !map_map. reflexivity.
Qed.

(** Rename as a commuting square: renaming a note and rewriting one URL
    in the built site are the same operation.  Three hypotheses, and each
    is a check an implementation runs -- the codec's laws, route
    injectivity (so that substituting a path and substituting its URL
    agree), that the note being renamed exists, and that every link
    points at a note the site has. *)
Theorem rename_correct :
  forall L p q s,
    lcodec_ok L ->
    (forall t, l_ok L t = true -> l_ok L (subst_path p q t) = true) ->
    routes_ok s = true ->
    In p (dom s) ->
    (forall r d t, In (r, d) s -> In t (links_of L r d) -> In t (dom s)) ->
    link_build L (rename L p q s)
    = map_urls (route p) (route q) (link_build L s).
Proof.
  intros L p q s HL Hg Hroutes Hp Hclosed.
  unfold link_build, rename, map_urls. rewrite !map_map.
  apply map_ext_in. intros [r d] Hin. cbn [fst snd].
  assert (Hr : In r (dom s)) by (apply (in_map fst s (r, d) Hin)).
  f_equal.
  - exact (route_subst s p q r Hroutes Hp Hr).
  - rewrite (links_of_retarget L r (subst_path p q r) (subst_path p q) d HL Hg).
    rewrite !map_map. apply map_ext_in. intros t Ht.
    exact (route_subst s p q t Hroutes Hp (Hclosed r d t Hin Ht)).
Qed.

(* Which new names a rename may use.  The site has to stay one page per
   URL, and that is not "q is a new path": renaming `a.dj` to
   `a/_index.dj` keeps the URL and is fine, while renaming it onto a
   name that routes where another note already routes is not.
   `route_collide` is what says those are the only two shapes to think
   about. *)
Lemma subst_url_id : forall u x, subst_url u u x = x.
Proof.
  intros u x. unfold subst_url. destruct (url_eqb x u) eqn:E; [|reflexivity].
  apply url_eqb_true in E. symmetry. exact E.
Qed.

Lemma no_dup_urls_subst :
  forall us u v,
    no_dup_urls us = true ->
    (url_eqb v u = true \/ existsb (url_eqb v) us = false) ->
    no_dup_urls (map (subst_url u v) us) = true.
Proof.
  intros us u v Hdup [Heq|Hfresh].
  { apply url_eqb_true in Heq. subst v.
    rewrite (map_ext _ (fun x => x) (subst_url_id u)), map_id. exact Hdup. }
  revert Hdup Hfresh. induction us as [|x us IH]; intros Hdup Hfresh; [reflexivity|].
  cbn [map no_dup_urls existsb] in Hdup, Hfresh |- *.
  apply andb_true_iff in Hdup as [Hx Hus].
  apply orb_false_iff in Hfresh as [Hvx Hvus].
  apply negb_true_iff in Hx.
  rewrite (IH Hus Hvus), andb_true_r. apply negb_true_iff.
  destruct (existsb (url_eqb (subst_url u v x)) (map (subst_url u v) us)) eqn:E;
    [|reflexivity].
  exfalso. apply existsb_exists in E as [y [Hy Heqy]].
  apply in_map_iff in Hy as [z [<- Hz]]. apply url_eqb_true in Heqy.
  assert (Hzx : z = x).
  { unfold subst_url in Heqy.
    destruct (url_eqb z u) eqn:Ez, (url_eqb x u) eqn:Ex.
    - apply url_eqb_true in Ez. apply url_eqb_true in Ex.
      rewrite Ez, Ex. reflexivity.
    - exfalso. rewrite <- Heqy in Hvx. rewrite url_eqb_refl in Hvx. discriminate.
    - exfalso.
      assert (Hin : existsb (url_eqb v) us = true).
      { apply existsb_exists. exists z. split; [exact Hz|].
        rewrite Heqy. apply url_eqb_refl. }
      rewrite Hin in Hvus. discriminate.
    - symmetry. exact Heqy. }
  subst z.
  assert (Hin : existsb (url_eqb x) us = true).
  { apply existsb_exists. exists x. split; [exact Hz | apply url_eqb_refl]. }
  rewrite Hin in Hx. discriminate.
Qed.

(** And the rename leaves a site that still passes the check it came in
    with, which is where the new name's freshness earns its place: this
    is the precondition, and it is about *routes* rather than paths. *)
Theorem rename_routes_ok :
  forall L p q s,
    routes_ok s = true ->
    In p (dom s) ->
    (url_eqb (route q) (route p) = true
     \/ existsb (url_eqb (route q)) (map route (dom s)) = false) ->
    routes_ok (rename L p q s) = true.
Proof.
  intros L p q s Hok Hp Hfresh.
  unfold routes_ok in Hok |- *. rewrite dom_rename, map_map.
  rewrite (map_ext_in _ (fun x => subst_url (route p) (route q) (route x))
             (dom s) (fun x Hx => route_subst s p q x Hok Hp Hx)).
  rewrite <- map_map. apply no_dup_urls_subst; assumption.
Qed.

(*
One codec, and one rename it performs
=====================================

The flat vault: notes sit in one directory and a note links to another
by its name.  `l_ok` is what says so -- this convention cannot name a
nested note at all -- and it is why `l_ok` is a field rather than a
side condition someone remembers.
*)

Definition flat_ok (p : path) : bool :=
  match p with [n] => (nonempty_str n && no_char "/"%char n)%bool | _ => false end.

Definition flat_spell (_ : path) (p : path) : string :=
  match p with [n] => n | _ => EmptyString end.

Definition flat_parse (_ : path) (s : string) : option path :=
  if (nonempty_str s && no_char "/"%char s)%bool then Some [s] else None.

Definition flat : lcodec := LCodec flat_ok flat_spell flat_parse.

Lemma flat_lcodec_ok : lcodec_ok flat.
Proof.
  split; [|split].
  - intros self [|n [|m rest]] H; try discriminate H.
    cbn [l_ok l_spell l_parse flat flat_ok flat_spell flat_parse] in H |- *.
    unfold flat_parse. rewrite H. reflexivity.
  - intros self self' s H. exact H.
  - intros self s t H.
    cbn [l_parse l_spell l_ok flat] in H |- *. unfold flat_parse in H.
    destruct (nonempty_str s && no_char "/"%char s)%bool eqn:E; [|discriminate H].
    injection H as <-. cbn [flat_spell flat_ok]. rewrite E. split; reflexivity.
Qed.

(* What this convention cannot say, which is the point of `l_ok`: a
   nested note has no name here, so no rename may produce one. *)
Example flat_names_one_directory :
  (flat_ok ["a"], flat_ok ["a"; "b"], flat_ok [""]) = (true, false, false).
Proof. reflexivity. Qed.

Definition flat_site : site :=
  [ (["a"], [cpara ["hello"]])
  ; (["b"], [CPara [[CIStr "see "; CILink false [CIStr "a"] "a"]]]) ].

(* The rename, in the source: `b`'s link destination is rewritten, and
   nothing else in `b` moves. *)
Example flat_rename_rewrites_source :
  rename flat ["a"] ["c"] flat_site
  = [ (["c"], [cpara ["hello"]])
    ; (["b"], [CPara [[CIStr "see "; CILink false [CIStr "a"] "c"]]]) ].
Proof. reflexivity. Qed.

(* The square, discharged through the theorem rather than by computation:
   the hypotheses are checks, and this is what running them looks like. *)
Example flat_rename_square :
  link_build flat (rename flat ["a"] ["c"] flat_site)
  = map_urls (route ["a"]) (route ["c"]) (link_build flat flat_site).
Proof.
  apply (rename_correct flat ["a"] ["c"] flat_site flat_lcodec_ok).
  - intros t H. unfold subst_path.
    destruct (path_eqb t ["a"]); [reflexivity|exact H].
  - reflexivity.
  - cbn [dom map fst]. left. reflexivity.
  - intros r d t Hin Ht. cbn [In] in Hin.
    destruct Hin as [E|[E|[]]]; injection E as <- <-; cbn in Ht.
    + destruct Ht.
    + destruct Ht as [<-|[]]. cbn [dom map fst]. left. reflexivity.
Qed.

(* The obligation this file does not discharge in general, discharged
   here: the renamed site is still canonical, so it can be rendered.
   `cblocks_ok` is decidable and a build runs it -- the general theorem
   needs the two codec conditions named above and a fact about what a
   destination can do to a rendered line. *)
Example flat_rename_stays_canonical :
  forallb (fun pd => cblocks_ok (snd pd)) (rename flat ["a"] ["c"] flat_site)
  = true.
Proof. reflexivity. Qed.

(* The two shapes of new name, from `route_collide`: turning a note into
   its own directory index keeps its URL and is admissible, while a name
   that routes where another note already routes is what the freshness
   check rejects. *)
Example rename_to_own_index_admissible :
  url_eqb (route ["a"; index_name]) (route ["a"]) = true.
Proof. reflexivity. Qed.

Example rename_onto_other_note_rejected :
  existsb (url_eqb (route ["b"])) (map route (dom flat_site)) = true.
Proof. reflexivity. Qed.
