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

From Stdlib Require Import String List Bool.
From DjotV Require Import Render.
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
