.PHONY: build test shape baseline generated deep probe oracles clean

build:
	dune build

# full differential run: gallina vs djot.js vs djoths over the corpus,
# then over the enumerated corpus (fast: djot.js is batched, one process)
test: build
	dune exec harness/main.exe
	dune exec harness/main.exe -- --generated --engines gallina,djotjs

# block structure only: inline content dropped, so a container bug is
# visible while inline parsing is still Phase 3
shape: build
	dune exec harness/main.exe -- --shape

# oracle-vs-oracle (and vs expected output); seeds the disagreement log
baseline: build
	dune exec harness/main.exe -- --baseline --verbose \
	  --report baseline-report.txt

# the enumerated cblock fragment against both oracles, with diffs.  Slower
# than the `test` run because djoths takes one process per document; it is
# here because adjudicating a diff needs the second opinion.
generated: build
	dune exec harness/main.exe -- --generated --verbose \
	  --report generated-report.txt

# the depth-3 enumeration (check/Deep.v), which dune does not build: it
# is ~10 minutes, and it sits downstream of the parser, so leaving it in
# the default build made every parser edit cost that.
#
# It asserts `parse (render d) = d` over canonical documents, so the test
# for needing it is not "did the parser change" but "can this change
# alter parse on *canonical output*".  Two consequences worth keeping in
# mind, both of which have saved a run:
#   - theories/Html.v is not in its cone at all (it imports Ast, Parser,
#     Render, Generate), so an HTML-only change never needs it;
#   - a new scanner mode reachable only through a byte sequence that
#     `needs_escape` prevents canonical rendering from emitting is
#     invisible to it.  Spans are the worked example: `IClosed` is only
#     ever followed by `(` or `[` in canonical output, never `{`.
# So: run it when cb_ok, the enumeration, Render.v or the block parser
# changes, and when an inline change is reachable from canonical source.
deep: build
	rocq c -R _build/default/theories DjotV check/Deep.v
	@rm -f check/Deep.vo check/Deep.vok check/Deep.vos check/Deep.glob \
	       check/.Deep.aux

# falsify a candidate lemma before proving it: add a `Compute` to
# check/Probe.v and run this.  ~0.5s.  Out of the dune build because
# check/Probe.v matches on every `pstate` constructor, so a parser edit
# should break `make probe` and not `dune build`.  The combinators live
# in theories/Probe.v, which is Stdlib-only and does build.
probe: build
	rocq c -R _build/default/theories DjotV check/Probe.v
	@rm -f check/Probe.vo check/Probe.vok check/Probe.vos check/Probe.glob \
	       check/.Probe.aux

oracles:
	cd djot.js && npm install --no-audit --no-fund && npm run build
	cd djoths && cabal build exe:djoths

clean:
	dune clean
