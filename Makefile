.PHONY: build doc build-doc test shape baseline generated roundtrip located-bounds deep probe keyed wiki oracles dist check-dist copy-extracted clean

build:
	dune build

# Reader-facing Rocqdoc site.  Use Dune's copied sources so the adjacent
# globalization files provide cross-module identifier links.
doc: build
	rm -rf _build/doc
	mkdir -p _build/doc
	rocq doc --html --toc --utf8 --gallina --index rocq-index \
	  -R _build/default/theories DjotV \
	  -d _build/doc \
	  _build/default/theories/*.v
	cp _build/doc/DjotV.Overview.html _build/doc/index.html

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

# every span the located parse records lies inside its document and
# inside its parent, over the generated corpus and the file corpus.
# Exits nonzero on a failure.  It found one when it landed: a spec
# spanning a line break left the run before it starting on the wrong
# line.
located-bounds: build
	dune exec harness/main.exe -- --located-bounds 3

# `parse (render d) = d` over every canonical document the enumerator
# accepts, in the extracted parser.  Depth 3 in ~5 seconds; this is the
# one to run.
#
# It replaces `make deep`, which checked the same statement in the Rocq
# kernel and took ~20 minutes to do it.  What that cost bought was the
# kernel certifying the computation -- and nothing depends on the result:
# `gen_roundtrip_3` is an `Example`, not a lemma, and every other number
# this project acts on already comes out of the same extraction.  Depths
# 1 and 2 are still certified, by `Generate.gen_roundtrip_1` and
# `gen_roundtrip_2`, which run on every build.
#
# Run it when `cb_ok`, the enumeration, `Render.v` or the block parser
# changes.  An inline change reaches it only through `escape_str`, and
# that is exercised at depth 1 -- what the depth buys is *nesting*, so
# the trigger is behaviour that varies with how deep a container sits:
# columns, offsets, container prefixes, `pad_state`.
roundtrip: build
	dune exec harness/main.exe -- --roundtrip 3

# The same sweep in the kernel, kept for when certification is wanted
# rather than an answer: ~20 minutes, and `make roundtrip` is the routine
# check.  It also pins `accepted_counts`, which `--roundtrip` pins too.
deep: build
	rocq c -R _build/default/theories DjotV dev/check/Deep.v
	@rm -f dev/check/Deep.vo dev/check/Deep.vok dev/check/Deep.vos dev/check/Deep.glob \
	       dev/check/.Deep.aux

# the keyed-block construct, pinned as whole documents against
# `keyed_bconfig`.  Out of the dune build for dev/check/Markdown.v's reason:
# `vm_compute` over documents is not something a parser edit should pay
# for.  Run it when key recognition, transitions, or canonical rendering
# change.  The extracted sweep covers keyed children and containers.
keyed: build
	rocq c -R _build/default/theories DjotV dev/check/Keyed.v
	@rm -f dev/check/Keyed.vo dev/check/Keyed.vok dev/check/Keyed.vos dev/check/Keyed.glob \
	       dev/check/.Keyed.aux
	dune exec harness/main.exe -- --keyed-roundtrip 1

# The wikilink pool: the ordinary one read with wikilinks on, plus each
# wikilink leaf in the containers.  No oracle has the construct, so the
# pinned count is what shows the pool still reaches it.
wiki: build
	dune exec harness/main.exe -- --wiki-roundtrip 2

# falsify a candidate lemma before proving it: add a `Compute` to
# dev/check/Probe.v and run this.  ~0.5s.  Out of the dune build because
# dev/check/Probe.v matches on every `pstate` constructor, so a parser edit
# should break `make probe` and not `dune build`.  The combinators live
# in dev/Probe.v, which is Stdlib-only and does build.
probe: build
	rocq c -R _build/default/theories DjotV \
	  -R _build/default/dev DjotVDev dev/check/Probe.v
	@rm -f dev/check/Probe.vo dev/check/Probe.vok dev/check/Probe.vos dev/check/Probe.glob \
	       dev/check/.Probe.aux

EXTRACTED = _build/default/extraction

# `dist/` is the extracted parser as a standalone dune project, committed
# so that a consumer builds it without Rocq.  The main build ignores the
# directory (`data_only_dirs`); build it with `cd dist && dune build`.
dist: build
	@$(MAKE) -s copy-extracted DEST=dist/src
	@echo "dist/src regenerated from $(EXTRACTED)"

# Fails when dist/src is behind the theories.  
check-dist: build
	@tmp=`mktemp -d`; $(MAKE) -s copy-extracted DEST=$$tmp; \
	if diff -r --exclude=dune dist/src $$tmp >/dev/null; then \
	  rm -rf $$tmp; echo "dist/src is current"; \
	else \
	  diff -r --exclude=dune dist/src $$tmp | head -20; rm -rf $$tmp; \
	  echo "dist/src is stale: run make dist"; exit 1; \
	fi

# The parser, without the fixtures the harness links alongside it.
copy-extracted:
	@mkdir -p $(DEST)
	@rm -f $(DEST)/*.ml $(DEST)/*.mli
	@for f in $(EXTRACTED)/*.ml $(EXTRACTED)/*.mli; do \
	  case `basename $$f` in Fixtures.*|Generate.*) ;; *) install -m 644 $$f $(DEST)/ ;; esac; \
	done

oracles:
	cd djot.js && npm install --no-audit --no-fund && npm run build
	cd djoths && cabal build exe:djoths

clean:
	dune clean
