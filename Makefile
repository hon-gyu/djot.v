.PHONY: help build doc build-djotjs build-haskell-extraction diff diff-shape \
        roundtrip roundtrip-kernel roundtrip-keyed roundtrip-wikilinks roundtrip-callouts roundtrip-dollar-math roundtrip-tags \
        check-span-containment bench probe-lemmas \
        ocaml-pkg-regen ocaml-pkg-check-current ocaml-pkg-split-branch \
        site site-serve

# Inputs the test/ executables run over:
#   test suite     djot.js/test/*.test, the cases with expected HTML
#   generated      canonical documents enumerated by dev/Generate.v
# V=1 on any test/ recipe prints each mismatch.
VERBOSE = $(if $(V),--verbose)

help:  ## Show this help
	@echo "Usage: make [recipe]"
	@echo "Recipes:"
	@awk '/^[a-zA-Z0-9_.-]+:.*?##/ { \
		helpMessage = match($$0, /## (.*)/); \
		if (helpMessage) { \
			recipe = $$1; \
			sub(/:/, "", recipe); \
			printf "  \033[36m%-24s\033[0m %s\n", recipe, substr($$0, RSTART + 3, RLENGTH); \
		} \
	}' $(MAKEFILE_LIST)

build:  ## Build the Rocq development and test/
	dune build

# Built from Dune's copies so the .glob files resolve cross-module links.
doc: build  ## Generate the Rocqdoc HTML site
	rm -rf _build/doc
	mkdir -p _build/doc
	rocq doc --html --toc --utf8 --gallina --index rocq-index \
	  -R _build/default/theories DjotV \
	  -d _build/doc \
	  _build/default/theories/*.v
	cp _build/doc/toc.html _build/doc/index.html

build-djotjs:  ## Build the djot.js submodule
	cd djot.js && npm install --no-audit --no-fund && npm run build

build-haskell-extraction:  ## Build the Haskell extraction into _build/haskell (needs ghc)
	scripts/haskell.sh build

# Differential runs
# -----------------

diff: build  ## Parser vs expected HTML on the test suite, then vs djot.js on generated
	dune exec test/diff.exe -- $(VERBOSE)
	dune exec test/diff.exe -- $(VERBOSE) --generated
	dune exec test/diff.exe -- $(VERBOSE) --lazy

diff-shape: build  ## As diff on the test suite, comparing block structure only
	dune exec test/diff.exe -- $(VERBOSE) --shape

# Roundtrip: parse (render d) = d
# -------------------------------

# Depths 1 and 2 are kernel-checked on every build (Generate.gen_roundtrip_1/2).
roundtrip: build  ## Extracted parser, generated documents to depth 3 (~20s)
	dune exec test/roundtrip.exe -- $(VERBOSE) 3

roundtrip-kernel: build  ## Same as roundtrip, checked in the Rocq kernel (~20min)
	rocq c -R _build/default/theories DjotV \
	  -R _build/default/dev DjotVDev dev/check/Deep.v
	@rm -f dev/check/Deep.vo dev/check/Deep.vok dev/check/Deep.vos dev/check/Deep.glob \
	       dev/check/.Deep.aux

roundtrip-keyed: build  ## Keyed-block extension (keyed_bconfig)
	dune exec test/roundtrip.exe -- $(VERBOSE) --keyed 1

roundtrip-wikilinks: build  ## Wikilink extension
	dune exec test/roundtrip.exe -- $(VERBOSE) --wiki 2

roundtrip-callouts: build  ## Callout extension
	dune exec test/roundtrip.exe -- $(VERBOSE) --callouts 3

roundtrip-dollar-math: build  ## Dollar math extension
	dune exec test/roundtrip.exe -- $(VERBOSE) --dollar 3

roundtrip-tags: build  ## Custom tag names
	dune exec test/roundtrip.exe -- $(VERBOSE) --tags 3

# Other checks
# ------------

check-span-containment: build  ## Located parse: every span lies inside its document and parent
	dune exec test/spans.exe -- $(VERBOSE) 3

bench: build  ## Scaling benchmark: parse and convert time on generated shapes (~1min)
	dune exec test/bench.exe -- $(SHAPES)

# Kept out of dune build so that a new pstate constructor breaks this
# recipe rather than the build.  See dev/check/Probe.v.
probe-lemmas: build  ## Search for counterexamples to candidate lemmas in dev/check/Probe.v
	rocq c -R _build/default/theories DjotV \
	  -R _build/default/dev DjotVDev dev/check/Probe.v
	@rm -f dev/check/Probe.vo dev/check/Probe.vok dev/check/Probe.vos dev/check/Probe.glob \
	       dev/check/.Probe.aux

# Extracted parser package
# ------------------------

EXTRACTED = _build/default/extraction/ocaml

# Copy the extracted modules, minus the test-only Fixtures and Generate,
# into directory $(1).
define copy-extracted-modules
mkdir -p $(1) && rm -f $(1)/*.ml $(1)/*.mli && \
for f in $(EXTRACTED)/*.ml $(EXTRACTED)/*.mli; do \
  case $${f##*/} in Fixtures.*|Generate.*) ;; \
    *) sed 's/[[:blank:]]*$$//' "$$f" > "$(1)/$${f##*/}"; \
       chmod 644 "$(1)/$${f##*/}" ;; esac; \
done
endef

ocaml-pkg-regen: build  ## Regenerate ocaml/kernel from the extraction and promtote to worktree
	@$(call copy-extracted-modules,ocaml/kernel)
	@echo "ocaml/kernel regenerated from $(EXTRACTED)"

ocaml-pkg-check-current: build  ## Fail if ocaml/kernel is behind the extraction
	@tmp=`mktemp -d`; $(call copy-extracted-modules,$$tmp); \
	if diff -r --exclude=dune ocaml/kernel $$tmp >/dev/null; then \
	  rm -rf $$tmp; echo "ocaml/kernel is current"; \
	else \
	  diff -r --exclude=dune ocaml/kernel $$tmp | head -20; rm -rf $$tmp; \
	  echo "ocaml/kernel is stale: run make ocaml-pkg-regen"; exit 1; \
	fi

# The ocaml branch holds ocaml/ at its root, for consumers that vendor the
# package as a git submodule.
# do `git push origin ocaml` to update the remote branch.
ocaml-pkg-split-branch:  ## Update the ocaml branch from ocaml/ at HEAD
	@git subtree split --prefix=ocaml --branch=ocaml -q >/dev/null
	@echo "local ocaml branch:  `git rev-parse --short refs/heads/ocaml`"
	@echo "origin/ocaml (as of last fetch): `git rev-parse --short -q --verify refs/remotes/origin/ocaml || echo none`"

# Site
# ----

# site/ is a dune project of its own, built with the switch that has the
# ocaml/ package's dependencies plus brr and js_of_ocaml.
SITE = _build/site

site:  ## Build the static site into _build/site
	cd site && dune build --root . --profile release ./gen/gen.exe ./playground/playground.bc.js ./playground/worker.bc.js
	cd ocaml && dune build @doc
	rm -rf $(SITE)
	site/_build/default/gen/gen.exe site/pages $(SITE)
	cp site/pages/theme.css site/pages/style.css site/pages/preview.css $(SITE)/
	cp site/_build/default/playground/playground.bc.js $(SITE)/playground/playground.js
	cp site/_build/default/playground/worker.bc.js $(SITE)/playground/worker.js
	cp -R ocaml/_build/default/_doc/_html $(SITE)/api/odoc
	touch $(SITE)/.nojekyll

site-serve: site  ## Build the site and serve it on localhost:8000
	python3 -m http.server -d $(SITE) 8000
