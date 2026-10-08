.PHONY: help build doc build-djotjs build-haskell-extraction diff diff-shape \
        roundtrip roundtrip-kernel roundtrip-keyed roundtrip-wikilinks roundtrip-callouts roundtrip-dollar-math roundtrip-tags roundtrip-holes \
        check-span-containment bench probe-lemmas \
        ocaml-pkg-regen ocaml-pkg-check-current ocaml-pkg-split-branch \
        site site-serve site-publish py-wasm check-py check-rocq check-readme check-axioms check-versions check-site

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

roundtrip-holes: build  ## Holes
	dune exec test/roundtrip.exe -- $(VERBOSE) --holes 3

roundtrip-escapes: build  ## Escapes of the canonical renderer that the parse does not need
	dune exec test/escapes.exe -- $(VERBOSE)

# Other checks
# ------------

check-span-containment: build  ## Located parse: every span lies inside its document and parent
	dune exec test/spans.exe -- $(VERBOSE) 3

check-stack: build  ## Extracted candidate-stack scan against the specification scan, on random paragraphs
	dune exec test/stack.exe -- $(VERBOSE)

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
	@cp VERSION ocaml/kernel/VERSION
	@echo "ocaml/kernel regenerated from $(EXTRACTED)"

# Compared with runs of whitespace as one space: where the extraction
# breaks its lines depends on the OCaml that Rocq was built with.
ocaml-pkg-check-current: build  ## Fail if ocaml/kernel is behind the extraction
	@tmp=`mktemp -d`; $(call copy-extracted-modules,$$tmp); \
	for d in ocaml/kernel $$tmp; do \
	  (cd $$d && for f in *.ml *.mli; do echo "== $$f"; tr -s ' \t\n' ' ' < $$f; echo; done) > $$tmp/`basename $$d`.flat; \
	done; \
	if diff $$tmp/kernel.flat $$tmp/`basename $$tmp`.flat >/dev/null; then \
	  rm -rf $$tmp; echo "ocaml/kernel is current"; \
	else \
	  diff -r --exclude=dune --exclude='*.flat' ocaml/kernel $$tmp | head -20; rm -rf $$tmp; \
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

# site/ is a dune project of its own, which needs the ocaml/ package's
# dependencies plus brr and js_of_ocaml.  The Python API reference is built
# from py/ with uv, from the source alone: it needs no djot.wasm.
SITE = _build/site

site:  ## Build the static site into _build/site
	cd site && dune build --root . --profile release ./gen/gen.exe ./playground/playground.bc.js ./playground/worker.bc.js
	cd ocaml && dune build @doc
	cd py && uv run --group docs zensical build --strict
	rm -rf $(SITE)
	site/_build/default/gen/gen.exe site/pages theories/spec $(SITE)
	cp site/pages/theme.css site/pages/style.css site/pages/preview.css $(SITE)/
	cp site/_build/default/playground/playground.bc.js $(SITE)/playground/playground.js
	cp site/_build/default/playground/worker.bc.js $(SITE)/playground/worker.js
	cp -R ocaml/_build/default/_doc/_html $(SITE)/api/odoc
	cp -R py/_build/docs $(SITE)/api/python
	touch $(SITE)/.nojekyll

site-serve: site  ## Build the site and serve it on localhost:8000
	python3 -m http.server -d $(SITE) 8000

# Run by hand.  The site becomes a new commit on the gh-pages branch of
# origin, which GitHub Pages serves.
site-publish: site  ## Build the site and push it to the gh-pages branch of origin
	scripts/site-publish.sh $(SITE)

# Python package
# --------------

# wasi/ is a dune project of its own, which needs the ocaml/ package's
# dependencies plus wasm_of_ocaml-compiler.  DJOT_NO_YAML=1 builds ocaml/
# without yaml where it is installed: it binds C, which the module cannot
# link.  It builds the library as a WASI command, which any WASI host with
# WasmGC can run.
PY_WASM = py/src/djotv/djot.wasm

py-wasm:  ## Build the WebAssembly module of the Python package into py/src/djotv
	cd wasi && DJOT_NO_YAML=1 dune build --root . --profile release ./djot_wasi.bc.wasm.js
	cp wasi/_build/default/djot_wasi.bc.wasm.assets/code.wasm $(PY_WASM)
	chmod 644 $(PY_WASM)

check-py:  ## test the Python package against the module in py/src/djotv
	cd py && uv run pytest -q

# All local checks. Run before branch merging
# --------------------------------------------

check-rocq: build ocaml-pkg-check-current check-readme check-axioms  ## check the proofs, that ocaml/kernel is the current extraction, the README tables, and that nothing is assumed

check-readme:  ## Fail if the README's property tables differ from theories/Properties.v (dune promote updates them)
	dune build @readme

# rocqchk checks the compiled theories a second time, apart from the
# build, and lists what they assume.  The awk fails unless each of the
# four lists is there and empty.
check-axioms: build  ## Fail if a theory rests on an axiom or on a check the kernel was told to skip (~30s)
	@ls _build/default/theories/*.vo | sed 's|.*/||; s|\.vo$$||; s|^|DjotV.|' \
	  | xargs rocqchk -silent -o -R _build/default/theories DjotV 2>&1 \
	  | awk '/^\* Axioms/ { on = 1 } on && NF { print } \
	         /^\* (Axioms|Constants|Inductives)/ { n++; if ($$0 !~ /<none> *$$/) bad = 1 } \
	         END { exit bad || n != 4 }'

check-versions:  ## Fail if VERSION, its copy in ocaml/kernel, the djot submodule and the changelog disagree
	@scripts/check-versions.sh

check-site: site  ## test the ocaml/ package and build the site
	cd ocaml && dune build @runtest @install
