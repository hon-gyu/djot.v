.PHONY: help build doc build-djotjs diff diff-shape \
        roundtrip roundtrip-kernel roundtrip-keyed roundtrip-wikilinks \
        check-spans probe-lemmas dist check-dist copy-parser

# Inputs the harness runs over:
#   test suite     djot.js/test/*.test, the cases with expected HTML
#   generated      canonical documents enumerated by dev/Generate.v
# V=1 on any harness recipe prints each mismatch.
HARNESS = dune exec harness/main.exe -- $(if $(V),--verbose)

help:  ## Show this help
	@echo "Usage: make [recipe]"
	@echo "Recipes:"
	@awk '/^[a-zA-Z0-9_.-]+:.*?##/ { \
		helpMessage = match($$0, /## (.*)/); \
		if (helpMessage) { \
			recipe = $$1; \
			sub(/:/, "", recipe); \
			printf "  \033[36m%-20s\033[0m %s\n", recipe, substr($$0, RSTART + 3, RLENGTH); \
		} \
	}' $(MAKEFILE_LIST)

build:  ## Build the Rocq development and harness
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

# Differential runs
# -----------------

diff: build  ## Parser vs expected HTML on the test suite, then vs djot.js on generated
	$(HARNESS)
	$(HARNESS) --generated

diff-shape: build  ## As diff on the test suite, comparing block structure only
	$(HARNESS) --shape

# Roundtrip: parse (render d) = d
# -------------------------------

# Depths 1 and 2 are kernel-checked on every build (Generate.gen_roundtrip_1/2).
roundtrip: build  ## Extracted parser, generated documents to depth 3 (~5s)
	$(HARNESS) --roundtrip 3

roundtrip-kernel: build  ## Same as roundtrip, checked in the Rocq kernel (~20min)
	rocq c -R _build/default/theories DjotV \
	  -R _build/default/dev DjotVDev dev/check/Deep.v
	@rm -f dev/check/Deep.vo dev/check/Deep.vok dev/check/Deep.vos dev/check/Deep.glob \
	       dev/check/.Deep.aux

roundtrip-keyed: build  ## Keyed-block extension (keyed_bconfig)
	$(HARNESS) --keyed-roundtrip 1

roundtrip-wikilinks: build  ## Wikilink extension
	$(HARNESS) --wiki-roundtrip 2

# Other checks
# ------------

check-spans: build  ## Located parse: every span lies inside its document and parent
	$(HARNESS) --located-bounds 3

# Kept out of dune build so that a new pstate constructor breaks this
# recipe rather than the build.  See dev/check/Probe.v.
probe-lemmas: build  ## Search for counterexamples to candidate lemmas in dev/check/Probe.v
	rocq c -R _build/default/theories DjotV \
	  -R _build/default/dev DjotVDev dev/check/Probe.v
	@rm -f dev/check/Probe.vo dev/check/Probe.vok dev/check/Probe.vos dev/check/Probe.glob \
	       dev/check/.Probe.aux

# Extracted parser package
# ------------------------

EXTRACTED = _build/default/extraction

# dist/ is committed so consumers build it without Rocq (cd dist && dune build).
dist: build  ## Regenerate dist/src from the extraction
	@$(MAKE) -s copy-parser DEST=dist/src
	@echo "dist/src regenerated from $(EXTRACTED)"

check-dist: build  ## Fail if dist/src is behind the extraction
	@tmp=`mktemp -d`; $(MAKE) -s copy-parser DEST=$$tmp; \
	if diff -r --exclude=dune dist/src $$tmp >/dev/null; then \
	  rm -rf $$tmp; echo "dist/src is current"; \
	else \
	  diff -r --exclude=dune dist/src $$tmp | head -20; rm -rf $$tmp; \
	  echo "dist/src is stale: run make dist"; exit 1; \
	fi

# Helper for dist and check-dist: copy the extracted modules, minus the
# harness-only Fixtures and Generate, into directory DEST.
copy-parser:
	@mkdir -p $(DEST)
	@rm -f $(DEST)/*.ml $(DEST)/*.mli
	@for f in $(EXTRACTED)/*.ml $(EXTRACTED)/*.mli; do \
	  case `basename $$f` in Fixtures.*|Generate.*) ;; *) install -m 644 $$f $(DEST)/ ;; esac; \
	done
