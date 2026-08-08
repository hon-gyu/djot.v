.PHONY: build test shape baseline oracles clean

build:
	dune build

# full differential run: gallina vs djot.js vs djoths over the corpus
test: build
	dune exec harness/main.exe

# block structure only: inline content dropped, so a container bug is
# visible while inline parsing is still Phase 3
shape: build
	dune exec harness/main.exe -- --shape

# oracle-vs-oracle (and vs expected output); seeds the disagreement log
baseline: build
	dune exec harness/main.exe -- --baseline --verbose \
	  --report .project/baseline-report.txt

oracles:
	cd djot.js && npm install --no-audit --no-fund && npm run build
	cd djoths && cabal build exe:djoths

clean:
	dune clean
