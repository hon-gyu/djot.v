#!/bin/sh
# ai-disclosure: ai-generated

# The Haskell extraction (extraction/haskell), built into _build/haskell
# with strings as String and as ByteString.
#
#   scripts/haskell.sh build   _build/haskell/djotv-string and
#                              _build/haskell/djotv-bytestring
#   scripts/haskell.sh diff    both variants against the test suite and
#                              the generated documents, as `make diff`
#   scripts/haskell.sh bench   wall time of both variants, the OCaml
#                              extraction, djoths and djot.js (~2min)
#
# Run from the repository root.  Needs ghc on PATH; bench also needs
# cabal, to build the djoths submodule.

set -eu

out=_build/haskell

build() {
  dune build
  mkdir -p "$out/string/src" "$out/bytestring/src"
  rm -f "$out"/*/src/*.hs
  rocq c -R _build/default/theories DjotV -noglob \
    -o "$out/Haskell.vo" extraction/haskell/Haskell.v
  for v in string bytestring; do
    # Extraction cannot emit imports.
    perl -0pi -e 's/^import qualified Prelude\n/import qualified Prelude\nimport qualified Data.Bits\nimport qualified Data.Char\nimport qualified Data.ByteString.Char8\n/m' \
      "$out/$v/src/"*.hs
    flag=
    [ "$v" = bytestring ] && flag=-DBYTESTRING
    ghc -O2 -w -package bytestring $flag -i"$out/$v/src" \
      -outputdir "$out/$v/obj" -o "$out/djotv-$v" extraction/haskell/Main.hs
  done
}

case "${1:-}" in
  build)
    build ;;
  diff)
    build
    for v in string bytestring; do
      dune exec test/diff.exe -- --subject "$PWD/$out/djotv-$v"
      dune exec test/diff.exe -- --subject "$PWD/$out/djotv-$v" --generated
    done ;;
  bench)
    build
    (cd djoths && cabal build exe:djoths --enable-optimization=2)
    djoths=$(cd djoths && cabal list-bin exe:djoths --enable-optimization=2)
    dune exec test/compare.exe -- \
      "ocaml=$PWD/_build/default/test/convert.exe" \
      "hs-string=$PWD/$out/djotv-string" \
      "hs-bytestring=$PWD/$out/djotv-bytestring" \
      "djoths=$djoths" \
      "djotjs=node $PWD/test/djotjs/djotjs.mjs" ;;
  *)
    echo "usage: scripts/haskell.sh build|diff|bench" >&2
    exit 2 ;;
esac
