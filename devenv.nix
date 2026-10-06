{ pkgs, lib, ... }:

let
  # <ai> nixpkgs builds Rocq 9.1 with OCaml 4.14.  Building it with the default
  # OCaml 5 package set instead leaves Rocq and its Stdlib as the only
  # packages not in the binary cache. </ai>
  ocamlPackages = pkgs.ocamlPackages;  # default OCaml package (5.5.0)
  rocqPackages = pkgs.mkRocqPackages (
    pkgs.rocq-core_9_1.override { customOCamlPackages = ocamlPackages; }
  );  # default to OCaml 4.14 so we override it

  ocamlLibs = with ocamlPackages; [
    rocqPackages.rocq-core  # for dune's Rocq support and extraction look up
    # ocaml/
    jsont
    bytesrw
    yaml
    # site/
    brr
    js_of_ocaml-compiler
    # wasi/
    wasm_of_ocaml-compiler
  ];
  siteLib = "lib/ocaml/${ocamlPackages.ocaml.version}/site-lib";
in
{
  # the programs put on `PATH`
  packages = [
    ocamlPackages.ocaml
    ocamlPackages.dune_3
    ocamlPackages.findlib
    ocamlPackages.odoc
    ocamlPackages.js_of_ocaml-compiler
    ocamlPackages.wasm_of_ocaml-compiler
    rocqPackages.rocq-core
    pkgs.binaryen  # wasm_of_ocaml runs wasm-opt and wasm-merge
    pkgs.nodejs  # djot.js, which make diff runs
    pkgs.ghc  # the Haskell extraction
    pkgs.uv  # py/
    pkgs.gnumake
    pkgs.git  # the site states the commit it is built from
  ];

  # <ai> packages puts programs on PATH, which is not where libraries are looked
  # for.  dune and ocamlfind find OCaml libraries in the directories of
  # OCAMLPATH, and rocq finds Stdlib in those of ROCQPATH.  Each nix package
  # is a directory of its own, so OCAMLPATH lists one for every library of
  # ocamlLibs and every library these depend on, which closePropagation
  # collects.  Left unset, OCAMLPATH would hold the libraries of packages
  # alone, and ROCQPATH nothing. </ai>
  env.OCAMLPATH = lib.makeSearchPath siteLib (lib.closePropagation ocamlLibs);
  env.ROCQPATH = "${rocqPackages.stdlib}/lib/coq/${rocqPackages.rocq-core.rocq-version}/user-contrib";  # holds Rocq's `Stdlib`

  # what `devenv test` runs
  enterTest = ''
    make check-rocq
    make check-site
    make py-wasm
    make check-py
  '';
}
