# djot

A djot parser extracted from the Rocq development in
[djot.v](https://github.com/hon-gyu/djot.v).  The roundtrip and
well-formedness properties it satisfies are proved there; this directory
carries only the OCaml the extraction produces, so building it needs no
Rocq installation.

```ocaml
let html = Djot.Html.convert "# hi\n\n*strong* and [a](b)\n"
```

`Djot.Html.convert : string -> string` is the intended entry point.  The
deeper modules mirror the Coq ones and are usable, but they speak the
extracted representation: numbers are the unary `Djot.Datatypes.nat`.

`src/` is generated.  Change `theories/` upstream and run `make dist`;
edits made here are overwritten.
