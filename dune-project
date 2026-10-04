(lang dune 3.20)
(name djot)
(generate_opam_files true)

(source (github hon-gyu/djot.v))
(authors "hongyu")
(maintainers "hongyu <linerwang1997@gmail.com>")
(license "MIT AND ISC")

(package
 (name djot)
 (synopsis "A djot parser extracted from a Rocq development")
 (description
  "A djot parser and HTML renderer extracted to OCaml from djot.v, a djot
parser written and verified in Rocq. The goals behind djot's design are
proved as theorems about the parser: no backtracking, container
uniformity, local interpretation of links, and safe hard-wrapping of
paragraphs. The extracted modules are the djot.kernel library. The
Djot module is an API over them whose module types are modeled on
cmarkit's."))
