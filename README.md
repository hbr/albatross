# General

This repository holds the sources for the Albatross compiler.

The language Albatross allows static verification (i.e. correctness proofs) of
programs.

The albatross compiler is a proof assistant and a compiler for the Albatross
language.


# Documentation

[Language Description](http://www.gitbook.com/book/hbr/alba-lang-description)


# Installation

Prerequisites:

- ocaml: In order to compile the Albatross compiler you need the `OCaml`
  compiler. The OCaml compiler is available at no cost through
  [caml.inria.fr](http://caml.inria.fr) and installs easily on a variety of
  platforms.

- ocamlbuild: Beside the ocaml compiler the program `ocamlbuild` is
  needed. The ocaml compiler versions below 4.03 already contain the program
  `ocamlbuild`. From version 4.03 on `ocamlbuild` is no longer part of the
  compiler suite and has to be installed separately. If you have opam just
  type `opam install ocamlbuild`.

- yojson: Library to process json files. Installation with opam `opam install
  yojson`.


Compile the Albatross compiler with the commands:

    cd path/to/albatross/ocaml

    ocamlbuild -use-ocamlfind -lib unix alba.native


After these commands you have the file `alba.native` in the directory
`albatross/ocaml/_build` which is the executable albatross compiler. Copy (or
link) it under the name `alba` to any location which is in the search path for
programs.

The basic libary is in `path/to/albatross/library/alba.base`. In order to use
it you have to compile it.

    cd path/to/albatross/library/alba.base

    alba init

    alba compile

Set the environment variable `ALBA_LIB_PATH` to `path/to/albatross/library`
(e.g. in the bash shell `export ALBA_LIB_PATH=/path/to/albatross/library`)
and the compiler will find the libraries automatically.

For the emacs editor there is an albatross mode which does syntax
highlighting. The file `albatross-mode.el` can be found in the directory
`path/to/albatross/misc`. The file contains instructions to activate the mode
in emacs.






<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
