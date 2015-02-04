# General

This repository holds the sources for the Albatross compiler.

The language Albatross allows static verification (i.e. correctness proofs) of
programs.

The albatross compiler is a proof assistant and a compiler for the Albatross
language.



# Installation

Prerequisites: In order to compile the Albatross compiler you need the `OCaml`
compiler. The OCaml compiler is available at no cost through
[caml.inria.fr](http://caml.inria.fr) and installs easily on a variety of
platforms.

    cd path/to/albatross/ocaml

    ocamlbuild -lib unix alba.native


Now you have the file `alba.native` in the directory `albatross/ocaml/_build`
which is the executable albatross compiler. Copy (or link) it under the name
`alba` to any location which is in the search path for programs.

The basic libary is in `albatross/library/alba.base`. In order to use it you
have to compile it.

    cd path/to/albatross/library/alba.base

    alba init

    alba compile

A minimal version of the basic library is in
`albatross/library/alba.base.minimal`. You can compile it in the same manner
as the basic library.

If you set the environment variable `ALBA_LIB_PATH` to
`path/to/albatross/library` (e.g. in the bash shell `export
ALBA_LIB_PATH=/path/to/albatross/library`) then the compiler will find the
libraries automatically.






<!---
Local Variables:
mode: outline
coding: iso-latin-1
outline-regexp: "#+"
End:
-->
