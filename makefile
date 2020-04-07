.PHONY: build build_dune test_alba \
	doc \
	fmlib fmlib_js \
	core albalib \
	alba2 alba-node alba-web alba_web2

build:
	cd ocaml;          \
	make alba.native;  \
	make alba.d.byte;  \
	make alba.base

build_dune:
	dune build ocaml/alba2/alba2.exe; \
	dune build ocaml/alba1/alba.exe;  \
	dune build ocaml/alba1/alba.bc;   \
	dune runtest;                     \
	dune exec -- ocaml/alba1/alba.exe init    -work-dir library/alba.base; \
	dune exec -- ocaml/alba1/alba.exe compile -work-dir library/alba.base; \
	mv library/alba.base/.alba/*.json library/alba.base/alba-dir

test_alba:
	dune build ocaml/alba1/alba.exe;  \
	dune exec -- ocaml/alba1/alba.exe init    -work-dir library/alba.base; \
	dune exec -- ocaml/alba1/alba.exe compile -work-dir library/alba.base


doc:
	dune build @doc

fmlib:
	dune build @ocaml/fmlib/runtest

fmlib_js:
	dune build ocaml/fmlib/js/fmlib_js.cma

fmlib_node:
	dune build ocaml/fmlib/node/fmlib_node.cma

core: fmlib
	dune build @ocaml/core/runtest

albalib: core
	dune build @ocaml/albalib/runtest

alba2: albalib
	dune build ocaml/alba2/alba2.bc

alba-node: albalib
	dune build ocaml/alba-node/alba_node.bc.js


alba-web: albalib
	dune build ocaml/alba-web/alba_web.js

alba-web2: albalib
	dune build ocaml/alba-web/alba_web2.js
