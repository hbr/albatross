.PHONY: build

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
	dune exec -- ocaml/alba1/alba.exe compile -work-dir library/alba.base

