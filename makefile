.PHONY: build

build:
	cd ocaml;          \
	make alba.native;  \
	make alba.d.byte;  \
	make alba.base

build_dune:
	dune build ocaml/alba.exe;   \
	dune build ocaml/alba.bc;   \
	dune exec -- ocaml/alba.exe init    -work-dir library/alba.base; \
	dune exec -- ocaml/alba.exe compile -work-dir library/alba.base

