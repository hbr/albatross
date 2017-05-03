.PHONY: build

build:
	cd ocaml;          \
	make alba.native;  \
	make alba.d.byte

