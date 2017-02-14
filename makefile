.PHONY: build

build:
	cd ocaml;       \
	make alba;      \
	make alba.byte

