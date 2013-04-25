main:
	ocamlbuild -yaccflag -v main.byte


test: main
	./main.byte test.e

kernel: main
	./main.byte ../library/kernel/kernel.eml

