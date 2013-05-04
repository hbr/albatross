main:
	ocamlbuild -yaccflag -v main.byte


test: main
	./main.byte test.e test.epc

kernel: main
	./main.byte ../library/kernel/kernel.eml

