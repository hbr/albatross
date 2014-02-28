boolean:
	ocamlbuild eiffelc.byte -- ../library/kernel/boolean.e

boolean1:
	ocamlbuild eiffelc.byte -- boolean1.e

any:
	ocamlbuild eiffelc.byte -- ../library/kernel/any.e

main:
	ocamlbuild -yaccflag -v main.byte


test: main
	./main.byte test.e test.epc

kernel: main
	./main.byte ../library/kernel/kernel.eml

clean:
	ocamlbuild -clean
