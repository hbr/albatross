.PHONY: alba.base                  \
	alba                       \
	test                       \
        test2                      \
        test2_library              \
        test2_draft                \
        test2_example              \
        test2_sf                   \
        alba.byte                  \
        alba.d.byte                \
        alba.native                \
        alba.p.native              \
        alba_node.byte             \
        boolean                    \
        predicate                  \
        tuple                      \
        predicate_logic            \
        function_logic             \
        lattice                    \
        partial_order              \
        endorelation


alba: alba.native


alba.byte:
	ocamlbuild \
            -use-ocamlfind \
            -yaccflags --explain,--dump,--infer,--fixed-exception \
            -lib unix \
	    alba.byte

alba.d.byte:
	ocamlbuild \
            -use-ocamlfind \
            -yaccflags --explain,--dump,--infer,--fixed-exception \
            -lib unix \
	    alba.d.byte

alba.native:
	ocamlbuild \
            -use-ocamlfind \
            -yaccflags --explain,--dump,--infer,--fixed-exception \
            -lib unix \
            alba.native

alba.p.native:
	ocamlbuild \
            -use-ocamlfind \
            -yaccflags --explain,--dump,--infer,--fixed-exception \
            -lib unix \
            alba.p.native


alba-node: alba_node.byte
	js_of_ocaml \
	    --custom-header='#!/usr/bin/env node' \
	    --pretty       \
            -o alba-node   \
	    alba_node.byte;\
        chmod u+x alba-node

alba_node.byte:
	ocamlbuild -use-ocamlfind             \
	-pkgs js_of_ocaml,js_of_ocaml.syntax  \
	-syntax camlp4o                       \
	alba_node.byte

alba.base: alba.native
	./alba.native -work-dir ../library/alba.base init;  \
	./alba.native -work-dir ../library/alba.base compile

doc:
	ocamlbuild eiffelc.docdir/index.html

test2: alba.byte test2_library test2_draft test2_example


test2_library: alba.byte
	./alba.byte -work-dir ../library/alba.base compile -force -verbosity 1

test2_draft: alba.byte
	./alba.byte -I ../library -work-dir ../_draft compile -force -verbosity 1

test2_example: alba.byte
	./alba.byte -I ../library -work-dir ../example compile -force -verbosity 1

test2_sf: alba.byte
	./alba.byte -I ../library -work-dir ../../sf compile -force -verbosity 1

test: alba test_library test_draft test_example

test_library: alba
	./alba.native -work-dir ../library/alba.base compile -force -verbosity 1

test_draft: alba
	./alba.native -I ../library -work-dir ../_draft compile -force -verbosity 1

test_example: alba
	./alba.native -I ../library -work-dir ../example compile -force -verbosity 1

boolean: alba.byte
	./alba.byte -work-dir ../library/alba.base  \
         compile -force -verbosity 3 boolean 1>&2

any: alba.byte
	./alba.byte -work-dir ../library/alba.base  \
         compile -force -verbosity 3 any 1>&2

boolean_logic: alba.byte
	./alba.byte -work-dir ../library/alba.base  \
         compile -force -verbosity 3 boolean_logic 1>&2

predicate: alba.byte
	./alba.byte -work-dir ../library/alba.base  \
         compile -force -verbosity 3 predicate 1>&2


tuple: alba.byte
	./alba.byte -work-dir ../library/alba.base  \
         compile -force -verbosity 3 tuple 1>&2


predicate_logic: alba.byte
	./alba.byte -work-dir ../library/alba.base  \
         compile -force -verbosity 3 predicate_logic 1>&2


function_logic: alba.byte
	./alba.byte -work-dir ../library/alba.base  \
         compile -force -verbosity 3 function_logic 1>&2


relation: alba.byte
	./alba.byte -work-dir ../library/alba.base  \
         compile -force -verbosity 3 relation 1>&2


lattice: alba.byte
	./alba.byte -work-dir ../library/alba.base  \
         compile -force -verbosity 3 lattice 1>&2

semilattice: alba.byte
	./alba.byte -work-dir ../library/alba.base  \
         compile -force -verbosity 3 semilattice 1>&2

complete_semilattice: alba.byte
	./alba.byte -work-dir ../library/alba.base  \
         compile -force -verbosity 3 complete_semilattice 1>&2

partial_order: alba.byte
	./alba.byte -work-dir ../library/alba.base  \
         compile -force -verbosity 3 partial_order 1>&2

endorelation: alba.byte
	./alba.byte -work-dir ../library/alba.base  \
         compile -force -verbosity 3 endorelation 1>&2

function: alba.byte
	./alba.byte -work-dir ../library/alba.base  \
         compile -force -verbosity 3 function 1>&2

linear_order: alba.byte
	./alba.byte -work-dir ../library/alba.base  \
         compile -force -verbosity 3 linear_order 1>&2

wellorder: alba.byte
	./alba.byte -work-dir ../library/alba.base  \
         compile -force -verbosity 3 wellorder 1>&2

natural: alba.byte
	./alba.byte -work-dir ../library/alba.base  \
         compile -force -verbosity 3 natural 1>&2

list: alba.byte
	./alba.byte -work-dir ../library/alba.base  \
         compile -force -verbosity 3 list 1>&2

binary_tree: alba.byte
	./alba.byte -work-dir ../library/alba.base  \
         compile -force -verbosity 3 binary_tree 1>&2

tree: alba.byte
	./alba.byte -work-dir ../_draft  \
         compile -force -verbosity 3 tree 1>&2




# to compile for debugging use '-cflag -g -lflag -g




clean:
	ocamlbuild -clean
