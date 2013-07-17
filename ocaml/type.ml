type 'a tree =
    Tree of 'a * 'a tree list

type typ =
    int tree

type class_descriptor =
    {constraints: typ list; parents: typ list}

type class_context =
    class_descriptor array

type type_context =
    typ array
