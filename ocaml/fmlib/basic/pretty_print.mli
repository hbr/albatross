(** Pretty Printer: Generate nicely formatted ascii text. *)

(** {1 Overview} *)

(** {2 Example}

    The usage of the pretty printer is best explained by an example. Suppose
    we want to print the function application [f a b (g c d) e] where the
    function names and arguments might have different length. We create a {i
    document} which represents the structure by

    {[
    let doc =
        group (
            text "f" <+> space <+>
            indent
                2
                (stack_or_pack
                    " "
                    [text "a";
                     text "b";
                     group (
                         text "(g" <+> space <+>
                         indent
                            2
                            (stack_or_pack " " [text "c"; text "d"])
                         <+> text ")");
                     text "e"])
        )
    ]}

    where [text "blabla"] is a document with some unbreakable text, [<+>]
    concatenates two documents, [space] is a break hint whose alternative text
    is a blank, [stack_or_pack atxt [...]] stacks a list of documents separated
    by a break hint with the alternative text [atxt].

    The command

    {[let stream = layout 5 doc ]}

    creates a stream of characters which is nicely formatted using a desired
    line width of 5 characters. Since 5 characters are not enough to put any of
    the subterms completely on a line, the output is

    {[
    123456789012345
    f
      a
      b
      (g
        c
        d)
      d
    ]}

    i.e. each break hint is printed as a newline.

    If we give the pretty printer a line width of 10, it could pack the
    application [g c d] on a line and print

    {[
    123456789012345
    f
      a
      b
      (g c d)
      d
    ]}

    If the pretty printer has enough line width e.g. a line width of 15, it can
    put the whole expression on a line.

    {[
    123456789012345
    f a b (g c d) d
    ]}

    By using [stack_or_pack] we instructed the pretty printer to either print
    all break hints as newlines or all break hints with their alternative texts.
    If we use [pack] instead of [stack_or_pack], the pretty printer tries to
    pack as many arguments as possible on a line.

    E.g. with a line width of 11 and using [pack] instead of [stack_or_pack] we
    get the output

    {[
    123456789012345
    f
      a b
      (g c d) d
    ]}

    With a line width of 10 and using [pack] we get

    {[
    123456789012345
    f
      a b
      (g c d)
      d
    ]}

    because the pretty printer cannot pack [(g c d)] and [d] on a single line.

*)

(** {2 Character Stream}

    The basic type [t] of the pretty printer is a lazy character stream. I.e.
    characters are only generated if needed. The pretty printer implements the
    interface {!Module_types.READABLE} to represent a character stream. You can
    ask the stream [has_more r] whether there are more characters in the stream
    and [peek r] to get the next character. The instruction [advance r] returns
    the stream [r] advanced by one character position.

    The pretty printer has a function [string_of r] to return a string
    representation of the character stream.

    However you very rarely need a string representation of a character stream.
    All io function in {!Fmlib} are able to handle character streams.


 *)





(** {1 Generate Documents}

    Clearly, it is tedious to write documents by hand. Usually you have some
    tree like structure and you want to generate a document from the tree
    structure.

    Let's assume you have a tree structure like

    {[
    type tree =
        { name: string; children: tree list; }

    let leaf (name: string): tree =
        {name; children = [] }

    let tree (name: string) (children: tree list): tree =
        {name; children}
    ]}

    Write a function which converts the tree structure to a document.

    {[
    let doc_of_tree (tree: tree): doc =
        let rec doc is_top tree =
            match tree.children with
            | [] ->
                text tree.name
            | _ ->
                let d =
                    text tree.name <+> space
                    <+>
                    nest
                        2
                        (stack_or_pack
                             " "
                             (List.map (doc false) tree.children))
                    |> group
                in
                if is_top then
                    d
                else
                    char '(' <+> d <+> char ')'
        in
        doc true tree
    ]}

    Then the simple command

    {[
    tree
        "f"
        [leaf "a";
         leaf "b";
         tree "g" [leaf "c"; leaf "d"];
         leaf "e"]
    |> layout 10
    ]}

    generates the character stream

    {[
    123456789012345
    f
      a
      b
      (g c d)
      e
    ]}
*)


(** {1 API}*)

(** A readable character stream. *)
type t

(** [has_more r] Does the stream [r] have more characters to read? *)
val has_more: t -> bool

(** [peek r] The next character in the stream [r]. *)
val peek: t -> char

(** [advance r] The character stream [r] advance by one position. *)
val advance: t -> t

(** [string_of r] A string representation of the stream [r]. *)
val string_of: t -> string


(** A document. *)
type doc

(** [layout width doc] Layout the document [doc] with a the line [width]. *)
val layout: int -> doc -> t


(** [layout width ribbon doc] Layout the document [doc] with a the line [width]
    and the [ribbon] width. Note: [width] is the complete line width and
    [ribbon] is the line width minus the indentation of the current line. *)
val layout_with_ribbon: int -> int -> doc -> t


(** An empty document. *)
val empty: doc


(** [text str] A document with the unbreakable string [str]. *)
val text: string -> doc


(** [substring str start length] A document with the unbreakable string [str]
    starting at position [start] and having [length]. *)
val substring: string -> int -> int -> doc


(** [char c] A document with the character [c]. *)
val char: char -> doc


(** [fill n c] A document with [n] repetitions of the character [c]. *)
val fill: int -> char -> doc


(** [break str] A break hint with the alternative text [str]. *)
val break: string -> doc


(** [space] A break hint with a blank as alternative text. *)
val space: doc


(** [cut] A break hint with an empty alternative text. *)
val cut: doc


(** [nest n doc] The document [doc] indented by [n] blanks. *)
val nest: int -> doc -> doc


(** [with_width n doc] Format the document [doc] with line [width].*)
val with_width: int -> doc -> doc


(** [with_ribbon n doc] Format the document [doc] with [ribbon] width.*)
val with_ribbon: int -> doc -> doc


(** [group doc] Treat all break hints belonging directly to [doc] consistently.
    Either print all as newlines or print all with their alternative text. *)
val group: doc -> doc


(** [doc1 <+> doc2] Concatentate the documents [doc1] and [doc2]. *)
val (<+>): doc -> doc -> doc


(** [doc >> lazy_doc] Concatenate the document [doc] with the lazy document
    [lazy_doc]. *)
val (>>): doc -> (unit -> doc) -> doc



(** [cat list] Concatenate all documents in the [list] of documents. *)
val cat: doc list -> doc


(** [separated_by sep list] Concatenate all documents in the [list] of documents
    separated by [sep]. *)
val separated_by: doc -> doc list -> doc


(** [pack str list] Pack as much documents of the [list] of documents as possible
    into a line. I.e. separate all documents by a break hint with [str] as an
    alternative text. *)
val pack: string -> doc list -> doc


(** [stack str list] The same as [separated_by (break str) list]. *)
val stack: string -> doc list -> doc

(** [stack_or_pack str list]
    Separated all documents of the [list] by a break hint with alternative text
    [str] and either print all break hints as newlines of with the alternative
    text [str]. *)
val stack_or_pack: string -> doc list -> doc

(** [wrap_words str]
    Split the string [str] into words (words are substrings of [str] not
    containing blanks) and pack as many of them onto a line. *)
val wrap_words: string -> doc
