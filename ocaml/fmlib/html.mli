module Attribute:
sig
    type _ t =
    | Style of string * string
    | Attribute of string * string
    | Property  of string * string  (* nyi: arbitrary properties, only string
                                       properties *)


    val style: string -> string -> 'a t
    (**
        [style name value]

    Examples:
    {[
        style "backgroundColor" "red"
        style "height" "90px"
        style "width" "100%"
    ]}
    *)

    val attribute: string -> string -> 'a t
    (** [attribute name value]. E.g. [attribute "for" "button"] *)

    val property: string -> string -> 'a t
end


type 'a t =
| Text of string
| Node of string * 'a Attribute.t list * 'a t list

type 'a node_function =
    'a Attribute.t list -> 'a t list -> 'a t


val text: string -> 'a t

val node: string -> 'a node_function

val div: 'a node_function

val textarea: 'a node_function

val pre: 'a node_function

val button: 'a node_function
