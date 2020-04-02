module type JS =
sig
    type t
    val int: t -> int option
    val field: string -> t -> t option

    val of_int:   int -> t
    val object_of_list: t list -> t
    val of_array: t array -> t
    val of_list:  t list -> t
end



module Make (Js: JS):
sig
    module Decoder:
    sig
        type 'a t

        val return: 'a -> 'a t
        val int: int t
        val field: string -> 'a t -> 'a t
        val run: Js.t -> 'a t -> 'a option
    end

    module Handler:
    sig
        type 'msg t =
        | Normal of 'msg Decoder.t
    end

    module Attribute:
    sig
        type 'msg t =
        | Style of string * string
        | Attribute of string * string
        | Property of string * string (* up to now: only string properties. *)
        | Handler of string * 'msg Handler.t
    end

    type 'msg t =
    | Text of string
    | Node of string * 'msg Attribute.t list * 'msg t list


    type 'msg attributes = 'msg Attribute.t list
    type 'msg children   = 'msg t list

    val text: string -> 'msg t

    val node: string -> 'msg attributes -> 'msg children -> 'msg t

    val div: 'msg attributes -> 'msg children -> 'msg t

    val textarea: 'msg attributes -> 'msg children -> 'msg t

    val pre: 'msg attributes -> 'msg children -> 'msg t

    val button: 'msg attributes -> 'msg children -> 'msg t
end





module Handler:
sig
    type 'a t =
    | Normal of 'a (* Very primitive implementation. Normally a handler needs a
                      decoder which is able to transform the event object (a
                      javascript object) into a value of type ['a]. *)
end


module Attribute:
sig
    type 'a t =
    | Style of string * string
    | Attribute of string * string
    | Property  of string * string  (* Up to new only string properties. *)
    | Handler of string * 'a Handler.t


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

    val on: string -> 'a Handler.t -> 'a t
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
