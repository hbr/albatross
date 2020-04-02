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



module Make (Js: JS) =
struct
    module Decoder =
    struct
        type 'a t = Js.t -> 'a option

        let return (a: 'a): 'a t =
            fun _ -> Some a

        let int: int t =
            Js.int

        let field (name: string) (d: 'a t): 'a t =
            fun js ->
                Option.( Js.field name js >>= d)

        let run (js: Js.t) (d: 'a t): 'a option =
            d js
    end



    module Handler =
    struct
        type 'msg t =
        | Normal of 'msg Decoder.t
    end


    module Attribute =
    struct
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


    let text (s: string): 'a t =
        Text (s)


    let node
        (s: string)
        (alist: 'a Attribute.t list)
        (children: 'a t list)
        : 'a t =
        Node (s, alist, children)


    let div attrs children =
        node "div" attrs children


    let textarea attrs children =
        node "textarea" attrs children


    let pre attrs children =
        node "pre" attrs children


    let button attrs children =
        node "button" attrs children
end






module Handler =
struct
    type 'a t =
    | Normal of 'a
end



module Attribute =
struct
    type 'a t =
    | Style of string * string
    | Attribute of string * string
    | Property of string * string  (* Up to new only string properties. *)
      (*| Property of string * Js.Unsafe.any (* Must be an encoded js value *)*)
    | Handler of string * 'a Handler.t


    let style (name: string) (value: string): 'a t =
        Style (name, value)


    let attribute (name: string) (value: string): 'a t =
        Attribute (name, value)


    let property (name: string) (value: string): 'a t =
        Property (name, value)

    let on (name: string) (handler: 'a Handler.t): 'a t =
        Handler (name, handler)
end




type 'a t =
| Text of string
| Node of string * 'a Attribute.t list * 'a t list


type 'a node_function =
    'a Attribute.t list -> 'a t list -> 'a t


let text (s: string): 'a t =
    Text (s)


let node
    (s: string)
    (alist: 'a Attribute.t list)
    (children: 'a t list)
    : 'a t =
    Node (s, alist, children)


let div attrs children =
    node "div" attrs children


let textarea attrs children =
    node "textarea" attrs children


let pre attrs children =
    node "pre" attrs children


let button attrs children =
    node "button" attrs children
