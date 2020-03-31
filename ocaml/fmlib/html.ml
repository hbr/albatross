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
