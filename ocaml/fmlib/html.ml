module Attribute =
struct
    type 'a t =
    | Style of string * string
    | Attribute of string * string
    | Property of string * string  (* nyi: arbitrary properties, only string
                                      properties *)
      (*| Property of string * Js.Unsafe.any (* Must be an encoded js value *)*)


    let style (name: string) (value: string): 'a t =
        Style (name, value)


    let attribute (name: string) (value: string): 'a t =
        Attribute (name, value)


    let property (name: string) (value: string): 'a t =
        Property (name, value)
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


let div: 'a node_function = node "div"


let textarea: 'a node_function =
    node "textarea"


let pre: 'a node_function =
    node "pre"


let button: 'a node_function =
    node "button"
