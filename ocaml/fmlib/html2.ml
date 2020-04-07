module type DECODER =
sig
    type _ t

    val return: 'msg -> 'msg t
    val string: string t
    val field:  string -> 'msg t -> 'msg t
end


module type VDOM =
sig
    type _ decoder


    module Attribute:
    sig
        type 'msg t =
        | Style of string * string
        | Attribute of string * string
        | Property of string * string
        | On of string * 'msg decoder
    end


    type 'msg t =
    | Text of string
    | Node of string * 'msg Attribute.t list * 'msg t list
end


module type BROWSER =
sig
    module Decoder: DECODER

    module Make:
    functor (Vdom: VDOM with type 'msg decoder = 'msg Decoder.t) ->
    sig
        val sandbox:
            'model
            -> ('model -> 'msg Vdom.t)
            -> ('msg -> 'model -> 'model)
            -> unit
    end
end


module Vdom (Browser: BROWSER) =
struct
    type 'msg decoder = 'msg Browser.Decoder.t


    module Attribute =
    struct
        type 'msg t =
        | Style of string * string
        | Attribute of string * string
        | Property of string * string
        | On of string * 'msg decoder

        let style (name: string) (value: string): 'msg t =
            Style (name, value)


        let attribute (name: string) (value: string): 'msg t =
            Attribute (name, value)


        let property (name: string) (value: string): 'msg t =
            Property (name, value)

        let on (name: string) (handler: 'msg decoder): 'msg t =
            On (name, handler)
    end




    type 'msg t =
    | Text of string
    | Node of string * 'msg Attribute.t list * 'msg t list


    type 'msg attributes = 'msg Attribute.t list
    type 'msg children   = 'msg t list


    let text (s: string): 'msg t =
        Text s


    let node
        (tag: string)
        (attrs: 'msg attributes)
        (children: 'msg children)
        : 'msg t
        =
        Node (tag, attrs, children)


    let div (attrs: 'msg attributes) (children: 'msg children): 'msg t =
        node "div" attrs children


    let input (attrs: 'msg attributes) (children: 'msg children): 'msg t =
        node "input" attrs children
end

