module type DECODER =
sig
    type _ t

    val return: 'msg -> 'msg t
    val string: string t
    val field:  string -> 'msg t -> 'msg t
    val map: ('a -> 'b) -> 'a t -> 'b t
end



module type ENCODER =
sig
    type t

    val string: string -> t
    val bool:   bool -> t
    val object_: (string * t) list -> t
end




module type VDOM =
sig
    type _ decoder

    type encoder


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

    module Encoder: ENCODER

    module Make:
    functor (Vdom: VDOM with type 'msg decoder = 'msg Decoder.t
                        and  type encoder = Encoder.t)
    ->
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
    module Decoder = Browser.Decoder
    module Encoder = Browser.Encoder

    type 'msg decoder = 'msg Decoder.t

    type encoder = Encoder.t


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



        let placeholder (value: string): 'msg t =
            attribute "placeholder" value

        let value (value: string): 'msg t =
            property "value" value

        let type_ (value: string): 'msg t =
            attribute "type" value


        let onClick (msg: 'msg): 'msg t =
            on "click" (Decoder.return msg)

        let onDoubleClick (msg: 'msg): 'msg t =
            on "doubleclick" (Decoder.return msg)

        let onMouseDown (msg: 'msg): 'msg t =
            on "mousedown" (Decoder.return msg)

        let onMouseUp (msg: 'msg): 'msg t =
            on "mouseup" (Decoder.return msg)

        let onMouseEnter (msg: 'msg): 'msg t =
            on "mouseenter" (Decoder.return msg)

        let onMouseLeave (msg: 'msg): 'msg t =
            on "mouseleave" (Decoder.return msg)

        let onMouseOver (msg: 'msg): 'msg t =
            on "mouseover" (Decoder.return msg)

        let onMouseOut (msg: 'msg): 'msg t =
            on "mouseout" (Decoder.return msg)


        let onInput (f: string -> 'msg): 'msg t =
            on
                "input"
                Decoder.(
                    field
                        "target"
                        (map
                            f
                            (field "value" string)))
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


    let pre (attrs: 'msg attributes) (children: 'msg children): 'msg t =
        node "pre" attrs children


    let p (attrs: 'msg attributes) (children: 'msg children): 'msg t =
        node "p" attrs children


    let h1 (attrs: 'msg attributes) (children: 'msg children): 'msg t =
        node "h1" attrs children


    let h2 (attrs: 'msg attributes) (children: 'msg children): 'msg t =
        node "h2" attrs children


    let h3 (attrs: 'msg attributes) (children: 'msg children): 'msg t =
        node "h3" attrs children


    let h4 (attrs: 'msg attributes) (children: 'msg children): 'msg t =
        node "h4" attrs children


    let h5 (attrs: 'msg attributes) (children: 'msg children): 'msg t =
        node "h5" attrs children


    let h6 (attrs: 'msg attributes) (children: 'msg children): 'msg t =
        node "h6" attrs children


    let button (attrs: 'msg attributes) (children: 'msg children): 'msg t =
        node "button" attrs children


    let input (attrs: 'msg attributes) (children: 'msg children): 'msg t =
        node "input" attrs children
end

