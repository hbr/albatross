module type DECODER =
sig
    type _ t

    val return: 'msg -> 'msg t
    val string: string t
    val field:  string -> 'msg t -> 'msg t
    val map: ('a -> 'b) -> 'a t -> 'b t
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




module Vdom (Browser: BROWSER):
sig
    type 'msg decoder = 'msg Browser.Decoder.t


    module Attribute:
    sig
        type 'msg t =
        | Style of string * string
        | Attribute of string * string
        | Property of string * string
        | On of string * 'msg decoder

        val style: string -> string -> 'msg t

        val attribute: string -> string -> 'msg t

        val property: string -> string -> 'msg t

        val on: string -> 'msg decoder -> 'msg t



        val placeholder: string -> 'msg t

        val value: string -> 'msg t
        (** Value property. Used in input elements like 'input', 'textarea'. *)

        val type_: string -> 'msg t
        (** Set the type attribute of an input element. Legal values "text"
        (default), "password", "checkbox", "radio", "color", "button", "file"
        etc. *)


        val onClick: 'msg -> 'msg t

        val onDoubleClick: 'msg -> 'msg t

        val onMouseDown: 'msg -> 'msg t

        val onMouseUp: 'msg -> 'msg t

        val onMouseEnter: 'msg -> 'msg t

        val onMouseLeave: 'msg -> 'msg t

        val onMouseOver: 'msg -> 'msg t

        val onMouseOut: 'msg -> 'msg t


        val onInput: (string -> 'msg) -> 'msg t
    end



    type 'msg t =
    | Text of string
    | Node of string * 'msg Attribute.t list * 'msg t list


    type 'msg attributes = 'msg Attribute.t list
    type 'msg children   = 'msg t list

    val text: string -> 'msg t

    val node: string -> 'msg attributes -> 'msg children -> 'msg t

    val div: 'msg attributes -> 'msg children -> 'msg t

    val pre: 'msg attributes -> 'msg children -> 'msg t

    val p: 'msg attributes -> 'msg children -> 'msg t

    val h1: 'msg attributes -> 'msg children -> 'msg t

    val h2: 'msg attributes -> 'msg children -> 'msg t

    val h3: 'msg attributes -> 'msg children -> 'msg t

    val h4: 'msg attributes -> 'msg children -> 'msg t

    val h5: 'msg attributes -> 'msg children -> 'msg t

    val h6: 'msg attributes -> 'msg children -> 'msg t

    val button: 'msg attributes -> 'msg children -> 'msg t

    val input: 'msg attributes -> 'msg children -> 'msg t
end
