module type DECODER =
sig
    type _ t

    val return: 'msg -> 'msg t
    val string: string t
    val bool:   bool t
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




module type VIRTUAL_APPLICATION =
sig
    type _ decoder

    type encoder


    module Attribute:
    sig
        type 'msg t =
        | Style of string * string
        | Attribute of string * string
        | Property of string * encoder
        | On of string * 'msg decoder
    end

    module Virtual_dom:
    sig
        type 'msg t =
        | Text of string
        | Node of string * 'msg Attribute.t list * 'msg t list
    end
end




module type BROWSER =
sig
    module Decoder: DECODER

    module Encoder: ENCODER

    module Make:
    functor (Vapp: VIRTUAL_APPLICATION
                    with type 'msg decoder = 'msg Decoder.t
                    and  type encoder = Encoder.t)
    ->
    sig
        val sandbox:
            'model
            -> ('model -> 'msg Vapp.Virtual_dom.t)
            -> ('msg -> 'model -> 'model)
            -> unit
    end
end




module Make (Browser: BROWSER):
sig
    type 'msg decoder = 'msg Browser.Decoder.t

    type encoder = Browser.Encoder.t


    module Attribute:
    sig
        type 'msg t =
        | Style of string * string
        | Attribute of string * string
        | Property of string * encoder
        | On of string * 'msg decoder

        val style: string -> string -> 'msg t

        val attribute: string -> string -> 'msg t

        val property: string -> encoder -> 'msg t

        val on: string -> 'msg decoder -> 'msg t



        val string_property: string -> string -> 'msg t
        (** [string_property name value] *)

        val bool_property: string -> bool -> 'msg t
        (** [bool_property name value] *)

        val placeholder: string -> 'msg t

        val value: string -> 'msg t
        (** Value property. Used in input elements like 'input', 'textarea'. *)

        val checked: bool -> 'msg t
        (** Indicate, if a checkbox is checked. *)

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



        val onKeyDown: (string -> 'msg) -> 'msg t

        val onKeyUp: (string -> 'msg) -> 'msg t


        val onInput: (string -> 'msg) -> 'msg t
        (** React on input of an input element like 'input', 'textarea', etc. *)

        val onCheck: (bool -> 'msg) -> 'msg t
        (** React on a checkbox click. *)
    end


    module Virtual_dom:
    sig
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


        val b: 'msg attributes -> 'msg children -> 'msg t
        (** Bold text *)

        val i: 'msg attributes -> 'msg children -> 'msg t
        (** Italic text *)

        val strong: 'msg attributes -> 'msg children -> 'msg t
        (** Important text *)



        val button: 'msg attributes -> 'msg children -> 'msg t

        val input: 'msg attributes -> 'msg children -> 'msg t
    end
end
