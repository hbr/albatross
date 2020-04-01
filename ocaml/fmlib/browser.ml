module type IO =
sig
    module Js_object: Html.JS

    val sandbox:
        'model -> ('model -> 'a Html.t) -> ('a -> 'model -> 'model) -> unit
end
