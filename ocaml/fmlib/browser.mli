module type IO =
sig
    val sandbox:
        'model -> ('model -> 'a Html.t) -> ('a -> 'model -> 'model) -> unit
    (** [sandbox model view update] *)
end
