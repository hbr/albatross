open Fmlib
open Js_of_ocaml

let window: Dom_html.window Js.t = Js.Unsafe.global

let document: Dom_html.document Js.t = window##.document

module Io =
struct
    module Js_object =
    struct
        type t = Js.Unsafe.any

        let int (_: t): int option =
            assert false

        let field (_: string) (_: t): t option =
            assert false
    end

    module Html2 = Html.Make (Js_object)


    type ('model,'msg) t = {
        model:    'model;
        view:     'model -> 'msg Html.t;
    }

    let make (model: 'a) (view: 'model -> 'msg Html.t): ('model,'msg) t =
        { model; view }


    let remove_children (node: Dom_html.element Js.t): unit =
        let rec remove () =
            match Js.Opt.to_option (node##.firstChild) with
            | None ->
                ()
            | Some child ->
                Dom.removeChild node child;
                remove ()
        in
        remove ()



    let add_attribute
        (attr: 'msg Html.Attribute.t)
        (node: Dom_html.element Js.t)
        : unit
        =
        let open Html.Attribute in
        match attr with
        | Style (name, value) ->
            Js.Unsafe.set node##.style (Js.string name) (Js.string value)

        | Attribute (name, value) ->
            node##setAttribute (Js.string name) (Js.string value)

        | Property (name, value) ->
            Js.Unsafe.set node (Js.string name) (Js.string value)

        | Handler (name, _) ->
            let _ = (* id *)
                Dom_html.addEventListener
                    node
                    (Dom_html.Event.make name)
                    (Dom_html.handler
                        (fun _ ->
                            Printf.printf "event <%s>\n" name;
                            Js._false
                        )
                    )
                    Js._false
            in
            ()



    let make_html
        (html: 'msg Html.t)
        (doc: Dom_html.document Js.t)
        : Dom_html.element Js.t
        =
        let open Html in
        let rec make html =
            match html with
            | Text text ->
                (
                    Js.Unsafe.coerce (doc##createTextNode (Js.string text))
                    : Dom_html.element Js.t
                )
            | Node (tag, attributes, children) ->
                let node =
                    doc##createElement (Js.string tag)
                in
                let node =
                    List.fold_left
                        (fun node attr ->
                            add_attribute attr node;
                            node)
                        node
                        attributes
                in
                List.fold_left
                    (fun node child ->
                        Dom.appendChild node (make child);
                        node
                    )
                    node
                    children
        in
        make html


    let sandbox
        (model: 'model)
        (view: 'model -> 'msg Html.t)
        (_: 'msg -> 'model -> 'model)
        : unit
        =
        window##.onload :=
            Dom_html.handler
                (fun _ ->
                    let _ = make model view in (* state *)
                    Printf.printf "%s\n" (Js.to_string document##._URL);
                    remove_children (document##.body);
                    Dom.appendChild
                        document##.body
                        (make_html (view model) document);
                    Js._false
                )
end
