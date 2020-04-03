open Js_of_ocaml
open Fmlib



type js_string = Js.js_string





(* classes for javascript dom objects *)


class type eventTarget =
object
    method addEventListener:
        js_string Js.t -> ('a Js.t -> unit) Js.callback -> unit Js.meth
        (* Do not use on text nodes! *)

    method removeEventListener:
        js_string Js.t -> ('a Js.t -> unit) Js.callback -> unit Js.meth
        (* Do not use on text nodes! *)
end



class type node =
object
    inherit eventTarget

    method nodeType: int Js.readonly_prop

    method parentNode:  node Js.t Js.Opt.t Js.readonly_prop


    (* The following methods can be used only on elements *)

    method firstChild:  node Js.t Js.Opt.t Js.readonly_prop

    method lastChild:   node Js.t Js.Opt.t Js.readonly_prop

    method nextSibling: node Js.t Js.Opt.t Js.readonly_prop

    method style: 'a Js.t Js.readonly_prop

    method setAttribute: js_string Js.t -> js_string Js.t -> unit Js.meth

    method appendChild: node Js.t -> unit Js.meth

    method removeChild: node Js.t -> unit Js.meth

    method replaceChild: node Js.t -> unit Js.meth
end





class type document =
object
    inherit eventTarget

    method body: node Js.t Js.readonly_prop

    method _URL: js_string Js.t Js.readonly_prop

    method title: js_string Js.t Js.prop

    method createElement:  js_string Js.t -> node Js.t Js.meth

    method createTextNode: js_string Js.t -> node Js.t Js.meth

    method getElementById: js_string Js.t -> node Js.Opt.t Js.meth
end






class type history =
object
    method pushState:
        'a Js.t Js.Opt.t -> js_string Js.t -> js_string Js.t -> unit Js.meth
        (* [pushState state title path] [title] is currently not used, [path]
        must not change origin. *)
end


class type window =
object
    inherit eventTarget

    method history: history Js.t Js.readonly_prop

    method document: document Js.t Js.readonly_prop
end






(* Globals *)


let get_window (): window Js.t =
    Js.Unsafe.global








module Io =
struct
    module Js_object =
    struct
        type t = Js.Unsafe.any

        let int (_: t): int option =
            assert false

        let field (_: string) (_: t): t option =
            assert false

        let of_int (_: int): t =
            assert false

        let object_of_list (_: t list): t =
            assert false

        let of_list (_: t list): t =
            assert false

        let of_array (_: t array): t =
            assert false
    end

    module Html2 = Html.Make (Js_object)


    type ('model,'msg) t = {
        window:   window Js.t;
        view:     'model -> 'msg Html.t;
        mutable model: 'model;
    }



    let make (model: 'a) (view: 'model -> 'msg Html.t): ('model,'msg) t =
        {   window = get_window ();
            model;
            view
        }


    let add_attribute
        (attr: 'msg Html.Attribute.t)
        (node: node Js.t)
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

        | Handler (_, _) ->
            () (* nyi *)


    let remove_children (node: node Js.t): unit =
        let rec remove () =
            match Js.Opt.to_option node##.firstChild with
            | None ->
                ()
            | Some child ->
                node##removeChild child;
                remove ()
        in
        remove ()



    let make_html
        (html: 'msg Html.t)
        (doc: document Js.t)
        : node Js.t
        =
        let open Html in
        let rec make html =
            match html with
            | Text text ->
                doc##createTextNode (Js.string text)

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
                        node##appendChild (make child);
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
        let state = make model view in
        state.window##addEventListener
            (Js.string "load")
            (Js.wrap_callback
                (fun _ ->
                    Printf.printf "load\n";
                    let document = state.window##.document in
                    document##.title := Js.string "my-test-app";
                    state.window##.history##pushState
                        Js.null
                        (Js.string "")
                        (Js.string "?chapter=compile#5");
                    let body = document##.body in
                    remove_children body;
                    body##appendChild
                        (make_html (view model) document)
                )
            )


end (* Io *)
