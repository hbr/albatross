open Js_of_ocaml
open Fmlib



type js_string = Js.js_string





(* classes for javascript dom objects *)


class type event =
object
    method stopPropagation: unit Js.meth
    method preventDefault:  unit Js.meth
end



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

    method requestAnimationFrame:
        (float -> unit) Js.callback -> unit Js.meth
end






(* Globals *)


let get_window (): window Js.t =
    Js.Unsafe.global







module Decoder =
struct
    type 'a t =
        Common.Void.t Js.t -> 'a option

    let return (a: 'a): 'a t =
        fun _ -> Some a

    let string: string t =
        fun js ->
            Printf.printf "typeof %s\n"
                (Js.to_string (Js.typeof js));
            if Js.to_string (Js.typeof js) = "string" then
                Some (
                    Printf.printf "string\n";
                    Js.to_string (Js.Unsafe.coerce js)
                )
            else
                (
                    Printf.printf "no string\n";
                    None
                )


    let field (name: string) (decode: 'a t): 'a t =
        fun obj ->
            Printf.printf "field %s\n" name;
            Option.(
                Js.Opt.to_option (Js.Unsafe.get obj (Js.string name))
                >>=
                decode
            )


    let map (f: 'a -> 'b) (decode: 'a t): 'b t =
        fun obj -> Option.( map f (decode obj) )
end







module Make (Vdom: Html2.VDOM with type 'a decoder = 'a Decoder.t) =
struct
    type ('model,'msg) t = {
        window:   window Js.t;
        view:     'model -> 'msg Vdom.t;
        update:   'msg -> 'model -> 'model;
        mutable model: 'model;
        mutable dirty: bool;
    }


    let make
        (model: 'model)
        (view: 'model -> 'msg Vdom.t)
        (update: 'msg -> 'model -> 'model)
        : ('model,'msg) t
        =
        {   window = get_window ();
            view;
            update;
            model;
            dirty = false;
        }


    let add_attribute
        (attr: 'msg Vdom.Attribute.t)
        (node: node Js.t)
        (state: ('model, 'msg) t)
        : unit
        =
        let open Vdom.Attribute in
        match attr with
        | Style (name, value) ->
            Js.Unsafe.set node##.style (Js.string name) (Js.string value)

        | Attribute (name, value) ->
            node##setAttribute (Js.string name) (Js.string value)

        | Property (name, value) ->
            Js.Unsafe.set node (Js.string name) (Js.string value)

        | On (name, decode) ->
            node##addEventListener
                (Js.string name)
                (Js.wrap_callback
                    (fun event ->
                        Printf.printf "event <%s> occurred\n" name;
                        (
                            match decode event with
                            | None ->
                                Printf.printf "cannot decode\n"
                            | Some message ->
                                (
                                    state.dirty <- true;
                                    state.model <-
                                        state.update message state.model
                                )
                        )
                    )
                )


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
        (html: 'msg Vdom.t)
        (state: ('model, 'msg) t)
        : node Js.t
        =
        let open Vdom in
        let doc = state.window##.document in
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
                            add_attribute attr node state;
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


    let update_html (state: ('model, 'msg) t): unit =
        Printf.printf "update_html\n";
        let node = state.window##.document##.body in
        remove_children node;
        node##appendChild
            (make_html (state.view state.model) state);
        state.dirty <- false



    let rec animate (state: ('model, 'msg) t) (_: 'a): unit =
        if state.dirty then
            update_html state
        else
            ();
        state.window##requestAnimationFrame
            (Js.wrap_callback (animate state))




    let sandbox
        (model: 'model)
        (view: 'model -> 'msg Vdom.t)
        (update: 'msg -> 'model -> 'model)
        : unit
        =
        Printf.printf "start sandbox\n";
        let state = make model view update in
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
                        (Js.string "?chapter=compile#6");
                    let body = document##.body in
                    remove_children body;
                    body##appendChild
                        (make_html (view model) state);
                    state.window##requestAnimationFrame
                        (Js.wrap_callback (animate state))
                )
            )
end
