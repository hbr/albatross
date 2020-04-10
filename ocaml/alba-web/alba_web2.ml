open Fmlib


module Browser = Fmlib_js.Browser


module Vdom = Html2.Vdom (Browser)

type entry = {
    description: string;
    completed: bool;
}


type model = {
    task: string;
    entries: entry list;
}



type message =
    | Update_task of string
    | Add_task




let model: model =
    {
        task = "bla";
        entries = [
            {description = "task 1"; completed = false }
        ];
    }



let update (msg: message) (model: model): model =
    match msg with
    | Update_task task ->
        {model with task}

    | Add_task ->
        assert false



let view_entry (e: entry): message Vdom.t =
    let open Vdom in
    let open Attribute in
    p []
      [ input [type_ "checkbox"] []
      ; text e.description
      ; input [type_ "button"; value "x"] []
      ]


let view (model: model): message Vdom.t =
    let open Vdom in
    let open Attribute in
    div []
        (
            h1 [] [text "todo"]
            ::
            p []
              [input [ placeholder "new task"
                     ; value model.task
                     ; onInput (fun task -> Update_task task)
                     ]
                     []
              ]
            ::
            List.map view_entry model.entries
        )



let _ =
    let module Program = Browser.Make (Vdom) in
    Program.sandbox model view update
