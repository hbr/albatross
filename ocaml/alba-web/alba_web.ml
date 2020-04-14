open Fmlib


module Browser = Fmlib_js.Browser

module App = Web_application.Make (Browser)

module Vdom = App.Dom

module Attribute = App.Attribute

module Command = App.Command


module Program = Browser.Make (App)


type show =
    | Output
    | Error
    | Info


type model = {
    expression: string;
    result: string;
    error: string;
    info: string;
    show: show;
}


type message =
    | Typecheck
    | Evaluate
    | Show of show
    | Update_expression of string
    | Update_info of string




let init (url: string): model * message Command.t =
    { expression = ""
    ; result = ""
    ; error = "error ?"
    ; info = ""
    ; show = Output
    },
    Command.http_get
        url
        (function
            | Ok response ->
                Update_info response
            | Error code ->
                Update_info ("Error: " ^ string_of_int code))



let update (msg: message) (model: model): model * 'message Command.t =
    match msg with
    | Typecheck ->
        {model with
            result = "typecheck: " ^ model.expression ;
            show   = Output},
        Command.None

    | Evaluate ->
        {model with
            result = "evaluate: " ^ model.expression ;
            show   = Output},
        Command.None

    | Show show ->
        {model with show}, Command.None

    | Update_expression expression ->
        {model with expression}, Command.None

    | Update_info info ->
        {model with info}, Command.None




let menu_item
    (show: show)
    (my_show: show)
    (str: string)
    : message Vdom.t
    =
    let open Vdom in
    let open Attribute in
    if show = my_show then
        li [ class_ "menu-item"
           ; onClick (Show my_show)
           ; style "background-color" "lightgrey"]
           [text str]
    else
        li [ class_ "menu-item"
           ; onClick (Show my_show)
           ]
           [text str]


let output (model: model): message Vdom.t =
    let open Vdom in
    let open Attribute in
    let class_attr, str =
        match model.show with
        | Output ->
            "output-result", model.result
        | Error ->
            "output-error" , model.error
        | Info ->
            "output-info"  , model.info
    in
    pre [class_ class_attr] [text str]




let view (model: model): message Vdom.t =
    let open Vdom in
    let open Attribute in
    div []
        [ h2 [] [ text "Alba Expression Compiler"]
        ; span  [ class_ "main-block" ]
                [ div []
                      [ button [onClick Typecheck] [text "Typecheck"]
                      ; button [onClick Evaluate]  [text "Evaluate"]
                      ]
                ; div []
                      [textarea [ class_ "editor-area"
                                ; placeholder "enter expression ..."
                                ; onInput (fun str -> Update_expression str)
                                (*; attribute "rows" "50"
                                ; attribute "cols" "80"*)
                                ]
                                []
                      ]
                ]
        ; span  [ class_ "main-block" ]
                [ ul [ class_ "menu" ]
                     [ menu_item model.show Output "Output"
                     ; menu_item model.show Error "Error"
                     ; menu_item model.show Info "Info"
                     ]
                ; output model
                ]
        ]



let subscription (_: 'model): 'msg App.Subscription.t =
    App.Subscription.None



let _ =
    Program.element
        Browser.Decoder.string
        init
        view
        update
        subscription
