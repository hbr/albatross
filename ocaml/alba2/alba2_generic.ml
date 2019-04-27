open Fmlib
open Common


module Make (IO:Io.S) =
  struct
    type command_line = {
        command: string option;
        work_dir: string;
        package_paths: string list;
        verbosity: int;
        force: bool;
        arguments: string list (* reversed *)
      }

    module PP =
      Pretty_printer.Make (IO)

    module CLP =
      Argument_parser.Make (struct type t = command_line end)

    let compile (cmd:command_line): unit IO.t =
      IO.put_line_out cmd.work_dir

    let status (cmd:command_line): unit IO.t =
      assert false

    let commands: (string*(command_line->unit IO.t)*string list) list =
      ["compile", compile,
       ["Compile the modules provided on the command line and";
        "all its dependencies if compilation is required.";
        "If no modules are provided all modules of the package";
        "which require compilation are compiled."
       ];
       "status", status,
       ["Display all modules which require compilation or recompilation."]
      ]

    let command_options: (CLP.key*CLP.spec*CLP.doc) list =
      let open CLP in
      [("-verbosity",
        Int (fun i a -> {a with verbosity = i}),
        ["Verbosity level (default 1)"]
       );

       ("-work-dir", String (fun s a -> {a with work_dir = s}),
        ["Path to the directory where the Alba package is located";
         "(default: current working directory)"]);

       ("-I", String (fun s a -> {a with package_paths =
                                           s :: a.package_paths}),
        ["Add argument to search path for used packages"]);

       ("-force", Unit (fun a -> {a with force = true}),
        ["Force compilation, even if it is not necessary"])
      ]

    let parse (args:string array): (command_line,CLP.error) result =
      let open CLP in
      parse
        args
        {command = None;
         work_dir = "";
         package_paths = [];
         verbosity = 1;
         force = false;
         arguments = []}
        command_options
        (fun s a ->
          match a.command with
          | None ->
             {a with command = Some s}
          | Some _ ->
             {a with arguments = s :: a.arguments})

    let print_options (p:PP.t): PP.t IO.t =
      let open PP in
      let rec print l p =
        match l with
        | [] ->
           IO.make p
        | (key,spec,doc) :: tl ->
           cut p
           >>= put_left 20 (key ^ CLP.argument_type spec)
           >>= hovbox 0 (put_wrapped doc)
           >>= print tl
      in
      print command_options p

    let print_commands (p:PP.t): PP.t IO.t =
      let open PP in
      let rec print l p =
        match l with
        | [] ->
           IO.make p
        | (cmd,_,lst) :: tl ->
           cut p >>= put_left 10 cmd
           >>= hovbox 0 (put_wrapped lst)
           >>= print tl
      in
      print commands p

    let print_usage (p:PP.t): PP.t IO.t =
      let open PP in
      put "Usage: alba command options arguments" p
      >>= cut >>= cut
      >>= vbox 4 (chain [put "Commands:"; print_commands])
      >>= cut >>= cut
      >>= vbox 4 (chain [put "Options:"; print_options])
      >>= cut

    let print_error (s:string): unit IO.t =
      let open PP in
      make 80 IO.stderr
      >>= vbox 0 (chain [put "Error: "; put s; cut; cut; print_usage])
      >>= stop

    let run (): unit =
      IO.(execute
            (command_line >>= fun args ->
             match parse args with
             | Ok cl ->
                begin
                  let open PP in
                  match cl.command with
                  | None ->
                     print_error "no command given"
                  | Some cmd ->
                     match
                       List.find (fun (c,_,_) -> c = cmd) commands
                     with
                     | None ->
                        print_error ("Unknown command '" ^ cmd ^ "'")
                     | Some (_,f,_) ->
                        f cl
                end
             | Error e ->
                print_error (CLP.string_of_error e) >>= fun _ -> exit 1
            )
      )
  end
