open Fmlib


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

    module CLP =
      Argument_parser.Make (struct type t = command_line end)

    let compile (cmd:command_line): unit IO.t =
      IO.put_line_out cmd.work_dir

    let status (_:command_line): unit IO.t =
      assert false

    let commands: (string*(command_line->unit IO.t)*string) list =
      ["compile", compile,
       "Compile the modules provided on the command line and all its \
        dependencies if compilation is required. If no modules are provided \
        all modules of the package which require compilation are compiled."
      ;
        "status", status,
        "Display all modules which require compilation or recompilation."
      ]

    let command_options: (CLP.key*CLP.spec*CLP.doc) list =
      let open CLP in
      [("-verbosity",
        Int (fun i a -> {a with verbosity = i}),
        "Verbosity level (default 1)"
       );

       ("-work-dir", String (fun s a -> {a with work_dir = s}),
        "Path to the directory where the Alba package is located (default: \
         current working directory)");

       ("-I", String (fun s a -> {a with package_paths =
                                           s :: a.package_paths}),
        "Add argument to search path for used packages");

       ("-force", Unit (fun a -> {a with force = true}),
        "Force compilation, even if it is not necessary")
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

    module Pr =
      struct
        include Pretty_printer
        let put_left (width:int) (s:string): unit t =
          let len = String.length s in
          if len < width then
            string s >> fill (width - len) ' '
          else
            string s
      end
    module R = Pr.Readable

    let print_options: unit Pr.t =
      let open Pr in
      chain
        (List.map
           (fun (key,spec,doc) ->
             chain [cut; put_left 20 (key ^ CLP.argument_type spec);
                    nest 20 @@ fill_paragraph doc])
           command_options)


    let print_commands: unit Pr.t =
      let open Pr in
      chain
        (List.map
           (fun (cmd,_,doc) ->
             chain [cut; put_left 10 cmd; nest 10 @@ fill_paragraph doc])
           commands)


    let print_usage: unit Pr.t =
      let open Pr in
      chain
        [string "Usage: alba command options arguments";
         cut; cut;
         nest 4 (string "Commands:" >> print_commands);
         cut; cut;
         nest 4 (string "Options:" >> print_options);
         cut]

    let print_error (s:string): unit IO.t =
      let module W = IO.Write(R) in
      IO.(W.write IO.stderr
            (let open Pr in
             run 0 80 80
             @@ chain [string "Error: "; string s; cut; cut; print_usage])

          >>= fun _ -> return ())


    let run (): unit =
      let module Write = IO.Write(R) in
      IO.(execute
            (command_line >>= fun args ->
             match parse args with
             | Ok cl ->
                begin
                  match cl.command with
                  | None ->
                     print_error "no commands given"
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
