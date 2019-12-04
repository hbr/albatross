open Fmlib
open Common

module Parser = Parser_lang

module Position = Character_parser.Position










module Pretty_make (Io:Io.SIG) =
  struct
    module Position = Character_parser.Position
    module Located = Character_parser.Located
    module Expression = Parser.Expression
    module Out = Fmlib.Io.Output (Io)
    module PP =  Pretty_printer.Pretty (Out)
    include PP

    let put_left (width:int) (s:string): t =
      let len = String.length s in
      if len < width then
        chain [string s; fill (width - len) ' ']
      else
        string s

    let print_list (l:'a list) (f:'a -> t): t =
      List.fold_right
        (fun a pr ->
          pr <+> f a)
        l
        empty

    let indented_paragraph (p:t): t =
      cut <+> nest 4 p <+> cut


    let indented_paragraphs (lst: t list): t =
      indented_paragraph (chain lst)

    let chain_separated (lst:t list) (sep:t): t =
      let rec chn = function
        | [] ->
           empty
        | [p] ->
           p
        | p :: tl ->
           p <+> sep <+> chn tl
      in
      chn lst


    let paragraphs (lst:t list): t =
      chain_separated lst cut




    let expression (e:Expression.t): t =
      (* print expression [e]. *)
      let rec exp e =
        let open Expression in
        match Located.value e with
        | Identifier str | Number str ->
           string str

        | Char i ->
           char '\'' <+> char (Char.chr i) <+> char '\''

        | String str ->
           char '"' <+> string str <+> char '"'

        | Operator op ->
           let str, _ = op in
           chain [char '(';
                  string str;
                  char ')']

        | Parenthesized e ->
           chain [char '(';
                  exp e;
                  char ')']

        | Binary (e1, op, e2) ->
           chain [char '(';
                  exp e1;
                  char ' ';
                  string
                    (let str, _  = Located.value op in str);
                  char ' ';
                  exp e2;
                  char ')']
        | Function (args,exp) ->
           assert false
      in
      chain [string "expression";
             cut;
             nest 4 (exp e);
             cut;cut]



    let error_header
          (error_type:string)
        : t
      =
      (* Print the error header. *)
      let err = " ERROR " in
      let nfill =
        max 0 (80 - 3 - (String.length error_type + String.length err))
      in
      chain [fill 2 '-';
             char ' ';
             string error_type;
             string err;
             fill nfill '-';
             cut;
             cut]


    let print_source
          (source:string)
          (start_line:int)
          (err_line:int)
          (err_col: int)
          (mark_len: int)
        : t =
      (* Print snippet of the erronous source code with line numbers and error
         marker. *)
      assert (0 <= start_line);
      assert (start_line <= err_line);
      assert (0 <= err_col);
      assert (0 <= mark_len);
      let err_line_str = string_of_int (err_line + 1) in
      let number_width = String.length err_line_str
      in
      let line_no i =
        let line_str = string_of_int (i + 1) in
        chain
          [fill
             (number_width - String.length line_str)
             ' ';
           string line_str;
           string "| "]
      in
      let rec lines offset line =
        if err_line < line || String.length source < offset then
          empty
        else
          let pos = String.find (fun c -> c = '\n') offset source in
          chain
            [line_no line;
             substring source offset (pos - offset);
             (if line = err_line then
                string
                  (if pos = String.length source then
                     "<end>"
                   else
                     " ...")
              else
                empty);
             cut;
             lines (pos + 1) (line + 1)]
      in
      chain [lines 0 0;
             fill (number_width + 2 + err_col) ' ';
             fill mark_len '^';
             cut;
             cut]


    let one_error_explanation (err:Parser.Dead_end.t): t =
      let source_text op1 op2 =
        chain [string "_ ";
               string op1;
               string " _ ";
               string op2;
               string " _"]
      and left op1 op2 =
        chain [string "( _ ";
               string op1;
               string " _ ) ";
               string op2;
               string " _"]
      and right op1 op2 =
        chain [string "_ ";
               string op1;
               string " ( _ ";
               string op2;
               string " _ )"]
      in
      match Parser.Dead_end.message err with
      | Parser.Problem.Expect str ->
         chain [char '<'; string str; char '>']

      | Parser.Problem.Operator_precedence (op1, op2) ->
         paragraphs
           [string "to be able to group your operator expression";
            indented_paragraph @@
              source_text op1 op2;
            string "either group the first two";
            indented_paragraph @@
              left op1 op2;
            string "or group the second two";
            indented_paragraph @@
              right op1 op2;
            fill_paragraph
              "However the precedence and associativity of these operators \
               don't give me enough information. Please put parentheses to \
               indicate your intention."

           ]


    let error_explanation (errors:Parser.Dead_end.t list): t =
      match errors with
      | [] ->
         assert false (* Illegal call! *)
      | [e] ->
         chain [string "At the marker I was expecting";
                nest_list 4 [cut; cut; one_error_explanation e];
                cut]
      | _ ->
         chain [string "At the marker I was expecting one of";
                cut;
                indented_paragraph @@
                  print_list errors
                    (fun e ->
                      chain [
                          string "- ";
                          one_error_explanation e;
                          cut])
                ]



    let print (fd:Io.File.Out.fd) (width:int) (pp:t): unit Io.t =
      Out.run fd (PP.run 0 width width pp)
  end (* Pretty_make *)









module Located = Character_parser.Located












module Make (Io:Io.SIG) =
  struct
    module Pretty = Pretty_make (Io)

    type command_line = {
        command: string option;
        workspace: string;
        package_paths: string list;
        verbosity: int;
        force: bool;
        arguments: string list (* reversed *)
      }

    module CLP =
      Argument_parser.Make (struct type t = command_line end)

    let find_in_array (p:'a->bool) (arr: 'a array): int =
      Interval.find
        (fun i -> p arr.(i))
        0
        (Array.length arr)

    let find_elem_in_array (a:'a) (arr:'a array): int =
      find_in_array (fun e -> e = a) arr

    let has_file (name:string) (arr:string array): bool =
      find_elem_in_array name arr < Array.length arr

    let rec find_workspace
          (path:string)
        : (string * string array) option Io.t =
      (* Find a directory with a file named "alba-workspace.yml" in the
         directory [path] and all its parent directories.

         Return the path to the directory, the directory entries and the
         position of the file "alba-workspace.yml" in the entries.  *)
      let open Io in
      read_directory path >>= function
      | None ->
         return None
      | Some arr ->
         let len = Array.length arr in
         let pos = find_elem_in_array "alba-workspace.yml" arr
         in
         if pos = len then (* not the root of the workspace *)
           match Path.split path with
           | None ->
              return None
           | Some (dir,_) ->
              find_workspace dir
         else
           return @@ Some (path,arr)

    let find_packages
          (ws_path:string) (entries:string array)
        : string list Io.t =
      (* Find the packages in the workspace [ws_path].

         Return a list of paths
       *)
      let open Io in
      let rec find path entries lst =
        let len = Array.length entries in
        let rec find_in_entries i lst =
          if i = len then
            return lst
          else
            let path1 = Path.join path entries.(i) in
            read_directory path1 >>= function
            | None ->
               find_in_entries (i+1) lst
            | Some entries1  ->
               find path1 entries1 lst >>= fun lst ->
               find_in_entries (i+1) lst
        in
        if has_file "alba-package.yml" entries then
          return @@ path :: lst
        else
          find_in_entries 0 lst
      in
      find ws_path entries []


    let explore_workspace (cmd:command_line)
        : (string * string list) option Io.t =
      (* Find the root of the workspace and a list of package directories in
         the workspace.  *)
      let open Io in
      Stdout.line "explore workspace ..." >>= fun _ ->
      Path.absolute cmd.workspace >>= fun path ->
      find_workspace (Path.normalize path) >>= function
      | None ->
         return None
      | Some (path, entries) ->
         find_packages path entries >>= fun pkgs ->
         return @@ Some (path,pkgs)





    let compile (cmd:command_line): unit Io.t =
      Io.(Stdout.line "compile ..." >>= fun _ ->
          explore_workspace cmd >>= function
          | None ->
             Stdout.line "no workspace found"
          | Some (ws_path, _) ->
             Stdout.line ("workspace <" ^ ws_path ^ ">"))

    let status (_:command_line): unit Io.t =
      Io.Stdout.line "status ..."



    let build_and_compute
          (src:string) (e:Parser.Expression.t)
        : Pretty.t
      =
      let std_context = Context.standard () in
      match Builder.build e std_context with
      | Error problem ->
         let module Position = Character_parser.Position in
         (match problem with
          | Builder.Problem.Overflow (pos, str) ->
             let open Pretty in
             error_header "OVERFLOW"
             <+> print_source src 0
                   (Position.line pos) (Position.column pos)
                   (String.length str)
             <+> fill_paragraph "Your number is too big to fit into a machine \
                                 word."
             <+> cut

          | Builder.Problem.No_name (pos, str) ->
             let open Pretty in
             chain
               [error_header "NAMING";
                print_source
                  src 0
                  (Position.line pos) (Position.column pos)
                  (String.length str);
                fill_paragraph @@ "A cannot find this name.";
                cut]

          | Builder.Problem.Not_enough_args (pos, len, nargs, acts) ->
             assert (acts <> []);
             let module GP = Builder.Print (Pretty) in
             Pretty.(error_header "TYPE"
                     <+> print_source
                           src 0
                           (Position.line pos) (Position.column pos)
                           len
                     <+> fill_paragraph
                           ("I was expecting a function/operator which can \
                             be applied to " ^ string_of_int nargs
                            ^ " arguments. But I found only"
                            ^ if List.length acts = 1 then
                                ""
                              else
                                " one of")
                     <+> cut
                     <+> indented_paragraph
                           (chain_separated
                              (List.map GP.actual acts)
                              cut)
                     <+> cut)

          | Builder.Problem.None_conforms (pos, len, reqs, acts) ->
             assert (reqs <> []);
             assert (acts <> []);
             let module GP = Builder.Print (Pretty) in
             Pretty.(error_header "TYPE"
                     <+> print_source
                           src 0
                           (Position.line pos) (Position.column pos)
                           len
                     <+> fill_paragraph
                           ("I was expecting an expression of "
                            ^ if List.length reqs = 1 then
                                "type"
                              else
                                "one of the types")
                     <+> cut
                     <+> indented_paragraph
                           (chain_separated
                              (List.map GP.required reqs)
                              cut)
                     <+> cut
                     <+> string ("but I found"
                                 ^ (if List.length acts = 1 then
                                      ""
                                    else " one of"))
                     <+> cut
                     <+> indented_paragraphs (List.map GP.actual acts)
                     <+> cut)
         )

      | Ok lst ->
         Pretty.(
          paragraphs
            (List.map
               (fun (t,tp) ->
                 let t = Context.compute t std_context in
                 let module P = Context.Pretty (Pretty) in
                 P.print t std_context
                 <+> string ": "
                 <+> P.print tp std_context
                 <+> cut)
               lst)
         )



    let eval_expression (p:Parser.parser) (src:string): Pretty.t =
      assert (Parser.has_ended p);
      match Parser.result p with
      | Ok None ->
         Pretty.empty

      | Ok (Some e) ->
         Pretty.(expression e <+> build_and_compute src e)

      | Error errors ->
         let open Pretty in
         chain
           [ error_header "SYNTAX";
             print_source src 0 (Parser.line p) (Parser.column p) 1;
             error_explanation errors]


    let repl (_:command_line): unit Io.t =
      let module State =
        struct
          type t = string
          let string (s:t): string =
            s
          let init: t =  ""
          let prompt (s:t): string option =
              Some (if s = "" then "> " else "| ")
          let is_last (line:string): bool =
            let len = String.length line in
            len = 0 || line.[len-1] <> ' '
          let add (line:string) (s:t): t =
            if s = "" then
              line
            else
              s ^ "\n" ^ line
        end
      in
      let parse (s:string): Parser.parser =
        let len = String.length s in
        let rec parse i p =
          let more = Parser.needs_more p in
          if i < len && more then
            parse (i+1) (Parser.put_char p s.[i])
          else if more then
            Parser.put_end p
          else
            p
        in
        parse 0 Parser.initial
      in
      let next (s:State.t) (line:string): State.t Io.t =
        let s = State.add line s in
        if State.is_last line then
          let input = State.string s in
          let p = parse input in
          Io.(Pretty.print File.stdout 80 (eval_expression p input)
              >>= fun _ ->
              return State.init)
        else
          Io.return s
      and stop (s:State.t): State.t Io.t =
        Io.return s
      in
      Io.(let module Cli = Cli (State) in
          Cli.loop State.init next stop >>= fun _ -> return ())





    let commands: (string*(command_line->unit Io.t)*string) list =
      ["compile", compile,
       "Compile the modules provided on the command line and all its \
        dependencies if compilation is required. If no modules are provided \
        all modules of the package which require compilation are compiled."
      ;
        "status", status,
        "Display all modules which require compilation or recompilation."
      ;
        "repl", repl,
        "Start an interactive programming session."
      ]

    let command_options: (CLP.key*CLP.spec*CLP.doc) list =
      let open CLP in
      [("-verbosity",
        Int (fun i a -> {a with verbosity = i}),
        "Verbosity level (default 1)"
       );

       ("-w", String (fun s a -> {a with workspace = s}),
        "Path into an Alba workspace (default: current working directory)");

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
         workspace = "";
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






    let print_options: Pretty.t =
      let open Pretty in
      chain
        (List.map
           (fun (key,spec,doc) ->
             chain [cut; put_left 20 (key ^ CLP.argument_type spec);
                    nest 20 @@ fill_paragraph doc])
           command_options)


    let print_commands: Pretty.t =
      let open Pretty in
      chain
        (List.map
           (fun (cmd,_,doc) ->
             chain [cut; put_left 10 cmd; nest 10 @@ fill_paragraph doc])
           commands)


    let print_usage: Pretty.t =
      let open Pretty in
      chain
        [string "Usage: alba command options arguments";
         cut; cut;
         nest_list 4 [string "Commands:"; print_commands];
         cut; cut;
         nest_list 4 [string "Options:";  print_options];
         cut]

    let print_error (s:string): unit Io.t =
      let open Pretty in
      print
        Io.File.stderr
        80
        (string "Error: " <+> string s <+> cut <+> cut <+> print_usage)






    let run (): unit =
      let open Io in
      Process.execute
        (Process.command_line >>= fun args ->
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
            print_error (CLP.string_of_error e) >>= fun _ ->
            Process.exit 1
        )
  end
