let usage_string = "\
Usage:
    eiffelc srcfile.e
"


let parse_file fn =
  let lexbuf = Lexing.from_channel (open_in fn)
  in
  lexbuf.Lexing.lex_curr_p <- 
    {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = fn};
  Support.parse_error_fun := Lexer.print_unexpected;
  Parser.main Lexer.token lexbuf




module Class_table = struct
  open Type

  let ctxt = Class.base_context ()
end


module Analyze = struct
  open Support
  let rec analyze (ast: declaration list) =
    let one_decl (d:declaration) =
      match d with
        Class_declaration (hm, cname, fgens, inherits, decl_blocks) ->
          assert (fgens.v = []);
          assert (inherits = []);
          assert (decl_blocks = []);
          assert false
      | _ -> assert false
    in
    match ast with
      [] -> ()
    | f::t -> one_decl f; analyze t
end




let _ =
  let file_name = ref "" in
  let anon_fun str =
    if !file_name <> "" then
      raise (Arg.Bad "Only one source file allowed")
    else if not (Filename.check_suffix str ".e") then
      raise (Arg.Bad "Eiffel source file must have suffix \".e\"")
    else
      file_name := str;
  in
  try 
    Arg.parse [] anon_fun usage_string;
    if !file_name = "" then
      raise (Support.Eiffel_error ("Need a source file\n" ^ usage_string));
    Analyze.analyze (parse_file !file_name)
  with 
    Support.Eiffel_error str
  | Sys_error str ->  prerr_string str; exit 1
  | Parsing.Parse_error -> exit 1
