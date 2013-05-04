let print_module (f:string) (d:Support.declaration list) =
  Printf.printf "module: %s\n" f


let parse_file (f:string) =
  let lexbuf = Lexing.from_channel (open_in f)
  (*and _ =   Parsing.set_trace true*)
  in
  lexbuf.Lexing.lex_curr_p <- 
    {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = f};
  Support.parse_error_fun := Lexer.print_unexpected;
  Parser.main Lexer.token lexbuf




let rec validate (modules:string list)  =
  let process_one (f:string) =
    let dlist = parse_file f
    in
    print_module f dlist
  in
  List.iter process_one modules
