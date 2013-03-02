

let parse_file (f:string) =
  let lexbuf = Lexing.from_channel (open_in f)
  in
  lexbuf.Lexing.lex_curr_p <- 
    {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = f};
  Support.parse_error_fun := Lexer.print_unexpected;
  Parser.main Lexer.token lexbuf

let parse_file2 (f:string) = let _ = parse_file f in ()

let rec validate (modules:string list)  = 
  List.iter parse_file2 modules
