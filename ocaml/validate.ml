(*
open Support

let used_packages (dl: declaration list) =
  let rec up_dl (dl: declaration list) =
    match dl with
      []   -> []
    | f::t -> List.rev_append (up_dec f) (up_dl t)
  and up_dec (d: Support.declaration) =
    match d with
      Assertion_feature (_,entlist,body) ->
        List.rev_append (up_entlist entlist.v) (up_body body)
    | Named_feature (_,entlist,rt,body) ->
        List.rev_append (up_entlist entlist.v) (up_body body)
  and
      up_entlist entlist =
        assert false
  and
      up_body body =
        assert false
  in
  up_dl dl
*)  
        

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
