{

let last_pos = ref (Lexing.dummy_pos)

let last_is_endtok = ref false

let cached_tok: ((Parser.token*(bool*bool)) * Lexing.position) option ref 
    = ref None



let print_error pos str =
  let name = pos.Lexing.pos_fname
  and line = pos.Lexing.pos_lnum
  and col  = pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1
  in
  Printf.eprintf "%s:%d:%d: %s\n" name line col str

let print_unexpected (str:string) = print_error !last_pos "Unexpected token"

let print_illegal pos = print_error pos "Illegal token"



let info lexbuf =
      let pos = Lexing.lexeme_start_p lexbuf
      in
      Support.FINFO( 
        pos.Lexing.pos_lnum, (pos.Lexing.pos_cnum - pos.Lexing.pos_bol))


let print_pos lexbuf =
  let pos = Lexing.lexeme_start_p lexbuf
  in
  let name = pos.Lexing.pos_fname
  and line = pos.Lexing.pos_lnum
  and col  = pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1
  in
  Printf.printf "%s:%d:%d: token <%s>\n" name line col (Lexing.lexeme lexbuf)




let keyword_table = Hashtbl.create 53

let _ =
  List.iter (fun (kwd,tok) -> Hashtbl.add keyword_table kwd tok)
    [
     ("CURRENT",   Parser.KWCURRENT);
     ("Current",   Parser.KWCurrent);
     ("NONE",      Parser.KWNONE);
     ("Precursor", Parser.KWPrecursor);
     ("Process",   Parser.KWProcess);
     ("Result",    Parser.KWResult);

     ("all",       Parser.KWall);
     ("and",       Parser.KWand);
     ("case",      Parser.KWcase);
     ("class",     Parser.KWclass);
     ("check",     Parser.KWcheck);
     ("create",    Parser.KWcreate);
     ("deferred",  Parser.KWdeferred);
     ("do",        Parser.KWdo);
     ("else",      Parser.KWelse);
     ("elseif",    Parser.KWelseif);
     ("end"  ,     Parser.KWend);
     ("ensure",    Parser.KWensure);
     ("feature",   Parser.KWfeature);
     ("ghost",     Parser.KWghost);
     ("if",        Parser.KWif);
     ("immutable", Parser.KWimmutable);
     ("in",        Parser.KWin);
     ("inspect",   Parser.KWinspect);
     ("invariant", Parser.KWinvariant);
     ("local",     Parser.KWlocal);
     ("not",       Parser.KWnot);
     ("note",      Parser.KWnote);
     ("or",        Parser.KWor);
     ("require",   Parser.KWrequire);
     ("then",      Parser.KWthen);

     ("->",        Parser.ARROW);
     (":=",        Parser.ASSIGN);
     ("|",         Parser.BAR);
     ("^",         Parser.CARET);
     (":",         Parser.COLON);
     ("=>",        Parser.DARROW);
     ("||",        Parser.DBAR);
     ("::",        Parser.DCOLON);
     ("/",         Parser.DIVIDE);
     ("=",         Parser.EQ);
     ("~",         Parser.EQV);
     (">=",        Parser.GE);
     ("> ",        Parser.GT);
     ("<=",        Parser.LE);
     ("<",         Parser.LT);
     ("-",         Parser.MINUS);
     ("/=",        Parser.NEQ);
     ("/~",        Parser.NEQV);
     ("+",         Parser.PLUS);
     ("*",         Parser.TIMES);
   ]


let kwtoken id =
  let kw = Hashtbl.find keyword_table id
  in
  match kw with
    Parser.KWrequire -> kw, (true,false)
  | Parser.KWend     -> kw, (false,true)
  | Parser.KWif      -> kw, (true,false)
  | Parser.KWinspect -> kw, (true,false)
  | _                -> kw, (false,false)



}





(* Rules *)

rule next_token = parse

  [' ' '\t'] +    { next_token lexbuf }

| "-- " [^'\n']*  { next_token lexbuf }

| '\n'            { Lexing.new_line lexbuf; Parser.NEWLINE, (false,false) }

| ','             { Parser.COMMA,    (false,false) }

| '.'             { Parser.DOT,      (false,false) }

| '!'             { Parser.EXCLAM,   (false,false) }

| '{'             { Parser.LBRACE,   (true,false)  }

| '['             { Parser.LBRACKET, (true,false)  }

| '('             { Parser.LPAREN,   (true,false)  }

| '?'             { Parser.QMARK,    (false,false) }

| '}'             { Parser.RBRACE,   (false,true)  }

| ']'             { Parser.RBRACKET, (false,true)  }

| ')'             { Parser.RPAREN,   (false,true)  }

| ';'             { Parser.SEMICOL,  (false,false) }

| '_'             { Parser.USCORE,   (false,false) }


| "/in"           { Parser.NOTIN,    (false,false) }


| ['+' '-' '/' '*' '<' '>' '=' '~' ':' '#' '|']+ as op {
  try
    kwtoken op
  with
    Not_found ->
      let _ = assert ((String.length op) > 0)
      in
      let last = op.[(String.length op)-1]
      and sym  = Support.symbol op
      in
      if last = ':' 
      then Parser.OPERATOR  sym, (false,false)
      else Parser.ROPERATOR sym, (false,false)
}


| ['0'-'9']+ as num { Parser.NUMBER num, (true,true) }


| ['A'-'Z'] ['A'-'Z' '0'-'9' '_']* as id {
  try
    kwtoken id
  with
    Not_found ->
      Parser.UIDENTIFIER (Support.symbol id), (true,true)
}


| ['a'-'z'] ['a'-'z' '0'-'9' '_']* as id { 
  try
    kwtoken id
  with
    Not_found -> Parser.LIDENTIFIER (Support.symbol id), (true,true)
}


| ['A'-'Z' 'a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']* as id { 
  try
    kwtoken id
  with
    Not_found ->
      Printf.eprintf "Illegal token %s\n" id;
      print_illegal (Lexing.lexeme_start_p lexbuf);
      raise (Sys_error "error during lexical analyis")
}

| eof   {Printf.printf "end of file encountered\n";
         Parser.EOF, (false,false) }


| _     {
  print_illegal (Lexing.lexeme_start_p lexbuf);
  raise (Sys_error "error during lexical analyis")
}



(* Trailer *)
{


let nextorcached_token lexbuf =
  match !cached_tok with
    None -> 
      let tok = next_token lexbuf 
      in  
      tok, Lexing.lexeme_start_p lexbuf
  | Some(t,p) ->
      cached_tok := None;
      t,p

let some_cached () =
  match !cached_tok with None -> false | Some(_,_) -> true

let cache_next lexbuf = 
  let tok = next_token lexbuf
  in
  assert  (some_cached () = false);
  cached_tok := Some (tok, Lexing.lexeme_start_p lexbuf);
  tok

let return_tok tok isend pos =
  last_is_endtok := isend;
  last_pos       := pos;
  tok

let rec token lexbuf =
  let tok,pos = nextorcached_token lexbuf
  and isstart t = fst (snd t)
  and isend   t = snd (snd t)
  in
  match fst tok with
    Parser.NEWLINE -> 
      if !last_is_endtok then
        let tok = cache_next lexbuf
        in
        if isstart tok then
          (last_is_endtok:=false;
           return_tok Parser.SEMICOL false pos)
        else
          token lexbuf
      else
        token lexbuf

  | _ -> 
      return_tok (fst tok) (isend tok) pos




}



