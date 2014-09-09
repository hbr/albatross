{

let last_is_endtok = ref false

type extended_token = Parser.token*(bool*bool)
              (* [token, [can_start_line,can_end_line]] *)

let parse_token (tok: extended_token): Parser.token = fst tok

let is_start_token (tok:extended_token): bool = fst (snd tok)

let is_end_token   (tok:extended_token): bool = snd (snd tok)

let cached_tok: (extended_token * Lexing.position) option ref
    = ref None



let comment_level: int ref = ref 0

let print_illegal (pos:Lexing.position): unit =
  Support.Parse_info.print_error pos "Illegal token"
  (*print_error pos "Illegal token"*)



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
     ("as",        Parser.KWas);
     ("case",      Parser.KWcase);
     ("check",     Parser.KWcheck);
     ("class",     Parser.KWclass);
     ("create",    Parser.KWcreate);
     ("deferred",  Parser.KWdeferred);
     ("do",        Parser.KWdo);
     ("else",      Parser.KWelse);
     ("elseif",    Parser.KWelseif);
     ("end"  ,     Parser.KWend);
     ("ensure",    Parser.KWensure);
     ("false",     Parser.KWfalse);
     ("feature",   Parser.KWfeature);
     ("ghost",     Parser.KWghost);
     ("if",        Parser.KWif);
     ("immutable", Parser.KWimmutable);
     ("import",    Parser.KWimport);
     ("in",        Parser.KWin);
     ("inherit",   Parser.KWinherit);
     ("inspect",   Parser.KWinspect);
     ("invariant", Parser.KWinvariant);
     ("local",     Parser.KWlocal);
     ("not",       Parser.KWnot);
     ("note",      Parser.KWnote);
     ("old",       Parser.KWold);
     ("or",        Parser.KWor);
     ("redefine",  Parser.KWredefine);
     ("rename",    Parser.KWrename);
     ("require",   Parser.KWrequire);
     ("some",      Parser.KWsome);
     ("then",      Parser.KWthen);
     ("true",      Parser.KWtrue);
     ("undefine",  Parser.KWundefine);
     ("use",       Parser.KWuse);

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
  | Parser.KWall     -> kw, (true,false)
  | Parser.KWend     -> kw, (false,true)
  | Parser.KWnot     -> kw, (true,false)
  | Parser.KWold     -> kw, (true,false)
  | Parser.KWsome    -> kw, (true,false)
  | Parser.KWif      -> kw, (true,false)
  | Parser.KWinspect -> kw, (true,false)
  | Parser.KWtrue    -> kw, (true,true)
  | Parser.KWfalse   -> kw, (true,true)
  | Parser.KWResult  -> kw, (true,true)
  | Parser.KWCurrent -> kw, (true,true)
  | Parser.KWProcess -> kw, (true,true)
  | _                -> kw, (false,false)



}





(* Rules *)

rule next_token = parse

  [' ' '\t'] +    { next_token lexbuf }

| "-- " [^'\n']*  { next_token lexbuf }

| "{:"            { comment_level:= !comment_level+1; comment lexbuf }

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

| "()"            { Parser.PARENOP,  (false,false) }

| "[]"            { Parser.BRACKETOP,(false,false) }


| ['+' '-' '/' '*' '<' '>' '=' '~' ':' '#' '|']+ as op {
  try
    kwtoken op
  with
    Not_found ->
      let _ = assert ((String.length op) > 0)
      in
      let last = op.[(String.length op)-1]
      and sym  = Support.ST.symbol op
      in
      if last = ':'
      then Parser.OPERATOR  sym, (false,false)
      else Parser.ROPERATOR sym, (false,false)
}


| ['0'-'9']+ as num { Parser.NUMBER (Support.ST.symbol num), (true,true) }


| ['A'-'Z'] ['A'-'Z' '0'-'9' '_']* as id {
  try
    kwtoken id
  with
    Not_found ->
      Parser.UIDENTIFIER (Support.ST.symbol id), (true,true)
}


| ['a'-'z'] ['a'-'z' '0'-'9' '_']* as id {
  try
    kwtoken id
  with
    Not_found -> Parser.LIDENTIFIER (Support.ST.symbol id), (true,true)
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

| eof   { Parser.EOF, (false,false) }


| _     {
  print_illegal (Lexing.lexeme_start_p lexbuf);
  raise (Sys_error "error during lexical analyis")
}

and comment = parse

  ':'           { comment lexbuf }

| '{'           { comment lexbuf }

| [^':' '{']+   { comment lexbuf }

| "{:"          { comment_level := !comment_level+1;
                  comment lexbuf}

| ":}"          { comment_level := !comment_level-1;
                  if !comment_level = 0 then
                    next_token lexbuf
                  else
                    comment lexbuf}


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
  assert  (not (some_cached ()));
  let tok = next_token lexbuf
  in
  cached_tok := Some (tok, Lexing.lexeme_start_p lexbuf);
  tok

let return_tok tok isend pos =
  last_is_endtok := isend;
  Support.Parse_info.set_last_position pos;
  tok

let rec token lexbuf =
  let tok,pos = nextorcached_token lexbuf
  in
  match parse_token tok with
    Parser.NEWLINE ->
      if !last_is_endtok then
        let tok = cache_next lexbuf
        in
        if is_start_token tok then
          (last_is_endtok:=false;
           return_tok Parser.SEMICOL false pos)
        else
          token lexbuf
      else
        token lexbuf

  | _ ->
      return_tok (fst tok) (is_end_token tok) pos




}



