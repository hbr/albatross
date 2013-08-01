open Support

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





module Block_stack: sig
  type t
  val empty: unit -> t
  val push:  Support.visibility -> t -> unit
  val pop:   t -> unit
  val is_empty: t -> bool
  val is_private: t -> bool
end = struct
  open Support
  type t = visibility Stack.t
  let empty () = Stack.create ()
  let push v s =
    assert (Stack.is_empty s);
    Stack.push v s
  let pop s =
    let _ = Stack.pop s in
    ()
  let is_empty s = Stack.is_empty s
  let is_private s =
    (not (Stack.is_empty s)) &&
    match Stack.top s with
      Private -> true | _ -> false
end




module Analyze = struct
  open Type

  let analyze(ast:declaration list) =
    let block_stack = Block_stack.empty ()
    and class_table = Class_table.base_table ()
    and feature_table = Feature_table.empty ()
    in
    let rec analyz (ast: declaration list) =
      let one_decl (d:declaration) =
        match d with
          Class_declaration (hm, cname, fgens, inherits, decl_blocks) ->
            assert (fgens.v = []);
            assert (inherits = []);
            assert (decl_blocks = []);
            Class_table.put class_table hm cname
        | Declaration_block (Feature_block (visi,dlist)) ->
            Block_stack.push visi block_stack;
            analyz dlist;
            Block_stack.pop block_stack;
            ()
        | Named_feature (fn, entlst, rt, body) ->
            Feature_table.put fn entlst rt body feature_table
        | _ -> assert false
      in
      match ast with
        [] -> ()
      | f::t -> one_decl f; analyz t
    in
    analyz ast
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
    try
      Analyze.analyze (parse_file !file_name)
    with Support.Error_info (inf,str) ->
      raise (Support.Error_fileinfo (!file_name,inf,str))
  with 
    Support.Eiffel_error str
  | Sys_error str ->  prerr_string str; exit 1
  | Support.Error_fileinfo (fn,inf,str) ->
      prerr_string ((Support.info_string fn inf) ^ " " ^ str); exit 1
  | Parsing.Parse_error -> exit 1
