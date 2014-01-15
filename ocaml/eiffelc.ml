open Support
open Container

let usage_string = "\
Usage:
    eiffelc options srcfile.e
"


let parse_file fn =
  let lexbuf = Lexing.from_channel (open_in fn)
  in
  lexbuf.Lexing.lex_curr_p <-
    {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = fn};
  Support.parse_error_fun := Lexer.print_unexpected;
  Parser.main Lexer.token lexbuf





module Analyze = struct

  let analyze(ast:declaration list) =
    let block_stack = Block_stack.make ()
    and class_table = Class_table.base_table ()
    and feature_table = Feature_table.empty ()
    and ass_table = Assertion_table.empty ()
    in
    let rec analyz (ast: declaration list) =
      let one_decl (d:declaration) =
        match d with
          Class_declaration (hm, cname, fgens, inherits, decl_blocks) ->
            assert (fgens.v = []);
            assert (inherits = []);
            assert (decl_blocks = []);
            Class_table.put hm cname class_table
        | Declaration_block (Feature_block (visi,dlist)) ->
            Block_stack.push visi block_stack;
            analyz dlist;
            Block_stack.pop block_stack;
            ()
        | Named_feature (fn, entlst, rt, body) ->
            Feature_table.put fn entlst rt body
              block_stack class_table feature_table
        | Assertion_feature (label, entlst, body) ->
            Prover.prove_and_store
              entlst body class_table feature_table ass_table
        | Formal_generic (name, concept) ->
            Class_table.put_formal name concept class_table
        | _ ->
            Class_table.print   class_table;
            Feature_table.print class_table feature_table;
            assert false
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
  and set_tracer (str:string): unit =
    if str = "proof" then
      Options.set_trace_proof ()
    else if str = "failed-proof" then
      Options.set_trace_failed_proof ()
    else
      raise (Arg.Bad "-trace proof  or  -trace failed-proof")
  and set_prover (str:string): unit =
    if str = "basic" then
      Options.set_prover_basic ()
    else if str = "local" then
      Options.set_prover_local ()
    else
      raise (Arg.Bad "")
  in
  try
    Arg.parse
      [("-trace",Arg.String set_tracer,"{proof,failed-proof}");
       ("-prover", Arg.String set_prover, "{basic,local}");
       ("-statistics", Arg.Unit Options.set_statistics, "");
       ("-goal-limit",
        Arg.Int
          (fun i ->
            if i<0 then
              raise (Arg.Bad "")
            else
              Options.set_goal_limit i),
        "maximum number of goals per proof");
       ("-no-limit", Arg.Unit Options.set_no_limit, "")
     ]
      anon_fun
      usage_string;
    if !file_name = "" then
      raise (Support.Eiffel_error ("Need a source file\n" ^ usage_string));
    try
      Analyze.analyze (parse_file !file_name);
      Statistics.write ();
    with Support.Error_info (inf,str) ->
      raise (Support.Error_fileinfo (!file_name,inf,str))
  with
    Support.Eiffel_error str
  | Sys_error str ->  prerr_string str; exit 1
  | Support.Error_fileinfo (fn,inf,str) ->
      prerr_string ((Support.info_string fn inf) ^ " " ^ str); exit 1
  | Parsing.Parse_error -> exit 1
