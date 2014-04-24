open Container
open Support
open Term

let usage_string = "\
Usage:
    eiffelc options srcfile.e
"

let file_name = ref ""
let dir_name  = ref ""
let base_name = ref ""
let mod_name  = ref ""

let parse_arguments (): unit =
  let anon_fun str =
    if !file_name <> "" then
      raise (Arg.Bad "Only one source file allowed")
    else if not (Filename.check_suffix str ".e") then
      raise (Arg.Bad "Eiffel source file must have suffix \".e\"")
    else begin
      file_name := str;
      dir_name  := Filename.dirname str;
      base_name := Filename.basename str;
      mod_name  := Filename.chop_extension !base_name
    end
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
    else if str = "forward" then
      Options.set_prover_forward ()
    else
      raise (Arg.Bad "")
  and set_trace_level (i:int): unit =
    if i<= 0 then raise (Arg.Bad "")
    else
      Options.set_trace_level i
  in
  Arg.parse
    [("-trace",  Arg.String set_tracer, "{proof,failed-proof}");
     ("-prover", Arg.String set_prover, "{basic,forward}");
     ("-statistics", Arg.Unit Options.set_statistics, "");
     ("-goal-limit",
      Arg.Int
        (fun i ->
          if i<0 then
            raise (Arg.Bad "")
          else
            Options.set_goal_limit i),
      "maximum number of goals per proof");
     ("-no-limit", Arg.Unit Options.set_no_limit, "");
     ("-trace-level", Arg.Int set_trace_level, "trace level")
   ]
    anon_fun
    usage_string;
  if !file_name = "" then
    raise (Support.Eiffel_error ("Need a source file\n" ^ usage_string))


let parse_file (fn:string): use_block * declaration list =
  Support.Parse_info.set_file_name fn;
  let lexbuf = Lexing.from_channel (open_in fn)
  in
  lexbuf.Lexing.lex_curr_p <-
    {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = fn};
  Parser.main Lexer.token lexbuf



let put_feature
    (fn: feature_name withinfo)
    (entlst: entities list withinfo)
    (rt: return_type)
    (bdy: feature_body option)
    (context: Context.t): unit =
  Context.push entlst rt context;
  let impstat,term_opt =
    match bdy with
      None ->
        Feature_table.No_implementation,
        None
    | Some (None, Some Impbuiltin, None) ->
        Feature_table.Builtin,
        None
    | Some (None, None, Some [ens]) ->
        begin
          match ens.v with
            Binexp (Eqop, ExpResult,def) ->
              let term =
                Typer.result_term
                  (withinfo ens.i def)
                  context
              in
              Feature_table.No_implementation,
              Some term
          | _ -> not_yet_implemented ens.i
                "functions not defined with \"Result = ...\""
        end
    | Some (None, Some Impdeferred, None) ->
        Feature_table.Deferred,
        None

     | _ -> not_yet_implemented fn.i
           "functions with implementation/preconditions"
  in
  Context.put_global_function fn impstat term_opt context;
  Context.pop context


let analyze(ast: declaration list) (context:Context.t): unit =
  let rec analyz (ast: declaration list): unit =
    let one_decl (d:declaration) =
      match d with
        Class_declaration (hm, cname, fgens, inherits, decl_blocks) ->
          assert (fgens.v = []);     (* nyi: formal generics *)
          assert (inherits = []);    (* nyi: inheritance     *)
          assert (decl_blocks = []); (* nyi: class features  *)
          Context.put_class hm cname context;
      | Declaration_block (Feature_block (visi,dlist)) ->
          Context.set_visibility visi context;
          analyz dlist;
          Context.reset_visibility context;
      | Named_feature (fn, entlst, rt, body) ->
          put_feature fn entlst rt body context;
      | Assertion_feature (label, entlst, body) ->
          Prover.prove_and_store entlst body context
      | Formal_generic (name, concept) ->
          Context.put_formal_generic name concept context
      | _ ->
          Context.print context;
          assert false
    in
    match ast with
      [] -> ()
      | f::t -> one_decl f; analyz t
  in
  analyz ast(*;
  Context.print context*)



let rec process_use (use_blk: use_block) (c:Context.t): unit =
  List.iter
    (fun name ->
      let nmestr = Filename.concat !dir_name  ((ST.string name.v) ^ ".ei") in
      let use_blk, ast = parse_file nmestr in
      process_use use_blk c;
      analyze ast c)
    use_blk

let _ =
  try
    parse_arguments ();
    try
      let use_blk,ast  = parse_file !file_name in
      let context = Context.make ()
      in
      Support.Parse_info.set_interface ();
      process_use use_blk context;
      Support.Parse_info.set_module ();
      Support.Parse_info.set_file_name !file_name;
      analyze ast context;
      Statistics.write ();
    with Support.Error_info (inf,str) ->
      let fn = Support.Parse_info.file_name () in
      raise (Support.Error_fileinfo (fn,inf,str))
  with
    Support.Eiffel_error str
  | Sys_error str ->  prerr_string (str ^ "\n"); exit 1
  | Support.Error_fileinfo (fn,inf,str) ->
      prerr_string ((Support.info_string fn inf) ^ " " ^ str ^ "\n"); exit 1
  | Parsing.Parse_error -> exit 1
