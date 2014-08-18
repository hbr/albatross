open Container
open Support
open Term

let usage_string = "\
Usage:
    eiffelc options src1.e src2.e ...
"

type file_name = {name: string; dir: string; base: string; mdlnme: string}

let files = ref []

let print_version (): unit =
  Printf.printf "version: tbd  sha1 %s\n" Sha1.sha1;
  exit 0

let parse_arguments (): unit =
  let anon_fun str =
    if not (Filename.check_suffix str ".e") then
      raise (Arg.Bad "Eiffel source file must have suffix \".e\"")
    else begin
      let base = Filename.basename str in
      files := {name   = str;
                dir    = Filename.dirname str;
                base   = base;
                mdlnme = Filename.chop_extension base} :: !files;
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
     ("-version",    Arg.Unit print_version, "");
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
  if !files = [] then
    raise (Support.Eiffel_error ("Need a source file\n" ^ usage_string))


let parse_file (fn:string): use_block * declaration list =
  Support.Parse_info.set_file_name fn;
  let lexbuf = Lexing.from_channel (open_in fn)
  in
  lexbuf.Lexing.lex_curr_p <-
    {lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = fn};
  Parser.file Lexer.token lexbuf



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


let analyze(ast: declaration list) (pc:Proof_context.t): unit =
  let context = Proof_context.context pc in
  let rec analyz (ast: declaration list): unit =
    let one_decl (d:declaration) =
      match d with
        Class_declaration (hm, cname, fgens, inherits) ->
          Context.put_class hm cname fgens inherits context;
      | Named_feature (fn, entlst, rt, body) ->
          put_feature fn entlst rt body context;
      | Assertion_feature (label, entlst, body) ->
          Prover.prove_and_store entlst body pc
      | Formal_generic (name, concept) ->
          Context.put_formal_generic name concept context
    in
    match ast with
      [] -> ()
      | f::t -> one_decl f; analyz t
  in
  analyz ast(*;
  Context.print context*)




let process_use (use_blk: use_block) (f:file_name) (pc:Proof_context.t): unit =
  let c = Proof_context.context pc in
  let rec used (use_blk: use_block) (stack: int list) (set:IntSet.t)
      : IntSet.t =
    let push (nme:int withinfo): int list =
      if List.exists (fun n -> n=nme.v) stack then
        error_info nme.i "Cyclic module dependency"
      else
        nme.v :: stack
    in
    List.fold_left
      (fun set nme ->
        let used_set =
          try
            let mdl = Context.find_module nme.v [] c in
            let used_set = Context.used_modules mdl c in
            IntSet.union set used_set
          with Not_found ->
            let nmestr = Filename.concat f.dir  ((ST.string nme.v) ^ ".ei") in
            Printf.printf "Parsing file \"%s\"\n" nmestr;
            let use_blk, ast = parse_file nmestr in
            let set = used use_blk (push nme) set in
            Context.add_module nme.v [] 2 set c;
            Support.Parse_info.set_file_name nmestr;
            analyze ast pc;
            IntSet.add (Context.current_module c) set
        in
        IntSet.union used_set set)
      set
      use_blk
  in
  let used_set = used use_blk [] IntSet.empty in
  Context.add_module (ST.symbol f.mdlnme) [] 0 used_set c






let compile (f: file_name) (pc:Proof_context.t): unit =
  Printf.printf "Compiling file \"%s\"\n" f.name;
  try
    let use_blk,ast  = parse_file f.name in
    (*Support.Parse_info.set_use_interface ();*)
    process_use use_blk f pc;
    (*Support.Parse_info.set_module ();*)
    Support.Parse_info.set_file_name f.name;
    analyze ast pc;
    Statistics.write ();
  with Support.Error_info (inf,str) ->
    let fn = Support.Parse_info.file_name () in
    raise (Support.Error_fileinfo (fn,inf,str))



let _ =
  try
    parse_arguments ();
    files := List.rev !files;
    let pc = Proof_context.make () in
    List.iter (fun f -> compile f pc) !files
  with
    Support.Eiffel_error str
  | Sys_error str ->  prerr_string (str ^ "\n"); exit 1
  | Support.Error_fileinfo (fn,inf,str) ->
      prerr_string ((Support.info_string fn inf) ^ " " ^ str ^ "\n"); exit 1
  | Parsing.Parse_error -> exit 1
