open Term
open Proof
open Support
open Printf

module PC = Proof_context


type kind =
    PAxiom
  | PDeferred
  | PNormal


let is_deferred (k:kind): bool =
  match k with
    PDeferred -> true
  | _         -> false



let analyze_imp_opt
    (i:int)
    (info:    info)
    (imp_opt: implementation option)
    (c:Context.t)
    : kind * compound =
  let iface = Context.is_interface_use c in
  let kind,is_do,clst =
    match imp_opt with
      None ->
        if iface then
          PAxiom,  false, []
        else
          PNormal, false, []
    | Some Impdeferred ->
        if 0 < i then
          error_info info "Deferred not allowed here";
        PDeferred,false, []
    | Some Impbuiltin ->
        if 0 < i then
          error_info info "Axiom not allowed here";
        if iface then
          error_info info "Axiom not allowed in interface file";
        PAxiom,   false, []
    | Some Impevent ->
        error_info info "Assertion cannot be an event"
    | Some (Impdefined (Some locs,is_do,cmp)) ->
        not_yet_implemented info "Local variables in assertions"
    | Some (Impdefined (None,is_do,cmp)) ->
        if iface then begin
          if is_do || cmp <> [] then
            error_info info "not allowed in interface file";
          PAxiom,  false, []
        end else
          PNormal, false, cmp
  in
  if is_do then
    not_yet_implemented info "Assertions with do block"
  else
    kind, clst


let analyze_body (i:int) (info:info) (bdy: feature_body) (c:Context.t)
    : kind * compound * compound * compound =
  match bdy with
    _, _, None ->
      error_info info "Assertion must have an ensure clause"
  | rlst_opt, imp_opt, Some elst ->
      let rlst =
        match rlst_opt with
          None   -> []
        | Some l -> l
      and kind,clst =
        analyze_imp_opt i info imp_opt c
      in
      kind, rlst, clst, elst



let get_term (ie: info_expression) (pc:PC.t): term =
  let c = PC.context pc in
  Typer.result_term ie c



let add_assumptions_or_axioms
    (lst:compound) (is_axiom:bool) (pc:PC.t): int list =
  let res =
    List.map
      (fun ie ->
        let t = get_term ie pc in
        if is_axiom then
          PC.add_axiom t pc
        else
          PC.add_assumption t pc)
    lst
  in
  if not is_axiom then PC.close_assumptions pc;
  res

let add_assumptions (lst:compound) (pc:PC.t): unit =
  let _ = add_assumptions_or_axioms lst false pc in ()

let add_axioms (lst:compound) (pc:PC.t): int list =
  add_assumptions_or_axioms lst true pc



let add_proved
    (defer: bool)
    (owner: int)
    (lst: (term*proof_term) list)
    (pc:PC.t)
    : unit =
  PC.add_proved_list defer owner lst pc




let prove_basic_expression (ie:info_expression) (pc:PC.t): int =
  let strength =
    if Proof_context.is_interface_check pc then 0
    else 2
  in
  let t = get_term ie pc in
  try
    Prover.prove t strength pc
  with Not_found ->
    error_info ie.i "Cannot prove"



let prove_ensure (lst:compound) (k:kind) (pc:PC.t): (term*proof_term) list =
  let idx_lst =
    match k with
      PAxiom | PDeferred ->
        add_axioms lst pc
    | PNormal ->
        let res = List.map (fun ie -> prove_basic_expression ie pc) lst in
        res
  in
  List.map (fun idx -> PC.discharged idx pc) idx_lst



let rec make_proof
    (i:int)
    (entlst: entities list withinfo)
    (kind: kind)
    (rlst: compound)
    (clst: compound)
    (elst: compound)
    (pc:   PC.t)
    : unit =
  let prove_check_expression (ie:info_expression): unit =
    let c = PC.context pc in
    match ie.v with
      Expquantified (q,entlst,Expproof(rlst,imp_opt,elst)) ->
        begin
          match q with
            Universal ->
              let kind, clst =
                analyze_imp_opt (i+1) entlst.i imp_opt c
              in
              make_proof (i+1) entlst kind rlst clst elst pc
          | Existential ->
              error_info ie.i "Only \"all\" allowed here"
        end
    | Expproof (rlst,imp_opt,elst) ->
        let kind, clst = analyze_imp_opt (i+1) ie.i imp_opt c in
        make_proof (i+1) (withinfo UNKNOWN []) kind rlst clst elst pc
    | _ ->
        let _ = prove_basic_expression ie pc in
        ()
  in
  PC.push entlst pc;
  let defer = is_deferred kind
  and owner = PC.owner pc
  in
  if defer then
    PC.check_deferred pc;  (* owner class has to be deferred *)
  add_assumptions rlst pc;
  List.iter (fun ie -> prove_check_expression ie) clst;
  let pair_lst = prove_ensure elst kind pc in
  PC.pop pc;
  add_proved defer owner pair_lst pc


let prove_and_store
    (entlst:  entities list withinfo)
    (bdy:     feature_body)
    (pc: PC.t)
    : unit =
  let c = PC.context pc in
  let kind, rlst, clst, elst = analyze_body 0 entlst.i bdy c
  in
  make_proof 0 entlst kind rlst clst elst pc



let put_class
    (hm:       header_mark withinfo)
    (cn:       classname)
    (fgs:      formal_generics)
    (inherits: inherit_clause list)
    (pc: PC.t)
    : unit =
  (** Analyze the class declaration [hm,cn,fgs,inherits] and add or update the
      corresponding class.  *)
  assert (PC.is_global pc);
  let ft = PC.feature_table pc in
  let ct = Feature_table.class_table ft in
  let idx =
    try
      let idx = Class_table.find_for_declaration cn.v ct in
      Class_table.update idx hm fgs  ct;
      idx
    with Not_found ->
      let path, cn0 = cn.v in
      if path <> [] then
        error_info cn.i
          ("Class \"" ^ (string_of_classname path cn0) ^ "\" cannot be found");
      let idx = Class_table.count ct in
      Class_table.add hm cn0 fgs ct;
      idx
  in
  List.iter
    (fun par_lst ->
      List.iter
        (fun (ghost,tp,adapt_lst) ->
          assert (adapt_lst = [] ); (* nyi: feature adaption *)
          let par_idx, par_args = Class_table.parent_type idx tp ct in
          let lst, lst_priv =
            Class_table.inherited_ancestors idx par_idx par_args tp.i ct in
          Class_table.do_inherit idx lst ct;
          if lst_priv <> [] then
            Class_table.export_inherited idx lst_priv ct;
          Feature_table.do_inherit idx lst tp.i ft;
          Feature_table.export_inherited idx lst_priv ft;
          PC.do_inherit idx lst tp.i pc)
        par_lst)
    inherits



let assertion_list (lst:compound) (context:Context.t): term list =
  List.map (fun e -> Typer.result_term e context) lst


let result_term (lst:info_expression list) (context:Context.t): term =
  match lst with
    [] -> assert false
  | [e] -> begin
      match e.v with
        Binexp (Eqop, ExpResult,def) ->
          Typer.result_term
            (withinfo e.i def)
            context
      | _ ->
          raise Not_found
  end
  | _ -> raise Not_found




let put_feature
    (fn: feature_name withinfo)
    (entlst: entities list withinfo)
    (rt: return_type)
    (is_func: bool)
    (bdy: feature_body option)
    (exp: info_expression option)
    (context: Context.t): unit =
  Context.push entlst rt false is_func context;
  let impstat,term_opt =
    match bdy, exp with
      None, None ->
        Feature_table.No_implementation,
        None
    | None, Some ie ->
        let term = Typer.result_term ie context in
        Feature_table.No_implementation,
        Some term
    | Some bdy, None ->
        begin
          match bdy with
            None, Some Impbuiltin, None ->
              Feature_table.Builtin,
              None
          | Some reqlst, Some Impbuiltin, None ->
              let _ = assertion_list reqlst context in
              Feature_table.Builtin,
              None
          | Some reqlst, None, None ->
              let _ = assertion_list reqlst context in
              Feature_table.No_implementation, None
          | Some reqlst, None, Some enslst ->
              (try
                let term = result_term enslst context in
                let _ = assertion_list reqlst context in
                Feature_table.No_implementation, Some term
              with Not_found ->
                not_yet_implemented fn.i
                  "functions not defined with `Result = ...'")
          | None, Some Impdeferred, None ->
              Feature_table.Deferred,
              None
          | _ -> not_yet_implemented fn.i
                "functions with implementation/preconditions"
        end
    | _ -> assert false (* cannot happen *)
  in
  Context.put_global_function fn impstat term_opt context;
  Context.pop context






let analyze(ast: declaration list) (pc:PC.t): unit =
  let context = PC.context pc in
  let rec analyz (ast: declaration list): unit =
    let one_decl (d:declaration) =
      match d with
        Class_declaration (hm, cname, fgens, inherits) ->
          put_class hm cname fgens inherits pc
      | Named_feature (fn, entlst, rt, is_func, body, expr) ->
          put_feature fn entlst rt is_func body expr context
      | Assertion_feature (label, entlst, body) ->
          prove_and_store entlst body pc
      | Formal_generic (name, concept) ->
          Context.put_formal_generic name concept context
    in
    match ast with
      [] -> ()
      | f::t -> one_decl f; analyz t
  in
  analyz ast;
  if PC.is_interface_check pc then
    PC.check_interface pc
