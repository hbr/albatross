(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Term
open Proof
open Signature
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
  let iface = Context.is_interface_use c || Context.is_interface_check c in
  let kind,is_do,clst =
    match imp_opt with
      None ->
        if Context.is_interface_use c then
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
        if Context.is_interface_use c then begin
          if is_do || cmp <> [] then
            error_info info "proof not allowed in interface file";
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



let get_boolean_term (ie: info_expression) (pc:Proof_context.t): term =
  let c = Proof_context.context pc in
  Typer.boolean_term ie c

let term_preconditions (t:term) (pc:PC.t): term list =
  let c = PC.context pc in
  Context.term_preconditions t c


let verify_preconditions (t:term) (info:info) (pc:Proof_context.t): unit =
  if PC.is_private pc then
    let pres = term_preconditions t pc in
    List.iter
      (fun t ->
        try Prover2.prove t pc
        with
          Not_found ->
            error_info info ("Cannot prove precondition " ^ (PC.string_of_term t pc))
        | Proof.Limit_exceeded limit ->
            error_info info ("Cannot prove precondition "
                             ^ (PC.string_of_term t pc)
                             ^ ", goal limit " ^ (string_of_int limit) ^ " exceeded"))
      pres


let add_assumptions_or_axioms
    (lst:compound) (is_axiom:bool) (pc:Proof_context.t): int list =
  List.map
    (fun ie ->
      let t = get_boolean_term ie pc in
      verify_preconditions t ie.i pc;
      if is_axiom then
        Proof_context.add_axiom t pc
      else begin
        Proof_context.add_assumption t pc
      end)
    lst


let add_assumptions (lst:compound) (pc:Proof_context.t): unit =
  let _ = add_assumptions_or_axioms lst false pc in ();
  PC.close pc


let add_axioms (lst:compound) (pc:Proof_context.t): int list =
  add_assumptions_or_axioms lst true pc



let add_proved
    (defer: bool)
    (owner: int)
    (lst: (term*proof_term) list)
    (pc:Proof_context.t)
    : unit =
  Proof_context.add_proved_list defer owner lst pc




let prove_basic_expression (ie:info_expression) (pc:Proof_context.t): int =
  let t = get_boolean_term ie pc in
  verify_preconditions t ie.i pc;
  try
    let res = Prover2.prove_and_insert t pc in
    PC.close pc;
    res
  with Not_found ->
    error_info ie.i "Cannot prove"
  | Limit_exceeded limit ->
      let str = string_of_int limit in
      error_info ie.i ("Cannot prove, goal limit " ^ str ^ " exceeded")



let prove_ensure (lst:compound) (k:kind) (pc:Proof_context.t): (term*proof_term) list =
  let idx_lst =
    match k with
      PAxiom | PDeferred ->
        add_axioms lst pc
    | PNormal ->
        let res = List.map (fun ie -> prove_basic_expression ie pc) lst in
        res
  in
  List.map (fun idx -> Proof_context.discharged idx pc) idx_lst



let rec make_proof
    (i:int)
    (entlst: entities list withinfo)
    (kind: kind)
    (rlst: compound)
    (clst: compound)
    (elst: compound)
    (pc:   Proof_context.t)
    : unit =
  let prove_check_expression (ie:info_expression) (pc:PC.t): unit =
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
  let pc1 = Proof_context.push entlst None false false pc in
  let defer = is_deferred kind
  and owner = Proof_context.owner pc1
  in
  if defer then
    Proof_context.check_deferred pc1;  (* owner class has to be deferred *)
  add_assumptions rlst pc1;
  List.iter (fun ie -> prove_check_expression ie pc1) clst;
  let pair_lst = prove_ensure elst kind pc1 in
  add_proved defer owner pair_lst pc;
  PC.close pc


let prove_and_store
    (entlst:  entities list withinfo)
    (bdy:     feature_body)
    (pc: Proof_context.t)
    : unit =
  let c = Proof_context.context pc in
  let kind, rlst, clst, elst = analyze_body 0 entlst.i bdy c
  in
  make_proof 0 entlst kind rlst clst elst pc



let put_class
    (hm:       header_mark withinfo)
    (cn:       classname)
    (fgs:      formal_generics)
    (inherits: inherit_clause)
    (pc: Proof_context.t)
    : unit =
  (** Analyze the class declaration [hm,cn,fgs,inherits] and add or update the
      corresponding class.  *)
  assert (Proof_context.is_global pc);
  let ft = Proof_context.feature_table pc in
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
  Inherit.inherit_parents idx inherits pc



let assertion_list (lst:compound) (context:Context.t): term list =
  List.map (fun e -> Typer.boolean_term e context) lst


let result_term (lst:info_expression list) (context:Context.t): term * info =
  match lst with
    [] -> assert false
  | [e] -> begin
      match e.v with
        Binexp (Eqop, ExpResult,def) ->
          Typer.result_term
            (withinfo e.i def)
            context,
          e.i
      | _ ->
          raise Not_found
  end
  | _ -> raise Not_found




let put_function
    (fn:       feature_name withinfo)
    (tvs:      Tvars.t)
    (argnames: int array)
    (sign:     Sign.t)
    (body:     Feature.body)
    (pc:       Proof_context.t): unit =
  assert (Tvars.count tvs = 0);  (* only formal generics, no untyped *)
  let ft = Proof_context.feature_table pc in
  try
    let idx = Feature_table.find_with_signature fn.v tvs sign ft in
    let inh =
      Feature_table.is_public ft && not (Feature_table.is_feature_public idx ft)
    and is_ghost = Sign.is_ghost sign
    in
    Feature_table.update_function idx fn.i is_ghost body ft;
    if inh then
      Inherit.inherit_to_descendants idx fn.i pc
  with Not_found ->
    let idx = Feature_table.count ft in
    Feature_table.add_function fn tvs argnames sign body ft;
    Inherit.inherit_to_descendants idx fn.i pc



let analyze_feature
    (fn: feature_name withinfo)
    (entlst: entities list withinfo)
    (rt: return_type)
    (is_func: bool)
    (bdy: feature_body option)
    (exp: info_expression option)
    (pc: Proof_context.t): unit =
  let pc1 = PC.push entlst rt false is_func pc in
  let context = Proof_context.context pc1 in
  let nms = Context.local_argnames context in
  let body =
    match bdy, exp with
      None, None ->
        (Feature.Spec.make_func_def nms None []),
        Feature.Empty
    | None, Some ie ->
        let term = Typer.result_term ie context in
        verify_preconditions term ie.i pc1;
        (Feature.Spec.make_func_def nms (Some term) []),
        Feature.Empty
    | Some bdy, None ->
        begin
          match bdy with
            None, Some Impbuiltin, None ->
              (Feature.Spec.make_func_def nms None []),
              Feature.Builtin
          | Some reqlst, Some Impbuiltin, None ->
              add_assumptions reqlst pc1;
              let pres = PC.assumptions pc1 in
              (Feature.Spec.make_func_spec nms pres []),
              Feature.Builtin
          | Some reqlst, None, None ->
              add_assumptions reqlst pc1;
              let pres = PC.assumptions pc1 in
              (Feature.Spec.make_func_spec nms pres []),
              Feature.Empty
          | None, None, Some enslst ->
              (try
                let term,info = result_term enslst context in
                verify_preconditions term info pc1;
                (Feature.Spec.make_func_def nms (Some term) []),
                Feature.Empty
              with Not_found ->
                not_yet_implemented fn.i
                  "functions not defined with `Result = ...'")
          | Some reqlst, None, Some enslst ->
              (try
                add_assumptions reqlst pc1;
                let pres = PC.assumptions pc1 in
                let term,info = result_term enslst context in
                verify_preconditions term info pc1;
                (Feature.Spec.make_func_def nms (Some term) pres),
                Feature.Empty
              with Not_found ->
                not_yet_implemented fn.i
                  "functions not defined with `Result = ...'")
          | None, Some Impdeferred, None ->
              (Feature.Spec.make_func_def nms None []),
              Feature.Deferred
          | Some reqlst, Some Impdeferred, None ->
              add_assumptions reqlst pc1;
              let pres = PC.assumptions pc1 in
              (Feature.Spec.make_func_spec nms pres []),
              Feature.Deferred
          | _ -> not_yet_implemented fn.i
                "functions with implementation/preconditions"
        end
    | _ -> assert false (* cannot happen *)
  in
  let argnames = Context.local_argnames context
  and sign     = Context.signature context
  and tvs      = Context.tvs context
  in
  put_function fn tvs argnames sign body pc






let analyze (ast: declaration list) (pc:Proof_context.t): unit =
  let context = Proof_context.context pc in
  let rec analyz (ast: declaration list): unit =
    let one_decl (d:declaration) =
      match d with
        Class_declaration (hm, cname, fgens, inherits) ->
          put_class hm cname fgens inherits pc
      | Named_feature (fn, entlst, rt, is_func, body, expr) ->
          analyze_feature fn entlst rt is_func body expr pc
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
  if Proof_context.is_interface_check pc then
    Proof_context.check_interface pc
