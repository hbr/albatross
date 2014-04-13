open Support
open Term


type kind =
    PAxiom
  | PDeferred
  | PNormal

type proof_term = Context.proof_term

exception Proof_found of int

type entry = {ens_lst: int list}

let empty_entry = {ens_lst = []}

type t = {context: Context.t;
          entry:   entry;
          stack:   entry list}



let make (c:Context.t): t =
  {context = c; entry = empty_entry; stack = []}





let analyze_body (info:info) (bdy: feature_body)
    : kind * compound * compound * compound =
  match bdy with
    _, _, None ->
      error_info info "Assertion must have an ensure clause"
  | rlst_opt, imp_opt, Some elst ->
      let rlst =
        match rlst_opt with
          None   -> []
        | Some l -> l
      and kind,is_do,clst =
        match imp_opt with
          None ->             PNormal,  false, []
        | Some Impdeferred -> PDeferred,false, []
        | Some Impbuiltin ->  PAxiom,   false, []
        | Some Impevent ->
            error_info info "Assertion cannot be an event"
        | Some (Impdefined (Some locs,is_do,cmp)) ->
            not_yet_implemented info "Local variables in assertions"
        | Some (Impdefined (None,is_do,cmp)) ->
            PNormal,is_do,cmp
      in
      if is_do then
        not_yet_implemented info "Assertions with do block"
      else
        kind, rlst, clst, elst



let get_term (ie: info_expression) (c:Context.t): term * term =
  let tn = Typer.boolean_term ie c in
  let t  = Context.expanded_term tn c in
  tn, t






let add_assumptions_or_axioms
    (lst:compound) (is_axiom:bool) (c:Context.t): int list =
  List.map
    (fun ie ->
      let tn,_ = get_term ie c in
      if is_axiom then
        Context.add_axiom tn c
      else
        Context.add_assumption tn c)
    lst


let add_assumptions (lst:compound) (c:Context.t): unit =
  let _ = add_assumptions_or_axioms lst false c in ()



let add_axioms (lst:compound) (c:Context.t): int list =
  add_assumptions_or_axioms lst true c



let add_proved (lst: (term*proof_term) list) (c:Context.t): unit =
  List.iter
    (fun (t,pterm) ->
      Context.add_proved t pterm c
    )
    lst




let print_local (c:Context.t): unit =
  Printf.printf "local assertions\n";
  Context.print_all_local_assertions c

let print_global (c:Context.t): unit =
  Printf.printf "global assertions\n";
  Context.print_global_assertions c;
  Printf.printf "\n"




let prove_term (t:term) (c:Context.t): int =
  let bwd_set = Context.backward_set t c in
  try
    List.iter
      (fun i ->
        Context.push_empty c;
        Printf.printf "using bwd rule %s\n"
          (Context.string_of_term (Context.assertion i c) c);
        assert false)
      bwd_set;
    raise Not_found
  with Proof_found idx ->
    Context.pop_keep_assertions c;
    idx






let rec prove_check (lst:compound) (c:Context.t): unit =
  List.iter
    (fun ie -> let _ = prove_expression ie true c in ())
    lst

and prove_ensure (lst:compound) (k:kind) (c:Context.t): (term*proof_term) list =
  let idx_lst =
    match k with
      PAxiom | PDeferred ->
        add_axioms lst c
    | PNormal ->
        List.map (fun ie -> prove_expression ie false c) lst
  in
  List.map (fun idx -> Context.discharged idx c) idx_lst

and prove_expression (ie:info_expression) (sub:bool) (c:Context.t): int =
  match ie.v with
    Expquantified (q,entlst,Expproof(rlst,imp_opt,elst)) ->
      begin
        match q with
          Universal ->
            if not sub then
              error_info ie.i "Proof expressions not allowed here";
            assert false  (* nyi: subproofs *)
        | Existential ->
            error_info ie.i "Only \"all\" allowed here"
      end
  | Expproof (rlst,imp_opt,elst) ->
      if not sub then
        error_info ie.i "Proof expressions not allowed here";
      assert false  (* nyi: subproofs *)
  | _ ->
      let tn,_ = get_term ie c in
      Printf.printf "try to prove %s\n" (Context.string_of_term tn c);
      prove_term tn c






let prove_assertion_feature
    (entlst:  entities list withinfo)
    (bdy:     feature_body)
    (c:       Context.t)
    : unit =
  Context.push entlst None c;
  let kind, rlst, clst, elst = analyze_body entlst.i bdy
  in
  add_assumptions rlst c;
  print_local c;
  prove_check clst c;
  let pair_lst = prove_ensure elst kind c in

  Context.pop c;
  add_proved pair_lst c;
  print_global c





let prove_and_store
    (entlst:  entities list withinfo)
    (bdy:     feature_body)
    (context: Context.t)
    : unit =
  prove_assertion_feature entlst bdy context
