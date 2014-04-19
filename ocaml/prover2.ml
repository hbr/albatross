open Container
open Support
open Term


type kind =
    PAxiom
  | PDeferred
  | PNormal

type proof_term = Context.proof_term

exception Proof_found of int

type t = {context: Context.t;
          mutable goal:  term;
          mutable stack: term list;
          mutable depth: int}


let start (t:term) (c:Context.t): t =
  {context=c; goal=t; stack=[]; depth=0}


let analyze_imp_opt
    (info:    info)
    (imp_opt: implementation option)
    : kind * compound =
  let kind,is_do,clst =
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
    kind, clst


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
      and kind,clst =
        analyze_imp_opt info imp_opt
      in
      kind, rlst, clst, elst




let untagged (ie: info_expression): info_expression =
  match ie.v with
    Taggedexp (tag,e) -> withinfo ie.i e
  | _                 -> ie

let get_term (ie: info_expression) (c:Context.t): term * term =
  let tn = Typer.boolean_term (untagged ie) c in
  let t  = Context.expanded_term tn c in
  tn, t



let string_of_term (t:term) (p:t): string =
  Context.string_of_term t p.context

let string_of_index (i:int) (p:t): string =
  assert (i < Context.count_assertions p.context);
  let t = Context.assertion i p.context in
  string_of_term t p


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


let print_pair (p:t): unit =
  Context.print_all_local_assertions p.context;
  Printf.printf "--------------------\n";
  let depth = Context.depth p.context in
  let prefix = String.make (2*(depth-1)) ' ' in
  Printf.printf "%s      %s\n\n" prefix (string_of_term p.goal p)

let split_implication (p:t): term * term =
  Context.split_implication p.goal p.context

let split_all_quantified (p:t): int * int array * term =
  Context.split_all_quantified p.goal p.context


let add_backward (p:t): unit =
  Context.add_backward p.goal p.context



let push (names:int array) (t:term) (p:t): unit =
  Context.push_untyped names p.context;
  p.stack <- p.goal::p.stack;
  p.goal  <- t;
  p.depth <- p.depth + 1


let push_empty (p:t): unit =
  push [||] p.goal p


let push_goal (t:term) (p:t): unit =
  push [||] t p


let pop (p:t): unit =
  assert (0 < p.depth);
  Context.pop p.context;
  p.goal  <- List.hd p.stack;
  p.stack <- List.tl p.stack;
  p.depth <- p.depth - 1


let rec pop_downto (i:int) (p:t): unit =
  assert (i <= p.depth);
  if p.depth = i then
    ()
  else begin
    pop p;
    pop_downto i p
  end


let discharge (idx:int) (p:t): int =
  (** Discharge the term [idx], pop one local context, insert the
      discharged term into the outer context and return the index
      of the discharged term in the outer context.
   *)
  assert (p.depth <> 0);
  let t,pterm = Context.discharged idx p.context in
  pop p;
  Context.add_proved t pterm p.context;
  Context.find_assertion t p.context


let rec discharge_downto (i:int) (idx:int) (p:t): int =
  (** Iterate 'pop' down to the stack level [i] starting by discharging
      the term [idx].
   *)
  assert (0 <= i);
  assert (i <= p.depth);
  if p.depth = i then
    idx
  else
    let idx = discharge idx p in
    discharge_downto i idx p


let check_goal (p:t): unit =
  try
    add_backward p;
    let idx = Context.find_assertion p.goal p.context in
    raise (Proof_found idx)
  with Not_found ->
    ()


let enter (p:t): unit =
  let rec do_implication (): unit =
    try
      let a,b = split_implication p in
      let _ = Context.add_assumption a p.context in
      p.goal <- b;
      check_goal p;
      do_implication ()
    with Not_found ->
      do_all_quantified ()
  and do_all_quantified (): unit =
    try
      let n,names,t = split_all_quantified p in
      assert (n = Array.length names);
      push names t p;
      check_goal p;
      do_implication ()
    with Not_found ->
      ()
  in
  do_implication ()




let rec prove_goal (p:t): unit =
  (** Prove the goal of [p] in a clean context (i.e. a context into which
      assumptions can be pushed).

      The function does not return. It either raises [Not_found] or
      [Proof_found idx] where [idx] points to the index of the goal
      in the context.

      Note that an arbitrary number of contexts can be pushed and [idx]
      points to an inner context. The caller has to pop the corresponding
      inner contexts and discharge the proved term.
   *)
  check_goal p;
  enter p;
  if Options.is_prover_backward () then
    let bwd_set = Context.backward_set p.goal p.context in
    print_pair p;
    Printf.printf "goal=%s, bwd_set={%s}\n"
      (string_of_term p.goal p)
      (String.concat "," (List.map string_of_int bwd_set));
    prove_alternatives bwd_set p;
    raise Not_found
  else
    raise Not_found

and prove_alternatives (bwds: int list) (p:t): unit =
  List.iter
    (fun i ->
      assert false)
    bwds

and prove_premises (ps:term list) (p:t): unit =
  (** Prove all premises [ps] of the goal of [p] and insert them one by one
      into the context.
   *)
  List.iter
    (fun t ->
      let depth = p.depth in
      push_goal t p;
      try
        prove_goal p
      with Proof_found idx ->
        let _ = discharge_downto depth idx p in
        ())
    ps







let prove_basic_expression (ie:info_expression) (c:Context.t): int =
  let tn,_ = get_term ie c in
  let p = start tn c in
  push_empty p;
  try
    prove_goal p;
    assert false  (* prove_goal shall never return *)
  with Proof_found idx ->
    Printf.printf "Trying to prove %s\n" (string_of_term tn p);
    print_pair p;
    Printf.printf "found a proof for %s (%d,%s), subgoal %s\n"
      (string_of_term tn p) idx (string_of_index idx p)
      (string_of_term p.goal p);
    discharge_downto 0 idx p
  | Not_found ->
      print_pair p;
      error_info ie.i "Cannot prove"



let rec prove_proof
    (kind:kind)
    (rlst: compound)
    (clst: compound)
    (elst: compound)
    (c:    Context.t)
    : unit =
  add_assumptions rlst c;
  prove_check clst c;
  let pair_lst = prove_ensure elst kind c in
  Context.pop c;
  add_proved pair_lst c


and prove_check (lst:compound) (c:Context.t): unit =
  List.iter
    (fun ie -> prove_check_expression ie c)
    lst

and prove_ensure
    (lst:compound)
    (k:kind)
    (c:Context.t)
    : (term*proof_term) list =
  let idx_lst =
    match k with
      PAxiom | PDeferred ->
        add_axioms lst c
    | PNormal ->
        List.map (fun ie -> prove_basic_expression ie c) lst
  in
  List.map (fun idx -> Context.discharged idx c) idx_lst

and prove_check_expression
    (ie:info_expression)
    (c:Context.t): unit =
  let ie = untagged ie in
  match ie.v with
    Expquantified (q,entlst,Expproof(rlst,imp_opt,elst)) ->
      begin
        match q with
          Universal ->
            let kind, clst =
              analyze_imp_opt
                entlst.i
                imp_opt
            in
            Context.push entlst None c;
            prove_proof kind rlst clst elst c
        | Existential ->
            error_info ie.i "Only \"all\" allowed here"
      end
  | Expproof (rlst,imp_opt,elst) ->
      let kind, clst = analyze_imp_opt ie.i imp_opt in
      Context.push_empty c;
      prove_proof kind rlst clst elst c
  | _ ->
      let _ = prove_basic_expression ie c in
      ()






let prove_and_store
    (entlst:  entities list withinfo)
    (bdy:     feature_body)
    (context: Context.t)
    : unit =
  let kind, rlst, clst, elst = analyze_body entlst.i bdy
  in
  Context.push entlst None context;
  prove_proof kind rlst clst elst context;
  print_global context
