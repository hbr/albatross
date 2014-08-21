open Container
open Support
open Term
open Printf


exception Proof_found of int

type kind =
    PAxiom
  | PDeferred
  | PNormal

type proof_term = Proof_context.proof_term

type entry = {mutable goal: term;
              mutable alter: bool; (* stack entry used for exploring
                                      alternatives *)
              nbenv:    int;
              used_gen: IntSet.t;  (* used non simplifying schematic rules
                                      to generate the goal *)
              used_bwd: IntSet.t   (* already used backward rules to
                                      generate the goal *)
            }

type t = {pc: Proof_context.t;
          mutable entry: entry;
          mutable beta:  bool;  (* goal already beta reduced? *)
          mutable stack: entry list;
          mutable depth: int;
          mutable trace_ctxt: bool;
          mutable trace: bool}


let context (p:t): Context.t = Proof_context.context p.pc

let start (t:term) (pc:Proof_context.t): t =
  let entry = {goal=t;
               alter= false;
               nbenv= 0;
               used_gen=IntSet.empty;
               used_bwd=IntSet.empty} in
  {pc     = pc;
   entry  = entry;
   beta   = false;
   stack  = [];
   depth  = 0;
   trace_ctxt = true;
   trace  = Options.is_tracing_proof ()}


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




let get_term (ie: info_expression) (pc:Proof_context.t): term =
  let c = Proof_context.context pc in
  let t  = Typer.boolean_term ie c in
  let tn = Context.expanded_term t c in
  tn



let string_of_term (t:term) (p:t): string =
  Context.string_of_term t (context p)

let string_of_index (i:int) (p:t): string =
  assert (i < Proof_context.count p.pc);
  let t = Proof_context.term i p.pc in
  string_of_term t p

let string_of_goal (p:t): string =
  string_of_term p.entry.goal p

let add_assumptions_or_axioms
    (lst:compound) (is_axiom:bool) (pc:Proof_context.t): int list =
  let res =
    List.map
      (fun ie ->
        let tn = get_term ie pc in
        if is_axiom then
          Proof_context.add_axiom tn pc
        else
          Proof_context.add_assumption tn pc)
    lst
  in
  Proof_context.close_assumptions pc;
  res

let add_assumptions (lst:compound) (pc:Proof_context.t): unit =
  let _ = add_assumptions_or_axioms lst false pc in ()



let add_axioms (lst:compound) (pc:Proof_context.t): int list =
  add_assumptions_or_axioms lst true pc


let add_assumption (t:term) (p:t): unit =
  let _ = Proof_context.add_assumption t p.pc in ()

let close_assumptions (p:t): unit =
  Proof_context.close_assumptions p.pc


let add_proved
    (defer: bool)
    (owner: int)
    (lst: (term*proof_term) list)
    (pc:Proof_context.t)
    : unit =
  Proof_context.add_proved_list defer owner lst pc




let print_local (pc:Proof_context.t): unit =
  printf "local assertions\n";
  Proof_context.print_all_local_assertions pc

let print_global (pc:Proof_context.t): unit =
  printf "global assertions\n";
  Proof_context.print_global_assertions pc


let print_pair (p:t): unit =
  printf "\n";
  print_local p.pc;
  printf "--------------------------------------\n";
  let depth = Proof_context.depth p.pc in
  let prefix = String.make (2*(depth-1)) ' ' in
  printf "%s      %s\n" prefix (string_of_term p.entry.goal p)


let split_implication (p:t): term * term =
  Proof_context.split_implication p.entry.goal p.pc

let split_all_quantified (p:t): int * int array * term =
  Proof_context.split_all_quantified p.entry.goal p.pc


let add_backward (p:t): unit =
  Proof_context.add_backward p.entry.goal p.pc;
  if not p.beta then begin
    p.beta <- true;
    p.entry.goal <- Term.reduce p.entry.goal;
    Proof_context.add_backward p.entry.goal p.pc
  end


let has_duplicate_goal (p:t): bool =
  let rec has_dup (i:int) (stack: entry list): bool =
    match stack with
      [] -> false
    | e::stack ->
        assert (e.nbenv <= p.entry.nbenv);
        if e.nbenv < p.entry.nbenv then
          false
        else if e.alter && p.entry.goal = e.goal then begin
          true
        end else
          has_dup (i+1) stack
  in
  has_dup 0 p.stack

let push
    (names:int array)
    (t:term)
    (used_gen:IntSet.t)
    (used_bwd:IntSet.t)
    (p:t): unit =
  let nbenv = p.entry.nbenv + Array.length names in
  Proof_context.push_untyped names p.pc;
  p.stack <- p.entry :: p.stack;
  p.entry <- {goal=t; alter=false; nbenv=nbenv;
              used_gen=used_gen; used_bwd=used_bwd};
  p.depth <- p.depth + 1


let push_context (names:int array) (t:term) (p:t): unit =
  push names t IntSet.empty IntSet.empty p


let push_empty (p:t): unit =
  push [||] p.entry.goal p.entry.used_gen p.entry.used_bwd p


let push_goal (t:term) (used_gen:IntSet.t) (p:t): unit =
  push [||] t used_gen p.entry.used_bwd p

let push_alternative (idx:int) (p:t): unit =
  let used_bwd = IntSet.add idx p.entry.used_bwd in
  p.entry.alter <- true;
  push [||] p.entry.goal p.entry.used_gen used_bwd p


let pop (p:t): unit =
  assert (0 < p.depth);
  Proof_context.pop p.pc;
  p.entry <- List.hd p.stack;
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
  let t,pterm = Proof_context.discharged idx p.pc in
  assert ((Proof_context.term idx p.pc) = p.entry.goal);
  pop p;
  let used_gen_tgt =
    let cnt = Proof_context.count p.pc in
    IntSet.filter (fun j -> j < cnt) p.entry.used_gen
  in
  Proof_context.add_proved false (-1) t pterm used_gen_tgt p.pc;
  Proof_context.find t p.pc


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
    let idx = Proof_context.find p.entry.goal p.pc in
    raise (Proof_found idx)
  with Not_found ->
    ()


let enter (p:t): unit =
  let rec do_implication (): unit =
    try
      let a,b = split_implication p in
      add_assumption a p;
      p.entry.goal <- b;
      do_implication ()
    with Not_found ->
      close_assumptions p;
      check_goal p;
      do_all_quantified ()
  and do_all_quantified (): unit =
    try
      let n,names,t = split_all_quantified p in
      assert (n = Array.length names);
      push_context names t p;
      do_implication ()
    with Not_found ->
      ()
  in
  do_implication ()


let prefix (p:t): string =
  String.make (2*p.depth) ' '


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
  (*add_backward p;*)
  enter p;
  if p.trace && p.trace_ctxt then begin
    if not (Options.is_tracing_proof ()) then
      print_global p.pc;
    print_pair p;
    p.trace_ctxt <- false
  end;
  if Options.is_prover_backward () then
    let bwd_lst = Proof_context.backward_set p.entry.goal p.pc in
    let bwd_lst =
      List.filter
        (fun idx -> not (IntSet.mem idx p.entry.used_bwd))
        bwd_lst
    in
    if has_duplicate_goal p then
      ()
    else
      prove_alternatives bwd_lst p;
    raise Not_found
  else
    raise Not_found

and prove_alternatives (bwds: int list) (p:t): unit =
  if p.trace then begin
    let n = List.length bwds in
    printf "%strying %d alternative(s)\n"
      (prefix p) n
  end;
  List.iteri
    (fun i idx ->
      let ps, used_gen = Proof_context.backward_data idx p.pc in
      let imp = Proof_context.term idx p.pc in
      let goal  = p.entry.goal
      and depth = p.depth in
      try
        if p.trace then begin
          let n    = List.length bwds
          and pre  = (prefix p)
          and tstr = string_of_term imp p
          in
          if n=1 then
            (assert (i=0);
            printf "%susing  %d %s\n" pre idx tstr)
          else
            printf "%salternative %d: %d %s\n" pre i idx tstr;
        end;
        push_alternative idx p;
        prove_premises ps used_gen p;
        (* all premises succeeded, i.e. the target is in the context *)
        let idx_tgt = Proof_context.find goal p.pc
        (*let idx_tgt =
          try Context.find_assertion goal p.context
          with Not_found -> assert false*)
        in
        let idx_tgt = discharge idx_tgt p in
        if p.trace then
          printf "%s... succeeded\n" (prefix p);
        raise (Proof_found idx_tgt)
      with Not_found ->
        pop_downto depth p;
        if p.trace then
          printf "%s... failed\n" (prefix p))
    bwds

and prove_premises (ps:term list) (used_gen: IntSet.t) (p:t): unit =
  (** Prove all premises [ps] of the goal of [p] coming from a backward
      rule with the set of used general rules [used_gen] and insert them
      one by one into the context.
   *)
  (*assert (not (IntSet.is_empty used_gen));*)
  let ngoal = Term.nodes p.entry.goal in
  List.iteri
    (fun i t ->
      let depth = p.depth in
      let nt = Term.nodes t in
      let used_gen =
        if nt <= ngoal then
          p.entry.used_gen
        else
          let inter = IntSet.inter p.entry.used_gen used_gen in
          if not (IntSet.is_empty inter) then begin
            raise Not_found
          end;
          IntSet.union p.entry.used_gen used_gen
      in
      if p.trace then begin
        let n    = List.length ps
        and pre  = prefix p
        and tstr = string_of_term t p
        in
        if n=1 then
          printf "%spremise: %s\n" pre tstr
        else
          printf "%spremise %d: %s\n" pre i tstr
      end;
      push_goal t used_gen p;
      try
        prove_goal p
      with Proof_found idx ->
        let _ = discharge_downto depth idx p in
        ())
    ps







let prove_basic_expression (ie:info_expression) (pc:Proof_context.t): int =
  let t = get_term ie pc in
  let rec prove (retry:bool): int =
    let p = start t pc in
    push_empty p;
    try
      prove_goal p;
      assert false  (* prove_goal shall never return *)
    with Proof_found idx ->
      discharge_downto 0 idx p
    | Not_found ->
        if not retry && not p.trace && Options.is_tracing_failed_proof ()
        then begin
          pop_downto 0 p;
          Options.set_trace_proof ();
          Proof_context.get_trace_info p.pc;
          p.trace <- true;
          Proof_context.print_global_assertions p.pc;
          prove true
        end else begin
          error_info ie.i "Cannot prove"
        end
  in
  prove false


let prove_ensure
    (lst:compound)
    (k:kind)
    (pc:Proof_context.t)
    : (term*proof_term) list =
  let idx_lst =
    match k with
      PAxiom | PDeferred ->
        add_axioms lst pc
    | PNormal ->
        List.map (fun ie -> prove_basic_expression ie pc) lst
  in
  List.map
    (fun idx ->
      let t,pterm = Proof_context.discharged idx pc in
      t,pterm)
    idx_lst



let rec make_proof
    (i:int)
    (entlst: entities list withinfo)
    (kind: kind)
    (rlst: compound)
    (clst: compound)
    (elst: compound)
    (pc:   Proof_context.t)
    : unit =
  let prove_check_expression (ie:info_expression): unit =
    let c = Proof_context.context pc in
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
  Proof_context.push entlst pc;
  let defer, owner =
    (match kind with PDeferred ->
      assert (i=0);
      Proof_context.check_deferred pc;
      true
    | _ ->
        false),
    Proof_context.owner pc
  in
  add_assumptions rlst pc;
  List.iter (fun ie -> prove_check_expression ie) clst;
  let pair_lst = prove_ensure elst kind pc in
  Proof_context.pop pc;
  add_proved defer owner pair_lst pc




let prove_and_store
    (entlst:  entities list withinfo)
    (bdy:     feature_body)
    (pc: Proof_context.t)
    : unit =
  let c = Proof_context.context pc in
  let kind, rlst, clst, elst = analyze_body 0 entlst.i bdy c
  in
  make_proof 0 entlst kind rlst clst elst pc;
