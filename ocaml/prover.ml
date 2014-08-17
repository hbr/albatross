open Container
open Support
open Term
open Printf


exception Proof_found of int

type kind =
    PAxiom
  | PDeferred
  | PNormal

type proof_term = Context.proof_term

type entry = {mutable goal: term;
              mutable alter: bool; (* stack entry used for exploring
                                      alternatives *)
              nbenv:    int;
              used_gen: IntSet.t;  (* used non simplifying schematic rules
                                      to generate the goal *)
              used_bwd: IntSet.t   (* already used backward rules to
                                      generate the goal *)
            }

type t = {context: Context.t;
          mutable entry: entry;
          mutable beta:  bool;  (* goal already beta reduced? *)
          mutable stack: entry list;
          mutable depth: int;
          mutable trace_ctxt: bool;
          mutable trace: bool}


let start (t:term) (c:Context.t): t =
  let entry = {goal=t;
               alter= false;
               nbenv= 0;
               used_gen=IntSet.empty;
               used_bwd=IntSet.empty} in
  {context= c;
   entry  = entry;
   beta   = false;
   stack  = [];
   depth  = 0;
   trace_ctxt = true;
   trace  = Options.is_tracing_proof ()}


let analyze_imp_opt
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
        PDeferred,false, []
    | Some Impbuiltin ->
        if iface then
          error_info info "not allowed in interface file";
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


let analyze_body (info:info) (bdy: feature_body) (c:Context.t)
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
        analyze_imp_opt info imp_opt c
      in
      kind, rlst, clst, elst




let get_term (ie: info_expression) (c:Context.t): term =
  let t  = Typer.boolean_term ie c in
  let tn = Context.expanded_term t c in
  tn



let string_of_term (t:term) (p:t): string =
  Context.string_of_term t p.context

let string_of_index (i:int) (p:t): string =
  assert (i < Context.count_assertions p.context);
  let t = Context.assertion i p.context in
  string_of_term t p

let string_of_goal (p:t): string =
  string_of_term p.entry.goal p

let add_assumptions_or_axioms
    (lst:compound) (is_axiom:bool) (c:Context.t): int list =
  List.map
    (fun ie ->
      let tn = get_term ie c in
      if is_axiom then
        Context.add_axiom tn c
      else
        Context.add_assumption tn c)
    lst


let add_assumptions (lst:compound) (c:Context.t): unit =
  let _ = add_assumptions_or_axioms lst false c in ()



let add_axioms (lst:compound) (c:Context.t): int list =
  add_assumptions_or_axioms lst true c



let add_proved (lst: (term*proof_term*IntSet.t) list) (c:Context.t): unit =
  List.iter
    (fun (t,pterm,used_gen) ->
      Context.add_proved t pterm used_gen c
    )
    lst




let print_local (c:Context.t): unit =
  printf "local assertions\n";
  Context.print_all_local_assertions c

let print_global (c:Context.t): unit =
  printf "global assertions\n";
  Context.print_global_assertions c


let print_pair (p:t): unit =
  printf "\n";
  Context.print_all_local_assertions p.context;
  printf "--------------------------------------\n";
  let depth = Context.depth p.context in
  let prefix = String.make (2*(depth-1)) ' ' in
  printf "%s      %s\n" prefix (string_of_term p.entry.goal p)

let split_implication (p:t): term * term =
  Context.split_implication p.entry.goal p.context

let split_all_quantified (p:t): int * int array * term =
  Context.split_all_quantified p.entry.goal p.context


let add_backward (p:t): unit =
  Context.add_backward p.entry.goal p.context;
  if not p.beta then begin
    p.beta <- true;
    p.entry.goal <- Term.reduce p.entry.goal;
    Context.add_backward p.entry.goal p.context
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
  Context.push_untyped names p.context;
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
  Context.pop p.context;
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
  let t,pterm = Context.discharged idx p.context in
  assert ((Context.assertion idx p.context) = p.entry.goal);
  pop p;
  let used_gen_tgt =
    let cnt = Context.count_assertions p.context in
    IntSet.filter (fun j -> j < cnt) p.entry.used_gen
  in
  Context.add_proved t pterm used_gen_tgt p.context;
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
    let idx = Context.find_assertion p.entry.goal p.context in
    raise (Proof_found idx)
  with Not_found ->
    ()


let enter (p:t): unit =
  let rec do_implication (): unit =
    try
      let a,b = split_implication p in
      let _ = Context.add_assumption a p.context in
      p.entry.goal <- b;
      check_goal p;
      do_implication ()
    with Not_found ->
      do_all_quantified ()
  and do_all_quantified (): unit =
    try
      let n,names,t = split_all_quantified p in
      assert (n = Array.length names);
      push_context names t p;
      check_goal p;
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
  enter p;
  if p.trace && p.trace_ctxt then begin
    if not (Options.is_tracing_proof ()) then
      print_global p.context;
    print_pair p;
    p.trace_ctxt <- false
  end;
  if Options.is_prover_backward () then
    let bwd_lst = Context.backward_set p.entry.goal p.context in
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
      let ps, used_gen = Context.backward_data idx p.context in
      let imp = Context.assertion idx p.context in
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
        let idx_tgt = Context.find_assertion goal p.context
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







let prove_basic_expression (ie:info_expression) (c:Context.t): int =
  let t = get_term ie c in
  let rec prove (retry:bool): int =
    let p = start t c in
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
          Context.get_trace_info p.context;
          p.trace <- true;
          Context.print_global_assertions p.context;
          prove true
        end else begin
          error_info ie.i "Cannot prove"
        end
  in
  prove false


let prove_ensure
    (lst:compound)
    (k:kind)
    (c:Context.t)
    : (term*proof_term*IntSet.t) list =
  let idx_lst =
    match k with
      PAxiom | PDeferred ->
        add_axioms lst c
    | PNormal ->
        List.map (fun ie -> prove_basic_expression ie c) lst
  in
  List.map
    (fun idx ->
      let t,pterm = Context.discharged idx c in
      t, pterm, IntSet.empty)
    idx_lst



let rec make_proof
    (entlst: entities list withinfo)
    (kind:kind)
    (rlst: compound)
    (clst: compound)
    (elst: compound)
    (c:    Context.t)
    : unit =
  let prove_check_expression
      (ie:info_expression)
      (c:Context.t): unit =
    match ie.v with
      Expquantified (q,entlst,Expproof(rlst,imp_opt,elst)) ->
        begin
          match q with
            Universal ->
              let kind, clst =
                analyze_imp_opt entlst.i imp_opt c
              in
              make_proof entlst kind rlst clst elst c
          | Existential ->
              error_info ie.i "Only \"all\" allowed here"
        end
    | Expproof (rlst,imp_opt,elst) ->
        let kind, clst = analyze_imp_opt ie.i imp_opt c in
        make_proof (withinfo UNKNOWN []) kind rlst clst elst c
    | _ ->
        let _ = prove_basic_expression ie c in
        ()
  in
  Context.push entlst None c;
  add_assumptions rlst c;
  List.iter (fun ie -> prove_check_expression ie c) clst;
  let pair_lst = prove_ensure elst kind c in
  Context.pop c;
  add_proved pair_lst c




let prove_and_store
    (entlst:  entities list withinfo)
    (bdy:     feature_body)
    (context: Context.t)
    : unit =
  let kind, rlst, clst, elst = analyze_body entlst.i bdy context
  in
  make_proof entlst kind rlst clst elst context;
