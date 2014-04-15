open Container
open Term
open Support


type backward_data = {bwd_ps:    term list;
                      bwd_tgt:   term;
                      bwd_simpl: bool}


type term_data = {term:     term;
                  nargs:    int;
                  nbenv:    int;
                  fwddat:   (term*term*int*bool) option;
                  bwddat:   backward_data}


type desc = {td:       term_data;
             used_fwd: IntSet.t}


type entry = {mutable prvd: Term_table0.t;
              mutable bwd:  Term_table0.t;
              mutable fwd:  Term_table0.t;
              mutable used_mp: IntSet.t;
              mutable count: int}

type proof_term = Proof_table.proof_term

type t = {base:     Proof_table.t;
          terms:    desc  Seq.sequence;
          mutable do_fwd: bool;
          mutable work:   int list;
          mutable entry:  entry;
          mutable stack:  entry list}


let empty_entry =
  let e = Term_table0.empty in
    {prvd=e; bwd=e; fwd=e;
     used_mp = IntSet.empty;
     count = 0}

let copied_entry (e:entry): entry =
  {prvd    = e.prvd;
   bwd     = e.bwd;
   fwd     = e.fwd;
   used_mp = e.used_mp;
   count   = e.count}


let make (imp_id:int) (all_id:int): t  =
  {base     = Proof_table.make imp_id all_id;
   terms    = Seq.empty ();
   do_fwd   = false;
   work     = [];
   entry    = empty_entry;
   stack    = []}

let is_using_forward (pc:t): bool =
  pc.do_fwd || Options.is_prover_local ()

let is_using_forced_forward (pc:t): bool =
  pc.do_fwd && not (Options.is_prover_local ())

let set_forward (pc:t): unit =
  pc.do_fwd <- true

let reset_forward (pc:t): unit =
  pc.do_fwd <- false

let stacked_counts (pc:t): int list =
  Proof_table.stacked_counts pc.base


let is_global (at:t): bool =
  Proof_table.is_global at.base

let is_local (at:t): bool =
  Proof_table.is_local at.base

let is_toplevel (at:t): bool =
  Proof_table.is_toplevel at.base

let nbenv (at:t): int = Proof_table.nbenv at.base

let nbenv_local (at:t): int = Proof_table.nbenv_local at.base

let count_0 (pc:t): int = Seq.count pc.terms

let count (pc:t): int = Proof_table.count pc.base

let is_consistent (pc:t): bool =
  count_0 pc = count pc

let count_previous (pc:t): int = Proof_table.count_previous pc.base
let count_global(pc:t): int = Proof_table.count_global pc.base

let depth (at:t): int = Proof_table.depth at.base

let all_id(at:t): int = Proof_table.all_id at.base

let imp_id(at:t): int = Proof_table.imp_id at.base

let term_orig (i:int) (pc:t): term * int =
  (** The [i]th proved term with the number of variables of its environment.
   *)
  assert (is_consistent pc);
  assert (i < count pc);
  Proof_table.term i pc.base

let term (i:int) (pc:t): term =
  (** The [i]th proved term in the current environment.
   *)
  assert (is_consistent pc);
  assert (i < count pc);
  Proof_table.local_term i pc.base



let split_implication (t:term) (pc:t): term * term =
  Proof_table.split_implication t pc.base

let split_all_quantified (t:term) (pc:t): int * int array * term =
  Proof_table.split_all_quantified t pc.base

let implication (a:term) (b:term) (pc:t): term =
  Proof_table.implication a b pc.base

let all_quantified (nargs:int) (names:int array) (t:term) (pc:t): term =
  Proof_table.all_quantified nargs names t pc.base

let all_quantified_outer(t:term) (pc:t): term  =
  Proof_table.all_quantified_outer t pc.base

let implication_chain (ps:term list) (tgt:term) (pc:t): term  =
  Proof_table.implication_chain ps tgt pc.base


let work (pc:t): int list = pc.work

let has_work (pc:t): bool = pc.work <> []


let is_forward_simplification (i:int) (pc:t): bool =
  assert (is_consistent pc);
  assert (i < count pc);
  let desc = Seq.elem pc.terms i in
  assert (Option.has desc.td.fwddat);
  let _,_,_,simpl = Option.value desc.td.fwddat in
  simpl



let used_forward (i:int) (pc:t): IntSet.t =
  assert (is_consistent pc);
  assert (i < count pc);
  (Seq.elem pc.terms i).used_fwd



let forward_data (t:term) (nargs:int) (pc:t): term * term * int * bool =
  (** The forward data of the term [t] with [nargs] arguments.

      The term is an applicable forward rule if it is an implication and
      the premise contains a complete prefix of the arguments and the
      implication is a simplification or an elimination rule
   *)
  let imp_id = nargs + imp_id pc       in
  let a,b = Term.binary_split t imp_id in
  if nargs = 0 then
    a, b, 0, true
  else begin
    let gp1   = Term.greatestp1_arg a nargs
    and avars = Term.bound_variables a nargs
    in
    if gp1 <> IntSet.cardinal avars then
      raise Not_found;
    let na = Term.nodes a
    and nb = Term.nodes b
    in
    let is_simpl = nb <= na in
    let ok =
      is_simpl ||
      let fvars_a = Term.free_variables a nargs
      and fvars_b = Term.free_variables b nargs
      in
      IntSet.exists (fun ia -> not (IntSet.mem ia fvars_b)) fvars_a
    in
    if ok then
      a, b, gp1, is_simpl
    else
      raise Not_found
  end







let analyze_backward (t:term) (nargs:int) (pc:t): backward_data =
  (** Analyze the schematic term [t] with [nargs] arguments as a backward
      rule.
   *)
  assert (0 < nargs);
  let imp_id = nargs + (imp_id pc) in
  let rec split
      (ps: (term*int*IntSet.t) list)
      (tgt:term)
      (max_nodes:int)
      (fvars:IntSet.t)
      : (term*int*IntSet.t) list * term =
    try
      let a,b = Term.binary_split tgt imp_id in
      let na  = Term.nodes a in
      let max_nodes =
        if max_nodes < na then na
        else max_nodes
      and fvars = IntSet.union fvars (Term.free_variables a nargs)
      in
      split ((a,max_nodes,fvars)::ps) b max_nodes fvars
    with Not_found ->
      ps, tgt
  in
  let rec ana_bwd
      (ps:(term*int*IntSet.t) list) (tgt: term)
      : term list * term * bool =
    match ps with
      [] ->
        [], tgt, true
    | (p,nmax,fvars)::ps_rest ->
        let ntgt = Term.nodes tgt
        and avars_tgt, fvars_tgt = Term.split_variables tgt nargs
        in
        let is_simpl = nmax <= ntgt in
        let ok =
          (IntSet.cardinal avars_tgt) = nargs
            &&
          (is_simpl
         || IntSet.exists (fun i -> not (IntSet.mem i fvars)) fvars_tgt)
        in
        if not ok then
          let tgt = Term.binary imp_id p tgt in
          ana_bwd ps_rest tgt
        else
          (List.rev_map (fun (p,_,_) -> p) ps), tgt, is_simpl
  in
  let ps, tgt = split [] t 0  IntSet.empty in
  let ps, tgt, simpl = ana_bwd ps tgt
  in
  {bwd_ps = ps; bwd_tgt = tgt; bwd_simpl = simpl}




let analyze (t:term)  (pc:t): term_data =
  try
    let nargs, nms, t = Term.quantifier_split t (all_id pc) in
    if IntSet.cardinal (Term.bound_variables t nargs) <> nargs then
      raise Not_found;
    let fwd =
      try Some (forward_data t nargs pc)
      with Not_found -> None
    and bwd = analyze_backward t nargs pc
    in
    {term      = t;
     nargs     = nargs;
     nbenv     = nbenv pc;
     fwddat    = fwd;
     bwddat    = bwd}
  with Not_found ->
    (* Not a useful quantified statement *)
    let imp_id = (imp_id pc) in
    let fwd =
      try
        let a,b = Term.binary_split t imp_id in
        Some (a,b,0,true)
      with Not_found ->
        None
    in
    let ps, tgt = Term.split_implication_chain t imp_id in
    let bwd =
      {bwd_ps = List.rev ps; bwd_tgt = tgt; bwd_simpl = true}
    in
    {term   = t;
     nargs  = 0;
     nbenv  = nbenv pc;
     fwddat = fwd;
     bwddat = bwd}




let find (t:term) (pc:t): int =
  (** The index of the assertion [t].
   *)
  let sublst = Term_table0.unify_with t 0 (nbenv pc) pc.entry.prvd in
  match sublst with
    []          -> raise Not_found
  | [(idx,sub)] -> idx
  | _ -> assert false  (* cannot happen, all entries in [prvd] are unique *)



let has (t:term) (pc:t): bool =
  (** Is the term [t] already in the proof context [pc]?
   *)
  try
    let _ = find t pc in
    true
  with Not_found ->
    false




let add_new (t:term) (used_fwd:IntSet.t) (pc:t): unit =
  (** Add the new term [t] to the context [pc].

      Note: The term has to be added to the proof context outside
      this function
   *)
  let td = analyze t pc
  and idx = Seq.count pc.terms
  in
  let add_to_proved (): unit =
    pc.entry.prvd <-
      Term_table0.add t 0 td.nbenv idx pc.entry.prvd;
    Seq.push pc.terms {td=td; used_fwd = used_fwd}

  and add_to_forward (): unit =
    match td.fwddat with
      None ->
        ()  (* do nothing, not a valid forward rule *)
    | Some (a,b,gp1,_) ->
        pc.entry.fwd <-
          Term_table0.add a td.nargs td.nbenv idx pc.entry.fwd

  and add_to_backward (): unit =
    pc.entry.bwd <-
      Term_table0.add td.bwddat.bwd_tgt td.nargs td.nbenv idx pc.entry.bwd

  and add_to_work (): unit =
    pc.work <- idx::pc.work

  in
  add_to_proved   ();
  add_to_forward  ();
  add_to_backward ();
  add_to_work     ()





let add_mp (t:term) (i:int) (j:int) (pc:t): unit =
  assert (not (has t pc));
  if is_using_forward pc then begin
    let used_fwd = IntSet.union (used_forward i pc) (used_forward j pc) in
    pc.entry.used_mp <- IntSet.add j pc.entry.used_mp;
    Proof_table.add_mp t i j pc.base;
    add_new t used_fwd pc
  end else
    ()



let add_specialized_forward
    (t:term)
    (i:int) (args: term array) (pc:t): unit =
  (** Add the new term [t] which is a specialization of the term [i]
      specialized with the arguments [args] to the proof context [pc].
   *)
  assert (not (has t pc));
  let used_fwd = used_forward i pc in
  let used_fwd =
    if is_forward_simplification i pc then
      used_fwd
    else
      IntSet.add i used_fwd
  in
  Proof_table.add_specialize t i args pc.base;
  add_new t used_fwd pc




let specialized_forward
    (i:int)
    (sub:Term_sub.t)
    (nbenv_sub:int)
    (pc:t)
    : term * term  * term array =
  (** The antecedent, the consequent and the arguments of the term [i]
      specialized with the substitution [sub] which comes from an environment
      with [nbenv_sub] variables.

      Note: The results are all valid in the current environment!
   *)
  assert (is_consistent pc);
  assert (i < count pc);
  let td_imp    = (Seq.elem pc.terms i).td in
  assert (Option.has td_imp.fwddat);
  let nargs     = td_imp.nargs
  and a,b,gp1,_ = Option.value td_imp.fwddat in
  assert (gp1 <= nargs);
  assert (Term_sub.count sub = gp1);
  let nbenv_imp = Proof_table.nbenv_term i pc.base
  and nbenv     = nbenv pc
  in
  assert (nbenv_sub <= nbenv);
  assert (nbenv_imp <= nbenv);
  let args  = Term_sub.arguments gp1 sub in
  Array.iteri
    (fun i t -> args.(i) <- Term.up (nbenv-nbenv_sub) t)
    args;
  let a = Term.part_sub a nargs args (nbenv-nbenv_imp)
  and b = Term.part_sub b nargs args (nbenv-nbenv_imp)
  in
  let a = Term.down (nargs-gp1) a
  in
  let b =
    if gp1 < nargs then
      all_quantified (nargs-gp1) [||] b pc
    else
      b
  in
  a, b, args




let add_consequence (i:int ) (j:int) (sub:Term_sub.t) (pc:t): unit =
  (** Add the consequence of [i] and the implication [j]. The term [j] might
      be a schematic implication which has to be converted into a specific
      implication by using the substitution [sub].

      Note: [sub] comes from the enviroment of the term [i]!
   *)
  assert (is_consistent pc);
  assert (i < count pc);
  assert (j < count pc);
  let nbenv_sub = Proof_table.nbenv_term i pc.base in
  let a, b, args = specialized_forward j sub nbenv_sub pc in
  if has b pc then
    ()
  else if args = [||] then begin
    add_mp b i j pc
  end else begin
    let imp  = implication a b pc
    and idx  = count pc
    in
    add_specialized_forward imp j args pc;
    add_mp b i idx pc
  end




let add_consequences_premise (i:int) (td:term_data) (pc:t): unit =
  (** Add the consequences of the analyzed term [i] with data [td] by using
      the term as a premise for already available implications.
   *)
  assert (td.nbenv = (nbenv pc));
  let sublst = Term_table0.unify td.term td.nbenv pc.entry.fwd in
  let sublst = List.rev sublst in
  List.iter
    (fun (idx,sub) ->
      assert (is_consistent pc);
      assert (idx < count pc);
      add_consequence i idx sub pc)
    sublst





let add_consequences_implication (i:int) (td:term_data) (pc:t): unit =
  (** Add the consequences of the analyzed term [i] with data [td] by using
      the term as an implication and searching for a matching premises.
   *)
  match td.fwddat with
    None -> ()
  | Some (a,b,gp1,_) ->
      let sublst =
        Term_table0.unify_with a td.nargs td.nbenv pc.entry.prvd
      in
      let sublst = List.rev sublst in
      List.iter
        (fun (idx,sub) ->
          assert (is_consistent pc);
          assert (idx < count pc);
          add_consequence idx i sub pc)
        sublst




let add_consequences (i:int) (pc:t): unit =
  (** Add the consequences of the analyzed term [i] which are not yet in
      the proof context [pc] to the proof context and to the work items.
   *)
  let td = (Seq.elem pc.terms i).td
  in
  add_consequences_premise     i td pc;
  add_consequences_implication i td pc



let add_specialized_backward (idx:int) (sub:Term_sub.t) (pc:t): unit =
  (** Add the schematic rule [idx] substituted by [sub] to the
      proof context [pc].
   *)
  assert (is_consistent pc);
  assert (idx < count pc);
  assert (not (Term_sub.is_empty sub));
  let desc = Seq.elem pc.terms idx              in
  let td   = desc.td                            in
  assert (td.nargs = Term_sub.count sub);
  let args = Term_sub.arguments td.nargs sub    in
  let t    = Proof_table.local_term idx pc.base in
  let n,nms,t = split_all_quantified t pc       in
  assert (n = Array.length args);
  let t    = Term.apply t args                  in
  if not (has t pc) then begin
    Proof_table.add_specialize t idx args pc.base;
    add_new t desc.used_fwd pc;
    assert (is_consistent pc)
  end else
    ()



let add_assumption_or_axiom (t:term) (is_axiom: bool) (pc:t): int =
  (** Add the term [t] as an assumption or an axiom to the context [pc].
   *)
  assert (is_consistent pc);
  let idx = count pc
  and has = has t pc
  in
  if is_axiom then
    Proof_table.add_axiom t pc.base
  else
    Proof_table.add_assumption t pc.base;
  if not has then begin
    add_new t IntSet.empty pc
  end else
    Seq.push pc.terms {td = analyze t pc; used_fwd = IntSet.empty};
  idx






      (* Public functions *)


let add_assumption (t:term) (pc:t): int =
  (** Add the term [t] as an assumption to the context [pc].
   *)
  add_assumption_or_axiom t false pc



let add_axiom (t:term) (pc:t): int =
  (** Add the term [t] as an axiom to the context [pc].
   *)
  add_assumption_or_axiom t true pc




let close_step (pc:t): unit =
  assert (has_work pc);
  let i = List.hd pc.work in
  pc.work <- List.tl pc.work;
  add_consequences i pc



let close (pc:t): unit =
  let rec cls (n:int): unit =
    if n > 1000 then assert false;  (* 'infinite' loop detection *)
    if has_work pc then begin
      close_step pc;
      cls (n-1)
    end else
      ()
  in
  cls 0;
  assert (not (has_work pc));
  ()



let push (nbenv:int) (names:int array) (pc:t): unit =
  assert (let len = Array.length names in len=0 || len=nbenv);
  assert (not (has_work pc));
  Proof_table.push nbenv names pc.base;
  pc.entry.count <- Seq.count pc.terms;
  pc.stack <- (copied_entry pc.entry)::pc.stack



let pop (pc:t): unit =
  assert (is_local pc);
  assert (not (has_work pc));
  Proof_table.pop pc.base;
  pc.work  <- [];
  pc.entry <- List.hd pc.stack;
  pc.stack <- List.tl pc.stack;
  Seq.keep pc.terms pc.entry.count


let pop_keep (pc:t): unit =
  assert (is_local pc);
  assert (not (has_work pc));
  Proof_table.pop_keep pc.base;
  pc.stack <- List.tl pc.stack




let add_backward (t:term) (pc:t): unit =
  (** Add all backward rules which have [t] as a target to the context [pc].
   *)
  let sublst = Term_table0.unify t (nbenv pc) pc.entry.bwd in
  List.iter
    (fun (idx,sub) ->
      if Term_sub.is_empty sub then
        if is_using_forced_forward pc then
          pc.work <- idx :: pc.work
        else
          ()
      else
        add_specialized_backward idx sub pc)
    sublst



let pull_backward (t:term) (pc:t): int * term list =
  (** Find a backward rule for the target [t] in the context [pc], remove
      the rule as a backward rule and return the rule and the list of
      premises for the target.

      If the list of premises is empty then the target is identical with the
      returned rule. In case that no backward rule exists for the target
      then [Not_found] is raised.
   *)
  assert false


let discharged (i:int) (pc:t): term * proof_term =
  (** The [i]th term of the current environment with all local variables and
      assumptions discharged together with its proof term.
   *)
  Proof_table.discharged i pc.base


let add_proved (t:term) (pterm:proof_term) (pc:t): unit =
  if has t pc then
    ()
  else begin
    Proof_table.add_proved t pterm pc.base;
    add_new t IntSet.empty pc
  end


let backward_set (t:term) (pc:t): int list =
  let sublst = Term_table0.unify t (nbenv pc) pc.entry.bwd in
  List.fold_left
    (fun lst (idx,sub) ->
      if Term_sub.is_empty sub then
        idx::lst
      else
        lst)
    []
    sublst
