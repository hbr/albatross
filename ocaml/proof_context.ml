open Container
open Term
open Support
open Printf


type simpl_data = int * int (* #nodes, level *)

type slot_data = {ndown:int;
                  sprvd: int TermMap.t}


type backward_data = {ps:        (term*bool) list;
                      ps_set:    TermSet.t;
                      tgt:       term}


type term_data = {
    term:     term;  (* inner term [if nargs<>0] *)
    nargs:    int;
    nbenv:    int;
    fwddat:   (term*term*int*bool*bool) option; (* a, b, gp1, simpl, elim *)
    bwddat:   backward_data option}


type desc = {td:       term_data;
             used_gen: IntSet.t}


type entry = {mutable prvd:  Term_table.t;  (* all proved terms *)
              mutable prvd2: Term_table.t;  (* as schematic terms *)
              mutable bwd:   Term_table.t;
              mutable fwd:   Term_table.t;
              mutable slots: slot_data array;
              mutable used_fwd: IntSet.t;
              mutable count: int}

type proof_term = Proof_table.proof_term

type gdesc = {mutable pub: bool;
              mdl: int;
              mutable defer: bool}

type t = {base:     Proof_table.t;
          terms:    desc  Seq.t;
          gseq:     gdesc Seq.t;
          mutable do_fwd: bool;
          mutable work:   int list;
          mutable entry:  entry;
          mutable stack:  entry list;
          mutable trace:  bool}


let context (pc:t): Context.t = Proof_table.context pc.base

let module_table (pc:t): Module_table.t =
  let c = context pc in
  Context.module_table c

let feature_table (pc:t): Feature_table.t =
  let c = context pc in
  Context.feature_table c

let class_table (pc:t): Class_table.t =
  let c = context pc in
  Context.class_table c

let is_private (pc:t): bool = Proof_table.is_private pc.base
let is_public  (pc:t): bool = Proof_table.is_public  pc.base
let is_interface_use   (pc:t): bool = Proof_table.is_interface_use  pc.base
let is_interface_check (pc:t): bool = Proof_table.is_interface_check  pc.base

let add_used_module (name:int*int list) (used:IntSet.t) (pc:t): unit =
  Proof_table.add_used_module name used pc.base

let add_current_module (name:int) (used:IntSet.t) (pc:t): unit =
  Proof_table.add_current_module name used pc.base

let set_interface_check (pub_used:IntSet.t) (pc:t): unit =
  Proof_table.set_interface_check pub_used pc.base



let depth (pc:t): int =
  let res = Context.depth (context pc) in
  assert (res = List.length pc.stack);
  res

let make_entry () =
  let e = Term_table.empty in
    {prvd=e; prvd2=e; bwd=e; fwd=e;
     slots = Array.make 1 {ndown = 0; sprvd = TermMap.empty};
     used_fwd = IntSet.empty;
     count = 0}

let copied_entry (e:entry): entry =
  {prvd     = e.prvd;
   prvd2    = e.prvd2;
   bwd      = e.bwd;
   fwd      = e.fwd;
   slots    = e.slots;
   used_fwd = e.used_fwd;
   count    = e.count}


let get_trace_info (pc:t): unit =
  pc.trace <- Options.is_tracing_proof () && Options.trace_level () > 0



let make (): t  =
  let res =
    {base     = Proof_table.make ();
     terms    = Seq.empty ();
     gseq     = Seq.empty ();
     do_fwd   = false;
     work     = [];
     entry    = make_entry ();
     stack    = [];
     trace    = false}
  in
  get_trace_info res;
  res


let is_using_forward (pc:t): bool =
  pc.do_fwd || Options.is_prover_forward ()

let is_using_forced_forward (pc:t): bool =
  pc.do_fwd && not (Options.is_prover_forward ())

let set_forward (pc:t): unit =
  pc.do_fwd <- true

let reset_forward (pc:t): unit =
  pc.do_fwd <- false


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


let is_assumption (i:int) (pc:t): bool =
  assert (i < count pc);
  Proof_table.is_assumption i pc.base


let split_implication (t:term) (pc:t): term * term =
  Proof_table.split_implication t pc.base

let split_all_quantified (t:term) (pc:t): int * int array * term =
  Proof_table.split_all_quantified t pc.base

let split_some_quantified (t:term) (pc:t): int * int array * term =
  Proof_table.split_some_quantified t pc.base

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

let is_used_forward (i:int) (pc:t): bool =
  (** Has the rule [i] already been used as a forward rule in the proof
      context [pc]?
   *)
  assert (i < count pc);
  IntSet.mem i pc.entry.used_fwd


let string_of_term (t:term) (pc:t): string =
  Context.string_of_term t 0 (context pc)


let string_of_term_anon (t:term) (nb:int) (pc:t): string =
  Context.string_of_term t nb (context pc)



let term_data (i:int) (pc:t): term_data =
  (Seq.elem i pc.terms).td

let used_schematic (i:int) (pc:t): IntSet.t =
  assert (is_consistent pc);
  assert (i < count pc);
  (Seq.elem i pc.terms).used_gen



let term_level (t:term) (nb:int) (pc:t): int =
  let ft = feature_table pc in
  let nb = nb + nbenv pc in
  Feature_table.term_level t nb ft



let simplification_data (t:term) (nargs:int) (pc:t): simpl_data =
  let ft = feature_table pc in
  let nargs = nargs + nbenv pc in
  let t_exp = Feature_table.expand_term t nargs ft in
  Term.nodes t_exp, 0

let is_sd_simpler ((na,la):simpl_data) ((nb,lb):simpl_data): bool =
  na <= nb

let is_simpler (a:term) (b:term) (nargs:int) (pc:t): bool =
  is_sd_simpler (simplification_data a nargs pc) (simplification_data b nargs pc)



let forward_data
    (t:term) (nargs:int) (elim:bool) (pc:t)
    : term * term * int * bool * bool =
  (** The forward data of the term [t] with [nargs] arguments. The [elim] flag
      specifies if the term comes from a partially applied elimination rule.

      The term is an applicable forward rule if it is an implication and
      the premise contains a complete prefix of the arguments and the
      implication is a simplification or an elimination rule
   *)
  assert (not elim || nargs > 0);
  let imp_id = nargs + imp_id pc       in
  let a,b = Term.binary_split t imp_id in
  if nargs = 0 then
    a, b, 0, (Term.nodes b) <= (Term.nodes a), elim
  else begin
    let gp1   = Term.greatestp1_arg a nargs
    and avars = Term.bound_variables a nargs
    in
    if gp1 <> IntSet.cardinal avars then
      raise Not_found;
    let is_simpl = is_simpler b a nargs pc in
    let elim =
      if is_simpl  then false
      else if elim then true
      else
        let fvars_a = Term.free_variables a nargs
        and fvars_b = Term.free_variables b nargs
        in
        IntSet.exists (fun ia -> not (IntSet.mem ia fvars_b)) fvars_a
    in
    if is_simpl || elim  then
      a, b, gp1, is_simpl, elim
    else
      raise Not_found
  end




let premise_list_to_set (ts: (term*bool) list): TermSet.t =
  List.fold_left (fun set (t,_) -> TermSet.add t set) TermSet.empty ts




let backward_simpl (ps:term list) (tgt:term) (nargs:int) (pc:t): (term*bool) list =
  (* Analyze the premises of a backward rule and add the information if they
     are not more complicated than the target. More complicated means a higher
     level or more nodes. *)
  let sd_tgt = simplification_data tgt nargs pc in
  List.rev_map
    (fun p ->
      let sd_p = simplification_data p nargs pc in
      let simpl =  is_sd_simpler sd_p sd_tgt
      in
      p,simpl
    )
    ps



let backward_tail (ps:term list) (tgt:term) (nargs:int) (pc:t): term list * term =
  assert (0 < nargs);
  let imp_id = nargs + imp_id pc in
  let rec tail (ps:term list) (tgt:term) (avars_tgt:IntSet.t): term list * term =
    assert (0 < nargs);
    match ps with
      [] -> ps, tgt
    | p::rest ->
        let ntgt = Term.nodes tgt in
        if ntgt = 1 || IntSet.cardinal avars_tgt < nargs then
          let avars = IntSet.union avars_tgt (Term.bound_variables p nargs) in
          let tgt = Term.binary imp_id p tgt in
          tail rest tgt avars
        else
          ps, tgt
  in
  tail ps tgt (Term.bound_variables tgt nargs)



let split_backward (t:term) (nargs:int) (pc:t): (term*bool) list * term =
  (* Split the term [t] into a list of premises and a target and indicates if
     the term applied as a backward rule is simplifying. A backward rule is
     simplifying if all premises are not more complicated than the target. More
     complicated means more nodes or a higher level.

     [t] is the implication chain (degenerate case [t=z])

         a => b => c => d => ... => z

     The chain is splitted into

         [c,b,a], d=>...=>z

     such that [d=>...=>z] is the shortest tail which contains all [nargs]
     variables and is not a single variable (no catchall).
   *)
  let imp_id = nargs + imp_id pc in
  let ps,tgt = Term.split_implication_chain t imp_id in
  let ps,tgt =
    if nargs = 0 then ps,tgt
    else backward_tail ps tgt nargs pc
  in
  let ps = backward_simpl ps tgt nargs pc in
  ps, tgt




let analyze_backward (t:term) (nargs:int) (pc:t): backward_data option =
  (** Analyze the schematic term [t] with [nargs] arguments as a backward
      rule.
   *)
  assert (0 < nargs);
  let ps, tgt = split_backward t nargs pc in
  match ps with
    [] -> None
  | _::_ ->
      let ps_set = premise_list_to_set ps in
      Some {ps = ps; ps_set = ps_set; tgt = tgt}




let analyze (t:term) (elim:bool) (pc:t): term_data =
  try
    let nargs, nms, t = Term.quantifier_split t (all_id pc) in
    if IntSet.cardinal (Term.bound_variables t nargs) <> nargs then
      raise Not_found;
    let fwd =
      try Some (forward_data t nargs elim pc)
      with Not_found -> None
    and bwd = analyze_backward t nargs pc
    in
    {term      = t;
     nargs     = nargs;
     nbenv     = nbenv pc;
     fwddat    = fwd;
     bwddat    = bwd}
  with Not_found ->
    (* Not a quantified assertion or not a useful quantified assertion *)
    let imp_id = (imp_id pc) in
    let fwd =
      try
        let a,b = Term.binary_split t imp_id      in
        let simpl = is_simpler b a 0 pc in
        Some (a,b,0,simpl,elim)
      with Not_found ->
        None
    in
    let ps,tgt = split_backward t 0 pc in
    let bwd =
      match ps with
        [] -> None
      | _::_ ->
          let set = premise_list_to_set ps in
          Some {ps = ps; ps_set = set; tgt = tgt}
    in
    {term   = t;
     nargs  = 0;
     nbenv  = nbenv pc;
     fwddat = fwd;
     bwddat = bwd}


let find_slot (t:term) (pc:t): int * term =
  let least_free = Term.least_free t
  and nslots = Array.length pc.entry.slots in
  let i = ref 0 in
  while !i < nslots
      && least_free < pc.entry.slots.(!i).ndown
  do i:=!i+1 done;
  assert (!i<nslots);
  !i,
  Term.down pc.entry.slots.(!i).ndown t


let find_in_slot (t:term) (pc:t): int =
  let i, ti = find_slot t pc in
  TermMap.find ti pc.entry.slots.(i).sprvd


let find_in_tab (t:term) (pc:t): int =
  (** The index of the assertion [t].
   *)
  let sublst = Term_table.unify_with t 0 (nbenv pc) pc.entry.prvd in
  match sublst with
    []          -> raise Not_found
  | [(idx,sub)] -> idx
  | _ -> assert false  (* cannot happen, all entries in [prvd] are unique *)


let find (t:term) (pc:t): int = find_in_tab t pc


let find_witness (t:term) (nargs:int) (pc:t): int * Term_sub.t =
  (** The index and substitution of the assertion which can be used as a
      witness for the assertion [some(a,b,...) t]. The substitution contains
      the variable substitutions for [a,b,...] valid in the environment of the
      found assertion.*)
  let sublst = Term_table.unify_with t nargs (nbenv pc) pc.entry.prvd in
  match sublst with
    []          -> raise Not_found
  | [x] -> x
  | _ -> assert false  (* cannot happen, all entries in [prvd] are unique *)



let has (t:term) (pc:t): bool =
  (** Is the term [t] already in the proof context [pc]?
   *)
  try
    let _ = find t pc in
    true
  with Not_found ->
    false




let find_stronger (t:term) (pc:t): int =
  (** The index of the assertion which is stronger as [t] (or equivalent).

      If [t] is schematic, a stronger or equivalent assertion is schematic
      with the a less or equal number of arguments and can be transformed into
      [t] by using an injective substitution.

      If [t] is not schematic an equivalent assertion is identical.

      Note: The term [t] must be valid in the current context!
   *)

  let n, _, t0 =
    try
      split_all_quantified t pc
    with Not_found ->
      0, [||], t
  in
  let submap = Term_table.unify t0 (n+(nbenv pc)) pc.entry.prvd2 in
  let submap =
    List.filter
      (fun (idx,sub) ->
        n >= (Seq.elem idx pc.terms).td.nargs && Term_sub.is_injective sub)
      submap
  in match submap with
    []        -> raise Not_found
  | [idx,sub] -> idx
  | _         -> assert false



let has_stronger (t:term) (pc:t): bool =
  (** Is there a term stronger as [t] (or equivalent) already in the proof
      context [pc]?

      Note: The term [t] must be valid in the current context!
   *)
  try
    let _ = find_stronger t pc in
    true
  with Not_found ->
    false


let print_assertions
    (prefix:string)
    (level:int)
    (c0:int)
    (c1:int)
    (global:bool)
    (pc:t): unit =
  let c = context pc in
  let argsstr = Context.ith_arguments_string level c in
  if argsstr <> "" then
    printf "%s%s\n" prefix argsstr;
  let rec print (i:int): unit =
    if i = c1 then ()
    else begin
      let t        = term i pc
      and is_hypo  = is_assumption   i pc
      and is_used  = is_used_forward i pc
      and used_gen = used_schematic  i pc
      in
      let tstr = string_of_term t pc
      and used_gen_str =
        if IntSet.is_empty used_gen then ""
        else " " ^ (intset_to_string used_gen)
      in
      if pc.trace || not is_used then
        printf "%s%3d   %s%s%s%s\n"
          prefix
          i
          (if global || is_hypo then "" else ". ")
          tstr
          used_gen_str
          (if is_used then " <used>" else "");
      print (i+1)
    end
  in
  print c0




let print_all_local_assertions (pc:t): unit =
  let rec print (level:int) (clst: int list): string =
      match clst with
        []
      | [_] -> ""
      | c1::c0::clst ->
          let prefix = print (level+1) (c0::clst) in
          print_assertions prefix level c0 c1 false pc;
          "  " ^ prefix
  in
  let clst = Proof_table.stacked_counts pc.base
  in
  let prefix = print 1 clst in
  print_assertions
    prefix
    0
    (count_previous pc)
    (count          pc)
    false
    pc



let print_global_assertions (pc:t): unit =
  let cnt = count_global pc
  and level = List.length pc.stack
  in
  print_assertions "" level 0 cnt true pc


let add_new_0
    (t:term) (used_gen:IntSet.t) (work:bool) (tabs:bool) (elim:bool) (pc:t)
    : unit =
  (** Add the new term [t] to the context [pc].

      Note: The term has to be added to the proof table outside
      this function
   *)
  assert (not tabs || not (has_stronger t pc));
  let td = analyze t elim pc
  and idx = Seq.count pc.terms
  in
  let add_to_proved (): unit =
    pc.entry.prvd <-
      Term_table.add t 0 td.nbenv idx pc.entry.prvd;
    pc.entry.prvd2 <-
      Term_table.add td.term td.nargs td.nbenv idx pc.entry.prvd2;
    let slot,ts = find_slot t pc in
    let sd   = pc.entry.slots.(slot) in
    pc.entry.slots.(slot) <- {sd with sprvd = TermMap.add ts idx sd.sprvd}

  and add_to_forward (): unit =
    match td.fwddat with
      None ->
        ()  (* do nothing, not a valid forward rule *)
    | Some (a,b,gp1,_,_) ->
        pc.entry.fwd <-
          Term_table.add a td.nargs td.nbenv idx pc.entry.fwd

  and add_to_backward (): unit =
    match td.bwddat with
      None -> ()
    | Some bwd ->
        let has_similar =
          td.nargs = 0 &&
          let sublst = Term_table.unify_with t 0 td.nbenv pc.entry.bwd in
          List.exists
            (fun (idx,_) ->
              bwd.ps_set =
              let bwddat = (Seq.elem idx pc.terms).td.bwddat in
              assert (Option.has bwddat);
              (Option.value bwddat).ps_set)
            sublst
        in
        if not has_similar then
          pc.entry.bwd <-
            Term_table.add bwd.tgt td.nargs td.nbenv idx pc.entry.bwd

  and add_to_work (): unit =
    pc.work <- idx::pc.work

  in
  if tabs then begin
    add_to_proved   ();
    add_to_forward  ();
    add_to_backward ()
  end;
  if work then
    add_to_work     ();
  Seq.push {td=td; used_gen = used_gen} pc.terms;
  if is_global pc then begin
    let mt = module_table pc in
    let mdl = Module_table.current mt in
    Seq.push {pub = is_public pc; defer = false; mdl = mdl} pc.gseq;
    assert (count pc = Seq.count pc.gseq);
  end



let with_work = true
let wo_work   = false
let with_tabs = true
let wo_tabs   = false
let with_elim = true
let wo_elim   = false


let add_new (t:term) (used_gen:IntSet.t) (pc:t): unit =
  add_new_0 t used_gen with_work with_tabs wo_elim pc




let add_mp (t:term) (i:int) (j:int) (pc:t): unit =
  (** Add the term [t] which is a consequence of [i] as a premise and [j]
      as an implication using the modus ponens rule to the context [pc].
   *)
  (*assert (not (has_stronger t pc));*)
  assert (i < count pc);
  assert (j < count pc);
  let td = (Seq.elem j pc.terms).td in
  let _,_,_,simpl,elim = Option.value td.fwddat in
  let gen_i = used_schematic i pc
  and gen_j = used_schematic j pc
  in
  let fwd_ok = simpl || elim || IntSet.is_empty (IntSet.inter gen_i gen_j) in
  if is_using_forward pc
      && fwd_ok
      && not (has_stronger t pc)
  then begin
    let gen = if simpl then gen_i else IntSet.union gen_i gen_j
    in
    pc.entry.used_fwd <- IntSet.add j pc.entry.used_fwd;
    Proof_table.add_mp t i j pc.base;
    add_new_0 t gen with_work with_tabs elim pc
  end else
    ()



let add_specialized_forward
    (t:term)
    (i:int) (args: term array) (pc:t): unit =
  (** Add the term [t] which is a specialization of the term [i]
      specialized with the arguments [args] to the proof context [pc]
      if it is not yet in.
   *)
  assert (i < count pc);
  if has t pc then  (* The term [t] is a specialization, therefore cannot be
                       all quantified, therefore cannot have equivalents
                       which are not identical *)
    ()
  else begin
    let used_gen = used_schematic i pc in
    let used_gen = IntSet.add i used_gen
    and td = term_data i pc in
    let _,_,gp1,_,elim = Option.value td.fwddat  (* must have forward data *)
    in
    let elim = elim && gp1 < td.nargs in
    Proof_table.add_specialize t i args pc.base;
    add_new_0 t used_gen wo_work with_tabs elim pc
  end



let specialized_forward
    (i:int)
    (sub:Term_sub.t)
    (nbenv_sub:int)
    (pc:t)
    : term * term  * term array * int =
  (** The antecedent, the consequent, the arguments and the number of
      arguments of the term [i] specialized with the substitution [sub] which
      comes from an environment with [nbenv_sub] variables.

      Note: The results are all valid in the current environment!
   *)
  assert (is_consistent pc);
  assert (i < count pc);
  let td_imp    = (Seq.elem i pc.terms).td in
  assert (Option.has td_imp.fwddat);
  let nargs     = td_imp.nargs
  and a,b,gp1,_,_ = Option.value td_imp.fwddat in
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
  a, b, args, nargs




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
  let a, b, args, nargs = specialized_forward j sub nbenv_sub pc
  and used_gen_i = used_schematic i pc
  in
  let j_in_used_gen_i = IntSet.mem j used_gen_i
  in
  if j_in_used_gen_i || has_stronger b pc then
                                  (* [b] might be all quantified *)
    ()
  else if nargs=0 then
    add_mp b i j pc
  else begin
    let imp  = implication a b pc in
    if has imp pc then
      ()
    else begin
      let idx  = count pc
      in
      add_specialized_forward imp j args pc;
      add_mp b i idx pc
    end
  end



let add_consequences_premise (i:int) (pc:t): unit =
  (** Add the consequences of the term [i] by using the term as a premise for
      already available implications.
   *)
  let t,nbenvt = Proof_table.term i pc.base in
  assert (nbenvt = (nbenv pc));
  let sublst = Term_table.unify t nbenvt pc.entry.fwd in
  let sublst = List.rev sublst in
  List.iter
    (fun (idx,sub) ->
      assert (is_consistent pc);
      assert (idx < count pc);
      add_consequence i idx sub pc)
    sublst





let add_fully_specialized (idx:int) (sub:Term_sub.t) (pc:t): unit =
  (** Add the schematic rule [idx] substituted by [sub] to the
      proof context [pc].

      Note: The substitution [sub] has to be complete and not partial!
   *)
  assert (is_consistent pc);
  assert (idx < count pc);
  assert (not (Term_sub.is_empty sub));
  let desc    = Seq.elem idx pc.terms              in
  let td      = desc.td                            in
  assert (td.nargs = Term_sub.count sub);
  let args    = Term_sub.arguments td.nargs sub    in
  let t       = Proof_table.local_term idx pc.base in
  let n,nms,t = split_all_quantified t pc          in
  assert (n = Array.length args);
  let t       = Term.apply t args                  in
  if has t pc then (* [t] is a complete specialization, therefore
                      cannot be schematic *)
    ()
  else begin
    let used_gen = IntSet.add idx desc.used_gen
    in
    Proof_table.add_specialize t idx args pc.base;
    add_new t used_gen pc;
    assert (is_consistent pc)
  end



let add_consequences_implication (i:int)(pc:t): unit =
  (** Add the consequences of the term [i] by using the term as an
      implication and searching for matching premises.
   *)
  let desc = Seq.elem i pc.terms in
  let td   = desc.td
  in
  match td.fwddat with
    None -> ()
  | Some (a,b,gp1,_,_) ->
      if 0 < td.nargs then  (* the implication is schematic *)
        let sublst =
          Term_table.unify_with a td.nargs td.nbenv pc.entry.prvd
        in
        let sublst = List.rev sublst in
        List.iter
          (fun (idx,sub) ->
            assert (is_consistent pc);
            assert (idx < count pc);
            add_consequence idx i sub pc)
          sublst
      else  (* the implication is not schematic *)
        try
          let idx = find a pc in   (* check for exact match *)
          assert (nbenv pc = td.nbenv);
          add_mp b idx i pc
        with Not_found -> (* no exact match *)
          let sublst = Term_table.unify a td.nbenv pc.entry.prvd2
          in
          match sublst with
            [] -> ()
          | (idx,sub)::_ ->
              (* the schematic rule [idx] matches the premise of [i]*)
              begin
                let idx_premise = count pc in
                assert (not (has a pc)); (* because there is no exact
                                            match *)
                add_fully_specialized idx sub pc;
                assert (idx_premise + 1 = count pc); (* specialized is
                                                        new *)
                add_mp b idx_premise i pc
              end



let add_consequences_expansion (i:int) (pc:t): unit =
  (* Add the focussed expansion of the term [i] in case that there is one if
     it is not yet in the proof context [pc] to the proof context and to the
     work items.  *)
  let t        = term i pc
  and used_gen = used_schematic i pc
  and ft       = feature_table pc
  and nbenv    = nbenv pc
  in
  try
    let texpand = Feature_table.expand_focus_term t nbenv ft in
    if has_stronger texpand pc then
      ()
    else begin
      (*printf "add_consequences_expansion t:\"%s\"  texp:\"%s\"\n"
        (string_of_term t pc) (string_of_term texpand pc);*)
      Proof_table.add_expand texpand i pc.base;
      add_new texpand used_gen pc
    end
  with Not_found ->
    ()



let add_consequences_reduce (i:int) (pc:t): unit =
  (* Add the beta reduction of the term [i] in case that there is one if
     it is not yet in the proof context [pc] to the proof context and to the
     work items.  *)
  let t        = term i pc
  and used_gen = used_schematic i pc
  in
  try
    let tred = Term.reduce_top t in
    if has_stronger tred pc then
      ()
    else begin
      Proof_table.add_reduce tred i pc.base;
      add_new tred used_gen pc
    end
  with Not_found ->
    ()



let add_consequences (i:int) (pc:t): unit =
  (** Add the consequences of the term [i] which are not yet in the proof
      context [pc] to the proof context and to the work items.
   *)
  add_consequences_premise     i pc;
  add_consequences_implication i pc;
  add_consequences_expansion   i pc;
  add_consequences_reduce      i pc




let close_step (pc:t): unit =
  assert (has_work pc);
  let i = List.hd pc.work in
  pc.work <- List.tl pc.work;
  add_consequences i pc


let prefix (pc:t): string = String.make (2*(depth pc)+2) ' '


let close (pc:t): unit =
  let rec print (c0:int) (c1:int): unit =
    assert (c0 <= c1);
    if c0 = c1 then ()
    else begin
      let used_gen = (Seq.elem c0 pc.terms).used_gen in
      let used_gen_str = intset_to_string used_gen in
      printf "%s%3d >       %s %s\n"
        (prefix pc) c0 (string_of_term (term c0 pc) pc) used_gen_str;
      print (c0+1) c1
    end
  in
  let rec cls (n:int): unit =
    if n > 100 then assert false;  (* 'infinite' loop detection *)
    if has_work pc then begin
      let cnt = count pc in
      close_step pc;
      if pc.trace then print cnt (count pc);
      (*print cnt (count pc);*)
      cls (n+1)
    end else
      ()
  in
  cls 0;
  assert (not (has_work pc))


let close_assumptions (pc:t): unit =
  pc.work <- List.rev pc.work;
  close pc



let add_assumption_or_axiom (t:term) (is_axiom: bool) (pc:t): int =
  (** Add the term [t] as an assumption or an axiom to the context [pc].
   *)
  assert (is_consistent pc);
  let idx = count pc
  and has = has_stronger t pc
  in
  if is_axiom then
    Proof_table.add_axiom t pc.base
  else
    Proof_table.add_assumption t pc.base;
  if not has then begin
    add_new t IntSet.empty pc
  end else
    add_new_0 t IntSet.empty wo_work wo_tabs wo_elim pc;
    (*Seq.push {td = analyze t pc; used_gen = IntSet.empty} pc.terms;*)
  if pc.trace then
    printf "%s%3d hypo:   %s\n" (prefix pc) idx (string_of_term t pc);
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




let push_slots (nbenv:int) (pc:t): unit =
  pc.entry.slots <-
    if nbenv=0 then
      Array.copy pc.entry.slots
    else
      let len = Array.length pc.entry.slots in
      Array.init
        (len+1)
        (fun i ->
          if i<len then
            let sd = pc.entry.slots.(i) in
            {sd with ndown = sd.ndown+nbenv}
          else
            {ndown=0; sprvd=TermMap.empty})


let push0 (nbenv:int) (pc:t): unit =
  pc.entry.count <- Seq.count pc.terms;
  pc.stack <- (copied_entry pc.entry)::pc.stack;
  push_slots nbenv pc


let push (entlst:entities list withinfo) (pc:t): unit =
  assert (not (has_work pc));
  Proof_table.push entlst pc.base;
  let nbenv = Proof_table.nbenv pc.base in
  push0 nbenv pc


let push_untyped (names:int array) (pc:t): unit =
  assert (not (has_work pc));
  Proof_table.push_untyped names pc.base;
  let nbenv = Proof_table.nbenv pc.base in
  push0 nbenv pc


let keep (cnt:int) (pc:t): unit =
  assert (count_previous pc <= cnt);
  Seq.keep cnt pc.terms


let pop (pc:t): unit =
  assert (is_local pc);
  assert (not (has_work pc));
  pc.work  <- [];
  pc.entry <- List.hd pc.stack;
  pc.stack <- List.tl pc.stack;
  Seq.keep pc.entry.count pc.terms;
  Proof_table.pop pc.base


let check_deferred (pc:t): unit = Context.check_deferred (context pc)

let owner (pc:t): int = Context.owner (context pc)

let variant (i:int) (cls:int) (pc:t): term =
  Proof_table.variant i cls pc.base



let inherit_deferred (i:int) (cls:int) (info:info) (pc:t): unit =
  (* Inherit the deferred assertion [i] in the class [cls] *)
  assert (i < count pc);
  let t = variant i cls pc in
  let ct = class_table pc in
  printf "    inherit deferred \"%s\" in %s\n"
    (string_of_term t pc)
    (Class_table.class_name cls ct);
  if not (has t pc) then
    error_info info ("The deferred assertion \""  ^
                     (string_of_term t pc) ^
                     "\" is missing in " ^
                     (Class_table.class_name cls (class_table pc)))



let inherit_effective (i:int) (cls:int) (pc:t): unit =
  (* Inherit the effective assertion [i] in the class [cls] *)
  let t = variant i cls pc in
  let ct = class_table pc in
  printf "    inherit \"%s\" in %s\n"
    (string_of_term t pc)
    (Class_table.class_name cls ct);
  if not (has_stronger t pc) then begin
    Proof_table.add_inherited t i cls pc.base;
    add_new t IntSet.empty pc;
    close pc
  end





let do_inherit
    (cls:int)
    (anc_lst: (int * type_term array) list)
    (info:info)
    (pc:t)
    : unit =
  let ct = class_table pc in
  List.iter
    (fun (par,_) ->
      let deflst = Class_table.deferred_assertions par ct in
      List.iter (fun i -> inherit_deferred i cls info pc) deflst;
      let efflst = Class_table.effective_assertions par ct in
      List.iter (fun i -> inherit_effective i cls pc) efflst
    )
    anc_lst


let add_backward_expansion (t:term) (pc:t): unit =
  let ft    = feature_table pc
  and nbenv = nbenv pc
  in
  try
    let texpand = Feature_table.expand_focus_term t nbenv ft in
    let impl = implication texpand t pc in
    if has_stronger impl pc then
      ()
    else begin
      Proof_table.add_expand_backward t impl pc.base;
      add_new impl IntSet.empty pc
    end
  with Not_found ->
    ()


let add_backward_reduce (t:term) (pc:t): unit =
  try
    let tred = Term.reduce_top t in
    let impl = implication tred t pc in
    if has_stronger impl pc then
      ()
    else begin
      Proof_table.add_reduce_backward t impl pc.base;
      add_new impl IntSet.empty pc
    end
  with Not_found ->
    ()


let add_backward_witness (t:term) (pc:t): unit =
  try
    let nargs,_,tt = split_some_quantified t pc in
    let idx,sub = find_witness tt nargs pc in
    let witness = term idx pc in
    let impl    = implication witness t pc in
    if has_stronger impl pc then
      ()
    else begin
      Proof_table.add_witness impl idx tt (Term_sub.arguments nargs sub) pc.base;
      add_new impl IntSet.empty pc
    end
  with Not_found ->
    ()


let add_backward (t:term) (pc:t): unit =
  (** Add all backward rules which have [t] as a target to the context [pc].
   *)
  set_forward pc;
  let add_lst (sublst: (int*Term_sub.t) list): unit =
    List.iter
      (fun (idx,sub) ->
        if Term_sub.is_empty sub then
          if is_using_forced_forward pc then
            pc.work <- idx :: pc.work
          else
            ()
        else
          add_fully_specialized idx sub pc)
      sublst
  in
  add_backward_expansion t pc;
  add_backward_reduce t pc;
  add_backward_witness t pc;
  let sublst = Term_table.unify t (nbenv pc) pc.entry.prvd2 in
  (if sublst <> [] then
    add_lst sublst
  else
    let sublst = Term_table.unify t (nbenv pc) pc.entry.bwd in
    add_lst sublst);
  close pc



let discharged (i:int) (pc:t): term * proof_term =
  (** The [i]th term of the current environment with all local variables and
      assumptions discharged together with its proof term and its base index.
   *)
  Proof_table.discharged i pc.base



let inherit_to_descendants (i:int) (defer:bool) (owner:int) (pc:t): unit =
  assert (is_global pc);
  assert (owner <> -1);
  let ct = class_table pc in
  if not defer then
    let descendants = Class_table.descendants owner ct in
    IntSet.iter
      (fun descendant -> inherit_effective i descendant pc)
      descendants



let add_proved_0
    (defer:bool)
    (owner:int)
    (t:term)
    (pterm:proof_term)
    (delta:int)
    (used_gen:IntSet.t)
    (pc:t)
    : unit =
  let ct = class_table pc in
  try
    let idx = find_stronger t pc in
    assert (not (is_global pc) || idx < Seq.count pc.gseq);
    if
      is_global pc &&
      owner <> -1  &&
      is_public pc &&
      not (Seq.elem idx pc.gseq).pub
    then begin
      Class_table.add_assertion idx owner defer ct;
      inherit_to_descendants idx defer owner pc;
      (Seq.elem idx pc.gseq).pub <- true
    end
  with Not_found -> begin
    let cnt = count pc in
    Proof_table.add_proved t pterm delta pc.base;
    add_new t used_gen pc;
    if is_global pc && owner <> -1 then begin
      (Seq.elem cnt pc.gseq).defer <- defer;
      Class_table.add_assertion cnt owner defer ct;
      inherit_to_descendants cnt defer owner pc
    end
  end;
  if pc.trace then begin
    let idx = find_stronger t pc in
    printf "%s%3d proved: %s\n" (prefix pc) idx (string_of_term t pc)
  end;
  close pc



let add_proved
    (defer:bool)
    (owner:int)
    (t:term)
    (pterm:proof_term)
    (used_gen:IntSet.t)
    (pc:t)
    : unit =
  add_proved_0 defer owner t pterm 0 used_gen pc



let add_proved_list
    (defer:bool)
    (owner:int)
    (lst: (term*proof_term) list)
    (pc:t)
    : unit =
  let cnt = count pc in
  List.iter
    (fun (t,pt) ->
      let delta = count pc - cnt in
      add_proved_0 defer owner t pt delta IntSet.empty pc)
    lst



let backward_set (t:term) (pc:t): int list =
  let sublst = Term_table.unify t (nbenv pc) pc.entry.bwd in
  List.fold_left
    (fun lst (idx,sub) ->
      if Term_sub.is_empty sub
          && not (IntSet.mem idx pc.entry.used_fwd)
      then
        idx::lst
      else
        lst)
    []
    sublst

let backward_data (idx:int) (pc:t): (term*bool) list * IntSet.t =
  let desc = Seq.elem idx pc.terms in
  assert (Option.has desc.td.bwddat);
  let bwd = Option.value desc.td.bwddat
  and nbenv_idx = Proof_table.nbenv_term idx pc.base
  and nbenv = nbenv pc
  in
  let ps = List.map (fun (t,simpl) -> Term.up (nbenv-nbenv_idx) t, simpl) bwd.ps
  in
  ps,
  desc.used_gen


let check_interface (pc:t): unit =
  assert (is_interface_check pc);
  let ft = feature_table pc in
  Feature_table.check_interface ft;
  assert (count pc = Seq.count pc.gseq);
  for i = 0 to count pc - 1 do
    let gdesc = Seq.elem i pc.gseq in
    if gdesc.defer && not gdesc.pub then
      error_info (FINFO (1,0))
        ("deferred assertion `" ^ (string_of_term (term i pc) pc) ^
         "' is not public")
  done
