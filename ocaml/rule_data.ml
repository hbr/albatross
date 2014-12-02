open Term
open Container


type t = {
    orig:int option;  (* original schematic assertion *)
    nbenv:     int;   (* number of variables between the arguments and the
                         global variables *)
    nargs:     int;
    spec:      bool;  (* is specialized *)
    nms:       int array;
    fwd_blckd: bool;  (* is blocked as forward rule *)
    nbwd:      int;   (* number of premises until backward rule *)
    ndropped:  int;   (* number of dropped premises *)
    nds_dropped:int;  (* max nodes of dropped premises *)
    premises:  (int * bool * term) list;
              (* gp1, cons,  term *)
    target:   term;
  }

let is_argument (t:term) (nargs:int): bool =
  match t with
    Variable i when i < nargs -> true
  | _                         -> false

let nbenv (rd:t): int = rd.nbenv

let is_schematic (rd:t) : bool =  not rd.spec


let is_orig_schematic (rd:t): bool =
  match rd.orig with
    None -> false
  | Some _ -> true


let previous_schematic (rd:t): int option = rd.orig


let is_implication (rd:t): bool = rd.premises <> []

let is_intermediate (rd:t): bool =
  is_implication rd && is_orig_schematic rd

let is_specialized (rd:t): bool = rd.spec

let is_fully_specialized (rd:t): bool =
  rd.nargs = 0


let allows_partial_specialization (rd:t): bool =
  is_implication rd &&
  let gp1,_,_ = List.hd rd.premises in
  gp1 < rd.nargs


let is_forward_catchall (rd:t): bool =
  is_implication rd &&
  let _,_,p = List.hd rd.premises in
  is_argument p rd.nargs



let is_forward (rd:t): bool =
  is_implication rd &&
  not (is_forward_catchall rd) &&
  (not rd.fwd_blckd || allows_partial_specialization rd)


let is_backward (rd:t): bool =
  is_implication rd &&
  (rd.nbwd = 0 &&
   (0 < rd.ndropped || not (is_argument rd.target rd.nargs)))


let short_string (rd:t): string =
  let lst = ref [] in
  if is_intermediate rd then
    lst := "i" :: !lst;
  if is_backward rd then
    lst := "b" :: !lst;
  if is_forward rd then
    lst := "f" :: !lst;
  String.concat "" !lst


let count_premises (rd:t): int =
  List.length rd.premises

let premises (rd:t) (nbenv:int): (term*bool) list =
  assert (is_fully_specialized rd);
  assert (is_implication rd);
  assert (rd.nbenv <= nbenv);
  let nbenv_delta = nbenv - rd.nbenv in
  let up t = Term.upbound nbenv_delta rd.nargs t in
  List.map (fun (gp1,cons,p) -> up p,cons) rd.premises



let prepend_premises (ps:(int*bool*term) list) (rd:t)
    : term =
  let all_id  = rd.nbenv + Feature_table.all_index in
  let imp_id  = rd.nargs + rd.nbenv + Feature_table.implication_index in
  let t = List.fold_right
      (fun (_,_,p) tgt ->
        Term.binary imp_id p tgt)
      ps
      rd.target
  in
  Term.quantified all_id rd.nargs rd.nms t
  


let term (rd:t) (nbenv:int): term =
  assert (rd.nbenv <= nbenv);
  let t =
    if is_implication rd && is_specialized rd then
      let (gp1,_,p), ps = List.hd rd.premises, List.tl rd.premises in
      assert (gp1 = 0);
      let p = Term.down rd.nargs p
      and t = prepend_premises ps rd
      and imp_id = rd.nbenv + Feature_table.implication_index in
      Term.binary imp_id p t
    else
      prepend_premises rd.premises rd
  in
  let nbenv_delta = nbenv - rd.nbenv in
  Term.up nbenv_delta t





let complexity (t:term) (nbenv:int) (ft:Feature_table.t): int =
  let t_exp = Feature_table.expand_term t nbenv ft in
  Term.nodes t_exp



let split_term (t:term) (nbenv:int) (ft:Feature_table.t)
    : int * int array  * (int*bool*term) list * term =
  (* nargs,nms,simpl_fwd,premises,target
     premise: gp1,cons,term *)
  let all_id = nbenv + Feature_table.all_index in
  let nargs,nms,t =
    try Term.quantifier_split t all_id
    with Not_found -> 0,[||], t
  in
  let imp_id = nbenv + nargs + Feature_table.implication_index
  in
  let ps, tgt = Term.split_implication_chain t imp_id
  in
  let ps = List.rev_map (fun p -> Term.greatestp1_arg p nargs, true,p) ps
  in
  nargs, nms, ps, tgt



let make (t:term) (nbenv:int) (ft:Feature_table.t): t =
  let nargs, nms, ps, tgt = split_term t nbenv ft
  in
  let rec nbwdfun n gp1 ps set =
    assert (IntSet.cardinal set <= nargs - gp1);
    if IntSet.cardinal set = nargs - gp1 then
      n
    else
      match ps with
        (gp1,_,_)::ps ->
          let set =
            if 0 < gp1 then IntSet.filter (fun i -> gp1 <=i) set
            else set in
          nbwdfun (n+1) gp1 ps set
      | _ -> assert false
  in
  let nbwd = nbwdfun 0 0 ps (Term.bound_variables tgt nargs) in
  let rd = { orig      = None;
             nbenv     = nbenv;
             nargs     = nargs;
             spec      = nargs = 0;
             nms       = nms;
             fwd_blckd = false;
             nbwd      = nbwd;
             ndropped  = 0;
             nds_dropped = 0;
             premises  = ps;
             target    = tgt}
  in
  assert (term rd nbenv = t);
  rd



let specialize (rd:t) (args:term array) (nbenv:int) (orig:int)
    (ft:Feature_table.t)
    : t =
  let nargs = Array.length args in
  assert (rd.nbenv <= nbenv);
  assert (not (is_specialized rd));
  assert (nargs <= rd.nargs);
  assert (nargs = rd.nargs || is_implication rd);
  assert (nargs = rd.nargs || let gp1,_,_ = List.hd rd.premises in nargs = gp1);
  let full        = nargs = rd.nargs
  and nbenv_delta = nbenv - rd.nbenv in
  let sub t = Term.part_sub t rd.nargs args nbenv_delta
  in
  assert ( match rd.premises with
    [] -> nargs = rd.nargs
  | (gp1,_,_)::_ ->
      nargs = rd.nargs || nargs = gp1);
  let tgt  = sub rd.target in
  let ps_rev =
    List.fold_left
      (fun lst (gp1,cons,p) ->
        let gp1 = if nargs <= gp1 then gp1-nargs else 0
        and p   = sub p in
        (gp1,cons,p)::lst)
      []
      rd.premises
  in
  let ps,fwd_blckd =
    if full then
      let ntgt = complexity tgt nbenv ft in
      let ps,max_nds =
        List.fold_left
          (fun (ps,max_nds) (gp1,cons,p) ->
            let nds  = complexity p nbenv ft in
            let cons = nds <= ntgt in
            let nds  = max nds max_nds in
            let ps   = (gp1,cons,p)::ps in
            ps,nds)
          ([],rd.nds_dropped)
          ps_rev
      in
      ps, max_nds <= ntgt
    else
      List.rev ps_rev, false
  and nms =
    if Array.length rd.nms = 0 then rd.nms
    else Array.sub rd.nms nargs (rd.nargs - nargs)
  in
  {rd with
   orig  = Some orig;
   spec  = true;
   fwd_blckd = fwd_blckd;
   nbenv = nbenv;
   nargs = rd.nargs - nargs;
   nms   = nms;
   premises = ps;
   target   = tgt}




let schematic_premise (rd:t): int * int * term =
  assert (is_implication rd);
  let gp1,_,p = List.hd rd.premises in
  let p = Term.down_from (rd.nargs - gp1) gp1 p in
  gp1, rd.nbenv, p



let schematic_target (rd:t): int * int * term =
  if rd.nbwd <> 0 then
    Printf.printf "schematic_target nbwd %d\n" rd.nbwd;
  assert (rd.nbwd = 0);
  rd.nargs, rd.nbenv, rd.target



let schematic_term (rd:t): int * int * term =
  let imp_id = rd.nargs + rd.nbenv + Feature_table.implication_index in
  let t =
    List.fold_left
      (fun t (_,_,p) ->
        Term.binary imp_id p t)
      rd.target
      rd.premises
  in
  rd.nargs, rd.nbenv, t


let drop (rd:t) (ft:Feature_table.t): t =
  assert (is_specialized rd);
  assert (is_implication rd);
  let gp1,_,p = List.hd rd.premises in
  assert (gp1 = 0);
  let p = Term.down rd.nargs p in
  {rd with
   spec     = rd.nargs = 0;
   nbwd     = if rd.nbwd > 0 then rd.nbwd - 1 else 0;
   ndropped = rd.ndropped + 1;
   nds_dropped = max rd.nds_dropped (complexity p rd.nbenv ft);
   premises = List.tl rd.premises}



let term_a (rd:t) (nbenv:int): term =
  assert (rd.nbenv <= nbenv);
  assert (is_specialized rd);
  assert (is_implication rd);
  let gp1,_,p = List.hd rd.premises in
  assert (gp1 = 0);
  let t = Term.down rd.nargs p in
  Term.up (nbenv - rd.nbenv) t



let term_b (rd:t) (nbenv:int): term =
  assert (is_specialized rd);
  assert (is_implication rd);
  assert (rd.nbenv <= nbenv);
  let ps = List.tl rd.premises in
  let t  = prepend_premises ps rd in
  let nbenv_delta = nbenv - rd.nbenv in
  Term.up nbenv_delta t





let target (rd:t) (nbenv:int): term =
  assert (is_fully_specialized rd);
  let nbenv_delta = nbenv - rd.nbenv in
  Term.up nbenv_delta rd.target
