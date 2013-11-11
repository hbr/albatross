open Term
open Type
open Container
open Proof


module FwdSet = Set.Make(struct
  type t = term * proof_term * IntSet.t
        (* conclusion b
           proof term of the implication a=>b
           used global forward rules to obtain a=>b *)
  let compare (x:t) (y:t) =
    let b1,_,_ = x
    and b2,_,_ = y in
    Pervasives.compare b1 b2
end)


module BwdSet = Set.Make(struct
  type t = int * TermSet.t * proof_term * int option
        (* number of premises
           set of premises  {a,b,c,...}
           proof_term of  the implication a=>b=>...=>z
           index of global backward rule *)
  let compare (x:t) (y:t) =
    let n1,ps1,_,_ = x
    and n2,ps2,_,_ = y
    in
    let cmp0 = Pervasives.compare n1 n2 in
    if cmp0=0 then
      Pervasives.compare ps1 ps2
    else
      cmp0
end)


type global_info = int array * typ array
type local_info  = IntSet.t

type context = {
    implication_id:    int;
    nargs:             int;
    mutable goal:      term;
    mutable count:     int;
    mutable context:   (proof_term * IntSet.t * int option) TermMap.t;
    mutable forward:   FwdSet.t TermMap.t;
    mutable backward:  BwdSet.t TermMap.t;
    mutable used_backward: IntSet.t; (* the used non simplifying backward
                                        rules *)
    mutable local:     local_info General_context.t
  }


type context_list = {
    head:    context;
    tail:    context_tail
  }
and  context_tail =
    Basic of global_info General_context.t
  | Combined of context_list


type work_item = proof_pair * IntSet.t * int option

type state = {
    list:         context_list;
    mutable work: work_item list;
  }


let split (t:term) (c:context): term * term =
  Term.binary_split t c.implication_id


let split_goal (c:context): term * term =
  split c.goal c



let add_and_apply
    (t:term)
    (pt:proof_term)
    (gfwds: IntSet.t)
    (gbwd: int option)
    (s: state): unit =
  assert (not (TermMap.mem t s.list.head.context));

  let c = s.list.head in

  c.context <- TermMap.add t (pt,gfwds,gbwd) c.context;
  c.count   <- c.count + 1;

  match t with
    Lam(nb,t) ->
      (* add to local general context *) (*?????*)
      c.local <-
        General_context.add t pt gfwds nb c.implication_id c.local
  | _ ->
      try
        let a,b = split t c in
        (* Apply or add as forward rule and as backward rule*)
        begin
          try
            let pt_a,gfwds_a,gbwd_a = TermMap.find a c.context in
            s.work <-
              ((b,MP(pt_a,pt)),IntSet.union gfwds_a gfwds,None)
              ::s.work
          with Not_found ->
            c.forward <-
              TermMap.add
                a
                (FwdSet.add
                   (b,pt,gfwds)
                   (try TermMap.find a c.forward
                   with Not_found -> FwdSet.empty)
                )
                c.forward;
            c.backward <-
              let ts = Term.binary_right t c.implication_id in
              let tgt,ps = List.hd ts, List.tl ts in
              let n,set =
                List.fold_left
                  (fun (n,set) p -> n+1, TermSet.add p set)
                  (0,TermSet.empty)
                  ps
              in
              TermMap.add
                tgt
                (BwdSet.add
                   (n,set,pt,gbwd)
                   (try TermMap.find tgt c.backward
                   with Not_found -> BwdSet.empty)
                )
                c.backward
        end
      with Not_found ->
        ()



let apply_forward_rules
    (t:term)
    (pt:proof_term)
    (gfwds: IntSet.t)
    (gbwd: int option)
    (s: state): unit =
  (* Use the term 't' as an antecedent and apply all possible forward rules.
     The forward rules can be specific or general. The general rules can be
     in the current context or in an outer context.
   *)
  let c = s.list.head in
  (* Apply specific forward rules where 't' is the antecedent *)
  try
    FwdSet.iter
      (fun (b,pt_imp,gfwds_imp) ->
        s.work <-
          ((b,MP(pt,pt_imp)),IntSet.union gfwds gfwds_imp,assert false)
          :: s.work
      )
      (TermMap.find t c.forward);
    c.forward <- TermMap.remove t c.forward
  with Not_found ->
    ()



let close_work (s:state): unit =
  let rec close () =
    match s.work with
      [] ->
        ()
    | ((t,pt),gfwds,gbwd)::tail ->
        s.work <- tail;
        add_and_apply t pt gfwds gbwd s;
        apply_forward_rules t pt gfwds gbwd s;
        close ()
  in
  close ()


let analyze_goal (s:state): unit =
  assert (s.work = []);
  let c = s.list.head    in
  let rec ana () =
    try
      let a,b = split_goal c in
      s.work <- ((a,Assume a),IntSet.empty,None) :: s.work;
      c.goal <- b;
      close_work s;
      ana ()
    with Not_found ->
      ()
  in
  ana ()



type node = {
    goal:           term;
    count:          int;

    context:        (proof_term * IntSet.t * int option) TermMap.t;
    forward:        FwdSet.t TermMap.t;
    backward:       BwdSet.t TermMap.t;

    used_backward:  IntSet.t; (* the used non simplifying backward rules *)
    global:         global_info General_context.t;
    local:          local_info  General_context.t;

    narguments:     int;
    implication_id: int;
  }



(*
module NodeOrd = struct
  type t = node
  let compare (n1:node) (n2:node): int =
    let cmp0 = Pervasives.compare n1.count n2.count in
    if cmp0=0 then
      Pervasives.compare (n1.goal,n1.context) (n2.goal,n2.context)
    else
      cmp0
end

module NodeMap = Map.Make(NodeOrd)
*)



type closure_state = {
    narguments2:        int;
    implication_id2:    int;
    global2:            global_info General_context.t;
    mutable goal2:      term;
    mutable local2:     local_info  General_context.t;
    mutable context2:   (proof_term * IntSet.t * int option) TermMap.t;
    mutable count2:     int;
    mutable forward2:   FwdSet.t TermMap.t;
    mutable backward2:  BwdSet.t TermMap.t;
    mutable work_items: work_item list;
  }





let node2state (n:node): closure_state =
  {count2          = n.count;
   narguments2     = n.narguments;
   implication_id2 = n.implication_id;
   global2         = n.global;
   local2          = n.local;
   goal2           = n.goal;
   context2        = n.context;
   forward2        = n.forward;
   backward2       = n.backward;
   work_items      = []}




let state2node (s:closure_state): node =
  {count           = s.count2;
   narguments      = s.narguments2;
   implication_id  = s.implication_id2;
   global          = s.global2;
   local           = s.local2;
   goal            = s.goal2;
   context         = s.context2;
   forward         = s.forward2;
   backward        = s.backward2;
   used_backward   = assert false}






let add_and_apply
    (t:term)
    (pt:proof_term)
    (gfwds: IntSet.t)
    (gbwd: int option)
    (state:closure_state): unit =
  assert (not (TermMap.mem t state.context2));

  state.context2 <- TermMap.add t (pt,gfwds,gbwd) state.context2;
  state.count2   <- state.count2 + 1;

  match t with
    Lam(nb,t) ->
      (* add to local general context *)
      state.local2 <-
        General_context.add t pt gfwds nb state.implication_id2 state.local2
  | _ ->
      try
        let a,b = Term.binary_split t state.implication_id2 in
        (* Apply or add as forward rule and as backward rule*)
        begin
          try
            let pt_a,gfwds_a,gbwd_a = TermMap.find a state.context2 in
            state.work_items <-
              ((b,MP(pt_a,pt)),IntSet.union gfwds_a gfwds,None)
              ::state.work_items
          with Not_found ->
            state.forward2 <-
              TermMap.add
                a
                (FwdSet.add
                   (b,pt,gfwds)
                   (try TermMap.find a state.forward2
                   with Not_found -> FwdSet.empty)
                )
                state.forward2;
            state.backward2 <-
              let ts = Term.binary_right t state.implication_id2 in
              let tgt,ps = List.hd ts, List.tl ts in
              let n,set =
                List.fold_left
                  (fun (n,set) p -> n+1, TermSet.add p set)
                  (0,TermSet.empty)
                  ps
              in
              TermMap.add
                tgt
                (BwdSet.add
                   (n,set,pt,gbwd)
                   (try TermMap.find tgt state.backward2
                   with Not_found -> BwdSet.empty)
                )
                state.backward2
        end
      with Not_found ->
        ()



let close_one
    (t:term)
    (pt:proof_term)
    (gfwds: IntSet.t)
    (gbwd:  int option)
    (state: closure_state)
    : unit  =
  assert (not (TermMap.mem t state.context2));

  add_and_apply t pt gfwds gbwd state;

  match t with
    Lam(_,_) -> ()
  | _ ->
      (* Add global forward rules *)
      List.iter
        (fun (nargs,idx,(t,_),_,sub,simpl,nopen) ->
          let gfwds = if simpl then IntSet.empty else IntSet.singleton idx
          in
          let tt = Term_sub.apply_0 t nargs sub (nopen=0) in
          let tt = if nopen=0 then tt else Lam(nargs,tt) in
          state.work_items <-
            ((tt,Specialize(Theorem idx,sub)),gfwds,None)::state.work_items
        )
        (General_context.forward t state.narguments2 state.global2);

      (* Apply local forward rules *)
      try
        let fwd_set = TermMap.find t state.forward2 in
        state.work_items <-
          FwdSet.fold
            (fun (b,pt_b,gfwds_b) lst ->
              ((b,MP(pt,pt_b)),IntSet.union gfwds gfwds_b,None)::lst
            )
            fwd_set
            state.work_items;
        state.forward2 <- TermMap.remove t state.forward2
      with Not_found ->
        ()





let rec analyze_goal (state:closure_state): unit =
  let add_backward (t:term): unit =
    List.iter
      (fun (nargs,idx,(t0,_),dat,sub,simpl) ->
        let pp =
          Term_sub.apply_covering t0 nargs sub,
          Specialize(Theorem idx,sub)
        in
        state.work_items <-
          (pp,IntSet.empty,Some idx)::state.work_items
      )
      (General_context.backward t state.narguments2 state.global2)
  in
  try
    let a,b = Term.binary_split state.goal2 state.implication_id2 in
    state.work_items <-
      ((a,Assume a), IntSet.empty, None)::state.work_items;
    add_backward b;
    state.goal2 <- b
  with Not_found ->
    add_backward state.goal2






let close_node (n:node): closure_state =
  let rec close (state: closure_state): unit =
    match state.work_items with
      [] -> ()
    | ((t,pt),gfwds,gbwd)::rest ->
        state.work_items <- rest;
        if TermMap.mem t state.context2 then
          ()
        else
          (close_one t pt gfwds gbwd state;
           close state)
  in
  let state = node2state n in
  analyze_goal state;
  close state;
  state
