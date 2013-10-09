open Term
open Container
open Proof


type proved_term = {
    pair: proof_pair;
    used_forward: IntSet.t;   (* the used non simplifying forward rules *)
  }

let compare_proved (a:proved_term) (b:proved_term): int =
  let t1,_ = a.pair
  and t2,_ = b.pair
  in
  Pervasives.compare t1 t2


type node = {
    goal:           term;
    count:          int;
    context:        TermSet.t;
    used_backward:  IntSet.t; (* the used non simplifying backward rules *)
    global:         General_context.t;
    local:          General_context.t;
    narguments:     int;
    implication_id: int;
  }


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
    


type work_item = proof_pair * IntSet.t (* used global forward rules *)

type closure_state = {
    narguments2:        int;
    global2:            General_context.t;
    mutable context2:   TermSet.t;
    mutable work_items: work_item list;
  }





let c_state (n:node) (work_items: work_item list): closure_state =
  {narguments2 = n.narguments;
   global2     = n.global;
   context2    = n.context;
   work_items  = work_items}







let close_one
    (t:term)
    (pt:proof_term)
    (gfwds: IntSet.t)
    (state: closure_state)
    : unit  =
  assert (not (TermSet.mem t state.context2));

  (* Add to context *)
  state.context2 <- TermSet.add t state.context2;

  (* Add global forward rules *)
  List.iter
    (fun (nargs,idx,(t,_),sub,simpl,nopen) ->
      let gfwds = if simpl then IntSet.empty else IntSet.singleton idx
      in
      let tt = Term_sub.apply_0 t nargs sub (nopen=0) in
      let tt = if nopen=0 then tt else Lam(nargs,tt) in
      state.work_items <-
          ((tt,Specialize(Theorem idx,sub)),gfwds)::state.work_items
    )
    (General_context.forward t state.narguments2 state.global2);

  (* Apply local forward rules *)

  (* Add term as potential backward rule *)

  (* Apply term as potential forward rule *)
  assert false





let close_node (n:node): node =
  let rec close (state: closure_state): unit =
    match state.work_items with
      [] -> ()
    | ((t,pt),gfwds)::rest ->
        state.work_items <- rest;
        if TermSet.mem t state.context2 then
          ()
        else
          (close_one t pt gfwds state;
           close state)
  in
  let chain = Term.implication_chain n.goal (n.implication_id+n.narguments) in
  let goals = List.map (fun (premises,target) -> target) chain
  and premises = match chain with
    (ps,_)::_ -> ps
  | _ -> assert false
  in
  let work_items =
    (assert false) @
    (List.map (fun p -> (p,Assume p), IntSet.empty) premises)
  in
  let state = c_state n work_items in 
  close state;
  assert false
