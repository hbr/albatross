open Term
open Proof


module FwdSet = Set.Make(struct
  type t = term * proof_term
        (* conclusion b
           proof term of the implication a=>b *)
  let compare (x:t) (y:t) =
    let b1,_ = x
    and b2,_ = y in
    Pervasives.compare b1 b2
end)


type term_descriptor = {
    pt_opt:     proof_term option;
    fwd_set:    FwdSet.t;
    bwd_set:    BwdSet.t
  }



type t = {
    map:   term_descriptor TermMap.t;
    count: int;            (* number of proofs in the context *)
  }




let empty: t = {
  map = TermMap.empty;
  count=0
}

  let count (c:t): int = c.count

  let proof_term (t:term) (c:t): proof_term =
    try
      match (TermMap.find t c.map).pt_opt with
        None -> raise Not_found
      | Some pt -> pt
    with Not_found ->
      raise Not_found

  let is_proved (t:term) (c:t) =
    try
      let _ = proof_term t c in
      true
    with Not_found ->
      false


  let proved_terms (c:t): proof_pair list =
    let lst =
      TermMap.fold
        (fun t desc lst ->
          match desc.pt_opt with
            None -> lst
          | Some pt -> (t,pt)::lst
        )
        c.map
        []
    in
    assert (c.count = (List.length lst));
    lst



let backward_set (t:term) (c:t): BwdSet.t =
  try
    (TermMap.find t c.map).bwd_set
  with Not_found ->
    BwdSet.empty



let consequences (t:term) (pt:proof_term) (c:t): proof_pair list =
  (* The direct consequences of the term 't' with the proof term 'pt' within
     the context 'c', i.e. if 'c' has a proved term 't=>u' then 'u' is
     one of the direct consequences of 't' *)
  try
    let lst = FwdSet.elements (TermMap.find t c.map).fwd_set in
    List.map (fun (b,pt_imp) -> b,MP(pt,pt_imp)) lst
  with
    Not_found -> []



let add_proof (t:term) (pt:proof_term) (c:t): t =
  (* Add the term 't' with the proof term 'pt' to the context 'c' *)
  try
    let d0 = TermMap.find t c.map in
    match d0.pt_opt with
      None ->
        {(*c with*)
         map   = TermMap.add t {d0 with pt_opt = Some pt} c.map;
         count = c.count + 1}
    | Some _ -> c
  with Not_found ->
    {(*c with*)
     map = TermMap.add t {pt_opt = Some pt;
                          fwd_set = FwdSet.empty;
                          bwd_set = BwdSet.empty} c.map;
     count = c.count + 1}


let add_forward
    (a:term)
    (b:term)
    (pt:proof_term)
    (c:t)
    : t =
  (* Add the  implication 'a=>b' with the proof term 'pt' to the forward set
     of the term 'a' in the context 'c, i.e. add the conclusion 'b' and the
     proof term 'pt' of the implication *)
  {c with
   map =
   TermMap.add
     a
     begin
       try
         let d0 = TermMap.find a c.map in
         {d0 with fwd_set = FwdSet.add (b,pt) d0.fwd_set}
         with Not_found ->
           {pt_opt  = None;
            fwd_set = FwdSet.singleton (b,pt);
            bwd_set = BwdSet.empty}
     end
     c.map}


let add_backward
    (chain: (term list * term) list)
    (pt:proof_term)
    (c:t)
    : t =
  (* It is assumed that 'a=>b=>...=>z' is proved with the proof term
     'pt'. The term is given as an implication chain. Then add
     'n,[a,b,...],pt' to the backward set of 'z' in the context 'c'
     where 'n' is the number of premises.

     Note that an implication chain has the form:

         [([],a=>b=>...=>z), ([a],b=>...=>z); ..., ([a,b,...],z)]

     i.e. the last element of the list is the interesting one.
   *)
  let add_one premises target c =
    let term_set ts =
      List.fold_left (fun set p -> TermSet.add p set) TermSet.empty ts
    in
    let n = List.length premises
    and pset = term_set premises in
    let e = (n,pset,premises,pt)
    and tm = c.map
    in
    {c with
     map =
     TermMap.add
       target
       begin
         try
           let d0 = TermMap.find target tm in
           if BwdSet.for_all
               (fun (_,pset0,_,_) -> pset0 <> pset)
               d0.bwd_set
           then
             {d0 with bwd_set = BwdSet.add e d0.bwd_set}
           else
             d0
         with Not_found ->
           {pt_opt  = None;
            fwd_set = FwdSet.empty;
            bwd_set = BwdSet.singleton e}
       end
       tm
   }
  in
  let rec add lst c =
    match lst with
      [] -> c
    | [(premises,target)] ->
        add_one premises target c
    | (premises,target)::tl ->
        add tl c
  in
  add chain c
