open Container
open Type
open Term
open Proof
open Support

exception Cannot_prove
exception Proof_found of proof_term
exception Cannot_prove_info of info



module TermSet = Set.Make(struct
  let compare = Pervasives.compare
  type t = term
end)



module FwdSet = Set.Make(struct
  type t = term * proof_term
        (* conclusion b
           proof term of the implication a=>b *)
  let compare (x:t) (y:t) =
    let b1,_ = x
    and b2,_ = y in
    Pervasives.compare b1 b2
end)



module BwdSet = Set.Make(struct
  type t = int * term list * proof_term
        (* number of premises
           list of premises  [a,b,c,...]
           proof_term of  the implication a=>b=>...=>z*)
  let compare (x:t) (y:t) =
    let n1,ps1,_ = x
    and n2,ps2,_ = y
    in
    let cmp0 = Pervasives.compare n1 n2 in
    if cmp0=0 then
      Pervasives.compare ps1 ps2
    else
      cmp0
end)



module TermMap = Map.Make(struct
  let compare = Pervasives.compare
  type t = term
end)





module Context: sig

  type t
  val empty: t
  val count: t -> int
  val proof_term:   term -> t -> proof_term
  val is_proved:    term -> t -> bool
  val backward_set: term -> t -> BwdSet.t
  val consequences: term -> proof_term -> t -> proof_pair list
  val add_proof:    term -> proof_term -> t -> t
  val add_forward:  term -> term -> proof_term -> t -> t
  val add_backward: (term list * term) list -> proof_term -> t -> t

end = struct

  type term_descriptor = {
      pt_opt:     proof_term option;
      fwd_set:    FwdSet.t;
      bwd_set:    BwdSet.t
    }

  type t = {
      map:   term_descriptor TermMap.t;
      count: int       (* number of proofs in the context *)
     }

  let empty: t = {map = TermMap.empty; count=0}

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

  let backward_set (t:term) (c:t): BwdSet.t =
    (TermMap.find t c.map).bwd_set

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
          {map = TermMap.add t {d0 with pt_opt = Some pt} c.map;
           count = c.count + 1}
      | Some _ -> c
    with Not_found ->
      {map = TermMap.add t {pt_opt = Some pt;
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
    {map =
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
       c.map;
     count = c.count}


  let add_backward
      (chain: (term list * term) list)
      (pt:proof_term)
      (c:t)
      : t =
    (* Add the implication chain 'a=>b=>...=>z' give as the list
     [[],a=>b=>...=>z; [a],b=>...=>z; [a,b],...=>z; ... ] with the proof
       term 'pt' to the backward set of the corresponding target in the
       context 'c' *)
    let add_one premises target c =
      let n = List.length premises in
      let e = (n,premises,pt)
      and tm = c.map
      and count = c.count
      in
      {map =
       TermMap.add
         target
         begin
           try
             let d0 = TermMap.find target tm in
             {d0 with bwd_set = BwdSet.add e d0.bwd_set}
           with Not_found ->
             {pt_opt  = None;
              fwd_set = FwdSet.empty;
              bwd_set = BwdSet.singleton e}
         end
         tm;
       count = count}
    in
    let rec add lst c =
      match lst with
        [] -> c
      | (premises,target)::tl ->
          add tl (add_one premises target c)
    in
    add chain c

end

type tried_map    = Context.t TermMap.t





let assertion_to_string
    (names: int array)
    (types: typ array)
    (term: term)
    (ct:Class_table.t)
    (ft:Feature_table.t): string =
  "all"
  ^ (Class_table.arguments_to_string names types ct)
  ^ " "
  ^ (Feature_table.term_to_string term names ft)










let prove
    (argnames: int array)
    (argtypes: typ array)
    (pre: compound)
    (chck: compound)
    (post: compound)
    (ct: Class_table.t)
    (ft: Feature_table.t)
    (at: Assertion_table.t)
    : (term * proof_term) list =
  (* Prove the top level assertion with the formal arguments 'argnames' and
     'argtypes' and the body 'pre' (preconditions), 'chck' (the intermediate
     assertions) and 'post' (postconditions) and return the list of all
     discharged terms and proof terms of the postconditions
   *)
  let traceflag = ref true in
  let do_trace (f:unit->unit): unit =
    if !traceflag then f () else ()
  in
  let arglen = Array.length argnames in
  let exp2term ie =  Feature_table.assertion_term ie argnames argtypes ct ft
  and term2string t = Feature_table.term_to_string t argnames ft
  and split = fun t -> Feature_table.split_implication t arglen ft
  and chain = fun t -> Feature_table.implication_chain t arglen ft
  and normal (t:term): term =
    let texp = Feature_table.expand_term t arglen ft in
    Term.reduce texp
  in

  let blank_string (i:int): string =
    assert (0<=i);
    let rec str i s =
      if i=0 then s
      else str (i-1) (s ^ " ")
    in
    str i ""
  in

  let level_string (i:int): string =
    assert (0<=i);
    blank_string (2*i)
  in

  let trace_header (): unit =
    Printf.printf "\nall%s\n"
      (Class_table.arguments_to_string argnames argtypes ct)

  and trace_string (str:string) (l:int) (): unit =
    Printf.printf "%s%s\n" (level_string l) str

  and trace_term (str:string) (t:term) (l:int) (): unit =
    Printf.printf "%s%-12s %s\n" (level_string l) str (term2string t)

  and trace_tagged_string (tag:string) (str:string) (l:int) (): unit =
    Printf.printf "%s%-12s%s\n" (level_string l) tag str

  and trace_premises (lst:term list) (l:int) (): unit =
    let n = List.length lst in
    if n>0 then
      let lstr = String.concat "," (List.map term2string lst) in
      Printf.printf "%sPremises [%s]\n" (level_string l) lstr
    else
      Printf.printf "%sGoal already in the context\n" (level_string l)
  in

  let pre_terms: term list = List.rev_map exp2term pre
  in

  (*let chain2string chn =
    "["
    ^ (String.concat "; "
         (List.map
            (fun (ps,t) ->
              "["
              ^ (String.concat "," (List.map (fun a -> term2string a) ps))
              ^ "]," ^ (term2string t))
            chn))
    ^ "]"
  in*)
  let add_one_ctxt
      (t:term)
      (pt:proof_term)
      (level:int)
      (split: term -> term*term)
      (chain: term -> (term list * term) list)
      (c:Context.t)
      : Context.t =
    (* Add the term 't' with the proof term 'pt' to the term map 'tm' *)
    do_trace (trace_term "Context" t level);
    let c = Context.add_proof t pt c in
    let c =
      try
      let a,b = split t in
      Context.add_forward a b pt c
      with Not_found ->
        c
    in
    let chn = chain t in
    let res =
      Context.add_backward chn pt c
    in
    assert (Context.is_proved t res);
    res
  in

  let add_ctxt_close
      (t:term)
      (pt:proof_term)
      (level: int)
      (split: term -> term*term)
      (chain: term -> (term list * term) list)
      (c:Context.t)
      : Context.t =
    (* Add the term 't' with the proof term 'pt' to the context 'c' and
       close it *)
    let step_close
        (t:term)
        (pt:proof_term)
        (lst: proof_pair list)
        (c:Context.t)
        : proof_pair list =
      let l1 = (Context.consequences t pt c) @ lst in
      try
        let a,b = split t in
        let pta = Context.proof_term a c in
        (b, MP(pta,pt)) :: l1
      with Not_found -> l1
    in
    let rec add (lst: proof_pair list) (c:Context.t): Context.t =
      match lst with
        [] -> c
      | (t,pt)::tl ->
          if Context.is_proved t c then
            add tl c
          else
            add
              (step_close t pt tl c)
              (add_one_ctxt t pt level split chain c)
    in
    add [t,pt] c
  in

  let rec prove_one
      (t:term)
      (c:Context.t)
      (tried: tried_map)
      (globals: IntSet.t)
      (level: int)
      : proof_term =
    (* Prove the term 't' within the term map 'tm' where all terms
       within the map 'tried' have been tried already on the stack
       with a corresponding term map.
     *)
    assert (level < 100); (* to detect potential endless loops !! *)
    begin
      do_trace (trace_term "Goal" t level);
    end;
    begin
      (* Bail out if the goal has already been tried in the same context *)
      try
        let c0 = TermMap.find t tried in
        if (Context.count c0) < (Context.count c) then
          ()
        else
          (do_trace (trace_term  "Failure (loop)"  t level);
           raise Cannot_prove)
      with Not_found -> ()
    end;
    let tried = TermMap.add t c tried in

    (*let bwd_glob =
      if IntSet.is_empty globals then
        Assertion_table.find_backward t arglen ft at
      else
        []
    in*)
    let bwd_glob =
      Assertion_table.find_backward t arglen ft at
    in
    let c,globals =
      List.fold_left
        (fun (c,g) ((t,pt),idx) ->
          do_trace (trace_tagged_string
                      "Global"
                      (Assertion_table.to_string idx ct ft at)
                      level);
          add_ctxt_close t pt (level+1) split chain c,
          IntSet.add idx g
        )
        (c,globals)
        bwd_glob
    in
    try (* backward, enter *)
      begin
        try
          let bwd_set = Context.backward_set t c in
          begin
            let n = BwdSet.cardinal bwd_set in
            if n>0 then
              do_trace (trace_string
                          ("Trying up to "
                           ^ (string_of_int n)
                           ^ " alternative(s)")
                          level)
            else ()
          end;
          let _ = BwdSet.iter
              (fun (_,premises,pt) ->
                try
                  do_trace (trace_premises premises (level+1));
                  let pt_lst =
                    List.rev_map
                      (fun t -> prove_one t c tried globals (level+2))
                      premises
                  in
                  let rec use_premises
                      (lst: proof_term list)
                      (pt:  proof_term)
                      : proof_term =
                    match lst with
                      [] -> pt
                    | pt1::tl ->
                        MP (pt1, use_premises tl pt)
                  in
                  do_trace (trace_term "Success" t level);
                  raise (Proof_found (use_premises pt_lst pt))
                with Cannot_prove -> ()
              )
              bwd_set
          in ()
        with Not_found -> ()
      end;
      begin
        try
          let a,b = split t in
          do_trace (trace_term "Enter" a level);
          let c = add_ctxt_close a (Assume a) (level+1) split chain c in
          try
            let ptb = prove_one b c tried globals (level+1) in
            do_trace (trace_term "Success" t level);
            raise (Proof_found (Discharge (a,ptb)))
          with Cannot_prove -> ()
        with Not_found -> () (* expand *)
      end;
      do_trace (trace_term "Failure" t level);
      raise Cannot_prove
    with
      Proof_found pt -> pt
  in

  let proof_compound
      (c:compound)
      (ctxt:Context.t)
      (level: int)
      : Context.t * (term*proof_term) list =
    List.fold_left
      (fun res ie ->
        let ctxt,lst = res in
        let t = exp2term ie in
        let tnormal = normal t in
        let pt =
          try
            do_trace (trace_term "User goal" t level);
            prove_one tnormal ctxt TermMap.empty IntSet.empty (level+1)
          with Cannot_prove ->
            do_trace (trace_term "User failure" t level);
            raise (Cannot_prove_info  ie.i)
        in
        do_trace (trace_term "User success" t level);
        add_ctxt_close tnormal pt (level+1) split chain ctxt,
        (t,pt)::lst
      )
      (ctxt,[])
      c
  in

  let prove_toplevel () : (proof_pair) list =
    do_trace trace_header;
    let tm_pre: Context.t =
      List.fold_left
        (fun c t ->
          do_trace (trace_term "Assumption" t 1);
          let tn = normal t in
          add_ctxt_close tn (Assume tn) 2 split chain c)
        Context.empty
        pre_terms
    in
    let tm_inter,_ = proof_compound chck tm_pre 1
    in
    let _,revlst = proof_compound post tm_inter 1
    in
    let rec discharge (pre: term list) (t:term) (pt:proof_term)
        : term * proof_term =
      match pre with
        [] -> t,pt
      | f::tl ->
          discharge
            tl (Feature_table.implication_term f t arglen ft) (Discharge (f,pt))
    in
    List.rev_map
      (fun (t,pt) ->
        discharge pre_terms t pt)
      revlst

  in

  try
    prove_toplevel ()
  with Cannot_prove_info i ->
    if not !traceflag then
      begin
        traceflag := true;
        try
          prove_toplevel ()
        with Cannot_prove_info i ->
          error_info i "Cannot prove"
      end
    else
      error_info i "Cannot prove"








(*   Public functions *)

let prove_and_store
    (entlst: entities list withinfo)
    (bdy:feature_body)
    (ct: Class_table.t)
    (ft: Feature_table.t)
    (at: Assertion_table.t): unit =
  let push_axiom (argnames: int array) (argtypes: typ array) (t:term) =
    Printf.printf "%3d axiom   %s\n"
      (Assertion_table.count at)
      (assertion_to_string argnames argtypes t ct ft);
    Assertion_table.put_axiom argnames argtypes t ft at
  and push_proved (argnames: int array) (argtypes: typ array)
      (t:term) (pt:proof_term): unit =
    Printf.printf "%3d proved  %s\n"
      (Assertion_table.count at)
      (assertion_to_string argnames argtypes t ct ft);
    Assertion_table.put_proved argnames argtypes t pt ft at
  in
  let argnames,argtypes = Class_table.arguments entlst ct in
  match bdy with
    _, _, None ->
      error_info entlst.i "Assertion must have an ensure clause"
  | rlst_opt, imp_opt, Some elst ->
      let rlst = match rlst_opt with None -> [] | Some l -> l
      and axiom,is_do,clst =
        match imp_opt with
          None -> false,false,[]
        | Some Impdeferred ->
            not_yet_implemented entlst.i "Deferred assertions"
        | Some Impbuiltin -> (
            true,false,[]
           )
        | Some Impevent ->
            error_info entlst.i "Assertion cannot be an event"
        | Some (Impdefined (Some locs,is_do,cmp)) ->
            not_yet_implemented entlst.i "Local variables in assertions"
        | Some (Impdefined (None,is_do,cmp)) ->
            false,is_do,cmp
      in
      if axiom then
        match rlst with
          [] ->
            List.iter
              (fun ie ->
                let term =
                  Feature_table.assertion_term ie argnames argtypes ct ft in
                let _ = Term.normalize argtypes term in
                push_axiom argnames argtypes term)
              elst
        | _ ->
            not_yet_implemented entlst.i "axioms with preconditions"
      else if is_do then
        not_yet_implemented entlst.i "Assertions with do block"
      else
        let lst =
          if Feature_table.has_implication ft then
            prove argnames argtypes rlst clst elst ct ft at
          else
            error_info entlst.i "\"=>\" is not yet defined"
        in
        List.iter
          (fun (t,pt) -> push_proved argnames argtypes t pt)
          lst




