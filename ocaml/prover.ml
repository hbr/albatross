open Container
open Type
open Term
open Proof
open Support

exception Cannot_prove
exception Cannot_prove_info of info
exception Goal_limit
exception Goal_limit_info of info
exception Proof_found of proof_term



module SizedTerm: sig
  type t
  val item: t -> term
  val make: term -> t
  val compare: t -> t -> int
end = struct
  type t = {size:int; term:term}
  let item (st:t): term =
    st.term
  let make (t:term): t =
    {size = Term.nodes t; term=t}
  let compare (a:t) (b:t): int =
    let cmp = Pervasives.compare a.size b.size in
    if cmp = 0 then
      Pervasives.compare a.term b.term
    else
      cmp
end

module SizedTermSet = Set.Make(struct
  let compare = SizedTerm.compare
  type t = SizedTerm.t
end)



module TermSetSet = Set.Make(struct
  let compare = Pervasives.compare
  type t = TermSet.t
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
  type t = int * TermSet.t * term list * proof_term
        (* number of premises
           list of premises  [a,b,c,...]
           proof_term of  the implication a=>b=>...=>z*)
  let compare (x:t) (y:t) =
    let n1,_,ps1,_ = x
    and n2,_,ps2,_ = y
    in
    let cmp0 = Pervasives.compare n1 n2 in
    if cmp0=0 then
      Pervasives.compare ps1 ps2
    else
      cmp0
end)



module AttemptMap = Map.Make(struct
  let compare = Pervasives.compare
  type t = term * TermSet.t
end)

type attempt_map = (proof_term option) AttemptMap.t




module Context: sig

  type t
  val empty: t
  val count: t -> int
  val proof_term:   term -> t -> proof_term
  val is_proved:    term -> t -> bool
  val proved_terms: t -> proof_pair list
  val proved_set:   t -> TermSet.t
  val backward_set: term -> t -> BwdSet.t
  val consequences: term -> proof_term -> t -> proof_pair list
  val add_proof:    term -> proof_term -> t -> t
  val add_forward:  term -> term -> proof_term -> t -> t
  val add_backward: (term list * term) list -> proof_term -> t -> t
  val one_eliminated: term -> t -> proof_pair * t

end = struct

  type term_descriptor = {
      pt_opt:     proof_term option;
      fwd_set:    FwdSet.t;
      bwd_set:    BwdSet.t
    }

  type elimination_descriptor = {
      elim_term:      term; (* term to be eliminated *)
      n_bound:        int;  (* of the environment of the term *)
      assertion_term: term;
      assertion_idx:  int;
      args:           term array;
      var_target:     int
    }

  type t = {
      map:   term_descriptor TermMap.t;
      elims: elimination_descriptor list;
      eliminated: TermSet.t; (* eliminated terms, subset of proved terms *)
      count: int;            (* number of proofs in the context *)
      proved_set: TermSet.t; (* set of proofed terms *)
    }

  let empty: t = {
    map = TermMap.empty;
    elims=[];
    eliminated = TermSet.empty;
    count=0;
    proved_set = TermSet.empty
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

  let proved_set (c:t): TermSet.t =
    c.proved_set

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
          {c with
           map   = TermMap.add t {d0 with pt_opt = Some pt} c.map;
           count = c.count + 1;
           proved_set = TermSet.add t c.proved_set}
      | Some _ -> c
    with Not_found ->
      {c with
       map = TermMap.add t {pt_opt = Some pt;
                            fwd_set = FwdSet.empty;
                            bwd_set = BwdSet.empty} c.map;
       count = c.count + 1;
       proved_set = TermSet.add t c.proved_set}


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


  let one_eliminated (t:term) (c:t): proof_pair * t =
    match c.elims with
      [] ->
        raise Not_found
    | elim::tl ->
        let args = Array.copy elim.args in
        args.(elim.var_target) <- t;
        (Term.sub elim.assertion_term elim.args elim.n_bound,
         Specialize (Theorem elim.assertion_idx, args)),
        {c with
         elims = tl;
         eliminated = TermSet.add elim.elim_term c.eliminated}

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




let ngoals = ref 0
let inc_goals () =   ngoals := !ngoals + 1
let reset_goals () = ngoals := 0






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
  let traceflag = ref (Options.is_tracing_proof ()) in
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
    Printf.printf "%3d %s%s\n" l (level_string l) str

  and trace_term (str:string) (t:term) (l:int) (): unit =
    Printf.printf "%3d %s%-12s %s\n" l (level_string l) str (term2string t)

  and trace_tagged_string (tag:string) (str:string) (l:int) (): unit =
    Printf.printf "%3d %s%-12s %s\n" l (level_string l) tag str

  and trace_premises (lst:term list) (l:int) (): unit =
    let n = List.length lst in
    if n>0 then
      let lstr = String.concat "," (List.map term2string lst) in
      Printf.printf "%3d %sPremises [%s]\n" l (level_string l) lstr
    else
      Printf.printf "%3d %sGoal already in the context\n" l (level_string l)

  and trace_context (c:Context.t) (l:int) (): unit =
    let lst = Context.proved_terms c in
    let len = List.length lst in
    if len > 0 then
      (Printf.printf "%3d %sContext\n" l (level_string l);
       Mylist.iteri
         (fun i (t,_) ->
           Printf.printf "%3d %s%2d: %s\n" l (level_string l) i (term2string t)
         )
         lst)
    else
      Printf.printf "%3d %sContext is empty\n" l (level_string l)
  in

  let attempt_map = ref AttemptMap.empty in

  let attempt (t:term) (c:Context.t): bool * proof_term option =
    let tset = Context.proved_set c in
    try
      let pt_opt = AttemptMap.find (t,tset) !attempt_map in
      true, pt_opt
    with
      Not_found ->
        false, None
  in

  let has_attempt (t:term) (c:Context.t): bool =
    let att,pt_opt = attempt t c in
    att (*&& match pt_opt with None -> true | _ -> false*)
  and has_success (t:term) (c:Context.t): bool =
    let att,pt_opt = attempt t c in
    att && match pt_opt with None -> false | _ -> true
  in

  let add_attempt (t:term) (c:Context.t): unit =
    begin
      let tset = Context.proved_set c in
      try
        let _ = AttemptMap.find (t,tset) !attempt_map in
        assert false  (* No repeated attempts! *)
      with Not_found ->
        attempt_map := AttemptMap.add (t,tset) None !attempt_map
    end;
    assert (has_attempt t c)

  and add_success (t:term) (c:Context.t) (pt:proof_term): unit =
    assert (has_attempt t c);
    begin
      let tset = Context.proved_set c in
      try
        let pt_opt_found = AttemptMap.find (t,tset) !attempt_map in
        match pt_opt_found with
          None ->
            attempt_map := AttemptMap.add (t,tset) (Some pt) !attempt_map
        | Some _ ->
            assert false (* No multiple successes! *)
      with Not_found ->
        assert false (* Success can be added only if attempt has
                        been added before *)
    end;
    assert (has_attempt t c);
    assert (has_success t c)

  and reset_attempts (): unit =
    attempt_map := AttemptMap.empty
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
    (*do_trace (trace_term "to context" t level);*)
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
      let lglobal,elims =
        (Assertion_table.consequences t (Array.length argtypes) ft at)
      in
      (* assert (elims = []); code for eliminations *)
      let l1 =
        (Context.consequences t pt c)
        @ (List.map (fun ((t,pt),_) -> t,pt) lglobal)
        @ lst in
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
      (level: int)
      : proof_term =
    (* Prove the term 't' within the term map 'tm' where all terms
       within the map 'tried' have been tried already on the stack
       with a corresponding term map.

       The function either returns a proof term for 't' or it raises
       the exception 'Cannot_prove'.
     *)
    assert (level < 500); (* to detect potential endless loops !! *)

    let global_backward (t:term) (c:Context.t): Context.t =
      (* The backward set from the global assertion table *)
      let bwd_glob =
        Assertion_table.find_backward t arglen ft at
      in
      List.fold_left
        (fun c ((t,pt),idx) ->
          (*do_trace (trace_tagged_string
                      "Global(bwd)"
                      (Assertion_table.to_string idx ct ft at)
                      level);*)
          add_ctxt_close t pt (level+1) split chain c
        )
        c
        bwd_glob
    in
    let do_elim (c:Context.t): unit =
      (* Check if there is an elimination rule to apply, if
         yes, mark the rule as eliminated and add it to the context
         with the term 't' as target and try to prove the term *)
      try
        let (te,pte), c_elim = Context.one_eliminated t c in
        let ctxt_new = add_ctxt_close te pte (level+1) split chain c_elim
        in
        let pt = prove_one t ctxt_new tried (level+1)
        in
        raise (Proof_found pt)
      with Not_found ->
        ()

    and do_backward (t:term) (c:Context.t) (tried:tried_map): unit =
      (* Backward reasoning *)
      let c = global_backward t c in
      do_trace (trace_context c (level+1));
      let bwd_set = Context.backward_set t c in
      begin
        let n = BwdSet.cardinal bwd_set in
        if n>0 then begin
          do_trace (trace_string
                      ("Trying up to "
                       ^ (string_of_int n)
                       ^ " alternative(s)")
                      level)
        end
          else ()
      end;
      let _ = BwdSet.iter
          (fun (_,_,premises,pt) ->
            try
              do_trace (trace_premises premises (level+1));
              let pt_lst =
                List.rev_map
                  (fun t -> prove_one t c tried (level+2))
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
      in
      (* All alternatives failed (or maybe there are no alternatives) *)
      ()

    and enter (t:term) (c:Context.t): term * Context.t =
      (* Check the term and split implications recursively *)
      let direct (t:term) (c:Context.t): Context.t =
        let c = global_backward t c in
        try
          let pt = Context.proof_term t c in
          do_trace (trace_term "Success" t level);
          raise (Proof_found pt);
        with Not_found ->
          c
      in
      let rec ent (t:term) (c:Context.t) (entered:bool)
          : term * Context.t * bool =
        try
          let a,b = split t in
          do_trace (trace_term "Enter" a level);
          let c = add_ctxt_close a (Assume a) (level+1) split chain c in
          let c = direct b c in
          ent b c true
        with Not_found ->
          t,c,entered
      in
      let c = direct t c in
      let t,c,entered = ent t c false in
      if entered then
        (do_trace (trace_term "Goal" t level);
         t,c)
      else
        t,c

    in
    begin
      do_trace (trace_term "Goal" t level);
      (*do_trace (trace_context c (level+1));*)
    end;
    begin
      (* Bail out if the goal has already been tried in the same context *)
      try
        let c0 = TermMap.find t tried in
        if (Context.count c0) < (Context.count c) then
          ()
        else
           (do_trace (trace_term  "Failure (1stloop)"  t level);
           raise Cannot_prove)
      with Not_found ->
        ()
    end;
    let tried = TermMap.add t c tried
    in

    begin (* Bail out if goal limit is exceeded *)
      if (Options.has_goal_limit ())
          && (Options.goal_limit ()) <= !ngoals then
        (do_trace (trace_term "Failure (goal-limit)" t level);
         raise Goal_limit)
    end;
    inc_goals ();
    begin
      let att,pt_opt = attempt t c in
      if att then
        match pt_opt with
          None ->
            assert (has_attempt t c);
            (do_trace (trace_term  "Failure (2ndloop)"  t level);
             raise Cannot_prove)
        | Some pt ->
            assert (has_success t c);
            pt
      else
        begin
          assert (not (has_attempt t c));
          assert (not (has_success t c));
          (*add_attempt t c;
          assert (has_attempt t c);*)
          try
            let t,c = enter t c in
            do_backward t c tried;
            do_trace (trace_term "Failure" t level);
            raise Cannot_prove
          with
            Proof_found pt ->
              (*assert (has_attempt t c);
              add_success t c pt;*)
              pt
        end
    end
  in

  let prove_compound
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
            prove_one tnormal ctxt TermMap.empty (level+1)
          with Cannot_prove ->
            do_trace (trace_term "User failure" t level);
            raise (Cannot_prove_info  ie.i)
          | Goal_limit ->
            do_trace (trace_term "User failure(goal limit)" t level);
            raise (Goal_limit_info  ie.i)
        in
        do_trace (trace_term "User success" t level);
        Statistics.proof_done !ngoals;
        reset_goals ();
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
    let tm_inter,_ = prove_compound chck tm_pre 1
    in
    let _,revlst = prove_compound post tm_inter 1
    in
    let rec discharge (pre: term list) (t:term) (pt:proof_term)
        : term * proof_term =
      match pre with
        [] -> t,pt
      | f::tl ->
          discharge
            tl
            (Feature_table.implication_term f t arglen ft)
            (Discharge (f,pt))
    in
    List.rev_map
      (fun (t,pt) ->
        discharge pre_terms t pt)
      revlst

  in

  try
    prove_toplevel ()

  with Cannot_prove_info i ->
    if not !traceflag && (Options.is_tracing_failed_proof ()) then
      begin
        traceflag := true;
        reset_attempts ();
        try
          prove_toplevel ()
        with Cannot_prove_info i ->
          error_info i "Cannot prove"
      end
    else
      error_info i "Cannot prove"

  | Goal_limit_info i ->
      let str = "Cannot prove (goal limit "
        ^ (string_of_int (Options.goal_limit ()))
        ^ " exceeded)\n)"
      in
      if not !traceflag && (Options.is_tracing_failed_proof ()) then
        begin
          traceflag := true;
          reset_attempts ();
          try
            prove_toplevel ()
          with Goal_limit_info i ->
          error_info i str
          | _ -> assert false
        end
      else
        error_info i str








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
    Assertion_table.put_proved argnames argtypes t pt ft at;
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
                (* let _ = Term.normalize argtypes term in*)
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




