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










type tried_map    = Local_context.t TermMap.t



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
let nfailed = ref 0
let inc_goals ()   =  ngoals  := !ngoals + 1
let inc_failed ()  =  nfailed := !nfailed + 1
let reset_goals () =  ngoals  := 0; nfailed := 0






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
  let imp_id = (Feature_table.implication_index ft) + arglen in
  let exp2term ie =  Feature_table.assertion_term ie argnames argtypes ct ft
  and term2string t = Feature_table.term_to_string t argnames ft
  and split = fun t -> Term.binary_split t imp_id
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

  and trace_premises (lst:term list) (l:int) (): unit =
    let n = List.length lst in
    if n>0 then
      let lstr = String.concat "," (List.map term2string lst) in
      Printf.printf "%3d %sPremises [%s]\n" l (level_string l) lstr
    else
      Printf.printf "%3d %sGoal already in the context\n" l (level_string l)

  and trace_context (c:Local_context.t) (l:int) (): unit =
    let lst = Local_context.proved_terms c in
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
      (c:Local_context.t)
      : Local_context.t =
    (* Add the term 't' with the proof term 'pt' to the term map 'tm' *)
    let c = Local_context.add_proof t pt c in
    let c =
      try
      let a,b = split t in
      Local_context.add_forward a b pt c
      with Not_found ->
        c
    in
    let chn = chain t in
    let res =
      Local_context.add_backward chn pt c
    in
    assert (Local_context.is_proved t res);
    res
  in

  let add_ctxt_close
      (t:term)
      (pt:proof_term)
      (level: int)
      (split: term -> term*term)
      (chain: term -> (term list * term) list)
      (c:Local_context.t)
      : Local_context.t =
    (* Add the term 't' with the proof term 'pt' to the context 'c' and
       close it *)
    let step_close
        (t:term)
        (pt:proof_term)
        (lst: proof_pair list)
        (c:Local_context.t)
        : proof_pair list =
      let lglobal =
        (Assertion_table.consequences t (Array.length argtypes) ft at)
      in
      let l1 =
        (Local_context.consequences t pt c)
        @ (List.map (fun ((t,pt),_) -> t,pt) lglobal)
        @ lst in
      try
        let a,b = split t in
        let pta = Local_context.proof_term a c in
        (b, MP(pta,pt)) :: l1
      with Not_found -> l1
    in
    let rec add (lst: proof_pair list) (c:Local_context.t): Local_context.t =
      match lst with
        [] -> c
      | (t,pt)::tl ->
          if Local_context.is_proved t c then
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
      (c:Local_context.t)
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

    let global_backward (t:term) (c:Local_context.t): Local_context.t =
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
    let do_backward (t:term) (c:Local_context.t) (tried:tried_map): unit =
      (* Backward reasoning *)
      let c = global_backward t c in
      do_trace (trace_context c (level+1));
      let bwd_set = Local_context.backward_set t c in
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

    and enter (t:term) (c:Local_context.t): term * Local_context.t =
      (* Check the term and split implications recursively *)
      let direct (t:term) (c:Local_context.t): Local_context.t =
        let c = global_backward t c in
        try
          let pt = Local_context.proof_term t c in
          do_trace (trace_term "Success" t level);
          raise (Proof_found pt);
        with Not_found ->
          c
      in
      let rec ent (t:term) (c:Local_context.t) (entered:bool)
          : term * Local_context.t * bool =
        try
          let a,b = split t in
          do_trace (trace_term "Enter" a level);
          let c = add_ctxt_close a (Assume a) (level+1) split chain c in
          let c = direct b c in
          ent b c true
        with Not_found ->
          t,c,false
      in
      let c = direct t c in
      let t,c,entered = ent t c false in
      if entered then
        (do_trace (trace_term "Goal" t level);
         t,c)
      else
        t,c

    in
    do_trace (trace_term "Goal" t level);
    begin
      (* Bail out if the goal has already been tried in the same context *)
      try
        let c0 = TermMap.find t tried in
        if (Local_context.count c0) < (Local_context.count c) then
          ()
        else
           (do_trace (trace_term  "Failure (loop)"  t level);
            inc_failed ();
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
         reset_goals ();
         raise Goal_limit)
      else
        ()
    end;
    inc_goals ();
    begin
      try
        let t,c = enter t c in
        do_backward t c tried;
        do_trace (trace_term "Failure" t level);
        inc_failed ();
        raise Cannot_prove
      with
        Proof_found pt ->
          (*let global (idx:int): int*term =
            Assertion_table.term idx at
          in
          let imp_idx = Feature_table.implication_index ft in
          let tt = Checker.term pt arglen imp_idx global in
          (if t<>tt then
            Printf.printf "t  = %s\ntt = %s\n"
              (Feature_table.term_to_string t argnames ft)
              (Feature_table.term_to_string tt argnames ft)
          else ());*)
          (*assert (t = tt);*)
          pt
    end
  in

  let prove_compound
      (c:compound)
      (ctxt:Local_context.t)
      (level: int)
      : Local_context.t * (term*proof_term) list =
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
        Statistics.proof_done !ngoals !nfailed;
        reset_goals ();
        add_ctxt_close tnormal pt (level+1) split chain ctxt,
        (t,pt)::lst
      )
      (ctxt,[])
      c
  in

  let prove_toplevel () : (proof_pair) list =
    do_trace trace_header;
    let tm_pre: Local_context.t =
      List.fold_left
        (fun c t ->
          do_trace (trace_term "Assumption" t 1);
          let tn = normal t in
          add_ctxt_close tn (Assume tn) 2 split chain c)
        Local_context.empty
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

  let fgnames, concepts, argnames,argtypes =
    Class_table.argument_signature entlst ct in
  assert ((Array.length fgnames) = 0);
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
