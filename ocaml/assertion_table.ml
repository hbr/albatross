open Container
open Type
open Term
open Proof
open Support

type descriptor = {names: int array; types: typ array;
                   term:term; pt: proof_term option}

type t  = {seq: descriptor seq}

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


type term_descriptor = {
    pt_opt:     proof_term option;
    fwd_set:    FwdSet.t;
    bwd_set:    BwdSet.t
  }


module TermMap = Map.Make(struct
  let compare = Pervasives.compare
  type t = term
end)


type term_map     = term_descriptor TermMap.t

type proof_pair = term * proof_term


let proof_term (t:term) (tm:term_map): proof_term =
  try
    match (TermMap.find t tm).pt_opt with
      None -> raise Not_found
    | Some pt -> pt
  with Not_found ->
    raise Not_found


let is_proved (t:term) (tm:term_map) =
  try
    let _ = proof_term t tm in
    true
  with Not_found ->
    false


type proved_map   = proof_term TermMap.t
type forward_map  = FwdSet.t TermMap.t
type backward_map = BwdSet.t TermMap.t

type proof_context = {
    mutable proved:     proof_term TermMap.t;
    mutable mp_targets: (term list * term * proof_term) TermMap.t;
    argnames:          int array;
    argtypes:          typ array;
    class_table:        Class_table.t;
    feature_table:      Feature_table.t;
    assertion_table:    t
  }

(*
module CTXT = struct
  let empty
      (argnames: int array)
      (argtypes: typ array)
      (ct: Class_table.t)
      (ft: Feature_table.t)
      (at: t)
      : proof_context
      =
    {proved          = TermMap.empty;
     mp_targets      = TermMap.empty;
     argnames        = argnames;
     argtypes        = argtypes;
     class_table     = ct;
     feature_table   = ft;
     assertion_table = at}


  let nbound (c:proof_context): int =
    Array.length c.argnames

  let term_to_string (t:term) (c:proof_context): string =
    Feature_table.term_to_string t c.argnames c.feature_table


  let add_proved (t:term) (pt:proof_term) (c:proof_context): unit =
    c.proved <- TermMap.add t pt c.proved


  let add_mp_target
      (target:  term)
      (premises:term list)
      (term:    term)
      (pt:      proof_term)
      (c:       proof_context)
      : unit =
    c.mp_targets <- TermMap.add target (premises,term,pt) c.mp_targets


  let term (ie:info_expression) (c:proof_context): term =
    Feature_table.assertion_term ie
      c.argnames c.argtypes c.class_table c.feature_table

  let find_proved (t:term) (c:proof_context): proof_term =
    TermMap.find t c.proved

  let discharge
      (ass:term list)
      (t:term)
      (pt:proof_term)
      (c:proof_context)
      : term * proof_term =
    (* Discharge all assumptions of the context 'c' in the term 't' and its
       corresponding proof term 'pt'. *)
    let rec dischrg ass t pt  =
      match ass with
        [] -> t,pt
      | f::tl ->
          let t,pt = dischrg tl t pt in
          Feature_table.implication_term f t (nbound c) c.feature_table,
          Discharge (f,pt)
    in
    dischrg ass t pt
end





let prove_in_context
    (ie: info_expression)
    (ctxt: proof_context)
    :
    term * proof_term =
  let term = CTXT.term ie ctxt in
  try
    let pt = CTXT.find_proved term ctxt in
    term,pt
  with Not_found ->
    assert false
*)


let header_to_string
    (names: int array)
    (types: typ array)
    (ct: Class_table.t)
    (ft:Feature_table.t)
    : string =
  let nargs = Array.length names in
  assert (nargs = (Array.length types));
  let args = Array.init
      nargs
      (fun i ->
        (ST.string names.(i))
        ^ ":"
        ^ (Class_table.type2string types.(i) 0 ct))
  in
  "all"
  ^ (
    if nargs=0 then " "
    else "(" ^ (String.concat "," (Array.to_list args)) ^ ")"
   )


let assertion_to_string
    (d:descriptor)
    (ct:Class_table.t)
    (ft:Feature_table.t): string =
  (header_to_string d.names d.types ct ft)
  ^ " "
  ^ (Feature_table.term_to_string d.term d.names ft)







let proof_term (t:term) (tm:term_map): proof_term =
  (* The proof term associated with the term 't' within the term map 'tm'
     raise Not_found if there is none *)
  let desc = TermMap.find t tm in
  match desc.pt_opt with
    Some pt -> pt
  | None -> raise Not_found



let consequences (t:term) (pt:proof_term) (tm:term_map): proof_pair list =
  (* The direct consequences of the term 't' with the proof term 'pt' within
     the term map 'tm', i.e. if 'tm' has a proved term 't=>u' then 'u' is
     one of the direct consequences of 't' *)
  try
    let lst = FwdSet.elements (TermMap.find t tm).fwd_set in
    List.map (fun (b,pt_imp) -> b,MP(pt,pt_imp)) lst
  with
    Not_found -> []



let add_term_tm
    (t:term)
    (pt:proof_term)
    (tm:term_map)
    : term_map =
  (* Add the term 't' with the proof term 'pt' to the term map 'tm' *)
  TermMap.add
    t
    begin
      try
        let d0 = TermMap.find t tm in
        {d0 with
         pt_opt  = Some pt}
      with Not_found ->
        {pt_opt  = Some pt;
         fwd_set = FwdSet.empty;
         bwd_set = BwdSet.empty}
    end
    tm



let add_forward_tm
    (a:term)
    (b:term)
    (pt:proof_term)
    (tm:term_map)
    : term_map =
  (* Add the  implication 'a=>b' with the proof term 'pt' to the forward set
     of the term 'a' in term map 'tm', i.e. add the conclusion 'b' and the
     proof term 'pt' of the implication *)
  TermMap.add
    a
    begin
      try
        let d0 = TermMap.find a tm in
        {d0 with fwd_set = FwdSet.add (b,pt) d0.fwd_set}
      with Not_found ->
        {pt_opt  = None;
         fwd_set = FwdSet.singleton (b,pt);
         bwd_set = BwdSet.empty}
    end
    tm




let add_backward_tm
    (chain: (term list * term) list)
    (pt:proof_term)
    (tm:term_map)
    : term_map =
  (* Add the implication chain 'a=>b=>...=>z' give as the list
     [[],a=>b=>...=>z; [a],b=>...=>z; [a,b],...=>z; ... ] with the proof
     term 'pt' to the backward set of the corresponding target in the
     term map 'tm' *)
  let add_one premises target tm =
    let n = List.length premises in
    let e = (n,premises,pt) in
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
      tm
  in
  let rec add lst tm =
    match lst with
      [] -> tm
    | (premises,target)::tl ->
        add tl (add_one premises target tm)
  in
  add chain tm




let prove
    (argnames: int array)
    (argtypes: typ array)
    (pre: compound)
    (chck: compound)
    (post: compound)
    (ct: Class_table.t)
    (ft: Feature_table.t)
    (at:t)
    : (term * proof_term) list =
  (* Prove the top level assertion with the formal arguments 'argnames' and
     'argtypes' and the body 'pre' (preconditions), 'chck' (the intermediate
     assertions) and 'post' (postconditions) and return the list of all
     discharged terms and proof terms of the postconditions
   *)
  let traceflag = ref false in
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
    Printf.printf "\n%s\n" (header_to_string argnames argtypes ct ft)

  and trace_string (str:string) (l:int) (): unit =
    Printf.printf "%s%s\n" (level_string l) str

  and trace_term (str:string) (t:term) (l:int) (): unit =
    let len = String.length str in
    let str1 = (if len<10 then str ^ (blank_string (10-len)) else str) ^ "  "
    in
    Printf.printf "%s%s%s\n" (level_string l) str1 (term2string t)

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
  let add_one_tm
      (t:term)
      (pt:proof_term)
      (level:int)
      (split: term -> term*term)
      (chain: term -> (term list * term) list)
      (tm:term_map)
      : term_map =
    (* Add the term 't' with the proof term 'pt' to the term map 'tm' *)
    do_trace (trace_term "Context" t level);
    let tm = add_term_tm t pt tm in
    let tm =
      try
      let a,b = split t in
      add_forward_tm a b pt tm
      with Not_found ->
        tm
    in
    let chn = chain t in
    let res =
      add_backward_tm chn pt tm
    in
    assert (is_proved t res);
    res
  in

  let add_tm_close
      (t:term)
      (pt:proof_term)
      (level: int)
      (split: term -> term*term)
      (chain: term -> (term list * term) list)
      (tm:term_map)
      : term_map =
    (* Add the term 't' with the proof term 'pt' to the term map 'tm' and
       close it *)
    let step_close
        (t:term)
        (pt:proof_term)
        (lst: proof_pair list)
        (tm:term_map)
        : proof_pair list =
      let l1 = (consequences t pt tm) @ lst in
      try
        let a,b = split t in
        let pta = proof_term a tm in
        (b, MP(pta,pt)) :: l1
      with Not_found -> l1
    in
    let rec add (lst: proof_pair list) (tm:term_map): term_map =
      match lst with
        [] -> tm
      | (t,pt)::tl ->
          if is_proved t tm then
            add tl tm
          else
            add
              (step_close t pt tl tm)
              (add_one_tm t pt level split chain tm)
    in
    add [t,pt] tm
  in

  let rec prove_one
      (t:term)
      (tm:term_map)
      (tried: TermSet.t)
      (level: int)
      : proof_term =
    (* Prove the term 't' within the term map 'tm' where all terms
       within the set 'tried' have been tried already on the stack
     *)
    begin
      do_trace (trace_term "Goal" t level);
    end;
    begin
      if TermSet.mem t tried then
        (do_trace (trace_term  "Failure (loop)"  t level);
         raise Cannot_prove)
      else ()
    end;
    let tried = TermSet.add t tried in
    try (* backward, enter, expand *)
      begin
        try
          let bwd_set = (TermMap.find t tm).bwd_set in
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
                      (fun t -> prove_one t tm tried (level+2))
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
          let tm = add_tm_close a (Assume a) (level+1) split chain tm in
          try
            let ptb = prove_one b tm tried (level+1) in
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
      (tm:term_map)
      (level: int)
      : term_map * (term*proof_term) list =
    List.fold_left
      (fun res ie ->
        let tm,lst = res in
        let t = exp2term ie in
        let tnormal = normal t in
        let pt =
          try
            do_trace (trace_term "User goal" t level);
            prove_one tnormal tm TermSet.empty (level+1)
          with Cannot_prove ->
            do_trace (trace_term "User failure" t level);
            raise (Cannot_prove_info  ie.i)
        in
        do_trace (trace_term "User success" t level);
        add_tm_close tnormal pt (level+1) split chain tm,
        (tnormal,pt)::lst
      )
      (tm,[])
      c
  in

  let prove_toplevel () : (proof_pair) list =
    do_trace trace_header;
    let tm_pre: term_map =
      List.fold_left
        (fun tm t ->
          do_trace (trace_term "Assumption" t 1);
          let tn = normal t in
          add_tm_close tn (Assume tn) 2 split chain tm)
        TermMap.empty
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

let empty () = {seq = Seq.empty () }

let put
    (entlst: entities list withinfo)
    (bdy:feature_body)
    (ct: Class_table.t)
    (ft: Feature_table.t)
    (at:t): unit =
  let push_axiom (argnames: int array) (argtypes: typ array) (t:term) =
    let desc = {names=argnames; types=argtypes; term=t; pt=None}
    in
    Printf.printf "axiom   %s\n" (assertion_to_string desc ct ft);
    Seq.push at.seq desc
  and push_proved (argnames: int array) (argtypes: typ array)
      (t:term) (pt:proof_term): unit =
    let desc = {names=argnames; types=argtypes; term=t; pt= Some pt}
    in
    Printf.printf "proved  %s\n" (assertion_to_string desc ct ft);
    Seq.push at.seq desc
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




let print (ct:Class_table.t) (ft:Feature_table.t) (at:t): unit =
  Seq.iter
    (fun desc -> Printf.printf "%s\n" (assertion_to_string desc ct ft))
    at.seq
