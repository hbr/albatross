(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Term
open Proof
open Container
open Support
open Printf

module ASeq = Ass_seq

type desc = {nbenv0:     int;
             term:       term;
             proof_term: proof_term;}

type t = {seq:       desc Ass_seq.t;
          names:     int array;
          c:         Context.t;
          depth:     int;
          count0:    int;      (* number of assertions at the start of the context *)
          mutable nreq:  int;  (* number of local assumptions *)
          mutable maxreq: int; (* first index with no more assumptions *)
          mutable reqs: int list;
          prev:      t option;
          verbosity: int}

let context (at:t): Context.t = at.c
let class_table (at:t):   Class_table.t   = Context.class_table at.c
let feature_table (at:t): Feature_table.t = Context.feature_table at.c


let is_private (at:t): bool = Context.is_private at.c
let is_public  (at:t): bool = Context.is_public  at.c
let is_interface_use   (at:t): bool = Context.is_interface_use  at.c
let is_interface_check (at:t): bool = Context.is_interface_check  at.c


let add_used_module (name:int*int list) (used:IntSet.t) (at:t): unit =
  Context.add_used_module name used at.c

let add_current_module (name:int) (used:IntSet.t) (at:t): unit =
  Context.add_current_module name used at.c

let set_interface_check (pub_used:IntSet.t) (at:t): unit =
  Context.set_interface_check pub_used at.c


let depth (at:t): int = at.depth

let is_global (at:t): bool = not (Option.has at.prev)

let is_local (at:t): bool =
  not (is_global at)

let previous (at:t): t =
  match at.prev with
    None -> assert false
  | Some x -> x


let is_toplevel (at:t): bool =
  not (is_global at) && is_global (previous at)


let count (at:t): int =
  Ass_seq.count at.seq

let count_previous (at:t): int =
  at.count0



let count_global (at:t): int =
  Ass_seq.count_first at.seq


let count_last_local (pt:t): int =
  (count pt) - (count_previous pt)


let count_variables (at:t): int = Context.count_variables at.c


let count_last_arguments (at:t): int =
  Context.count_last_arguments at.c

let local_argnames (at:t): int array =
  Context.local_argnames at.c

let has_result (at:t): bool =
  Context.has_result at.c

let has_result_variable (at:t): bool =
  Context.has_result_variable at.c

let last_arguments_string (at:t): string =
  Context.local_arguments_string at.c

let descriptor (i:int) (at:t): desc =
  assert (i < count at);
  Ass_seq.elem i at.seq


let names (at:t): int array =
  at.names

let imp_id (at:t): int =
  Context.implication_index at.c

let split_implication (t:term) (at:t): term * term =
  Term.binary_split t (imp_id at)

let split_all_quantified (t:term) (at:t): int * int array * term =
  Term.all_quantifier_split t

let split_some_quantified (t:term) (at:t): int * int array * term =
  Term.some_quantifier_split t

let implication (a:term) (b:term) (at:t): term =
  Term.binary (imp_id at) a b

let implication_chain (ps: term list) (tgt:term) (at:t): term =
  Term.make_implication_chain ps tgt (imp_id at)

let split_implication_chain (t:term) (at:t): term list * term =
  Term.split_implication_chain t (imp_id at)

let quantified (is_all:bool) (nargs:int) (nms:int array) (t:term) (at:t): term =
  Context.quantified is_all nargs nms t at.c

let all_quantified (nargs:int) (names:int array) (t:term) (at:t): term =
  Context.all_quantified nargs names t at.c

let some_quantified (nargs:int) (names:int array) (t:term) (at:t): term =
  Context.some_quantified nargs names t at.c

let string_of_term (t:term) (at:t): string =
  Context.string_of_term t true 0 at.c

let string_of_term_anon (t:term) (nb:int) (at:t): string =
  Context.string_of_term t true nb at.c


let expand_term (t:term) (at:t): term =
  Context.fully_expanded t 0 at.c


let prepend_names (nms:int array) (names:int array): int array =
  let nms = Feature_table.adapt_names nms names in
  Array.append nms names


let prenex_term (t:term) (at:t): term =
  (* The term [t] in prenex normal form with respect to universal quantifiers *)
  Context.prenex_term t at.c


let equivalent (t1:term) (t2:term) (at:t): bool =
  (* Are the terms equivalent without regarding names and positions of the
     all quantifiers? *)
  let rec equiv t1 t2 imp_id =
    let split (t:term): int * term option * term =
      let n, t0 =
        try
          let n,nms,t0 = Term.all_quantifier_split t in n,t0
        with Not_found -> 0, t in
      let a, b =
        try
          let a,b = Term.binary_split t0 (n+imp_id) in Some a, b
        with Not_found -> None, t0
      in
      n, a, b
    in
    let n1, a1, b1 = split t1
    and n2, a2, b2 = split t2 in
    match a1, a2 with
      None, None when n1 = n2 ->
        true
    | Some a1, Some a2 ->
        if n1 = n2 then
          let imp_id = n1 + imp_id in
          equiv a1 a2 imp_id &&
          equiv b1 b2 imp_id
        else
          let first_less n1 a1 b1 n2 a2 b2 =
            assert (n1 <= n2);
            let gp1_a1 = Term.greatestp1_arg a1 n1
            and gp1_a2 = Term.greatestp1_arg a2 n2 in
            gp1_a1 = gp1_a2 &&
            let imp_id = gp1_a1+imp_id
            and nargs1, nargs2 = n1-gp1_a1, n2-gp1_a2 in
            equiv
              (Term.down_from nargs1 gp1_a1 a1)
              (Term.down_from nargs2 gp1_a2 a2)
              imp_id &&
            equiv
              (Term.all_quantified nargs1 [||] b1)
              (Term.all_quantified nargs2 [||] b2)
              imp_id
          in
          if n1 <= n2 then first_less n1 a1 b1 n2 a2 b2
          else first_less n2 a2 b2 n1 a1 b1
    | _, _ ->
        false
  in
  equiv t1 t2 (imp_id at)



let make (verbosity:int): t =
  {seq      = Ass_seq.empty ();
   depth    = 0;
   count0   = 0;
   names    = [||];
   nreq    = 0;
   maxreq  = 0;
   reqs    = [];
   prev    = None;
   c = Context.make verbosity;
   verbosity = verbosity}


let push0 (names: int array) (c:Context.t) (at:t): t =
  {at with
   seq = Ass_seq.clone at.seq;
   names = names;
   c        = c;
   depth    = 1 + at.depth;
   count0   = count at;
   nreq     = 0;
   maxreq   = count at;
   reqs     = [];
   prev     = Some at}



let push
    (entlst:entities list withinfo)
    (rt:return_type)
    (is_pred:bool)
    (is_func:bool)
    (rvar: bool)
    (at:t): t =
  let c = context at in
  assert (depth at = Context.depth c);
  let c = Context.push entlst rt is_pred is_func rvar c in
  let names = Context.local_argnames c in
  push0 names c at



let push_untyped (names:int array) (at:t): t =
  let c = context at in
  let c = Context.push_untyped names c in
  assert (names = Context.local_argnames c);
  push0 names c at



let pop (at:t): t =
  assert (is_local at);
  assert (depth at >= Context.depth (context at));
  previous at



let term (i:int) (at:t): term * int =
  (** The [i]th proved term with the number of variables of its environment.
   *)
  assert (i < count at);
  let desc = descriptor i at in
  desc.term, desc.nbenv0


let nbenv_term (i:int) (at:t): int =
  (** The number of variables of the environment of the  [i]th proved term.
   *)
  assert (i < count at);
  (descriptor i at).nbenv0



let local_term (i:int) (at:t): term =
  (** The [i]th proved term in the local environment.
   *)
  assert (i < count at);
  let desc = descriptor i at in
  let n_up = count_variables at - desc.nbenv0
  in
  Term.up n_up desc.term


let variant (i:int) (bcls:int) (cls:int) (at:t): term =
  let ft = feature_table at in
  let t,nbenv = term i at   in
  let t = Feature_table.variant_term t nbenv bcls cls ft in
  t



let discharged_assumptions (i:int) (at:t): int * int array * term =
  (* The [i]th term of the current environment with all quantified variables
     of the term and assumptions discharged. A potential quantifier in the
     term is moved up (prenex normal form) all assumptions.

     Note: If [i] is not in the current environment it cannot be quantified!
   *)
  let cnt0 = count_previous at
  and tgt  = local_term i at in
  let n,nms,tgt =
    try
      let n,nms,t = split_all_quantified tgt at in
      if i < cnt0 then
        printf "  i %d, cnt0 %d tgt %s\n" i cnt0 (string_of_term tgt at);
      assert (cnt0 <= i);
      n,nms,t
    with Not_found -> 0,[||],tgt
  in
  let imp_id = n + imp_id at in
  assert (at.nreq = List.length at.reqs);
  let res =
    List.fold_left
      (fun tgt k ->
        let t = local_term k at in
        let t = Term.up n t in
        Term.binary imp_id t tgt)
      tgt
      at.reqs in
  n,nms,res


let assumptions (at:t): term list =
  (* The assumptions of the current context *)
  List.fold_left
    (fun lst i ->
      (local_term i at)::lst)
    []
    at.reqs



let discharged_term (i:int) (at:t): term =
  (* The [i]th term of the current environment with all local variables and
     assumptions discharged.
   *)
  assert (is_local at);
  assert (not (has_result at));
  let n1,nms1,t = discharged_assumptions i at in
  let nargs = n1 + count_last_arguments at
  and nms   = prepend_names nms1 (names at) in
  all_quantified nargs nms t (previous at)



let is_axiom (i:int) (at:t): bool =
  assert (i < count at);
  let desc = descriptor i at in
  match desc.proof_term with
    Axiom _ -> true
  | _       -> false


let is_assumption (i:int) (at:t): bool =
  assert (i < count at);
  let desc = descriptor i at in
  match desc.proof_term with
    Assumption _ -> true
  | _            -> false


let proof_term (i:int) (at:t): proof_term =
  assert (i < count at);
  (descriptor i at).proof_term


let add_proved_0 (t:term) (pt:proof_term) (at:t): unit =
  (** Add the term [t] and its proof term [pt] to the table.
   *)
  let raw_add () =
    Ass_seq.push {nbenv0 = count_variables at;
                  term   = t;
                  proof_term = pt} at.seq
  in
  match pt with
    Assumption _ ->
      let idx = count at in
      raw_add ();
      at.reqs <- idx :: at.reqs;
      at.nreq <- at.nreq + 1;
      at.maxreq <- idx + 1
  | _ ->
      raw_add ()


exception Illegal_proof_term


let definition (idx:int) (nb:int) (at:t): int * int array * term =
  let c = context at in
  Context.definition idx nb c


let arity (idx:int) (nb:int) (at:t): int =
  Context.arity idx nb at.c


let split_equality (t:term) (nb:int) (at:t): int * term * term =
  let nargs, eq_id, left, right =
    Feature_table.split_equality t (nb + count_variables at) (feature_table at) in
  nargs,left,right



let specialized (i:int) (args:term array) (nb:int) (at:t): term =
  assert (i < count at);
  let nbenv = count_variables at in
  let t, nbenv_t = term i at in
  assert (nbenv_t <= nbenv);
  let nbenv_delta = nb + nbenv - nbenv_t in
  if Array.length args = 0 then
    Term.up nbenv_delta t
  else
    let nargs, _, t0 = Term.all_quantifier_split t in
    assert (nargs = Array.length args);
    Term.sub t0 args nbenv_delta


let beta_reduce (n:int) (t:term) (args:term array) (nb:int) (at:t): term =
  Context.beta_reduce n t args nb at.c


let apply_term (t:term) (args:term array) (nb:int) (at:t): term =
  Term.apply t args


let reconstruct_evaluation (e:Eval.t) (at:t): term * term =
  (* Return the unevaluated and the evaluated term *)
  let rec reconstruct e nb =
    let domain_id = nb + count_variables at + Feature_table.domain_index
    and reconstr_args args =
      let n = Array.length args in
      let args = Array.map (fun e -> reconstruct e nb) args in
      let argsa = Array.init n (fun i -> fst args.(i))
      and argsb = Array.init n (fun i -> snd args.(i)) in
      argsa, argsb
    in
    let ta,tb =
    match e with
      Eval.Term t -> t,t
    | Eval.Exp (idx,args,e) when idx = domain_id ->
        let doma, domb = reconstruct e nb in
        if doma <> domb then raise Illegal_proof_term;
        if Array.length args <> 1 then raise Illegal_proof_term;
        let argsa,argsb = reconstr_args args in
        assert (argsa = argsb); (* must be valid in case of domain_id *)
        begin match argsa.(0) with
          Lam(n,nms,pres,t0,pr) ->
            if pr then raise Illegal_proof_term;
            if Context.domain_of_lambda n nms pres nb (context at) <> doma then
              raise Illegal_proof_term
        | Variable idx2 when arity idx2 nb at > 0 ->
            if Context.domain_of_feature idx2 nb (context at) <> doma then
              raise Illegal_proof_term
        | _ -> ()
        end;
        VAppl(idx,argsa), doma
    | Eval.Exp (idx,args,e) ->
        let n,nms,t =
          try definition idx nb at
          with Not_found -> raise Illegal_proof_term
        in
        let argslen = Array.length args in
        let t =
          if n <> argslen then begin
            assert (argslen = 0);
            Context.make_lambda n nms [] t false nb (context at)
          end else t in
        let ta,tb = reconstruct e nb
        and argsa,argsb = reconstr_args args in
        let uneval =
          if argslen = 0 then Variable idx
          else VAppl(idx,argsa) in
        let exp =
          try apply_term t argsb nb at
          with Not_found ->
            raise Illegal_proof_term in
        if not (Term.equivalent exp ta) then begin
          printf "reconstruct exp   %s\n" (string_of_term_anon exp nb at);
          printf "            tb    %s\n" (string_of_term_anon tb nb at);
        end;
        if not (Term.equivalent exp ta) then raise Illegal_proof_term;
        uneval, tb
    | Eval.VApply (i,args) ->
        let argsa, argsb = reconstr_args args in
        VAppl (i,argsa), VAppl (i,argsb)
    | Eval.Apply (f,args,pr) ->
        let fa,fb = reconstruct f nb in
        let argsa, argsb = reconstr_args args in
        Application (fa,argsa,pr), Application (fb,argsb,pr)
    | Eval.Lam (n,nms,pres,e,pr) ->
        let ta,tb = reconstruct e (1 + nb) in
        Lam (n,nms,pres,ta,pr), Lam (n,nms,pres,tb,pr)
    | Eval.QExp (n,nms,e,is_all) ->
        let ta,tb = reconstruct e (nb+n) in
        QExp (n,nms,ta,is_all), QExp (n,nms,tb,is_all)
    | Eval.Beta e ->
        let ta,tb = reconstruct e nb in
        begin match tb with
          Application(Lam(n,nms,_,t0,_),args,_) ->
            let tb = beta_reduce n t0 args nb at in
            ta,tb
        | _ -> raise Illegal_proof_term end
    | Eval.Simpl (e,idx,args) ->
        let eq = specialized idx args nb at in
        let n,left,right = split_equality eq nb at in
        assert (n = 0);
        let ta,tb = reconstruct e nb in
        if tb <> left then begin
          printf "reconstruct ta    %s\n" (string_of_term_anon ta nb at);
          printf "            tb    %s\n" (string_of_term_anon tb nb at);
          printf "            left  %s\n" (string_of_term_anon left nb at);
          printf "            right %s\n" (string_of_term_anon right nb at);
          raise Illegal_proof_term
        end;
        ta,right
    | Eval.Flow (ctrl,args) ->
        let argsa, argsb = reconstr_args args in
        Flow (ctrl,argsa), Flow (ctrl,argsb)
    | Eval.If (cond,idx,args) ->
        assert (Array.length args = 3);
        let argsa, argsb = reconstr_args args in
        Flow (Ifexp,argsa), if cond then argsb.(1) else argsb.(2)
    | Eval.As (cond,args) ->
        assert (Array.length args = 2);
        let argsa, argsb = reconstr_args args in
        let res =
          let nvars = count_variables at in
          if cond then Variable (nvars + Feature_table.true_index)
          else Variable (nvars + Feature_table.false_index)
        in
        Flow (Asexp,argsa), res
    | Eval.Inspect (t,inspe,icase,nvars,rese) ->
        let inspa,inspb = reconstruct inspe nb
        and resa,resb   = reconstruct rese nb in
        begin match t with
          Flow(Inspect,args) ->
            let len = Array.length args in
            if len < 3 || len mod 2 <> 1 then raise Illegal_proof_term;
            let ncases = len / 2 in
            if icase < 0 || ncases <= icase then raise Illegal_proof_term;
            let n1,_,mtch = Term.pattern_split args.(2*icase+1)
            and n2,_,res  = Term.pattern_split args.(2*icase+2) in
            if n1 <> n2 then raise Illegal_proof_term;
            begin try
              let subarr = Term_algo.unify inspb n1 mtch in
              assert (Array.length subarr = n2);
                let res = Term.apply res subarr in
                if res <> resa then begin
                  printf "inspect result different\n";
                  printf "  res       %s\n" (string_of_term_anon res nb at);
                  printf "  resa      %s\n" (string_of_term_anon resa nb at);
                  raise Illegal_proof_term
                end;
                t, resb
            with Not_found ->
              printf "inspect no match\n";
              printf "  term      %s\n" (string_of_term_anon inspa nb at);
              printf "  eval      %s\n" (string_of_term_anon inspb nb at);
              printf "  case %d   %s\n"
                icase (string_of_term_anon mtch (n1+nb) at);
              raise Illegal_proof_term
            end
        | _ ->
            printf "no inspect expression %s\n" (string_of_term_anon t nb at);
            raise Illegal_proof_term
        end
    in
    let tb = Context.downgrade_term tb nb at.c in
    ta, tb
  in
  reconstruct e 0




let term_of_mp (a:int) (b:int) (at:t): term =
  assert (a < count at);
  assert (b < count at);
  let ta = local_term a at
  and tb = local_term b at
  in
  let b1,b2 =
    try Term.binary_split tb (imp_id at)
    with Not_found ->
      printf "tb is not an implication\n";
      printf "  ta %d:%s\n" a (string_of_term ta at);
      printf "  tb %d:%s\n" b (string_of_term tb at);
      raise Illegal_proof_term
  in
  let ok = equivalent ta b1 at in
  if not ok then begin
    printf "antecedent of tb does not conincide with ta (ok %b)\n" ok;
      printf "  ta %d:%s\n" a (string_of_term ta at);
      printf "  tb %d:%s\n" b (string_of_term tb at);
    raise Illegal_proof_term
  end;
  b2



let term_of_eval (i:int) (e:Eval.t) (at:t): term =
  let ta,tb = reconstruct_evaluation e at
  and t = local_term i at in
  let ok = (Term.equivalent t  ta) in
  if not ok then begin
    printf "evaluated terms do not coincide\n";
    printf "   term %3d  %s  %s\n" i (string_of_term t at)(Term.to_string t);
    printf "   eval      %s  %s\n" (string_of_term ta at) (Term.to_string ta);
    printf "   evaluated %s  %s\n" (string_of_term tb at) (Term.to_string tb);
    raise Illegal_proof_term
  end;
  tb


let term_of_eval_bwd (t:term) (e:Eval.t) (at:t): term =
  let ta,tb = reconstruct_evaluation e at in
  let ok = (t = ta) in
  if not ok then begin
    printf "evaluated terms (bwd) do not coincide\n";
    printf "   term      %s  %s\n" (string_of_term t at) (Term.to_string t);
    printf "   eval      %s  %s\n" (string_of_term ta at) (Term.to_string ta);
    printf "   evaluated %s\n" (string_of_term tb at);
    raise Illegal_proof_term
  end;
  implication tb ta at



let term_of_specialize (i:int) (args:term array) (at:t): term =
  assert (i < count at);
  let nargs = Array.length args
  and t = local_term i at
  in
  let n,nms,t0 =
    try Term.all_quantifier_split t
    with Not_found -> assert false
  in
  assert (nargs <= n);
  let tsub = Term.part_sub t0 n args 0
  in
  if nargs < n then
    let imp_id0 = (imp_id at)           in
    let imp_id1 = imp_id0 + (n-nargs)   in
    try
      let a,b = Term.binary_split tsub imp_id1 in
      Term.binary
        imp_id0
        (Term.down (n-nargs) a)
        (Term.all_quantified
           (n-nargs)
           (Array.sub nms nargs (n-nargs))
           b)
    with Term_capture ->
      printf "term capture\n";
      raise Illegal_proof_term
    | Not_found ->
        printf "not found\n";
        raise Illegal_proof_term
  else
    tsub




let term_of_witness (i:int) (nms:int array) (t:term) (args:term array) (at:t)
    : term =
  let nargs = Array.length args in
  Array.iter (fun t ->
    match t with Variable i when i = -1 ->
      raise Illegal_proof_term
    | _ -> ())
    args;
  let some_term = some_quantified nargs nms t at in
  let ti  = local_term i at in
  let wt  = Term.apply t args in
  if not (Term.equivalent ti wt) then begin
    printf "illegal witness ti  \"%s\"\n" (string_of_term ti at);
    printf "                wt  \"%s\"\n" (string_of_term wt at);
    printf "                for \"%s\"\n" (string_of_term some_term at);
    raise Illegal_proof_term
  end;
  implication ti some_term at


let someelim (i:int) (at:t): term =
  (** Transform the term [i] if it has the form [some(a,b,...) e1] into
      [all(e2) (all(a,b,...) e1 => e2) => e2]. Otherwise [raise Not_found]
   *)
  assert (i < count at);
  let t = local_term i at in
  let nargs,nms,tt = split_some_quantified t at in
  let tt = Term.upbound 1 nargs tt in
  let imp_id  = imp_id at
  in
  let imp_id1 = imp_id + (nargs+1)
  and imp_id2 = imp_id + 1
  and e_name = ST.symbol "$e"
  in
  let impl1   = Term.binary imp_id1 tt (Variable nargs) in
  let all1    = Term.all_quantified nargs nms impl1 in
  let impl2   = Term.binary imp_id2 all1 (Variable 0) in
  let all2    = Term.all_quantified 1 [|e_name|] impl2 in
  all2



let term_of_someelim (i:int) (at:t): term =
  try
    someelim i at
  with Not_found ->
    raise Illegal_proof_term


let is_inductive_set (i:int) (at:t): bool =
  Context.is_inductive_set i at.c


let inductive_set (t:term) (at:t): term =
  Context.inductive_set t at.c


let closure_rule (i:int) (t:term) (at:t): term =
  try
    let set = inductive_set t at in
    Term.closure_rule i set t
  with Not_found
  | Invalid_argument _ ->
    raise Illegal_proof_term


let function_property (idx:int) (i:int) (args:term array) (at:t): term =
  try
    Context.function_property idx i args at.c
  with Invalid_argument _ ->
    raise Illegal_proof_term


let set_induction_law (t:term) (at:t): term =
  let p =
    try
      Context.inductive_set t at.c
    with Not_found ->
      raise Illegal_proof_term in
  Term.induction_law (imp_id at) p t


let type_induction_law (cls:int) (at:t): term =
  Feature_table.induction_law cls (count_variables at) (feature_table at)


let count_assumptions (pt_arr:proof_term array): int =
  let p (pt:proof_term): bool =
    match pt with
      Assumption _ -> false | _ -> true
  in
  try
    Search.array_find_min p pt_arr
  with Not_found ->
    Array.length pt_arr




let arguments_string (at:t): string =
  let names = Array.to_list at.names in
  let str = String.concat "," (List.map ST.string names) in
  if str = "" then str
  else "(" ^ str ^ ")"



let reconstruct_term (pt:proof_term) (trace:bool) (at:t): term =
  let depth_0 = depth at
  in
  let rec reconstruct (pt:proof_term) (at:t): term =
    let prefix (d:int): string = String.make (4*(d+1-depth_0)) ' '
    in
    let print (t:term) (at:t) =
      printf "%s%3d %s"
        (prefix (depth at)) (count at) (string_of_term t at)
    and print_all (at:t) =
      let pre = prefix (depth at - 1) in
      printf "%s%3d all%s\n%s    require\n"
        pre (count at) (arguments_string at) pre
    and print_str (str:string) (at:t):unit =
      let pre = prefix (depth at - 1) in
      printf "%s    %s\n" pre str
    in
    let print0 (t:term) at = print t at; printf "\n"
    and print1 (t:term) (i:int) at = print t at; printf "\t{%d}\n" i
    and print2 (t:term) (i:int) (j:int) at = print t at; printf "\t{%d,%d}\n" i j
    in
    let cnt = count at in
    match pt with
      Axiom t | Assumption t ->
        if trace then print0 t at;
        t
    | Funprop (idx,i,args) ->
        let t = function_property idx i args at in
        if trace then print0 t at;
        t
    | Indset_rule (t,i) ->
        let t = closure_rule i t at in
        if trace then print0 t at;
        t
    | Indset_ind t ->
        let t = set_induction_law t at in
        if trace then print0 t at;
        t
    | Indtype cls ->
        let t = type_induction_law cls at in
        if trace then print0 t at;
        t
    | Detached (a,b) ->
        let t = term_of_mp a b at in
        if trace then print2 t a b at;
        t
    | Specialize (i,args) ->
        let t = term_of_specialize i args at in
        if trace then print1 t i at;
        t
    | Eval (i,e) ->
        let t = term_of_eval i e at in
        if trace then print1 t i at;
        t
    | Eval_bwd (t,e) ->
        let t = term_of_eval_bwd t e at in
        if trace then print0 t at;
        t
    | Witness (idx,nms,t,args) ->
        let t = term_of_witness idx nms t args at in
        if trace then print0 t at;
        t
    | Someelim idx ->
        let t = term_of_someelim idx at in
        if trace then print0 t at;
        t
    | Inherit (idx,bcls,cls) ->
        let t =  variant idx bcls cls at in
        if trace then print1 t idx at;
        t
    | Subproof (nargs,names,res_idx,pt_arr) ->
        let at = push_untyped names at in
        let pt_len = Array.length pt_arr in
        let pt_nass =
          if trace then count_assumptions pt_arr else 0
        in
        assert (res_idx < cnt + pt_len);
        if trace then print_all at;
        for i = 0 to pt_len - 1 do
          if trace && i = pt_nass then print_str "check" at;
          let t = reconstruct pt_arr.(i) at in
          add_proved_0 t pt_arr.(i) at
        done;
        if trace then begin
          print_str "ensure" at;
          print1 (local_term res_idx at) res_idx at;
          print_str "end" at;
        end;
        let term = discharged_term res_idx at in
        term
  in
  reconstruct pt at




let term_of_pt (pt:proof_term) (at:t): term =
  (** Construct a term from the proof term [pt].
   *)
  reconstruct_term pt false at


let print_pt (pt:proof_term) (at:t): unit =
  let _ = reconstruct_term pt true at in ()



let is_proof_pair (t:term) (pt:proof_term) (at:t): bool =
  try
    (*let t_pt = reconstruct_term pt true at in*)
    let t_pt = term_of_pt pt at in
    let res = (t = t_pt) (*Term.equal_wo_names t t_pt*) in
    if not res then begin
      printf "unequal t    %s\n" (string_of_term t at);
      printf "        t_pt %s\n" (string_of_term t_pt at)
    end;
    res
  with Illegal_proof_term ->
    printf "Illegal proof term\n";
    print_pt pt at;
    false


let add_proved (t:term) (pt:proof_term) (delta:int) (at:t): unit =
  (** Add the term [t] and its proof term [pt] to the table.
   *)
  assert (delta <= count at);
  let start = count at - delta in
  let pt = Proof_term.adapt start delta pt in
  assert (not (is_global at) || is_proof_pair t pt at);
  add_proved_0 t pt at


let add_axiom (t:term) (at:t): unit =
  assert (is_toplevel at);
  let pt = Axiom t in
  add_proved_0 t pt at


let add_assumption (t:term) (at:t): unit =
  let pt = Assumption t in
  add_proved_0 t pt at


let add_inherited (t:term) (idx:int) (bcls:int) (cls:int) (at:t): unit =
  assert (is_global at);
  let pt = Inherit (idx,bcls,cls) in
  add_proved_0 t pt at


let add_mp (t:term) (i:int) (j:int) (at:t): unit =
  let pt = Detached (i,j) in
  add_proved_0 t pt  at


let add_specialize (t:term) (i:int) (args:term array) (at:t): unit =
  let pt = Specialize (i,args) in
  add_proved_0 t pt  at


let add_eval (t:term) (i:int) (e:Eval.t) (at:t): unit =
  add_proved_0 t (Eval (i,e)) at


let add_eval_backward (t:term) (impl:term) (e:Eval.t) (at:t): unit =
  (* [impl = (teval => t)] *)
  add_proved_0 impl (Eval_bwd (t,e)) at



let add_witness
    (impl:term) (i:int)
    (nms:int array) (t:term)
    (args:term array) (at:t): unit =
  add_proved_0 impl (Witness (i,nms,t,args)) at


let add_someelim (i:int) (t:term) (at:t): unit =
  add_proved_0 t (Someelim i) at



let discharged_proof_term (i:int) (at:t): int * int array * proof_term array =
  (* The [i]th term of the current environment with all quantified variables and
     assumptions discharged.

     Note: If [i] is not in the current environment it cannot be quantified!
   *)
  let cnt0 = count_previous at
  and pt   = proof_term i at in
  let n,nms,pt =
    match pt with
      Axiom t -> begin
        try
          let n,nms,t = split_all_quantified t at in
          n, nms, Axiom t
        with Not_found ->
          0,[||],pt
      end
    | _ -> begin
        try
          let n,nms,idx,pt_arr = Proof_term.split_subproof pt in
          assert (n=0 || cnt0 <= i);
          n,nms, Subproof (0,[||],idx,pt_arr)
        with Not_found ->
          0, [||], pt
    end
  in
  let narr = if at.maxreq<=i  then i+1-cnt0 else at.maxreq - cnt0 in
  let pterm j =
    let pt = proof_term (cnt0+j) at in Proof_term.term_up n pt
  in
  let pt_arr = Array.init narr (fun j -> if cnt0+j=i then pt else pterm j)
  in
  n, nms, pt_arr






let discharged (i:int) (at:t): term * proof_term =
  assert (not (has_result at));
  let n1,nms1,t = discharged_assumptions i at
  in
  let nargs = n1 + count_last_arguments at
  and nms   = prepend_names nms1 (names at)
  and nreq  = at.nreq
  and cnt0  = count_previous at
  and axiom = is_axiom i at
  in
  let len, pt_arr =
    let n2,nms2,pt_arr = discharged_proof_term i at in
    assert (n1 = n2);
    assert (nms1 = nms2);
    Array.length pt_arr, pt_arr
  in
  if nargs = 0 && nreq = 0 && len = 1 then
    t, pt_arr.(0)
  else
    let i,pt_arr =
      if len=0 then i,pt_arr else Proof_term.remove_unused i cnt0 pt_arr
    in
    let nargs,nms,t,pt_arr = Proof_term.normalize_pair nargs nms cnt0 t pt_arr
    in
    let t  = Term.all_quantified nargs nms t
    in
    let pt = if axiom then Axiom t else Subproof (nargs,nms,i,pt_arr)
    in
    t, pt
