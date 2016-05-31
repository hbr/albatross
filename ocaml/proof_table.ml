(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Term
open Signature
open Proof
open Container
open Support
open Printf

module ASeq = Ass_seq

type desc = {nbenv0:     int;
             c:          Context.t;
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

let count_last_type_variables (at:t): int = Context.count_last_type_variables at.c

let count_last_arguments (at:t): int =
  Context.count_last_arguments at.c

let local_argnames (at:t): int array =
  Context.local_argnames at.c

let local_formals (at:t): formals =
  Context.local_formals at.c

let local_fgs (at:t): formals =
  Context.local_fgs at.c

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


let tvars (at:t): Tvars.t = Context.tvars at.c

let imp_id (at:t): int =
  Context.implication_index at.c

let split_implication (t:term) (at:t): term * term =
  Term.binary_split t (imp_id at)

let split_all_quantified (t:term) (at:t): int * formals * formals * term =
  Term.all_quantifier_split t

let split_some_quantified (t:term) (at:t): int * formals * term =
  Term.some_quantifier_split t

let implication (a:term) (b:term) (at:t): term =
  Term.binary (imp_id at) a b

let implication_chain (ps: term list) (tgt:term) (at:t): term =
  Term.make_implication_chain ps tgt (imp_id at)

let split_implication_chain (t:term) (at:t): term list * term =
  Term.split_implication_chain t (imp_id at)

let quantified
    (is_all:bool) (nargs:int) (tps:formals) (fgs:formals) (t:term) (at:t)
    : term =
  Context.quantified is_all nargs tps fgs t at.c

let all_quantified (nargs:int)  (tps:formals) (fgs:formals)(t:term) (at:t): term =
  Context.all_quantified nargs tps fgs t at.c

let some_quantified (nargs:int)  (tps:formals) (fgs:formals) (t:term) (at:t): term =
  Context.some_quantified nargs tps fgs t at.c


let string_of_term (t:term) (at:t): string =
  Context.string_of_term t at.c

let string_long_of_term (t:term) (at:t): string =
  Context.string_long_of_term t at.c

let string_of_term_anon (t:term) (nb:int) (at:t): string =
  Context.string_of_term0 t true false nb at.c



let prepend_names (nms:int array) (names:int array): int array =
  let nms = Feature_table.adapt_names nms names in
  Array.append nms names


let prenex_term (t:term) (at:t): term =
  (* The term [t] in prenex normal form with respect to universal quantifiers *)
  Context.prenex_term t at.c



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



let push_typed (tps:formals) (fgs:formals) (at:t): t =
  let c = Context.push_typed tps fgs at.c in
  let nms = fst tps in
  push0 nms c at


let pop (at:t): t =
  assert (is_local at);
  assert (depth at >= Context.depth (context at));
  previous at



let term (i:int) (at:t): term * Context.t =
  (** The [i]th proved term and its context.
   *)
  assert (i < count at);
  let desc = descriptor i at in
  desc.term, desc.c


let transformed_to_current (t:term) (idx:int) (at:t): term =
  (* The term [t] transformed form the environment of the term at [idx] into the
     current environment.
   *)
  Context.transformed_term t (descriptor idx at).c (context at)


let string_of_term_i (i:int) (at:t): string =
  let desc = descriptor i at in
  Context.string_of_term desc.term desc.c


let string_long_of_term_i (i:int) (at:t): string =
  let desc = descriptor i at in
  Context.string_long_of_term desc.term desc.c


let nbenv_term (i:int) (at:t): int =
  (** The number of variables of the environment of the  [i]th proved term.
   *)
  assert (i < count at);
  (descriptor i at).nbenv0


let ntvs_term (i:int) (at:t): int =
  (* The complete number of type variables of the environment of the [i]th
     proved term.  *)
  TVars_sub.count_all (Context.tvars_sub (descriptor i at).c)


let local_term (i:int) (at:t): term =
  (** The [i]th proved term in the local environment.
   *)
  assert (i < count at);
  let desc = descriptor i at in
  if desc.c == at.c then
    desc.term
  else
    Context.transformed_term desc.term desc.c at.c


let variant (i:int) (bcls:int) (cls:int) (at:t): term =
  assert (is_global at);
  let t,c = term i at in
  assert (c == at.c);
  let n,(nms,tps),(fgnms,fgcon),t0 =
    try Term.all_quantifier_split t
    with Not_found -> assert false in
  assert (Array.length fgcon = 1); (* Only one formal generic *)
  let bcls0,_ = Class_table.split_type_term fgcon.(0) in
  assert (bcls0 = bcls + 1);
  let ft = feature_table at
  and ct = class_table at in
  let ctp,tvs = Class_table.class_type cls ct in
  let ags = [|ctp|] in
  let nall = Tvars.count_all tvs in
  let tps  = Array.map
      (fun tp -> Term.subst tp nall ags)
      tps
  and fgnms, fgcon = Tvars.fgnames tvs, Tvars.fgconcepts tvs in
  let t0 = Feature_table.substituted t0 n 0 0 [||] 0 ags tvs ft in
  Term.all_quantified n (nms,tps) (fgnms,fgcon) t0



let count_local_assumptions (at:t): int =
  at.nreq

let assumptions (at:t): term list =
  (* The assumptions of the current context *)
  List.fold_left
    (fun lst i ->
      (local_term i at)::lst)
    []
    at.reqs


let discharged_assumptions (i:int) (at:t): term =
  assert (is_local at);
  assert (not (has_result at));
  let tgt = local_term i at in
  assert (count_last_arguments at = 0 || not (Term.is_all_quantified tgt));
  List.fold_left
    (fun tgt i -> implication (local_term i at) tgt at)
    tgt
    at.reqs


let discharged_term (i:int) (at:t): term =
  (* The [i]th term of the current environment with all local variables and
     assumptions discharged.
   *)
  let t0 = discharged_assumptions i at in
  let n, tps, fgs = count_last_arguments at, local_formals at, local_fgs at in
  Term.all_quantified n tps fgs t0



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
  (*assert (Context.is_well_typed t at.c);*)
  let raw_add () =
    Ass_seq.push {nbenv0 = count_variables at;
                  c      = at.c;
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


let definition (idx:int) (nb:int) (ags:agens) (at:t): int * int array * term =
  let c = context at in
  Context.definition idx nb ags c


let arity (idx:int) (nb:int) (at:t): int =
  Context.arity idx nb at.c


let split_equality (t:term) (nb:int) (at:t): int * term * term =
  let nargs, eq_id, left, right =
    Feature_table.split_equality t (nb + count_variables at) (feature_table at) in
  nargs,left,right



let specialized (i:int) (args:term array) (nb:int) (at:t): term =
  assert (i < count at);
  assert false
  (*let nbenv = count_variables at in
  let t, nbenv_t = term i at in
  assert (nbenv_t <= nbenv);
  let nbenv_delta = nb + nbenv - nbenv_t in
  if Array.length args = 0 then
    Term.up nbenv_delta t
  else
    let nargs, _, t0 = Term.all_quantifier_split t in
    assert (nargs = Array.length args);
    Term.sub t0 args nbenv_delta*)


let beta_reduce
    (n:int) (t:term) (tp:type_term) (args:term array) (nb:int) (at:t)
    : term =
  Context.beta_reduce n t tp args nb at.c


let apply_term (t:term) (args:term array) (nb:int) (at:t): term =
  Term.apply t args


let term_of_specialize (i:int) (args:term array) (ags:agens) (at:t): term =
  (* Specialize the assertion [i] with the actual arguments [args] and the
     actual generics [ags] coming from the current context.
   *)
  assert (i < count at);
  let tvs   = tvars at in
  let nargs = Array.length args
  and desc  = descriptor i at
  and nall  = Tvars.count_all tvs
  in
  let nvars_i = Context.count_variables desc.c
  and ntvs_i  = ntvs_term i at
  in
  let d1 = count_variables at - nvars_i in
  let n,(nms,tps),(fgnms,fgcon),t0 =
    try Term.all_quantifier_split desc.term
    with Not_found -> 0, empty_formals, empty_formals, desc.term
  in
  assert (nargs <= n);
  let tsub =
    Feature_table.substituted
      t0 n nvars_i ntvs_i
      args d1
      ags tvs (feature_table at)
  and nms = Array.sub nms nargs (n-nargs)
  and tps = Array.sub tps nargs (n-nargs)
  in
  let tps = Term.subst_array tps (nall-ntvs_i) ags in
  if nargs < n then
    let imp_id0 = (imp_id at)           in
    let imp_id1 = imp_id0 + (n-nargs)   in
    try
      let a,b = Term.binary_split tsub imp_id1 in
      Term.binary
        imp_id0
        (Term.down (n-nargs) a)
        (Term.all_quantified (n-nargs) (nms,tps) empty_formals b)
    with Term_capture ->
      printf "term capture\n";
      raise Illegal_proof_term
    | Not_found ->
        printf "not found\n";
        raise Illegal_proof_term
  else
    tsub




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
    | Eval.Exp (idx,ags,args,e) when idx = domain_id ->
        let doma, domb = reconstruct e nb in
        if doma <> domb then raise Illegal_proof_term;
        if Array.length args <> 1 then raise Illegal_proof_term;
        let argsa,argsb = reconstr_args args in
        assert (argsa = argsb); (* must be valid in case of domain_id *)
        begin match argsa.(0) with
          Lam(n,nms,pres,t0,pr,tp0) ->
            if pr then raise Illegal_proof_term;
            if Context.domain_of_lambda n nms pres tp0 nb (context at) <> doma then
              raise Illegal_proof_term
        | VAppl(idx2,args,ags) when arity idx2 nb at > 0 ->
            if Context.domain_of_feature idx2 nb ags (context at) <> doma then
              raise Illegal_proof_term
        | _ -> ()
        end;
        VAppl(idx,argsa,ags), doma
    | Eval.Exp (idx,ags,args,e) ->
        let n,nms,t =
          try definition idx nb ags at
          with Not_found -> raise Illegal_proof_term
        in
        let argslen = Array.length args in
        let t =
          if n <> argslen then begin
            assert (argslen = 0);
            let tp = assert false in
            Context.make_lambda n nms [] t false nb tp (context at)
          end else t in
        let ta,tb = reconstruct e nb
        and argsa,argsb = reconstr_args args in
        let uneval = VAppl(idx,argsa,ags) in
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
    | Eval.VApply (i,args,ags) ->
        let argsa, argsb = reconstr_args args in
        VAppl (i,argsa,ags), VAppl (i,argsb,ags)
    | Eval.Apply (f,args,pr) ->
        let fa,fb = reconstruct f nb in
        let argsa, argsb = reconstr_args args in
        Application (fa,argsa,pr), Application (fb,argsb,pr)
    | Eval.Lam (n,nms,pres,e,pr,tp) ->
        let ta,tb = reconstruct e (1 + nb) in
        Lam (n,nms,pres,ta,pr,tp), Lam (n,nms,pres,tb,pr,tp)
    | Eval.QExp (n,tps,fgs,e,is_all) ->
        let ta,tb = reconstruct e (nb+n) in
        QExp (n,tps,fgs,ta,is_all), QExp (n,tps,fgs,tb,is_all)
    | Eval.Beta e ->
        let ta,tb = reconstruct e nb in
        begin match tb with
          Application(Lam(n,nms,_,t0,_,tp),args,_) ->
            let tb = beta_reduce n t0 tp args nb at in
            ta,tb
        | _ -> raise Illegal_proof_term end
    | Eval.Simpl (e,idx,args,ags) ->
        let eq = term_of_specialize idx args ags at in
        let eq = Term.up nb eq in
        (*let eq = specialized idx args nb at in*)
        let n,left,right = split_equality eq nb at in
        assert (n = 0);
        assert (Array.length args = 0);
        assert (Array.length ags  = 0);
        let ta,tb = reconstruct e nb in
        if tb <> left then begin
          printf "reconstruct ta    %s\n" (string_of_term_anon ta nb at);
          printf "            tb    %s %s\n"
            (string_of_term_anon tb nb at) (Term.to_string tb);
          printf "            left  %s %s\n"
            (string_of_term_anon left nb at) (Term.to_string left);
          printf "            right %s\n" (string_of_term_anon right nb at);
          if nb = 0 then begin
            let c = context at in
            assert (Context.is_well_typed left c);
            assert (Context.is_well_typed tb c);
          end;
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
          if cond then Feature_table.true_constant nvars
          else Feature_table.false_constant nvars
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
  let ok = Term.equivalent ta b1 in
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
    printf "   term %3d  %s  %s\n" i (string_long_of_term t at)(Term.to_string t);
    printf "   eval      %s  %s\n" (string_long_of_term ta at) (Term.to_string ta);
    printf "   evaluated %s  %s\n" (string_long_of_term tb at) (Term.to_string tb);
    raise Illegal_proof_term
  end;
  tb


let term_of_eval_bwd (t:term) (e:Eval.t) (at:t): term =
  let ta,tb = reconstruct_evaluation e at in
  let ok = (Term.equivalent t ta) in
  if not ok then begin
    printf "evaluated terms (bwd) do not coincide\n";
    printf "   term      %s  %s\n" (string_long_of_term t at) (Term.to_string t);
    printf "   eval      %s  %s\n" (string_long_of_term ta at) (Term.to_string ta);
    printf "   evaluated %s\n" (string_long_of_term tb at);
    raise Illegal_proof_term
  end;
  implication tb ta at



let term_of_witness
    (i:int) (nms:names) (tps:types) (t:term) (args:term array) (at:t)
    : term =
  let nargs = Array.length args in
  Array.iter
    (fun t ->
      match t with Variable i when i = -1 ->
        raise Illegal_proof_term
      | _ -> ()
    )
    args;
  let some_term = Term.some_quantified nargs (nms,tps) t in
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
  (* If the term [i] has not the form [some(a:A,b:B,...) t] then raise
     Not_found.

     If the term is an existentially quantified assertions then transform it
     into

         all(u:BOOLEAN) (all(a:A,b:B,...) t ==> u) ==> u

   *)

  assert (i < count at);
  let t_i = local_term i at in
  let nargs,(nms,tps),t0 = split_some_quantified t_i at in
  let imp_id  = imp_id at
  in
  let imp_id_inner = imp_id + (nargs+1)
  and imp_id_outer = imp_id + 1
  and e_name = ST.symbol "$e"
  and e_tp   = Context.boolean at.c
  in
  let t1 = Term.up_from 1 nargs t0
  in
  let t_impl_u   = Term.binary imp_id_inner t1 (Variable nargs) in
  let all_inner  = Term.all_quantified nargs (nms,tps) empty_formals t_impl_u in
  let impl_outer = Term.binary imp_id_outer all_inner (Variable 0) in
  Term.all_quantified 1 ([|e_name|],[|e_tp|]) empty_formals impl_outer



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
  let set_tp = Context.type_of_term p at.c in
  let elem_tp = Class_table.domain_type set_tp in
  Term.induction_law (imp_id at) p t elem_tp set_tp


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
        (prefix (depth at)) (count at) (string_long_of_term t at)
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
    and printstr (t:term) (str:string) at =
      print t at; printf "\t{%s}\n" str
    in
    let cnt = count at in
    match pt with
      Axiom t | Assumption t ->
        if trace then print0 t at;
        t
    | Funprop (idx,i,args) ->
        let t = function_property idx i args at in
        if trace then printstr t "funprop" at;
        t
    | Indset_rule (t,i) ->
        let t = closure_rule i t at in
        if trace then printstr t "rule" at;
        t
    | Indset_ind t ->
        let t = set_induction_law t at in
        if trace then printstr t "indset" at;
        t
    | Indtype cls ->
        let t = type_induction_law cls at in
        if trace then printstr t "indlaw" at;
        t
    | Detached (a,b) ->
        let t = term_of_mp a b at in
        if trace then print2 t a b at;
        t
    | Specialize (i,args,ags) ->
        let t = term_of_specialize i args ags at in
        if trace then print1 t i at;
        t
    | Eval (i,e) ->
        let t = term_of_eval i e at in
        if trace then print1 t i at;
        t
    | Eval_bwd (t,e) ->
        let t = term_of_eval_bwd t e at in
        if trace then printstr t "evalbwd" at;
        t
    | Witness (idx,(nms,tps),t,args) ->
        let t = term_of_witness idx nms tps t args at in
        if trace then print1 t idx at;
        t
    | Someelim idx ->
        let t = term_of_someelim idx at in
        if trace then print1 t idx at;
        t
    | Inherit (idx,bcls,cls) ->
        let t =  variant idx bcls cls at in
        if trace then print1 t idx at;
        t
    | Subproof (tps,fgs,res_idx,pt_arr) ->
        let at = push_typed tps fgs at in
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
    let res = Term.equivalent t t_pt in
    if not res then begin
      printf "unequal t    %s\n" (string_of_term t at);
      printf "        t_pt %s\n" (string_of_term t_pt at)
    end;
    res
  with Illegal_proof_term ->
    printf "Illegal proof term\n";
    printf "   term \"%s\"\n" (string_long_of_term t at);
    print_pt pt at;
    false


let is_well_typed (t:term) (at:t): bool =
  Context.is_well_typed t at.c


let add_proved (t:term) (pt:proof_term) (delta:int) (at:t): unit =
  (** Add the term [t] and its proof term [pt] to the table.
   *)
  assert (delta <= count at);
  let start = count at - delta in
  let pt = Proof_term.adapt start delta pt in
  assert (not (is_global at) || is_well_typed t at);
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


let add_specialize (t:term) (i:int) (args:term array) (ags:agens) (at:t): unit =
  let pt = Specialize (i,args,ags) in
  add_proved_0 t pt  at


let add_eval (t:term) (i:int) (e:Eval.t) (at:t): unit =
  add_proved_0 t (Eval (i,e)) at


let add_eval_backward (t:term) (impl:term) (e:Eval.t) (at:t): unit =
  (* [impl = (teval => t)] *)
  add_proved_0 impl (Eval_bwd (t,e)) at



let add_witness
    (impl:term)
    (i:int)
    (nms:names)
    (tps:types)
    (t:term)
    (args:arguments) (at:t): unit =
  add_proved_0 impl (Witness (i,(nms,tps),t,args)) at


let add_someelim (i:int) (t:term) (at:t): unit =
  add_proved_0 t (Someelim i) at


(*  Discharging
    ===========

    Suppose the prover has accepted the assertion:

        all[G:CG,H:CH,...](a:A,b:B,...)
            require
                r0;r1;...
            ensure
                e
            end

    I.e. at the end we get a proof term for 'e' valid in the context.

    Discharged premises:  'r0 ==> r1 ==> ... ==> e'

    In the implication chain not all variables 'a,b,...' might be
    used. I.e. we can calculate a map 'f:int->int' which maps old variables to
    new variables and a set of used variables 'usd'. The map is undefined for
    old variables which are unused.

    Having this we get a type sequence 'UT1,UT2,...' of the used types which
    is 'A,B,...' with all types corresponding to unused variables removed.

    Formal generics not occurring in 'UT1,UT2,...' are unused as well. This
    gives rise to a map 'ffg:int->int' which maps old formal generics to new
    formal generics and a set of used formal generics 'usdfg'. The map is
    undefined for unused formal generics.

    With this we get a formal generics sequence 'UG1:CUG1,UG2,CUG2,..'.

    We have to map all terms with 'f' and all types with 'ffg' in the term and
    the proof term. In case that in the proof term some a function is applied
    to an undefined argument, then the proof term uses more variables than the
    final term. This has to be considered as an error.

 *)


(* Special cases for discharging:

   1. The target is an axiom: Just discharge the term (with bubbling up and
      removing of unneeded variables)  and use an axiom as a proof term.

   2. Only one proof term in the subproof, no assumptions and no variables:

      The only possibility to create such a situation is with `ensure ass end`
      which should be syntactically forbidden or reduced to the equivalent form
      `ass`.

   3. The target is a universally quantified assertion: Maybe it is best to
      forbid universally quantified assertions in ensure clauses and require the
      user to bubble them up. This removes a lot of complexity.

      Exception: The current environment has neither variables nor assumptions.
                 Then the universally quantified assertion and its proof term
                 do not need any modification.

   4. The target is from an outer context: In that case the target does not contain
      any of the variables of the inner context and does not need the assumptions
      of the inner context to be proved.


   The only remaining action for discharging: Remove unneeded variables.

 *)
let discharged (i:int) (at:t): term * proof_term =
  let tgt = local_term i at
  and pt  = proof_term i at in
  if count_last_arguments at = 0 &&
    count_local_assumptions at = 0 &&
    count_last_local at = 1 &&
    i = count_previous at
  then begin
    assert (i = count_previous at);
    tgt,pt
  end else begin
    if count_last_arguments at <> 0 && Term.is_all_quantified tgt then
      printf "discharged %d %s\n" i (string_long_of_term_i i at);
    assert (count_last_arguments at = 0 || not (Term.is_all_quantified tgt));
    let t0 = discharged_assumptions i at in
    let tps, args, fgs, ags =
      let tps  = local_formals at
      and ntvs = count_last_type_variables at
      and fgs  = local_fgs at in
      Term.unused_transform tps ntvs fgs t0
    in
    let n1new, n2new = count_formals tps, count_formals fgs in
    let t0 = Term.subst0 t0 n1new args n2new ags in
    let t  = Term.all_quantified n1new tps fgs t0
    in
    match pt with
      Axiom _ ->
        let pt = Axiom t in
        t, pt
    | _ ->
        let cnt0  = count_previous at in
        let narr = if at.maxreq <= i then i+1-cnt0 else at.maxreq-cnt0 in
        if narr = 0 then begin
          assert (i < cnt0);
          t, Subproof (empty_formals,empty_formals,i,[||])
        end else begin
          let nargs = Array.length args in
          let ptarr = Array.init narr (fun j -> proof_term (cnt0+j) at) in
          let i,ptarr  = Proof_term.remove_unused_proof_terms i cnt0 ptarr in
          let uvars_pt = Proof_term.used_variables nargs ptarr in
          if not (n1new = IntSet.cardinal uvars_pt &&
                  IntSet.for_all
                    (fun i ->
                      assert (i < nargs);
                      args.(i) <> Variable (-1))
                    uvars_pt)
          then begin
            printf "n1new %d, IntSet.cardinal uvars_pt %d\n"
              n1new (IntSet.cardinal uvars_pt);
            printf "uvars_pt %s\n" (intset_to_string uvars_pt);
            printf "#ptarr %d\n" (Array.length ptarr);
            Proof_term.print_pt_arr "    " cnt0 ptarr;
            raise Not_found
          end;
          let ptarr =
            Proof_term.remove_unused_variables args n1new ags n2new ptarr in
          let pt = Subproof (tps,fgs,i,ptarr) in
          t,pt
        end
  end
