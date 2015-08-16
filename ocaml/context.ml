(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Container
open Signature
open Term
open Support
open Printf

type formal = Class_table.formal

type entry = {
    tvs_sub:      TVars_sub.t;        (* cumulated *)
    fargs:        formal array;       (* cumulated *)
    ntvs_delta:   int;
    nfgs_delta:   int;
    nargs_delta:  int;
    rvar:         bool;
    result:       Result_type.t;
    info:         info;
  }


type t = {
    entry: entry;
    prev:  t option;
    depth: int;
    ft:            Feature_table.t;
    verbosity:     int
  }


let empty_entry: entry =
  {tvs_sub      = TVars_sub.empty;
   fargs        = [||];
   ntvs_delta   = 0;
   nfgs_delta   = 0;
   nargs_delta  = 0;
   rvar         = false;
   result   = Result_type.empty;
   info      = UNKNOWN}



let class_table(c:t): Class_table.t     = Feature_table.class_table c.ft
let feature_table(c:t): Feature_table.t = c.ft
let module_table(c:t): Module_table.t   = Class_table.module_table (class_table c)


let current_module (c:t): int =
  Feature_table.current_module c.ft

let find_module (name:int*int list) (c:t): int =
  Feature_table.find_module name c.ft


let add_used_module (name:int*int list) (used:IntSet.t) (c:t): unit =
  Feature_table.add_used_module name used c.ft

let add_current_module (name:int) (used:IntSet.t) (c:t): unit =
  Feature_table.add_current_module name used c.ft

let set_interface_check (pub_used:IntSet.t) (c:t): unit =
  Feature_table.set_interface_check pub_used c.ft


let used_modules (mdl:int) (c:t): IntSet.t =
  Feature_table.used_modules mdl c.ft


let is_private (c:t): bool = Feature_table.is_private c.ft
let is_public  (c:t): bool = Feature_table.is_public  c.ft
let is_interface_check (c:t): bool = Feature_table.is_interface_check  c.ft

let is_interface_use (c:t): bool = Feature_table.is_interface_use c.ft


let is_global (c:t): bool =
  c.prev = None


let is_toplevel (c:t): bool =
  match c.prev with
    Some prev -> is_global prev
  | _   -> false


let previous (c:t): t =
  assert (not (is_global c));
  Option.value c.prev

let entry_arity (e:entry): int = e.nargs_delta

let arity     (c:t): int = entry_arity c.entry

let verbosity (c:t): int = c.verbosity

let has_result_variable (c:t): bool = c.entry.rvar

let has_result (c:t): bool = Result_type.has_result c.entry.result

let result_type (c:t): type_term =
  (* The result type of the context *)
  assert (has_result c);
  Result_type.result c.entry.result


let count_type_variables (c:t): int =
  (** The number of cumulated type variables in this context and all
      preceeding contexts
   *)
  TVars_sub.count c.entry.tvs_sub

let count_local_type_variables (c:t): int =
  c.entry.ntvs_delta


let entry_nfgs (e:entry): int = TVars_sub.count_fgs e.tvs_sub

let count_formal_generics (c:t): int =
  (** The cumulated number of formal generics in this context and all
      previous contexts
   *)
  entry_nfgs c.entry


let count_last_formal_generics (c:t): int =
  (* The number of  formal generics introduced in this context.
   *)
  c.entry.nfgs_delta


let count_last_arguments (c:t): int = c.entry.nargs_delta

let count_last_variables (c:t): int =
  c.entry.nargs_delta +
  if has_result c then 1 else 0

let count_variables (c:t): int = Array.length c.entry.fargs


let implication_index (c:t): int =
  count_variables c + Feature_table.implication_index

let and_index (c:t): int =
  count_variables c + Feature_table.and_index

let or_index (c:t): int =
  count_variables c + Feature_table.or_index

let not_index (c:t): int =
  count_variables c + Feature_table.not_index

let domain_index (c:t): int =
  count_variables c + Feature_table.domain_index


let variable_name (i:int) (c:t): int =
  assert (i < count_variables c);
  fst c.entry.fargs.(i)


let variable_type (i:int) (c:t): type_term =
  assert (i < count_variables c);
  snd c.entry.fargs.(i)

let ntvs (c:t): int =
  (** The cumulated number of formal generics and type variables in
      this context and all previous contexts
   *)
  (count_formal_generics c) + (count_type_variables c)



let entry_local_argnames (e:entry): int array =
  Array.init e.nargs_delta (fun i -> fst e.fargs.(i))


let local_argnames (c:t): int array = entry_local_argnames c.entry


let entry_varnames (e:entry): int array =
  Array.map (fun (n,_) -> n) e.fargs


let varnames (c:t): int array = entry_varnames c.entry



let entry_fgnames (e:entry): int array = TVars_sub.fgnames e.tvs_sub

let fgnames (c:t): int array = entry_fgnames c.entry

let tvars (c:t): Tvars.t = TVars_sub.tvars c.entry.tvs_sub

let sign2string (s:Sign.t) (c:t): string =
  Class_table.string_of_signature
    s
    (tvars c)
    (class_table c)


let string_of_term (t:term) (norm:bool) (nanon:int) (c:t): string =
  Feature_table.term_to_string t norm nanon (varnames c) c.ft


let make_lambda
    (n:int) (nms:int array) (ps:term list) (t:term) (pred:bool) (nb:int) (c:t)
    : term =
  let nbenv = count_variables c in
  Feature_table.make_lambda n nms ps t pred (nb+nbenv) c.ft


let make_application
    (f:term) (args:term array) (nb:int) (pred:bool) (c:t): term =
  let nbenv = count_variables c in
  let res = Feature_table.make_application f args pred (nb+nbenv) c.ft in
  res


let beta_reduce (n:int) (tlam:term) (args:term array) (nb:int )(c:t): term =
  Feature_table.beta_reduce n tlam args (nb+count_variables c) c.ft


let quantified (is_all:bool) (nargs:int) (nms:int array) (t:term) (c:t): term =
  Term.quantified is_all nargs nms t

let all_quantified (nargs:int) (names:int array) (t:term) (c:t): term =
  quantified true nargs names t c

let some_quantified (nargs:int) (names:int array) (t:term) (c:t): term =
  quantified false nargs names t c





let entry_signature (e:entry) (c:t): Sign.t =
  (** The signature of the entry [e] in the context [c].  *)
  let argtypes = Array.init (entry_arity e) (fun i -> snd e.fargs.(i)) in
  Sign.make argtypes e.result




let signature (c:t): Sign.t =
  (** The signature of the context [c].  *)
  entry_signature c.entry c


let signature_string (c:t): string =
  (** Print the signature of the context [c].  *)
  sign2string (signature c) c


let variable_index (nme:int) (c:t): int =
  Search.array_find_min (fun (n,_) -> n = nme) c.entry.fargs


let owner (c:t): int =
  if is_toplevel c then
    let ct  = class_table c
    and tvs = TVars_sub.tvars c.entry.tvs_sub
    and s   = signature c
    in
    Class_table.owner tvs s ct
  else
    -1



let anchor_class (c:t): int =
  if is_toplevel c then
    let ct  = class_table c
    and tvs = TVars_sub.tvars c.entry.tvs_sub
    and s   = signature c
    in
    Class_table.anchor_class tvs s ct
  else
    -1



let split_equality (t:term) (nb:int) (c:t): int * int * term * term =
  Feature_table.split_equality t (nb + count_variables c) c.ft

let check_deferred (c:t): unit =
  assert (is_toplevel c);
  let ct  = class_table c
  and tvs = TVars_sub.tvars c.entry.tvs_sub
  and s   = signature c
  in
  let owner = Class_table.owner tvs s ct in
  let anchored = Class_table.anchored tvs owner ct in
  let nanchors = Array.length anchored in
  Class_table.check_deferred owner nanchors c.entry.info ct



let depth (c:t): int = c.depth

let rec ith_entry (i:int) (c:t): entry =
  assert (i <= depth c);
  if i = 0 then c.entry
  else ith_entry (i-1) (previous c)

let is_untyped (i:int) (c:t): bool =
  (* Is the variable [i] untyped? *)
  assert (i < count_variables c);
  let tp = snd c.entry.fargs.(i) in
  match tp with
    Variable j when j < count_type_variables c -> true
  | _ -> false



let variable_data (i:int) (c:t): Tvars.t * Sign.t =
  let nvars = count_variables c in
  if i < nvars then
    TVars_sub.tvars c.entry.tvs_sub,
    Sign.make_const (snd c.entry.fargs.(i))
  else
    let idx = i - nvars in
    let tvs,s = Feature_table.signature idx (feature_table c) in
    Tvars.fgs_to_global tvs, s


let variable (name:int) (c:t): int * Tvars.t * Sign.t =
  (** The term and the signature of the argument named [name] *)
  let i = variable_index name c in
  let tvs,s = variable_data i c in
  i,tvs,s


let make (verbosity:int): t =
  {entry = empty_entry;
   prev  = None;
   depth = 0;
   ft    = Feature_table.base_table verbosity;
   verbosity = verbosity
 }


let string_of_tvars (tv:TVars_sub.t) (c:t): string =
  let ct = class_table c
  and ntvs       = TVars_sub.count_local tv
  and fgnames    = TVars_sub.fgnames tv
  and fgconcepts = TVars_sub.fgconcepts tv
  and concepts   = Array.to_list (TVars_sub.concepts tv)
  in
  let fgs = Array.to_list (Myarray.combine fgnames fgconcepts) in
  let fgstring =
    String.concat ","
       (List.map
          (fun (nme,cpt) ->
            (ST.string nme) ^ ":" ^ Class_table.type2string cpt 0 [||] ct)
          fgs)
  and cptstring =
    String.concat ","
      (List.map (fun cpt -> Class_table.type2string cpt 0 [||] ct) concepts)
  in
  (string_of_int ntvs) ^ "[" ^ cptstring ^ "]["  ^ fgstring ^ "]"



let push_with_gap
    (entlst: entities list withinfo)
    (rt: return_type)
    (is_pred: bool)
    (is_func: bool)
    (rvar:    bool)
    (ntvs_gap:int)
    (c: t)
    : t =
  (** Push the new type variables, formal generics and the formal arguments of
      [entlst,rt] to the context [c] leaving a gap of [ntvs_gap] above the
      possibly newly introduced type variables of the signature. *)
  assert (not (is_pred && is_func));
  let entry      = c.entry
  and ct         = class_table c
  and mt         = module_table c in
  let tvs_sub  =
    Module_table.formal_generics entlst rt is_func ntvs_gap entry.tvs_sub mt in
  let tvs = TVars_sub.tvars tvs_sub
  in
  let ntvs0 = TVars_sub.count_local entry.tvs_sub
  and nfgs0 = TVars_sub.count_fgs entry.tvs_sub
  in
  let ntvs1 = Tvars.count_local tvs - ntvs0
  and nfgs1 = Tvars.count_fgs tvs   - nfgs0
  in
  let fargs1, res =
    Class_table.analyze_signature entlst rt is_pred is_func rvar tvs ct in
  let fargs =
    Array.append
      fargs1
      (Array.map
         (fun (n,t) -> n, Term.up ntvs1 (Term.upbound nfgs1 ntvs0 t))
         entry.fargs)
  and nargs_delta = Array.length fargs1 -
    if rvar then 1 else 0 (*variables*)
  in
  assert (0 <= nargs_delta);
  {c with
   entry =
   {tvs_sub    = tvs_sub;
    fargs        = fargs;
    ntvs_delta   = ntvs1;
    nfgs_delta   = nfgs1;
    nargs_delta  = nargs_delta;
    rvar         = Result_type.has_result res;
    result       = res;
    info         = entlst.i};
   prev  = Some c;
   depth = 1 + c.depth}




let push
    (entlst: entities list withinfo)
    (rt: return_type)
    (is_pred: bool)
    (is_func: bool)
    (rvar:    bool)
    (c: t)
    : t =
  (** Push the new type variables, formal generics and the formal arguments of
      [entlst,rt] to the context [c]. *)
  push_with_gap entlst rt is_pred is_func rvar 0 c




let push_untyped_with_gap
    (names:int array) (is_pred:bool) (is_func:bool) (rvar:bool) (ntvs_gap:int) (c:t)
    : t =
  let entlst = withinfo UNKNOWN [Untyped_entities (Array.to_list names)] in
  push_with_gap entlst None is_pred is_func rvar ntvs_gap c


let push_untyped_gap (names:int array) (ntvs_gap:int) (c:t): t =
  push_untyped_with_gap names false false false ntvs_gap c

let push_untyped (names:int array) (c:t): t =
  let entlst = withinfo UNKNOWN [Untyped_entities (Array.to_list names)] in
  push entlst None false false false c



let pop (c:t): t =
  (** Pop the last context
   *)
  assert (not (is_global c));
  previous c





let type_variables (c:t): TVars_sub.t = c.entry.tvs_sub

let boolean (c:t): term =
  Class_table.boolean_type (ntvs c)


let update_type_variables (tvs:TVars_sub.t) (c:t): unit =
  (** Update the type variables of the current context with [tvs]
   *)
  try
    TVars_sub.update_subs c.entry.tvs_sub tvs;
    let args = TVars_sub.args c.entry.tvs_sub in
    let ntvs = Array.length args                in
    Array.iteri
      (fun i (nme,t) -> c.entry.fargs.(i) <- (nme, Term.sub t args ntvs))
      c.entry.fargs
  with Term_capture ->
    not_yet_implemented c.entry.info "Type inference of formal generics"






let arguments_string (e:entry) (ct:Class_table.t): string =
  (** The string "(a:A, b1,b2:B, ... )" of all local arguments of the entry [e].
      In case that there are no arguments the empty string is returned and
      not "()".
   *)
  let nargs = entry_arity e in
  if nargs = 0 then
    ""
  else
    let fargs = Array.to_list (Array.sub e.fargs 0 nargs)
    in
    let llst = List.fold_left
        (fun ll (n,tp) -> match ll with
          [] -> [[n],tp]
        | (ns,tp1)::tl ->
            if tp=tp1 then [n::ns,tp]
            else           ([n],tp)::ll )
        []
        fargs
    in
    "("
    ^  String.concat
        ","
        (List.rev_map
           (fun (ns,tp) ->
             let ntvs = TVars_sub.count e.tvs_sub in
             (String.concat "," (List.rev_map (fun n -> ST.string n) ns))
             ^ ":"
             ^ (Class_table.type2string tp ntvs (entry_fgnames e) ct))
           llst)
    ^ ")"


let ith_arguments_string (i:int) (c:t): string =
  assert (i <= depth c);
  let e = ith_entry i c
  and ct = class_table c
  in
  arguments_string e ct


let local_arguments_string (c:t): string =
  let ct = class_table c in
  arguments_string c.entry ct


let result_string (e:entry) (ct:Class_table.t): string =
  if Result_type.has_result e.result then
    Class_table.type2string
      (Result_type.result e.result) 0 (entry_fgnames e) ct
  else ""


let named_signature_string (c:t): string =
  (** Print the signature of the context [c] with all argument names.
   *)
  let ct = class_table c in
  let argsstr = arguments_string c.entry ct
  and resstr  = result_string    c.entry ct
  in
  let has_args = argsstr <> ""
  and has_res  = resstr <> ""
  in
  if has_args && has_res then
    argsstr ^ ": " ^ resstr
  else if has_args then
    argsstr
  else
    resstr





let string_of_assertion (t:term) (c: t): string =
  "all"
  ^ (named_signature_string c) ^ " "
  ^ (string_of_term t true 0 c)


let put_formal_generic
    (name:int withinfo)
    (concept:type_t withinfo)
    (c:t)
    : unit =
  (** Add the formal generic [name] with its [concept] to the formal
      generics.
   *)
  assert (is_global c);
  Class_table.put_formal name concept (class_table c)




let find_funcs
    (fn:feature_name)
    (nargs:int)
    (c:t)
    : (int*Tvars.t*Sign.t) list =
  (** Find all the functions with name [fn] and [nargs] arguments in the
      global feature table and transform them into the context.
   *)
  let lst = Feature_table.find_funcs fn nargs c.ft
  in
  let lst = List.rev_map
      (fun (i,tvs,s) -> i+(count_variables c), tvs, s)
      lst
  in
  lst


let find_identifier
    (name:int)
    (nargs_id:int)
    (c:t)
    : (int * Tvars.t * Sign.t) list =
  (** Find the identifier named [name] which accepts [nargs] arguments
      in one of the local contexts or in the global feature table. Return
      the list of variables together with their signature
   *)
  if is_global c then
    find_funcs (FNname name) nargs_id c
  else
    try
      [variable name c]
    with
      Not_found ->
        find_funcs
          (FNname name) nargs_id c



let find_feature
    (fn:feature_name)
    (nargs_feat:int)
    (c:t)
    : (int * Tvars.t * Sign.t) list =
  (** Find the feature named [fn] which accepts [nargs] arguments global
      feature table. Return the list of variables together with their
      signature.
   *)
  find_funcs fn nargs_feat c




let definition (idx:int) (nb:int) (c:t): int * int array * term =
  let nbenv = count_variables c in
  if idx < nb + nbenv then
    raise Not_found
  else
    Feature_table.definition idx (nb + nbenv) (feature_table c)


let fully_expanded (t:term) (nb:int) (c:t): term =
  let rec expand t nb =
    let expargs args = Array.map (fun arg -> expand arg nb) args in
    let apply f args pr =
      match f with
        Lam(n,_,_,t0,_) ->
          beta_reduce n t0 args nb c
      | _ ->
          Application (f,args,pr)
    in
    match t with
      Variable i ->
        begin try
          let n,nms,t0 = definition i nb c in
          if n = 0 then
            t0
          else
            make_lambda n nms [] t0 false nb c
        with Not_found ->
          t
        end
    | VAppl (i, args) ->
        let args = expargs args in
        begin try
          let n,nms,t0 = definition i nb c in
          let t0 = expand t0 (n+nb) in
          if n = 0 then
            apply t0 args false
          else begin
            assert (n = Array.length args);
            Term.apply t0 args
          end
        with Not_found ->
          VAppl (i, args)
       end
    | Application (Variable i, args, pr) ->
        let args = expargs args in
        begin try
          let n,nms,t0 = definition i nb c in
          let t0 = expand t0 (n+nb) in
          if n = 0 then
            apply t0 args false
          else begin
            assert (n = Array.length args);
            beta_reduce n t0 args nb c
          end
        with Not_found ->
          Application (Variable i, args, pr)
       end
    | Application (f,args,pr) ->
        let f    = expand f nb
        and args = expargs args in
        apply f args pr
    | Lam (n,nms,pres,t,pr) ->
        Lam (n, nms, pres, expand t (1+nb), pr)
    | QExp (n,nms,t,is_all) ->
        QExp (n, nms, expand t (n+nb), is_all)
    | Flow (ctrl,args) ->
        t
  in
  expand t nb



let preconditions (idx:int) (nb:int) (c:t): int * int array * term list =
  let nbenv = count_variables c in
  if idx < nb + nbenv then
    0, [||], []
  else
    Feature_table.preconditions idx (nb+nbenv) (feature_table c)



let postconditions (idx:int) (nb:int) (c:t): int * int array * term list =
  let nbenv = count_variables c in
  if idx < nb + nbenv then
    0, [||], []
  else
    Feature_table.postconditions idx (nb+nbenv) (feature_table c)



let domain_of_lambda (n:int) (nms:int array) (pres:term list) (nb:int) (c:t): term =
  (* Construct the domain of a lambda expression with the precondition [pres] where
     the lambda expression is within an environment with [nb] variables more than the
     context [c].
   *)
  let nbenv = count_variables c in
  match pres with
    [] ->
      let true_id = 1 + nb + nbenv + Feature_table.true_index in
      Lam(n,nms,[],Variable true_id,true)
  | p::pres ->
      let and_id  = 1 + nb + nbenv + Feature_table.and_index in
      let inner =
        List.fold_left
          (fun t p -> Term.binary and_id t p)
          p
          pres in
      Lam(n,nms,[],inner,true)



let domain_of_feature (idx:int) (nb:int) (c:t): term =
  (* Construct the domain of feature [idx] in an environment with [nb] variables more
     than the context [c].
   *)
  let nbenv = count_variables c in
  if idx < nb + nbenv then
    assert false (* nyi: local features *)
  else
    Feature_table.domain_of_feature idx (nb+nbenv) c.ft


let remove_tuple_accessors (t:term) (nargs:int) (nb:int) (c:t): term =
  let nbenv = nb + count_variables c in
  Feature_table.remove_tuple_accessors t nargs nbenv c.ft


let tuple_of_args (args:term array) (nb:int) (c:t): term =
  let nbenv = nb + count_variables c in
  Feature_table.tuple_of_args args nbenv c.ft




let is_case_match_expression (t:term) (c:t): bool =
  (* Is the term [t] a match expression (i.e. does it consist only of variables of
     the inner context and constructors)? *)
  let nvars0 = count_last_variables c
  and nvars  = count_variables c
  in
  let rec is_match t =
    let is_match_args res args =
      Array.fold_left (fun res arg -> res && is_match arg) res args in
    match t with
      Variable i when i < nvars0 -> true
    | Variable i when i < nvars  -> false
    | Variable i ->
        Feature_table.is_constructor (i-nvars) c.ft
    | VAppl(i,args) ->
        let res = Feature_table.is_constructor (i-nvars) c.ft in
        is_match_args res args
    | _ ->
        false
  in
  is_match t





(* Calculation of preconditions:

       a ==> b:   pa0, pa1, ..., a ==> pb0, a ==> pb1, ...

       a and b:   same as 'a ==> b'


       a or b:    pa0, pa1, ..., not a ==> pb0, not a ==> pb1, ...

       if c then a else b end:
                  pc0,pc1,...,
                  c or not c,
                  c ==> pa0,c==>pa1,...,
                  not c ==> pb0, not c ==> pb1,...


       all(x,y,...) e:
                  all(x,y,...) pe0, all(x,y,...) pe1, ...

       some(x,y,...) e:
                  same as 'all(x,y,...) e'

       {x,y,...: e}:
                  same as 'all(x,y,...) e'

       (x,y,...) -> e:
                  no preconditions

       f(x,y,...): px, py, ...               -- function object application
                   (x,y,...) in f.domain

       p(x,y,...): px, py, ...               -- predicate (relation) application
                   no preconditions

       f(x,y,...):
                  pf0, pf1, ...
                  px0,...,py0,...,...
                  (x,y,...).(f.domain)
 *)
(*
  (x -> y -> exp) (x) ~> (y -> exp)
 *)


let case_preconditions
    (insp:term) (n:int) (nms:int array) (pat:term)
    (pres:term list) (lst:term list) (nb:int) (c:t)
    : term list =
  (*  Generate all(x,y,...) insp = pat ==> pre
   *)
  let insp   = Term.up n insp
  and imp_id = n + nb + implication_index c
  and eq_id  =
    let i =
      match pat with
        Variable i -> i
      | VAppl(i,_) -> i
      | _ -> assert false (* cannot happen in pattern *)
    in
    let ndelta = n + nb + count_variables c in
    let i = i - ndelta in
    assert (0 <= i);
    assert (Feature_table.is_constructor i c.ft);
    let cls = Feature_table.class_of_feature i c.ft in
    ndelta + Feature_table.equality_index cls c.ft
  in
  List.fold_left
    (fun lst pre ->
      let t = Term.binary imp_id (Term.binary eq_id insp pat) pre in
      let t = Term.all_quantified n nms t in
      t :: lst)
    lst
    pres



let term_preconditions (t:term)  (c:t): term list =
  let imp_id0 = implication_index c
  and and_id0 = and_index c
  and or_id0  = or_index c
  and not_id0 = not_index c
  and dom_id0 = domain_index c
  in
  let rec pres (t:term) (nb:int) (lst:term list): term list * term option =
    let imp_id  = nb + imp_id0
    and and_id  = nb + and_id0
    and or_id   = nb + or_id0
    and not_id  = nb + not_id0
    and dom_id  = nb + dom_id0
    in
    let remove_tup t n = remove_tuple_accessors t n nb c in
    let remove_tup_lst lst n =
      List.map (fun t -> remove_tup t n) lst
    in
    let pres_args args lst =
      Array.fold_left
        (fun lst t -> let lst,_ = pres t nb lst in lst)
        lst
        args
    and pres_lam n nms t lst =
      let lst0,_ = pres t (n+nb) [] in
      List.fold_right
        (fun t lst -> QExp(n,nms,t,true)::lst)
        lst0
        lst
    in
    let domain_t =  Some (VAppl (dom_id,[|t|])) in
    match t with
    | Variable i ->
       lst, domain_t
    | VAppl (i, args) when i = imp_id || i = and_id ->
        assert (Array.length args = 2);
        let lst1,_ = pres args.(0) nb lst
        and lst2,_ = pres args.(1) nb []  in
        List.fold_right
          (fun t lst -> (Term.binary imp_id args.(0) t)::lst)
          lst2
          lst1,
        domain_t
    | VAppl (i, args) when i = or_id ->
        assert (Array.length args = 2);
        let lst1,_  = pres args.(0) nb lst
        and lst2,_  = pres args.(1) nb []
        and not_t = Term.unary not_id args.(0) in
        List.fold_right
          (fun t lst -> (Term.binary imp_id not_t t)::lst)
          lst2
          lst1,
        domain_t
    | VAppl (i,args) ->
        let n,nms,lst1 = preconditions i nb c in
        assert (n = Array.length args);
        let lst = pres_args args lst in
        List.fold_left
          (fun lst t -> (Term.apply t args)::lst)
          lst
          lst1,
        domain_t
    | Application (f,args,pr) when pr ->
        let lst,dom = pres f nb lst in
        pres_args args lst,
        None
    | Application (f,args,pr) ->
        assert (Array.length args = 1);
        let lst,dom = pres f nb lst in
        let lst = pres_args args lst in
        begin match dom with
          Some dom ->
            Application(dom,args,true)::lst
        | None ->
            lst
        end,
        domain_t
    | Lam (n,nms,pres0,t0,pr) ->
        let pres0     = remove_tup_lst pres0 n
        and t0        = remove_tup t0 n
        and imp_id    = n + imp_id in
        let lst,_ = (* collect preconditions of preconditions *)
          List.fold_left
            (fun (lst,plst) p ->
              let pres_p,_ = pres p (n+nb) [] in
              let lst = List.fold_left
                  (fun lst pre_p ->
                    let chn = Term.make_implication_chain plst pre_p imp_id in
                    QExp(n,nms,chn,true)::lst)
                  lst
                  pres_p
              in
              lst, p::plst)
            (lst,[])
            pres0
        in
        let pres_t0,_ = pres t0 (n+nb) [] in
        let lst = (* preconditions have to imply the preconditions of the inner
                     expression *)
          let pres0_rev = List.rev pres0 in
          List.fold_right
            (fun tgt lst ->
              let chn = Term.make_implication_chain pres0_rev tgt imp_id in
              QExp(n,nms,chn,true)::lst)
            pres_t0 (* is reversed *)
            lst in
        lst,None
    | QExp (n,nms,t0,is_all) ->
        pres_lam n nms t0 lst,
        None
    | Flow (ctrl,args) ->
        let len = Array.length args in
        begin
          match ctrl with
            Ifexp ->
              assert (2 <= len);
              assert (len <= 3);
              let lst1,_ = pres args.(0) nb lst
              and lst2,_ = pres args.(1) nb []
              in
              let reslst =
                List.fold_right
                  (fun t lst -> (Term.binary imp_id args.(0) t) :: lst)
                  lst2
                  lst1
              in
              let reslst =
                if len = 2 then
                  args.(0) :: reslst
                else
                  let neg = Term.unary not_id args.(0)
                  and lst3,_ = pres args.(2) nb [] in
                  List.fold_right
                    (fun t lst -> (Term.binary imp_id neg t) :: lst)
                    lst3
                    reslst
              in
              reslst, domain_t
          | Inspect ->
              assert (3 <= len);
              assert (len mod 2 = 1);
              let ncases = len / 2
              and nvars = count_variables c in
              let unmatched =
                Feature_table.unmatched_inspect_cases args (nb+nvars) c.ft
              in
              let lst = List.fold_left
                  (fun lst (n,mtch) ->
                    let nms = Feature_table.standard_argnames n in
                    let q   = Term.pattern n nms mtch in
                    let t = Flow(Asexp,[|args.(0);q|]) in
                    let t = Term.unary not_id t in
                    t :: lst)
                  lst
                  unmatched in
              let rec cases_from (i:int) (lst:term list): term list =
                if i = ncases then
                  lst
                else
                  let n,nms,pat,res = Term.case_split args.(2*i+1) args.(2*i+2) in
                  let lst_inner,_ = pres res (nb+n) [] in
                  let lst_inner   = List.rev lst_inner in
                  let lst =
                    case_preconditions args.(0) n nms pat lst_inner lst nb c in
                  cases_from (i+1) lst
              in
              let lst = cases_from 0 lst in
              lst, domain_t
          | Asexp ->
              assert (len = 2);
              pres args.(0) nb lst
        end
  in
  let ps,_ = pres t 0 [] in
  List.rev ps



let existence_condition (posts:term list) (c:t): term =
  (* Generate the existence condition

         some(x) e1_x and e2_x and ...

     where [ei_x] is the ith postcondition with the variable [Result] substituted
     by [x].
   *)
  assert (has_result_variable c);
  assert (posts <> []);
  let nargs   = count_last_arguments c
  and and_id  = 1 + and_index c
  in
  let args =
    Array.init
      (1 + nargs)
      (fun i -> if i < nargs then Variable (1+i) else Variable 0) in
  let replace t =
    Term.sub t args (2 + nargs)
  in
  let term_inner =
    List.fold_left
      (fun inner p -> Term.binary and_id inner (replace p))
      (replace (List.hd posts))
      (List.tl posts) in
  some_quantified 1 [|ST.symbol "x"|] term_inner c



let uniqueness_condition (posts:term list) (c:t): term =
  (* Generate the uniqueness condition

         all(x,y) e1_x ==> e1_y ==> ...
                  e2_x ==> e2_y ==> ... ==> x = y

     where [ei_x]/[ei_y] is the ith postcondition with the variable [Result]
     substituted by [x]/[y].  *)
  assert (has_result_variable c);
  assert (posts <> []);
  let nargs   = count_last_arguments c
  and imp_id  = 2 + implication_index c
  and rt      = result_type c
  and tvs     = tvars c
  in
  let cls = Tvars.principal_class rt tvs in
  let eq_id  = 2 + (count_variables c)
      + Feature_table.variant Feature_table.eq_index cls c.ft in
  let args_var xyvar  =
    assert (xyvar < 2);
    Array.init
      (1 + nargs)
      (fun i -> if i < nargs then Variable (2+i) else Variable xyvar) in
  let argsx = args_var 0
  and argsy = args_var 1 in
  let replace_by_args t args =
    Term.sub t args (3 + nargs)
  in
  let term_inner =
    List.fold_right
      (fun t inner ->
        let t1 = Term.binary imp_id (replace_by_args t argsy) inner in
        Term.binary imp_id (replace_by_args t argsx) t1)
      posts
      (Term.binary eq_id (Variable 0) (Variable 1)) in
  all_quantified 2 [|ST.symbol "x";ST.symbol "y"|] term_inner c





let function_postconditions (idx:int) (posts:term list) (c:t): term list =
  (* Generate the postconditions

     [e1_f; e2_f; ...]

     where [ei_f] is [ei] with the variable [Result] substituted by [f(a,b,...)] and
     [idx] is the index of the function [f].
   *)
  assert (has_result_variable c);
  assert (posts <> []);
  let nargs   = count_last_arguments c in
  let fargs = Array.init nargs (fun i -> Variable i) in
  let fterm = VAppl (1+nargs+idx, fargs) in
  let args  =
    Array.init (1+nargs) (fun i -> if i < nargs then Variable i else fterm) in
  let replace t = Term.sub t args (1+nargs) in
  List.map replace posts


let get_type (tp:type_t withinfo) (c:t): type_term =
  let tvs = tvars c in
  Class_table.get_type tp tvs (class_table c)

let string_of_type (tp:type_term) (c:t): string =
  Class_table.string_of_type tp (tvars c) (class_table c)


let downgrade_term (t:term) (nb:int) (c:t): term =
  Feature_table.downgrade_term t (nb + count_variables c) c.ft
