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


let rec is_outer (c_outer:t) (c:t): bool =
  if c_outer == c then
    true
  else
    match c.prev with
      None ->
        false
    | Some c ->
        is_outer c_outer c



let entry_arity (e:entry): int = e.nargs_delta

let arity     (c:t): int = entry_arity c.entry

let verbosity (c:t): int = c.verbosity

let info (c:t): info = c.entry.info

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

let count_last_type_variables (c:t): int =
  c.entry.ntvs_delta

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

let tuple_index (c:t): int =
  count_variables c + Feature_table.tuple_index


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


let function_index (c:t): int =
  ntvs c + Class_table.function_index

let predicate_index (c:t): int =
  ntvs c + Class_table.predicate_index

let tuple_class (c:t): int =
  ntvs c + Class_table.tuple_index


let function_type (a_tp: type_term) (r_tp: type_term) (c:t): type_term =
  VAppl (function_index c, [|a_tp;r_tp|], [||])

let predicate_type (a_tp: type_term) (c:t): type_term =
  VAppl (predicate_index c, [|a_tp|], [||])

let entry_local_argnames (e:entry): int array =
  Array.init e.nargs_delta (fun i -> fst e.fargs.(i))

let entry_local_types (e:entry): term array =
  Array.init e.nargs_delta (fun i -> snd e.fargs.(i))


let local_argnames (c:t): int array = entry_local_argnames c.entry

let local_types (c:t): term array = entry_local_types c.entry

let local_formals (c:t): formals =
  entry_local_argnames c.entry,
  entry_local_types c.entry

let local_fgs (c:t): formals =
  let tvs = TVars_sub.tvars c.entry.tvs_sub in
  let nfgs = c.entry.nfgs_delta in
  let fgnms = Array.sub (Tvars.fgnames tvs) 0 nfgs
  and fgcon = Array.sub (Tvars.fgconcepts tvs) 0 nfgs in
  fgnms,fgcon



let local_type_reduced (i:int) (c:t): type_term =
  (* Requires that the type of argument i does not contain local type variables *)
  assert (i < count_last_arguments c);
  let ntvs = count_last_type_variables c in
  let _,tp = c.entry.fargs.(i) in
  try
    Term.down ntvs tp
  with
    Term_capture ->
      assert false (* precondition violated *)



let local_types_reduced (c:t): types =
  let nargs = count_last_arguments c in
  Array.init nargs (fun i -> local_type_reduced i c)



let entry_varnames (e:entry): int array =
  Array.map (fun (n,_) -> n) e.fargs


let varnames (c:t): int array = entry_varnames c.entry



let entry_fgnames (e:entry): int array = TVars_sub.fgnames e.tvs_sub

let entry_fgconcepts (e:entry): type_term array = TVars_sub.fgconcepts e.tvs_sub

let fgnames (c:t): int array = entry_fgnames c.entry

let fgconcepts (c:t): type_term array = entry_fgconcepts c.entry

let tvars_sub (c:t): TVars_sub.t = c.entry.tvs_sub

let tvars (c:t): Tvars.t = TVars_sub.tvars c.entry.tvs_sub

let string_of_signature (s:Sign.t) (c:t): string =
  Class_table.string_of_signature
    s
    (tvars c)
    (class_table c)


let string_of_term0 (t:term) (norm:bool) (long:bool) (nanon:int) (c:t): string =
  let tvs = tvars c in
  Feature_table.term_to_string t norm long nanon (varnames c) tvs c.ft

let string_of_term (t:term) (c:t): string =
  string_of_term0 t true false 0 c

let string_long_of_term (t:term) (c:t): string =
  string_of_term0 t true true 0 c


let string_of_term_anon (t:term) (nb:int) (c:t): string =
  string_of_term0 t true false nb c


let string_long_of_term_anon (t:term) (nb:int) (c:t): string =
  string_of_term0 t true true nb c


let string_of_term_array (sep:string) (arr: term array) (c:t): string =
  String.concat sep
    (List.map (fun t -> string_of_term t c) (Array.to_list arr))

let string_of_arguments (arr: term array) (c:t): string =
  "(" ^ (string_of_term_array "," arr c) ^ ")"


let string_of_type_term (tp:type_term) (c:t): string =
  Class_table.string_of_type tp (tvars c) (class_table c)


let string_of_type_array (sep:string) (tps:types) (c:t): string =
  String.concat sep
    (List.map (fun tp -> string_of_type_term tp c) (Array.to_list tps))

let string_of_ags (ags:agens) (c:t): string =
  "["
  ^ (string_of_type_array "," ags c)
  ^ "]"


let make_lambda
    (n:int) (nms:int array) (ps:term list) (t:term) (pred:bool) (nb:int) (c:t)
    : term =
  let nbenv = count_variables c in
  assert false
  (*Feature_table.make_lambda n nms ps t pred (nb+nbenv) c.ft*)


let make_application
    (f:term) (args:term array) (nb:int) (pred:bool) (c:t): term =
  let nbenv = count_variables c in
  let res = Feature_table.make_application f args pred (nb+nbenv) c.ft in
  res


let beta_reduce
    (n:int) (tlam:term) (tp:type_term) (args:term array) (nb:int )(c:t)
    : term =
  Feature_table.beta_reduce n tlam tp args (nb+count_variables c) c.ft


let quantified (is_all:bool) (nargs:int) (tps:formals) (fgs:formals) (t:term) (c:t)
    : term =
  Term.quantified is_all nargs tps fgs t

let all_quantified (nargs:int) (tps:formals) (fgs:formals) (t:term) (c:t): term =
  quantified true nargs tps fgs t c

let some_quantified (nargs:int) (tps:formals) (fgs:formals) (t:term) (c:t): term =
  quantified false nargs tps fgs t c


let prenex_term (t:term) (c:t): term =
  Term.prenex t (count_variables c) (ntvs c) Feature_table.implication_index


let entry_signature (e:entry) (c:t): Sign.t =
  (** The signature of the entry [e] in the context [c].  *)
  let argtypes = Array.init (entry_arity e) (fun i -> snd e.fargs.(i)) in
  Sign.make argtypes e.result




let signature (c:t): Sign.t =
  (** The signature of the context [c].  *)
  entry_signature c.entry c


let signature_string (c:t): string =
  (** Print the signature of the context [c].  *)
  string_of_signature (signature c) c


let variable_index (nme:int) (c:t): int =
  Search.array_find_min (fun (n,_) -> n = nme) c.entry.fargs



let unique_name (nme:int) (c:t): int =
  let patched nme = ST.symbol ("$" ^ (ST.string nme)) in
  let rec name n =
    try ignore(variable_index n c); name (patched n)
    with Not_found -> n
  in
  name nme


let unique_names (nms:int array) (c:t): int array =
  let nms  = Array.copy nms in
  Array.iteri (fun i n -> nms.(i) <- unique_name n c) nms;
  nms




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
         (fun (n,t) -> n, Term.up ntvs1 (Term.up_from nfgs1 ntvs0 t))
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


let push_typed ((nms,tps):formals) ((fgnms,fgcon):formals) (c:t): t =
  assert (ntvs c = 0 || (fgnms,fgcon) = empty_formals);
  let nfgs_new  = Array.length fgcon
  and nargs_new = Array.length tps in
  assert (nfgs_new  = Array.length fgnms);
  assert (nargs_new = Array.length nms);
  let tvs_sub = TVars_sub.augment 0 fgnms fgcon c.entry.tvs_sub in
  let ntvs0   = TVars_sub.count_local c.entry.tvs_sub in
  let nargs   = nargs_new + Array.length c.entry.fargs in
  let fargs = Array.init nargs
      (fun i ->
        if i < nargs_new then nms.(i), tps.(i)
        else
          let i = i - nargs_new in
          let nme,con = c.entry.fargs.(i) in
          let con = Term.up_from nfgs_new ntvs0 con in
          nme,con) in
  {c with
   entry =
   {tvs_sub = tvs_sub;
    fargs   = fargs;
    ntvs_delta  = 0;
    nfgs_delta  = nfgs_new;
    nargs_delta = nargs_new;
    rvar    = false;
    result  = Result_type.empty;
    info    = UNKNOWN};
   prev = Some c;
   depth = 1 + c.depth}



let extract_from_tuple (n:int) (tp:type_term) (c:t): types =
  Class_table.extract_from_tuple n (ntvs c) tp


let push_lambda (n:int) (nms:names) (tp:type_term) (c:t): t =
  assert (0 < n);
  assert (n = Array.length nms);
  let cls,ags = Class_table.split_type_term tp
  and all_ntvs = ntvs c
  in
  let cls0 = cls - all_ntvs in
  assert (cls0 = Class_table.predicate_index && Array.length ags = 1
        || cls0 = Class_table.function_index && Array.length ags = 2);
  let tps = extract_from_tuple n ags.(0) c in
  push_typed (nms,tps) empty_formals c




let pop (c:t): t =
  (** Pop the last context
   *)
  assert (not (is_global c));
  previous c





let type_variables (c:t): TVars_sub.t = c.entry.tvs_sub


let boolean (c:t): term =
  Class_table.boolean_type (ntvs c)


let rec type_of_term (t:term) (c:t): type_term =
  let nvars = count_variables c in
  match t with
    Variable i when i < nvars -> variable_type i c
  | Variable i -> assert false (* Global constants are not variables *)
  | VAppl(i,args,ags) ->
      assert (nvars <= i);
      Feature_table.result_type (i-nvars) ags (ntvs c) c.ft
  | Application(f,args,pr) ->
      if pr then
        boolean c
      else begin
        let f_tp = type_of_term f c in
        let cls,ags = Class_table.split_type_term f_tp in
        assert (Array.length ags = 2);
        assert (cls = function_index c);
        ags.(1)
      end
  | Lam(_,_,_,_,_,tp) -> tp
  | QExp _            -> boolean c
  | Indset (_,tp,_)   -> tp
  | Flow(ctrl,args) ->
      match ctrl with
        Ifexp ->
          assert (2 <= Array.length args);
          type_of_term args.(1) c
      | Inspect ->
          assert (3 <= Array.length args);
          let _,tps,res = Term.pattern_split args.(2) in
          let c1 = push_typed tps empty_formals c in
          type_of_term res c1
      | Asexp ->
          boolean c


let predicate_of_type (tp:type_term) (c:t): type_term =
  let pred_idx = predicate_index c in
  VAppl(pred_idx,[|tp|],[||])


let predicate_of_term (t:term) (c:t): type_term =
  let tp = type_of_term t c in
  predicate_of_type tp c


let update_types (subs:type_term array) (c:t): unit =
  let len = Array.length subs in
  assert (len = TVars_sub.count_local c.entry.tvs_sub);
  Array.iteri
    (fun i (nme,tp) ->
      let tp = Term.subst tp len subs in
      c.entry.fargs.(i) <- nme,tp)
    c.entry.fargs



let arguments_string (e:entry) (ct:Class_table.t): string =
  (* The string "(a:A, b1,b2:B, ... )" of all local arguments of the entry [e].
     In case that there are no arguments the empty string is returned and
     not "()". In case that there are formal generics they are prefixed.
   *)
  let nargs = entry_arity e
  and tvs   = TVars_sub.tvars e.tvs_sub
  in
  let args = Array.sub e.fargs 0 nargs in
  Class_table.arguments_string tvs args ct



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
  ^ (string_of_term t c)


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




let definition (idx:int) (nb:int) (ags:agens) (c:t)
    : int * int array * term =
  let nbenv = count_variables c in
  if idx < nb + nbenv then
    raise Not_found
  else
    Feature_table.definition idx (nb + nbenv) ags (tvars c) (feature_table c)



let arity (idx:int) (nb:int) (c:t): int =
  let nbenv = count_variables c in
  if idx < nb + nbenv then
    0
  else
    Feature_table.arity (idx-nb-nbenv) c.ft



let fully_expanded (t:term) (nb:int) (c:t): term =
  let nvars = count_variables c
  and tvs   = tvars c in
  Feature_table.fully_expanded t (nb+nvars) tvs c.ft



let is_inductive_set (i:int) (c:t): bool =
  let nb = count_variables c in
  nb <= i &&
  Feature_table.is_inductive_set i nb c.ft



let inductive_set (t:term) (c:t): term =
  (* The inductive set represented by the term [t]. *)
  let nb = count_variables c
  and tvs  = tvars c in
  let indset i args ags =
    if i < nb then
      raise Not_found
    else
      Feature_table.inductive_set i args ags nb tvs c.ft in
  match t with
    Indset _ ->
      t
  | VAppl (i,args,ags) ->
      indset i args ags
  | _ ->
      raise Not_found


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


let function_property (idx:int) (i:int) (args:term array) (c:t): term =
  let nbenv = count_variables c in
  if idx < nbenv then invalid_arg "variables don't have properties";
  Feature_table.function_property idx i nbenv args c.ft


let has_preconditions (idx:int) (nb:int) (c:t): bool =
  let _,_,lst = preconditions idx nb c in
  lst <> []



let domain_type (tp:type_term) (c:t): type_term =
  (* [tp] is either a function type [A->B] or a predicate type {A}. The domain
     type is in both cases A.
   *)
  Class_table.domain_type tp




let domain_of_lambda
    (n:int) (nms:int array) (pres:term list) (f_tp:type_term) (nb:int) (c:t)
    : term =
  (* Construct the domain of a lambda expression with the preconditions [pres] where
     the lambda expression is within an environment with [nb] variables more than the
     context [c].

     The lambda expression must have function type because the function 'domain'
     requires a function argument.

         agent (a:A): B
             require
                 p1; p2; ...
             ensure
                 -> ...
             end

     The domain is the set {a:A: p1 and p2 and ... } or {a:A: true} in case that
     there are no preconditions.
   *)
  let a_tp = domain_type f_tp c in
  let p_tp = predicate_type a_tp c in
  let nbenv = count_variables c
  and is_pred = true
  in
  match pres with
    [] ->
      let true_const = Feature_table.true_constant (1+nb+nbenv) in
      Lam(n, nms, [], true_const, is_pred, p_tp)
  | p::pres ->
      let and_id  = 1 + nb + nbenv + Feature_table.and_index in
      let inner =
        List.fold_left
          (fun t p -> Term.binary and_id t p)
          p
          pres in
      Lam(n, nms, [], inner, is_pred, p_tp)



let domain_of_feature (idx:int) (nb:int) (c:t): term =
  (* Construct the domain of feature [idx] in an environment with [nb] variables more
     than the context [c].
   *)
  let nbenv = count_variables c in
  if idx < nb + nbenv then
    assert false (* nyi: local features *)
  else
    Feature_table.domain_of_feature idx (nb+nbenv) c.ft


let remove_tuple_accessors (t:term) (nargs:int) (c:t): term =
  let nbenv = count_variables c in
  Feature_table.remove_tuple_accessors t nargs nbenv c.ft


let tuple_of_args (args:arguments) (tup_tp:type_term) (c:t): term =
  (* The arguments [a,b,...] transformed to a tuple (a,b,...) or the type [tup_tp].
   *)
  let nargs = Array.length args
  and tup_id = tuple_index c
  in
  assert (0 < nargs);
  let rec tup_from (i:int) (tup_tp:type_term): term =
    if i = nargs - 1 then
      args.(i)
    else begin
      assert (i + 2 <= nargs);
      let cls,ags = Class_table.split_type_term tup_tp in
      assert (cls = tuple_class c);
      assert (Array.length ags = 2);
      let b = tup_from (i + 1) ags.(1) in
      VAppl (tup_id, [| args.(i); b |], ags)
    end
  in
  tup_from 0 tup_tp


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
    | VAppl(i,args,_) ->
        let res = Feature_table.is_constructor (i-nvars) c.ft in
        is_match_args res args
    | _ ->
        false
  in
  is_match t


exception Type_error of string




let rec type_of_term_full (t:term) (trace:bool) (c:t): type_term =
  let nvars = count_variables c
  and ntvs  = ntvs c in
  let getargs args c = Array.map (fun t -> type_of_term_full t trace c) args
  and split_type_term tp pr =
    let cls,ags = Class_table.split_type_term tp in
    assert (ntvs <= cls);
    if pr then begin
      if cls <> ntvs + Class_table.predicate_index then
        raise (Type_error
                 ("The type " ^ string_of_type_term tp c ^ " is not a predicate"));
      assert (Array.length ags = 1)
    end else begin
      if cls <> ntvs + Class_table.function_index then
        raise (Type_error
                 ("The type " ^ string_of_type_term tp c ^ " is not a function"));
      assert (Array.length ags = 2)
    end;
    ags
  in
  let feature_signature (i:int) (ags:type_term array): Sign.t =
    assert (nvars <= i);
    let tvs,s = Feature_table.signature (i-nvars) c.ft in
    if Tvars.count_fgs tvs <> Array.length ags then
      raise (Type_error
               ("The feature \"" ^
                Feature_table.string_of_signature (i-nvars) c.ft ^
                "\" does not have " ^ string_of_int (Array.length ags) ^
                " formal generic(s)"));
    let trans tp = Term.subst tp ntvs ags in
    Sign.map trans s
  in
  let trace_tp tp =
    if trace then
      printf "  %s : %s\n" (string_long_of_term t c) (string_of_type_term tp c);
    tp
  in
  let check_args sub reqargs actargs =
    if reqargs <> actargs then
      raise (Type_error
               ("\n    term:     " ^ string_of_term t c ^
                "\n    subterm : " ^ string_of_term sub c ^
                "\n    required argument types: " ^
                string_of_ags reqargs c ^
                "\n    actual argument types: " ^
                string_of_ags actargs c))
  in
  match t with
    Variable i ->
      assert (i < nvars);
      trace_tp (variable_type i c)
  | VAppl (i,args,ags) ->
      assert (nvars <= i);
      let argtps = getargs args c
      and s      = feature_signature i ags in
      assert (Sign.has_result s);
      check_args t (Sign.arguments s) argtps;
      trace_tp (Sign.result s)
  | Application (f,args,pr) ->
      assert (Array.length args = 1);
      let ftp    = type_of_term_full f trace c
      and argtps = getargs args c in
      let ags = split_type_term ftp pr in
      check_args t [|ags.(0)|] argtps;
      if pr then
        trace_tp (boolean c)
      else
        trace_tp (ags.(1))
  | Lam (n,nms,ps,t0,pr,tp) ->
      let ags = split_type_term tp pr in
      let c1 = push_typed ([|ST.symbol "t"|],[|ags.(0)|]) empty_formals c in
      let rtp = type_of_term_full t0 trace c1 in
      if pr then
        assert (rtp = boolean c)
      else
        assert (rtp = ags.(1));
      trace_tp tp
  | QExp (n,tps,fgs,t0,is_all) ->
      assert (ntvs = 0 || fgs = empty_formals);
      let c1 = push_typed tps fgs c in
      let rtp = type_of_term_full t0 trace c1 in
      if rtp <> boolean c1 then begin
        printf "rtp  %s\n" (string_of_type_term rtp c1);
        printf "bool %s\n" (string_of_type_term (boolean c1) c1);
      end;
      assert (rtp = boolean c1);
      trace_tp (boolean c)
  | Indset (nme,tp,rs) ->
      tp
  | Flow (ctrl,args) ->
      let len = Array.length args in
      match ctrl with
        Ifexp ->
          assert (2 <= len);
          assert (len <= 3);
          let cond_tp = type_of_term_full args.(0) trace c
          and if_tp   = type_of_term_full args.(1) trace c
          in
          assert (cond_tp = boolean c);
          if len = 3 then begin
            let else_tp = type_of_term_full args.(2) trace c in
            assert (if_tp = else_tp)
          end;
          trace_tp if_tp
      | Asexp ->
          assert (len = 2);
          let tp = type_of_term_full args.(0) trace c in
          let n,tps,t0 = Term.pattern_split args.(1) in
          let c1 = push_typed tps empty_formals c in
          let pat_tp = type_of_term_full t0 trace c1 in
          if tp <> pat_tp then
            raise (Type_error (
                   ("Types in \"" ^ string_of_term t c ^
                    "\" are different\n    " ^
                    string_of_term args.(0) c ^ ": " ^
                    (string_of_type_term tp c) ^
                    "\n    " ^
                    string_of_term t0 c1 ^ ": "  ^
                    (string_of_type_term pat_tp c)
                   )));
          boolean c
      | Inspect ->
          assert (3 <= len);
          assert (len mod 2 = 1);
          let ncases = len / 2 in
          assert (0 < ncases);
          let insp_tp = type_of_term_full args.(0) trace c in
          let rec check_cases_from i tp =
            if i = ncases then
              tp
            else
              let n,(nms,tps),pat,res =
                Term.case_split args.(2*i+1) args.(2*i+2) in
              let c1 = push_typed (nms,tps) empty_formals c in
              let insp_tp_i =  type_of_term_full pat trace c1
              and res_tp_i  =  type_of_term_full res trace c1 in
              if insp_tp <> insp_tp_i then
                raise (Type_error
                         ("Pattern of case " ^ string_of_term pat c1 ^
                          " does not have type " ^
                            string_of_type_term insp_tp c1));
              if tp <> empty_term && tp <> res_tp_i then
                  raise (Type_error
                           ("Term " ^ string_of_term res c1 ^
                            " does not have type " ^
                            string_of_type_term tp c1));
              res_tp_i
          in
          trace_tp (check_cases_from 0 empty_term)



let check_well_typed (t:term) (c:t): unit =
  let check trace = ignore(type_of_term_full t trace c) in
  try
    check false
  with Type_error str ->
    printf "check_well_typed\n  \"%s\"\n  \"%s\"\n"
      (string_long_of_term t c) (Term.to_string t);
    printf "  type error: %s\n" str;
    check true


let is_well_typed (t:term) (c:t): bool =
  try check_well_typed t c; true
  with Type_error _ -> false



let transformed_term0 (t:term) (nargs:int) (c0:t) (c:t): term =
  (* The term [t] with [nargs] arguments valid in the context [c0] transformed
     to the inner context [c].  *)
  assert (is_outer c0 c);
  if is_global c0 then begin
    assert (not (Term.is_all_quantified t));
    let nvars = count_variables c
    and ntvs  = count_formal_generics c + count_type_variables c in
    Term.shift_from nvars nargs ntvs 0 t
  end else begin
    assert (not (is_global c0));
    assert (count_formal_generics c0 = count_formal_generics c);
    let ntvs0 = count_type_variables c0
    and ntvs  = count_type_variables c in
    assert (ntvs0 <= ntvs);
    let nvars0 = count_variables c0
    and nvars  = count_variables c in
    assert (nvars0 <= nvars);
    Term.shift_from (nvars-nvars0) nargs (ntvs-ntvs0) 0 t
  end


let transformed_term (t:term) (c0:t) (c:t): term =
  (* The term [t] valid in the context [c0] transformed to the inner context
     [c].
   *)
  transformed_term0 t 0 c0 c


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

       agent(x:X,y:Y,...)
           require r0;r1;...
           ensure  -> t
           end

   Lambda terms

      A lambda term is either

          {a,b,...: t}

      or

          agent (a,b,...)
              require
                  r0; r1; ...
              ensure
                  -> t
              end

      The preconditions are:

             all(a,b,..) p0r0     -- The preconditions of 'r0' have to be
             all(a,b,..) p1r0     -- satisfied
             ...
             all(a,b,..) r0 ==> p0r1
             all(a,b,..) r0 ==> p1r1
             ...
             all(a,b,..) r0 ==> r1 ==> p0r2
             all(a,b,..) r0 ==> r1 ==> p1r2
             ...
             ...
             all(a,b,..) r0 ==> r1 ==> ... ==> p0t
             all(a,b,..) r0 ==> r1 ==> ... ==> p1t
             ...

      Note: A set expression does not have inner preconditions, therefore we
            get as a special case (which is included in the above scheme):

             all(a,b,..) p0t
             all(a,b,..) p1t
             ...
   *)


let case_preconditions
    (insp:term) (n:int) (nms:int array) (tps:types) (pat:term)
    (pres:term list) (lst:term list) (nb:int) (c:t)
    : term list =
  (*  Generate all(x,y,...) insp = pat ==> pre
   *)
  let insp   = Term.up n insp
  and imp_id = n + nb + implication_index c
  and eq_id  =
    let i =
      match pat with
        Variable i   -> i
      | VAppl(i,_,_) -> i
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
      let t = Term.all_quantified n (nms,tps) empty_formals t in
      t :: lst)
    lst
    pres





let term_preconditions (t:term)  (c:t): term list =
  (* The preconditions of the term [t] *)
  let all_ntvs = ntvs c
  in
  let rec pres
      (t:term) (lst:term list) (c:t)
      : term list =
    let imp_id = implication_index c
    and or_id  = or_index c
    and and_id = and_index c
    and not_id = not_index c in
    let pres_args args lst =
      Array.fold_left
        (fun lst t -> pres t lst c)
        lst
        args
    in
    match t with
    | Variable i ->
       lst
    | VAppl (i,args,_) when i = imp_id || i = and_id ->
        assert (Array.length args = 2);
        let lst1 = pres args.(0) lst c
        and lst2 = pres args.(1) [] c in
        List.fold_right
          (fun t lst -> (Term.binary imp_id args.(0) t) :: lst)
          lst2
          lst1
    | VAppl (i, args,_) when i = or_id ->
        assert (Array.length args = 2);
        let lst1  = pres args.(0) lst c
        and lst2  = pres args.(1) [] c
        and not_t = Term.unary not_id args.(0) in
        List.fold_right
          (fun t lst -> (Term.binary imp_id not_t t)::lst)
          lst2
          lst1
    | VAppl (i,args,ags) ->
        if Array.length args = 0 && arity i 0 c > 0 then
          lst
        else
          let n,nms,lst1 = preconditions i 0 c in
          assert (n = Array.length args);
          let lst = pres_args args lst in
          List.fold_left
            (fun lst t -> (Term.apply0 t args ags)::lst)
            lst
            lst1
    | Application (f,args,true) -> (* predicate application *)
        let lst = pres f lst c in
        pres_args args lst
    | Application (f,args,false) -> (* function application *)
        assert (Array.length args = 1);
        let lst = pres f lst c
        and ags =
          let f_cls,ags =
            Class_table.split_type_term (type_of_term f c) in
          assert (f_cls = function_index c);
          assert (Array.length ags = 2);
          ags
        in
        let lst = pres_args args lst
        and dom = VAppl (domain_index c,[|f|],ags) in
        Application(dom,args,true)::lst
    | Lam (n,nms,pres0,t0,pr,tp) ->
        let t0     = remove_tuple_accessors t0 n c
        and pres0  = List.map (fun p -> remove_tuple_accessors p n c) pres0
        and c      = push_lambda n nms tp c
        and imp_id = n + imp_id
        and tps =
          let cls,ags = Class_table.split_type_term tp in
          extract_from_tuple n ags.(0) c
        in
        let prepend_pres
            (ps_rev:term list) (tgt:term) (lst:term list): term list =
          let chn = Term.make_implication_chain ps_rev tgt imp_id in
          QExp (n, (nms,tps), empty_formals, chn, true) :: lst
        in
        let prepend_pres_of_term
            (ps_rev:term list) (p:term) (lst:term list)
            : term list =
          let pres_p_rev = pres p [] c in
          List.fold_left
            (fun lst p -> prepend_pres ps_rev p lst)
            lst
            (List.rev pres_p_rev)
        in
        let ps_rev,lst =
          List.fold_left
            (fun (ps_rev,lst) p ->
              p :: ps_rev,
              prepend_pres_of_term ps_rev p lst
            )
            ([],lst)
            pres0
        in
        prepend_pres_of_term ps_rev t0 lst
    | QExp (n,tps,fgs,t0,is_all) ->
        let c = push_typed tps fgs c in
        let lst0 = pres t0 [] c in
        List.fold_right
          (fun t lst ->
            QExp(n,tps,fgs,t,true) :: lst
          )
          lst0
          lst
    | Indset (nme,tp,rs) ->
        let c = push_typed ([|nme|],[|tp|]) empty_formals c in
        let lst =
          Array.fold_left
            (fun lst r ->
              let lst_r = pres r [] c in (* reversed *)
              let lst_r =
                List.rev_map
                  (fun p ->
                    try Term.down 1 p
                    with Term_capture -> assert false)
                  lst_r in
              List.rev_append lst_r lst)
            lst
            rs in
        lst
    | Flow (ctrl,args) ->
        let len = Array.length args in
        begin
          match ctrl with
            Ifexp ->
              assert (2 <= len);
              assert (len <= 3);
              let lst1 = pres args.(0) lst c
              and lst2 = pres args.(1) [] c
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
                  and lst3 = pres args.(2) [] c in
                  List.fold_right
                    (fun t lst -> (Term.binary imp_id neg t) :: lst)
                    lst3
                    reslst
              in
              reslst
          | Inspect ->
              assert (3 <= len);
              assert (len mod 2 = 1);
              let ncases = len / 2
              and nvars = count_variables c in
              let unmatched =
                Feature_table.unmatched_inspect_cases args nvars all_ntvs c.ft
              in
              let lst = List.fold_left
                  (fun lst (n,tps,pat) ->
                    let nms = standard_argnames n
                    and tps = Array.of_list tps in
                    let q = Term.pattern n (nms,tps) pat in
                    let t = Flow(Asexp,[|args.(0);q|]) in
                    let t = Term.unary not_id t in
                    t :: lst)
                  lst
                  unmatched in
              let rec cases_from (i:int) (lst:term list): term list =
                if i = ncases then
                  lst
                else
                  let n,(nms,tps),pat,res =
                    Term.case_split args.(2*i+1) args.(2*i+2) in
                  let c1 = push_typed (nms,tps) empty_formals c in
                  let lst_inner   = pres res [] c1 in
                  let lst_inner   = List.rev lst_inner in
                  let lst =
                      case_preconditions args.(0) n nms tps pat lst_inner lst 0 c in
                  cases_from (i+1) lst
              in
              cases_from 0 lst
          | Asexp ->
              assert (len = 2);
              pres args.(0) lst c
        end
  in
  List.rev_map
    (fun p -> prenex_term p c)
    (pres t [] c)

let existence_condition (posts:term list) (c:t): term =
  (* Generate the existence condition

         some(x:RT) e1_x and e2_x and ...

     where [ei_x] is the ith postcondition with the variable [Result] substituted
     by [x] and [RT] is the result type of the function.
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
    Term.subst t (2 + nargs) args
  in
  let term_inner =
    List.fold_left
      (fun inner p -> Term.binary and_id inner (replace p))
      (replace (List.hd posts))
      (List.tl posts) in
  Term.some_quantified 1 ([|ST.symbol "x"|],[|result_type c|]) term_inner



let uniqueness_condition (posts:term list) (c:t): term =
  (* Generate the uniqueness condition

         all(x,y:RT) e1_x ==> e1_y ==> ...
                     e2_x ==> e2_y ==> ... ==> x = y

     where [ei_x]/[ei_y] is the ith postcondition with the variable [Result]
     substituted by [x]/[y].
   *)
  assert (is_toplevel c);
  assert (has_result_variable c);
  assert (posts <> []);
  let nargs   = count_last_arguments c
  and nvars   = count_last_variables c
  and imp_id  = 2 + implication_index c
  and rt      = result_type c
  and tvs     = tvars c
  in
  let cls = Tvars.principal_class rt tvs in
  let eq_id  = 2 + (count_variables c)
      + Feature_table.variant Feature_table.eq_index cls c.ft
  in
  let args_var xyvar  =
    assert (xyvar < 2);
    Array.init
      (1 + nargs)
      (fun i -> if i < nargs then Variable (2+i) else Variable xyvar) in
  let argsx = args_var 0
  and argsy = args_var 1 in
  let replace_by_args t args =
    Term.subst t (3 + nargs) args
  in
  let x_eq_y =
    let eq_id_0 = 2 + nvars + Feature_table.eq_index in
    let x_eq_y_0 = VAppl (eq_id_0, [|Variable 0; Variable 1|], [|Variable 0|])
    in
    Feature_table.substituted
      x_eq_y_0  0  (2+nvars)  0  [||]  0  [|rt|] tvs c.ft
  in
  let term_inner =
    List.fold_right
      (fun t inner ->
        let t1 = Term.binary imp_id (replace_by_args t argsy) inner in
        Term.binary imp_id (replace_by_args t argsx) t1
      )
      posts
      x_eq_y
      (*(VAppl (eq_id,[|Variable 0; Variable 1|], [|rt|]))*)
  and nms = [|ST.symbol "x"; ST.symbol "y"|]
  and tps = [|rt; rt|]
  in
  Term.all_quantified 2 (nms,tps) empty_formals term_inner





let function_postconditions (idx:int) (posts:term list) (c:t): term list =
  (* Generate the postconditions

     [e1_f; e2_f; ...]

     where [ei_f] is [ei] with the variable [Result] substituted by [f(a,b,...)] and
     [idx] is the index of the function [f].
   *)
  assert (has_result_variable c);
  assert (posts <> []);
  let tvs   = Feature_table.tvars idx c.ft
  and nargs = count_last_arguments c
  in
  let fargs = Array.init nargs (fun i -> Variable i)
  and ags   = Array.init (Tvars.count_fgs tvs) (fun i -> Variable i)
  in
  let fterm = VAppl (1+nargs+idx, fargs, ags) in
  let args  =
    Array.init (1+nargs) (fun i -> if i < nargs then Variable i else fterm) in
  let replace t = Term.subst t (1+nargs) args in
  List.map replace posts


let get_type (tp:type_t withinfo) (c:t): type_term =
  let tvs = tvars c in
  Class_table.get_type tp tvs (class_table c)

let string_of_type (tp:type_term) (c:t): string =
  Class_table.string_of_type tp (tvars c) (class_table c)


let string_of_type_array (sep:string) (arr: type_term array) (c:t): string =
  String.concat
    sep
    (List.map (fun tp -> string_of_type tp c) (Array.to_list arr))


let downgrade_term (t:term) (nb:int) (c:t): term =
  Feature_table.downgrade_term t (nb + count_variables c) c.ft


let arity_of_downgraded_type (tp:type_term) (c:t): int =
  let ntvs = TVars_sub.count_all c.entry.tvs_sub in
  Class_table.arity_of_downgraded ntvs tp

let specialized (t:term) (c:t): term =
  let nvars = count_variables c
  and tvs   = tvars c in
  Feature_table.specialized t nvars tvs c.ft
