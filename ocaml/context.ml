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
    nfargs_delta: int;
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
   nfargs_delta = 0;
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

let entry_nfargs (e:entry): int = Array.length e.fargs

let entry_arity (e:entry): int = e.nfargs_delta

let arity     (c:t): int = entry_arity c.entry

let verbosity (c:t): int = c.verbosity

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


let count_last_arguments (c:t): int = c.entry.nfargs_delta

let count_arguments (c:t): int = Array.length c.entry.fargs


let all_index (c:t): int =
  count_arguments c + Feature_table.all_index

let some_index (c:t): int =
  count_arguments c + Feature_table.some_index

let implication_index (c:t): int =
  count_arguments c + Feature_table.implication_index

let and_index (c:t): int =
  count_arguments c + Feature_table.and_index

let or_index (c:t): int =
  count_arguments c + Feature_table.or_index


let argument_name (i:int) (c:t): int =
  assert (i < count_arguments c);
  fst c.entry.fargs.(i)


let argument_type (i:int) (c:t): type_term =
  assert (i < count_arguments c);
  snd c.entry.fargs.(i)


let nfargs (c:t): int =
  (** The cumulated number of formal arguments in this context and all
      previous contexts
   *)
  entry_nfargs c.entry


let ntvs (c:t): int =
  (** The cumulated number of formal generics and type variables in
      this context and all previous contexts
   *)
  (count_formal_generics c) + (count_type_variables c)



let entry_local_argnames (e:entry): int array =
  Array.init e.nfargs_delta (fun i -> fst e.fargs.(i))


let local_argnames (c:t): int array = entry_local_argnames c.entry


let entry_argnames (e:entry): int array =
  Array.map (fun (n,_) -> n) e.fargs


let argnames (c:t): int array = entry_argnames c.entry

let outer_argnames (c:t): int array =
  assert (not (is_global c));
  entry_argnames ((previous c).entry)


let entry_fgnames (e:entry): int array = TVars_sub.fgnames e.tvs_sub

let fgnames (c:t): int array = entry_fgnames c.entry

let tvs (c:t): Tvars.t = TVars_sub.tvars c.entry.tvs_sub

let sign2string (s:Sign.t) (c:t): string =
  Class_table.string_of_signature
    s
    (tvs c)
    (class_table c)


let string_of_term (t:term) (nanon:int) (c:t): string =
  Feature_table.term_to_string t nanon (argnames c) c.ft

let string_of_term_outer (t:term) (nanon:int) (c:t): string =
  Feature_table.term_to_string t
    nanon
    (outer_argnames c)
    c.ft


let untupelize_inner (t:term) (nargs:int) (c:t): term =
  let nbenv = count_arguments c in
  Feature_table.untupelize_inner t nargs nbenv c.ft

let tupelize_inner (t:term) (nargs:int) (c:t): term =
  let nbenv = count_arguments c in
  let res = Feature_table.tupelize_inner t nargs nbenv c.ft in
  assert (t = untupelize_inner res nargs c);
  res

let quantified (is_all:bool) (nargs:int) (nms:int array) (t:term) (c:t): term =
  let _ = tupelize_inner t nargs c in
  let q_id = if is_all then all_index c else some_index c in
  Term.quantified q_id nargs nms t

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


let argument_index (nme:int) (c:t): int =
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
  Feature_table.split_equality t (nb + count_arguments c) c.ft

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
  (* Is the argument [i] untyped? *)
  assert (i < nfargs c);
  let tp = snd c.entry.fargs.(i) in
  match tp with
    Variable j when j < count_type_variables c -> true
  | _ -> false



let argument_data (i:int) (c:t): Tvars.t * Sign.t =
  assert (i < count_arguments c);
  TVars_sub.tvars c.entry.tvs_sub,
  Sign.make_const (snd c.entry.fargs.(i))


let argument (name:int) (c:t): int * Tvars.t * Sign.t =
  (** The term and the signature of the argument named [name] *)
  let i = argument_index name c in
  let tvs,s = argument_data i c in
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
    (ntvs_gap)
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
  let fargs1, n_untyped = Class_table.formal_arguments entlst tvs ct in
  let res  = Class_table.result_type rt is_pred is_func n_untyped tvs ct
  in
  let fargs      =
    Array.append
      fargs1
      (Array.map
         (fun (n,t) -> n, Term.up ntvs1 (Term.upbound nfgs1 ntvs0 t))
         entry.fargs)
  in
  {c with
   entry =
   {tvs_sub    = tvs_sub;
    fargs        = fargs;
    ntvs_delta   = ntvs1;
    nfgs_delta   = nfgs1;
    nfargs_delta = Array.length fargs1;
    result       = res;
    info         = entlst.i};
   prev  = Some c;
   depth = 1 + c.depth}




let push
    (entlst: entities list withinfo)
    (rt: return_type)
    (is_pred: bool)
    (is_func: bool)
    (c: t)
    : t =
  (** Push the new type variables, formal generics and the formal arguments of
      [entlst,rt] to the context [c]. *)
  push_with_gap entlst rt is_pred is_func 0 c




let push_untyped_with_gap
    (names:int array) (is_func:bool) (ntvs_gap:int) (c:t): t =
  let entlst = withinfo UNKNOWN [Untyped_entities (Array.to_list names)] in
  push_with_gap entlst None (not is_func) is_func ntvs_gap c


let push_untyped (names:int array) (c:t): t =
  let entlst = withinfo UNKNOWN [Untyped_entities (Array.to_list names)] in
  push entlst None true false c



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
  ^ (string_of_term t 0 c)


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
      (fun (i,tvs,s) -> i+(nfargs c), tvs, s)
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
      [argument name c]
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



let variable_data (i:int) (c:t): Tvars.t * Sign.t =
  let nfargs = count_arguments c in
  if i < nfargs then
    argument_data i c
  else
    let idx = i - nfargs in
    let tvs,s = Feature_table.signature idx (feature_table c) in
    Tvars.fgs_to_global tvs, s



let print_local_contexts (c:t): unit =
  assert false
  (*let ct = class_table c in
  let args_str (e:entry): string =
    let str = arguments_string e ct in
    if str = "" then "<empty>" else str
  in
  let rec print_stack (stack: entry list): unit =
    match stack with
      []
    | [_] ->
        ()
    | e::tail ->
        print_stack tail;
        printf "%s\n" (args_str e)
  in
  printf "local contexts\n";
  print_stack c.stack;
  printf "%s\n" (args_str c.entry)*)


let expanded_term (t:term) (nb:int) (c:t): term =
  let nbenv = nfargs c in
  Feature_table.expand_term t (nb+nbenv) c.ft



let to_tuple (args:term array) (nb:int) (c:t): term =
  let tup_id = nb + count_arguments c + Feature_table.tuple_index in
  let n = Array.length args in
  assert (1 < n);
  let rec to_tup i t =
    if i = 0 then
      t
    else
      let i = i - 1 in
      let t = Application(Variable tup_id, [|args.(i);t|],false) in
      to_tup i t
  in
  to_tup (n-1) args.(n-1)


let adapt_arguments (n:int) (args:term array) (nb:int) (c:t): term array =
  let n2 = Array.length args in
  assert (0 < n);
  assert (0 < n2);
  assert (n = n2 || n = 1 || n2 = 1);
  if n = 1 && n2 > 1 then
    [|to_tuple args nb c|]
  else if n2 = 1 && n > 1 then
    assert false (* nyi: providing a tuple to a multiargument function *)
  else
    args




let definition (idx:int) (nb:int) (c:t): term =
  let nbenv = count_arguments c in
  if idx < nb + nbenv then
    raise Not_found
  else begin
    Feature_table.definition idx (nb + nbenv) (feature_table c)
  end


let expanded_definition (idx:int) (nb:int) (c:t): term =
  let nbenv = count_arguments c in
  if idx < nb + nbenv then
    raise Not_found
  else begin
    Feature_table.expanded_definition idx (nb + nbenv) (feature_table c)
  end


let preconditions (idx:int) (nb:int) (c:t): int * int array * term list =
  let nbenv = count_arguments c in
  if idx < nb + nbenv then
    0, [||], []
  else
    Feature_table.preconditions idx (nb+nbenv) (feature_table c)


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

       f(x,y,...):
                  pf0, pf1, ...
                  px0,...,py0,...,...
                  (x,y,...).(f.domain)
 *)
(*
  (x -> y -> exp) (x) ~> (y -> exp)
 *)
let specification i c = assert false

let term_preconditions (t:term)  (c:t): term list =
  let rec pres (t:term) (lst:term list) (c:t): term list * Feature.Spec.t =
    let all_id = all_index c
    and some_id = some_index c
    and imp_id  = implication_index c
    and and_id  = and_index c
    and or_id   = or_index c in
    let do_pred n nms t =
      let c = push_untyped nms c in
      let ps,_ = pres t [] c in
      List.fold_right
        (fun p lst -> (Term.quantified all_id n nms p)::lst)
        ps
        lst in
   match t with
    | Variable i ->
        lst,
        specification i c
    | Application (Variable i, args, pr) when i = imp_id || i = and_id ->
        assert false
    | Application (Variable i, args, pr) when i = or_id ->
        assert false
    | Application (Variable i, args, pr) when i = all_id || i = some_id ->
        assert (Array.length args = 1);
        begin try
          let n,nms,t0 = Term.lambda_split args.(0) in
          let lst = do_pred n nms t0 in
          lst, assert false
        with Not_found ->
          assert false (* cannot happen *)
        end
    | Application (f,args,pr) ->
        let lst,fspec = pres f lst c in
        assert (Array.length args = Feature.Spec.count_arguments fspec);
        begin try
          let def = Feature.Spec.definition_term fspec in
          let exp = Term.apply def args in
          pres exp lst c
        with Not_found ->
          let lst = Array.fold_left
              (fun lst arg ->
                let lst,_ = pres arg lst c in lst)
              lst
              args in
          let lst = List.fold_left
              (fun lst pre -> assert false)
              lst
              (Feature.Spec.preconditions fspec)
          in
          lst, assert false
        end
    | Lam (n,nms,t0,pr) when pr ->
        let lst = do_pred n nms t0 in
        lst, assert false (* nyi *)
    | Lam (n,nms,t0,pr) ->
        lst,
        Feature.Spec.make_func_def nms (Some t0)
    | QLam (n,nms,t0) ->
        assert false (* nyi *)
  in
  let ps,_ = pres t [] c in
  ps
