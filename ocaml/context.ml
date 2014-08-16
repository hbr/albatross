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


type proof_term = Proof_context.proof_term

type t = {
    mutable entry: entry;
    mutable stack: entry list;
    mutable trace: bool;
    ft:            Feature_table.t;
    pc:            Proof_context.t
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


let has_current_module (c:t): bool =
  Feature_table.has_current_module c.ft

let current_module (c:t): int =
  Feature_table.current_module c.ft

let count_modules (c:t): int =
  Feature_table.count_modules c.ft

let find_module (name:int) (lib:int list) (c:t): int =
  Feature_table.find_module name lib c.ft



let add_module
    (name:int) (lib:int list) (mode:int) (used:IntSet.t) (c:t): unit =
  Feature_table.add_module name lib mode used c.ft

let used_modules (mdl:int) (c:t): IntSet.t =
  Feature_table.used_modules mdl c.ft

let is_interface_use (c:t): bool = Feature_table.is_interface_use c.ft


let is_global (c:t): bool =
  c.stack = []


let is_toplevel (c:t): bool =
  match c.stack with
    [_] -> true
  | _   -> false


let entry_nfargs (e:entry): int = Array.length e.fargs

let entry_arity (e:entry): int = e.nfargs_delta

let arity     (c:t): int = entry_arity c.entry


let has_result (c:t): bool = Result_type.has_result c.entry.result

let result_type (c:t): type_term =
  (** The result type of the context
   *)
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


let count_last_arguments (c:t): int = c.entry.nfargs_delta

let count_arguments (c:t): int = Array.length c.entry.fargs

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


(*
let formal_generics (c:t): formal array =
  (** The cumulated formal generics of this context and all
      previous contexts
   *)
  c.entry.fgs
*)
let concepts (c:t): type_term array = TVars_sub.fgconcepts c.entry.tvs_sub



let entry_fargnames (e:entry): int array =
  Array.init e.nfargs_delta (fun i -> fst e.fargs.(i))



let last_fargs (c:t): int array =
  (** The argument names of the last push *)
  assert false
  (*Array.sub c.entry.fargs 0 (arity c)*)


let last_fargnames (c:t): int array =
  let n = arity c in
  Array.init n (fun i -> fst c.entry.fargs.(i))


let local_fargnames (c:t): int array = entry_fargnames c.entry




let entry_fargnames (e:entry): int array =
  Array.map (fun (n,_) -> n) e.fargs


let fargnames (c:t): int array = entry_fargnames c.entry


let entry_fgnames (e:entry): int array = TVars_sub.fgnames e.tvs_sub

let fgnames (c:t): int array = entry_fgnames c.entry

let tvs (c:t): Tvars.t = TVars_sub.tvars c.entry.tvs_sub

let string_of_term (t:term) (c:t): string =
  Feature_table.term_to_string t (fargnames c) c.ft



let sign2string (s:Sign.t) (c:t): string =
  Class_table.string_of_signature
    s
    (tvs c)
    (class_table c)





let entry_signature (e:entry) (c:t): Sign.t =
  (** The signature of the entry [e] in the context [c].  *)
  let argtypes = Array.init (entry_nfargs e) (fun i -> snd e.fargs.(i)) in
  Sign.make argtypes e.result




let signature (c:t): Sign.t =
  (** The signature of the context [c].  *)
  entry_signature c.entry c


let signature_string (c:t): string =
  (** Print the signature of the context [c].  *)
  sign2string (signature c) c


let depth (c:t): int =
  List.length c.stack


let is_untyped (i:int) (c:t): bool =
  (* Is the argument [i] untyped? *)
  assert (i < nfargs c);
  let tp = snd c.entry.fargs.(i) in
  match tp with
    Variable j when j < count_type_variables c -> true
  | _ -> false



let argument (name:int) (c:t): int * Tvars.t * Sign.t =
  (** The term and the signature of the argument named [name] *)
  let i = Search.array_find_min (fun (n,_) -> n=name) c.entry.fargs in
  let sign = Sign.make_const (snd c.entry.fargs.(i)) in
  i,
  TVars_sub.tvars c.entry.tvs_sub,
  sign



let read_trace_info (c:t): unit =
  c.trace <- Options.is_tracing_proof () && Options.trace_level () > 0

let make (): t =
  {entry = empty_entry;
   stack = [];
   trace =  Options.is_tracing_proof () && Options.trace_level () > 0;
   ft        = Feature_table.base_table ();
   pc        =
   Proof_context.make
     Feature_table.implication_index
     Feature_table.all_index
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
    (ntvs_gap)
    (c: t)
    : unit =
  (** Push the new type variables, formal generics and the formal arguments of
      [entlst,rt] to the context [c] leaving a gap of [ntvs_gap] above the
      possibly newly introduced type variables of the signature. *)
  let entry      = c.entry
  and ct         = class_table c in
  let tvs_sub  =
    Class_table.formal_generics entlst rt ntvs_gap entry.tvs_sub ct in
  let tvs = TVars_sub.tvars tvs_sub
  in
  let ntvs0 = TVars_sub.count_local entry.tvs_sub
  and nfgs0 = TVars_sub.count_fgs entry.tvs_sub
  in
  let ntvs1 = Tvars.count_local tvs - ntvs0
  and nfgs1 = Tvars.count_fgs tvs   - nfgs0
  in
  let res        = Class_table.result_type rt tvs ct in
  let fargs1     = Class_table.formal_arguments entlst tvs ct
  in
  let fargs      =
    Array.append
      fargs1
      (Array.map
         (fun (n,t) -> n, Term.up ntvs1 (Term.upbound nfgs1 ntvs0 t))
         entry.fargs)
  in
  c.entry <-
    {tvs_sub    = tvs_sub;
     fargs        = fargs;
     ntvs_delta   = ntvs1;
     nfgs_delta   = nfgs1;
     nfargs_delta = Array.length fargs1;
     result       = res;
     info         = entlst.i};
  c.stack <- entry::c.stack;

  assert (not (Proof_context.has_work c.pc));
  Proof_context.push (arity c) (last_fargnames c) c.pc




let push
    (entlst: entities list withinfo)
    (rt: return_type)
    (c: t)
    : unit =
  (** Push the new type variables, formal generics and the formal arguments of
      [entlst,rt] to the context [c]. *)
  push_with_gap entlst rt 0 c




let push_untyped (names:int array) (c:t): unit =
  let entlst = withinfo UNKNOWN [Untyped_entities (Array.to_list names)] in
  push entlst None c



let push_empty (c:t): unit =
  push_untyped [||] c


let pop (c:t): unit =
  (** Pop the last context
   *)
  assert (not (is_global c));
  c.entry <- List.hd c.stack;
  c.stack <- List.tl c.stack;
  Proof_context.pop c.pc





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
  let nargs = entry_arity e in (*Sign.arity e.signature in*)
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




let put_global_function
    (fn:       feature_name withinfo)
    (impstat:  Feature_table.implementation_status)
    (term_opt: term option)
    (c:      t)
    : unit =
  assert (is_toplevel c);
  Feature_table.put_function
    fn
    (TVars_sub.tvars c.entry.tvs_sub)
    (fargnames c)
    (signature c)
    impstat
    term_opt
    c.ft


let implication_id (c:t): int =
  Feature_table.implication_index + (nfargs c)


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



let inherit_parent_assertions
    (cls_idx:int)
    (par_idx:int)
    (par_args:type_term array)
    (info:info)
    (c:t)
    : unit =
  ()

let put_class
    (hm:       header_mark withinfo)
    (cn:       int withinfo)
    (fgs:      formal_generics)
    (inherits: inherit_clause list)
    (c:t)
    : unit =
  (** Analyze the class declaration [hm,cn,fgs,inherits] and add or update the
      corresponding class.  *)
  assert (is_global c);
  let ct = class_table c
  and ft = feature_table c in
  let idx =
    try
      let idx = Class_table.find cn.v ct in
      Class_table.update idx hm fgs  ct;
      idx
    with Not_found ->
      let idx = Class_table.count ct in
      Class_table.add hm cn fgs ct;
      idx
  in
  List.iter
    (fun par_lst ->
      List.iter
        (fun (tp,adapt_lst) ->
          assert (adapt_lst = [] ); (* nyi: feature adaption *)
          let par_idx, par_args = Class_table.parent_type idx tp ct in
          let lst = Class_table.inherited_ancestors idx par_idx par_args tp.i ct in
          Class_table.do_inherit idx lst ct;

          Feature_table.do_inherit idx lst tp.i ft;
          inherit_parent_assertions idx par_idx par_args tp.i c)
        par_lst)
    inherits




let find_funcs
    (fn:feature_name)
    (nargs:int)
    (c:t)
    : (int*Tvars.t*Sign.t) list =
  (** Find all the functions with name [fn] and [nargs] arguments in the
      global feature table and transform them into the context.
   *)
  let lst = Feature_table.find_funcs fn nargs c.ft
  and nfgs = count_formal_generics c
  in
  let lst = List.rev_map
      (fun (i,tvs,s) ->
        (* make space for formal generics *)
        let start = Tvars.count tvs in
        assert (Tvars.count_local tvs = 0);
        let sign = Sign.up_from nfgs start s in
        i+(nfargs c), tvs, sign)
      lst
  in
  lst

exception Wrong_signature

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
      let i,tvs,s = argument name c
      in
      if (Sign.arity s) = nargs_id || is_untyped i c then
        [i,tvs,s]
      else
        try
          let s = Class_table.downgrade_signature (ntvs c) s nargs_id in
          [i,tvs,s]
        with Not_found ->
          raise Wrong_signature
    with
      Not_found ->
        find_funcs
          (FNname name) nargs_id c
    | Wrong_signature ->
        raise Not_found



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




let assertion (i:int) (c:t): term =
  Proof_context.term i c.pc


let print_assertions
    (prefix:string)
    (e:entry)
    (c0:int)
    (c1:int)
    (global:bool)
    (c:t): unit =
  let argsstr = arguments_string e (class_table c) in
  if argsstr <> "" then
    printf "%s%s\n" prefix argsstr;
  let rec print (i:int): unit =
    if i = c1 then ()
    else begin
      let t,nbenv = Proof_context.term_orig i c.pc
      and is_hypo = Proof_context.is_assumption i c.pc
      and is_used = Proof_context.is_used_forward i c.pc
      and used_gen = Proof_context.used_schematic i c.pc
      in
      assert (nbenv = Array.length e.fargs);
      let tstr = Feature_table.term_to_string t (entry_fargnames e) c.ft
      and used_gen_str =
        if IntSet.is_empty used_gen then ""
        else " " ^ (intset_to_string used_gen)
      in
      if c.trace || not is_used then
        printf "%s%3d   %s%s%s%s\n"
          prefix
          i
          (if global || is_hypo then "" else ". ")
          tstr
          used_gen_str
          (if is_used then " <used>" else "");
      print (i+1)
    end
  in
  print c0


let print_local_contexts (c:t): unit =
  let ct = class_table c in
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
  printf "%s\n" (args_str c.entry)

let print_global_assertions (c:t): unit =
  let cnt = Proof_context.count_global c.pc
  and e   =
    if c.stack = [] then c.entry
    else
      let rec get_e0 (lst: entry list): entry =
        match lst with
          []    -> assert false
        | [e]   -> e
        | _::lst -> get_e0 lst
      in
      get_e0 c.stack
  in
  print_assertions "" e 0 cnt true c



let print_all_local_assertions (c:t): unit =
  let rec print (elst: entry list) (clst: int list): string =
      match elst, clst with
        [], []
      | [_], [_] -> ""
      | e1::e0::elst, c1::c0::clst ->
          let prefix = print (e0::elst) (c0::clst) in
          print_assertions prefix e1 c0 c1 false c;
          "  " ^ prefix
      | _, _ -> assert false (* shall never happen, elst and clst must have
                                equal length *)
  in
  let clst = Proof_context.stacked_counts c.pc
  in
  let prefix = print c.stack clst in
  print_assertions
    prefix
    c.entry
    (Proof_context.count_previous c.pc)
    (Proof_context.count          c.pc)
    false
    c


let count_assertions (c:t): int =
  Proof_context.count c.pc

let find_assertion (t:term) (c:t): int =
  Proof_context.find t c.pc

let has_assertion (t:term) (c:t): bool =
  Proof_context.has t c.pc

let split_implication (t:term) (c:t): term * term =
  Proof_context.split_implication t c.pc

let split_all_quantified (t:term) (c:t): int * int array * term =
  Proof_context.split_all_quantified t c.pc

let all_quantified_outer (t:term) (c:t): term =
  Proof_context.all_quantified_outer t c.pc

let implication_chain (ps:term list) (tgt:term) (c:t): term =
  Proof_context.implication_chain ps tgt c.pc

let expanded_term (t:term) (c:t): term =
  let nbenv = nfargs c in
  Feature_table.expand_term t nbenv c.ft

let prefix (c:t): string =
  String.make (2*(depth c)+2) ' '

let close (c:t): unit =
  let rec print (c0:int) (c1:int): unit =
    assert (c0 <= c1);
    if c0 = c1 then ()
    else begin
      printf "%s%3d >       %s\n"
        (prefix c) c0 (string_of_term (assertion c0 c) c);
      print (c0+1) c1
    end
  in
  let rec cls (n:int): unit =
    if Proof_context.has_work c.pc then begin
      (*assert (n < 50);*)
      let cnt = count_assertions c in
      Proof_context.close_step c.pc;
      if c.trace then print cnt (count_assertions c);
      cls (n+1)
    end else
      ()
  in
  cls 0;
  assert (not (Proof_context.has_work c.pc))

let add_assumption (t:term) (c:t): int =
  let res = Proof_context.add_assumption t c.pc
  in
  if c.trace then
    printf "%s%3d hypo:   %s\n" (prefix c) res (string_of_term t c);
  close c;
  res

let add_axiom (t:term) (c:t): int =
  let res = Proof_context.add_axiom t c.pc in
  if c.trace then
    printf "%s%3d axiom:  %s\n" (prefix c) res (string_of_term t c);
  close c;
  res


let discharged (i:int) (c:t): term * proof_term =
  Proof_context.discharged i c.pc


let add_proved (t:term) (pterm:proof_term) (used_gen:IntSet.t) (c:t): unit =
  Proof_context.add_proved t pterm used_gen c.pc;
  if c.trace then begin
    let idx = find_assertion t c in
    printf "%s%3d proved: %s\n" (prefix c) idx (string_of_term t c)
  end;
  close c


let add_backward (t:term) (c:t): unit =
  Proof_context.set_forward c.pc;
  Proof_context.add_backward t c.pc;
  close c


let backward_set (t:term) (c:t): int list =
  Proof_context.backward_set t c.pc

let backward_data (idx:int) (c:t): term list * IntSet.t =
  Proof_context.backward_data idx c.pc


let print (c:t): unit =
  assert (is_global c);
  Class_table.print   (class_table c);
  Feature_table.print c.ft;
  print_global_assertions c
