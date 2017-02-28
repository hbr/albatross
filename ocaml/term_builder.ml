(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Support
open Term
open Container
open Signature
open Printf

(*

  context:          locs                     + fgs
  builder:    space locs + globs space + space fgs

The builder has enough space to accomodate all untyped variables and formal
generics of the inner contexts and all global type variables imported from
global generic functions, needed for arguments of lambda expressions, needed
to represent arguments, return type, function/predicate type of term
applications.

Global type variables are introduced

- as placeholders for formal generics of used global functions

- as anchors for untyped variables in lambda expressions (arguments in lambda
  expressions have to satisfy ANY, therefore untyped variables are linked to
  global type variables with concept ANY).

- as placeholders for arguments, for the result type and for the
  function/predicate type of a term application (note: in all term
  applications we don't know the types of the arguments, only that they have
  to satisfy the concept of ANY; we might not know if the term is a predicate
  or a function and we might not know the result type).


Each type variable has a possible substitution. Substitutions are immutable.

Each type variable points to its substitution which can be another type
variable or a definitive type. Pointer chains of type variables are
possible. Cycles of pointers are not allowed.

If a type variable points to another type variable then the concept of the
other type variable is stronger than the concept of the original type
variable.



*)
type application =
    GlFun of int*Sign.t*bool*int*int*int*bool
                        (* is_const, nargs, start fgs, nfgs, is_pred *)
  | TermApp of int * int (* nargs, start fgs *)

type t = {
    mutable req:       type_term option;
    mutable reqs:      type_term list;
    mutable terms:     (term*type_term) list;
    mutable calls:     application list;
    mutable contexts:  Context.t list;
    mutable nlocals:   int;
    mutable nglobals:  int;
    mutable nfgs:      int;
    mutable tvs:       Tvars.t;
    mutable sub:       type_term array;
    mutable feature_fg_ranges: (int*int*int) list (* fidx (absolut), start, nfgs *)
  }

let oo_from_am (am:application_mode): bool =
  match am with
    AMoo -> true
  | _ -> false

let globals_start (tb:t): int =
  Tvars.count_local tb.tvs

let globals_beyond (tb:t): int =
  globals_start tb + tb.nglobals

let locals_start (tb:t): int =
  globals_start tb - tb.nlocals

let count_all (tb:t): int =
  Tvars.count_all tb.tvs

let fgs_start (tb:t): int =
  count_all tb - tb.nfgs

let local_capacity (tb:t): int =
  Tvars.count_local tb.tvs

let global_capacity (tb:t): int =
  Tvars.count_global tb.tvs

let fg_capacity (tb:t): int =
  Tvars.count_fgs tb.tvs

let is_tv (i:int) (tb:t): bool =
  let gstart = globals_start tb in
  gstart - tb.nlocals <= i  &&  i < gstart + tb.nglobals

let is_local (i:int) (tb:t): bool =
  let gstart  = globals_start tb in
  gstart - tb.nlocals <= i && i < gstart


let concept (i:int) (tb:t): type_term =
  assert begin
    (globals_start tb <= i && i < globals_beyond tb) ||
    (fgs_start tb <= i && i < count_all tb)
  end;
  Tvars.concept i tb.tvs

let transform0
    (start:int) (space1:int) (space2:int) (tp:type_term): type_term =
  (* Starting from [start] shift all [space1] up and then shift all by
     [space2] up.*)
  let tp = Term.up_from space1 start tp in
  Term.up space2 tp

let transform_from_global
    (tvs:Tvars.t) (tb:t)
    : type_term -> type_term
        =
      assert (Tvars.count tvs = 0); (* no locals and no globals *)
      let nfgs0  = Tvars.count_fgs tvs in
      let gstart = globals_beyond tb
      and nall = Tvars.count_all tb.tvs
      in
      transform0 nfgs0 (nall-gstart-nfgs0) gstart


let transform_from_context (c:Context.t) (tb:t): type_term -> type_term
    =
  let tvs = Context.tvars c in
  assert (Tvars.count_global tvs = 0); (* no globals in a context *)
  assert (Tvars.count_local tvs = tb.nlocals);
  assert (Tvars.count_fgs tvs = tb.nfgs);
  let space1 = global_capacity tb + fg_capacity tb - tb.nfgs
  and space2 = local_capacity tb - tb.nlocals
  and start = Tvars.count_local tvs in
  transform0 start space1 space2



let one_substituted_type (tp:type_term) (tb:t): type_term =
  Term.subst tp (Array.length tb.sub) tb.sub


let substituted_type (tp:type_term) (tb:t): type_term =
  let len = Array.length tb.sub
  in
  let one_sub tp = one_substituted_type tp tb
  in
  let rec sub tp n =
    if n = 0 then
      assert false (* infinite loop *)
    else
      let tp_new = one_sub tp in
      if Term.equivalent tp_new tp then
        tp
      else
        sub tp_new (n-1)
  in
  sub tp (len+1) (* if we have 1 type variable the first substitution can return
                    a different type but the second substitution must have no
                    effect *)


let context (tb:t): Context.t =
  assert (tb.contexts <> []);
  List.hd tb.contexts

let feature_table (tb:t): Feature_table.t =
  assert (tb.contexts <> []);
  Context.feature_table (context tb)

let class_table (tb:t): Class_table.t =
  assert (tb.contexts <> []);
  Context.class_table (context tb)

let count_variables (tb:t): int =
  Context.count_variables (context tb)

let in_index (tb:t): int =
  count_variables tb + Constants.in_index

let any_index       (tb:t): int = count_all tb + Class_table.any_index
let boolean_index   (tb:t): int = count_all tb + Class_table.boolean_index
let predicate_index (tb:t): int = count_all tb + Class_table.predicate_index
let function_index  (tb:t): int = count_all tb + Class_table.function_index

let any_type     (tb:t): type_term = Variable (any_index tb)
let boolean_type (tb:t): type_term = Variable (boolean_index tb)

let string_of_term (t:term) (tb:t): string =
  let c = context tb in
  let ft = Context.feature_table c
  and names = Context.varnames c
  in
  Feature_table.term_to_string t true true 0 names tb.tvs ft


let string_of_type (tp:type_term) (tb:t): string =
  let ct = Context.class_table (context tb) in
  Class_table.string_of_type tp tb.tvs ct


let string_of_substituted_type (tp:type_term) (tb:t): string =
  let tp = substituted_type tp tb in
  string_of_type tp tb


let has_required_type (tb:t): bool =
  Option.has tb.req


let push_required (tp:type_term) (tb:t): unit =
  tb.reqs <- tp :: tb.reqs


let used_type_variables (tp:type_term) (tb:t): int array =
  let used = Term.used_variables tp (globals_beyond tb) in
  let used = Array.of_list used in
  Array.sort Pervasives.compare used;
  used



let string_of_substituted_type_with_tvs
    (tp:type_term) (tb:t): string =
  let tp = substituted_type tp tb in
  let tpstr = string_of_type tp tb in
  let used = used_type_variables tp tb in
  if Array.length used = 0 then
    tpstr
  else
    let gstart = globals_start tb in
    let used =
      Array.map
        (fun ivar ->
          let tpstr = string_of_type (Variable ivar) tb in
          if ivar < gstart then
            tpstr
          else
            let cstr = string_of_type (concept ivar tb) tb in
            tpstr ^ ":" ^ cstr
        )
        used
    in
    let tvstr = String.concat "," (Array.to_list used) in
    "[" ^ tvstr ^ "] " ^ tpstr



let string_of_required_type (tb:t): string =
  assert (has_required_type tb);
  string_of_substituted_type_with_tvs (Option.value tb.req) tb



let string_of_tvs (tb:t): string =
  let lstart  = locals_start tb
  and gstart  = globals_start tb
  and fgstart = fgs_start tb in
  let _,str =
    interval_fold
      (fun (has,str) i ->
        if lstart <= i && i < gstart then
          let s = (string_of_int i) ^ ":_" in
          true, str ^ (if has then "," else "") ^ s
        else if gstart <= i && i < gstart + tb.nglobals then
          let s = (string_of_int i) ^ ":"
            ^ (string_of_type (Tvars.concept i tb.tvs) tb) in
          true, str ^ (if has then "," else "") ^ s
        else if fgstart <= i then
          let s = (ST.string (Tvars.name i tb.tvs)) ^ ":"
            ^ (string_of_type (Tvars.concept i tb.tvs) tb) in
          true, str ^ (if has then "," else "") ^ s
        else
          has,str)
      (false,"")
      0 (Tvars.count_all tb.tvs)
  in
  if str = "" then str else "[" ^ str ^"]"


let string_of_substitutions (tb:t): string =
  let lst =
    interval_fold
      (fun lst i ->
        let tp = tb.sub.(i) in
        if tp = Variable i then
          lst
        else
          (i,tp) :: lst
      )
      [] (locals_start tb) (globals_beyond tb)
  in
  if lst = [] then ""
  else
    "[" ^ (String.concat ","
             (List.map
                (fun (i,t) -> (string_of_int i) ^ ":=" ^ (string_of_type t tb))
                (List.rev lst))) ^ "]"



let count_terms (tb:t): int =
  List.length tb.terms

let head_term (tb:t): term =
  assert (tb.terms <> []);
  let t,_ = List.hd tb.terms in
  t

let head_type (tb:t): type_term =
  assert (tb.terms <> []);
  let _,tp = List.hd tb.terms in
  tp


let result_type_of_type (tp:type_term) (tb:t): type_term =
  let cls,ags = Class_table.split_type_term tp in
  if cls = predicate_index tb then
    boolean_type tb
  else if cls = function_index tb  then
    begin
      assert (Array.length ags = 2);
      ags.(1)
    end
  else
    assert false (* cannot happen *)


let string_of_head_term(tb:t): string =
  assert (tb.terms <> []);
  let t = head_term tb in
  string_of_term t tb


let string_of_complete_head_term (tb:t): string =
  assert (tb.terms <> []);
  let t,tp = List.hd tb.terms in
  let tstr = string_of_term t tb
  and tpstr = string_of_substituted_type_with_tvs tp tb in
  tstr ^ " : " ^  tpstr


let copy (tb:t): t =
  {req = tb.req;
   reqs = tb.reqs;
   terms = tb.terms;
   calls = tb.calls;
   contexts  = tb.contexts;
   nlocals = tb.nlocals;
   nglobals = tb.nglobals;
   nfgs = tb.nfgs;
   tvs = Tvars.copy tb.tvs;
   sub = Array.copy tb.sub;
   feature_fg_ranges = tb.feature_fg_ranges}


let has_substitution (i:int) (tb:t): bool =
  assert (is_tv i tb);
  tb.sub.(i) <> Variable i



let satisfies (t1:type_term) (t2:type_term) (tb:t): bool =
  (*printf "satisfies\n";
  printf " %s %s\n" (string_of_tvs tb) (string_of_substitutions tb);
  printf " tp1:  %s,   %s\n"
    (string_of_type t1 tb)
    (string_of_substituted_type_with_tvs t1 tb);
  printf " tp2:  %s,   %s\n"
    (string_of_type t2 tb)
    (string_of_substituted_type_with_tvs t2 tb);*)
  Class_table.satisfies t1 tb.tvs t2 tb.tvs (class_table tb)


let can_reach (tp:type_term) (i:int) (tb:t): bool =
  (* Can the type term [tp] reach the type variable [i] by substitutions? *)
  let ntvs = Array.length tb.sub in
  let rec can tp n =
    assert (n <= ntvs + 1); (* infinite loop protection *)
    if tp = Variable i then
      true
    else
      match tp with
        Variable j when is_tv j tb && has_substitution j tb ->
          can tb.sub.(j) (n+1)
      | _ ->
          false
  in
  can tp 0


let substitute (i:int) (tp:type_term) (tb:t): unit =
  assert (is_tv i tb);
  assert (not (has_substitution i tb));
  if satisfies (substituted_type tp tb) (Variable i) tb then
    if can_reach tp i tb then
      ()
    else
      tb.sub.(i) <- tp
  else
    raise Reject


let substitute_var_var (i:int) (j:int) (tb:t): unit =
  assert (not (has_substitution i tb));
  assert (not (has_substitution j tb));
  assert (not (is_local i tb && is_local j tb));
  try
    substitute i (Variable j) tb
  with Reject ->
    substitute j (Variable i) tb




let unify (t1:type_term) (t2:type_term) (tb:t): unit =
  (*printf "unify\n";
  printf " %s %s\n" (string_of_tvs tb) (string_of_substitutions tb);
  printf "  %s,   %s\n"
    (string_of_type t1 tb)
    (string_of_substituted_type_with_tvs t1 tb);
  printf "  %s,   %s\n"
    (string_of_type t2 tb)
    (string_of_substituted_type_with_tvs t2 tb);
  flush_all ();*)
  let ntvs = Tvars.count tb.tvs in
  let rec unify0 t1 t2 =
    match t1, t2 with
      Variable i, Variable j when i = j ->
      ()

    | Variable i, Variable j when i < ntvs && j < ntvs ->
       assert (not (is_local i tb && is_local j tb));
       let i_has_sub = has_substitution i tb
       and j_has_sub = has_substitution j tb
       in
       if not i_has_sub && not j_has_sub then
         substitute_var_var i j tb
       else if not i_has_sub then
         unify0 t1 tb.sub.(j)
       else if not j_has_sub then
         unify0 tb.sub.(i) t2
       else
           (* Both have substitutions *)
         unify0 tb.sub.(i) tb.sub.(j)


    | Variable i, _ when i < ntvs ->
       if has_substitution i tb then
         unify0 tb.sub.(i) t2
       else
         substitute i t2 tb

    | _, Variable j when j < ntvs ->
       if has_substitution j tb then
         unify0 t1 tb.sub.(j)
       else
         substitute j t1 tb

    | Variable i, _ ->
       raise Reject  (* Different types cannot be unified *)

    | _, Variable j ->
       raise Reject  (* Different types cannot be unified *)

    | VAppl(i1,args1,_,_), VAppl(i2,args2,_,_) when i1 = i2 ->
       let len = Array.length args1 in
       assert (len = Array.length args2);
       for i = 0 to len - 1 do
         unify0 args1.(i) args2.(i)
       done

    | VAppl(i1,args1,_,_), VAppl(i2,args2,_,_) ->
       assert (i1 <> i2);
       raise Reject (* Different classes cannot be unified *)
    | _ ->
       assert false (* Cannot happen with types *)
  in
  unify0 t1 t2
  (*try
    unify0 t1 t2;
    printf "unify ok  %s\n" (string_of_substitutions tb)
  with Reject ->
    printf "unify rejected\n";
    raise Reject*)



let unify_with_required (tp:type_term) (tb:t): unit =
  match tb.req with
    None ->
      ()
  | Some req ->
      unify req tp tb


let make
    (tp:type_term option) (nlocs:int) (nglobs:int) (nfgs:int) (c:Context.t)
    : t =
  let tvs_c = Context.tvars c in
  assert (Tvars.count_global tvs_c = 0);
  let nfgs_c       = Tvars.count_fgs tvs_c
  and nlocs_c      = Tvars.count_local tvs_c
  and fgconcepts_c = Tvars.fgconcepts tvs_c
  and fgnames_c    = Tvars.fgnames tvs_c
  in
  let maxlocs  = nlocs + nlocs_c
  and maxglobs = nglobs (* Context does not have globals *)
  and maxfgs   = nfgs + nfgs_c
  in
  let trans =
    let start  = nlocs_c
    and space1 = maxglobs + nfgs
    and space2 = nlocs in
    transform0 start space1 space2
  in
  let tp =
    match tp with
      None -> tp
    | Some tp -> Some (trans tp)
  in
  let tvs_tb =
    let concepts   = Array.make maxglobs empty_term
    and fgconcepts =
      Array.init
        maxfgs
        (fun i ->
          if i < maxfgs - nfgs_c then empty_term
          else trans fgconcepts_c.(i - (maxfgs - nfgs_c)))
    and fgnames    =
      let sym = ST.symbol "_" in
      Array.init maxfgs
        (fun i ->
          if i < maxfgs - nfgs_c then sym
          else fgnames_c.(i - (maxfgs - nfgs_c)))
    in
    Tvars.make maxlocs concepts fgnames fgconcepts
  in
  {req = tp;
   reqs = [];
   terms = [];
   calls = [];
   contexts  = [c];
   nlocals  = nlocs_c;
   nglobals = 0;
   nfgs     = nfgs_c;
   tvs = tvs_tb;
   sub = Array.init (maxlocs + maxglobs) (fun i -> Variable i);
   feature_fg_ranges = []
 }


let is_in_outer_context (tb:t): bool =
  match tb.contexts with
  | [_] ->
     true
  | [] ->
     assert false (* Cannot happen *)
  | _ ->
     false


let variable_type (i:int) (tb:t): type_term =
  let c = context tb in
  let tp = Context.variable_type i c in
  (transform_from_context c tb) tp


let add_variable (i:int) (tb:t): unit =
  let tp = variable_type i tb in
  unify_with_required tp tb;
  tb.terms <- (Variable i, tp) :: tb.terms


let expect_argument (i:int) (tb:t): unit =
  (* Set the required type for the argument [i] of the current function *)
  assert (tb.calls <> []);
  match List.hd tb.calls with
    GlFun (_,s,_,nargs,_,_,_) ->
      assert (i < nargs);
      assert (i < Sign.arity s);
      tb.req <- Some (Sign.arg_type i s)
  | TermApp (nargs,start) ->
      assert (i < nargs);
      tb.req <- Some (Variable (start+i))


let expect_boolean (tb:t): unit =
  tb.req <- Some (boolean_type tb)


let expect_type (tp:type_term) (tb:t): unit =
  let tp = (transform_from_context (context tb) tb) tp in
  unify_with_required tp tb;
  tb.req <- Some tp


let pop_term
    (terms:(term*type_term) list)
    : (term*type_term) * (term*type_term) list =
  assert (terms <> []);
  match terms with
    hd :: tl ->
      hd, tl
  | _ ->
      assert false (* Cannot happen *)

let pop_args
    (n:int) (terms:(term*type_term) list)
    : (term*type_term) list * (term*type_term) list
    =
  assert (n <= List.length terms);
  let args,terms =
    interval_fold
      (fun (args,terms) i ->
        match terms with
          [] -> assert false (* cannot happen *)
        | hd :: tl ->
            hd::args, tl
      )
      ([],terms) 0 n
  in
  args, terms


let add_globals (new_concepts:type_term array) (tb:t): unit =
  let n = Array.length new_concepts
  and concepts = Tvars.concepts tb.tvs
  and start = globals_beyond tb
  and gstart = globals_start tb
  in
  assert (Array.length tb.sub = Tvars.count tb.tvs);
  assert (n + tb.nglobals <= global_capacity tb);
  assert (start + n <= Array.length tb.sub);
  for i = start to start + n - 1 do
    tb.sub.(i) <- Variable i;
    concepts.(i-gstart) <- new_concepts.(i-start)
  done;
  tb.nglobals <- tb.nglobals + n


let add_anys (n:int) (tb:t): unit =
  let concepts = Array.make n (any_type tb) in
  add_globals concepts tb


let context_names_and_types (tb:t): int * names * types =
  let c = context tb in
  let nargs = Context.count_last_variables c
  and names = Context.local_argnames c
  and trans = transform_from_context c tb
  in
  let tps =
    Array.init
      nargs
      (fun i ->
        let tp = trans (Context.variable_type i c) in
        substituted_type tp tb
      )
  in
  nargs, names, tps


let tuple_type_of_args (start:int) (nargs:int) (tb:t): type_term =
  let arr =
    Array.init nargs (fun i -> Variable (start+i))
  in
  Class_table.to_tuple (count_all tb) 0 arr




let predicate_of_args (start:int) (nargs:int) (tb:t): type_term =
  let tup = tuple_type_of_args start nargs tb in
  make_type (predicate_index tb) [|tup|]


let function_of_args (start:int) (nargs:int) (rt:type_term) (tb:t): type_term =
  let tup = tuple_type_of_args start nargs tb in
  make_type (function_index tb) [|tup;rt|]




let tuple_of_args (args:term array) (tup_tp:type_term) (tb:t): term =
  let tup_tp = substituted_type tup_tp tb in
  let c = context tb in
  let nvars = Context.count_variables c
  and ft = Context.feature_table c in
  Feature_table.tuple_of_args args tup_tp nvars ft



let link_new_locals_to_new_globals (tb:t): unit =
  let c = context tb in
  let new_locs = Context.count_local_type_variables c in
  let gstart = globals_beyond tb
  and lstart = locals_start tb in
  add_anys new_locs tb;
  for i = 0 to new_locs - 1 do
    substitute (lstart + i) (Variable (gstart + i)) tb
  done

let context_signature (tb:t): Sign.t =
  (* The signature of the current context in the type environment of [tb]. *)
  let c = context tb in
  Sign.map (transform_from_context c tb) (Context.signature c)



let upgraded_signature (s:Sign.t) (is_pred:bool) (tb:t): type_term =
  (* The signature [s] upgraded to a predicate or a function. *)
  assert (Sign.has_result s);
  let ntvs = Tvars.count_all tb.tvs  in
  Class_table.upgrade_signature ntvs is_pred s



let partially_upgraded_signature
    (s:Sign.t) (nargs:int) (is_pred:bool) (tb:t)
    : type_term
    =
  (* The signature [s] without the first [nargs] arguments upgraded to a
     predicate or a function. *)
  assert (Sign.has_result s);
  let arity = Sign.arity s in
  assert (nargs < arity);
  let args = Array.sub (Sign.arguments s) nargs (arity-nargs) in
  let s = Sign.make_func args (Sign.result s) in
  upgraded_signature s is_pred tb



let required_can_be_boolean (tb:t): bool =
  match tb.req with
  | None ->
     true
  | Some tp ->
     let tp = substituted_type tp tb in
     match tp with
     | Variable i when i < globals_beyond tb ->
        assert (globals_start tb <= i);
        let cpt = concept i tb
        and nall = count_all tb in
        let cls,_ = Class_table.split_type_term cpt in
        assert (nall <= cls);
        Class_table.has_ancestor
          Constants.boolean_index
          (cls - nall)
          (class_table tb)
     | _ ->
        tp = boolean_type tb



let start_global_application (fidx:int) (nargs:int) (tb:t): unit =
  let tvs,s = Context.feature_signature fidx (context tb) in
  assert (Sign.has_result s);
  assert (Tvars.count tvs = 0); (* no locals, no globals *)
  let trans = transform_from_global tvs tb in
  let s = Sign.map trans s
  and concepts = Array.map trans (Tvars.fgconcepts tvs)
  in
  let start = globals_beyond tb
  and nfgs = Tvars.count_fgs tvs
  in
  add_globals concepts tb;
  tb.feature_fg_ranges <- begin
    let fidx = fidx - Context.count_variables (context tb) in
    (fidx,start,nfgs) :: tb.feature_fg_ranges
  end;
  let nargs_s = Sign.arity s in
  if nargs = nargs_s then
    begin
      tb.calls <- GlFun (fidx,s,false,nargs,start,nfgs,false) :: tb.calls;
      unify_with_required (Sign.result s) tb
    end
  else if nargs < nargs_s then
    begin
    (* The global function [fidx] has more arguments than there are arguments
       provided. We have to convert the call into an application of a function
       or a predicate expression. Suppose we have two arguments [a] and [b]
       and the function needs four arguments.

           ((c,d) -> f(a,b,c,d))    or {(c,d): f(a,b,c,d)}

       This is possible only if the types of the missing arguments satisfy the
       concept of [ANY].

           f(a:A,b:B,c:C,d:D): RT

           ((c,d) -> f(a,b,c,d)) : (C,D) -> RT
     *)
      if 0 < nargs then
        raise Reject; (* Partial application not yet allowed *)
      let is_pred =
        match tb.req with
          None -> false
        | Some tp ->
            let cls,_ = Class_table.split_type_term tp in
            if cls = function_index tb then
              false
            else if cls = predicate_index tb then
              true
            else
              raise Reject
      in
      let any_tp = any_type tb in
      if interval_exist
          (fun i -> not (satisfies (Sign.arg_type i s) any_tp tb))
          nargs nargs_s
      then
        raise Reject;
      let f_tp =
        let ntvs = count_all tb in
        let tup_tp = Class_table.to_tuple ntvs nargs (Sign.arguments s) in
        if not is_pred then
          Class_table.function_type tup_tp (Sign.result s) ntvs
        else if Sign.result s = boolean_type tb then
          Class_table.predicate_type tup_tp ntvs
        else
          raise Reject
      in
      tb.calls <- GlFun (fidx,s,false,nargs,start,nfgs,is_pred) :: tb.calls;
      unify_with_required f_tp tb
    end
  else if nargs_s = 0 then
    begin
      (* The global function [fidx] is a constant. It has to be a function or a
         predicate. *)
      assert (Sign.is_constant s);
      let s =
        try
          Class_table.downgrade_signature (count_all tb) s nargs
        with Not_found ->
          raise Reject
      in
      assert (Sign.arity s = nargs);
      tb.calls <- GlFun (fidx,s,true,nargs,start,nfgs,false) :: tb.calls;
      unify_with_required (Sign.result s) tb
    end
  else
    raise Reject



let start_predicate_application (nargs:int) (tb:t): unit =
  assert (required_can_be_boolean tb);
  let start = globals_beyond tb in
  tb.calls <- TermApp (nargs,start) :: tb.calls;
  begin
    try
      unify_with_required (boolean_type tb) tb
    with Reject ->
      assert false (* cannot happen because required can be boolean *)
  end;
  add_anys nargs tb;
  (* Set the required type to FUNCTION[ARGTUP,TP] *)
  tb.req <- Some (predicate_of_args start nargs tb)



let start_function_application (nargs:int) (tb:t): unit =
  let start = globals_beyond tb in
  tb.calls <- TermApp (nargs,start) :: tb.calls;
  match tb.req with
  | None ->
     add_anys (nargs + 1) tb;  (* one for the unknown result type *)
     let tp = Variable (start + nargs) in
     tb.req <- Some (function_of_args start nargs tp tb)
  | Some tp ->
     add_anys nargs tb;
     (* Set the required type to FUNCTION[ARGTUP,TP] *)
     tb.req <- Some (function_of_args start nargs tp tb)





let complete_application (am:application_mode) (tb:t): unit =
  assert (tb.calls <> []);
  match List.hd tb.calls with
    GlFun (fidx,s,is_const,nargs,start,nfgs,is_pred) ->
      tb.calls <- List.tl tb.calls;
      let nargs_s = Sign.arity s in
      let ags = Array.init nfgs (fun i -> Variable (start + i)) in
      let args,terms = pop_args nargs tb.terms in
      let args,tps = List.split args in
      let args = Array.of_list args
      and tps  = Array.of_list tps
      in
      if not is_const && nargs = nargs_s then
        begin
          let t =
            if fidx = in_index tb then
              Application (args.(1), [|args.(0)|], true)
            else
              VAppl (fidx, args, ags, oo_from_am am)
          in
          tb.terms <- (t,Sign.result s) :: terms;
        end
      else if not is_const && nargs < nargs_s then
        begin
          (* partial application: The first nargs (possibly 0) arguments are
             provided, for the rest we need a lambda expression.

             ((c,d) -> f(a,b,c,d))

           *)
          let tp = partially_upgraded_signature s nargs is_pred tb
          and names =
            Feature_table.argument_names
              (fidx - count_variables tb)
              (feature_table tb)
          and args =
            let args1 = Array.map (fun t -> Term.up (nargs_s-nargs) t) args
            and args2 = Array.init (nargs_s-nargs) (fun i -> Variable i) in
            Array.append args1 args2
          in
          let t0 =
            let t0 = VAppl(fidx+nargs_s-nargs, args, ags, false)
            and tup_tp = Class_table.domain_type tp in
            Feature_table.add_tuple_accessors
              t0
              (nargs_s-nargs)
              tup_tp
              (count_variables tb)
              (feature_table tb)
          in
          let t = Lam (nargs_s-nargs, names, [], t0, is_pred, tp) in
          tb.terms <- (t,tp) :: terms
        end
      else if is_const then
        (* The global function is a constant, but applied to arguments *)
        begin
          let tup = Class_table.to_tuple (count_all tb) 0 tps in
          let arg = tuple_of_args args tup tb in
          let f = VAppl(fidx,[||],ags,false) in
          let t = Application(f, [|arg|],false)
          and tp = Sign.result s
          in
          tb.terms <- (t,tp) :: terms
        end
      else
        assert false (* cannot happen *)
  | TermApp (nargs,start) ->
      tb.calls <- List.tl tb.calls;
      let args,terms = pop_args (nargs+1) tb.terms in
      let f,f_tp,args =
        match args with
          (f,f_tp) :: args ->
            f, f_tp, args
        | _ ->
            assert false (* Cannot happen *)
      in
      let f_tp = substituted_type f_tp tb in
      let arg =
        let args = Array.of_list (List.map (fun (t,_) -> t) args) in
        let cls,ags = Class_table.split_type_term f_tp in
        assert begin
          cls = predicate_index tb ||
          cls = function_index tb
        end;
        tuple_of_args args ags.(0) tb
      in
      let t = Application (f, [|arg|], false) in
      let tp = result_type_of_type f_tp tb in
      tb.terms <- (t,tp) :: terms



let push_context (c_new:Context.t) (tb:t): unit =
  let c = context tb in
  assert (c == Context.previous c_new);
  assert(Context.count_formal_generics c_new = tb.nfgs);

  let nlocs_new = Context.count_type_variables c_new in
  assert (tb.nlocals <= nlocs_new);
  assert (nlocs_new <= local_capacity tb);

  let lstart = locals_start tb in
  tb.nlocals <- nlocs_new;
  let lstart_new = locals_start tb in
  tb.contexts <- c_new :: tb.contexts;
  for i = lstart_new to lstart - 1 do
    tb.sub.(i) <- Variable i
  done


let pop_context (tb:t): unit =
  let c = context tb in
  let nlocals_delta = Context.count_last_type_variables c in
  assert (nlocals_delta <= tb.nlocals);
  tb.nlocals <- tb.nlocals - nlocals_delta;
  tb.contexts <- List.tl tb.contexts




let start_quantified (c:Context.t) (tb:t): unit =
  unify_with_required (boolean_type tb) tb;
  push_context c tb;
  tb.req <- Some (boolean_type tb)



let complete_quantified (is_all:bool) (tb:t): unit =
  let nargs,names,tps = context_names_and_types tb in
  let t0,t0_tp = List.hd tb.terms in
  let t =
    if is_all then
      Term.all_quantified nargs (names,tps) empty_formals t0
    else
      Term.some_quantified nargs (names,tps) t0
  in
  pop_context tb;
  tb.terms <- (t,t0_tp) :: List.tl tb.terms




let start_lambda (c_new:Context.t) (is_pred:bool) (tb:t): unit =
  assert (Context.previous c_new == context tb);
  push_context c_new tb;
  link_new_locals_to_new_globals tb;
  let csig = context_signature tb in
  assert (Sign.has_result csig);
  let tp = upgraded_signature csig is_pred tb in
  unify_with_required tp tb;
  tb.req <-
    Some begin
      if is_pred then
        boolean_type tb
      else
        Sign.result csig
    end



let complete_lambda (is_pred:bool) (npres:int) (tb:t): unit =
  assert (not is_pred || npres = 0);
  let c = context tb in
  let csig = context_signature tb
  and names = Context.local_argnames c
  and nargs = Context.count_last_arguments c
  in
  let tp = upgraded_signature csig is_pred tb in
  (* pop preconditions *)
  let pres,terms = pop_args npres tb.terms
  in
  (* pop t0 *)
  let t0,t0_tp = List.hd terms
  and terms = List.tl terms
  in
  let t0,pres =
    let tup_tp = Class_table.domain_type tp in
    let ft = Context.feature_table c in
    let nvars = Context.count_variables c in
    let add_tup_acc t =
      Feature_table.add_tuple_accessors t nargs tup_tp (nvars-nargs) ft
    in
    add_tup_acc t0,
    List.map (fun (t,tp) -> add_tup_acc t) pres
  in
  let t = Lam (nargs,names,pres,t0,is_pred,tp)
  in
  pop_context tb;
  tb.terms <- (t,tp) :: terms




let expect_else_expression (tb:t): unit =
  let _,tp = List.hd tb.terms in
  tb.req <- Some tp




let complete_if_expression (tb:t): unit =
  let (cond,cond_tp),terms = pop_term tb.terms in
  let (e2,e1_tp),terms     = pop_term terms in
  let (e1,e2_tp),terms     = pop_term terms in
  tb.terms <- (Flow (Ifexp, [|cond;e1;e2|]),e1_tp) :: terms



let start_as_expression (tb:t): unit =
  unify_with_required (boolean_type tb) tb;
  tb.req <- None


let expect_as_pattern (c:Context.t) (tb:t): unit =
  let _,tp = List.hd tb.terms in
  push_context c tb;
  tb.req <- Some tp


let complete_as_expression (tb:t): unit =
  let (pat,_),  terms = pop_term tb.terms in
  let nargs,names,tps = context_names_and_types tb in
  let pat = Term.some_quantified nargs (names,tps) pat
  in
  pop_context tb;
  let (insp,_), terms = pop_term terms in
  let t = Flow(Asexp,[|insp;pat|])
  and tp = boolean_type tb
  in
  tb.terms <- (t,tp) :: terms



let start_inspect (tb:t): unit =
  let tp =
    match tb.req with
      None ->
        let glob_new = globals_beyond tb in
        add_anys 1 tb;
        Variable glob_new
    | Some tp ->
        tp
  in
  push_required tp tb;
  tb.req <- None


let start_cases (tb:t): unit =
  assert (tb.terms <> []);
  let _,tp = List.hd tb.terms in
  push_required tp tb;
  tb.req <- Some tp


let start_case (c:Context.t) (tb:t): unit =
  assert (List.length tb.reqs >= 2);
  tb.req <- Some (List.nth tb.reqs 0);
  push_context c tb


let expect_case_result (tb:t): unit =
  assert (List.length tb.reqs >= 2);
  tb.req <- Some (List.nth tb.reqs 1)


let complete_case (tb:t): unit =
  assert (List.length tb.terms >= 2);
  let (res,_), terms = pop_term tb.terms in
  let (pat,_), terms = pop_term terms in
  let nargs, names,tps = context_names_and_types tb in
  let pat = Term.some_quantified nargs (names,tps) pat
  and res = Term.some_quantified nargs (names,tps) res in
  tb.terms <- (res,empty_term) :: (pat,empty_term) :: terms;
  pop_context tb


let complete_inspect (ncases:int) (tb:t): unit =
  assert (List.length tb.reqs >= 2);
  assert (List.length tb.terms >= 2*ncases + 1);
  let args,terms = pop_args (2*ncases+1) tb.terms in
  let args = Array.of_list (List.map (fun (t,_) -> t) args) in
  let tp = List.nth tb.reqs 1
  and t = Flow(Inspect,args) in
  tb.terms <- (t,tp) :: terms;
  tb.reqs <- List.tl (List.tl tb.reqs)


let start_inductive_set (c_new:Context.t) (tb:t): unit =
  assert (Context.previous c_new == context tb);
  assert (Context.count_last_variables c_new = 1);
  push_context c_new tb;
  let nlocs = Context.count_last_type_variables c_new in
  assert (nlocs <= 1);
  if nlocs = 1 then begin
    let start = globals_beyond tb in
    add_anys 1 tb;
    let pred_tp = Class_table.predicate_type (Variable start) (count_all tb) in
    assert (not (has_substitution (locals_start tb) tb));
    substitute (locals_start tb) pred_tp tb
  end;
  let pred_tp = Variable (locals_start tb) in
  unify_with_required pred_tp tb


let complete_inductive_set (n:int) (tb:t): unit =
  let args,terms = pop_args n tb.terms in
  let names = Context.local_argnames (context tb) in
  assert (Array.length names = 1);
  let tp = variable_type 0 tb
  and rules = Array.of_list (List.map (fun (t,tp) -> t) args)
  in
  let t = Indset (names.(0), tp, rules) in
  pop_context tb;
  tb.terms <- (t,tp) :: terms


let has_undefined_globals (tb:t): bool =
  interval_exist
    (fun i -> tb.sub.(i) = Variable i)
    (globals_start tb)
    (globals_beyond tb)


let is_fully_typed (tb:t): bool =
  not (has_undefined_globals tb)



let type_in_context (tp:type_term) (tb:t): type_term =
  let tp = substituted_type tp tb in
  try
    let ntvs = Context.count_type_variables (context tb) in
    let fg0 = fgs_start tb in
    let tp = Term.down fg0 tp in
    Term.up ntvs tp
  with Term_capture ->
    assert false (* substituted type should not contain type variables *)


let head_term_in_context (tb:t): term =
  assert (is_fully_typed tb);
  let tpc tp = type_in_context tp tb in
  let tpc_args args = Array.map tpc args in
  let rec term t =
    let targs args = Array.map term args
    and tlst  lst  = List.map  term lst in
    match t with
      Variable _ -> t
    | VAppl(i,args,ags,oo) ->
        VAppl(i,targs args, tpc_args ags, oo)
    | Application (f,args,inop) ->
        let f = term f
        and args = targs args in
        Application (f,args,inop)
    | Lam (n,nms,ps,t0,pr,tp) ->
        let ps = tlst ps
        and t0 = term t0
        and tp = tpc tp in
        Lam (n,nms,ps,t0,pr,tp)
    | QExp (n,(nms,tps),fgs,t0,is_all) ->
        assert (fgs = empty_formals);
        let tps = tpc_args tps
        and t0  = term t0 in
        QExp (n,(nms,tps),fgs,t0,is_all)
    | Indset (nme,tp,rs) ->
        Indset(nme,tpc tp, targs rs)
    | Flow (ctrl,args) ->
        Flow (ctrl, targs args)
  in
  term (head_term tb)


let undefined_untyped (tb:t): int list =
  (* The list of untyped variables of the context of [tb] which could not be
     determined completely *)
  assert (is_in_outer_context tb);
  let c = context tb in
  let tvs_c = Context.tvars c in
  let nlocs_c = Tvars.count_local tvs_c
  and globs_beyond = globals_beyond tb
  and locs_start   = locals_start tb
  in
  assert (Tvars.count_global tvs_c = 0);
  assert (nlocs_c = tb.nlocals);
  interval_fold
    (fun lst i ->
      let sub = substituted_type tb.sub.(locs_start+i) tb in
      match sub with
      | Variable j when j < globs_beyond ->
         i :: lst
      | _ ->
         lst
    )
    []
    0 nlocs_c


let untyped_in_context (tb:t): type_term array =
  assert (is_fully_typed tb);
  assert (is_in_outer_context tb);
  let c = context tb in
  let tvs_c = Context.tvars c in
  let nlocs_c = Tvars.count_local tvs_c
  and nfgs_c  = Tvars.count_fgs tvs_c
  in
  assert (Tvars.count_global tvs_c = 0);
  assert (nlocs_c = tb.nlocals);
  assert (nfgs_c  = tb.nfgs);
  let loc_start  = globals_start tb - tb.nlocals
  and glob_start = globals_start tb in
  let space2     = Tvars.count_all tb.tvs - nfgs_c - glob_start in
  Array.init
    nlocs_c
    (fun i ->
      if has_substitution (loc_start+i) tb then
        let sub = substituted_type tb.sub.(loc_start+i) tb in
        try
          let sub = Term.down_from space2 glob_start sub in
          Term.down loc_start sub
        with Term_capture ->
          assert false (* cannot happen *)
      else
        Variable i)



let update_context (c:Context.t) (tb:t): unit =
  assert (is_fully_typed tb);
  assert (is_in_outer_context tb);
  let subs = untyped_in_context tb in
  Context.update_types subs c


let result_term (tb:t): term =
  let t = head_term_in_context tb in
  let t = Context.specialized t (context tb) in
  Context.prenex_term t (context tb)
