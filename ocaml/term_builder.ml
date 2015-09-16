(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Term
open Signature
open Container
open Support
open Printf


type term_rec = {
    term:  term;
    sign:  Sign.t;
    sign0: Sign.t
  }
type fun_rec  = {
    pos: int;
    level:int;
    nargs: int;
    pr: int (* 0: function, 1: predicate, -1: don't know *)
  }
type con_rec = {
    c: Context.t
  }
type t = {
    mutable tvs:      Tvars.t;
    mutable subs:     type_term array;
    mutable nlocals:  int;
    mutable nglobals: int;
    mutable nfgs:     int;
    mutable rtype:    type_term;
    mutable norm:     bool;
    mutable level:    int;
    terms:            term_rec Seq.t;
    funstack:         fun_rec  Seq.t;
    constack:         con_rec  Seq.t;
    lamstack:         type_term Seq.t;
    reqstack:         type_term Seq.t;
    gcntseq:          int Seq.t;
    mutable trace:    bool
  }

(*
  global:                          gglobs
  context:          locs         +                   fgs
  builder:  blocs + locs + globs +         garbfgs + fgs

  The locals of a context are always a suffix of the locals of the builder.

  The formal generics of a context are always a suffix of the formal generics
  of the builder.

 *)


let depth (tb:t): int = Seq.count tb.constack

let has_context (tb:t): bool =
  0 < depth tb

let context (tb:t): Context.t =
  assert (depth tb > 0);
  (Seq.last tb.constack).c


let class_table (tb:t): Class_table.t =
  Context.class_table (context tb)

let locals_start   (tb:t): int = Tvars.count_local tb.tvs - tb.nlocals
let globals_start  (tb:t): int = Tvars.count_local tb.tvs
let globals_beyond (tb:t): int = globals_start tb + tb.nglobals
let fgs_start (tb:t): int      = Tvars.count_all tb.tvs - tb.nfgs


let count_local (te:t): int = te.nlocals
let count_global (te:t): int = te.nglobals
let count_fgs (te:t): int = te.nfgs
let local_capacity  (te:t): int = Tvars.count_local  te.tvs
let global_capacity (te:t): int = Tvars.count_global te.tvs
let fgs_capacity    (te:t): int = Tvars.count_fgs    te.tvs

let count_local_added (tb:t): int =
  let res = tb.nlocals - Context.count_type_variables (context tb) in
  assert (0 <= res);
  res

let is_local (i:int) (tb:t): bool =
  let gstart = globals_start tb in
  gstart - tb.nlocals <= i && i < gstart

let is_global (i:int) (tb:t): bool =
  let gstart = globals_start tb in
  gstart <= i && i < gstart + tb.nglobals


let is_tv (i:int) (tb:t): bool =
  let gstart = globals_start tb in
  gstart - tb.nlocals <= i && i < gstart + tb.nglobals


let is_fg (i:int) (tb:t): bool =
  let nall = Tvars.count_all tb.tvs in
  nall - tb.nfgs <= i && i < nall


let can_add_globals (n:int) (tb:t): bool =
  globals_start tb + tb.nglobals + n + tb.nfgs <
  Tvars.count_all tb.tvs



let boolean_index   (tb:t): int = Tvars.count_all tb.tvs + Class_table.boolean_index
let any_index       (tb:t): int = Tvars.count_all tb.tvs + Class_table.any_index
let predicate_index (tb:t): int = Tvars.count_all tb.tvs + Class_table.predicate_index
let function_index  (tb:t): int = Tvars.count_all tb.tvs + Class_table.function_index
let dummy_index     (tb:t): int = Tvars.count_all tb.tvs + Class_table.dummy_index

let boolean_type (tb:t): type_term = Variable (boolean_index tb)
let any_type     (tb:t): type_term = Variable (any_index tb)

let count_terms (tb:t): int = Seq.count tb.terms


let ith_term (i:int) (tb:t): term =
  assert (i < count_terms tb);
  (Seq.elem i tb.terms).term


let head_term (tb:t): term =
  assert (0 < Seq.count tb.terms);
  (Seq.first tb.terms).term

let last_term (tb:t): term =
  assert (0 < Seq.count tb.terms);
  (Seq.last tb.terms).term


let is_expecting_function (tb:t): bool =
  Seq.count tb.funstack > 0 &&
  let funrec = Seq.last tb.funstack in
  funrec.pos = Seq.count tb.terms && funrec.level = tb.level

let expected_arity (tb:t): int =
  if is_expecting_function tb then
    (Seq.last tb.funstack).nargs
  else
    0

let tvars (tb:t): Tvars.t = tb.tvs

let string_of_term (t:term) (tb:t): string =
  Context.string_of_term t tb.norm 0 (context tb)



let string_of_head_term (tb:t): string =
  string_of_term (head_term tb) tb


let string_of_last_term (tb:t): string =
  string_of_term (last_term tb) tb


let string_of_reduced_complete_signature (s:Sign.t) (tb:t): string =
  let ct = class_table tb in
  Class_table.string_of_reduced_complete_signature s tb.tvs ct

let string_of_reduced_complete_type (tp:type_term) (tb:t): string =
  let s = Sign.make_const tp in
  string_of_reduced_complete_signature s tb


let string_of_type (t:type_term) (tb:t): string =
  Class_table.string_of_type t tb.tvs (class_table tb)

let string_of_signature (s:Sign.t) (tb:t): string =
  Class_table.string_of_signature s tb.tvs (class_table tb)


let string_of_head_signature (tb:t): string =
  assert (0 < Seq.count tb.terms);
  let trec = Seq.elem 0 tb.terms in
  string_of_signature trec.sign tb

let string_of_last_signature (tb:t): string =
  assert (0 < Seq.count tb.terms);
  let trec = Seq.last tb.terms in
  string_of_signature trec.sign tb

let string_of_tvs (tb:t): string =
  let lstart  = locals_start tb
  and gstart  = globals_start tb
  and fgstart = fgs_start tb in
  let _,str = interval_fold
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
  let ntvs = Tvars.count_all tb.tvs in
  let lst,_ =
    Array.fold_left
      (fun (lst,i) t ->
        match t with
          Variable j when j < ntvs ->
            if i=j then lst, i+1
            else (i,t)::lst, i+1
        | _ -> (i,t)::lst, i+1)
      ([],0)
      tb.subs in
  if lst = [] then ""
  else
    "[" ^ (String.concat ","
             (List.map
                (fun (i,t) -> (string_of_int i) ^ ":=" ^ (string_of_type t tb))
                (List.rev lst))) ^ "]"


let string_of_complete_type (t:type_term) (tb:t): string =
  (string_of_tvs tb) ^ (string_of_substitutions tb) ^
  " " ^ (string_of_type t tb)

let string_of_complete_signature (s:Sign.t) (tb:t): string =
  (string_of_tvs tb) ^ (string_of_substitutions tb) ^
  " " ^ (string_of_signature s tb)


let string_of_reduced_required_type (tb:t): string =
  string_of_reduced_complete_type tb.rtype tb



let substituted_type (tp:type_term) (tb:t): type_term =
  Term.sub tp tb.subs (Array.length tb.subs)

let substituted_signature (s:Sign.t) (tb:t): Sign.t =
  Sign.map (fun tp -> substituted_type tp tb) s

let make () =
  let maxglobals = 30
  and maxfgs     = 10
  and maxlocals  = 10 in
  (*let maxglobals = 0
  and maxfgs     = 0
  and maxlocals  = 0 in*)
  let concepts   = Array.make maxglobals (Variable 0)
  and fgconcepts = Array.make maxfgs     (Variable 0)
  and fgnames    =
    let sym = ST.symbol "_" in
    Array.make maxfgs sym
  in
  { tvs       =  Tvars.make maxlocals concepts fgnames fgconcepts;
    rtype     =  Variable 0;
    nlocals   =  0;
    nglobals  =  0;
    nfgs      =  0;
    level     =  0;
    norm      =  false;
    subs      =  Array.init (maxlocals+maxglobals) (fun i -> Variable i);
    terms     =  Seq.empty ();
    funstack  =  Seq.empty ();
    constack  =  Seq.empty ();
    lamstack  =  Seq.empty ();
    reqstack  =  Seq.empty ();
    gcntseq   =  Seq.empty ();
    trace     =  false
  }


let clone (tb:t): t =
  let concepts   = Array.copy (Tvars.concepts tb.tvs)
  and fgconcepts = Array.copy (Tvars.fgconcepts tb.tvs)
  and fgnames    = Array.copy (Tvars.fgnames tb.tvs) in
  { tvs = Tvars.make (Tvars.count_local tb.tvs) concepts fgnames fgconcepts;
    rtype    =  tb.rtype;
    nlocals  =  tb.nlocals;
    nglobals =  tb.nglobals;
    nfgs     =  tb.nfgs;
    level    =  tb.level;
    norm     =  tb.norm;
    subs     =  Array.copy tb.subs;
    terms    =  Seq.copy tb.terms;
    funstack =  Seq.copy tb.funstack;
    constack =  Seq.copy tb.constack;
    lamstack =  Seq.copy tb.lamstack;
    reqstack =  Seq.copy tb.reqstack;
    gcntseq  =  Seq.copy tb.gcntseq;
    trace    =  tb.trace
  }

let remove_local (n:int) (tb:t): unit =
  assert (n <= tb.nlocals);
  let start = locals_start tb in
  for i = 0 to n - 1 do
    tb.subs.(start+i)  <- Variable (start+i)
  done;
  tb.nlocals <- tb.nlocals - n



let remove_global (n:int) (tb:t): unit =
  assert (n <= tb.nglobals);
  let start0 = globals_start tb + tb.nglobals - n
  and start1 = tb.nglobals - n
  and concepts = Tvars.concepts tb.tvs in
  for i = 0 to n - 1 do
    tb.subs.(start0+i)  <- Variable (start0+i);
    concepts.(start1+i) <- Variable 0
  done;
  tb.nglobals <- tb.nglobals - n



let remove_fg (n:int) (tb:t): unit =
  assert (n <= tb.nfgs);
  let sym = ST.symbol "_"
  and start1 = Tvars.count_fgs tb.tvs - tb.nfgs
  and fgconcepts = Tvars.fgconcepts tb.tvs
  and fgnames    = Tvars.fgnames tb.tvs in
  for i = 0 to n - 1 do
    fgconcepts.(start1+i) <- Variable 0;
    fgnames.   (start1+i) <- sym
  done;
  tb.nfgs <- tb.nfgs - n



let reset (tb:t): unit =
  remove_local  tb.nlocals tb;
  remove_global tb.nglobals tb;
  remove_fg     tb.nfgs tb;
  tb.level <- 0;
  tb.norm  <- false;
  Seq.keep 0 tb.terms;
  Seq.keep 0 tb.funstack;
  Seq.keep 0 tb.constack;
  Seq.keep 0 tb.lamstack;
  Seq.keep 0 tb.reqstack;
  Seq.keep 0 tb.gcntseq;
  tb.rtype    <- Variable 0;
  (*assert begin
    interval_for_all (fun i ->
      match tb.subs.(i) with Variable j -> i = j | _ -> false)
      0 (Array.length tb.subs)
  end;*)
  tb.trace    <- false



let resize (nlocs:int) (nglobs:int) (nfgs:int) (tb:t): unit =
  if
    nlocs  + tb.nlocals  <= local_capacity tb &&
    nglobs + 2 + tb.nglobals <= global_capacity tb &&
    nfgs   + tb.nfgs     <= fgs_capacity tb then ()
  else begin
    if tb.trace then begin
      printf "resize %d, %d, %d\n" nlocs nglobs nfgs;
      printf "  tvs  %s\n" (string_of_tvs tb);
      printf "  subs %s\n" (string_of_substitutions tb)
    end;
    let nglobs = nglobs + 2 in  (* always 2 globals reserve *)
    let nall = Tvars.count_all tb.tvs
    and cnt  = Tvars.count tb.tvs
    and fcap = fgs_capacity tb
    and gcap = global_capacity tb
    and lcap = local_capacity tb
    and start_locs0  = locals_start tb
    and start_globs0 = globals_start tb
    in
    let start_locs1  = start_locs0 + nlocs
    and start_globs1 = start_globs0 + nlocs in
    let transform =
      (fun tp ->
        let tp = Term.upbound nfgs nall tp in
        let tp = Term.upbound nglobs cnt tp in
        Term.up nlocs tp)
    in
    tb.rtype <- transform tb.rtype;
    tb.tvs <- begin
      let concepts = Array.make (gcap+nglobs) (Variable 0)
      and fgconcepts = Array.make (fcap+nfgs) (Variable 0)
      and fgnames    = Array.make (fcap+nfgs) (ST.symbol "_")
      and start0     = fcap - tb.nfgs
      and start1     = fcap + nfgs - tb.nfgs in
      for i = 0 to tb.nfgs - 1 do
        fgconcepts.(start1+i) <- transform (Tvars.fgconcepts tb.tvs).(start0+i);
        fgnames.(start1+i)    <- (Tvars.fgnames tb.tvs).(start0+i)
      done;
      for i = 0 to tb.nglobals - 1 do
        concepts.(i) <- transform (Tvars.concepts tb.tvs).(i)
      done;
      Tvars.make (lcap+nlocs) concepts fgnames fgconcepts end;
    tb.subs <-
      Array.init (lcap+nlocs+gcap+nglobs)
        (fun i ->
          if i < start_locs1 then Variable i
          else if start_locs1 <= i && i < start_globs1 + tb.nglobals then
            transform tb.subs.(i-nlocs)
          else Variable i);
    interval_iter
      (fun i ->
        let trec = Seq.elem i tb.terms in
        Seq.put
          i
          {trec with sign = Sign.map transform trec.sign;
           sign0 = Sign.map transform trec.sign0}
          tb.terms)
      0 (Seq.count tb.terms);
    let transform_seq seq =
      interval_iter
        (fun i -> Seq.put i (transform (Seq.elem i seq)) seq)
        0 (Seq.count seq)
    in
    transform_seq tb.lamstack;
    transform_seq tb.reqstack;
    if tb.trace then begin
      printf "  tvs  %s\n" (string_of_tvs tb);
      printf "  subs %s\n" (string_of_substitutions tb)
    end
  end




let transform_from_global (tvs:Tvars.t) (tb:t): type_term -> type_term  =
  (* Calculation the transformation triple [space1,start,space2] for the
     signature [tvs,s] coming from a global environment. [space1] is the
     space needed at the bottom and [space2] is the space needed starting
     from [start] *)
  assert (Tvars.count_local tvs = 0);
  assert (Tvars.count_fgs tvs   = 0);
  let nglobs = Tvars.count_global tvs in
  let space1 = globals_start tb + (tb.nglobals - nglobs)
  and nall   = Tvars.count_all tb.tvs
  in
  let space2 = nall - (space1 + nglobs) in
  (fun tp ->
    let tp = Term.upbound space2 nglobs tp in
    Term.up space1 tp)


let transform_from_context (tvs:Tvars.t) (tb:t): type_term -> type_term =
  (* Calculation the transformation triple [space1,start,space2] for the
     signature [tvs,s] coming from a context. [space1] is the space needed
     at the bottom and [space2] is the space needed starting from [start] *)
  assert (Tvars.count_global tvs = 0);
  assert (Tvars.count_local tvs <= tb.nlocals);
  assert (Tvars.count_fgs tvs   <= tb.nfgs);
  let nfgs  = Tvars.count_fgs tvs
  and nlocs  = Tvars.count_local tvs in
  let space2 = Tvars.count_global tb.tvs + Tvars.count_fgs tb.tvs - nfgs
  and space1 = Tvars.count_local tb.tvs - nlocs in
  (fun tp ->
    let tp = Term.upbound space2 nlocs tp in
    Term.up space1 tp)



let substituted_context_signature (tb:t): Sign.t =
  assert (has_context tb);
  let c = context tb in
  let s = Context.signature c in
  let trans = transform_from_context (Context.tvars c) tb in
  Sign.map (fun t -> substituted_type (trans t) tb) s



let add_local_wo_resize (n:int) (tb:t): unit =
  assert (n + tb.nlocals <= Tvars.count_local tb.tvs);
  tb.nlocals <- n + tb.nlocals



let add_fg_wo_resize (tvs:Tvars.t) (tb:t): unit =
  assert (tb.nfgs <= Tvars.count_fgs tvs); (* nyi: garbage fgs *)
  if not (Tvars.count_fgs tvs <= fgs_capacity tb) then
    printf "count_fgs %d, fgcap %d, nfgs %d\n"
      (Tvars.count_fgs tvs) (fgs_capacity tb) tb.nfgs;
  assert (Tvars.count_fgs tvs <= fgs_capacity tb);
  let fgnames     = Tvars.fgnames tb.tvs
  and fgconcepts  = Tvars.fgconcepts tb.tvs
  and fgnames0    = Tvars.fgnames tvs
  and fgconcepts0 = Tvars.fgconcepts tvs in
  let start0 = Tvars.count_fgs tb.tvs - Tvars.count_fgs tvs
  and space  = Tvars.count_all tb.tvs - Tvars.count_all tvs  in
  for i = 0 to Tvars.count_fgs tvs - tb.nfgs - 1 do
    fgconcepts.(start0+i) <- Term.up space fgconcepts0.(i);
    fgnames.(start0+i)    <- fgnames0.(i)
  done;
  tb.nfgs <- Tvars.count_fgs tvs



let has_sub (i:int) (tb:t): bool =
  assert (is_tv i tb);
  match tb.subs.(i) with Variable j -> i <> j | _ -> true



let add_sub (i:int) (t:type_term) (tb:t): unit =
  assert (is_tv i tb);
  assert (not (has_sub i tb));
  tb.subs.(i) <- t;
  for k = locals_start tb to globals_beyond tb - 1 do
    tb.subs.(k) <- Term.sub tb.subs.(k) tb.subs (Tvars.count tb.tvs)
  done;
  assert (not (IntSet.mem i (Term.bound_variables t (Tvars.count tb.tvs))))



let push_context (c:Context.t) (tb:t): unit =
  let ntvs = Context.count_type_variables c
  and nfgs =
    if Seq.is_empty tb.constack then
      Context.count_formal_generics c
    else
      Context.count_last_formal_generics c in
  assert (tb.nlocals <= ntvs);
  let ntvs_delta = ntvs - tb.nlocals in
  resize ntvs_delta 0 nfgs tb;
  Seq.push {c=c} tb.constack;
  tb.level <- tb.level + 1;
  add_local_wo_resize (ntvs - tb.nlocals) tb;
  add_fg_wo_resize (Context.tvars c) tb;
  let tvs_sub = Context.type_variables c in
  let trans = transform_from_context (TVars_sub.tvars tvs_sub) tb in
  for i = 0 to ntvs_delta - 1 do
    let tp = trans (TVars_sub.get i tvs_sub) in
    tb.subs.(locals_start tb + i) <- tp
  done


let pop_context (tb:t): unit =
  assert (Seq.count tb.constack > 0);
  Seq.pop 1 tb.constack;
  tb.level <- tb.level - 1


let init (c:Context.t) (tb:t): unit =
  assert (tb.nlocals  = 0);
  assert (tb.nglobals = 0);
  assert (tb.nfgs     = 0);
  resize 0 0 0 tb;
  let tvs = Context.tvars c in
  assert (Tvars.count_global tvs = 0);
  push_context c tb;
  tb.trace <- 6 <= Context.verbosity c



let unify (t1:type_term) (t2:type_term) (tb:t): unit =
  let ntvs = Tvars.count tb.tvs
  in
  let rec uni t1 t2 =
    let not_found str =
      raise Not_found in
    let do_sub i t =
      assert (is_tv i tb);
      assert (not (has_sub i tb));
      add_sub i t tb;
      if i < globals_start tb then
        ()
      else
        let con = Tvars.concept i tb.tvs in
        match t with
          Variable j when is_local j tb ->
            not_found "is_local"
        | Variable j when is_global j tb || is_fg j tb ->
            let con2 = Tvars.concept j tb.tvs in
            if not (Class_table.satisfies
                      con2 tb.tvs con tb.tvs (class_table tb)) then
              not_found "not satisfies"
        | _ ->
            let anc_cls,_ = Class_table.split_type_term con in
            let anc_tp =
              Class_table.ancestor_type t anc_cls
                (Tvars.count_all tb.tvs) (class_table tb) in
            uni con anc_tp
    in
    let do_sub_varvar i j =
      assert (is_tv i tb);
      assert (is_tv j tb);
      assert (not (has_sub i tb));
      assert (not (has_sub j tb));
      let i,j = if i<=j then i,j else j,i in
      if is_local i tb then do_sub i (Variable j)
      else
        let coni,conj = Tvars.concept i tb.tvs, Tvars.concept j tb.tvs
        and ct = class_table tb in
        if Class_table.satisfies coni tb.tvs conj tb.tvs ct then
          add_sub j (Variable i) tb
        else if Class_table.satisfies conj tb.tvs coni tb.tvs ct then
          add_sub i (Variable j) tb
        else
          not_found "not satisfies varvar"
    in
    let do_vareq i t =
      if not (is_tv i tb) then begin
        printf "not tv %d,  nlocs %d, lcap %d\n" i tb.nlocals (local_capacity tb)
      end;
      assert (is_tv i tb);
      if has_sub i tb then
        uni tb.subs.(i) t
      else
        do_sub i t
    in
    match t1, t2 with
      Variable i, Variable j when i = j ->
        ()
    | Variable i, Variable j when i < ntvs && j < ntvs ->
        assert (is_tv i tb);
        assert (is_tv j tb);
        if not (has_sub i tb) && not (has_sub j tb) then
          do_sub_varvar i j
        else if not (has_sub i tb) then
          uni t1 tb.subs.(j)
        else if not (has_sub j tb) then
          uni tb.subs.(i) t2
        else
          uni tb.subs.(i) tb.subs.(j)
    | VAppl(i1,args1), _ when i1 = dummy_index tb ->
        if tb.trace then printf "unify dummy %s with %s\n"
            (string_of_type t1 tb) (string_of_type t2 tb);
        assert (Array.length args1 = 2);
        begin match t2 with
          Variable j when j < ntvs && has_sub j tb->
            if tb.trace then printf "unify dummy with substituted variable\n";
            uni t1 tb.subs.(j);
        | VAppl(i2,args2) when i2 = predicate_index tb ->
            if tb.trace then printf "unify dummy with predicate\n";
            assert (Array.length args2 = 1);
            uni args1.(0) args2.(0);
            uni args1.(1) (boolean_type tb);
        | VAppl(i2,args2) when i2 = function_index tb ->
            if tb.trace then printf "unify dummy with function\n";
            assert (Array.length args2 = 2);
            uni args1.(0) args2.(0);
            uni args1.(1) args2.(1);
        | _ ->
            if tb.trace then printf "unify dummy fall through\n";
            raise Not_found
        end
    | Variable i, _ when i < ntvs->
        do_vareq i t2
    | _ , Variable j when j < ntvs ->
        do_vareq j t1
    | Variable i, Variable j when i = j ->
        ()
    | VAppl(i1,args1), VAppl(i2,args2) ->
        let nargs = Array.length args1 in
        if nargs <> (Array.length args2) then
          not_found "diff args len (2)";
        uni (Variable i1) (Variable i2);
        for i = 0 to nargs-1 do
          uni args1.(i) args2.(i)
        done
    | _ ->
        not_found "fall through"
  in
  try
    if tb.trace then begin
      printf "    unify %s%s\n" (string_of_tvs tb) (string_of_substitutions tb);
      printf "          %s\n" (string_of_type t1 tb);
      printf "          %s\n" (string_of_type t2 tb);
    end;
    uni t1 t2;
  with Not_found ->
    if tb.trace then printf "    fail\n";
    raise Not_found



let context_signature (tb:t): Sign.t =
  let c = context tb in
  let transform = transform_from_context (Context.tvars c) tb in
  Sign.map transform (Context.signature c)


let expect_new_untyped (tb:t): unit =
  resize 1 0 0 tb;
  add_local_wo_resize 1 tb;
  tb.rtype <- Variable (locals_start tb)


let add_anys (n:int) (tb:t):unit =
  assert (tb.nglobals + n <= global_capacity tb);
  (*resize 0 n 0 tb;*)
  let anytp    = any_type tb
  and concepts = Tvars.concepts tb.tvs in
  for i = 0 to n-1 do
    concepts.(tb.nglobals+i)  <- anytp
  done;
  tb.nglobals <- n + tb.nglobals


let push_expected (tb:t): unit =
  Seq.push tb.rtype tb.reqstack



let get_expected (n:int) (tb:t): unit =
  let cnt = Seq.count tb.reqstack in
  assert (n < cnt);
  tb.rtype <- Seq.elem (cnt-1-n) tb.reqstack



let drop_expected (tb:t): unit =
  Seq.pop 1 tb.reqstack





let expect_boolean_expression (tb:t): unit =
  tb.rtype <- boolean_type tb



let expect_boolean (tb:t): unit =
  unify tb.rtype (boolean_type tb) tb


let expect_type (tp:type_term) (tb:t): unit =
  let c   = context tb in
  let tvs = Context.tvars c in
  let tp = (transform_from_context tvs tb) tp in
  unify tb.rtype tp tb



let add_global_tvs (tvs:Tvars.t) (tb:t): unit =
  let nglobs = Tvars.count_global tvs in
  resize 0 nglobs 0 tb;
  let tvs_concepts = Tvars.concepts tvs
  and concepts     = Tvars.concepts tb.tvs in
  let start0 = tb.nglobals in
  tb.nglobals <- nglobs + tb.nglobals;
  let import = transform_from_global tvs tb in
  for i = 0 to nglobs - 1 do
    concepts.(start0+i) <- import tvs_concepts.(i)
  done



let callable_signature (s:Sign.t) (tb:t): Sign.t =
  let funrec = Seq.last tb.funstack in
  if Sign.is_constant s then
    let rt = substituted_type (Sign.result s) tb in
    let s =
      match rt with
        Variable i when is_tv i tb  ->
          let tp =
            let start = globals_start tb + tb.nglobals in
            if funrec.pr = 1 then begin
              add_anys 1 tb;
              VAppl(predicate_index tb,[|Variable (start)|])
            end else if funrec.pr = 0 then begin
              add_anys 2 tb;
              VAppl(function_index tb,
                    [|Variable (start); Variable (start+1)|])
            end else begin
              add_anys 2 tb;
              VAppl(dummy_index tb,
                    [|Variable (start); Variable (start+1)|])
            end
          in
          unify tp rt tb;
          Sign.make_const tp
      | _ ->
          Sign.make_const rt
    in
    Class_table.downgrade_signature (Tvars.count_all tb.tvs) s funrec.nargs
  else
    s



let push_term (t:term) (s:Sign.t) (tb:t): unit =
  (* Push the term [t] which is not a leaf *)
  assert (Sign.is_constant s);
  let s1 =
    if is_expecting_function tb then callable_signature s tb else s in
  Seq.push {term = t; sign0 = s; sign = s1} tb.terms



let check_as_function (i:int) (s:Sign.t) (tb:t): unit =
  (* Add [i] to a function position, the signature [s] has already been transformed
     into the builder and downgraded if necessary. The expected type specifies the
     required result type of the function.
   *)
  assert (Sign.has_result s);
  let nargs = (Seq.last tb.funstack).nargs
  and rt    = Sign.result s
  in
  assert (Sign.arity s <= nargs);
  if Sign.arity s <> nargs then
    raise Not_found;
  unify tb.rtype rt tb



let is_predicate (t:type_term) (tb:t): bool =
  let t =
    match t with
      Variable i when is_tv i tb -> tb.subs.(i)
    | _ -> t in
  let cls,_ = Class_table.split_type_term t in
  cls = predicate_index tb


let check_as_argument (i:int) (s:Sign.t) (tb:t): unit =
  assert (Sign.has_result s);
  if Sign.is_constant s then
    unify tb.rtype (Sign.result s) tb
  else begin
    let nall = Tvars.count_all tb.tvs
    and args = Sign.arguments s
    and res  = Sign.result s in
    let tup = Class_table.to_tuple nall 0 args in
    let tp  =
      if is_predicate tb.rtype tb then begin
        if Context.has_preconditions i 0 (context tb) then
          raise Not_found;
        unify (boolean_type tb) res tb;
        VAppl(predicate_index tb,[|tup|])
      end else
        VAppl(function_index tb, [|tup;res|]) in
    unify tb.rtype tp tb
  end



let add_leaf (i:int) (tvs:Tvars.t) (s:Sign.t) (tb:t): unit =
  assert (Sign.has_result s);
  resize 0 0 0 tb;
  Seq.push tb.nglobals tb.gcntseq;
  let transform =
    if Tvars.count_local tvs = 0 && Tvars.count_fgs tvs = 0  then begin
      add_global_tvs tvs tb;
      transform_from_global tvs tb
    end else
      transform_from_context tvs tb in
  let s = Sign.map transform s
  in
  if tb.trace then
    printf "  %s  \"%s\"  %s\n"
      (if is_expecting_function tb then "fun" else "arg")
      (string_of_term (Variable i) tb) (string_of_complete_signature s tb);
  let s1 =
    if is_expecting_function tb then begin
      let s = callable_signature s tb in
      check_as_function i s tb; s
    end else begin
      check_as_argument i s tb; s
    end in
  Seq.push {term = Variable i; sign = s1; sign0 = s} tb.terms


let expect_function (nargs:int) (pr:int) (tb:t): unit =
  if tb.trace then printf "  expect function nargs %d, pr %d\n" nargs pr;
  let pos = Seq.count tb.terms in
  if is_expecting_function tb then begin (* already expecting a function, new function
                                            has to return a predicate or a function *)
    resize 0 (nargs+1) 0 tb;
    let funrec = Seq.last tb.funstack in
    let start  = globals_start tb + tb.nglobals in
    add_anys (funrec.nargs + (if funrec.pr = 1 then 0 else 1)) tb;
    let args = Array.init funrec.nargs (fun i -> Variable (start+i)) in
    let tup  = Class_table.to_tuple (Tvars.count_all tb.tvs) 0 args in
    tb.rtype <-
      if funrec.pr = 1 then begin
        unify tb.rtype (boolean_type tb) tb;
        VAppl(predicate_index tb, [|tup|])
      end else if funrec.pr = 0 then begin
        unify tb.rtype (Variable (start+funrec.nargs)) tb;
        VAppl(function_index tb,[|tup;Variable (start+funrec.nargs)|])
      end else begin
        unify tb.rtype (Variable (start+funrec.nargs)) tb;
        VAppl(dummy_index tb,[|tup;Variable (start+funrec.nargs)|])
      end
  end;
  Seq.push {pos = pos; nargs = nargs; pr = pr; level = tb.level} tb.funstack


let expect_argument (tb:t): unit =
  if tb.trace then printf "  expect argument\n";
  let pos    = Seq.count tb.terms
  and funrec = Seq.last tb.funstack in
  let argi   = pos - funrec.pos - 1 in
  assert (0 <= argi);
  assert (argi < funrec.nargs);
  let s = (Seq.elem funrec.pos tb.terms).sign in
  assert (Sign.arity s = funrec.nargs);
  tb.rtype <- Sign.arg_type argi s


let complete_function (tb:t): unit =
  resize 0 0 0 tb;
  let funrec = Seq.pop_last tb.funstack in
  let frec = Seq.elem funrec.pos tb.terms
  and args = Array.init funrec.nargs
      (fun i -> (Seq.elem (funrec.pos + 1 + i) tb.terms).term) in
  Seq.pop (1 + funrec.nargs) tb.terms;
  let term =
    if Sign.is_constant frec.sign0 then
      let rt = substituted_type (Sign.result frec.sign0) tb in
      let cls,_ = Class_table.split_type_term rt in
      let pr = (cls = predicate_index tb) in
      Application(frec.term, args, pr)
    else begin
      assert (Term.is_variable frec.term);
      VAppl (Term.variable frec.term, args)
    end
  and s0 = Sign.make_const (Sign.result frec.sign)
  in
  if tb.trace then
    printf "  call \"%s\"  %s\n" (string_of_term term tb)
      (string_of_complete_signature s0 tb);
  push_term term s0 tb


let expect_if (tb:t): unit =
  if tb.trace then printf "  expect if\n";
  tb.level <- tb.level + 1

let complete_if (has_else:bool) (tb:t): unit =
  resize 0 0 0 tb;
  get_expected 0 tb;
  let args =
    let cnt = Seq.count tb.terms in
    if has_else then begin
      assert (cnt >= 3);
      let cond = (Seq.elem (cnt-3) tb.terms).term
      and t1   = (Seq.elem (cnt-2) tb.terms).term
      and t2   = (Seq.elem (cnt-1) tb.terms).term in
      Seq.pop 3 tb.terms;
      [|cond;t1;t2|]
    end else begin
      assert (cnt >= 2);
      let cond = (Seq.elem (cnt-2) tb.terms).term
      and t1   = (Seq.elem (cnt-1) tb.terms).term in
      Seq.pop 2 tb.terms;
      [|cond;t1|]
    end in
  let t = Flow(Ifexp,args)
  and s = Sign.make_const tb.rtype in
  if tb.trace then
    printf "  \"%s\"  %s\n" (string_of_term t tb)
      (string_of_complete_signature s tb);
  tb.level <- tb.level - 1;
  push_term t s tb


let expect_as (tb:t): unit =
  if tb.trace then printf "  expect as\n";
  tb.level <- tb.level + 1

let complete_as (tb:t): unit =
  resize 0 0 0 tb;
  let nms = Context.local_argnames (context tb) in
  let n   = Array.length nms in
  let start = count_terms tb - 2 in
  assert (0 <= start);
  let exp = ith_term start tb
  and pat = ith_term (start+1) tb in
  get_expected 1 tb;
  let tp = tb.rtype in
  Seq.pop 2 tb.terms;
  tb.level <- tb.level - 1;
  pop_context tb;
  let t = Flow(Asexp,[|exp; Term.pattern n nms pat|]) in
  if tb.trace then
    printf "  \"%s\"  %s\n"
      (string_of_term t tb) (string_of_complete_type tp tb);
  push_term t (Sign.make_const tp) tb


let expect_inspect (tb:t): unit =
  if tb.trace then printf "  expect inspect\n";
  tb.level <- tb.level + 1

let expect_case (c:Context.t) (tb:t): unit =
  push_context c tb

let complete_case (tb:t): unit =
  resize 0 2 0 tb;
  let nms = Context.local_argnames (context tb) in
  let n   = Array.length nms in
  pop_context tb;
  get_expected 1 tb;
  let tp_res = tb.rtype in
  get_expected 0 tb;
  let tp_pat = tb.rtype in
  let start = Seq.count tb.terms - 2 in
  assert (0 <= start);
  let pat = Term.pattern n nms (Seq.elem start tb.terms).term
  and res = Term.pattern n nms (Seq.elem (start+1) tb.terms).term in
  Seq.pop 2 tb.terms;
  push_term pat (Sign.make_const tp_pat) tb;
  push_term res (Sign.make_const tp_res) tb



let complete_inspect (ncases:int) (tb:t): unit =
  resize 0 0 0 tb;
  let start = Seq.count tb.terms - (2*ncases+1) in
  assert (0 <= start);
  let args = Array.make (2*ncases+1) (Variable (-1)) in
  args.(0) <- ith_term start tb;
  for i = 0 to ncases - 1 do
    args.(2*i+1) <- ith_term (start+2*i+1) tb;
    args.(2*i+2) <- ith_term (start+2*i+2) tb
  done;
  get_expected 1 tb;
  let t = Flow(Inspect,args)
  and s = Sign.make_const tb.rtype in
  if tb.trace then
    printf "  \"%s\"  %s\n"
      (string_of_term t tb) (string_of_complete_type tb.rtype tb);
  tb.level <- tb.level - 1;
  Seq.pop (2*ncases+1) tb.terms;
  push_term t s tb



let upgraded_signature (s:Sign.t) (is_pred:bool) (tb:t): type_term =
  (* The signature [s] upgraded to a predicate or a function. *)
  assert (Sign.has_result s);
  if Sign.is_constant s then
    Sign.result s
  else
    let ntvs = Tvars.count_all tb.tvs  in
    Class_table.upgrade_signature ntvs is_pred s



let expect_lambda (is_pred:bool) (c:Context.t) (tb:t): unit =
  let nargs = Context.count_last_arguments c in
  if tb.trace then printf "  expect lambda (%s) nargs %d\n"
      (if is_pred then "predicate" else "function") nargs;
  let nanys = nargs + if is_pred then 0 else 1
  and expfun = is_expecting_function tb in
  resize 0 nanys 0 tb;
  add_anys nanys tb;
  push_context c tb;
  let csig = context_signature tb in
  assert (Sign.arity csig = nargs);
  let start = globals_start tb + tb.nglobals - nanys in
  let args = Array.init nargs (fun i -> Variable (start+i)) in
  let rsig = Sign.make_func args tb.rtype in
  let rtype = upgraded_signature rsig is_pred tb in
  for i = 0 to nargs - 1 do
    unify (Sign.arg_type i csig) (Variable (start+i)) tb done;
  if not is_pred then
    unify (Sign.result csig) (Variable (start+nargs)) tb;
  let t2 =
    if expfun then Sign.result csig
    else upgraded_signature csig is_pred tb in
  unify tb.rtype t2 tb;
  Seq.push rtype tb.lamstack;
  tb.rtype <- Sign.result csig



let complete_lambda (n:int) (nms:int array) (npres:int) (is_pred:bool) (tb:t)
    : unit =
  (* stack: ... t0 p0 p1 p2 ...
   *)
  resize 0 0 0 tb;
  let pos_t0 = Seq.count tb.terms - npres - 1 in
  assert (0 <= pos_t0);
  let term i = (Seq.elem i tb.terms).term in
  let t0 = term pos_t0
  and pres =
    let pos_last = pos_t0 + npres  in
    interval_fold (fun lst i -> term (pos_last-i) :: lst)
      [] 0 npres in
  let lam = Lam (n,nms,pres,t0,is_pred) in
  Seq.keep pos_t0 tb.terms;
  pop_context tb;
  let s = Sign.make_const (Seq.pop_last tb.lamstack) in
  if tb.trace then
    printf "  lam  \"%s\"  %s\n" (string_of_term lam tb)
      (string_of_complete_signature s tb);
  push_term lam s tb


let expect_quantified (c:Context.t) (tb:t): unit =
  if tb.trace then printf "  expect quantified\n";
  push_context c tb;
  expect_boolean tb


let complete_quantified (is_all:bool) (tb:t): unit =
  resize 0 0 0 tb;
  let names = Context.local_argnames (context tb) in
  let nargs = Array.length names in
  assert (0 < nargs);
  pop_context tb;
  let trec = Seq.pop_last tb.terms in
  let term =
    if IntSet.cardinal (Term.bound_variables trec.term nargs) <> nargs then
      raise Not_found;
    if is_all then
      Term.all_quantified nargs names  trec.term
    else
      Term.some_quantified nargs names  trec.term
  in
  if tb.trace then
    printf "  qexp \"%s\"  %s\n" (string_of_term term tb)
      (string_of_complete_signature trec.sign tb);
  push_term term trec.sign tb




let variant (idx:int) (gcnt:int) (nb:int) (tb:t): int =
  let c = context tb in
  let nvars = nb + Context.count_variables c in
  if idx < nvars then
    idx
  else
    let ft = Context.feature_table c in
    let nfgs = Feature_table.count_fgs (idx-nvars) ft in
    if nfgs = 0 then
      idx
    else
      let gstart0 = globals_start tb in
      let ags = Array.init nfgs (fun i -> tb.subs.(gstart0+gcnt+i)) in
      let idx = try
        Feature_table.variant_feature idx nvars ags tb.tvs ft
      with Not_found ->
        printf "no variant found for %s\n"
          (Feature_table.string_of_signature (idx-nvars) ft);
        printf "  substitution(s)\n";
        Array.iter (fun tp ->
          printf "    %s\n"
            (string_of_reduced_complete_type tp tb))
          ags;
        assert false in
      idx



let specialize_head (tb:t): unit =
  assert (Seq.count tb.terms = 1);
  let rec spec (t:term) (gpos:int) (nb:int): term * int =
    let spec_args (args:term array) (gpos:int) (nb:int): term array * int =
      let len = Array.length args in
      let args1  = Array.make len (Variable 0) in
      let i,gpos1 =
        Array.fold_left
          (fun (i,gpos1) arg ->
            let t,gpos2 = spec arg gpos1 nb in
            args1.(i)  <- t;
            i+1,gpos2)
          (0,gpos)
          args in
      assert (i = len);
      args1, gpos1
    and spec_lst (lst:term list) (gpos:int) (nb:int): term list * int =
      let gpos,lst =
        List.fold_left
          (fun (gpos,lst) t ->
            let t,gpos = spec t gpos nb in
            gpos, t::lst)
          (gpos,[])
          lst in
      List.rev lst, gpos
    in
    match t with
      Variable i ->
        let gcnt = Seq.elem gpos tb.gcntseq in
        let idx = variant i gcnt nb tb in
        Variable idx, (gpos+1)
    | VAppl (idx,args) ->
        let gcnt = Seq.elem gpos tb.gcntseq in
        let idx1 = variant idx gcnt nb tb in
        let args1, gpos = spec_args args (gpos+1) nb in
        VAppl(idx1,args1), gpos
    | Application (f,args,pr) ->
        let f1,gpos  = spec f gpos nb in
        let args1,gpos = spec_args args gpos nb in
        Application(f1,args1,pr), gpos
    | Lam (n,nms,pres,t0,pr) ->
        let nb = (if tb.norm then 1 else n) + nb in
        let t0,gpos = spec t0 gpos nb in
        let pres,gpos = spec_lst pres gpos nb in
        Lam(n,nms,pres,t0,pr), gpos
    | QExp (n,nms,t0,is_all) ->
        let nb = n + nb in
        let t0,gpos = spec t0 gpos nb in
        QExp(n,nms,t0,is_all), gpos
    | Flow(ctrl,args) ->
        let args,gpos = spec_args args gpos nb in
        Flow(ctrl,args), gpos
  in
  let trec = Seq.elem 0 tb.terms in
  let t,gpos = spec trec.term 0 0 in
  assert (gpos = Seq.count tb.gcntseq);
  Seq.put 0 {trec with term = t} tb.terms



let normalized_result (tb:t): term =
  assert (Seq.count tb.terms = 1);
  let res = head_term tb in
  let c = context tb in
  let ft = Context.feature_table c
  and nb = Context.count_variables c in
  Feature_table.normalize_lambdas res nb ft

exception Illegal_term

let check_term (t:term) (tb:t): unit =
  let rec check (t:term) (tb:t): unit =
    let c0 = context tb in
    let lambda n nms pres t is_pred tb =
      assert (0 < n);
      assert (Array.length nms = n);
      let nms0 = if n > 1 then [|ST.symbol "$0"|] else nms in
      let ntvs_gap = count_local tb - Context.count_type_variables c0
      and is_func = not is_pred in
      let c = Context.push_untyped_with_gap nms0 is_pred is_func false ntvs_gap c0
      in
      expect_lambda is_pred c tb;
      check t tb;
      let rec check_pres (pres:term list) (npres:int) (tb:t): int =
        match pres with
          [] -> npres
        | p::pres ->
            expect_boolean_expression tb;
            check p tb;
            check_pres pres (npres+1) tb
      in
      let npres = check_pres pres 0 tb in
      begin try
        complete_lambda n nms npres is_pred tb
      with Not_found -> assert false
      end
    and qlambda n nms t is_all tb =
      assert (0 < n);
      assert (Array.length nms = n);
      let ntvs_gap = count_local tb - Context.count_type_variables c0 in
      let c = Context.push_untyped_with_gap nms false false false ntvs_gap c0 in
      expect_quantified c tb;
      check t tb;
      begin try
        complete_quantified is_all tb
      with Not_found ->
        assert false
      end
    and add_lf i =
      let tvs,s = Context.variable_data i c0 in
      begin
        try add_leaf i tvs s tb
        with Not_found ->
          let ct = Context.class_table c0 in
          printf "illegal term \"%s\" \"%s\" %s%s\n"
            (string_of_term t tb) (Term.to_string t)
            (string_of_tvs tb) (string_of_substitutions tb);
          printf "  type     %s\n"
            (Class_table.string_of_complete_signature s tvs ct);
          printf "  expected %s\n" (string_of_type tb.rtype tb);
          raise Illegal_term
      end
    in
    match t with
      Variable i ->
        add_lf i
    | VAppl(i,args) ->
        let nargs = Array.length args in
        expect_function nargs (-1) tb;
        add_lf i;
        Array.iter (fun a -> expect_argument tb; check a tb) args;
        complete_function tb
    | Application (f,args,pr) ->
        let nargs = Array.length args
        and pr    = if pr then 1 else 0 in
        assert (nargs = 1);
        expect_function nargs pr tb;
        check f tb;
        expect_argument tb;
        check args.(0) tb;
        complete_function tb
    | Lam(n,nms,pres,t0,is_pred) ->
        assert (0 < n);
        assert (n = Array.length nms);
        lambda n nms pres t0 is_pred tb
    | QExp(n,nms,t0,is_all) ->
        assert (n = Array.length nms);
        qlambda n nms t0 is_all tb
    | Flow (ctrl,args) ->
        let len = Array.length args in
        begin
          match ctrl with
            Ifexp ->
              assert (2 <= len);
              assert (len <= 3);
              expect_if tb;
              push_expected tb;
              expect_boolean_expression tb;
              check args.(0) tb;
              get_expected 0 tb;
              check args.(1) tb;
              let has_else =
                if len = 3 then begin
                  get_expected 0 tb;
                  check args.(2) tb;
                  true
                end else false in
              complete_if has_else tb;
              drop_expected tb
          | Inspect ->
              assert (3 <= len);
              assert (len mod 2 = 1);
              let ncases = len / 2 in
              let rec do_cases_from (i:int) (tb:t): unit =
                if i = ncases then
                  ()
                else
                  let n, nms, pat,res = Term.case_split args.(2*i+1) args.(2*i+2)
                  and ntvs_gap = count_local tb - Context.count_type_variables c0
                  in
                  let c1 = Context.push_untyped_gap nms ntvs_gap c0 in
                  expect_case c1 tb;
                  get_expected 0 tb;
                  check pat tb;
                  get_expected 1 tb;
                  check res tb;
                  complete_case tb;
                  do_cases_from (i+1) tb
              in
              expect_inspect tb;
              push_expected tb;
              expect_new_untyped tb;
              push_expected tb;
              check args.(0) tb;
              do_cases_from 0 tb;
              complete_inspect ncases tb;
              drop_expected tb;
              drop_expected tb
          | Asexp ->
              expect_boolean tb;
              expect_as tb;
              push_expected tb;
              expect_new_untyped tb;
              push_expected tb;
              check args.(0) tb;
              let n, nms, pat = Term.pattern_split args.(1)
              and ntvs_gap = count_local tb - Context.count_type_variables c0 in
              let c1 = Context.push_untyped_gap nms ntvs_gap c0 in
              expect_case c1 tb;
              get_expected 0 tb;
              check pat tb;
              complete_as tb;
              drop_expected tb;
              drop_expected tb
        end
  in
  let depth = Context.depth (context tb) in
  check t tb;
  assert (depth = Context.depth (context tb))



let pool = ref []

let occupy (c:Context.t): t =
  let tb = match !pool with
    [] -> make ()
  | h::t -> pool := t; h in
  init c tb;
  tb



let occupy_boolean (c:Context.t): t =
  let tb = occupy c in
  expect_boolean_expression tb;
  tb


let occupy_untyped (c:Context.t): t =
  let tb = occupy c in
  expect_new_untyped tb;
  tb


let occupy_context (c:Context.t): t =
  assert (Context.has_result c);
  let tb = occupy c in
  let trans = transform_from_context (Context.tvars c) tb in
  tb.rtype <- trans (Context.result_type c);
  tb


let occupy_typed (tp:type_term) (c:Context.t): t =
  let tb = occupy c in
  let trans = transform_from_context (Context.tvars c) tb in
  tb.rtype <- trans tp;
  tb


let occupy_term (t:term) (c:Context.t): t =
  let tb = occupy c in
  tb.norm <- true;
  expect_new_untyped tb;
  check_term t tb;
  tb


let release (tb:t): unit =
  reset tb;
  pool := tb :: !pool



let update_context (tb:t): unit =
  assert (Seq.count tb.constack = 1);
  assert (Seq.count tb.terms = 1);
  let c    = context tb in
  let tvs  = Context.tvars c in
  let ntvs = Tvars.count_local tvs in
  let nfgs = Tvars.count_fgs tvs in
  assert (Tvars.count_global tvs = 0);
  assert (ntvs <= tb.nlocals);
  assert(nfgs = tb.nfgs);
  let loc_start  = locals_start tb + (tb.nlocals - ntvs)
  and glob_start = globals_start tb in
  let space2     = Tvars.count_all tb.tvs - nfgs - glob_start in
  try
    let subs = Array.init ntvs
        (fun i ->
          if has_sub (loc_start+i) tb then
            let sub = tb.subs.(loc_start+i) in
            let sub = Term.down_from space2 glob_start sub in
            Term.down loc_start sub
          else
            Variable i)
    in
    Context.update_types subs c
  with Term_capture ->
    not_yet_implemented (Context.info c) "Type inference of formal generics"


let specialize (t:term) (c:Context.t): term =
  let tb = occupy_untyped c in
  tb.norm <- true;
  if tb.trace then begin
    printf "specialize \"%s\" \"%s\"\n" (string_of_term t tb) (Term.to_string t);
    printf "  %s\n" (string_of_tvs tb);
    printf "  %s\n" (string_of_substitutions tb)
  end;
  let t0 = Feature_table.seeded_term t
      (Context.count_variables c) (Context.feature_table c) in
  check_term t0 tb;
  specialize_head tb;
  let t1 = head_term tb in
  if not (Term.equivalent t t1) then begin
    printf "t   %s  %s\n" (string_of_term t tb) (Term.to_string t);
    printf "t1  %s  %s\n" (string_of_term t1 tb)
      (Term.to_string t1)
  end;
  assert (Term.equivalent t t1);
  release tb;
  t1




let is_valid (t:term) (c:Context.t): bool =
  try
    let _ = specialize t c in true
  with Not_found ->
    printf "invalid term %s\n" (Context.string_of_term t true 0 c);
    false
