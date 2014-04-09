open Container
open Signature
open Term
open Proof
open Support



type t = {
    fgnames:   int array;           (* cumulated        *)
    concepts:  type_term array;     (* cumulated        *)
    argnames:  int array;           (* cumulated        *)
    argtypes:  type_term array;     (* cumulated        *)
    info:      info;
    mutable signature: Sign.t;      (* from declaration *)
    mutable tvars_sub: TVars_sub.t; (* cumulated        *)
    is_basic:     bool;
    mutable visi: visibility;
    ct:           Class_table.t;
    ft:           Feature_table.t;
    at:           Assertion_table.t;
  }


let make_basic (): t =
  {fgnames  = [||];
   concepts = [||];
   argnames = [||];
   argtypes = [||];
   info      = UNKNOWN;
   signature = Sign.empty;
   tvars_sub = TVars_sub.make 0;
   is_basic  = true;
   visi      = Public;
   ct        = Class_table.base_table ();
   ft        = Feature_table.base_table ();
   at        = Assertion_table.empty ()}


let make_next
    (entlst: entities list withinfo)
    (rt: return_type)
    (loc: t)
    : t =
  (** Make a next local context with the argument list [entlst] and the
      return type [rt] based on previous local global context [loc]
   *)
  let fgnames, concepts, argnames, argtypes, ntvs, sign =
    let ntvs0 = TVars_sub.count_local loc.tvars_sub in
    Class_table.signature entlst rt
      loc.fgnames loc.concepts loc.argnames loc.argtypes ntvs0 loc.ct
  in
  {fgnames   =  fgnames;
   concepts  =  concepts;
   argnames  =  argnames;
   argtypes  =  argtypes;
   info      =  entlst.i;
   signature =  sign;
   tvars_sub =  TVars_sub.add_local ntvs loc.tvars_sub;
   is_basic  =  false;
   visi      =  loc.visi;
   ct        =  loc.ct;
   ft        =  loc.ft;
   at        =  loc.at}



let arity     (loc:t): int = Sign.arity loc.signature

let argument (name:int) (loc:t): int * TVars.t * Sign.t =
  (** The term and the signature of the argument named [name] *)
  let i = Search.array_find_min (fun n -> n=name) loc.argnames in
  i, TVars_sub.tvars loc.tvars_sub, Sign.argument i loc.signature
    (* bug: argnames are cumulated and signature not!! *)


let has_result (loc:t): bool =
  Sign.has_result loc.signature

let result_type (loc:t): type_term =
  (** The result type of the context
   *)
  assert (has_result loc);
  Sign.result loc.signature

let count_type_variables (loc:t): int =
  (** The number of cumulated type variables in this context and all
      preceeding contexts
   *)
  TVars_sub.count loc.tvars_sub


let nfgs (loc:t): int =
  (** The cumulated number of formal generics in this context and all
      previous contexts
   *)
  Array.length loc.fgnames

let nargs (loc:t): int =
  (** The cumulated number of formal arguments in this context and all
      previous contexts
   *)
  Array.length loc.argnames

let ntvs (loc:t): int =
  (** The cumulated number of formal generics and type variables in
      this context and all previous contexts
   *)
  (nfgs loc) + (count_type_variables loc)


let fgnames (loc:t): int array=
  (** The cumulated formal generic names of this context and all
      previous contexts
   *)
  loc.fgnames


let ct (loc:t): Class_table.t    = loc.ct
let ft (loc:t): Feature_table.t  = loc.ft
let at (g:t): Assertion_table.t  = g.at

let is_basic (loc:t): bool =  loc.is_basic

let is_private (loc:t): bool =
  match loc.visi with
    Private -> true
  | _ -> false

let is_public (loc:t): bool = not (is_private loc)

let set_visibility (v:visibility) (loc:t): unit =
  assert (is_basic loc);
  loc.visi <- v

let reset_visibility (loc:t): unit =
  assert (is_basic loc);
  loc.visi <- Public



let type_variables (loc:t): TVars_sub.t = loc.tvars_sub

let boolean (loc:t): term =
  Class_table.boolean_type (ntvs loc)


let update_type_variables (tvs:TVars_sub.t) (loc:t): unit =
  (** Update the type variables of the current context with [tvs]
   *)
  try
    TVars_sub.update loc.tvars_sub tvs
  with Term_capture ->
    not_yet_implemented loc.info "Type inference of formal generics"




let string_of_term (t:term) (loc:t): string =
  Feature_table.term_to_string t loc.argnames loc.ft



let sign2string (s:Sign.t) (loc:t): string =
  Class_table.string_of_signature
    s
    (count_type_variables loc)
    loc.fgnames
    loc.ct



let signature_string (loc:t): string =
  (** Print the signature of the context [loc].
   *)
  sign2string loc.signature loc



let named_signature_string (loc:t): string =
  (** Print the signature of the context [loc] with all argument names.
   *)
  let nargs = arity loc in
  let has_res = has_result loc
  and has_args = (nargs <> 0) in
  let argsstr =
    if not has_args then
      ""
    else
      let zipped = Array.to_list (Array.init nargs
                                    (fun i ->
                                      loc.argnames.(i), loc.argtypes.(i)))
      in
      let llst = List.fold_left
          (fun ll (n,tp) -> match ll with
            [] -> [[n],tp]
          | (ns,tp1)::tl ->
              if tp=tp1 then [n::ns,tp]
              else           ([n],tp)::ll )
          []
          zipped
      in
      "("
      ^  String.concat
          ","
          (List.rev_map
             (fun (ns,tp) ->
               (String.concat "," (List.rev_map (fun n -> ST.string n) ns))
               ^ ":"
               ^ (Class_table.type2string tp 0 loc.fgnames loc.ct))
             llst)
      ^ ")"
  and resstr =
    if has_res then
      Class_table.type2string (result_type loc) 0 loc.fgnames loc.ct
    else ""
  in
  if has_args && has_res then argsstr ^ ": " ^ resstr
  else if has_args then       argsstr
  else                        resstr






let put_global_function
    (fn:       feature_name withinfo)
    (is_priv:  bool)
    (impstat:  Feature_table.implementation_status)
    (term_opt: term option)
    (loc:      t)
    : unit =
  Feature_table.put_function
    fn
    loc.fgnames
    loc.concepts
    loc.argnames
    loc.signature
    is_priv
    impstat
    term_opt
    loc.ft


let implication_id (loc:t): int =
  Feature_table.implication_index + (nargs loc)


let string_of_assertion (t:term) (loc: t): string =
  "all"
  ^ (named_signature_string loc) ^ " "
  ^ (string_of_term t loc)


let put_global_assertion
    (t:term) (pt_opt: proof_term option) (loc:t): unit =
  (** Put the assertion [t] with its optional proof term [pt_opt]
      into the global assertion table.
   *)
  Printf.printf "%3d %s  %s\n"
    (Assertion_table.count loc.at)
    (match pt_opt with
      None    -> "axiom "
    | Some pt -> "proved")
    (string_of_assertion t loc);
  Assertion_table.put_assertion t (arity loc) pt_opt loc.ft loc.at


let put_formal_generic
    (name:int withinfo)
    (concept:type_t withinfo)
    (loc:t)
    : unit =
  (** Add the formal generic [name] with its [concept] to the formal
      generics.
   *)
  assert (is_basic loc);
  Class_table.put_formal name concept loc.ct



let put_class (hm:header_mark withinfo) (cn:int withinfo) (loc:t): unit =
  assert (is_basic loc);
  Class_table.put hm cn loc.ct





let find_funcs
    (fn:feature_name) (nargs:int)
    (nfgs:int) (nvars:int)
    (ft:Feature_table.t)
    : (int*TVars.t*Sign.t) list =
  let lst = Feature_table.find_funcs fn nargs ft
  in
  let lst = List.rev_map
      (fun (i,tvs,s) ->
        let start = TVars.count tvs in
        i+nvars, tvs, Sign.up_from nfgs start s)
      lst
  in
  lst

exception Wrong_signature

let find_identifier
    (name:int)
    (nargs_id:int)
    (loc:t)
    : (int * TVars.t * Sign.t) list =
  (** Find the identifier named [name] which accepts [nargs] arguments
      in one of the local contexts or in the global feature table. Return
      the list of variables together with their signature
   *)
  let nfgs_c0  = nfgs loc
  and nargs_c0 = nargs loc
  in
  if is_basic loc then
    find_funcs (FNname name) nargs_id nfgs_c0 nargs_c0 loc.ft
  else
    try
      let i,tvs,s = argument name loc
      in
      if (Sign.arity s) = nargs_id then begin
        [i,tvs,s]
      end else
        raise Wrong_signature
    with
      Not_found ->
        find_funcs
          (FNname name) nargs_id nfgs_c0 nargs_c0 loc.ft
    | Wrong_signature ->
        raise Not_found



let find_feature
    (fn:feature_name)
    (nargs_feat:int)
    (loc:t)
    : (int * TVars.t * Sign.t) list =
  (** Find the feature named [fn] which accepts [nargs] arguments global
      feature table. Return the list of variables together with their
      signature.
   *)
  let nfgs_c0  = nfgs loc
  and nargs_c0 = nargs loc
  in
  find_funcs fn nargs_feat nfgs_c0 nargs_c0 loc.ft
