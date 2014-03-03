open Container
open Signature
open Term
open Support



type t = {
    fgnames:   int array;           (* cumulated        *)
    concepts:  type_term array;     (* cumulated        *)
    argnames:  int array;           (* cumulated        *)
    argtypes:  type_term array;     (* cumulated        *)
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
  let i = Search.array_find_min name loc.argnames in
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



let tvars_sub (loc:t): TVars_sub.t = loc.tvars_sub

let boolean (loc:t): term =
  Class_table.boolean_type (ntvs loc)

let update_type_variables (tvs:TVars_sub.t) (loc:t): unit =
  (** Update the type variables of the current context with [tvs]
   *)
  try
    TVars_sub.update loc.tvars_sub tvs
  with Term_capture ->
    assert false (* nyi: assignment of constraints to type variables *)


let string_of_term (t:term) (loc:t): string =
  Feature_table.term_to_string t loc.argnames loc.ft

let sign2string (s:Sign.t) (loc:t): string =
  Class_table.string_of_signature
    s
    (count_type_variables loc)
    loc.fgnames
    loc.ct

let signature_string (loc:t): string =
  sign2string loc.signature loc

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
