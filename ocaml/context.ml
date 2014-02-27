open Container
open Term
open Signature
open Support





module Global_context: sig

  type t
  val make: unit -> t
  val is_private: t -> bool
  val is_public:  t -> bool
  val set_visibility: visibility -> t -> unit
  val reset_visibility: t -> unit
  val ct:  t -> Class_table.t
  val ft:  t -> Feature_table.t
  val at:  t -> Assertion_table.t
  val string_of_term: term -> t -> string
  val sign2string: Sign.t -> t -> string
end = struct
  type t = {
      mutable visi: visibility;
      ct: Class_table.t;
      ft: Feature_table.t;
      at: Assertion_table.t;
    }

  let make (): t =
    {visi = Public;
     ct = Class_table.base_table ();
     ft = Feature_table.empty ();
     at = Assertion_table.empty ()}

  let is_private (g:t): bool =
    match g.visi with
      Private -> true
    | _ -> false

  let is_public (g:t): bool = not (is_private g)

  let set_visibility (v:visibility) (g:t): unit =  g.visi <- v

  let reset_visibility (g:t): unit =  g.visi <- Public

  let ct (g:t): Class_table.t      = g.ct
  let ft (g:t): Feature_table.t    = g.ft
  let at (g:t): Assertion_table.t  = g.at

  let string_of_term (t:term) (g:t): string =
    Feature_table.term_to_string t [||]  g.ft

  let sign2string (s:Sign.t) (g:t): string =
    Class_table.string_of_signature s 0 [||] g.ct

end (* Global_context *)








module Local_context: sig

  type t
  val make_first:
      entities list withinfo -> return_type -> Global_context.t -> t
  val make_next:
      entities list withinfo -> return_type -> t -> t
  val arity:     t -> int
  val argument:  int -> t -> int * TVars.t * Sign.t

  val result_type: t -> type_term

  val count_type_variables: t -> int

  val nfgs:    t -> int
  val nargs:   t -> int
  val fgnames: t -> int array
  val ct:      t -> Class_table.t
  val ft:      t -> Feature_table.t

  val tvars_sub: t -> TVars_sub.t

  val boolean: t -> term

  val update_type_variables: TVars_sub.t -> t -> unit

  val string_of_term: term -> t -> string
  val sign2string:    Sign.t -> t -> string

  val put_global_function:
      feature_name withinfo -> bool -> Feature_table.implementation_status ->
        term option -> t -> unit

end = struct

  type t = {
      fgnames:   int array;           (* cumulated        *)
      concepts:  type_term array;     (* cumulated        *)
      argnames:  int array;           (* cumulated        *)
      mutable signature: Sign.t;      (* from declaration *)
      mutable tvars_sub: TVars_sub.t; (* cumulated        *)
      ct:        Class_table.t;
      ft:        Feature_table.t
    }


  let make_first
      (entlst: entities list withinfo)
      (rt: return_type)
      (g: Global_context.t)
      : t =
    (** Make a first local context with the argument list [entlst] and the
        return type [rt] based on the global context [g]
     *)
    let ct = Global_context.ct g
    and ft = Global_context.ft g in
    let fgnames, concepts, argnames, ntvs, sign =
      Class_table.signature entlst rt [||] [||] [||] 0 ct
    in
    {fgnames    =  fgnames;
     concepts   =  concepts;
     argnames   =  argnames;
     signature  =  sign;
     tvars_sub  =  TVars_sub.make ntvs;
     ct         =  ct;
     ft         =  ft}



  let make_next
      (entlst: entities list withinfo)
      (rt: return_type)
      (loc: t)
      : t =
    (** Make a next local context with the argument list [entlst] and the
        return type [rt] based on previous local global context [loc]
     *)
    let fgnames, concepts, argnames, ntvs, sign =
      let ntvs0 = TVars_sub.count_local loc.tvars_sub in
      Class_table.signature entlst rt
        loc.fgnames loc.concepts loc.argnames ntvs0 loc.ct
    in
    {fgnames   =  fgnames;
     concepts  =  concepts;
     argnames  =  argnames;
     signature =  sign;
     tvars_sub =  TVars_sub.add_local ntvs loc.tvars_sub;
     ct        =  loc.ct;
     ft        =  loc.ft}


  let arity     (loc:t): int = Sign.arity loc.signature

  let argument (name:int) (loc:t): int * TVars.t * Sign.t =
    (** The term and the signature of the argument named [name] *)
    let i = Search.array_find_min name loc.argnames in
    i, TVars_sub.tvars loc.tvars_sub, Sign.argument i loc.signature


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

  let ct (loc:t): Class_table.t = loc.ct

  let ft (loc:t): Feature_table.t = loc.ft

  let tvars_sub (loc:t): TVars_sub.t = loc.tvars_sub

  let boolean (loc:t): term =
    Class_table.boolean_type (ntvs loc)

  let update_type_variables (tvs:TVars_sub.t) (loc:t): unit =
    (** Update the type variables of the current context with [tvs]
     *)
    let nloc1  = TVars_sub.count_local  tvs
    and nloc2  = TVars_sub.count_local  loc.tvars_sub
    and nglob1 = TVars_sub.count_global tvs
    and nglob2 = TVars_sub.count_global loc.tvars_sub
    in
    assert (nloc1 = nloc2);
    assert (nglob1 >= nglob2);
    loc.tvars_sub <- tvs;
    loc.signature <- Sign.up_from (nglob1-nglob2) nglob2 loc.signature

  let string_of_term (t:term) (loc:t): string =
    Feature_table.term_to_string t loc.argnames loc.ft

  let sign2string (s:Sign.t) (loc:t): string =
    Class_table.string_of_signature
      s
      (count_type_variables loc)
      loc.fgnames
      loc.ct

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
end (* Local_context *)







module Context: sig

  type t

  val make:  unit -> t

  val is_basic:     t -> bool
  val global:       t -> Global_context.t
  val local:        t -> Local_context.t
  val is_public:    t -> bool
  val is_private:   t -> bool
  val set_visibility:   visibility -> t -> unit
  val reset_visibility: t -> unit
  val string_of_term: term -> t -> string
  val sign2string:  Sign.t -> t -> string
  val boolean:      t -> term
  val count_formals: t -> int * int
  val push: entities list withinfo -> return_type -> t -> t
  val put_function:
      feature_name withinfo -> Feature_table.implementation_status
        -> term option -> t -> unit


  val put_formal_generic: int withinfo -> type_t withinfo -> t -> unit
  val put_class: header_mark withinfo -> int withinfo -> t -> unit

  val print: t -> unit

  val find_identifier: int -> int -> t
    -> (int * TVars.t * Sign.t) list * int * int

  val find_feature:    feature_name -> int -> t
    -> (int * TVars.t * Sign.t) list * int * int

  val type_variables:  t -> TVars_sub.t

  val update_type_variables: TVars_sub.t -> t -> unit

end = struct


  type t =
      Basic    of Global_context.t
    | Combined of Local_context.t * t


  let make (): t =
    Basic (Global_context.make ())


  let rec global (c:t): Global_context.t =
    match c with
      Basic g -> g
    | Combined (_,c) -> global c


  let is_basic (c:t): bool =
    match c with
      Basic _ -> true
    | _       -> false


  let local (c:t): Local_context.t =
    assert (not (is_basic c));
    match c with
      Basic _ -> assert false
    | Combined (loc,_) -> loc


  let is_private (c:t): bool =
    Global_context.is_private (global c)


  let is_public (c:t): bool =
    Global_context.is_public (global c)


  let set_visibility (v:visibility) (c:t): unit =
    assert (is_basic c);
    match c with
      Basic g -> Global_context.set_visibility v g
    | _       -> assert false (* illegal path *)


  let reset_visibility (c:t): unit =
    assert (is_basic c);
    match c with
      Basic g -> Global_context.reset_visibility g
    | _       -> assert false (* illegal path *)



  let string_of_term (t:term) (c:t): string =
    match c with
      Basic g          -> Global_context.string_of_term t g
    | Combined (loc,c) -> Local_context.string_of_term t loc

  let sign2string (s:Sign.t) (c:t): string =
    match c with
      Basic g          -> Global_context.sign2string s g
    | Combined (loc,c) -> Local_context.sign2string s loc

  let count_formals (c:t): int * int =
    match c with
      Basic _          -> 0,0
    | Combined (loc,_) -> Local_context.nfgs loc, Local_context.nargs loc

  let boolean (c:t): term =
    match c with
      Basic g          -> Class_table.boolean_type 0
    | Combined (loc,c) -> Local_context.boolean loc


  let push
      (entlst: entities list withinfo)
      (rt: return_type)
      (c:t)
      : t =
    (** Push the entity list [entlst] with the return type [rt] as a new
        local context onto the context [c]
     *)
    let loc =
      match c with
        Basic g ->           Local_context.make_first entlst rt g
      | Combined (loc,c) ->  Local_context.make_next  entlst rt loc
    in
    Combined (loc,c)


  let put_function
      (fn: feature_name withinfo)
      (impstat: Feature_table.implementation_status)
      (term_opt: term option)
      (c:t)
      : unit =
    (** Put the function [fn] into the corresponding table.
     *)
    assert (not (is_basic c));
    match c with
      Combined (loc, Basic _) ->
        Local_context.put_global_function
          fn
          (is_private c)
          impstat
          term_opt
          loc
    | Combined (loc0, Combined (loc,_)) ->
        assert false (* nyi: local functions *)
    | _ -> assert false (* illegal path *)


  let put_class (hm:header_mark withinfo) (cn:int withinfo) (c:t): unit =
    assert (is_basic c);
    Class_table.put hm cn (Global_context.ct (global c))




  let put_formal_generic
      (name:int withinfo)
      (concept:type_t withinfo)
      (c:t)
      : unit =
    (** Add the formal generic [name] with its [concept] to the formal
        generics.
     *)
    assert (is_basic c);
    Class_table.put_formal name concept (Global_context.ct (global c))



  let print (c:t): unit =
    assert (is_basic c);
    let g = global c in
    let ct,ft = Global_context.ct g, Global_context.ft g in
    Class_table.print ct;
    Feature_table.print ct ft




  let find_identifier
      (name:int)
      (nargs:int)
      (c:t)
      : (int * TVars.t * Sign.t) list * int * int =
    (** Find the identifier named [name] which accepts [nargs] arguments
        in one of the local contexts or in the global feature table. Return
        the list of variables together with their signature and the difference
        of the number of formals (generics and arguments) between the actual
        context [c] and the context where the identifier has been found
     *)
    let nfgs_c0,nargs_c0 = count_formals c
    in
    let rec ident (c:t)
        :(int * TVars.t * Sign.t) list * int * int =
      match c with
        Basic g ->
          Feature_table.find_funcs (FNname name) nargs (Global_context.ft g),
          nfgs_c0, nargs_c0
      | Combined (loc,cprev) ->
          try
            let i,tvs,s = Local_context.argument name loc
            in
            if (Sign.arity s) = nargs then begin
              let nfgs_c,nargs_c = count_formals c in
              [i,tvs,s], nfgs_c0 - nfgs_c, nargs_c0 - nargs_c
            end else
              raise Not_found
          with Not_found ->
            ident cprev

    in
    ident c


  let find_feature
      (fn:feature_name)
      (nargs:int)
      (c:t)
      : (int * TVars.t * Sign.t) list * int * int =
    (** Find the feature named [fn] which accepts [nargs] arguments global
        feature table. Return the list of variables together with their
        signature and the difference of the number of formals (generics
        and variables) between the actual context [c] and the global context.
      *)
    let nfgs_c0, nargs_c0 = count_formals c in
    let rec feat (c:t)
        :(int * TVars.t * Sign.t) list * int * int =
      match c with
        Basic g ->
          Feature_table.find_funcs fn nargs (Global_context.ft g),
          nfgs_c0,
          nargs_c0
      | Combined (loc,c) ->
            feat c

    in
    feat c


  let type_variables (c:t): TVars_sub.t =
    assert (not (is_basic c));
    match c with
      Basic _ -> assert false (* illegal path *)
    | Combined (loc,_) -> Local_context.tvars_sub loc

  let update_type_variables (tv:TVars_sub.t) (c:t): unit =
    assert (not (is_basic c));
    let loc = local c in
    Local_context.update_type_variables tv loc

end (* Context *)
