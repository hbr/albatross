open Container
open Term
open Proof
open Signature
open Support



module Context: sig

  type t

  val make:  unit -> t

  val is_basic:     t -> bool
  val is_toplevel:  t -> bool
  val local:        t -> Local_context.t
  val is_public:    t -> bool
  val is_private:   t -> bool
  val set_visibility:   visibility -> t -> unit
  val reset_visibility: t -> unit
  val string_of_term: term -> t -> string
  val sign2string:  Sign.t -> t -> string
  val signature_string:   t -> string
  val named_signature_string: t -> string
  val boolean:      t -> term
  val count_formals: t -> int * int
  val push: entities list withinfo -> return_type -> t -> t
  val put_function:
      feature_name withinfo -> Feature_table.implementation_status
        -> term option -> t -> unit
  val implication_id:    t -> int
  val put_assertion: term -> proof_term option -> t -> unit

  val put_formal_generic: int withinfo -> type_t withinfo -> t -> unit
  val put_class: header_mark withinfo -> int withinfo -> t -> unit

  val print: t -> unit

  val find_identifier: int -> int -> t
    -> (int * TVars.t * Sign.t) list

  val find_feature:    feature_name -> int -> t
    -> (int * TVars.t * Sign.t) list

  val type_variables:  t -> TVars_sub.t

  val update_type_variables: TVars_sub.t -> t -> unit

end = struct

  type t =
      Basic    of Local_context.t
    | Combined of Local_context.t * t


  let make (): t =
    Basic (Local_context.make_basic ())


  let local (c:t): Local_context.t =
    match c with
      Basic loc        -> loc
    | Combined (loc,_) -> loc


  let is_basic (c:t): bool =
    match c with
      Basic _ -> true
    | _       -> false

  let is_toplevel (c:t): bool =
    match c with
      Combined (_, Basic _ ) -> true
    | _                      -> false

  let is_private (c:t): bool =
    Local_context.is_private (local c)

  let is_public (c:t): bool =
    Local_context.is_public (local c)

  let set_visibility (v:visibility) (c:t): unit =
    assert (is_basic c);
    Local_context.set_visibility v (local c)

  let reset_visibility (c:t): unit =
    assert (is_basic c);
    Local_context.reset_visibility (local c)


  let string_of_term (t:term) (c:t): string =
    Local_context.string_of_term t (local c)

  let sign2string (s:Sign.t) (c:t): string =
    Local_context.sign2string s (local c)


  let signature_string (c:t): string =
    assert (not (is_basic c));
    Local_context.signature_string (local c)

  let named_signature_string (c:t): string =
    assert (not (is_basic c));
    Local_context.named_signature_string (local c)


  let count_formals (c:t): int * int =
    let loc = local c in
    Local_context.nfgs loc, Local_context.nargs loc


  let boolean (c:t): term =
    Local_context.boolean (local c)


  let push
      (entlst: entities list withinfo)
      (rt: return_type)
      (c:t)
      : t =
    (** Push the entity list [entlst] with the return type [rt] as a new
        local context onto the context [c]
     *)
    let loc = Local_context.make_next entlst rt (local c)
    in
    Combined (loc,c)


  let implication_id (c:t): int =
    Local_context.implication_id (local c)

  let put_assertion (t:term) (pt_opt: proof_term option) (c:t): unit =
    (** Put the assertion [t] with its optional proof term [pt_opt]
        into the global assertion table.
     *)
    assert (is_toplevel c);
    Local_context.put_global_assertion t pt_opt (local c)


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
    Class_table.put hm cn (Local_context.ct (local c))




  let put_formal_generic
      (name:int withinfo)
      (concept:type_t withinfo)
      (c:t)
      : unit =
    (** Add the formal generic [name] with its [concept] to the formal
        generics.
     *)
    assert (is_basic c);
    Class_table.put_formal name concept (Local_context.ct (local c))



  let print (c:t): unit =
    assert (is_basic c);
    let loc = local c in
    let ct,ft = Local_context.ct loc, Local_context.ft loc in
    Class_table.print ct;
    Feature_table.print ct ft



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
      (nargs:int)
      (c:t)
      : (int * TVars.t * Sign.t) list =
    (** Find the identifier named [name] which accepts [nargs] arguments
        in one of the local contexts or in the global feature table. Return
        the list of variables together with their signature
     *)
    let nfgs_c0,nargs_c0 = count_formals c
    in
    let ident (c:t)
        :(int * TVars.t * Sign.t) list =
      match c with
        Basic loc ->
          find_funcs (FNname name) nargs nfgs_c0 nargs_c0
            (Local_context.ft loc)
      | Combined (loc,cprev) ->
          try
            let i,tvs,s = Local_context.argument name loc
            in
            if (Sign.arity s) = nargs then begin
              let nfgs_c,nargs_c = count_formals c in
              assert (nfgs_c0  = nfgs_c);
              assert (nargs_c0 = nargs_c);
              [i,tvs,s]
            end else
              raise Wrong_signature
          with
            Not_found ->
              find_funcs
                (FNname name) nargs nfgs_c0 nargs_c0 (Local_context.ft loc)
          | Wrong_signature ->
              raise Not_found
    in
    ident c


  let find_feature
      (fn:feature_name)
      (nargs:int)
      (c:t)
      : (int * TVars.t * Sign.t) list =
    (** Find the feature named [fn] which accepts [nargs] arguments global
        feature table. Return the list of variables together with their
        signature.
      *)
    let nfgs_c0, nargs_c0 = count_formals c in
    let rec feat (c:t): (int * TVars.t * Sign.t) list =
      match c with
        Basic loc ->
          find_funcs fn nargs nfgs_c0 nargs_c0 (Local_context.ft loc)
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
