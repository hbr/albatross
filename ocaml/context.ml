open Container
open Signature
open Term
open Proof
open Support


type entry = {
    fgnames:   int array;           (* cumulated        *)
    concepts:  type_term array;     (* cumulated        *)
    argnames:  int array;           (* cumulated        *)
    argtypes:  type_term array;     (* cumulated        *)
    info:      info;
    mutable signature: Sign.t;      (* from declaration *)
    mutable tvars_sub: TVars_sub.t; (* cumulated        *)
  }

type proof_term_0 = proof_term

type proof_term = Proof_context.proof_term

type t = {
    mutable entry: entry;
    mutable stack: entry list;
    mutable visi:  visibility;
    ct:            Class_table.t;
    ft:            Feature_table.t;
    at:            Assertion_table.t;
    pc:            Proof_context.t
  }


let empty_entry: entry =
  {fgnames  = [||];
   concepts = [||];
   argnames = [||];
   argtypes = [||];
   info      = UNKNOWN;
   signature = Sign.empty;
   tvars_sub = TVars_sub.make 0}

let next_entry
    (fgnames:  int array)
    (concepts: type_term array)
    (argnames: int array)
    (argtypes: type_term array)
    (info:     info)
    (sign:     Sign.t)
    (tvars:    TVars_sub.t): entry =
  {fgnames  = fgnames;
   concepts = concepts;
   argnames = argnames;
   argtypes = argtypes;
   info     = info;
   signature = sign;
   tvars_sub = tvars}


let is_global (c:t): bool =
  c.stack = []


let is_toplevel (c:t): bool =
  match c.stack with
    [_] -> true
  | _   -> false



let arity     (c:t): int = Sign.arity c.entry.signature

let argument (name:int) (c:t): int * TVars.t * Sign.t =
  (** The term and the signature of the argument named [name] *)
  let i = Search.array_find_min (fun n -> n=name) c.entry.argnames in
  i, TVars_sub.tvars c.entry.tvars_sub, Sign.argument i c.entry.signature
    (* bug: argnames are cumulated and signature not!! *)


let has_result (c:t): bool =
  Sign.has_result c.entry.signature

let result_type (c:t): type_term =
  (** The result type of the context
   *)
  assert (has_result c);
  Sign.result c.entry.signature

let count_type_variables (c:t): int =
  (** The number of cumulated type variables in this context and all
      preceeding contexts
   *)
  TVars_sub.count c.entry.tvars_sub


let nfgs (c:t): int =
  (** The cumulated number of formal generics in this context and all
      previous contexts
   *)
  Array.length c.entry.fgnames

let nargs (c:t): int =
  (** The cumulated number of formal arguments in this context and all
      previous contexts
   *)
  Array.length c.entry.argnames

let ntvs (c:t): int =
  (** The cumulated number of formal generics and type variables in
      this context and all previous contexts
   *)
  (nfgs c) + (count_type_variables c)


let fgnames (c:t): int array=
  (** The cumulated formal generic names of this context and all
      previous contexts
   *)
  c.entry.fgnames



let last_argnames (c:t): int array =
  (** The argument names of the last push *)
  Array.sub c.entry.argnames 0 (arity c)



let make (): t =
  {entry = empty_entry;
   stack = [];
   visi      = Public;
   ct        = Class_table.base_table ();
   ft        = Feature_table.base_table ();
   at        = Assertion_table.empty ();
   pc        =
   Proof_context.make
     Feature_table.implication_index
     Feature_table.all_index
 }


let push_empty (c:t): unit =
  c.stack <- c.entry::c.stack;
  Proof_context.push 0 [||] c.pc


let push
    (entlst: entities list withinfo)
    (rt: return_type)
    (c: t)
    : unit =
  (** Make a next local context with the argument list [entlst] and the
      return type [rt] based on previous local global context [c]
   *)
  let entry = c.entry in
  let fgnames, concepts, argnames, argtypes, ntvs, sign =
    let ntvs0 = TVars_sub.count_local c.entry.tvars_sub
    in
    Class_table.signature entlst rt
      entry.fgnames entry.concepts entry.argnames entry.argtypes ntvs0 c.ct
  in
  c.entry <-
    next_entry fgnames concepts argnames argtypes entlst.i sign
      (TVars_sub.add_local ntvs c.entry.tvars_sub);
  c.stack <- entry::c.stack;

  Proof_context.push (arity c) (last_argnames c) c.pc



let pop (c:t): unit =
  (** Pop the last context
   *)
  assert (not (is_global c));
  c.entry <- List.hd c.stack;
  c.stack <- List.tl c.stack;
  Proof_context.pop c.pc




let print (c:t): unit =
  assert (is_global c);
  Class_table.print   c.ct;
  Feature_table.print c.ct c.ft






let ct (c:t): Class_table.t    = c.ct
let ft (c:t): Feature_table.t  = c.ft
let at (g:t): Assertion_table.t  = g.at

let is_private (c:t): bool =
  match c.visi with
    Private -> true
  | _ -> false

let is_public (c:t): bool = not (is_private c)

let set_visibility (v:visibility) (c:t): unit =
  assert (is_global c);
  c.visi <- v

let reset_visibility (c:t): unit =
  assert (is_global c);
  c.visi <- Public



let type_variables (c:t): TVars_sub.t = c.entry.tvars_sub

let boolean (c:t): term =
  Class_table.boolean_type (ntvs c)


let update_type_variables (tvs:TVars_sub.t) (c:t): unit =
  (** Update the type variables of the current context with [tvs]
   *)
  try
    TVars_sub.update c.entry.tvars_sub tvs
  with Term_capture ->
    not_yet_implemented c.entry.info "Type inference of formal generics"




let string_of_term (t:term) (c:t): string =
  Feature_table.term_to_string t c.entry.argnames c.ft



let sign2string (s:Sign.t) (c:t): string =
  Class_table.string_of_signature
    s
    (count_type_variables c)
    c.entry.fgnames
    c.ct



let signature_string (c:t): string =
  (** Print the signature of the context [c].
   *)
  sign2string c.entry.signature c




let arguments_string (e:entry) (ct:Class_table.t): string =
  (** The string "(a:A, b1,b2:B, ... )" of all local arguments of the entry [e].
      In case that there are no arguments the empty string is returned and
      not "()".
   *)
  let nargs = Sign.arity e.signature in
    if nargs = 0 then
      ""
    else
      let zipped = Array.to_list (Array.init nargs
                                    (fun i ->
                                      e.argnames.(i),
                                      e.argtypes.(i)))
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
               ^ (Class_table.type2string tp 0 e.fgnames ct))
             llst)
      ^ ")"



let result_string (e:entry) (ct:Class_table.t): string =
  if Sign.has_result e.signature then
    Class_table.type2string (Sign.result e.signature) 0 e.fgnames ct
  else ""


let named_signature_string (c:t): string =
  (** Print the signature of the context [c] with all argument names.
   *)
  let argsstr = arguments_string c.entry c.ct
  and resstr  = result_string    c.entry c.ct
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
    c.entry.fgnames
    c.entry.concepts
    c.entry.argnames
    c.entry.signature
    (is_private c)
    impstat
    term_opt
    c.ft


let implication_id (c:t): int =
  Feature_table.implication_index + (nargs c)


let string_of_assertion (t:term) (c: t): string =
  "all"
  ^ (named_signature_string c) ^ " "
  ^ (string_of_term t c)


let put_global_assertion
    (t:term) (pt_opt: proof_term_0 option) (c:t): unit =
  (** Put the assertion [t] with its optional proof term [pt_opt]
      into the global assertion table.
   *)
  assert (is_toplevel c);
  Printf.printf "%3d %s  %s\n"
    (Assertion_table.count c.at)
    (match pt_opt with
      None    -> "axiom "
    | Some pt -> "proved")
    (string_of_assertion t c);
  Assertion_table.put_assertion t (arity c) pt_opt c.ft c.at


let put_formal_generic
    (name:int withinfo)
    (concept:type_t withinfo)
    (c:t)
    : unit =
  (** Add the formal generic [name] with its [concept] to the formal
      generics.
   *)
  assert (is_global c);
  Class_table.put_formal name concept c.ct



let put_class (hm:header_mark withinfo) (cn:int withinfo) (c:t): unit =
  assert (is_global c);
  Class_table.put hm cn c.ct





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
    (c:t)
    : (int * TVars.t * Sign.t) list =
  (** Find the identifier named [name] which accepts [nargs] arguments
      in one of the local contexts or in the global feature table. Return
      the list of variables together with their signature
   *)
  let nfgs_c0  = nfgs c
  and nargs_c0 = nargs c
  in
  if is_global c then
    find_funcs (FNname name) nargs_id nfgs_c0 nargs_c0 c.ft
  else
    try
      let i,tvs,s = argument name c
      in
      if (Sign.arity s) = nargs_id then begin
        [i,tvs,s]
      end else
        raise Wrong_signature
    with
      Not_found ->
        find_funcs
          (FNname name) nargs_id nfgs_c0 nargs_c0 c.ft
    | Wrong_signature ->
        raise Not_found



let find_feature
    (fn:feature_name)
    (nargs_feat:int)
    (c:t)
    : (int * TVars.t * Sign.t) list =
  (** Find the feature named [fn] which accepts [nargs] arguments global
      feature table. Return the list of variables together with their
      signature.
   *)
  let nfgs_c0  = nfgs c
  and nargs_c0 = nargs c
  in
  find_funcs fn nargs_feat nfgs_c0 nargs_c0 c.ft


let print_assertions (e:entry) (c0:int) (c1:int) (c:t): unit =
  let argsstr = arguments_string e c.ct in
  if argsstr <> "" then
    Printf.printf "%s\n" argsstr;
  let rec print (i:int): unit =
    if i = c1 then ()
    else begin
      let t,nbenv = Proof_context.term i c.pc in
      assert (nbenv = Array.length e.argnames);
      let tstr = Feature_table.term_to_string t e.argnames c.ft in
      Printf.printf "%3d\t%s\n" i tstr;
      print (i+1)
    end
  in
  print c0



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
  print_assertions e 0 cnt c



let print_all_local_assertions (c:t): unit =
  let rec print (elst: entry list) (clst: int list): unit =
    match elst, clst with
      [], []
    | [_], [_] ->
        ()
    | e1::e0::elst, c1::c0::clst ->
        print (e0::elst) (c0::clst);
        print_assertions e1 c0 c1 c
    | _, _ -> assert false (* shall never happen, elst and clst must have
                              equal length *)
  in
  let clst = Proof_context.stacked_counts c.pc
  in
  print c.stack clst;
  print_assertions
    c.entry
    (Proof_context.count_previous c.pc)
    (Proof_context.count          c.pc)
    c


let all_quantified_outer (t:term) (c:t): term =
  Proof_context.all_quantified_outer t c.pc

let implication_chain (ps:term list) (tgt:term) (c:t): term =
  Proof_context.implication_chain ps tgt c.pc

let expanded_term (t:term) (c:t): term =
  let nbenv = nargs c in
  Feature_table.normalize_term t nbenv c.ft


let add_assumption (t:term) (c:t): int =
  Proof_context.add_assumption t c.pc

let add_axiom (t:term) (c:t): int =
  Proof_context.add_axiom t c.pc

let discharged (i:int) (c:t): term * proof_term =
  Proof_context.discharged i c.pc
