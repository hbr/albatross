open Container
open Type
open Term
open Proof
open Support

type descriptor = {names: int array; types: typ array; term:term}

type t  = {seq: descriptor seq}

module TermMap = Map.Make(struct
  let compare = Pervasives.compare
  type t = term
end)


type proof_context = {
    mutable proved:     proof_term TermMap.t;
    mutable mp_targets: (term list * term * proof_term) TermMap.t;
    argnames:          int array;
    argtypes:          typ array;
    class_table:        Class_table.t;
    feature_table:      Feature_table.t;
    assertion_table:    t
  }


module CTXT = struct
  let empty
      (argnames: int array)
      (argtypes: typ array)
      (ct: Class_table.t)
      (ft: Feature_table.t)
      (at: t)
      : proof_context
      =
    {proved          = TermMap.empty;
     mp_targets      = TermMap.empty;
     argnames        = argnames;
     argtypes        = argtypes;
     class_table     = ct;
     feature_table   = ft;
     assertion_table = at}


  let nbound (c:proof_context): int =
    Array.length c.argnames

  let term_to_string (t:term) (c:proof_context): string =
    Feature_table.term_to_string t c.argnames c.feature_table


  let add_proved (t:term) (pt:proof_term) (c:proof_context): unit =
    c.proved <- TermMap.add t pt c.proved


  let add_mp_target
      (target:  term)
      (premises:term list)
      (term:    term)
      (pt:      proof_term)
      (c:       proof_context)
      : unit =
    c.mp_targets <- TermMap.add target (premises,term,pt) c.mp_targets


  let term (ie:info_expression) (c:proof_context): term =
    Feature_table.assertion_term ie
      c.argnames c.argtypes c.class_table c.feature_table

  let find_proved (t:term) (c:proof_context): proof_term =
    TermMap.find t c.proved

  let discharge
      (ass:term list)
      (t:term)
      (pt:proof_term)
      (c:proof_context)
      : term * proof_term =
    (* Discharge all assumptions of the context 'c' in the term 't' and its
       corresponding proof term 'pt'. *)
    let rec dischrg ass t pt  =
      match ass with
        [] -> t,pt
      | f::tl ->
          let t,pt = dischrg tl t pt in
          Feature_table.implication_term f t (nbound c) c.feature_table, 
          Discharge (f,pt)
    in
    dischrg ass t pt
end





let prove_in_context
    (ie: info_expression)
    (ctxt: proof_context)
    :
    term * proof_term =
  let term = CTXT.term ie ctxt in
  try
    let pt = CTXT.find_proved term ctxt in
    term,pt
  with Not_found ->
    assert false


let prove
    (argnames: int array)
    (argtypes: typ array)
    (pre: compound)
    (chck: compound)
    (post: compound)
    (ct: Class_table.t)
    (ft: Feature_table.t)
    (at:t)
    :
    (term * proof_term) list =
  (* Prove the top level assertion with the formal arguments 'argnames' and
     'argtypes' and the body 'pre' (preconditions), 'chck' (the intermediate
     assertions) and 'post' (postconditions)
   *)
  assert (Mylist.is_empty chck); (* check part not yet implemented *)
  let termlist l =
    List.map
      (fun ie ->Feature_table.assertion_term ie argnames argtypes ct ft)
      l
  in
  let rlst,arglen = termlist pre, Array.length argtypes
  and context = CTXT.empty argnames argtypes ct ft at
  in
  let _ =   (* Initialize the map 'proved' with the preconditions and
               the map 'mp_targets' with the targets of implications of the
               preconditions *)
    List.iter
      (fun t ->
        CTXT.add_proved t (Assume t) context;
        let imp = Feature_table.implication_chain t arglen ft in
        List.iter
          (fun e ->
            let premises,term = e in
            match premises with
              [] -> ()
            | _ ->
                CTXT.add_mp_target term premises t (Assume t) context;
          )
          imp
      )
      rlst
  in
  List.map
    (fun ie ->
      let t,pt = prove_in_context ie context
      in
      let t1,pt1 = CTXT.discharge rlst t pt context
      in
      Printf.printf "proved assertion %s\n" (CTXT.term_to_string t1 context);
      t1,pt1
    )
    post




let assertion_to_string
    (d:descriptor)
    (ct:Class_table.t)
    (ft:Feature_table.t): string =
  let nargs = Array.length d.names in
  assert (nargs = (Array.length d.types));
  let args = Array.init
      nargs
      (fun i ->
        (ST.string d.names.(i))
        ^ ":"
        ^ (Class_table.type2string d.types.(i) 0 ct))
  in
  "all"
  ^ (
    if nargs=0 then " "
    else "(" ^ (String.concat "," (Array.to_list args)) ^ ") "
   )
  ^ (Feature_table.term_to_string d.term d.names ft)


(*   Public functions *)

let empty () = {seq = Seq.empty () }

let put
    (entlst: entities list withinfo)
    (bdy:feature_body)
    (ct: Class_table.t)
    (ft: Feature_table.t)
    (at:t): unit =
  let argnames,argtypes = Class_table.arguments entlst ct in
  match bdy with
    _, _, None ->
      error_info entlst.i "Assertion must have an ensure clause"
  | rlst_opt, imp_opt, Some elst ->
      let rlst = match rlst_opt with None -> [] | Some l -> l
      and axiom,is_do,clst =
        match imp_opt with
          None -> false,false,[]
        | Some Impdeferred ->
            not_yet_implemented entlst.i "Deferred assertions"
        | Some Impbuiltin -> (
            true,false,[]
           )
        | Some Impevent ->
            error_info entlst.i "Assertion cannot be an event"
        | Some (Impdefined (Some locs,is_do,cmp)) ->
            not_yet_implemented entlst.i "Local variables in assertions"
        | Some (Impdefined (None,is_do,cmp)) ->
            false,is_do,cmp
      in
      if axiom then
        match rlst with
          [] ->
            List.iter
              (fun ie ->
                let term =
                  Feature_table.assertion_term ie argnames argtypes ct ft in
                let _ = Term.normalize argtypes term in
                Seq.push at.seq {names=argnames; types=argtypes; term=term})
              elst
        | _ ->
            not_yet_implemented entlst.i "axioms with preconditions"
      else if is_do then
        not_yet_implemented entlst.i "Assertions with do block"
      else
        let _ =
          if Feature_table.has_implication ft then
            prove argnames argtypes rlst clst elst ct ft at
          else
            error_info entlst.i "\"=>\" is not yet defined"
        in
        ()




let print (ct:Class_table.t) (ft:Feature_table.t) (at:t): unit =
  Seq.iter
    (fun desc -> Printf.printf "%s\n" (assertion_to_string desc ct ft))
    at.seq
