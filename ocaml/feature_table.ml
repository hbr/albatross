open Container
open Support
open Term
open Signature

type implementation_status = No_implementation | Builtin | Deferred

module ESignature_map = Map.Make(struct
  type t = constraints * Sign.t
  let compare = Pervasives.compare
end)

module Key_map = Map.Make(struct
  type t = feature_name * int (* name, # of arguments *)
  let compare = Pervasives.compare
end)

type definition = term
type formal     = int * term

type descriptor = {mutable mdl: int;
                   cls:         int;
                   fname:       feature_name;
                   impstat:     implementation_status;
                   fgnames:     int array;
                   concepts:    type_term array;
                   argnames:    int array;
                   sign:        Sign.t;
                   priv:        definition option;
                   mutable pub: definition option option}

type t          = {mutable map: int ESignature_map.t Key_map.t;
                   seq:         descriptor seq;
                   ct:          Class_table.t}


let empty (): t =
  {map  = Key_map.empty;
   seq  = Seq.empty ();
   ct   = Class_table.base_table ()}

let class_table (ft:t):  Class_table.t   = ft.ct
let module_table (ft:t): Module_table.t  = Class_table.module_table ft.ct


let count (ft:t): int =
  Seq.count ft.seq


let descriptor (i:int) (ft:t): descriptor =
  assert (i < count ft);
  Seq.elem i ft.seq


let names_of_formals (farr: formal array): int array =
  Array.map (fun (name,_) -> name) farr

let terms_of_formals (farr: formal array): term array =
  Array.map (fun (_,t) -> t) farr





let implication_index: int = 0
let paren_index:       int = 1
let all_index:         int = 2
let some_index:        int = 3


let add_key (i:int) (ft:t): unit =
  (** Add the key of the feature [i] to the key table. *)
  assert (i < count ft);
  let desc  = Seq.elem i ft.seq
  in
  let fn    = desc.fname
  and nargs = Sign.arity desc.sign
  in
  let esign_map =
    try Key_map.find (fn,nargs) ft.map
    with Not_found -> ESignature_map.empty
  in
  ft.map <-
    Key_map.add
      (fn,nargs)
      (ESignature_map.add (desc.concepts,desc.sign) i esign_map)
      ft.map


let add_keys (ft:t): unit =
  for i = 0 to (count ft)-1 do
    add_key i ft
  done


let base_table () : t =
  (** Construct a basic table which contains at least implication.  *)
  let bool    = Class_table.boolean_type 0 in
  let ft      = empty ()
  and fnimp   = FNoperator DArrowop
  and signimp = Sign.make_func [|bool;bool|] bool
  in
  (* boolean *)
  Class_table.add_feature
    implication_index Class_table.boolean_index false ft.ct;
  Seq.push
    {mdl      = -1;
     cls      = Class_table.boolean_index;
     fname    = fnimp;
     impstat  = Builtin;
     fgnames  = [||];
     concepts = [||];
     argnames = [||];
     sign     = signimp;
     priv     = None;
     pub      = Some None}  (* 0: implication *)
    ft.seq;
  (* predicate *)
  let g = ST.symbol "G"
  and p = ST.symbol "p"
  and any   = Variable Class_table.any_index
  and bool1 = Variable (Class_table.boolean_index+1)
  and g_tp  = Variable 0 in
  let p_tp  = Application (Variable (Class_table.predicate_index+1),
                           [|g_tp|])
  in
  let entry =
    {mdl      = -1;
     cls      = Class_table.predicate_index;
     fname    = FNoperator Allop;
     impstat  = Builtin;
     fgnames  = [|g|];
     concepts = [|any|];
     argnames = [|p|];
     sign     = Sign.make_func [|p_tp|] bool1;
     priv     = None;
     pub      = Some None}
  in
  begin
    let idx,fn,sign = 1, FNoperator Parenop,
      Sign.make_func [|p_tp;g_tp|] bool1
    in
    Class_table.add_feature paren_index Class_table.function_index false ft.ct;
    Seq.push {entry with fname = FNoperator Parenop;
              sign = sign}  ft.seq;  (* 1: "()" *)
  end;
  Class_table.add_feature all_index  Class_table.predicate_index false ft.ct;
  Class_table.add_feature some_index Class_table.predicate_index false ft.ct;
  Seq.push entry ft.seq;                                   (* 2: all  *)
  Seq.push{entry with fname = FNoperator Someop} ft.seq;   (* 3: some *)
  add_keys ft;
  assert ((descriptor implication_index ft).fname = FNoperator DArrowop);
  assert ((descriptor paren_index ft).fname       = FNoperator Parenop);
  assert ((descriptor all_index ft).fname         = FNoperator Allop);
  assert ((descriptor some_index ft).fname        = FNoperator Someop );
  ft




let implication_term (a:term) (b:term) (nbound:int) (ft:t)
    : term =
  (* The implication term a=>b in an environment with 'nbound' bound variables
   *)
  let args = [|a;b|] in
  Application (Variable (implication_index+nbound), args)






let find
    (fn:feature_name)
    (nargs:int)
    (concepts:type_term array)
    (sign:Sign.t)
    (ft:t)
    : int =
  ESignature_map.find
    (concepts,sign)
    (Key_map.find (fn,nargs) ft.map)




let find_funcs
    (fn:feature_name)
    (nargs:int) (ft:t)
    : (int * TVars.t * Sign.t) list =
  (** Find all functions with name [fn] and [nargs] arguments in the feature
      table [ft]. Return the indices with the corresponding type variables
      and signature
   *)
  ESignature_map.fold
    (fun (cs,sign) i lst -> (i,TVars.make 0 cs,sign)::lst)
    (Key_map.find (fn,nargs) ft.map)
    []




let rec expand_term (t:term) (nbound:int) (ft:t): term =
  (* Expand the definitions of the term 't' within an environment with
     'nbound' bound variables, i.e. a variable i with nbound<=i refers to
     the global feature i-nbound *)
  Term.map
    (fun i nb ->
      let n = nb+nbound in
      if i<n then
        Variable i
      else
        let idx = i-n in
        assert (idx < (Seq.count ft.seq));
        let desc = Seq.elem idx ft.seq in
        match desc.priv with
          None -> Variable i
        | Some def ->
            let nargs = Sign.arity desc.sign in
            let t = expand_term def nargs ft in
            Lam (nargs, [||], Term.upbound n nargs t)
    )
    t




let rec normalize_term (t:term) (nbound:int) (ft:t): term =
  (* Expand the definitions of the term 't' and beta reduce it within an
     environment with 'nbound' bound variables, i.e. a variable i with
     nbound<=i refers to the global feature i-nbound *)
  Term.reduce (expand_term t nbound ft)



let term_to_string
    (t:term)
    (names: int array)
    (ft:t)
    : string =
  (** Convert the term [t] in an environment with the named variables [names]
      to a string.
   *)
  let rec to_string
      (t:term)
      (names: int array)
      (nanon: int)
      (outop: (operator*bool) option)
      : string =
    (* nanon: number of already used anonymous variables
       outop: the optional outer operator and a flag if the current term
              is the left operand of the outer operator
     *)
    let nnames = Array.length names
    and anon2sym (i:int): int =
      ST.symbol ("$" ^ (string_of_int (nanon+i)))
    in
    let var2str (i:int): string =
      if i < nnames then
        ST.string names.(i)
      else
        feature_name_to_string
          (Seq.elem (i-nnames) ft.seq).fname
    and find_op (f:term): operator  =
      match f with
        Variable i when nnames <= i ->
          begin
            match (Seq.elem (i-nnames) ft.seq).fname with
              FNoperator op -> op
            | _ -> raise Not_found
          end
      | _ -> raise Not_found
    and args2str (n:int) (nms:int array): string =
      let nnms  = Array.length nms in
      assert (nnms = n);
      let argsstr = Array.init n (fun i -> ST.string nms.(i)) in
      String.concat "," (Array.to_list argsstr)
    in
    let local_names (n:int) (nms:int array): int * int array =
      let nnms  = Array.length nms in
      if n = nnms then
        nanon, nms
      else
        nanon+n, Array.init n anon2sym
    in
    let lam_strs (n:int) (nms:int array) (t:term): string * string =
      let nanon, nms = local_names n nms in
      let names = Array.append nms names in
      args2str n nms,
      to_string t names nanon None
    in
    let q2str (qstr:string) (args:term array): string =
      let nargs = Array.length args in
      assert (nargs = 1);
      match args.(0) with
        Lam (n,nms,t) ->
          let argsstr, tstr = lam_strs n nms t in
          qstr ^ "(" ^ argsstr ^ ") " ^ tstr
      | _ -> assert false  (* cannot happen *)
    in
    let op2str (op:operator) (args: term array): string =
      match op with
        Allop  -> q2str "all"  args
      | Someop -> q2str "some" args
      | _ ->
          let nargs = Array.length args in
          if nargs = 1 then
            (operator_to_rawstring op) ^ " "
            ^ (to_string args.(0) names nanon (Some (op,false)))
          else begin
            assert (nargs=2); (* only unary and binary operators *)
            (to_string args.(0) names nanon (Some (op,true)))
            ^ " " ^ (operator_to_rawstring op) ^ " "
        ^ (to_string args.(1) names nanon (Some (op,false)))
          end
    and app2str (f:term) (args: term array): string =
      (to_string f names nanon None)
      ^ "("
      ^ (String.concat
           ","
           (List.map
              (fun t -> to_string t names nanon None)
              (Array.to_list args)))
      ^ ")"
    and lam2str (n:int) (nms: int array) (t:term): string =
      let argsstr, tstr = lam_strs n nms t in
      "((" ^ argsstr ^ ") -> " ^ tstr ^ ")"
    in
    let inop, str =
      match t with
        Variable i ->
          None, var2str i
      | Application (f,args) ->
          begin
            try
              let op = find_op f in
              Some op, op2str op args
            with Not_found ->
              None, app2str f args
          end
      | Lam (n,nms,t) ->
          None, lam2str n nms t
    in
    match inop, outop with
      Some iop, Some (oop,is_left) ->
        let _,iprec,iassoc = operator_data iop
        and _,oprec,oassoc = operator_data oop
        in
        let paren1 = iprec < oprec
        and paren2 = (iop = oop) &&
          match oassoc with
            Left  -> not is_left
          | Right -> is_left
          | _     -> false
        and paren3 = (iprec = oprec) && (iop <> oop)
        in
        if  paren1 || paren2 || paren3 then
          "(" ^ str ^ ")"
        else
          str
    | _ -> str
  in
  to_string t names 0 None





let print (ft:t): unit =
  Seq.iteri
    (fun i fdesc ->
      let name   = feature_name_to_string fdesc.fname
      and mdlnme =
        if fdesc.mdl = -1
        then ""
        else
          Module_table.name fdesc.mdl (module_table ft)
      and tname  =
        Class_table.string_of_signature fdesc.sign 0 fdesc.fgnames ft.ct
      and bdyname def_opt =
        match def_opt with
          None -> "Basic"
        | Some def -> term_to_string def fdesc.argnames ft
      and clsnme =
        if fdesc.cls = -1 then ""
        else Class_table.class_name fdesc.cls ft.ct
      in
      match fdesc.pub with
        None ->
          Printf.printf "%s.%s: %s %s = (%s)\n"
            mdlnme clsnme name tname (bdyname fdesc.priv)
      | Some pdef ->
          Printf.printf "%s.%s: %s %s = (%s, %s)\n"
            mdlnme clsnme name tname (bdyname fdesc.priv) (bdyname pdef))
    ft.seq




let put_function
    (fn:       feature_name withinfo)
    (fgs:      formal array)
    (argnames: int array)
    (sign:     Sign.t)
    (impstat:  implementation_status)
    (term_opt: term option)
    (ft:       t): unit =
  (** Add the function with then name [fn], the formal generics [fgs], the
      arguments [argnames], the signature [sign] to the feature table *)
  let is_priv = Parse_info.is_module () in
  let cnt   = Seq.count ft.seq
  and nargs = Sign.arity sign
  and fgnames, concepts = Myarray.split fgs
  in
  let idx =
     try find fn.v nargs concepts sign ft
     with Not_found -> cnt
  in
  let mdl = Module_table.current (module_table ft) in
  let cls = Class_table.owner mdl concepts sign ft.ct in
  if idx=cnt then begin (* new feature *)
    Seq.push
      {mdl      = mdl;
       cls      = cls;
       fname    = fn.v;
       impstat  = impstat;
       fgnames  = fgnames;
       concepts = concepts;
       argnames = argnames;
       sign     = sign;
       priv     = term_opt;
       pub      = if is_priv then None else Some term_opt}
      ft.seq;
    add_key cnt ft
  end else begin        (* feature update *)
    let desc = Seq.elem idx ft.seq
    and not_match str =
      let str = "The " ^ str ^ " of \""
        ^ (feature_name_to_string fn.v)
        ^ "\" does not match the previous definition"
      in
      error_info fn.i str
    in
    desc.mdl <- mdl;
    assert (cls = desc.cls);
    if is_priv then begin
      if impstat <> desc.impstat then
        not_match "implementation status";
      if term_opt <> desc.priv
      then
        not_match "private definition"
    end else
      match desc.pub with
        None ->
          desc.pub <- Some term_opt
      | Some def ->
          if def <> term_opt then
            not_match "public definition"
  end
