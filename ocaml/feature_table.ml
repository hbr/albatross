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

type descriptor = {fname:       feature_name;
                   impstat:     implementation_status;
                   fgnames:     int array;
                   concepts:    term array;
                   argnames:    int array;
                   sign:        Sign.t;
                   priv:        definition option;
                   mutable pub: definition option option}

type key        = {name: feature_name; sign: Sign.t}

type t          = {mutable map: int ESignature_map.t Key_map.t;
                   mutable implication: int option;
                   features: descriptor seq}


let empty () =
  {map  = Key_map.empty;
   implication = None;
   features = Seq.empty ()}




let has_implication (ft:t): bool =
  match ft.implication with
    None -> false
  | _    -> true


let implication_index (ft:t): int =
  assert (has_implication ft);
  match ft.implication with
    None -> assert false
  | Some i -> i


let implication_term (a:term) (b:term) (nbound:int) (ft:t)
    : term =
  (* The implication term a=>b in an environment with 'nbound' bound variables
   *)
  assert (has_implication ft);
  match ft.implication with
    None -> assert false  (* Cannot happen *)
  | Some i ->
      let args = Array.init 2 (fun i -> if i=0 then a else b) in
      Application (Variable (i+nbound), args)





let implication_chain
    (t:term)
    (nbound:int)
    (ft:t)
    : (term list * term) list =
  (* Split the term t into its implication chain i.e. split a=>b=>c into
     [ [],a=>b=>c; [a],b=>c; [a,b],c ]
     and return in the second return parameter the optional premise and
     conclusion of the implication (i.e. a,b=>c)
   *)
  let is_implication t =
    match t,ft.implication with
      Variable i, Some j -> i=j+nbound
    | _ -> false
  in
  let rec split(t:term): (term list * term) list =
    match t with
      Variable _
    | Lam (_,_)  -> [ [], t ]
    | Application (f,args) ->
        let len = Array.length args in
        if len=2 && is_implication f then
          let chain = split args.(1) in
          ([],t) :: (List.map
                       (fun e ->
                         let premises,term=e in
                         args.(0)::premises, term
                       )
                       chain)
        else
          [ [], t ]
  in
  split t




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
        assert (idx < (Seq.count ft.features));
        let desc = Seq.elem ft.features idx in
        match desc.priv with
          None -> Variable i
        | Some def ->
            let nargs = Sign.arity desc.sign in
            let t = expand_term def nargs ft in
            Lam (nargs, Term.upbound n nargs t)
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
  let nnames = Array.length names
  and anon2str (i:int): string = "@" ^ (string_of_int i)
  in
  let rec to_string (t:term) (nb:int) (outop: (operator*bool) option): string =
    (* outop is the optional outer operator and a flag if the current term
       is the left operand of the outer operator
     *)
    let var2str (i:int): string =
      if i<nb then
        anon2str i
      else if i < nb + nnames then
        ST.string names.(i-nb)
      else
        feature_name_to_string
          (Seq.elem ft.features (i-nnames-nb)).fname
    and find_op (f:term): operator  =
      match f with
        Variable i when nnames+nb <= i ->
          begin
            match (Seq.elem ft.features (i-nnames-nb)).fname with
              FNoperator op -> op
            | _ -> raise Not_found
          end
      | _ -> raise Not_found
    and op2str (op:operator) (args: term array): string =
      let nargs = Array.length args in
      if nargs = 1 then
        (operator_to_rawstring op) ^ " "
        ^ (to_string args.(0) nb (Some (op,false)))
      else begin
        assert (nargs=2); (* only unary and binary operators *)
        (to_string args.(0) nb (Some (op,true)))
        ^ " " ^ (operator_to_rawstring op) ^ " "
        ^ (to_string args.(1) nb (Some (op,false)))
      end
    and app2str (f:term) (args: term array): string =
      (to_string f nb None)
      ^ "("
      ^ (String.concat
           ","
           (List.map
              (fun t -> to_string t nb None)
              (Array.to_list args)))
      ^ ")"
    and lam2str (n:int) (t:term): string =
      let fargs  = Array.init n (fun i -> anon2str i) in
      let argstr = String.concat "," (Array.to_list fargs)
      and tstr   = to_string t (nb+n) None
      in
      "((" ^ argstr ^ ") -> " ^ tstr ^ ")"
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
      | Lam (n,t) ->
          None, lam2str n t
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
  to_string t 0 None





let print (ct:Class_table.t)  (ft:t): unit =
  Seq.iteri
    (fun i fdesc ->
      let name = feature_name_to_string fdesc.fname
      and tname =
        Class_table.string_of_signature fdesc.sign 0 fdesc.fgnames ct
      and bdyname def_opt =
        match def_opt with
          None -> "Basic"
        | Some def -> term_to_string def fdesc.argnames ft
      in
      match fdesc.pub with
        None ->
          Printf.printf "%-7s  %s = (%s)\n" name tname (bdyname fdesc.priv)
      | Some pdef ->
          Printf.printf "%-7s  %s = (%s, %s)\n"
            name tname (bdyname fdesc.priv) (bdyname pdef))
    ft.features




let put_function
    (fn:       feature_name withinfo)
    (fgnames:  int array)
    (concepts: type_term array)
    (argnames: int array)
    (sign:     Sign.t)
    (is_priv:  bool)
    (impstat:  implementation_status)
    (term_opt: term option)
    (ft:       t): unit =
  (** Add the function with then name [fn], the formal generics [fgnames] with
      their constraints [concepts], the arguments [argnames], the
      signature [sign] to the feature table
   *)
  let cnt   = Seq.count ft.features
  and ntvs  = Array.length fgnames
  and nargs = Sign.arity sign
  in
  let sig_map =
    try Key_map.find (fn.v,nargs) ft.map
    with Not_found -> ESignature_map.empty
  in
  let idx =
    try ESignature_map.find (concepts,sign) sig_map
    with Not_found -> cnt in
  if idx=cnt then begin (* new feature *)
    if fn.v = (FNoperator DArrowop) &&
      (Class_table.is_boolean_binary sign ntvs) then
      ft.implication <- Some cnt;
    Seq.push
      ft.features
      {fname    = fn.v;
       impstat  = impstat;
       fgnames  = fgnames;
       concepts = concepts;
       argnames = argnames;
       sign     = sign;
       priv     = term_opt;
       pub      = if is_priv then None else Some term_opt};
    ft.map <- Key_map.add
        (fn.v,nargs)
        (ESignature_map.add (concepts,sign) idx sig_map)
        ft.map;
  end else begin        (* feature update *)
    let desc = Seq.elem ft.features idx
    and not_match str =
      let str = "The " ^ str ^ " of \""
        ^ (feature_name_to_string fn.v)
        ^ "\" does not match the previous definition"
      in
      error_info fn.i str
    in

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
