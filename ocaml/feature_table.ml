open Container
open Type
open Term
open Support



type definition = {names: int array; term:term}
type descriptor = {priv:        definition option;
                   mutable pub: definition option option}

type key        = {name: feature_name; typ: typ}
type t          = {keys: key key_table;
                   mutable implication: int option;
                   features: descriptor seq}



let empty () =
  {keys = Key_table.empty () ; implication = None; features = Seq.empty ()}




let has_implication (ft:t): bool =
  match ft.implication with
    None -> false
  | _    -> true




let implication_term (a:term) (b:term) (nbound:int) (ft:t)
    : term =
  (* The implication term a=>b in an environment with 'nbound' bound variables
   *)
  assert (has_implication ft);
  match ft.implication with
    None -> assert false
  | Some i ->
      let args = Array.init 2 (fun i -> if i=0 then a else b) in
      Application (Variable (i+nbound), args)




let split_implication (t:term) (nbound:int) (ft:t): term*term =
  (* Split the implication 'a=>b' into its components 'a' and 'b' *)
  match t with
    Application (f,args) ->
      begin match f,ft.implication with
        Variable i, Some j ->
          if i=j+nbound then begin
            assert ((Array.length args)=2);
            args.(0), args.(1)
          end
          else raise Not_found
      | _,_ -> raise Not_found
      end
  | _ -> raise Not_found



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






let find_feature (name: feature_name) (ft:t)
    : int list =
  (* List of features with the name 'name' *)
  let lst = ref []
  in
  let _ =
    Key_table.iteri
      (fun i k ->
        if k.name=name then
          lst := i::!lst
        else
          () )
      ft.keys
  in
  !lst


let find_function (name: feature_name) (nargs:int) (ct:Class_table.t) (ft:t)
    : (int * typ array * typ) list =
  (* List of functions with the name 'name' and with 'nargs' argumens *)
  let lst = ref []
  in
  let _ =
    Key_table.iteri
      (fun i k ->
        if k.name=name then
          try
            let args,rt = Class_table.split_function k.typ ct in
            if nargs = (Array.length args) then
              lst := (i,args,rt)::!lst
            else ()
          with Failure _ ->
            ()
        else
          () )
      ft.keys
  in
  !lst




let typed_term
    (ie:info_expression)
    (names: int array)
    (types: typ array)
    (ct:Class_table.t)
    (ft:t):  term * typ =
  assert ((Array.length names) = (Array.length types));
  let nbound = Array.length types in
  let check_match (e:expression) (tp:typ) (expected:typ): unit =
    if tp<>expected then
      raise (
      Error_info (ie.i,
                 "expression " ^ (string_of_expression e) ^ " has type "
                  ^ (Class_table.type2string tp 0 ct)
                  ^ " expected type "
                  ^ (Class_table.type2string expected 0 ct)
                 ))
    else ()
  in
  let find_name (name:int): term * typ =
    let idx =
      try
        nbound - 1 - (Search.array_find_min name names)
      with Not_found ->
          assert false (* search in global feature table!! *)
    in
    Variable idx,
    if idx<nbound then types.(nbound-1-idx) else assert false
  in
  let rec trm e: term * typ =
    match e with
      Identifier i ->
        find_name i
    | Expfalse ->
        let flst = find_feature FNfalse ft
        in
        begin
          match flst with
            [i] -> Variable (nbound+i), (Key_table.key ft.keys i).typ
          | _ -> assert false
        end
    | Expparen e -> trm e
    | Taggedexp (label,e) -> trm e
    | Binexp (op,e1,e2) ->
        assert (is_binary op);
        let t1,tp1 = trm e1
        and t2,tp2 = trm e2
        and oplst = find_function (FNoperator op) 2 ct ft
        in begin
          match oplst with
            [] ->
              raise (Error_info (ie.i,
                                "There is no binary operator \"" ^
                                (operator_to_rawstring op) ^ "\""))
          | [idx,tarr,rt] ->
              assert ((Array.length tarr) = 2);
              let _ = check_match e1 tp1 tarr.(0)
              and _ = check_match e1 tp2 tarr.(1)
              in
              Application (Variable (nbound+idx), [|t1;t2|]),rt
          | _ -> error_info ie.i
                ("Cannot type expression " ^
                 (string_of_expression ie.v))
        end
    | _ -> error_info ie.i
          ("Cannot type expression " ^
           (string_of_expression ie.v))
  in
  trm ie.v




let term
    (ie:info_expression)
    (names: int array)
    (types: typ array)
    (ct:Class_table.t)
    (ft:t):  term =
  let t,_ = typed_term ie names types ct ft
  in
  t




let assertion_term
    (ie:info_expression)
    (names: int array)
    (types: typ array)
    (ct:Class_table.t)
    (ft:t):  term =
  let t,tp = typed_term ie names types ct ft
  in
  if tp <> (Class_table.boolean_type ct) then
    error_info ie.i "Expression does not have type BOOLEAN"
  else
    t



let term_to_string (t:term) (names:int array) (ft:t): string =
  let len = Array.length names in
  let rec tostr_op (t:term): string * operator option * int =
    let fname i =
      if i<len then FNname names.(len-1-i)
      else begin
        assert ((i-len)<Seq.count ft.features);
        (Key_table.key ft.keys (i-len)).name
      end
    in
    match t with
      Variable i ->
        feature_name_to_string (fname i), None, 0
    | Application (f,args) ->
        let argsstr_op = Array.map (fun t -> tostr_op t) args
        and nargs = Array.length args in
        let lower_op op low_op left =
          let str,op_opt,nargs = low_op in
          match op_opt with
            None -> str
          | Some op1 ->
              let _,prec1,assoc1 = operator_data op1
              and _,prec,assoc   = operator_data op in
              if op=op1 && nargs=2 && (
                match assoc with
                  Left -> not left
                | Right -> left
                | Nonassoc -> assert false
               ) then "(" ^ str ^ ")"
              else if op<>op1 && nargs=2 && prec1<=prec then
                "(" ^ str ^ ")"
              else
                str
        in begin
          match f with
            Variable i ->
              let fn = fname i in begin
                match fn with
                  FNoperator op ->
                    if nargs = 1 then
                      (operator_to_rawstring op)
                      ^ " " ^ (lower_op op argsstr_op.(0) true),
                      Some op, nargs
                    else if nargs = 2 then
                      (lower_op op argsstr_op.(0) true)
                      ^ " " ^ (operator_to_rawstring op) ^ " "
                      ^ (lower_op op argsstr_op.(1) false),
                      Some op, nargs
                    else
                      assert false
                | _ ->
                    (feature_name_to_string fn) ^ "("
                    ^ (String.concat
                         ","
                         (List.map
                            (fun str_op -> let str,_,_ = str_op in str)
                            (Array.to_list argsstr_op)))
                    ^ ")", None, nargs
              end
          | Lam (tarr,t) ->
              assert false
          | Application (f,args) ->
              assert false
        end
    | Lam (tarr,t) -> assert false
  in
  let s,_,_ = tostr_op t in s





let print (ct:Class_table.t)  (ft:t): unit =
  Seq.iteri
    (fun i fdesc ->
      let key = Key_table.key ft.keys i
      in
      let name = feature_name_to_string key.name
      and tname = Class_table.type2string key.typ 0 ct
      and bdyname def_opt =
        match def_opt with
          None -> "Basic"
        | Some def -> term_to_string def.term def.names ft
      in
      match fdesc.pub with
        None ->
          Printf.printf "%s  %s = (%s)\n" name tname (bdyname fdesc.priv)
      | Some pdef ->
          Printf.printf "%s  %s = (%s, %s)\n"
            name tname (bdyname fdesc.priv) (bdyname pdef))
    ft.features




let put
    (fn: feature_name withinfo)
    (entlst: entities list withinfo)
    (rt: return_type)
    (bdy: feature_body option)
    (bs: Block_stack.t)
    (ct: Class_table.t)
    (ft: t) =
  let argtypes,rettype,functype,argnames =
    Class_table.feature_type entlst rt ct
  in
  let func_def: definition option =
    match bdy with
      None -> None
    | Some (None, Some Impbuiltin, None) -> None
    | Some (None, None, Some [ens]) ->
        begin
          match ens.v with
            Binexp (Eqop, ExpResult,def) ->
              Some {names = argnames;
                    term  = term (withinfo ens.i def) argnames argtypes ct ft}
          | _ -> assert false (*NYI*)
        end
    | _ -> assert false (*NYI*)
  in
  let nargs = Array.length argtypes in
  let _ =
    match fn.v with
      FNoperator op ->
        if
          (nargs=1 && is_unary op) ||
          (nargs=2 && is_binary op)||
          (nargs>0 && is_nary op) then ()
        else if nargs=0 then
          raise (
          Error_info (fn.i, "Operator \"" ^
                      (operator_to_rawstring op)
                      ^ "\" must have arguments"))
        else if nargs=1 then
          raise (
          Error_info (fn.i, "Operator \"" ^
                      (operator_to_rawstring op)
                      ^ "\" is not a unary operator"))
        else if nargs=2 then
          raise (
          Error_info (fn.i, "Operator \"" ^
                      (operator_to_rawstring op)
                      ^ "\" is not a binary operator"))
        else
          raise (
          Error_info (fn.i, "Operator \"" ^
                      (operator_to_rawstring op)
                      ^ "\" is not an nary operator"))
    | FNfalse | FNtrue | FNnumber _ ->
        if nargs <> 0 then
          raise (
          Error_info (fn.i, "\"" ^ (feature_name_to_string fn.v)
                      ^ "\" must be a constant"))
        else
          ()
    | _ -> ()
  in
  let key =
    let _ =
      match fn.v with
        FNoperator op ->
          (match op with
            DArrowop ->
              if functype = Class_table.boolean_binary ct then ()
              else error_info fn.i "Operator \"=>\" must be boolean binary"
          | Andop ->
              if functype = Class_table.boolean_binary ct then ()
              else error_info fn.i "Operator \"and\" must be boolean binary"
          | Orop ->
              if functype = Class_table.boolean_binary ct then ()
              else error_info fn.i "Operator \"or\" must be boolean binary"
          | Notop ->
              if functype = Class_table.boolean_unary ct then ()
              else error_info fn.i "Operator \"not\" must be boolean unary"
          | _ -> ()  (* more error checks here *)
          )
      | _ -> ()
    in
    {name = fn.v; typ = functype}
  in
  let idx = Key_table.index ft.keys key
  and cnt = Seq.count ft.features
  in
  if idx < cnt then begin
    if Block_stack.is_private bs then
      raise (
      Error_info (fn.i,
                  "The feature \"" ^ (feature_name_to_string fn.v)
                  ^ "\" has already a private definition"))
    else
      match func_def with
        None ->
          (Seq.elem ft.features idx).pub <- Some func_def
      | Some _ ->
          assert false (*NYI*)
  end
  else begin
    assert (idx=cnt);
    if fn.v = (FNoperator DArrowop) then
      ft.implication <- Some idx
    else ();
    Seq.push
      ft.features
      (if Block_stack.is_private bs then {priv=func_def;pub=None}
      else {priv = func_def; pub = Some func_def});
  end
