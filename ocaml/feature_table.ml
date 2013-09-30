open Container
open Type
open Term
open Support



type definition = {names: int array; types: typ array; term:term}
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
      let args = Array.init 2 (fun i -> if i=1 then a else b) in
      Application (Variable (i+nbound), args)




let split_implication (t:term) (nbound:int) (ft:t): term*term =
  (* Split the implication 'a=>b' into its components 'a' and 'b' *)
  match t with
    Application (f,args) ->
      begin match f,ft.implication with
        Variable i, Some j ->
          if i=j+nbound then begin
            assert ((Array.length args)=2);
            args.(1), args.(0)
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
          let chain = split args.(0) in
          ([],t) :: (List.map
                       (fun e ->
                         let premises,term=e in
                         args.(1)::premises, term
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
        match (Seq.elem ft.features idx).priv with
          None -> Variable i
        | Some def ->
            let nargs = Array.length def.types in
            let t = expand_term def.term nargs ft in
            Lam (nargs, Term.upbound n nargs t)
    )
    t




let rec normalize_term (t:term) (nbound:int) (ft:t): term =
  (* Expand the definitions of the term 't' and beta reduce it within an
     environment with 'nbound' bound variables, i.e. a variable i with
     nbound<=i refers to the global feature i-nbound *)
  Term.reduce (expand_term t nbound ft)






let check_match
    (i:info)
    (e:expression)
    (tp:typ)
    (expected:typ)
    (ct:Class_table.t)
    : unit =
  if tp<>expected then
    error_info
      i
      ("expression " ^ (string_of_expression e) ^ " has type "
       ^ (Class_table.type2string tp 0 ct)
       ^ " expected type "
       ^ (Class_table.type2string expected 0 ct))
    else ()


let typed_term
    (ie:info_expression)
    (names: int array)
    (types: typ array)
    (ct:Class_table.t)
    (ft:t):  term * typ =
  assert ((Array.length names) = (Array.length types));
  let nbound = Array.length types in
  let check e tp expected = check_match ie.i e tp expected ct
  in
  let find_name (name:int): term * typ =
    let idx =
      try
        Search.array_find_min name names
      with Not_found ->
        not_yet_implemented ie.i
          ("Search in global feature table of name " ^ (ST.string name))
    in
    Variable idx,
    if idx<nbound then
      types.(idx)
    else
      assert false (* would be global *)
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
          | _ -> not_yet_implemented ie.i "feature overloading"
        end
    | Exptrue ->
        let flst = find_feature FNtrue ft
        in
        begin
          match flst with
            [i] -> Variable (nbound+i), (Key_table.key ft.keys i).typ
          | _ -> not_yet_implemented ie.i "feature overloading"
        end
    | Expparen e -> trm e
    | Taggedexp (label,e) -> trm e
    | Binexp (op,e1,e2) ->
        assert (is_binary op);
        let t1,tp1 = trm e1
        and t0,tp0 = trm e2
        and oplst = find_function (FNoperator op) 2 ct ft
        in begin
          match oplst with
            [] ->
              raise (Error_info (ie.i,
                                "There is no binary operator \"" ^
                                (operator_to_rawstring op) ^ "\""))
          | [idx,tarr,rt] ->
              assert ((Array.length tarr) = 2);
              let _ = check e1 tp1 tarr.(0)
              and _ = check e2 tp0 tarr.(1)
              in
              Application (Variable (nbound+idx), [|t0;t1|]),rt
          | _ -> not_yet_implemented ie.i
                ("(Binexp)Typing of expression " ^
                 (string_of_expression ie.v))
        end
    | Unexp (op,e1) ->
        assert (is_unary op);
        let t1,tp1 = trm e1
        and oplst = find_function (FNoperator op) 1 ct ft
        in begin
          match oplst with
            [] ->
              raise (Error_info (ie.i,
                                "There is no unary operator \"" ^
                                (operator_to_rawstring op) ^ "\""))
          | [idx,tarr,rt] ->
              assert ((Array.length tarr) = 1);
              let _ = check e1 tp1 tarr.(0)
              in
              Application (Variable (nbound+idx), [|t1|]),rt
          | _ -> not_yet_implemented ie.i
                ("(Unexp)Typing of expression " ^
                 (string_of_expression ie.v))
        end
    | _ -> not_yet_implemented ie.i
          ("(others)Typing of expression " ^
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



let maybe_parenthesized
    (op:operator)
    (exp:string*operator option*int)
    (left:bool) =
  (* Put parenthesis around the expression 'exp' if necessary. The expression
     consists of the string and optional operator and a number of arguments.
     'op' is the operator of the next higher expression. The boolean 'left'
     signifies that 'exp' is the left argument of the operator 'op'
   *)
  let str,op_opt,nargs = exp in
  match op_opt with
    None -> str
  | Some op1 ->
      let _,prec1,assoc1 = operator_data op1
      and _,prec,assoc   = operator_data op in
      if op=op1 && nargs=2 && (
        match assoc with
          Left -> not left
        | Right -> left
        | Nonassoc -> assert false (* Cannot happen, or the parser does not
                                      work correctly *)
       ) then "(" ^ str ^ ")"
      else if op<>op1 && nargs=2 && prec1<=prec then
        "(" ^ str ^ ")"
      else
        str



let feature_name (i:int) (names:int array) (nanon:int) (ft:t): feature_name =
  (* The name of the feature number 'i' in an environment with the arguments
     'names' and 'nanon' further anonymous variables *)
  let arglen = Array.length names in
  if i<nanon then
    FNname (ST.symbol ("@" ^ (string_of_int (nanon-1-i))))
  else if i < arglen+nanon then
    FNname names.(i-nanon)
  else
    begin
      assert ((i-(arglen+nanon))<Seq.count ft.features);
      (Key_table.key ft.keys (i-(arglen+nanon))).name
    end


let normal_application2string
    (name:string)
    (args: (string*operator option*int) array) =
  let nargs = Array.length args in
  name ^ "("
  ^ (String.concat
       ","
       (List.rev_map
          (fun str_op -> let str,_,_ = str_op in str)
          (Array.to_list args)))
  ^ ")", None, nargs

let application2string
    (fn:feature_name)
    (args: (string*operator option*int) array) =
  (* Convert the function application with the feature name 'fn' and the
     arguments 'args' (already as string, optional operator and a number of
     arguments to distinguish unary and binary operators)
   *)
  let nargs = Array.length args in
  match fn with
    FNoperator op ->
      if nargs = 1 then
        (operator_to_rawstring op)
        ^ " " ^ (maybe_parenthesized op args.(0) true),
        Some op, nargs
      else if nargs = 2 then
        (maybe_parenthesized op args.(1) true)
        ^ " " ^ (operator_to_rawstring op) ^ " "
        ^ (maybe_parenthesized op args.(0) false),
        Some op, nargs
      else
        assert false (* There are only unary and binary operators *)
  | _ ->
      normal_application2string (feature_name_to_string fn) args




let term_to_string_base (t:term) (names:int array) (nanon:int) (ft:t): string =
  let fname i nanon = feature_name i names nanon ft
  in
  let rec term2str (t:term) (nanon:int): string * operator option * int =
    match t with
      Variable i ->
        feature_name_to_string (fname i nanon), None, 0
    | Application (f,args) ->
        app2str f args nanon
    | Lam (tarr,t) ->
        (lam2str tarr t nanon),None,0
  and app2str (f:term) (args:term array) (nanon:int)
      : string * operator option * int =
    let arg_strings = Array.map (fun t -> term2str t nanon) args
    in
    match f with
      Variable i ->
        let fn = fname i nanon in
        application2string fn arg_strings
    | Lam (n,t) ->
        normal_application2string
          (lam2str n t nanon)
          arg_strings
    | Application (f,args) ->
        let fstr,_,_ = app2str f args nanon in
        normal_application2string fstr arg_strings
  and lam2str (len:int) (t:term) (nanon:int): string =
    let tstr,_,_ = term2str t (nanon+len) in
    let fargs =
      String.concat
        ","
        (let arr =
          (Array.init len
             (fun i ->
               feature_name_to_string (fname (len-1-i) (nanon+len))))
        in
        List.rev (Array.to_list arr)
        )
    in
    "([" ^ fargs ^ "] -> " ^ tstr ^ ")"
  in
  let s,_,_ = term2str t nanon in s



let term_to_string (t:term) (names:int array) (ft:t): string =
  term_to_string_base t names 0 ft


let raw_term_to_string (t:term) (nanon:int) (ft:t): string =
  term_to_string_base t [| |] nanon ft




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
              let term,tp =
                typed_term (withinfo ens.i def) argnames argtypes ct ft
              in
              check_match ens.i def tp rettype ct;
              Some {names = argnames;
                    types = argtypes;
                    term  = term}
          | _ -> not_yet_implemented ens.i
                "functions not defined with \"Result = ...\""
        end
    | _ -> not_yet_implemented fn.i
          "functions with implementation/preconditions"
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
      error_info fn.i
        ("The feature \"" ^ (feature_name_to_string fn.v)
         ^ "\" has already a private definition")
    else
      match func_def with
        None ->
          (Seq.elem ft.features idx).pub <- Some func_def
      | Some _ ->
          not_yet_implemented fn.i
            ("public function definition if there is already "
             ^ "a private definition")
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
