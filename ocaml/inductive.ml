open Container
open Alba2_common

module Term = Term2



(* An inductive family consists of

   - a list of parameters

   - a list of inductive types

   - for each inductive type a list of constructors


   A simple definition defines only one inductive type with its list of
   constructors.

   Additional information:

   - a list of positive parameters

   - for each constructor a list of recursive arguments and a list of positive
   parameter arguments.


  *)

type param =
  string option * Term.typ * bool

type carg_class =
  Normal | Positive | Recursive

type constructor = {
    cname: Term.fname;
    typ:   Term.typ; (* valid in a context with all inductive types and the
                        parameters. *)
    argcls: carg_class list
  }


type t = {
    params: (string option * Term.typ * bool) array; (* flag: is_positive *)
    types: (Feature_name.t option
            * Term.typ
            * bool) array;  (* Valid in a context with parameters; flag if
                                   elimination is restricted. *)
    cs: (int * constructor array) array}


let nparams ind = Array.length ind.params


let ntypes ind = Array.length ind.types


let nconstructors i ind =
  assert (i < ntypes ind);
  Array.length(snd ind.cs.(i))


let constructor_base_index i ind =
  (* The number of all constructors of the inductive types of the family
     before [i]. *)
  assert (i < ntypes ind);
  fst ind.cs.(i)


let params0 ind: Term.arguments =
  Array.map (fun (nme,tp,_) -> nme,tp) ind.params


let params ind: Term.arguments =
  let ni = ntypes ind
  and np = nparams ind in
  Array.map (fun (nme,tp,_) -> nme, Term.up_from np ni tp) ind.params

let positive_parameters ind =
  Array.map (fun (_,_,flag) -> flag) ind.params


let name i ind =
  assert (i < ntypes ind);
  let nme,_,_ = ind.types.(i) in
  nme


let itype i ind =
  (* The inductive type (and its name) in the base context. *)
  assert (i < ntypes ind);
  let nme,tp,_ = ind.types.(i) in
  nme, Term.push_product (params0 ind) tp


let types0 (ind:t): Term.gamma =
  (* The inductive types in a context with parameters. *)
  Array.map
    (fun (nme,tp,_) -> nme,tp)
    ind.types

let types (ind:t): Term.gamma =
  let pars = params0 ind in
  Array.map
    (fun (nme,tp,_) -> nme, Term.push_product pars tp)
    ind.types


let is_restricted i ind =
  assert (i < ntypes ind);
  let _,_,res = ind.types.(i) in
  res



let cname i j ind =
  assert (i < ntypes ind);
  let _,cs = ind.cs.(i) in
  assert (j < Array.length cs);
  cs.(j).cname


let constructors i ind =
  assert (i < ntypes ind);
  let _,cs = ind.cs.(i) in
  Array.map (fun co -> co.cname, co.typ, co.argcls) cs


let constructor_arguments i j ind =
  assert (i < ntypes ind);
  let _,cs = ind.cs.(i) in
  assert (j < Array.length cs);
  cs.(j).argcls


let ctype i j ind =
  (* The type of the [j]th constructor of the type [i] of the family in an
     environment with all absolute inductive types and no parameters. *)
  assert (i < ntypes ind);
  let _,cs = ind.cs.(i) in
  assert (j < Array.length cs);
  let pars = params ind in
  cs.(j).cname, Term.push_product pars cs.(j).typ



let rec ndproduct (lst:Term.typ list): Term.typ =
  match lst with
  | [] ->
     assert false (* Illegal call: At least one type *)
  | [tp] ->
     tp
  | hd :: tl ->
     Term.All (None, hd, ndproduct tl)


let cmake cname argcls typ =
  {cname;typ;argcls}


let make params types cs =
  let ni = List.length types in
  assert (List.length cs = ni);
  let _,cs =
    List.fold_left
      (fun (i,lst) clst ->
        let carr = Array.of_list clst in
        let n = Array.length carr in
        i+n, (i,carr) :: lst)
      (0,[]) cs in
  {params = Array.of_list params;
   types = Array.of_list types;
   cs = Array.of_list cs}



let make_simple name params typ restr cs =
  make params [name,typ,restr] [cs]









(* class false create end *)
let make_false: t =
  let open Term in
  make_simple
    some_feature_false
    []
    proposition
    false
    []



(* class true create
       true_is_valid
    end *)
let make_true: t =
  let open Term in
  make_simple
    some_feature_true
    []
    proposition
    false
    [cmake (some_feature_name "true_is_valid") [] variable0]




(* class
       (and) (a,b:Proposition): Proposition
   create
       conjunction (a,b): a and b
   end
 *)
let make_and: t =
  let open Term in
  make_simple
    (some_feature_operator Operator.Andop)
    [ Some "a", proposition, true;
      Some "b", proposition, true ]
    proposition
    false
    begin
      let vand = variable0
      and a = variable1
      and b = variable2
      in
      let a_and_b = apply2 vand a b in
      [ cmake
          (some_feature_name "conjunction")
          [Positive; Positive]
          (ndproduct [a; b; a_and_b] |> to_index 3)
      ]
    end





(* class
       (or) (a,b:Proposition): Proposition
   create
       left (a): a or b
       right(b): a or b
   end
 *)
let make_or: t =
  let open Term in
  make_simple
    (some_feature_operator Operator.Orop)
    [ Some "a", proposition, true;
      Some "b", proposition, true ]
    proposition
    true
    begin
      let vor = variable0
      and a   = variable1
      and b   = variable2
      and n   = 3 in
      let a_or_b = apply2 vor a b in
      [ cmake
          (some_feature_name "left")
          [Positive]
          (ndproduct [a; a_or_b] |> to_index n);
        cmake
         (some_feature_name "right")
          [Positive]
          (ndproduct [b; a_or_b] |> to_index n);
      ]
    end







(* class
       accessible (A:Any, r:Relation(A,A), y:A): Proposition
   create
       access_intro
           (f:all(x) r(x,y) -> r.accessible(x))
           : r.accessible(y)
   end
 *)
let make_accessible (sv0:int): t =
  let open Term in
  make_simple
    (some_feature_name "accessible")
    [ Some "A", sort_variable sv0, false;
      Some "r", arrow variable0 (arrow variable0 proposition), false;
      Some "y", variable1, false]
    proposition
    false
    begin
      let acc = variable0
      and a =   variable1
      and r =   variable2
      and y =   variable3
      and x =   variable4
      and n =   4 in
      [cmake
         (some_feature_name "access_intro")
         [Recursive]
         (All (Some "f",
               All(Some "x",
                   a,
                   ndproduct [apply2 r x y; apply3 acc a r x]
                 ),
               apply3 acc a r y
            )
          |> to_index n)
      ]
    end





(* class
       (=) (A:Any, a:A): all(B:Any) B -> Proposition
   create
       reflexive: a = a
   end
 *)
let make_equal (sv0:int): t =
  let open Term in
  let abig = variable0
  and bbig = variable2
  and n = 4
  in
  make_simple
    (some_feature_operator Operator.Eqop)
    [
      Some "A", (sort_variable sv0), true;
      Some "a", abig,                false
    ]
    ( All(Some "B", sort_variable (sv0+1), ndproduct [bbig; proposition])
      |> to_index n)
    false
    begin
      let eq = variable0
      and abig = variable1
      and a = variable2
      and n = 3 in
      [
        cmake
          (some_feature_name "reflexive")
          []
          (apply4 eq abig a abig a |> to_index n)
      ]
    end






(* class
       Natural
   create
       0
       successor(Natural)
   end *)
let make_natural: t =
  let open Term in
  make_simple
    (some_feature_name "Natural")
    []       (* no parameter *)
    datatype (* of sort datatype *)
    false    (* no elim restriction *)
    begin
      let nat = variable0 in
      [
        cmake (some_feature_number 0) [] variable0;
        cmake
          (some_feature_name "successor") [Recursive]
          (ndproduct [nat;nat] |> to_index 1)
      ]
    end






(* class
       List(A)
   create
       []
       (^)(A,List(A))
   end
 *)
let make_list (sv0:int): t =
  let open Term in
  make_simple
    (some_feature_name "List")
    [ Some "A", sort_variable sv0, true]    (* one parameter *)
    (sort_variable (sv0+1))                 (* arity *)
    false                                   (* no elim restriction *)
    begin
      let lst = variable0
      and a = variable1 in
      let lsta = apply1 lst a
      in
      [ cmake
          some_feature_bracket
          []
          (apply1 lst a |> to_index 2);

        cmake
          (some_feature_operator Operator.Caretop)
          [Positive; Recursive]
          (ndproduct [a; lsta; lsta] |> to_index 2)
      ]
    end
