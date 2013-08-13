module Dummy = struct end



type typ = string

type expression =
    Variable of int * typ
  | Call of expression * expression array
  | Namedop of string * typ array * typ * expression option
  | Abstraction of typ array * expression





let arr2string (sep:string) (sfun:'a->string)(arr: 'a array)=
  String.concat "," (List.map sfun (Array.to_list arr))





let rec exp2string (e:expression) =
  match e with
    Variable (i,t) ->
      (string_of_int i) (*^ ":" ^ t*)
  | Call (op,earr) ->
      (exp2string op) ^ "(" ^ (arr2string "," exp2string earr) ^ ")"
  | Namedop (name,_,_,_) ->
      name
  | Abstraction (tarr,e) ->
      "(" ^ "[" ^ (arr2string "," (fun x->x) tarr) ^ "]"
      ^ (exp2string e) ^ ")"





let rec expand (e:expression) =
  match e with
    Namedop (name,args,rt,Some exp) -> Abstraction (args,exp)
  | Call (op,earr) ->
      Call (expand op, Array.map (fun e -> expand e) earr)
  | Abstraction (tarr, exp) ->
      Abstraction (tarr, expand exp)
  | _ -> e






(* Substitute in expression 'e' 'n' variables starting from variable 'i0'
   by the corresponding values in 'args' and shift down all variables
   above 'n+i0' by 'n' *)
let substitute (e:expression) (n:int) (i0:int) (args: expression array) =
  let len = Array.length args
  in
  assert (n <= len);
  let rec sub e i0 =
    match e with
    | Variable (i,t) ->
        if n+i0 <= i then
          Variable (i-n,t)
        else if i0<=i then
          args.(n-1-(i-i0))
        else
          e
    | Call (op,args) ->
        Call (sub op i0, Array.map (fun x -> sub x i0) args)
    | Abstraction (tarr,e) ->
        Abstraction (tarr, sub e (i0+(Array.length tarr)))
    | Namedop (_,_,_,_) ->
        e
  in
  sub e i0




let apply (op:expression) (args: expression array) =
  match op with
    Namedop (_,_,_,_) ->
      Call (op,args)
  | Abstraction (tarr,exp) ->
      let len,lenargs = Array.length tarr, Array.length args
      in
      if len <= lenargs then
        substitute exp len 0 args
      else
        Abstraction (Array.sub tarr lenargs (len-lenargs),
                     substitute exp lenargs (len-lenargs) args)
  | _ ->
      assert false



(* Make all possible beta reductions *)
let rec reduce (e:expression) =
  match e with
    Call (op,args) ->
      let opred = reduce op
      and argsr = Array.map (fun x -> reduce x) args
      in
      apply opred argsr
  | Abstraction (tarr,exp) -> Abstraction (tarr, reduce exp)
  | _ -> e



(* Shift all variables in expression 'e' above 'base' up by 'n' *)
let rec shift_above_up (e:expression)  (base:int) (n:int) =
  match e with
    Variable (i,t) ->
      if base<=i
      then Variable (i+n,t)
      else e
  | Call (op,earr) ->
      Call (op, Array.map (fun e -> shift_above_up e base n) earr)
  | Namedop (name,_,_,_) -> e
  | Abstraction (tarr,exp) ->
      let len = Array.length tarr in
      Abstraction (tarr, shift_above_up exp len n)



let shift_up (e:expression) (n:int) =
  shift_above_up e 0 n





(* Given an array 'arr' and a predicat 'p' find a permutation 'perm' and an
   index 'idx' such that all elements below the index satisfy 'p' and all
   elements above the index do not satisfy 'p'.

   perm.(i) is the position of element i of the original array after the
   permutation

   The permutation is stable i.e. the elements below and above idx are in
   their original order
*)
let partition (p:'a->bool) (arr: 'a array) =
  let rec part (i:int) (len1:int) (l1:int list) (l2:int list) =
    if i=0 then
      len1,l1,l2
    else
      if p arr.(i-1) then
        part (i-1) (len1+1) ((i-1)::l1) l2
      else
        part (i-1) len1 l1 ((i-1)::l2)
  in
  let len1,l1,l2 = part (Array.length arr) 0 [] []
  in
  (Array.of_list (List.append l1 l2)), len1


let invers_permutation (perm: int array) =
  let len = Array.length perm
  in
  let invers = Array.make len (-1)
  in
  let f i =
    assert (0<=i); assert (i<len);
    invers.(perm.(i))<-i
  in
  Array.iter f perm;
  invers



let permute (arr:'a array) (perm:int array) =
  assert ((Array.length arr)=(Array.length perm));
  let f i =
    assert (perm.(i)<(Array.length arr));
    arr.(perm.(i))
  in
  Array.init (Array.length arr) f


let print_permutation (perm:int array) =
  Printf.printf "perm = [%s], invers = [%s]\n"
    (arr2string "," (fun i -> string_of_int i) perm)
    (arr2string "," (fun i -> string_of_int i) (invers_permutation perm))





(* Abstract all variables in 'e' starting from base, return the
   type list, the length of the list, the expression and the argument list
*)
let rec abstract_based (e:expression) (base:int) =
  match e with
    Variable (i,t) ->
      if base <= i then
        [t], 1, 1, Variable (base,t), [i]
      else
        [], 0, 1, e, []
  | Abstraction (tarr,exp) ->
      let tlist,tlen,nvars,e,arglst = abstract_based exp (Array.length tarr)
      in
      tlist,tlen, nvars(*?*), Abstraction (tarr,e), arglst
  | Call (op,args) ->
      let argsabs = Array.map (fun a -> abstract_based a base) args
      and argslen = Array.length args
      and tlsto,tleno,nvarso,eo,alsto   = abstract_based op base
      in
      let merge_one tlst1 tlen1 nvars1 e1 alst1 tlst tlen nvars elst alst =
        (List.append tlst1 tlst),
        (tlen1+tlen),
        (nvars1+nvars),
        ((shift_up e1 tlen)::elst),
        (List.append alst1 alst)
      in
      let rec merge i tlst tlen nvars elst alst =
        if i=0 then
          tlst,tlen,nvars,elst,alst
        else
          let tlsti,tleni,nvarsi,ei,alsti = argsabs.(i-1)
          in
          let tlstc,tlenc,nvarsc,elstc,alstc =
            merge_one tlsti tleni nvarsi ei alsti tlst tlen nvars elst alst
          in
          merge (i-1) tlstc tlenc nvarsc elstc alstc
      in
      let tlstc,tlenc,nvarsc,elstc,alstc = merge argslen [] 0 0 [] []
      in
      let tlst,tlen,nvars,elst,alst =
        merge_one tlsto tleno nvarso eo alsto tlstc tlenc nvarsc elstc alstc
      in
      tlst, tlen, nvars, Call (eo,(Array.of_list elstc)), alst
  | Namedop (_,_,_,_) -> [],0,0,e,[]


(*
let abstract (e:expression) =
  let tlst,tlen,nvars,exp,arglst = abstract_based e 0
  in
  let tarr,argsint =
    Array.of_list tlst, Array.of_list arglst
  in
  let args = Array.init tlen (fun i -> Variable(argsint.(i),tarr.(i)))
  in
  let res = Call (Abstraction (tarr,exp), args)
  in
  (*assert ((reduce res) = (reduce e));*)
  res
*)



let rec abstract_parts (e:expression) =
  match e with
    Variable (i,t) ->
      [|t|], Variable (0,t), [|i|]
  | Abstraction (tarr, exp) ->
      let tarrlen = Array.length tarr
      in
      let ta,e,args = abstract_parts exp
      in
      let talen = Array.length ta
      in
      let perm,lenfree = partition (fun i -> tarrlen<=i) args
      in
      let farr arr base = fun i ->
        assert (0<=(base+i)); assert ((base+i)<(Array.length arr));
        arr.(perm.(base+i))
      in
      Printf.printf "lenfree,tarrlen,len(ta),len(args) = %d,%d,%d,%d\n"
        lenfree tarrlen (Array.length ta) (Array.length args);
      print_permutation perm;
      (Array.init lenfree (farr ta 0)),
      Abstraction (Array.init (talen-lenfree) (farr ta lenfree),
                   substitute e talen 0
                     (let pinv = invers_permutation perm in
                     (Array.init
                        talen
                        (fun i -> Variable(talen-pinv.(i)-1,ta.(i)))))
                  ),
      (Array.init lenfree (farr args 0))
  | Call (op,earr) ->
      let aearr = Array.map (fun e -> abstract_parts e) earr
      and len = Array.length earr
      in
      let rec merge i base tarr0 exp0 args0 =
        if i=0 then
          tarr0,exp0,args0,base
        else
          let tarr,exp,args = aearr.(i-1)
          in
          merge
            (i-1)
            (base + (Array.length tarr))
            (Array.append tarr tarr0)
            (Array.append [| shift_up exp base |] exp0)
            (Array.append args args0)
      in
      let tarr, exparr, args, base0 =
        merge len 0 [| |] [| |] [| |]
      in
      let  tarrop, expop, argsop = abstract_parts op
      in
      let down =
        match expop with
          Namedop (_,_,_,_) -> 0
        | Abstraction (tarr,exp) ->
            let nargs = Array.length args
            and nt    = Array.length tarr in
            if nargs > nt then
              nt
            else
              nargs
        | _ -> assert false
      in
      (Array.append tarrop tarr),
      (Call (shift_up expop base0,exparr)),
      (Array.append
         (Array.map
            (fun i -> assert (i>=down); i-down)
            argsop)
         args)
  | Namedop (_,_,_,_) -> [| |], e, [| |]




let abstract (e:expression) =
  let tarr, exp, args = abstract_parts e
  in
  let res = Call (Abstraction (tarr,exp),
                  (Array.init
                     (Array.length args)
                     (fun i -> Variable(args.(i),tarr.(i)))))
  in
  assert ((reduce res) = (reduce e));
  res




(* Experiment with functors *)

module type TypSig = sig
  type typ
end

module Verifier (Typ: TypSig) = struct
  type typ = Typ.typ

  type expression =
      Variable of typ * int
    | Operation of typ array * op_definition
    | Abstraction of typ array * expression
    | Call of expression * expression array
  and op_definition =
      Elementary of typ
    | Defined of expression

end
