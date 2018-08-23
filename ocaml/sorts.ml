open Container


module IArr = Immutable_array

module Set:
sig
  type t
  val count: t -> int
  val empty: t
  val singleton: int -> bool -> t
  val equal: t -> t -> bool
  val add: int -> bool -> t -> t
  val union: t -> t -> t
  val is_singleton: int -> bool -> t -> bool
  val is_lower_bound: int -> t -> bool
  val is_strict_lower_bound: int -> t -> bool
end
  =
  struct
    type t = bool IntMap.t (* maps to true, if type of variable is meant,
                              maps to false, if variable is meant *)

    let count (s:t): int =
      IntMap.cardinal s

    let equal (a:t) (b:t) :bool = IntMap.equal (fun b1 b2 -> b1 = b2)  a b

    let empty = IntMap.empty

    let singleton (i:int) (strict:bool): t =
      IntMap.singleton i strict

    let is_singleton (i:int) (strict:bool) (s:t): bool =
      IntMap.cardinal s = 1
      && IntMap.min_binding s = (i,strict)

    let add (i:int) (strict:bool) (s:t): t =
      if strict || not (IntMap.mem i s) then
        IntMap.add i strict s
      else
        s

    let union (a:t) (b:t): t =
      let br = ref b in
      IntMap.iter
        (fun i strict -> br := add i strict !br)
        a;
      !br

    let is_lower_bound (i:int) (s:t): bool =
      IntMap.mem i s

    let is_strict_lower_bound (i:int) (s:t): bool =
      try
        IntMap.find i s
      with Not_found ->
        false
  end





module Variables =
  struct
    type t = Set.t IArr.t

    let count (vs:t): int =
      IArr.length vs

    let le (vs:t) (i:int) (j:int): bool =
      assert (i <> j);
      assert (i < count vs);
      assert (j < count vs);
      Set.is_lower_bound i (IArr.elem j vs)

    let lt (vs:t) (i:int) (j:int): bool =
      assert (i <> j);
      assert (i < count vs);
      assert (j < count vs);
      Set.is_strict_lower_bound i (IArr.elem j vs)

    let empty: t =
      IArr.empty


    let push (n:int) (cs:(int*int*bool) list) (vs:t): t =
      let nvars = n + count vs
      and vsr = ref vs in
      for i = 0 to n - 1 do
        vsr := IArr.push Set.empty !vsr
      done;
      assert (IArr.length !vsr = nvars);
      List.iter
        (fun (i,j,strict) ->
          assert (i <> j);
          assert (i < nvars);
          assert (j < nvars);
          assert (not (strict && le vs j i));
          (* add i and the transitive closure to the lower bounds of j *)
          vsr := IArr.put
                   j
                   (Set.add i strict (IArr.elem j !vsr)
                    |> Set.union (IArr.elem i !vsr))
                   !vsr
        )
        cs;
      !vsr
  end



type t =
  | Proposition
  | Datatype
  | Any1
  | Variable of int     (* Datatype < Variable i, Any1 <= Variable i *)
  | Variable_type of int
  | Max of Set.t



let equal (s1:t) (s2:t): bool =
  match s1, s2 with
  | Proposition, Proposition
    | Datatype, Datatype
    | Any1, Any1 ->
     true
  | Variable i, Variable j | Variable_type i, Variable_type j when i = j ->
     true
  | Max s, Variable i | Variable i, Max s ->
     Set.is_singleton i false s
  | Max s, Variable_type i | Variable_type i, Max s ->
     Set.is_singleton i true s
  | Max s1, Max s2 ->
     Set.equal s1 s2
  | _, _ ->
     false



let type_of (s:t): t option =
  match s with
  | Proposition | Datatype ->
     Some Any1
  | Variable i ->
     Some (Variable_type i)
  | _ ->
     (* None *)
     assert false (* Illegal call ?? Really ?? *)


let max_of (s:t): t =
  match s with
  | Proposition ->
     assert false (* illegal call *)
  | Datatype -> Max Set.empty
  | Any1 -> Max Set.empty
  | Variable i -> Max (Set.singleton i false)
  | Variable_type i -> Max (Set.singleton i true)
  | Max _ -> s


let merge (s1:t) (s2:t): t =
  match s1, s2 with
  | Max s1, Max s2 ->
     Max (Set.union s1 s2)
  | _, _ ->
     assert false




let product (s1:t) (s2:t): t =
  match s1, s2 with
  | Proposition, _ ->
     s2
  | _, Proposition ->
     Proposition
  | Datatype, Datatype ->
     Datatype
  | Datatype, Any1
    | Any1, Datatype
    | Any1, Any1
    ->
     Any1
  | Datatype, Variable i | Any1, Variable i
    | Variable i, Datatype | Variable i, Any1 ->
     Variable i
  | Datatype, Variable_type i | Any1, Variable_type i
    | Variable_type i, Datatype | Variable_type i, Any1 ->
     Variable_type i
  | Variable i, Variable j ->
     if i = j then
       Variable i
     else
       Max (Set.add i false (Set.singleton j false))
  | Variable_type i, Variable j | Variable j, Variable_type i->
     if i = j then
       Variable_type i
     else
       Max (Set.add i true (Set.singleton j false))
  | Variable_type i, Variable_type j ->
     if i = j then
       Variable_type i
     else
       Max (Set.add i true (Set.singleton j true))
  | Max s, (Datatype|Any1) | (Datatype|Any1), Max s ->
     Max s
  | Variable i, Max s | Max s, Variable i ->
     Max (Set.add i false s)
  | Variable_type i, Max s | Max s, Variable_type i ->
     Max (Set.add i true s)
  | Max s1, Max s2 ->
     Max (Set.union s1 s2)



let sub (s1:t) (s2:t) (le:int->int->bool) (lt:int->int->bool): bool =
  (* Proposition < Datatype < Any1 <= Variable i *)
  match s1 with
  | Proposition ->
     true
  | Datatype ->
     begin
       match s2 with
       | Proposition ->
          false
       | _ ->
          true
     end
  | Any1 ->
     begin
       match s2 with
       | Proposition | Datatype ->
          false
       | _ ->
          true
     end
  | Variable i ->
     begin
       match s2 with
       | Proposition | Datatype | Any1 ->
          (* A sort variable cannot have a fixed upper bound *)
          false
       | Variable j | Variable_type j ->
          i = j || le i j
       | Max set2 ->
          assert false (* nyi *)
     end
  | Variable_type i ->
     begin
       match s2 with
       | Proposition | Datatype | Any1 ->
          false
       | Variable j ->
          i <> j &&  lt i j
       | Variable_type j ->
          i = j || le i j
       | Max set2 ->
          assert false (* nyi *)
     end
  | Max s1 ->
     assert (Set.count s1 <> 0);
     match s2 with
     | Proposition | Datatype | Any1 ->
        (* Sort variables have no fixed upper bound *)
        false
     | Variable j ->
        assert false (* nyi *)
     | Variable_type j ->
        assert false (* nyi *)
     | Max s2 ->
        assert (Set.count s2 <> 0);
        assert false (* nyi *)
