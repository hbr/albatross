open Container


module Set:
sig
  type t
  val empty: t
  val singleton: int -> bool -> t
  val equal: t -> t -> bool
  val add: int -> bool -> t -> t
  val union: t -> t -> t
  val is_lower_bound: int -> t -> bool
  val is_strict_lower_bound: int -> t -> bool
end
  =
  struct
    type t = bool IntMap.t (* maps to true, if type of variable is meant,
                              maps to false, if variable is meant *)
    let equal (a:t) (b:t) :bool = IntMap.equal (fun b1 b2 -> b1 = b2)  a b
    let empty = IntMap.empty
    let singleton (i:int) (strict:bool): t =
      IntMap.singleton i strict
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
  | Max s1, Max s2 ->
     Set.equal s1 s2
  | _, _ ->
     false

let maybe_sort_of (s:t): t option =
  match s with
  | Proposition | Datatype ->
     Some Any1
  | Variable i ->
     Some (Variable_type i)
  | _ ->
     None



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
  | _, _ ->
     let s1 = max_of s1
     and s2 = max_of s2 in
     merge s1 s2

let sub (s1:t) (s2:t) (le:int->int->bool): bool =
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
       | _ ->
          assert false (* nyi *)
     end
  | Variable_type i ->
     begin
       match s2 with
       | Proposition | Datatype | Any1 ->
          false
       | Variable j when i = j ->
          false
       | Variable_type j ->
          i = j || le i j
       | _ ->
          assert false (* nyi *)
     end
  | Max s1 ->
     assert false (* nyi *)
