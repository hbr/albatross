open Container


module IArr = Immutable_array


(* Set of lower bound sort variables. A variable can be either a strict lower
   bound or a lower bound in the set. *)
module Set =
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

    let bindings (s:t): (int*bool) list =
      IntMap.bindings s

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

    let type_of (s:t) (n:int): t option =
      try
        Some
          (IntMap.mapi
             (fun i b ->
               if i < 0 || n <= i || b then
                 raise Not_found
               else
                 true)
             s)
      with Not_found ->
        Printf.printf "Sorts.Set.type_of s %d  no type\n" n;
        None

    let is_lower_bound (i:int) (s:t): bool =
      IntMap.mem i s

    let is_strict_lower_bound (i:int) (s:t): bool =
      try
        IntMap.find i s
      with Not_found ->
        false
  end




(* Variables implements an array of sort variables. Each sort variable is
   characterized by its set of lower bounds. *)
module Variables =
  struct
    type t = Set.t IArr.t

    let count (vs:t): int =
      IArr.length vs

    let le (i:int) (j:int) (vs:t): bool =
      assert (i <> j);
      assert (i < count vs);
      assert (j < count vs);
      Set.is_lower_bound i (IArr.elem j vs)

    let lt (i:int) (j:int) (vs:t): bool =
      assert (i <> j);
      assert (i < count vs);
      assert (j < count vs);
      Set.is_strict_lower_bound i (IArr.elem j vs)

    let empty: t =
      IArr.empty


    let push (n:int) (cs:(int*int*bool) list) (vs:t): t =
      (* Add [n] new sort variables and the constraints [cs] to the variables
         [vs].

         A constraint consist of a lower variable, a higher variable and a
         strictness flag. With the strictness flag set, the lower variable is
         strictly lower than the higher variable.

         The new constraints must not introduce any circularity.

       *)
      let nvars = n + count vs
      and vsr = ref vs in
      for i = 0 to n - 1 do
        vsr := IArr.push Set.empty !vsr
      done;
      assert (IArr.length !vsr = nvars);
      (* Iterate through all constraints [i,j,strict] and add [i] as a
         (strict) lower bound to [j]. Avoid cyclicity *)
      List.iter
        (fun (i,j,strict) ->
          assert (i <> j);
          assert (i < nvars);
          assert (j < nvars);
          assert (not (strict && le j i vs)); (* Illegal call: No cycles
                                                 allowed. *)
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
  | Max of Set.t

let variable (i:int): t =
  Max (Set.singleton i false)

let variable_type (i:int): t =
  Max (Set.singleton i true)

let equal (s1:t) (s2:t): bool =
  match s1, s2 with
  | Proposition, Proposition
    | Datatype, Datatype
    | Any1, Any1 ->
     true
  | Max set1, Max set2 ->
     Set.equal set1 set2
  | _, _ ->
     false



let type_of (s:t) (n:int): t option =
  match s with
  | Proposition | Datatype ->
     Some Any1
  | Any1 ->
     None
  | Max set ->
     Option.(
      Set.type_of set n >>= fun set ->
      Some (Max set))




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
  | (Datatype | Any1), Max set | Max set, (Datatype | Any1) ->
     Max set
  | Max set1, Max set2 ->
     Max (Set.union set1 set2)



let sub (s1:t) (s2:t) (vs:Variables.t): bool =
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
  | Max set1 ->
     begin
       match s2 with
       | Datatype | Proposition | Any1 ->
          (* A sort variable cannot have a fixed upper bound *)
          false
       | Max set2 ->
          IntMap.for_all
            (fun i bi ->
              IntMap.for_all
                (fun j bj ->
                  if not bi || bj then
                    i = j || Variables.le i j vs
                  else
                    begin
                      assert bi;
                      assert (not bj);
                      i <> j && Variables.lt i j vs
                    end
                )
                set2
            )
            set1
     end
