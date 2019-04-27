include
  Monad.Make(
      struct
        type 'a t = 'a option
        let make (a:'a): 'a t =
          Some a
        let bind (m:'a t) (f:'a -> 'b t): 'b t =
          match m with
          | None -> None
          | Some a -> f a
      end
    )

let has (o: 'a t): bool =
  match o with
  | None -> false
  | Some _ -> true

let value (o: 'a t): 'a =
  match o with
  | None ->
     assert false (* illegal call *)
  | Some x ->
     x


let of_bool (b:bool): unit t =
  if b then
    Some ()
  else
    None

let iter (f:'a -> unit) (m:'a t): unit =
  ignore (map f m)


let fold_interval (f:'a->int->'a t) (a0:'a) (start:int) (beyond:int): 'a t =
  assert (start <= beyond);
  let rec fold i a =
    if i = beyond then
      Some a
    else
      match f a i with
      | None ->
         None
      | Some a ->
         fold (i+1) a
  in
  fold start a0





let fold_array (f:'a->'b->int->'a t) (start:'a) (arr:'b array): 'a t =
  let len = Array.length arr
  in
  let rec fold a i =
    if i = len then
      Some a
    else
      match f a arr.(i) i with
       | Some a ->
          fold a (i+1)
       | None ->
          None
  in
  fold start 0









module Within (M:Monad.MONAD) =
  struct
    include
      Monad.Make(
          struct
            type 'a t = 'a option M.t
            let make (a:'a): 'a t =
              a |> make |> M.make
            let bind (m:'a t) (f:'a -> 'b t): 'b t =
              M.(m >>= fun opt ->
                 match opt with
                 | None -> make None
                 | Some a -> f a)
          end
        )
  end
