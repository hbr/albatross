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


let interval_fold (f:'a->int->'a t) (a0:'a t) (start:int) (beyond:int): 'a t =
  assert (start <= beyond);
  let rec fold i a =
    if i = beyond then
      a
    else
      match a with
      | None ->
         None
      | Some a ->
         fold (i+1) (f a i)
  in
  fold start a0



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
