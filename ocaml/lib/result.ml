type ('a,'e) t = ('a,'e) result


let continue (r:('a,'e) result) (f1:'a->'z) (f2:'e->'z): 'z =
  match r with
  | Ok a ->
     f1 a
  | Error e ->
     f2 e


module Make (E: Common.ANY) =
  struct
    type error = E.t
    include
      Monad.Make(
          struct
            type 'a t = ('a,error) result
            let make (a:'a): 'a t = Ok a
            let bind (m:'a t) (f:'a -> 'b t): 'b t =
              match m with
              | Ok a -> f a
              | Error e -> Error e
          end
        )
    let throw (e:error): 'a t =
      Error e
    let catch (m:'a t) (f:error->'a t): 'a t =
      match m with
      | Ok a -> m
      | Error e -> f e
  end


module Within (M:Monad.S) (E: Common.ANY) =
  struct
    module M = M
    type error = E.t
    include
      Monad.Make(
          struct
            type 'a t = ('a,error) result M.t
            let make (a:'a): 'a t =
              Ok a |> M.make
            let bind (m:'a t) (f:'a -> 'b t): 'b t =
              M.(m >>= fun res ->
                 match res with
                 | Ok a ->
                    f a
                 | Error e ->
                    Error e |> make
              )
          end)
    let unwrap (m:'a t): ('a,error) result M.t =
      m
    let wrap (m:('a,error) result M.t): 'a t =
      m
  end
