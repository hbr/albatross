module type S =
  sig
    type env
    include Monad.S
    val get: env t
    val local: (env -> env) -> 'a t -> 'a t
    val eval: env -> 'a t -> 'a
  end


module Make (ENV: sig type t end) =
  struct
    type env = ENV.t
    include
      Monad.Make(
          struct
            type 'a t = env -> 'a * env
            let make (a:'a): 'a t =
              fun e -> a,e
            let bind (m:'a t) (f:'a -> 'b t): 'b t =
              (fun e ->
                let a,e = m e in
                f a e)
          end
        )

    let get: env t =
      fun e -> e,e

    let local (f:env->env) (m:'a t): 'a t =
      (fun e ->
        let a,_ = m (f e) in
        a,e)

    let eval (e:env) (m:'a t): 'a =
      m e |> fst
  end
