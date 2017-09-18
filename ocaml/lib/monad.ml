module type S0 =
  sig
    type _ t
    val make: 'a -> 'a t
    val bind: 'a t -> ('a -> 'b t) -> 'b t
  end

module type S =
  sig
    type _ t
    val make:  'a -> 'a t
    val bind:  'a t -> ('a -> 'b t) -> 'b t
    val apply: ('a->'b) t -> 'a t -> 'b t
    val map:   ('a -> 'b) -> 'a t -> 'b t
    val (>>=): 'a t -> ('a -> 'b t) -> 'b t
    val (>>):  'a t -> 'b t -> 'b t
    val sequence: 'a t list -> 'a list t
  end

module Make (M:S0): S with type 'a t = 'a M.t =
  struct
    include M
    let (>>=) = bind
    let map (f:'a -> 'b) (m:'a t): 'b t =
      m >>= fun a -> make (f a)
    let apply (f: ('a -> 'b) t) (m:'a t): 'b t =
      f >>= fun f -> map f m
    let sequence (lst:'a t list): 'a list t =
      List.fold_right
        (fun m mlst ->
          mlst >>= fun lst ->
          m >>= fun a ->
          make (a :: lst)
        )
        lst
        (make [])
    let (>>) (m1:'a t) (m2:'b t): 'b t =
      m1 >>= fun _ -> m2
  end
