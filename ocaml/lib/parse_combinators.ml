open Common


module type BASIC =
  sig
    type token
    type error
    type 'a res = ('a,error) result

    include Monad.MONAD

    val succeed: 'a -> 'a t
    val fail: error -> 'a t
    val consumer: 'a t -> 'a t
    val backtrackable: 'a t -> 'a t
    val commit: 'a -> 'a t
    val catch: 'a t -> (error -> 'a t) -> 'a t
  end





module type COMBINATORS =
  functor (P:BASIC) ->
  sig
    val (>>-): 'a P.t -> ('a -> 'b P.t) -> 'b P.t
    val (>>|): 'a P.t -> (P.error -> 'a P.t) -> 'a P.t
    val optional: 'a P.t -> 'a option P.t
    val one_of: 'a P.t list -> (P.error list -> P.error) -> 'a P.t
    val zero_or_more: 'a P.t -> 'a list P.t
    val one_or_more:  'a P.t -> 'a list P.t
    val (|=): ('a -> 'b) P.t -> 'a P.t -> 'b P.t
    val (|.): 'v P.t -> 'a P.t -> 'v P.t
  end





module Combinators: COMBINATORS =
  functor (P:BASIC) ->
  struct
    let (>>-) (p:'a P.t) (f:'a -> 'b P.t): 'b P.t =
      P.(backtrackable (p >>= commit >>= f))

    let (>>|) = P.catch

    let optional (p:'a P.t): 'a option P.t =
      let open P in
      (map (fun a -> Some a) p) >>| fun _ -> succeed None

    let one_of (l:'a P.t list) (f:P.error list -> P.error): 'a P.t =
      let open P in
      let rec one_of l le =
        match l with
        | [] ->
           assert false (* Illegal call *)
        | [p] ->
           p >>| fun e -> fail (List.rev (e::le) |> f)
        | p :: ps ->
           p >>| fun e -> one_of ps (e::le)
      in
      one_of l []

    let zero_or_more (p:'a P.t): 'a list P.t =
      let open P in
      let rec many l =
        (p >>= fun a -> many (a::l))
        >>| (fun _ -> succeed (List.rev l))
      in
      many []

    let one_or_more (p:'a P.t): 'a list P.t =
      P.(consumer p >>= fun a ->
          zero_or_more p >>= fun l ->
          succeed (a::l))

    let (|=) (pf:('a->'b) P.t) (p:'a P.t): 'b P.t =
      let open P in
      pf >>= fun f -> p >>= fun a -> succeed (f a)

    let (|.) (v:'b P.t) (p:'a P.t): 'b P.t =
      let open P in
      map (fun v _ -> v) v |= p
  end
