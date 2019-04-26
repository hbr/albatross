open Common


module type BASIC =
  sig
    type _ t
    type error
    val succeed: 'a -> 'a t
    val fail:    error -> 'a t
    val consumer: 'a t -> 'a t
    val map:     ('a -> 'b) -> 'a t -> 'b t
    val (>>=):   'a t -> ('a -> 'b t) -> 'b t
    val (<|>):   'a t -> 'a t -> 'a t
    val backtrackable: 'a t -> 'a t
    val commit: 'a -> 'a t
  end


module type COMBINATORS =
  functor (P:BASIC) ->
  sig
    val (>>-): 'a P.t -> ('a -> 'b P.t) -> 'b P.t
    val optional: 'a P.t -> 'a option P.t
    val one_of: 'a P.t list  -> 'a P.t
    val zero_or_more: 'a P.t -> 'a list P.t
    val one_or_more:  'a P.t -> 'a list P.t
    val skip_zero_or_more: 'a P.t -> int P.t
    val skip_one_or_more:  'a P.t -> int P.t
    val zero_or_more_separated: 'a P.t -> _ P.t -> 'a list P.t
    val one_or_more_separated: 'a P.t -> _ P.t -> 'a list P.t
    val (|=): ('a -> 'b) P.t -> 'a P.t -> 'b P.t
    val (|.): 'v P.t -> 'a P.t -> 'v P.t
  end




module Combinators: COMBINATORS =
  functor (P:BASIC) ->
  struct
    let (>>-) (p:'a P.t) (f:'a -> 'b P.t): 'b P.t =
      P.(backtrackable (p >>= commit >>= f))

    let optional (p:'a P.t): 'a option P.t =
      let open P in
      (map (fun a -> Some a) p)
      <|> succeed None

    let rec one_of (l:'a P.t list): 'a P.t =
      let open P in
      match l with
      | [] ->
         assert false (* Illegal call *)
      | [p] ->
         p
      | p :: ps ->
         p <|> one_of ps

    let zero_or_more (p:'a P.t): 'a list P.t =
      let open P in
      let rec many l =
        (p >>= fun a -> many (a::l))
        <|> succeed @@ List.rev @@ l
      in
      many []

    let one_or_more (p:'a P.t): 'a list P.t =
      P.(consumer p >>= fun a ->
          zero_or_more p >>= fun l ->
          succeed (a::l))

    let skip_zero_or_more (p:'a P.t): int P.t =
      let open P in
      let rec many i =
        (consumer p >>= fun _ -> many (i+1))
        <|> succeed i
      in
      many 0

    let skip_one_or_more (p:'a P.t): int P.t =
      let open P in
      p >>= fun _ ->
      skip_zero_or_more p
      >>= fun n -> succeed (n + 1)

    let one_or_more_separated (p:'a P.t) (sep: _ P.t): 'a list P.t =
      let open P in
      p >>= fun a ->
      zero_or_more (sep >>= fun _ -> p) >>= fun l ->
      succeed (a::l)

    let zero_or_more_separated (p:'a P.t) (sep: _ P.t): 'a list P.t =
      let open P in
      one_or_more_separated p sep
      <|> succeed []


    let (|=) (pf:('a->'b) P.t) (p:'a P.t): 'b P.t =
      let open P in
      pf >>= fun f -> p >>= fun a -> succeed (f a)

    let (|.) (v:'b P.t) (p:'a P.t): 'b P.t =
      let open P in
      map (fun v _ -> v) v |= p
  end
