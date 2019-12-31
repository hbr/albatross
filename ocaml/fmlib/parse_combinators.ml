open Common

module type COMBINATORS =
  sig
    type 'a tp
    val optional: 'a tp -> 'a option tp
    val one_of: 'a tp list -> 'a tp
    val loop: 'a -> ('a -> ('a,'b) Loop_state.t tp) -> 'b tp
    val zero_or_more: 'a tp -> 'a list tp
    val one_or_more:  'a tp -> 'a list tp
    val skip_zero_or_more: 'a tp -> int tp
    val skip_one_or_more:  'a tp -> int tp
    val zero_or_more_separated: 'a tp -> _ tp -> 'a list tp
    val one_or_more_separated: 'a tp -> _ tp -> 'a list tp
    val (|=): ('a -> 'b) tp -> 'a tp -> 'b tp
    val (|.): 'v tp -> 'a tp -> 'v tp
  end

module type ADD_COMBINATORS =
  functor (P:Generic_parser.BASIC) ->
  sig
    include COMBINATORS with type 'a tp = 'a P.t
  end



module Add_combinators: ADD_COMBINATORS =
  functor (P:Generic_parser.BASIC) ->
  struct
    type 'a tp = 'a P.t

    let optional (p:'a P.t): 'a option P.t =
      let open P in
      (map (fun a -> Some a) p)
      <|> return None

    let rec one_of (l:'a P.t list): 'a P.t =
      let open P in
      match l with
      | [] ->
         assert false (* Illegal call *)
      | [p] ->
         p
      | p :: ps ->
         p <|> one_of ps


    let loop (a:'a) (f: 'a -> ('a,'b) Loop_state.t P.t): 'b P.t =
      let open P in
      let rec loop st =
        Loop_state.fold
          (fun a -> f a >>= loop)
          return
          st
      in
      f a >>= loop



    let zero_or_more (p:'a P.t): 'a list P.t =
      let open P in
      loop
        []
        (fun lst ->
          (p >>= fun a ->
           return @@ Loop_state.more (a :: lst))
          <|> let st = Loop_state.exit (List.rev lst) in
              if lst = [] then
                return st
              else
                succeed st)


    let one_or_more (p:'a P.t): 'a list P.t =
      P.(consumer p >>= fun a ->
          zero_or_more p >>= fun l ->
          succeed (a::l))


    let skip_zero_or_more (p:'a P.t): int P.t =
      let open P in
      let rec many i =
        (consumer p >>= fun _ -> many (i+1))
        <|> if i > 0 then succeed i else return i
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
      <|> return []


    let (|=) (pf:('a->'b) P.t) (p:'a P.t): 'b P.t =
      let open P in
      pf >>= fun f -> map f p

    let (|.) (v:'b P.t) (p:'a P.t): 'b P.t =
      let open P in
      map (fun v _ -> v) v |= p
  end
