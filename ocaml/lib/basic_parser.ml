open Common
open Common_module_types
open Parse_combinators




module Buffer (T:ANY) =
  struct
    type token = T.t
    type consumed = bool
    type is_buffering = bool
    type committing = bool
    type committed  = bool
    type consumption_length = int
    type t = {
        mutable consumption: token list;
        mutable lookahead: token list;
        mutable consumed: consumed;
        mutable nc: consumption_length;
        mutable isbuf: is_buffering;
        mutable committing: committing;
        mutable committed:  committed;
        mutable stack:
                  (is_buffering
                   * consumed
                   * consumption_length
                   * committing
                   * committed) list
      }
    let init (_:unit): t =
      {consumption = []; lookahead = []; consumed = false;
       nc = 0; isbuf = false; committing = false; committed = false;
       stack = []}

    let no_lookahead (b:t): bool =
      b.lookahead = []

    let consume (t:token) (b:t): unit =
      assert (b.lookahead = []); (* Illegal call: Cannot consume tokens as
                                    long as there are tokens in the lookahead
                                    buffer. *)
      if b.isbuf then
        (b.consumption <- t :: b.consumption;
         b.nc <- b.nc + 1;
         if b.committing && not b.committed then
           (b.committed <- true;
            match b.stack with
            | [] ->
               b.isbuf <- false
            | (isbuf,_,_,_,_) :: _ ->
               b.isbuf <- isbuf)
        );
      b.consumed <- true

    let reject (t:token) (b:t): unit =
      assert (b.lookahead = []); (* Illegal call: Cannot reject tokens as long
                                    as there are tokens in the lookahead
                                    buffer. *)
      b.lookahead <- t :: b.lookahead

    let set_consumed (c:consumed) (b:t): unit =
      b.consumed <- b.consumed || c

    let reset_consumed (b:t): consumed =
      let c = b.consumed in
      b.consumed <- false;
      c

    let push (b:t): unit =
      b.stack <-
        (b.isbuf, b.consumed, b.nc, b.committing, b.committed)
        :: b.stack

    let pop (b:t): is_buffering
                   * consumed
                   * consumption_length
                   * committing
                   * committed =
      match b.stack with
      | [] ->
         assert false (* Illegal call. *)
      | top :: rest ->
         b.stack <- rest;
         top

    let start_backtrack (b:t): unit =
      push b;
      b.consumed <- false;
      b.isbuf <- true;
      b.committing <- false;
      b.committed  <- false

    let commit (b:t): unit =
      assert (b.isbuf);
      assert (not b.committing);
      assert (not b.committed);
      b.committing <- true

    let remove_consumption (nc:consumption_length) (la:bool) (b:t): unit =
      assert (nc <= b.nc);
      while nc <> b.nc do
        match b.consumption with
        | [] ->
           assert false (* Illegal call *)
        | t :: ts ->
           b.consumption <- ts;
           b.nc <- b.nc - 1;
           if la then
             b.lookahead <- t :: b.lookahead
      done

    let end_backtrack_success (b:t): unit =
      let isbuf,c,nc,comm,commd = pop b in
      b.isbuf <- isbuf;
      b.consumed <- c || b.consumed;
      b.committing <- comm;
      b.committed  <- commd;
      if not isbuf then
        remove_consumption nc false b

    let end_backtrack_fail (b:t): unit =
      assert (not b.committed || b.consumed); (* committed => consumed *)
      let isbuf,c,nc,comm,commd = pop b in
      if not b.committed then
        (b.consumed <- c;
         remove_consumption nc true b)
      else if not isbuf then
         remove_consumption nc false b;
      b.isbuf <- isbuf;
      b.committing <- comm;
      b.committed  <- commd



    let pop_lookahead (b:t): token list =
      let la = b.lookahead in
      b.lookahead <- [];
      la
  end (* Buffer *)






module Basic (T:ANY) (S:ANY) (E:ANY) (F:ANY):
sig
  include BASIC with type token = T.t and
                     type error = E.t
  type final = F.t
  type state = S.t

  type parser

  val parser: state -> final t -> parser

  val expect: (state -> token -> 'a res * state) -> 'a t
  val get: state t
  val put: state -> unit t
  val update: (state -> state) -> unit t

  val needs_more: parser -> bool
  val has_ended:  parser -> bool
  val state: parser -> state
  val result: parser -> final res
  val lookahead: parser -> token list

  val put_token: parser -> token -> parser
end =
  struct
    type token = T.t
    type lookaheads = token list
    type error = E.t
    type state = S.t
    type final = F.t
    type 'a res = ('a,error) result

    module B = Buffer (T)

    type parser =
      | Final of state * final res * lookaheads
      | More of state * (state -> token -> parser)


    let state (p:parser): state =
      match p with
      | Final (st,_,_) | More (st,_) ->
         st

    let needs_more (p:parser): bool =
      match p with
      | More _ -> true
      | _ -> false

    let has_ended (p:parser): bool =
      not (needs_more p)

    let lookahead (p:parser): token list =
      match p with
      | Final (_, _, la) ->
         la
      | _ ->
         assert false (* Illegal call *)

    let result (p:parser): final res =
      match p with
      | Final (_, r, _) ->
         r
      | _ ->
         assert false (* Illegal call *)

    let put_token (p:parser) (t:token): parser =
      match p with
      | Final (st,r,las) ->
         Final (st, r, t :: las)
      | More (st, f) ->
         f st t

    module K =
      struct
        (* Invariant: Every continuation function handles the lookahead before
           applying an new parser. *)
        type 'a t = 'a res -> state -> parser
      end


    module M =
      struct
        (* Invariant: No parser of type ['a t] is ever called with some
           lookahead tokens in the buffer. The lookahead tokens are handled by
           the continuation function before calling any new parser of type ['a
           t]. *)
        type 'a t =  B.t -> state -> 'a K.t -> parser

        let apply_lookahead (b:B.t) (p:'a t) (st:state) (k:'a K.t): parser =
          let la = B.pop_lookahead b in
          assert (B.no_lookahead b);
          List.fold_left put_token (p b st k) la

        let make (a:'a) (b:B.t) (st:state) (k:'a K.t): parser =
          assert (B.no_lookahead b);
          k (Ok a) st

        let bind (p:'a t) (f:'a -> 'b t) (b:B.t) (st:state) (k:'b K.t): parser =
          assert (B.no_lookahead b);
          p b st
            (fun r st ->
              match r with
              | Ok a ->
                 apply_lookahead b (f a) st k
              | Error e ->
                 k (Error e) st )
      end
    include Monad.Make (M)


    let parser (st:state) (p:final t): parser =
      let b = B.init () in
      p b st
        (fun r st -> Final (st, r, b.lookahead))

    let get (_:B.t) (st:state) (k: state K.t): parser =
      k (Ok st) st

    let put (st:state) (_:B.t) (_:state) (k:unit K.t): parser =
      k (Ok ()) st

    let update (f:state->state) (_:B.t) (st:state) (k:unit K.t): parser =
      k (Ok ()) (f st)

    let succeed: 'a -> 'a t = make

    let fail (e:error) (b:B.t) (st:state) (k:'a K.t): parser =
      assert (B.no_lookahead b);
      k (Error e) st

    let consumer (p:'a t) (b:B.t) (st:state) (k:'a K.t): parser =
      let c0 = B.reset_consumed b in
      p b st
        (fun r st ->
          let c1 = b.consumed in
          B.set_consumed c0 b;
          (match r with
           | Ok _ ->
              assert c1
           | _ ->
              ());
          k r st)

    let expect
          (f:state->token->'a res * state) (b:B.t) (st:state) (k:'a K.t)
        : parser =
      assert (B.no_lookahead b);
      More( st,
            (fun st t ->
              let r,st = f st t in
              match r with
              | Ok a ->
                 B.consume t b;
                 k (Ok a) st
              | Error e ->
                 B.reject t b;
                 k (Error e) st) )

    let catch (p:'a t) (f:error -> 'a t) (b:B.t) (st:state) (k:'a K.t): parser =
      assert (B.no_lookahead b);
      let c0 = B.reset_consumed b in
      p b st
        (fun r st ->
          let c1 = b.consumed in
          B.set_consumed c0 b;
          match r with
          | Error e when not c1 ->
             M.apply_lookahead b (f e) st k
          | _ ->
             k r st)

    let backtrackable (p:'a t) (b:B.t) (st0:state) (k:'a K.t): parser =
      assert (B.no_lookahead b);
      B.start_backtrack b;
      p b st0
        (fun r st1 ->
          match r with
          | Ok _ ->
             B.end_backtrack_success b;
             k r st1
          | Error _ ->
             B.end_backtrack_fail b;
             k r st0)

    let commit (a:'a) (b:B.t) (st:state) (k:'a K.t): parser =
      B.commit b;
      succeed a b st k
  end (* Basic *)
