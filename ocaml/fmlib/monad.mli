open Common_module_types

module type SIG_MIN =
  sig
    type _ t
    val return: 'a -> 'a t
    val (>>=): 'a t -> ('a -> 'b t) -> 'b t
  end

module type SIG_WITH_MAP =
  sig
    include SIG_MIN
    val map: ('a -> 'b) -> 'a t -> 'b t
  end



module type RESULT =
  sig
    include MONAD
    type error
    val throw: error -> 'a t
    val catch: 'a t -> (error -> 'a t) -> 'a t
    val continue: 'a t -> ('a -> 'z) -> (error -> 'z) -> 'z
  end




module type RESULT_IN =
  sig
    include MONAD
    module M: MONAD
    type error
    val throw: error -> 'a t
    val catch: 'a t -> (error -> 'a t) -> 'a t
    val lift: 'a M.t -> 'a t
  end


module type READER =
  functor (Env:ANY) ->
  sig
    include MONAD
    type env = Env.t
    val ask: env t
    val local: (env->env) -> 'a t -> 'a t
    val run: env -> 'a t -> 'a
  end



module type READER_INTO =
  functor (M:MONAD) (Env:ANY) ->
  sig
    include MONAD

    type env = Env.t

    val run: env -> 'a t -> 'a M.t
    val ask: env t
    val local: (env->env) -> 'a t -> 'a t
    val lift: 'a M.t -> 'a t
  end




module type STATE =
  functor (S:ANY) ->
  sig
    include MONAD
    type state = S.t
    val get: state t
    val put: state -> unit t
    val update: (state -> state) -> unit t
    val run: state -> 'a t -> 'a * state
    val eval: state -> 'a t -> 'a
    val state: state -> 'a t -> state
  end



module type STATE_INTO =
  functor (M:MONAD) (S:ANY) ->
  sig
    include MONAD
    type state = S.t
    val lift: 'a M.t -> 'a t
    val get: state t
    val put: state -> unit t
    val update: (state -> state) -> unit t
    val run: state -> 'a t -> ('a*state) M.t
    val eval: state -> 'a t -> 'a M.t
  end




module type STATE_WITH_RESULT =
  sig
    include MONAD
    type state
    type error
    val get: state t
    val put: state -> unit t
    val update: (state -> state) -> unit t
    val throw: error -> 'a t
    val catch: 'a t -> (error -> 'a t) -> 'a t
    val continue: state -> 'a t ->
                  (state -> 'a -> 'z) ->
                  (state -> error -> 'z) ->
                  'z
  end





module Of_sig_min (M:SIG_MIN): MONAD with type 'a t = 'a M.t

module Of_sig_with_map (M:SIG_WITH_MAP): MONAD with type 'a t = 'a M.t


module Result (Error:ANY): RESULT with type error = Error.t and
                                       type 'a t = ('a,Error.t) result

module Result_in (M:MONAD) (Error:ANY): RESULT_IN


module Reader: READER

module Reader_into: READER_INTO

module State: STATE


module State_into: STATE_INTO


module State_with_result (S:ANY) (Error:ANY)
       : STATE_WITH_RESULT with type state = S.t and
                                type error = Error.t

module String_buffer:
sig
  include MONAD
  val length: int t
  val putc: char -> unit t
  val getc: int -> char t
  val fill: char -> int -> unit t
  val put_string: string -> unit t
  val put_substring: string -> int -> int -> unit t
  val run: int -> 'a t -> string
end