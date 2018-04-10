module type MONAD0 =
  sig
    type _ t
    val make: 'a -> 'a t
    val bind: 'a t -> ('a -> 'b t) -> 'b t
  end

module type MONAD =
  sig
    type _ t
    val make:  'a -> 'a t
    val bind:  'a t -> ('a -> 'b t) -> 'b t
    val apply: ('a->'b) t -> 'a t -> 'b t
    val map:   ('a -> 'b) -> 'a t -> 'b t
    val (>>=): 'a t -> ('a -> 'b t) -> 'b t
    val (>>):  'a t -> 'b t -> 'b t
    val sequence: 'a t list -> 'a list t
    val map_list: 'a list -> ('a -> 'b t) -> 'b list t
    val map_array: 'a array -> ('a -> 'b t) -> 'b array t
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





module type STATE =
  sig
    include MONAD
    type state
    val get: state t
    val put: state -> unit t
    val update: (state -> state) -> unit t
    val run: state -> 'a t -> 'a * state
    val eval: state -> 'a t -> 'a
    val state: state -> 'a t -> state
  end



module type STATE_INTO =
  sig
    include MONAD
    module M: MONAD
    type state
    val lift: 'a M.t -> 'a t
    val get: state t
    val put: state -> unit t
    val update: (state -> state) -> unit t
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





module Make (M:MONAD0): MONAD with type 'a t = 'a M.t

module Result (Error:Common.ANY): RESULT with type error = Error.t and
                                              type 'a t = ('a,Error.t) result

module Result_in (M:MONAD) (Error:Common.ANY): RESULT_IN


module State (St:Common.ANY): STATE with type state = St.t


module State_into (M:MONAD) (St:Common.ANY)
       : STATE_INTO with type state = St.t


module State_with_result (S:Common.ANY) (Error:Common.ANY)
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
  val put_substring: int -> int -> string -> unit t
  val run: int -> 'a t -> string
end
