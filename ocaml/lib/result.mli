type  ('a,'e) t = ('a,'e) result

val continue: ('a,'e) result -> ('a->'z) -> ('e->'z) -> 'z


module Make (E: Common.ANY):
sig
  type error = E.t
  include Monad.S with
            type 'a t = ('a,E.t) result
  val throw: error -> 'a t
  val catch: 'a t -> (error->'a t) -> 'a t
end

module Within (M:Monad.S) (E: Common.ANY):
sig
  type error = E.t
  include Monad.S with
            type 'a t = ('a,E.t) result M.t
  val throw: error -> 'a t
  val catch: 'a t -> (error -> 'a t) -> 'a t
  val wrap: ('a,error) result M.t -> 'a t
  val unwrap: 'a t -> ('a,error) result M.t
end
