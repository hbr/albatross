open Fmlib

module Make (Io: Io.SIG):
sig
    val run_cli:  'a -> unit Io.t
    val run_eval: 'a -> unit Io.t
end
