open Fmlib

module Make (Io: Io.SIG):
sig
    val run_cli: 'a -> unit Io.t
end
