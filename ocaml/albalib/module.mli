open Fmlib

module Make (Io: Io.SIG):
sig
    val run: _ -> unit Io.t
end
