open Lib

module Make (IO:Io.S):
sig
  val run: unit -> unit
end
