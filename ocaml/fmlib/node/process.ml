open Js_of_ocaml
open Js


class type process =
  object
    method exit: int -> 'a meth
    method nextTick: (unit -> unit) callback -> unit meth
  end

let process: process t = Unsafe.eval_string "require('process')"

let next_tick (k:unit -> unit): unit =
  process##nextTick
    (wrap_callback k)

let exit (code:int): 'a  =
  Printf.printf "exiting with code %d\n" code;
  process##exit code
