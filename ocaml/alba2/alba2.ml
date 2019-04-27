open Fmlib

module Alba2 = Alba2_generic.Make (Ocaml_io.IO)

let _ = Alba2.run ()
