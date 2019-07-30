open Fmlib
open Albalib

module Alba2 = Alba_console.Make (Ocaml_io.IO)

let _ = Alba2.run ()
