module Path = Fmlib_node.Path
module Fs   = Fmlib_node.File_system
module Io   = Fmlib_node.Node_io

let _ =
  Io.(
    let rec step () =
      getchar >>= function
      | None -> exit 1
      | Some c ->
         putchar c >>= function
         | None -> return ()
         | Some () -> step ()
    in
    execute @@ step ())
