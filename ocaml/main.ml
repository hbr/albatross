(*open Verify.Dummy*)

let write_package = ();;



try
  let _,efiles,_ = Arguments.parse ()
  in
  Validate.validate efiles;
  write_package
with
  Support.Exit_error str -> prerr_endline str; exit 1
| Parsing.Parse_error ->
    exit 1
| Sys_error str -> prerr_endline str; exit 1

