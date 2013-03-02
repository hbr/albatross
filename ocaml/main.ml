

let write_package = ();;



try
  Validate.validate (Arguments.parse ());
  write_package
with
  Support.Exit_error str -> prerr_endline str; exit 1
| Parsing.Parse_error ->
    exit 1
| Sys_error str -> prerr_endline str; exit 1

