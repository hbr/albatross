let modules : string list ref = ref [];;


let add_module str = modules := str :: !modules;;


let write_package = ();;



Arg.parse [] add_module "Usage: main options files";
modules := List.rev !modules;

try
  Validate.validate !modules;
  write_package
with
  Support.Exit_error str -> prerr_endline str; exit 1
| Parsing.Parse_error ->
    exit 1
| Sys_error str -> prerr_endline str; exit 1

