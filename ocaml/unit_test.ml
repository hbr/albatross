(* Library modules *)
let _ =
  Pretty_printer.test ();
  Character_parser.test ()



(* Albatross modules *)
let _ =
  Term_printer.test();
  Type_checker.test()
