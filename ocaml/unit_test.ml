(* Library modules *)
let _ =
  Pretty_printer.test ();
  Pretty_printer2.test ();
  Character_parser.test ()



(* Albatross modules *)
let _ =
  Term_printer.test();
  Type_checker.test()
