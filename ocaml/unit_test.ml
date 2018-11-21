(* Library modules *)
let _ =
  Document.test ();
  Pretty_printer.test ();
  Character_parser.test ()



(* Albatross modules *)
let _ =
  Term_printer.test();
  Term_printer2.test();
  Type_checker.test()
