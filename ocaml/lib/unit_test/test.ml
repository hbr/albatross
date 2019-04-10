open Lib

let _ =
  Document.test ();
  Pretty_printer.test ();
  Pretty_printer2.test ();
  Character_parser.test ()
