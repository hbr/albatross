
type t =
  | Empty of Term.typ

  | Some_args of
      {
        typ: Term.typ;    (* complete type *)
        arg: Term.typ;    (* first argument *)
        implicits: int;   (* how many implicits starting from here to first
                             explicit? *)
        explicits: int;   (* how many explicit arguments does the signature
                             have ? *)
        nargs: int;       (* number of arguments *)
        rest: t
      }


let count_args (s: t): int * int * int =
  match s with
  | Empty _ ->
     0, 0, 0
  | Some_args args ->
     args.implicits, args.explicits, args.nargs



let count_explicit_args (s: t): int =
  let _, explicits, _ = count_args s in
  explicits



let count_first_implicits (s: t): int =
  let implicits, _, _ = count_args s in
  implicits


let count (s: t): int =
  let _, _, nargs = count_args s in
  nargs


let has_args (s: t): bool =
  match s with
  | Empty _ ->
     false
  | _ ->
     true


let typ (s: t): Term.typ =
  match s with
  | Empty tp ->
     tp
  | Some_args args ->
     args.typ


let arg_typ (s: t): Term.typ =
  match s with
  | Empty _ ->
     assert false (* Illegal call! *)

  | Some_args args ->
     args.arg



let make (tp: Term.typ): t =
  Empty tp


let push (s: t) (typ: Term.typ) (arg: Term.typ) (implicit: bool): t =
  let implicits, explicits, nargs = count_args s
  in
  Some_args {
      typ;
      arg;
      implicits =
        if implicit then
          implicits + 1
        else
          implicits;
      explicits =
        if implicit then
          explicits
        else
          explicits + 1;
      nargs = nargs + 1;
      rest = s
    }
