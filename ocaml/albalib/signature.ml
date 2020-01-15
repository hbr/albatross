(* All entries of a signature have some common elements. *)

type common = {
    typ: Term.typ;    (* complete type *)

    nargs: int;       (* number of arguments *)
    nb: int;          (* number of bound variables *)
    cnt: int;         (* size of the base context *)
    n_up: int;

    implicits: int;   (* how many implicits starting from here to first
                         explicit? *)
    explicits: int;   (* how many explicit arguments does the signature have ? *)
  }


(* A signature has either no arguments i.e. consists only of the common
   part. Or it has arguments. In the latter case it consists of the type of
   the first argument, the common parts and the remaining part of the
   signature .*)

type t =
  | Last of
      common
  | More of
      {
        arg: Term.typ;
        common: common;
        rest: t
      }


let make (cnt: int) (nb: int) (typ: Term.typ): t =
  Last {typ; nargs = 0; nb; cnt; n_up = 0; implicits = 0; explicits = 0}


let get_common (s: t): common =
  match s with
  | Last common ->
     common
  | More e ->
     e.common


let push (s: t) (typ: Term.typ) (arg: Term.typ) (implicit: bool): t =
  let common = get_common s in
  assert (0 < common.nb);
  More {
      arg;
      common =
        {typ;
         nargs = common.nargs + 1;
         nb    = common.nb - 1;
         cnt   = common.cnt;
         n_up  = 0;
         implicits =
           if implicit then
             common.implicits + 1
           else
             0;
         explicits =
           if implicit then
             common.explicits
           else
             common.explicits + 1;
        };
      rest = s;
    }





let up (n: int) (s: t): t =
  let common_up common =
    {common with n_up = common.n_up + n}
  in
  match s with
  | Last common ->
     Last (common_up common)
  | More e ->
     More {e with common = common_up e.common}


let base_context_size (s: t): int =
  (get_common s).cnt


let context_size (s: t): int =
  let common = get_common s in
  common.cnt + common.n_up + common.nb


let to_context_size (n: int) (s: t): t =
  let cnt0 = context_size s in
  assert (cnt0 <= n);
  up (n - cnt0) s


let count_arguments (s: t): int =
  (get_common s).nargs


let count_explicits (s: t): int =
  (get_common s).explicits

let count_first_implicits (s: t): int =
  (get_common s).implicits


let term_up (common: common) (term: Term.t): Term.t =
  Term.up_from common.n_up common.nb term


let typ (s: t): Term.typ =
  let common = get_common s in
  term_up common common.typ



let pop (s: t): (Term.typ * t) option =
  match s with
  | More entry ->
    Some (
      term_up entry.common entry.arg,
      up entry.common.n_up entry.rest
    )
  | _ ->
    None


let pop_safe (s: t): Term.typ * t =
  match pop s with
  | None ->
    assert false (* Illegal call! *)
  | Some res ->
    res
