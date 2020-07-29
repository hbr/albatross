(** Description of a type error *)

open Fmlib


type t =
  | Higher_universe of int
  | Not_a_type
  | Name_not_found of string
  | Not_yet_implemented of string



module Print (P: Pretty_printer.SIG) =
struct
    let print (error: t): P.t =
        let open P in
        match error with
        | Higher_universe uni ->
            string ("Universe level " ^ string_of_int uni ^ " not allowed")
            <+> cut

        | Not_a_type ->
            string "I have expected a type, but this is not a type."
            <+> cut

        | Not_yet_implemented what ->
            string (what ^ " is not yet implemented") <+> cut

        | Name_not_found name ->
            string ("Cannot find <" ^ name ^ ">") <+> cut
end
