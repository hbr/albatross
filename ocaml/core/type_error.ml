(** Description of a type error *)

open Fmlib


type t =
  | Higher_universe of int
  | Not_a_type
  | Naming_no_type_variable
  | Naming_type_variable
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

        | Naming_no_type_variable ->
            wrap_words
                "This identifier must not start with an upper case letter. \
                Identifiers starting with upper case letters are allowed \
                only for types and type constructors."
            <+> cut

        | Naming_type_variable ->
            wrap_words
                "This identifier must not start with a lower case letter. \
                Identifiers starting with lower case letters are allowed \
                only for object variables, proofs and propositions."
            <+> cut

        | Not_yet_implemented what ->
            string (what ^ " is not yet implemented") <+> cut

        | Name_not_found name ->
            string ("Cannot find <" ^ name ^ ">") <+> cut
end
