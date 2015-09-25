open Term
open Support

val case_variables: info -> expression -> bool -> Context.t -> expression * int array

val result_term: info_expression -> Context.t -> term

val boolean_term: info_expression -> Context.t -> term

val typed_term: info_expression -> type_term -> Context.t -> term
