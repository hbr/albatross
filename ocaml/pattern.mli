open Term

val is_pattern: int -> term -> int -> Feature_table.t -> bool

val unify_with_pattern: term -> int -> term -> Context.t -> arguments * term list

val evaluated_as_expression: term -> Context.t -> term
