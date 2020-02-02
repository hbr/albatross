(**

    [Gamma_holes] is a context with holes which can be filled later. A hole is a
    local unnamed variable with a type (i.e. an assumption that an element with
    this type exists), initially without value. Later on the value can be
    provided.

*)


type t


val context: t -> Gamma.t
(** The current context with holes. *)


val base_context: t -> Gamma.t
(** The initial context without holes. *)


val count: t -> int
(** The size of the context. *)


val count_base: t -> int
(** The size of the base context. *)


val count_bounds: t -> int
(** The number of bound variables which have been entered. *)


val is_hole: int -> t -> bool
(** Is the variable a hole? *)


val is_bound: int -> t -> bool
(** Is the variable a bound variable? *)


val bound_number: int -> t -> int
(**
    [bound_number idx gh]

    Return the number of the bound variable at [idx].

    Precondition:
    {[is_bound idx gh]}
*)





(*
val level_of_bound: int -> t -> int
(** [level_of_bound i gh]

    Compute the level of the [i]th bound variable.

    Precondition:
    {[i< count_bounds gh]}
*)
*)


val has_value: int -> t -> bool
(** Has the variable a value i.e. is it a hole with value. *)


val value: int -> t -> Term.t option
(** The optional value of the hole. *)


val unfilled_holes: int -> Term.t -> t -> int list
(** [unfilled_holes cnt0 term gh]

    List of unfilled holes in [term] starting at level [cnt0].

    The returned list contains the De Bruijn indices of the unfilled holes.

    Precondition:
    {[cnt0 <= count gh]}

*)


val expand: Term.t -> t -> Term.t
(** [expand term gh] Replace all holes in [term] with its values, if
available. *)


val is_expanded: Term.t -> t -> bool
(** [is_expanded term gh] Does [term] not have any holes which have already got
a value?  *)



val fill_hole: int -> Term.t -> t -> t
(** [fill_hole idx value gh] Fill the hole at [idx] with [value].

    Preconditions:
    {[is_hole idx gh
      not (has_value idx gh)
      is_expanded value gh
    ]}
*)


val push_hole: Term.typ -> t -> t
(** [push_hole typ gh] Add a hole of type [typ] to [gh]. *)


val push_bound: string -> bool -> Term.typ -> t -> t
(** [push_bound name is_typed gh] adds a bound variable to the context. The
bound variable can be later used to construct binders like [Pi (arg_tp, res_tp,
info] or [Lambda (arg_tp, exp, info]. [is_typed] is used to construct the
binder. *)




(*
val type_of_term: Term.t -> t -> Term.typ
(** [type_of_term term gh] Compute the type of [term]. The result does not
contain holes which have been filled.*)
*)

(*
val pi: int -> int -> Term.typ -> t -> Term.typ
(** [pi cnt0 nbounds result_tp gh]

    Compute a product type with [result_tp] using the [nbounds] most recently
    introduced bound variables.

    {[all (a: A) (b: B) ... : RT]}

    Preconditions:
    {[cnt0   <= count gh
      0      <  nbound
      nbound <= count_bounds gh
      cnt0   <= level_of_bound (nbound - 1)]}
    and [A, B, ..., RT] do not contain unfilled holes starting at level [cnt0].

*)

val lambda: int -> int -> Term.t -> t -> Term.t
(** [lambda cnt0 nbounds exp gh]

    Compute a function term with the inner expression [exp] using the [nbounds]
    most recently introduced bound variables.

    {[\ (a: A) (b: B) ... := exp]}

    Preconditions:
    {[cnt0   <= count gh
      0      <  nbound
      nbound <= count_bounds gh
      cnt0   <= level_of_bound (nbound - 1)]}
    and [A, B, ..., exp] do not contain unfilled holes starting at level [cnt0].

*)
*)

val make: Gamma.t -> t
