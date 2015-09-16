(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Term
open Signature

exception Illegal_term
type t
val occupy_boolean: Context.t -> t
val occupy_untyped: Context.t -> t
val occupy_context: Context.t -> t
val occupy_typed:   type_term -> Context.t -> t
val occupy_term:    term -> Context.t -> t
val release: t -> unit
val clone:   t -> t
val count_local: t -> int
val count_local_added:   t -> int
val expected_arity:      t -> int
val string_of_term:      term -> t -> string
val string_of_head_term: t -> string
val string_of_last_term: t -> string
val string_of_tvs:       t -> string
val string_of_substitutions: t -> string
val string_of_head_signature: t -> string
val string_of_last_signature: t -> string
val string_of_reduced_required_type: t -> string
val head_term: t -> term
val last_term: t -> term
val tvars:     t -> Tvars.t
val substituted_context_signature: t -> Sign.t
val normalized_result: t -> term
val push_expected: t -> unit
val drop_expected: t -> unit
val get_expected: int -> t -> unit
val expect_boolean_expression: t -> unit
val expect_boolean:     t -> unit
val expect_type:        type_term -> t -> unit
val expect_new_untyped: t -> unit
val add_leaf:   int -> Tvars.t -> Sign.t -> t -> unit
val expect_argument: t -> unit
val expect_function: int -> int -> t -> unit
val complete_function: t -> unit
val expect_lambda: bool -> Context.t -> t -> unit
val complete_lambda: int -> int array -> int -> bool -> t -> unit
val expect_quantified: Context.t -> t -> unit
val complete_quantified: bool -> t -> unit
val expect_if:      t -> unit
val complete_if:    bool -> t -> unit
val expect_case:    Context.t -> t -> unit
val complete_case:  t -> unit
val expect_inspect: t -> unit
val complete_inspect: int -> t -> unit
val expect_as:      t -> unit
val complete_as:    t -> unit
val specialize_head:t -> unit

val update_context: t -> unit

val is_valid:   term -> Context.t -> bool
