(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Support
open Term

type t
val context: t -> Context.t
val count_terms: t -> int
val head_term: t -> term
val has_required_type: t -> bool
val string_of_required_type: t -> string
val string_of_head_term: t -> string
val string_of_complete_head_term: t -> string
val string_of_tvs: t -> string
val string_of_substitutions: t -> string
val make: type_term option -> int -> int -> int -> Context.t -> t
val copy: t -> t
val expect_argument: int -> t -> unit
val expect_boolean: t -> unit
val expect_type: type_term -> t -> unit
val add_variable: int -> t -> unit
val start_global_application: int -> int -> t -> unit
val complete_application: application_mode -> t -> unit
val start_quantified: Context.t -> t -> unit
val complete_quantified: bool -> t -> unit
val start_lambda:    Context.t -> bool -> t -> unit
val complete_lambda: bool -> int -> t -> unit
val start_inductive_set: Context.t -> t -> unit
val complete_inductive_set: int -> t -> unit
val expect_else_expression: t -> unit
val complete_if_expression: t -> unit
val start_as_expression: t -> unit
val expect_as_pattern: Context.t -> t -> unit
val complete_as_expression: t -> unit
val start_inspect: t -> unit
val start_cases: t -> unit
val start_case: Context.t -> t -> unit
val expect_case_result: t -> unit
val complete_case: t -> unit
val complete_inspect: int -> t -> unit
val has_undefined_globals: t -> bool
val start_term_application: int -> t -> unit
val is_fully_typed: t -> bool
val undefined_globals: t -> (int * int list) list
val update_context: Context.t -> t -> unit
val result_term: t -> term
