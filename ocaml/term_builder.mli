(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

(** Structure to build terms *)

open Signature
open Term

type t
      (** The type of the structure. It consists of the expected signature, an
          array of type variables with their substitutions and a list of
          terms. *)

val signature:         t -> Sign.t
    (** The expected signature *)

val signature_string:  t -> string
    (** The expected signature as a string *)

val substitution_string: t -> string
    (** The substitutions of the type variables as a string *)

val concepts_string:   t -> string
    (** The concepts of the type variables as a string *)

val count:            t -> int
    (** The number of type variables with and without concept. *)

val make:              type_term -> Context.t -> t
    (** [make tp c] makes a term builder for a term with the expected type
        [tp] in the contexct [c]. *)

val expect_function:   int -> t -> unit
    (** [expect_function nargs tb] converts the currently expected signature
        to a function signature with [nargs] arguments and adds [nargs] fresh
        type variables, one for each argument.  *)

val complete_function: int -> t -> unit
  (** [complete_function nargs tb] completes the current function with [nargs]
      arguments, i.e.

      a) Pops the [nargs] arguments and the function term off the term list
      and push the corresponding application to the term list.

      b) Removes the bottom [nargs] type variables from [tb.tvars] (all must
      have proper substitutions)

      Note: The signature is meaningless (it is just the expected signature
      of the last argument. If there are more arguments to come, then
      [expect_argument] will put a new expected signature into the
      accumulator.  *)

val expect_argument:   int -> t -> unit
  (** [expect_argument i tb] lets the term builder [tb] expect the [i]th
      argument as the next term. It puts the type variable [i] as the expected
      signature *)


val add_leaf:          int ->  Tvars.t -> Sign.t ->  t -> t
  (** [add_leaf i tvs s tb] adds the term [i,tvs,s] as an elementary term to
      the term builder [tb] *)

val expect_lambda:     int -> t -> unit
   (** [expect_lambda nargs tb] prepares the term builder [tb] to expect a
       lambda expression with [nargs] arguments. It assumes that the currently
       expected signature is either callable i.e. has [nargs] arguments and a
       result type or the result type is downgradable (PREDICATE or
       FUNCTION). It puts a constant signature with the expected return type
       of the lambda expression as the expected signature. *)

val complete_lambda:   int -> int array -> t -> unit
   (** [complete_lambda nargs names tb] converts the term on top the term list
       into a lamda term with [nargs] arguments and the argument names
       [names]. *)

val check_type_variables: Support.info -> t -> unit
   (** Check that the substitutions contain no dummy types (i.e. incomplete
       types which should be updated either to FUNCTION or PREDICATE *)


val update_term: t -> unit
    (** [update_term tb] substitutes all features in the result term by the
        most specific feature *)

val result:            t -> term * TVars_sub.t
   (** The result term and the corresponding substitutions for the used type
       variables. *)
