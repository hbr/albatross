(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Term

type t

val make: term ->  Context.t -> t

val nbenv:                t -> int
val is_schematic:         t -> bool
val is_forward:           t -> bool
val is_backward:          t -> bool
val is_specialized:       t -> bool
val is_fully_specialized: t -> bool
val is_implication:       t -> bool
val is_intermediate:      t -> bool
val is_equality:          t -> bool
val equality_data:        t -> int * int * term * term
val previous_schematic:   t -> int option
val premises:             t -> int -> (term*bool) list
val count_premises:       t -> int
val short_string:         t -> string
val specialize: t -> term array -> int -> Context.t -> t

val drop: t -> Context.t -> t

val schematic_premise: t -> int * int * term
val schematic_target:  t -> int * int * term
val schematic_term:    t -> int * int * term

val term:     t -> int -> term
val term_a:   t -> int -> term
val term_b:   t -> int -> term
val target:   t -> int -> term

