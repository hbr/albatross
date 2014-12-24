(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Support
open Term

type parent_descriptor = Class_table.parent_descriptor

val do_inherit: int -> (int*parent_descriptor)list -> info -> Proof_context.t -> unit

val export_inherited: int -> (int*parent_descriptor)list -> Proof_context.t -> unit

val inherit_to_descendants: int -> info -> Proof_context.t -> unit
