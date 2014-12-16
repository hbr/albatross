(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Term

type 'a t

val make: unit -> 'a t

(*val count: 'a t -> int

val has: 'a -> 'a t -> bool*)

val terms: 'a t -> ('a*int*int*term) list

val add:   term -> int -> int -> 'a -> 'a t -> unit

val unify: term -> int -> 'a t -> ('a * Term_sub.t) list

val unify_with: term -> int -> int -> 'a t -> ('a * Term_sub.t) list

val remove: 'a -> 'a t -> unit
