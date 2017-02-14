(* Copyright (C) 2017 Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Support


module Src :
sig
  type t
  val name: t -> string
  val directory: t -> string
  val path: t -> string
  val is_new: t -> bool
  val is_modified: t -> bool
  val is_affected: t -> bool
  val dependencies: t -> module_name withinfo list
  val full_dependencies: t -> int list
  val parse: t -> declaration list
  val info_abort: info -> string -> t -> 'a
  val write_json: t -> unit
end


module M :
sig
  type t
  val compare: t -> t -> int
  val primary_source: t -> Src.t
  val name: t -> module_name
  val base_name: t -> int
  val package_name: t -> library_name
  val string_of_name: t -> string
  val is_external: t -> bool
  val is_affected: t -> bool
  val has_interface: t -> bool
  val has_implementation: t -> bool
  val interface: t -> Src.t
  val implementation: t -> Src.t
  val has_id: t -> bool
  val id: t -> int
  val get: string -> string -> module_name -> t
end


module MSet:
sig
  type node = M.t
  type t
  type graph = t
  val verbosity: t -> int
  val map: graph -> M.t Module_map.t
  val string_of_node: node -> string
  val module_of_id: int -> t -> M.t
  val compare: node -> node -> int
  val dependencies: node -> graph -> node list
  val fold: ('a -> M.t -> 'a) -> 'a -> t -> 'a
  val iter: (M.t->unit) -> t -> unit
end


val make_set: Command_line.t -> MSet.graph
