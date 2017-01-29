(* Copyright (C) 2017 Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)


type t = <
    readdir: string -> string array;
    is_directory: string -> bool;
    mkdir: string -> int -> unit;
    getcwd: unit -> string
        >

val set: t -> unit
val get: unit -> t

val readdir: string -> string array
val is_directory: string -> bool
val mkdir: string -> int -> unit
val getcwd: unit -> string
