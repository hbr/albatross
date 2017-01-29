(* Copyright (C) 2017 Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

type t = <
    readdir: string -> string array;
    is_directory: string -> bool
        >

module Dummy = struct end

let obj: t option ref = ref None


let set (p:t): unit =
  obj := Some p


let get (): t =
  match !obj with
    None ->
      assert false (* Illegal use, not initialized *)
  | Some p ->
      p

let readdir (path:string): string array =
  (get ())#readdir path

let is_directory (path:string): bool =
  (get ())#is_directory path
