open Fmlib
open Common

type names = int list String_map.t


type t = {
    gamma: Gamma.t;
    map: names
  }



let count (c:t): int =
  Gamma.count c.gamma


let gamma (c:t): Gamma.t =
  c.gamma


let add_name_to_names
      (name:string)
      (i:int)
      (global:bool)
      (map:names)
    : names
  =
  if name = "" || name = "_" then
    map

  else
    String_map.add
      name
      (match
         String_map.maybe_find name map
       with
       | None ->
          [i]

       | Some lst ->
          if global then
            i :: lst
          else
            [i])
      map


let standard (): t =
  let gamma = Gamma.standard () in
  {gamma;
   map =
     Interval.fold
       String_map.empty
       (fun i m ->
         add_name_to_names
           Gamma.(string_of_name (name_of_level i gamma))
           i
           true
           m)
       0 (Gamma.count gamma)
  }


let compute (t:Term.t) (c:t): Term.t =
  Gamma.compute t c.gamma


let find_name (name:string) (c:t): int list =
  match String_map.maybe_find name c.map with
  | None ->
     []

  | Some lst ->
     lst


module Pretty (P:Pretty_printer.SIG) =
  struct
    module P0 = Gamma.Pretty (P)
    let print (t:Term.t) (c:t): P.t =
      P0.print t c.gamma
  end
