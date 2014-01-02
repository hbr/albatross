open Support

type typ =
    Simple of int
  | Generic of int * typ array
  | TLam of typ array * typ


let type_map (f:int->int->int) (t:typ) =
  let rec map nb t =
    match t with
      Simple j -> Simple (f j nb)
    | Generic (j,tarr) ->
        Generic (f j nb, Array.map (fun t -> map nb t) tarr)
    | TLam (tarr,t) ->
        TLam(tarr, map (nb+Array.length tarr) t)
  in
  map 0 t

let type_up (i:int) (t:typ) =
  (* Shift all classes up by 'i' in type 't' *)
  type_map
    (fun j nb ->
      if j<nb then j
      else j+i)
    t
