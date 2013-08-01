open Container
open Type
open Term
open Support

type feature_descriptor = {typ:typ; definition: term option}


type t = {names: feature_name key_table; features: feature_descriptor seq}

let empty () =
  {names=Key_table.empty () ; features=Seq.empty ()}

let put
    (fn: feature_name withinfo)
    (entlst: entities list withinfo)
    (rt: return_type)
    (bdy: feature_body option)
    (ft: t) =
  assert false
