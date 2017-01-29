(* Copyright (C) 2017 Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)


module type Application_data =
  sig
    type node
    type graph
    val compare: node -> node -> int
    val dependencies: node -> graph -> node list
  end



module type S =
    sig
      type node
      type graph
      val sort: node list -> graph -> (node list, node list) result
    end


module Make(AD: Application_data)
    : S with type node = AD.node and type graph = AD.graph
