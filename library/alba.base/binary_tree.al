{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}

use
    predicate_logic
    list
end

G:ANY

case class
    BINARY_TREE[G]
create
    leaf
    tree(info:G, left,right:BINARY_TREE[G])
end


preorder (t:BINARY_TREE[G]): LIST[G]
    -> inspect t
       case leaf        then nil
       case tree(i,l,r) then i ^ (l.preorder + r.preorder)
       end

inorder (t:BINARY_TREE[G]): LIST[G]
    -> inspect t
       case leaf        then nil
       case tree(i,l,r) then l.inorder + i ^ r.inorder
       end

postorder (t:BINARY_TREE[G]): LIST[G]
    -> inspect t
       case leaf        then nil
       case tree(i,l,r) then l.postorder + r.postorder + [i]
       end


(-) (t:BINARY_TREE[G]): BINARY_TREE[G]
    -> inspect t
       case leaf        then leaf
       case tree(i,l,r) then tree(i, -r, -l)
       end
