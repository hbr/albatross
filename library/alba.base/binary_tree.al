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


preorder (t:BINARY_TREE[G]): [G]
    -> inspect t
       case leaf        then []
       case tree(i,l,r) then i ^ (l.preorder + r.preorder)
       end

inorder (t:BINARY_TREE[G]): [G]
    -> inspect t
       case leaf        then []
       case tree(i,l,r) then l.inorder + i ^ r.inorder
       end

postorder (t:BINARY_TREE[G]): [G]
    -> inspect t
       case leaf        then []
       case tree(i,l,r) then l.postorder + r.postorder + [i]
       end


(-) (t:BINARY_TREE[G]): BINARY_TREE[G]
    -> inspect t
       case leaf        then leaf
       case tree(i,l,r) then tree(i, -r, -l)
       end


all(t:BINARY_TREE[G])
    proof
        inspect t ensure - - t = t end
    ensure
        - - t = t
    end


all(t:BINARY_TREE[G])
    proof
        inspect t
        case tree(i,l,r) proof
            (-tree(i,l,r)).inorder            = -r.inorder + ([i] + (-l.inorder))
            (-r.inorder) + ([i] + -l.inorder) = (-r.inorder + [i]) + -l.inorder
            (-r.inorder + [i]) + -l.inorder   = - i^r.inorder + -l.inorder
            (-i^r.inorder) + -l.inorder       = - (l.inorder + i^r.inorder)
            (- (l.inorder + i^r.inorder))     = - tree(i,l,r).inorder
        ensure -t.inorder = (-t).inorder end
    ensure
        (-t).inorder = - t.inorder
    end


all(t:BINARY_TREE[G])
    proof
        inspect t
        case tree(i,l,r) proof
            (-r.postorder) + - l.postorder = - (l.postorder + r.postorder)

            (-tree(i,l,r)).preorder             = i ^ ((-r).preorder + (-l).preorder)
            i ^ ((-r).preorder + (-l).preorder) = i ^ (-r.postorder + -l.postorder)
            i ^ (-r.postorder + -l.postorder)   = i ^ (-(l.postorder + r.postorder))
            i ^ -(l.postorder + r.postorder)    = - (l.postorder + r.postorder + [i])
            (-(l.postorder + r.postorder + [i]))= - tree(i,l,r).postorder
        ensure
            (-t).preorder = - t.postorder
        end
    ensure
        (-t).preorder = - t.postorder
    end
