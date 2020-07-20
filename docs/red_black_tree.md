**Insertion and Deletion in Red Black Trees**

The algorithm described here is implemented
[here](../ocaml/fmlib/basic/red_black.ml)


Basics
======

Definition
----------

A red black tree is either an empty tree or a node with a color, a left son, an
info element and a right son.

Each node has a color and the empty tree is considered black with a black height
of zero.

A definition is a functional language like ocaml looks like
```ocaml
    type info = ... (* type of the information element, must be sortable *)

    type color = Red | Black

    type t = Empty | Node of color * t * info * t
```

Insertion and deletion is always done at the bottom. We insert a node by
replacing an empty tree by a singleton red node. We delete a node by replacing a
singleton node (i.e. a node with two empty sons) by an empty node.


Invariant
---------

1. A red node has only black chilren (an empty tree counts as black).

2. Every path from the root to an empty node contains the same number of black
   nodes.

3. The inorder sequence is sorted i.e. a red black tree is a binary search tree.


Because the empty tree is considered black, a singleton red node does not
violate the invariant. It has two empty black sons.


Examples:

```
    one red node:

            Rx

    black node with one or two children:

            By                  By                  By
        Rx                  Rx      Rz          Bx      Bz
```


If `h` is the black height of a red black tree, then the maximal height of the
tree is `2 * h + 1`. E.g. a singleton red node has black height `0` but height
`1`.


Insertion and deletion might create a violation of the invariant. Inserting a
singleton red node below a red node might create a red violation because there
are two red nodes in a row. Deleting a black node might create a black
violation, because its sibling has a black height of one and the empty node has
a black height of zero.



Insertion
=========

Basics
------

A red black tree is sorted. If we want to insert an info element into a tree, we
search for it following the order relation of the info element. There are two
possiblilities.

1. We find a node with the info element we want to insert. There is nothing to
   be done.

2. Our search ends at an empty tree. This is the place to insert a new singleton
   red tree.

Let's look at the path from the insertion point to the root node.
```
    Rnew    |   B R B B R ....

    Rnew    |   R B R B B ...
```

In the first case we are ready, because no violation is created.

The second case is problematic, because we want to insert a red node below a red
parent. We know that the grandparent must be black. We could swap the colors of
the parent and the grandparent, creating a new red violation. This can bubble up
until we reach two black nodes in a row.

However the solution is not that simple, because *stealing* the blackness of a
parent might create two new other kind of violations. 1. The black parent might
have a red child. 2. The black height of a path of the other branch to which the parent belongs reduces by one.



Algorithm
---------

We can get a solution by satisfying the following insertion invariant: Inserting
an element into a valid red black tree results in one of the states:

1. A nonempty tree where the root color has been changed from black to red and
   the new tree has the original black height.

2. A nonempty tree where the root color has not been changed and the new tree
   has the original black height.

3. Insertion into a red rooted tree ends with `a x b y c` where `a`, `b` and `c`
   are black rooted valid red black trees where the insertion has been successul
   in one of them and `x` and `y` are two info elements separating them. The
   black height of `a`, `b` and `c` is the black height of the original tree.
   Therefore we cannot form a valid red black tree of the original height
   without creating a red violation. The parent is black.


Note that all subtrees must be valid red black trees.

We have to prove that we can maintain the insertion invariant.

Initially we are in state 1. We insert the new element into an empty tree by
creating a singleton red tree. Because the empty tree is considered black
rooted, the root color has been changed from black to red. The new tree has the
same black height as the initial tree (namely zero) and the new tree is a valid
red black tree.

Now we have to consider inserting into a tree `Node(color, left, info, right)`.
We only analyze the situation of inserting into the left son. Inserting into the
right son is symmetrical. We assume that insertion into the left subtree ended
in state 1, 2 or 3. We have to prove that insertion at the current level ends
either in state 1, 2 or 3 as well.

1. Insertion into `left` created a new tree `Node(Red, a, x, b)` and `a` and `b`
   have the black height of the original tree `left`.

   - color = Black: We create `node(Black, Node(Red,a,x,b), info, right)` and
     end in state 2.

   - color = Red: We cannot create a new valid red black tree. Therefore we end
     in state 3 with `a x b info right`. The next parent must be black, because
     the current node is red.

2. Insertion into `left` created a new tree `leftNew` whose color has not been
   changed. We remain in state 2 by returning `Node(color, leftNew, info,
   right)`

3. Insertion into `left` ended up with `a x b y c`. The black height of `a`, `b`
   and `c` is the same as the black height of `left`. Because we are in state 3,
   the color of the current node must be black. We end in state 1 and return
   `Node (Red, Node (Black, a, x, b), y, Node (Black, c, info, right))`.


During insertion we have the following state diagramm.
```
                        --
                       /  \
                      |    |
                      v    |
       1   ------->   2 --/
       ^   \
       |    \
       |     ----->   3
       |              |
       \--------------/
```

If the insertion ends in state 1 or 2 at the root, then there is nothing to do.
State 1 and 2 represent valid red black trees.

Ending in state 3 with `a x b y c` at the root we are allowed to introduce a new
black level and generate either `Node (Black, a, x, Node (Red, b, y, c))` or
`Node (Black, Node (Red, a, x, b), y, c)`.




Comparison to Chris Okasaki's Insertion Algorithm
-------------------------------------------------

In 1993 Chris Okasaki published an article named *Red-Black Trees in a
Functional Setting* as a functional pearl in the journal of functional
programming. The article described an insertion algorithm for red black trees in
Haskell.

His algorithm is considered as the simplest possible insertion algorithm
for red black trees in functional programming. I claim that the here presented
insertion algorithm is even a little bit simpler than Chris Okasaki's and
understandable without painting tree diagramms.

Furthermore it is more
efficient, because

- It does in the rebalancing case only one case split and it does not need deep
  pattern match.

- It introduces the state 2 where nothing more has to be done until the root is
  reached.









Deletion
========

