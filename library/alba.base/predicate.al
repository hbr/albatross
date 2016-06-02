{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}

use
    any
    boolean_logic
end


G: ANY

immutable class PREDICATE[G] end

(in)  (e:G, p:{G}): BOOLEAN  note built_in end
(/in) (a:G, p:{G}): BOOLEAN -> not p(a)

(<=) (p,q:{G}): ghost BOOLEAN -> all(x) p(x) ==> q(x)


(=) (p,q:{G}): ghost BOOLEAN -> p <= q and q <= p



all(p:{G}) ensure p = p end


immutable class PREDICATE[G]
inherit         ghost ANY end


all(a,b:G)
        -- leibniz rule
    require  a = b
    ensure   all(p:{G}) p(a) ==> p(b)
    note     axiom end


all(x:G, p,q:{G})
    require p <= q
            p(x)
    ensure  q(x) end


is_empty (p:{G}): ghost BOOLEAN
        -- Is the set 'p' empty?
    -> all(x) x /in p

is_universal (p:{G}): ghost BOOLEAN
        -- Is the set 'p' the universal set?
    -> all(x) x in p

has_some (p:{G}): ghost BOOLEAN
    -> some(x) x in p

(+) (p,q:{G}): {G}   -> {x: p(x) or q(x)}

(*) (p,q:{G}): {G}   -> {x: p(x) and q(x)}

(-) (p,q:{G}): {G}   -> {x: p(x) and not q(x)}

(-) (p:{G}): {G}     -> {x: not p(x)}

singleton (a:G): {G} -> {x: x = a}

0:{G} = {x: false}
1:{G} = {x: true}

empty:{G}     = {x: false}
universal:{G} = {x: true}

(+) (pp:{{G}}): ghost {G} -> {x: some(p) pp(p) and p(x)}

(*) (pp:{{G}}): ghost {G} -> {x: all(p) pp(p) ==> p(x)}

is_lower_bound (p:{G}, ps:{{G}}): ghost BOOLEAN
    -> all(q) ps(q) ==> p <= q

is_upper_bound (p:{G}, ps:{{G}}): ghost BOOLEAN
    -> all(q) ps(q) ==> q <= p

lower_bounds(ps:{{G}}): ghost {{G}}
    -> {p: p.is_lower_bound(ps)}

upper_bounds(ps:{{G}}): ghost {{G}}
    -> {p: p.is_upper_bound(ps)}

is_least (p:{G}, ps:{{G}}): ghost BOOLEAN
    -> ps(p) and p.is_lower_bound(ps)

is_greatest (p:{G}, ps:{{G}}): ghost BOOLEAN
    -> ps(p) and p.is_upper_bound(ps)

is_infimum (p:{G}, ps:{{G}}): ghost BOOLEAN
    -> p.is_greatest(lower_bounds(ps))

is_supremum (p:{G}, ps:{{G}}): ghost BOOLEAN
    -> p.is_least(upper_bounds(ps))
