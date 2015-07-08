{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}

use
    any
    boolean_logic
end


G: ANY

immutable class PREDICATE[G] end

(in)  (e:G, p:G?): BOOLEAN  note built_in end
(/in) (a:G, p:G?): BOOLEAN -> not p(a)

(<=) (p,q:G?): ghost BOOLEAN -> all(x) p(x) ==> q(x)


(=) (p,q:G?): ghost BOOLEAN -> p <= q and q <= p



all(p:G?) ensure p = p end


immutable class PREDICATE[G]
inherit         ghost ANY end


all(a,b:G)
        -- leibniz rule
    require  a = b
    note     axiom
    ensure   all(p:G?) p(a) ==> p(b) end


all(x:G, p,q:G?)
    require p <= q
            p(x)
    ensure  q(x) end



(+) (p,q:G?): G?   -> {x: p(x) or q(x)}

(*) (p,q:G?): G?   -> {x: p(x) and q(x)}

(-) (p,q:G?): G?   -> {x: p(x) and not q(x)}

(-) (p:G?): G?     -> {x: not p(x)}

singleton (a:G): G? -> {x: x = a}

0:G? = {x: false}
1:G? = {x: true}

(+) (pp:G??): ghost G? -> {x: some(p) p(x) and pp(p)}

(*) (pp:G??): ghost G? -> {x: all(p) pp(p) ==> p(x)}
