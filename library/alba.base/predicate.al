{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}

use
    any
end


G: ANY

immutable class PREDICATE[G] end

(in) (e:G, p:G?): BOOLEAN  note built_in end

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


all(p:G?)
    ensure
        0 <= p
        p <= 1
        p * (-p) = 0
        p + (-p) = 1
    end


all(a:G)
    proof
        require {a} = 0
        proof   all(x:G) {x}(x)
                {a}(a)
        ensure  false end
    ensure
        {a} /= 0
    end

all(p:G?)
    require
        some(x) x in p
    proof
        all(x) x in p ==> p /= 0    
    ensure
        p /= 0
    end

all(p:G?)
    require
        p /= 0
    proof
        not (some(x) x in p) ==> false
    ensure
        some(x) x in p
    end


all(p,q:G?)
    require
         p /= 0
    proof
         some(x) x in p
         all(x)
             require
                 p(x)
             proof
                 x in p + q
                 some(x) x in {x: x in p + q}
             ensure
                 p + q /= 0
             end
    ensure
         p + q /= 0
    end



all(a:G, p:G?)
    require
        a.p
    ensure
        a.(p + {a})
    end

all(p,q:G?)
    require
        p <= q
    proof
        all(x) require (q+p)(x)
               proof   q(x) or p(x)
                       q(x) ==> q(x)
                       p(x) ==> q(x)
               ensure  q(x) end
    ensure
        p * q = p
        q + p = q
    end


all(p,q:G?)
    ensure
        p + q = q + p
    end

all(p,q:G?)
    ensure
        p * q = q * p
    end

all(p,q,r:G?)
    ensure
        (p * q) * r = p * (q * r)
    end

all(p,q,r:G?)
    ensure
        (p + q) + r = p + (q + r)
    end

all(p:G?)
    ensure
        p + p = p
    end

all(p:G?)
    ensure
        p * p = p
    end




(+) (pp:G??): ghost G? -> {x: some(p) p(x) and pp(p)}

(*) (pp:G??): ghost G? -> {x: all(p) pp(p) ==> p(x)}


-- some theorems

all(a,b:G)
        -- symmetry of equality
    require a = b
    proof   {x:x=a}(b)
    ensure  b = a end

all(a,b,c:G)
        -- transitivity of equality
    require a = b
            b = c
    proof   {x: a=x}(c)
    ensure  a = c end


all(x:G, p:G?)
    require
        p(x)
    proof
        all(y) require {x}(y)
               proof   x = y
               ensure  p(y) end
    ensure
        {x} <= p
    end


all(p:G?) ensure p <= p; p = p end

all(p,q,r:G?) require p <= q
                      q <= r
              ensure  p <= r end

all(p,q:G?)   require p <= q
                      q <= p
              ensure  p = q end



all(p:G?, e:BOOLEAN)
    require
        some(x) p(x)
        all(x) p(x) ==> e
    ensure
        e
    end


all(p,q:G?)
    require
        some(x) p(x)
        p <= q
    proof
        {: all(x) p(x) ==> some(x) q(x) :}
        all(x) require p(x)
               proof   q(x)
               ensure some(x) q(x) end
    ensure
        some(x) q(x)
    end
