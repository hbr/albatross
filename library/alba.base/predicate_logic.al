use
    boolean_logic
    predicate
end

G: ANY

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
        all(x) require p(x)
               proof   q(x)
               ensure some(x) q(x) end
    ensure
        some(x) q(x)
    end
