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
        a in 0 ==> false
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
        not not some(x) x in p
    ensure
        some(x) x in p
    end


{: De Morgan's Laws
   ================ :}

all(p:G?)
    require
        all(x) x /in p
    proof
        require
            some(x) x in p
        proof
            all(x) require x in p
                   proof   x /in p
                   ensure  false end
        ensure
            false
        end
    ensure
        not some(x) x in p
    end

all(x:G, p:G?)
    require
        not some(x) x in p
    ensure
        x /in p
    end



all(p:G?)
    require
        some(x) x /in p
    proof
        require
            all(x) x in p
        proof
            all(x) require x /in p
                   proof   x in p
                   ensure  false end
        ensure
            false
        end
    ensure
        not all(x) x in p
    end


all(p:G?)
    require
        not all(x) x in p
    proof
        require
            not some(x) x /in p
        proof
            all(x) proof not not (x in p)
                   ensure x in p end
        ensure
            false
        end
    ensure
        some(x) x /in p
    end


all(p,q:G?)
    require
        p /= 0
    proof
        all(x) require p(x)
               proof   x in p + q
               ensure  p + q /= 0 end
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

all(p:G?)
    ensure
        p = 0 + p
    end


-- some theorems

all(a,b:G)
        -- symmetry of equality
    require a = b
    proof   b in {a}
    ensure  b = a end

all(a,b,c:G)
        -- transitivity of equality
    require a = b
            b = c
    proof   c in {a}
    ensure  a = c end


all(a,b,c,d,e:G)
    require
        a = b
        b = c
        c = d
        d = e
    ensure
        a = e
    end

all(x:G, p:G?)
    require
        x in p
    proof
        all(y) require y in {x}
               proof   x = y
               ensure  y in p end
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
        some(x) x in p
        p <= q
    proof
        all(x) require x in p
               proof   x in q
               ensure  some(x) x in q end
    ensure
        some(x) x in q
    end


all(ps:G??)
    proof
        all(p,q,x)
            require
                p.is_lower_bound(ps)
                x in p
                q in ps
            proof
                p <= q
            ensure
                x in q
            end
    ensure
        (*ps).is_infimum(ps)
    end

all(ps:G??)
    proof
        proof
            all(q,x)
                require
                    q in ps
                    x in q
                proof
                    q in ps and x in q
                ensure
                    x in +ps
                end
        ensure
            (+ps) in upper_bounds(ps)
        end

        all(p,x)
            require
                p.is_upper_bound(ps)
                x in +ps
            proof
                all(q)
                    require
                        q in ps and x in q
                    proof
                        q <= p
                    ensure
                        x in p
                    end
            ensure
                x in p
            end
    ensure
        (+ps).is_supremum(ps)
    end
