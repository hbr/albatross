use
    boolean_logic
    predicate
end

G: ANY

all(p:{G})
    ensure
        0 <= p
    end



all(p:{G})
    ensure
        p <= 1
    end



all(p:{G})
    ensure
        p * (-p) = 0
    end



all(p:{G})
    ensure
        p + (-p) = 1
    end



all(a:G)
    ensure
        {a} /= 0
    proof
        a in 0 ==> false
    end


all(p:{G})
    require
        some(x) x in p
    ensure
        p /= 0
    proof
        all(x)
            require
                p(x)
                p = 0
            ensure
                false
            proof
                x in 0
            end
        -- all(x) x in p ==> p /= 0 -- Redesign: No longer working!
    end


all(p:{G})
    require
        p /= 0
    ensure
        some(x) x in p
    proof
        not not some(x) x in p
    end


{: De Morgan's Laws
   ================ :}

all(p:{G})
    require
        all(x) x /in p
    ensure
        not some(x) x in p
    proof
        require
            some(x) x in p
        ensure
            false
        proof
            all(x) require x in p
                   ensure  false
                   proof   x /in p end
        end
        {: better as via 'some(x) proof'
        require
            some(x) x in p
        ensure
            false
        via some(x) require x in p
                    ensure  false
                    proof   x /in p end
        end:}
    end

all(x:G, p:{G})
    require
        not some(x) x in p
    ensure
        x /in p
    end



all(p:{G})
    require
        some(x) x /in p
    ensure
        not all(x) x in p
    proof
        require
            all(x) x in p
        ensure
            false
        proof
            all(x) require x /in p
                   ensure  false
                   proof   x in p end
        end
    end


all(p:{G})
    require
        not all(x) x in p
    ensure
        some(x) x /in p
    proof
        require
            not some(x) x /in p
        ensure
            false
        proof
            all(x) ensure x in p
                   proof not not (x in p) end
        end
    end


all(p,q:{G})
    require
        p /= 0
    ensure
        p + q /= 0
    proof
        all(x) require p(x)
               ensure  p + q /= 0
               proof   x in p + q end
    end



all(a:G, p:{G})
    require
        a.p
    ensure
        a.(p + {a})
    end

all(p,q:{G})
    require
        p <= q
    ensure
        p * q = p
    end


all(p,q:{G})
    require
        p <= q
    ensure
        q + p = q
    proof
        all(x) require (q+p)(x)
               ensure  q(x)
               if q(x) orif p(x)
               end
    end


all(p,q:{G})
    ensure
        p + q = q + p
    end

all(p,q:{G})
    ensure
        p * q = q * p
    end

all(p,q,r:{G})
    ensure
        (p * q) * r = p * (q * r)
    end

all(p,q,r:{G})
    ensure
        (p + q) + r = p + (q + r)
    end

all(p:{G})
    ensure
        p + p = p
    end

all(p:{G})
    ensure
        p * p = p
    end

all(p:{G})
    ensure
        p = 0 + p
    end


-- some theorems

all(a,b:G)
        -- symmetry of equality
    require a = b
    ensure  b = a
    proof   b in {a} end

all(a,b,c:G)
        -- transitivity of equality
    require a = b
            b = c
    ensure  a = c
    proof   c in {a} end


all(a,b,c,d,e:G)
    require
        a = b
        b = c
        c = d
        d = e
    ensure
        a = e
    end

all(x:G, p:{G})
    require
        x in p
    ensure
        {x} <= p
    proof
        all(y) require y in {x}
               ensure  y in p
               proof   x = y end
    end


all(p:{G}) ensure p <= p end

all(p:{G}) ensure p = p end

all(p,q,r:{G}) require p <= q
                      q <= r
              ensure  p <= r end

all(p,q:{G})   require p <= q
                      q <= p
              ensure  p = q end



all(p:{G}, e:BOOLEAN)
    require
        some(x) p(x)
        all(x) p(x) ==> e
    ensure
        e
    end


all(p,q:{G})
    require
        some(x) x in p
        p <= q
    ensure
        some(x) x in q
    proof
        all(x) require x in p
               ensure  some(x) x in q
               proof   x in q end
    end


all(ps:{{G}})
    ensure
        (*ps).is_infimum(ps)
    proof
        all(p,q,x)
            require
                p.is_lower_bound(ps)
                x in p
                q in ps
            ensure
                x in q
            proof
                p <= q
            end
    end

all(ps:{{G}})
    ensure
        (+ps).is_supremum(ps)
    proof
        ensure
            (+ps) in upper_bounds(ps)
        proof
            all(q,x)
                require
                    q in ps
                    x in q
                ensure
                    x in +ps
                proof
                    q in ps and x in q
                end
        end

        all(p,x)
            require
                p.is_upper_bound(ps)
                x in +ps
            ensure
                x in p
            proof
                all(q)
                    require
                        q in ps and x in q
                    ensure
                        x in p
                    proof
                        q <= p
                    end
            end
    end
