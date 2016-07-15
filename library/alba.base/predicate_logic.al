use
    boolean_logic
    predicate
end

G: ANY


{: Set order
   ========= :}

all(p:{G}) ensure p <= p end

all(p:{G}) ensure p = p end

all(p,q,r:{G}) require p <= q
                       q <= r
               ensure  p <= r end

all(p,q:{G})   require p <= q
                       q <= p
               ensure  p = q end





{: Proper subset
   ============= :}

(<)  (p,q:{G}): ghost BOOLEAN
    -> p <= q and some(x) x /in p and x in q

all(p,q:{G})
    require
        p < q
    ensure
        q.has_some
        via some(x) x /in p and x in q
            assert
                x in q
    end


all(p,q:{G})
    require
        p < q
    ensure
        p /= q
        via require p = q
        via some(x) x /in p and x in q
    end


all(p,q:{G})
    require
        p <= q
        p /= q
    ensure
        p < q
        via require not some(x) x /in p and x in q  -- a
        assert
            all(x)
                    -- construct contradiction by proving 'q <= p' which
                    -- contradicts 'p /= q'
                require
                    x in q
                ensure
                    x in p
                    assert
                        not (x /in p and x in q)  -- consequence of 'a' by
                                                  -- contrapositive
                        x in p or x /in q
                        ensure
                            x in p
                            if x in p orif x /in q
                        end
                end
    end


all(p,q,r:{G})
    require
        p < q
        q <= r
    ensure
        p < r
    via
        some(x) x /in p and x in q
    end


all(p,q,r:{G})
    require
        p <= q
        q < r
    ensure
        p < r
    via
        some(x) x /in q and x in r
    end


{: Singleton set
   ============= :}


singleton (a:G): {G} -> {x: x = a}

all(x:G, p:{G})
    require
        x in p
    ensure
        {x} <= p
    assert
        all(y) require y in {x}
               ensure  y in p
               assert   x = y end
    end


all(x:G)
    ensure
        {x}.has_some
        assert
            x in {x}
    end


all(p:{G}, x:G)
    require
        p < {x}
    ensure
        p.is_empty
        via require p.has_some
        via some(y) y in p
            assert
                p /= {x}
                y in {x}
                {x} <= p
    end


{: De Morgan's Laws
   ================ :}

all(p:{G})
    require
        all(x) x /in p   -- a
    ensure
        not some(x) x in p

        via require
            some(x) x in p
        via some(x) x in p
                assert   x /in p  -- from 'a'
    end





all(p:{G})
    require
        not some(x) x in p
    ensure
        all(x) x /in p
    end





all(p:{G})
    require
        some(x) x /in p
    ensure
        not all(x) x in p

        via require
            all(x) x in p
        via some(x) x /in p
                assert   x in p
    end








all(p:{G})
    require
        not all(x) x in p   -- a1
    ensure
        some(x) x /in p

        via require
            not some(x) x /in p  -- a2
        assert
            all(x)
                ensure
                    x in p  -- contradicts 'a1'

                    via require
                        not (x in p)   -- a3
                    assert
                        some(x) x /in p -- witness 'a3', contradicts 'a2'
                end
    end






{: Set algebra
   =========== :}


(+) (p,q:{G}): {G}   -> {x: p(x) or q(x)}

(*) (p,q:{G}): {G}   -> {x: p(x) and q(x)}

(-) (p,q:{G}): {G}   -> {x: x in p and x /in q}

(-) (p:{G}): {G}     -> {x: not p(x)}

disjoint(p,q:{G}): ghost BOOLEAN -> (p*q).is_empty


all(p,q,r:{G})
    require
        p + q <= r
    ensure
        p <= r
    end

all(p,q,r:{G})
    require
        p + q <= r
    ensure
        q <= r
    end

all(p,q,r:{G})
    require
        p <= r
        q <= r
    ensure
        p + q <= r
    assert
        all(x)
            require
                x in p + q
            ensure
                x in r
            if   x in p
            orif x in q
            end
    end


all(p,q:{G})
    require
        disjoint(p,q)
    ensure
        disjoint(q,p)
        assert
            p*q = q*p
            q*p in {x: x.is_empty}
    end

all(a:G, p,q:{G})
    require
        disjoint(p,q)
        a in p
    ensure
        a /in q
        via require a in q
            assert
               a in (p*q)
    end


all(p,q:{G})
    require
        not disjoint(p,q)
    ensure
        (p*q).has_some
    via
        require not (p*q).has_some
    end


all(p,q:{G})
    require
        q < p
    ensure
        (p - q).has_some
    via
        some(x) x /in q and x in p
        assert
            x in p - q
    end


{: Union and intersection of collections of sets
   ============================================= :}

(+) (pp:{{G}}): ghost {G} -> {x: some(p) pp(p) and p(x)}

(*) (pp:{{G}}): ghost {G} -> {x: all(p) pp(p) ==> p(x)}
