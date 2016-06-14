use
    function
    tuple
    boolean_logic
    predicate_logic
end

A: ANY
B: ANY




{: Override
   ======== :}


(+) (f:A->B,e:(A,B)): (A->B)
    -> agent (a:A): B
           require a = e.first or a in f.domain
           ensure  -> if a = e.first then e.second else f(a) end end


(+) (f,g:A->B): ghost (A->B)
    -> agent (a:A): B
           require
               a in (g.domain + f.domain)
           ensure
               -> if a in g.domain then g(a) else f(a) end
           end


all(f:A->B, a:A, b:B)
    ensure
        (f + (a,b))(a) = b
        assert
            a = (a,b).first
    end


all(f:A->B, a,x:A, b:B)
    require
        x in f.domain
        x /= a
    ensure
        (f + (a,b))(x) = f(x)
        assert
            x /= (a,b).first
    end




{: Order Structure
   =============== :}


(<=) (f,g:A->B): ghost BOOLEAN
    -> f.domain <= g.domain
       and
       consistent(f,g)

(<) (f,g:A->B): ghost BOOLEAN
    -> f <= g
       and
       some(a) a in g.domain and a /in f.domain



all(f:A->B)
        -- reflexivity of '<='
    ensure
        f <= f
    end

all(f,g:A->B)
        -- antisymmetry of '<='
    ensure
        f <= g  ==>  g <= f  ==> f = g
    end


all(f,g,h:A->B)
        -- transitivity of '<='
    require
        f <= g
        g <= h
    ensure
        f <= h
        assert
            all(x)
                require
                    x in f.domain
                ensure
                    f(x) = h(x)
                assert
                    f(x) = g(x)
                    g(x) = h(x)
                end
    end





all(f,g:A->B)
    require
        f < g
    ensure
        f /= g
        via require
            g <= f
        via some(a) a in g.domain and a /in f.domain
    end


all(f,g:A->B)
    require
        f <= g
        f /= g
    ensure
        f < g
        via require not some(x) x in g.domain and x /in f.domain
            assert
            all(x)
                require
                    x in g.domain
                ensure
                    x in f.domain
                    assert
                        not (x in g.domain and x/in f.domain)
                        x /in g.domain or x in f.domain
                end
    end



all(f,g:A->B)
    ensure
        g <= f + g
    end

all(f,g:A->B)
    require
        consistent(f,g)
    ensure
        f <= f + g
        assert
            f.domain <= (f+g).domain
            all(x)
                require
                    x in f.domain
                ensure
                    f(x) = (f + g)(x)
                    if x in g.domain
                    assert
                        g(x) = (f + g)(x)
                    orif x /in g.domain
                end
    end

all(f,g:A->B)
    require
        consistent(f,g)
    ensure
        some(h) f <= h  and g <= h
        assert
            f <= f + g and g <= f + g
    end


all(f,g,h:A->B)
    require
        f <= h
        g <= h
    ensure
        consistent(f,g)
        assert
            all(x)
                require
                    x in f.domain
                    x in g.domain
                ensure
                    f(x) = g(x)
                    assert
                        f(x) = h(x)
                        h(x) = g(x)
                end
    end



{: Domain restriction
   ================== :}


(|) (f:A->B, p:{A}): (A->B)
    -> agent (a:A):B
           require
               a in f.domain
               a in p
           ensure
               -> f(a)
           end





{: Injectivity
   ===========

   A function is injective if it is one to one. I.e. each value in the range of
   the function has a unique origin.

:}

is_injective (f:A->B): ghost BOOLEAN
    -> all(x,y) x in f.domain
                ==> y in f.domain
                ==> f(x) = f(y)
                ==> x = y


preimage(b:B, f:A->B): ghost A
    require
        f.is_injective
        b in f.range
    ensure
        Result in f.domain
        f(Result) = b
    end



all(x:A, f:A->B)
    require
        x in f.domain
    ensure
        f(x) in f.range
        assert
            x in f.domain and f(x) = f(x)
    end


inverse0 (f:A->B): ghost (B -> A)
        -- Helper function
    require
        f.is_injective
    ensure
        -> agent(b:B): A
               require
                   b in f.range
               ensure
                   -> b.preimage(f)
               end
    end


all(f:A->B)
    require
        f.is_injective
    ensure
        (f.inverse0).domain = f.range
    end





all(f:A->B)
        -- Existence of an inverse of an injective function.
    require
        f.is_injective
    ensure
        some(g) g.domain = f.range
                and
                all(x) x in f.domain ==> g(f(x)) = x
            assert
                f.inverse0.domain = f.range
                and
                all(x) x in f.domain ==> (f.inverse0)(f(x)) = x
    end



all(f:A->B, g,h:B->A)
        -- Uniqueness of the inverse of an injective function.
    require
        f.is_injective
        g.domain = f.range
        h.domain = f.range
        all(x) x in f.domain ==> g(f(x)) = x
        all(x) x in f.domain ==> h(f(x)) = x
    ensure
        g = h
        assert
            g.domain = h.domain
            all(y)
                require
                    y in f.range
                ensure
                    g(y) = h(y)
                    via some(x) x in f.domain and f(x) = y
                        assert
                            f(x) = y
                            g(f(x)) = x
                            h(f(x)) = x
                            y in {y: y in g.domain and g(y) = h(y)}
                end
    end




inverse (f:A->B): ghost (B -> A)
    require
        f.is_injective
    ensure
        Result.domain = f.range
        all(x) x in f.domain ==> Result(f(x)) = x
    end
