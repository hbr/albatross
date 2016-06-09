use
    function
    boolean_logic
    predicate_logic
end

A: ANY
B: ANY

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
    proof
        all(x)
            require
                x in f.domain
            ensure
                f(x) = h(x)
            proof
                f(x) = g(x)
                g(x) = h(x)
            end
    end


all(f:A->B, a:A, b:B)
    ensure
        (f + (a,b))(a) = b
    proof
        a = (a,b).first
    end


all(f:A->B, a,x:A, b:B)
    require
        x in f.domain
        x /= a
    ensure
        (f + (a,b))(x) = f(x)
    proof
        x /= (a,b).first
    end


all(f,g:A->B)
    require
        consistent(f,g)
    ensure
        consistent(g,f)
    end

all(f,g:A->B)
    ensure
        f <= f + g
    end

all(f,g:A->B)
    require
        consistent(f,g)
    ensure
        g <= f + g
    proof
        g.domain <= (f+g).domain
        all(x)
            require
                x in g.domain
            ensure
                g(x) = (f + g)(x)
            proof
                x in f.domain or x /in f.domain
                require
                    x in f.domain
                ensure
                    g(x) = (f + g)(x)
                proof
                    f(x) = (f + g)(x)
                end
            end
    end

all(f,g:A->B)
    require
        consistent(f,g)
    ensure
        some(h) f <= h  and g <= h
    proof
        f <= f + g and g <= f + g
    end


all(f,g:A->B)
    require
        some(h) f <= h  and g <= h
    ensure
        consistent(f,g)
    proof
        all(h)
            require
                f <= h and g <= h
            ensure
                consistent(f,g)
            proof
                all(x)
                    require
                        x in f.domain
                        x in g.domain
                    ensure
                        f(x) = g(x)
                    proof
                        f(x) = h(x)
                        h(x) = g(x)
                    end
            end
    end
