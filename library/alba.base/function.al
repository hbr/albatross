use
    boolean_logic
    predicate
    tuple
end

A: ANY
B: ANY

class FUNCTION[A,B]


domain (f:A->B): ghost {A}  note built_in end

undefined: (A->B)           note built_in end

is_total (f:A->B): ghost BOOLEAN
    -> f.domain.is_universal

consistent (f,g:A->B): ghost BOOLEAN
    -> all(x) x in f.domain  ==>  x in g.domain  ==> f(x) = g(x)


(=) (f,g:A->B): ghost BOOLEAN
    -> f.domain = g.domain and consistent(f,g)


all(f:A->B)
    ensure
        consistent(undefined,f)
        note axiom
    end

all(f:A->B)
    ensure
        consistent(f,f)
    end

all(f,g:A->B)
    ensure
        consistent(f,g) ==> consistent(g,f)
    end

all(f:A->B) ensure f = f end




class
    FUNCTION[A,B]
inherit
    ghost ANY
end




range (f:A->B): ghost {B}
    -> {y: some(x) x in f.domain and f(x) = y}


[] (f:A->B, p:{A}): ghost {B}
    -> {y: some(x) x in p and x in f.domain and f(x) = y}


all(x:A, f:A->B)
    require
        x in f.domain
    ensure
        f(x) in f.range
        assert
            x in f.domain and f(x) = f(x)
    end

all(f:A->B)
    ensure
        f[f.domain] <= f.range
        assert
            all(y)
            require
                y in f[f.domain]
            ensure
                y in f.range
                via some (x)
                        x in f.domain and
                        x in f.domain and
                        f(x) = y
            end
    end

all(f:A->B)
    ensure
        f.range <= f[f.domain]
        assert
            all(y)
            require
                y in f.range
            ensure
                y in f[f.domain]
                via some(x) x in f.domain and f(x) = y
                    assert
                        x in f.domain and x in f.domain and f(x) = y
            end

    end


all(p,q:{A}, f:A->B)
    require
        p <= q
    ensure
        f[p] <= f[q]
        assert
            all(y)
            require
                y in f[p]
            ensure
                y in f[q]
                via some(x) x in p and x in f.domain and f(x) = y
                    assert
                        x in q and x in f.domain and f(x) = y
            end

    end


origin (q:{B}, f:A->B): ghost {A}
    -> {x: x in f.domain and f(x) in q}


all(f:A->B)
    ensure
        f.domain <= f.range.origin(f)
    end

all(f:A->B)
    ensure
        f.range.origin(f) <= f.domain
    end
