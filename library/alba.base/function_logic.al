{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}

use
    function
    boolean_logic
    predicate_logic
end

A: ANY
B: ANY

all(f,g:A->B)
        -- reflexivity and antisymmetry of '<='
    ensure
        f <= f
        f <= g  ==>  g <= f  ==> f = g
    end

all(f,g,h:A->B)
        -- transitivity of '<='
    require
        f <= g
        g <= h
    proof
        all(x)
            require
                x in f.domain
            proof
                f(x) = g(x)
                g(x) = h(x)
            ensure
                f(x) = h(x)
            end
    ensure
        f <= h
    end


all(f:A->B, a:A, b:B)
    proof
        a = (a,b).first
    ensure
        (f + (a,b))(a) = b
    end


all(f:A->B, a,x:A, b:B)
    require
        x in f.domain
        x /= a
    proof
        x /= (a,b).first
    ensure
        (f + (a,b))(x) = f(x)
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
    proof
        g.domain <= (f+g).domain
        all(x)
            require
                x in g.domain
            proof
                x in f.domain or x /in f.domain
                require
                    x in f.domain
                proof
                    f(x) = (f + g)(x)
                ensure
                    g(x) = (f + g)(x)
                end
            ensure
                g(x) = (f + g)(x)
            end
    ensure
        g <= f + g
    end

all(f,g:A->B)
    require
        consistent(f,g)
    proof
        f <= f + g and g <= f + g
    ensure
        some(h) f <= h  and g <= h
    end


all(f,g:A->B)
    require
        some(h) f <= h  and g <= h
    proof
        all(h)
            require
                f <= h and g <= h
            proof
                all(x)
                    require
                        x in f.domain
                        x in g.domain
                    proof
                        f(x) = h(x)
                        h(x) = g(x)
                    ensure
                        f(x) = g(x)
                    end
            ensure
                consistent(f,g)
            end
    ensure
        consistent(f,g)
    end
