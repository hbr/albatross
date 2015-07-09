{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}

use
    predicate_logic
    tuple
end

A: ANY
B: ANY

immutable class FUNCTION[A,B] end


domain (f:A->B): ghost A?   note built_in end

(<=) (f,g:A->B): ghost BOOLEAN
    ensure
        Result = (f.domain <= g.domain
                  and
                  all(x) x in f.domain ==> f(x) = g(x))
    end

(=) (f,g:A->B): ghost BOOLEAN
    -> f <= g and g <= f



range (f:A->B): ghost B?
    ensure
        Result = {b: some(a) a in f.domain and f(a) = b}
    end

image (f:A->B, p:A?): ghost B?
    ensure
        Result = {y: some(x) x in (f.domain*p) and f(x) = y}
    end

preimage (f:A->B, q:B?): ghost A?
    ensure
        Result = {x: x in f.domain and f(x) in q}
    end

is_total (f:A->B): ghost BOOLEAN
    -> all(a) a in f.domain

is_injective (f:A->B): ghost BOOLEAN
    ensure
        Result = all(x,y) x in f.domain
                      ==> y in f.domain
                      ==> f(x) = f(y)
                      ==> x = y
    end

is_finite (p:A?): ghost BOOLEAN
    -> all(f:A->A) f.is_injective
               ==> f.domain = p
               ==> f.range <= p
               ==> f.range = p

is_choice (f:A?->A, p:A?): ghost BOOLEAN
    ensure
        Result = ({q: q <= p} <= f.domain and all(q) q <= p ==> f(q) in q)
    end

is_iterable (f:A->A): ghost BOOLEAN
    ensure
        Result = all(a) a in f.domain ==> f(a) in f.domain
    end

is_fixpoint (a:A, f:A->A): ghost BOOLEAN
    ensure
        Result = (a in f.domain and f(a) = a)
    end

is_idempotent (f:A->A): ghost BOOLEAN
    ensure
        Result = (f.is_iterable and all(a) a in f.domain ==> f(a).is_fixpoint(f))
    end


preimage(f:A->B, b:B): ghost A
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
    proof
        x in f.domain and f(x) = f(x)
    ensure
        f(x) in f.range
    end


inverse0 (f:A->B): ghost (B -> A)
    require
        f.is_injective
    ensure
        Result = agent (b:B):A
                     require
                         b in f.range
                     ensure
                         Result = f.preimage(b)
                     end
    end


all(f:A->B, b:B)
    require
        f.is_injective
    ensure
        (f.inverse0).domain = f.range
    end


can_join (f,g:A->B): ghost BOOLEAN
    -> some(h) f <= h and g <= h


all(f:A->A)
    require
        f.is_iterable
    proof
        all(a)
            require
                a in f.range
            proof
                all(x) x in f.domain and f(x) = a ==> a in f.domain
            ensure
                a in f.domain
            end
    ensure
        f.range <= f.domain
    end

{:
(|) (f:A->B, p:A?): ghost (A->B)
    ensure
        Result.domain = f.domain * p
        Result <= f
    end
:}


all(f:A->B) ensure f = f end

immutable class FUNCTION[A,B]
inherit         ghost ANY end



all(f:A->B)
    require
        f.is_injective
    proof
        f.inverse0.domain = f.range and all(x) x in f.domain ==> (f.inverse0)(f(x)) = x
    ensure
        some(g) g.domain = f.range and all(x) x in f.domain ==> g(f(x)) = x
    end

all(f:A->B, g,h:B->A)
    require
        f.is_injective
        g.domain = f.range
        h.domain = f.range
        all(x) x in f.domain ==> g(f(x)) = x
        all(x) x in f.domain ==> h(f(x)) = x
    proof
        g.domain = h.domain
        all(y)
            require
                y in f.range
            proof
                some(x) x in f.domain and f(x) = y
                all(x)
                    require
                        x in f.domain and f(x) = y
                    proof
                        f(x) = y
                        g(f(x)) = x
                        h(f(x)) = x
                        y in {y: y in g.domain and g(y) = h(y)}
                    ensure
                        g(y) = h(y)
                    end
            ensure
                g(y) = h(y)
            end
    ensure
        g = h
    end

inverse (f:A->B): ghost (B -> A)
    require
        f.is_injective
    ensure
        Result.domain = f.range
        all(x) x in f.domain ==> Result(f(x)) = x
    end



all(a:A)
    ensure
        all(x)(x -> a)(x) = a
        all(x)(x -> a)(x) = a
    end

all(a:A)
    ensure
        (x -> x)(a) = a
        all(x)(x -> a)(x) = a      -- in this form it is untypeable
                                   -- !!it is. The type checker choses the most
                                   -- general type (G:ANY)

        all(x)((x:A) -> a)(x) = a  -- in this form the type checker cannot
                                   -- reconstruct the types
    end


all(f,g,h:A->B)
    require
        f.domain = g.domain
        f <= h
        g <= h
    proof
        all(a)
            require
                a in f.domain
            proof
                f(a) = h(a)
                h(a) = g(a)
            ensure
                f(a) = g(a)
            end
    ensure
        f = g
    end

all(f,g:A->B)
    require
        f.domain = g.domain
        f.can_join(g)
    proof
        all(h) require
                   f <= h and g <= h
               proof
                   all(x) require
                              (f.domain)(x)
                          proof
                              f(x) = h(x)
                              h(x) = g(x)
                          ensure
                              f(x) = g(x)
                          end
               ensure
                   f = g
               end
    ensure
        f = g
    end



{:
all(f:A->B, p:A?)
    proof
        all(y:B)
            require
                y in f.image(p)
            proof
                some(x) (f.domain*p)(x) and f(x) = y

                all(x)
                    require
                        (f.domain*p)(x) and f(x) = y
                    proof
                        (f.domain*p)(x)
                        (f.domain)(x)
                        (f.domain*f.domain)(x)
                        f(x) = y
                        {x: (f.domain*f.domain)(x) and f(x) = y}(x)
                    ensure
                        some(x) {x:(f.domain*f.domain)(x) and f(x) = y}(x)
                           -- cannot prove
                    end
                some(x) (f.domain*f.domain)(x) and f(x) = y
            ensure
                y in f.range
            end
    ensure
        f.image(p) <= f.range
    end
:}