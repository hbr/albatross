{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}

use
    boolean_logic
    predicate_logic
    tuple
end

A: ANY
B: ANY

immutable class FUNCTION[A,B] end


domain (f:A->B): ghost A?   note built_in end

0: (A->B)                   note built_in end

(<=) (f,g:A->B): ghost BOOLEAN
    -> f.domain <= g.domain
       and
       all(x) x in f.domain ==> f(x) = g(x)

(=) (f,g:A->B): ghost BOOLEAN
    -> f <= g and g <= f

all(f:A->B)
    require
        f = 0
    ensure
        f.domain = 0
    note axiom
    end


all(f:A->B) ensure f = f end

immutable class FUNCTION[A,B]
inherit         ghost ANY end


range (f:A->B): ghost B?
    -> {b: some(a) a in f.domain and f(a) = b}

image (p:A?, f:A->B): ghost B?
    -> {y: some(x) x in (f.domain*p) and f(x) = y}

preimage (q:B?, f:A->B): ghost A?
    -> {x: x in f.domain and f(x) in q}


(|) (f:A->B, p:A?): (A->B)
    -> agent (a:A):B
           require
               a in f.domain
               a in p
           ensure
               -> f(a)
           end

(+) (f:A->B, e:(A,B)): (A->B)
    -> agent (a:A): B
           require
               a = e.first or a in f.domain
           ensure
               -> if a = e.first then
                      e.second
                  else
                      f(a)
                  end
           end


(+) (f,g:A->B): ghost (A->B)
    -> agent (a:A): B
           require
               a in (f.domain + g.domain)
           ensure
               -> if a in f.domain then
                     f(a)
                  else
                     g(a)
                  end
           end

is_total (f:A->B): ghost BOOLEAN
    -> all(a) a in f.domain

is_injective (f:A->B): ghost BOOLEAN
    -> all(x,y) x in f.domain
                ==> y in f.domain
                ==> f(x) = f(y)
                ==> x = y


is_finite (p:A?): ghost BOOLEAN
    -> all(f:A->A) f.is_injective
               ==> f.domain = p
               ==> f.range <= p
               ==> f.range = p

is_choice (f:A?->A, p:A?): ghost BOOLEAN
    -> all(q) q /= 0 and q <= p ==> q in f.domain and f(q) in q

is_iterable (f:A->A): ghost BOOLEAN
    -> all(a) a in f.domain ==> f(a) in f.domain

is_fixpoint (a:A, f:A->A): ghost BOOLEAN
    -> a in f.domain and f(a) = a


is_idempotent (f:A->A): ghost BOOLEAN
    -> f.is_iterable and all(a) a in f.domain ==> f(a).is_fixpoint(f)


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
    proof
        x in f.domain and f(x) = f(x)
    end


inverse0 (f:A->B): ghost (B -> A)
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


consistent (f,g:A->B): ghost BOOLEAN
    -> all(x) x in f.domain ==> x in g.domain ==> f(x) = g(x)


all(f:A->A)
    require
        f.is_iterable
    ensure
        f.range <= f.domain
    proof
        all(a)
            require
                a in f.range
            ensure
                a in f.domain
            proof
                all(x) x in f.domain and f(x) = a ==> a in f.domain
            end
    end

{:
(|) (f:A->B, p:A?): ghost (A->B)
    ensure
        Result.domain = f.domain * p
        Result <= f
    end
:}


all(f:A->B)
    require
        f.is_injective
    ensure
        some(g) g.domain = f.range
                and
                all(x) x in f.domain ==> g(f(x)) = x
    proof
        f.inverse0.domain = f.range
        and
        all(x) x in f.domain ==> (f.inverse0)(f(x)) = x
    end

all(f:A->B, g,h:B->A)
    require
        f.is_injective
        g.domain = f.range
        h.domain = f.range
        all(x) x in f.domain ==> g(f(x)) = x
        all(x) x in f.domain ==> h(f(x)) = x
    ensure
        g = h
    proof
        g.domain = h.domain
        all(y)
            require
                y in f.range
            ensure
                g(y) = h(y)
            proof
                some(x) x in f.domain and f(x) = y
                all(x)
                    require
                        x in f.domain and f(x) = y
                    ensure
                        g(y) = h(y)
                    proof
                        f(x) = y
                        g(f(x)) = x
                        h(f(x)) = x
                        y in {y: y in g.domain and g(y) = h(y)}
                    end
            end
    end

inverse (f:A->B): ghost (B -> A)
    require
        f.is_injective
    ensure
        Result.domain = f.range
        all(x) x in f.domain ==> Result(f(x)) = x
    end


{:
all(a:A)
    ensure
        all(x)(x -> a)(x) = a   -- 'x' not typeable !!!
        all(x)(x -> a)(x) = a
    end
:}
{:
all(a:A)
    ensure
        (x -> x)(a) = a
        all(x)(x -> a)(x) = a      -- in this form it is untypeable
                                   -- !!it is. The type checker choses the most
                                   -- general type (G:ANY)

        all(x)((x:A) -> a)(x) = a  -- in this form the type checker cannot
                                   -- reconstruct the types
    end
:}

all(f,g,h:A->B)
    require
        f.domain = g.domain
        f <= h
        g <= h
    ensure
        f = g
    proof
        all(a)
            require
                a in f.domain
            ensure
                f(a) = g(a)
            proof
                f(a) = h(a)
                h(a) = g(a)
            end
    end
{:
all(f,g:A->B)
    require
        f.domain = g.domain
        f.consistent(g)
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
:}


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