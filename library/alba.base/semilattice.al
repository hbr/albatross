use partial_order end

deferred class SEMILATTICE end

SL: SEMILATTICE

(=)  (a,b:SL): BOOLEAN deferred end
(*)  (a,b:SL): SL      deferred end
(<=) (a,b:SL): BOOLEAN -> a = a * b

all(a,b,c:SL)
    ensure
        a = a

        a * a = a

        a * b = b * a

        a * b * c = a * (b * c)
    deferred end


deferred class SEMILATTICE
inherit        ANY end

all(a:SL)
    ensure
        a <= a
    end

all(a,b:SL)
    require
        a <= b
        b <= a
    ensure
        a = b
    proof
        a = a * b
        a * b = b * a
        b * a = b
    end




all(a,b,c:SL)
    require
        a <= b
        b <= c
    ensure
        a <= c
    proof
        a = a * b

        ensure a * b = a * (b * c)
        proof  b * c = b
        end

        a * (b * c) = a * b * c

        ensure a * b * c = a * c
        proof  a * b = a
        end

        a = a * c
    end

deferred class SEMILATTICE
inherit        PARTIAL_ORDER end

all(a,b:SL)
    ensure
        a * b <= a
    proof
        ensure a * b = a * a * b
        proof  a * a = a end

        a * a * b = a * (a * b)

        ensure a * (a * b) = a * (b * a)
        proof  a * b = b * a
               b * a in {x: a * (a * b) = a * x}
        end

        a * (b * a) = a * b * a

        a * b = a * b * a
    end


all(a,b:SL)
    ensure
        a * b <= b
    proof
        ensure a * b  = a * (b * b)
        proof  b * b = b end

        a * (b * b) = a * b * b


        a * b = a * b * b
    end

all(a,b,c:SL)
    require
        c <= a
        c <= b
    ensure
        c <= a * b
    proof
        c = c * a

        ensure
            c * a = c * a * b
        proof  c * a = a * c
               ensure a * c = a * (c * b)
               proof  c * b = c
               end

               a * (c * b) = a * c * b

               ensure a * c * b  = c * a * b
               proof  a * c = c * a
                      c * a in {x: a * c * b = x * b}
               end
        end


        c = c * a * b
    end



all(a,b:SL)
    ensure
        (a * b).is_infimum({a,b})
    end


G:ANY


all(p:{G})
    ensure
        p * p = p
    end

all(p,q:{G})
    ensure
        p * q = q * p
    end

all(p,q,r:{G})
    ensure
        (p * q) * r = p * (q * r)
    end

immutable class
    predicate.PREDICATE[G]
inherit
    ghost SEMILATTICE
end