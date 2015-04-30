{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}

use partial_order end

deferred class SEMILATTICE end

SL: SEMILATTICE

(=)  (a,b:SL): BOOLEAN deferred end
(*)  (a,b:SL): SL      deferred end
(<=) (a,b:SL): BOOLEAN -> a = a * b

all(a,b,c:SL)
    deferred ensure
        a = a

        a * a = a
        
        a * b = b * a

        a * b * c = a * (b * c)
    end

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
    proof
        a = a * b
        a * b = b * a
        b * a = b
    ensure
        a = b
    end


all(a,b,c:SL)
    require
        a <= b
        b <= c
    proof
        a = a * b

        proof  b * c = b
        ensure a * b = a * (b * c) end

        a * (b * c) = a * b * c

        proof  a * b = a
        ensure a * b * c = a * c end

        a = a * c
    ensure
        a <= c
    end

deferred class SEMILATTICE
inherit        PARTIAL_ORDER end

all(a,b:SL)
    proof
        proof  a * a = a
        ensure a * b = a * a * b end

        a * a * b = a * (a * b)

        proof  a * b = b * a
               b * a in {x: a * (a * b) = a * x}
        ensure a * (a * b) = a * (b * a) end

        a * (b * a) = a * b * a

        a * b = a * b * a
    ensure
        a * b <= a
    end


all(a,b:SL)
    proof
        proof  b * b = b
        ensure a * b  = a * (b * b) end

        a * (b * b) = a * b * b


        a * b = a * b * b
    ensure
        a * b <= b
    end

all(a,b,c:SL)
    require
        c <= a
        c <= b
    proof
        c = c * a

        proof  c * a = a * c
               proof  c * b = c
               ensure a * c = a * (c * b) end
               a * (c * b) = a * c * b
               proof  a * c = c * a
                      c * a in {x: a * c * b = x * b}
               ensure a * c * b  = c * a * b end
        ensure c * a = c * a * b end
        

        c = c * a * b
    ensure
        c <= a * b
    end

all(a,b:SL)
    ensure
        (a * b).is_infimum({a,b})
    end


G:ANY

immutable class predicate.PREDICATE[G]
inherit         ghost SEMILATTICE end