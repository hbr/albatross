{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}

use
    boolean_logic
    partial_order
end


deferred class LINEAR_ORDER end

LO: LINEAR_ORDER

(=)  (a,b:LO): BOOLEAN    deferred end
(<=) (a,b:LO): BOOLEAN    deferred end

all(a,b,c:LO)
    deferred
    ensure
        a = a
        a <= b or b <= a
        a <= b  ==>  b <= a  ==>  a = b
        a <= b  ==>  b <= c  ==>  a <= c
    end

all(a:LO)
    proof
        a <= a or a <= a
    ensure
        a <= a
    end

deferred class LINEAR_ORDER
inherit        PARTIAL_ORDER end


all(a,b:LO)
    require
        not (a <= b)
    proof
        a <= b  or  b <= a
        require  b = a
        proof    a in {x: x <= b}
        ensure   false end
    ensure
        b < a
    end

all(a,b:LO)
    require
        not (a < b)
    proof
        require  not (b <= a)
        proof    a < b
        ensure   false end
    ensure
        b <= a
    end

all(a,b:LO)
    require
        a /= b
    proof
        require
            not (a < b)
        ensure
            b < a
        end
    ensure
        a < b  or  b < a
    end



{: Maximum and Minimum
   =================== :}

min (a,b:LO): LO  -> if a <= b then a else b end
max (a,b:LO): LO  -> if a <= b then b else a end


all(a,b:LO)
    proof
        proof  a <= b  or  not (a <= b)
               a <= b  ==> min(a,b) in {a,b}
        ensure min(a,b) in {a,b} end

        all(x) require x in {a,b}
               proof   a <= b  or  not (a <= b)
                       a <= b        ==> min(a,b) <= x
                       not (a <= b)  ==> min(a,b) <= x
               ensure  min(a,b) <= x end
    ensure
        min(a,b).is_least({a,b})
    end


all(a,b:LO)
    proof
        proof  a <= b  or  not (a <= b)
               a <= b  ==> max(a,b) in {a,b}
        ensure max(a,b) in {a,b} end

        all(x)
            require
                x in {a,b}
            proof
                x = a  or x = b
                a <= b or not (a <= b)
                require
                    x = a
                proof
                    a <= b       ==> x <= max(a,b)
                    not (a <= b) ==> x <= max(a,b)
                ensure
                    x <= max(a,b)
                end

                require
                    x = b
                proof
                    a <= b  ==>  x <= max(a,b)
                    not (a <= b) ==> x <= max(a,b)
                ensure
                    x <= max(a,b)
                end
            ensure
                x <= max(a,b)
            end
    ensure
        max(a,b).is_greatest({a,b})
    end
