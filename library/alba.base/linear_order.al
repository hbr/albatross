{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}

use
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
        a <= b ==> b <= a ==> a = b
        a <= b ==> b <= c ==> a <= c
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