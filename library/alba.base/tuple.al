{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}

use any end

A: ANY
B: ANY

immutable class TUPLE[A,B] end

tuple  (a:A,b:B): (A,B) note built_in end
first  (t:(A,B)): A     note built_in end
second (t:(A,B)): B     note built_in end

(=) (t,u:(A,B)): BOOLEAN -> t.first = u.first and t.second = u.second

all(a:A,b:B)
    note axiom ensure
        (a,b).first  = a
        (a,b).second = b
    end

all(t:(A,B))
    ensure
        t = t 
    end

immutable class TUPLE[A,B] inherit ANY end