{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}

use predicate end

A: ANY
B: ANY

case class
    TUPLE[A,B]
create
    tuple(first:A, second:B)
end



first0 (t:(A,B)): A
    -> inspect t
       case (a,_) then a
       end

second0 (t:(A,B)): B
    -> inspect t
       case (_,b) then b
       end


first  (t:(A,B)): A     note built_in end  -- destructors still missing
second (t:(A,B)): B     note built_in end

all(a:A,b:B)
    ensure
        (a,b).first0  = a
        (a,b).second0 = b
    end

all(a:A,b:B)
    note axiom ensure
        (a,b).first  = a
        (a,b).second = b
    end
