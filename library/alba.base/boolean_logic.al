{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}

use boolean end


all(a:BOOLEAN)
    require
        false
    ensure
        a
    proof
        not a ==> false
    end

all(a,b:BOOLEAN)
    require
        not (a or b)
    ensure
        not a
    end


all(a,b:BOOLEAN)
    require
        not (a or b)
    ensure
        not b
    end


all(a,b:BOOLEAN)
    require
        not a
        not b
    ensure
        not (a or b)
    end

all(a,b:BOOLEAN)
    require
        not (a and b)
    ensure
        not a or not b
    proof
        not (not a or not b) ==> false
    end


all(a,b:BOOLEAN)
    require
        not a or not b
    ensure
        not (a and b)
    if not a
    orif not b
    end






all(a:BOOLEAN)
    require
        a or a
    ensure
        a
    proof
        a ==> a
    end

all(a,b:BOOLEAN)
    require
        a or b
    ensure
        b or a
    if a orif b end


all(a,b,c:BOOLEAN)
    require
        a or b or c
    ensure
        a or (b or c)
    if a or b
    proof
        a ==> a or (b or c)
    orif c
    end



all(a,b,c:BOOLEAN)
    require
        a or (b or c)
    ensure
        a or b or c
    end
