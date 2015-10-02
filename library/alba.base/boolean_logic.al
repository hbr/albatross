{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}

use boolean end


all(a:BOOLEAN)
    require
        false
    proof
        not a ==> false
    ensure
        a
    end

all(a,b:BOOLEAN)
    require
        not (a or b)
    ensure
        not a
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
    proof
        not (not a or not b) ==> false
    ensure
        not a or not b
    end


all(a,b:BOOLEAN)
    require
        not a or not b
    proof
        if not a orif not b ensure not (a and b) end
    ensure
        not (a and b)
    end



all(a:BOOLEAN)
    require
        a or a
    proof
        a ==> a
    ensure
        a
    end

all(a,b:BOOLEAN)
    require
        a or b
    proof
        if a orif b ensure b or a end
    ensure
        b or a
    end

all(a,b,c:BOOLEAN)
    require
        a or b or c
    proof
        if a or b proof a ==> a or (b or c)
        orif c
        ensure a or (b or c) end
    ensure
        a or (b or c)
    end

all(a,b,c:BOOLEAN)
    require
        a or (b or c)
    ensure
        a or b or c
    end
