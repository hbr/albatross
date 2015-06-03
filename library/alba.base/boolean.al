{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}

immutable class BOOLEAN end


false: BOOLEAN               note built_in end

(==>) (a,b:BOOLEAN): BOOLEAN note built_in end

(not) (a:BOOLEAN): BOOLEAN   -> a ==> false

true: BOOLEAN                = false ==> false

(and) (a,b:BOOLEAN): BOOLEAN -> not (a ==> b ==> false)

(or)  (a,b:BOOLEAN): BOOLEAN -> not a ==> b

(=)   (a,b:BOOLEAN): BOOLEAN -> (a ==> b) and (b ==> a)




all(a:BOOLEAN)
    note axiom
    ensure
        not not a ==> a    -- double negation
    end

all(a:BOOLEAN)
        -- indirect proof
    require
        not a ==> false
    proof
        not not a
    ensure
        a
    end

all ensure true end

all(a,b:BOOLEAN)
        -- 'and' elimination
    require
        a and b
    proof
        not not a
        not not b
    ensure
        a
        b
    end

all(a,b:BOOLEAN)
        -- 'and' introduction
    ensure
        a ==> b ==> a and b
    end

all(a,b:BOOLEAN)
        -- 'or' introduction
    proof
        require
            a
            not a
        proof
            not not b
        ensure
            b
        end
    ensure
        a ==> a or b
        b ==> a or b
    end

all(a,b,c:BOOLEAN)
        -- 'or' elimination
    require
        a or b
        a ==> c
        b ==> c
    proof
        not not c
    ensure
        c
    end


all(a:BOOLEAN)
    ensure
        a = a
    end
