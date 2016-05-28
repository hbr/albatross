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
    ensure
        not not a ==> a    -- double negation
    note axiom
    end

all(a:BOOLEAN)
        -- indirect proof
    require
        not a ==> false
    ensure
        a
    proof
        not not a
    end

all ensure true end


all(a,b:BOOLEAN)
        -- 'and' elimination 1
    require
        a and b
    ensure
        a
    proof
        not not a
    end

all(a,b:BOOLEAN)
        -- 'and' elimination 2
    require
        a and b
    ensure
        b
    proof
        not not b
    end


all(a,b:BOOLEAN)
        -- 'and' introduction
    ensure
        a ==> b ==> a and b
    end




all(a,b:BOOLEAN)
        -- 'or' introduction
    ensure
        a ==> a or b
    proof
        require
            a
            not a
        ensure
            b
        proof
            not not b
        end
    end


all(a,b:BOOLEAN)
        -- 'or' introduction 2
    ensure
        b ==> a or b
    end




all(a,b,c:BOOLEAN)
        -- 'or' elimination
    require
        a or b
        a ==> c
        b ==> c
    ensure
        c
    proof
        not not c
    end


all(a:BOOLEAN)
    ensure
        a or not a
    end

all(a,b:BOOLEAN)
    ensure
        a or b ==> not a ==> b
    end


all(a,b:BOOLEAN)
    ensure
        (not a ==> b) ==> a or b
    end

all(a:BOOLEAN)
    ensure
        a = a
    end
