class BOOLEAN end


{: Built in functions
   ================== :}

false: BOOLEAN               note built_in end

(==>) (a,b:BOOLEAN): BOOLEAN note built_in end





{: Negation
   ======== :}

(not) (a:BOOLEAN): BOOLEAN   -> a ==> false




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
        assert
            not not a  -- can be derived from assumption and
                       -- proves 'a' by the double negation law
    end

all(a:BOOLEAN)
    require
        false
    ensure
        a
        via require not a
    end


{: The constant 'true'
   =================== :}

true: BOOLEAN                = false ==> false


all ensure true end



(and) (a,b:BOOLEAN): BOOLEAN -> not (a ==> b ==> false)


all(a,b:BOOLEAN)
        -- 'and' elimination 1
    require
        a and b
    ensure
        a
        via require not a
    end

all(a,b:BOOLEAN)
        -- 'and' elimination 2
    require
        a and b
    ensure
        b
        via require not b
    end


all(a,b:BOOLEAN)
        -- 'and' introduction
    ensure
        a ==> b ==> a and b
    end



(or)  (a,b:BOOLEAN): BOOLEAN -> not a ==> b


all(a,b:BOOLEAN)
        -- 'or' introduction
    require
        a
    ensure
        a or b
    assert
        require
            not a
        ensure
            b
            via require not b
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
        via require not c
        assert
            not a  -- contrapositive of 'a ==> c'
            b      -- def 'a or b'
            c
    end


all(a:BOOLEAN)
    require
        a or a
    ensure
        a
        if a orif a
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




{: Boolean equivalence
   =================== :}


(=)   (a,b:BOOLEAN): BOOLEAN -> (a ==> b) and (b ==> a)

all(a:BOOLEAN)
    ensure
        a = a
    end
