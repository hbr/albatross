immutable class
    BOOLEAN
end


feature   -- Basic functions
    => (a,b:BOOLEAN): BOOLEAN
        note built_in end

    false: BOOLEAN
        note built_in end

end

feature {NONE}   -- Axioms
    all(a:BOOLEAN)
        note built_in ensure
            classic:  ((a=>false)=>false) => a
            ex_falso: false => a
        end
end


feature {NONE} -- Negation
    not (a:BOOLEAN): BOOLEAN
        ensure
            Result = (a=>false)
        end
end

feature   -- Negation
    not (a:BOOLEAN): BOOLEAN


    all(a:BOOLEAN)
        ensure
            refutation:    (a => false)     => not a
            indirect:      (not a => false) => a
            contradiction: a => not a => false
        end
end



feature {NONE}  -- conjunction
    and (a,b:BOOLEAN): BOOLEAN
        ensure
            Result = not (a => not b)
        end
end


feature -- conjunction
    and (a,b:BOOLEAN): BOOLEAN

    all(a,b:BOOLEAN)
        ensure
            a and b => a
            a and b => b
            a => b => a and b
        end
end



=  (a,b:BOOLEAN): BOOLEAN
    note built_in end

all(a,b,e:BOOLEAN)
    note built_in ensure
        equal_reflexive:  a=a
        equal_rewrite:    a=b => e => e[a:=b]
        antisymmetric:    (a=>b) => (b=>a) => (a=b)
        classic:          ((a=>false)=>false) => a
        deduction:        require a ensure b end => (a=>b)
    end

not (a:BOOLEAN): BOOLEAN
    ensure
        Result = (a=>false)
    end

and (a,b:BOOLEAN): BOOLEAN
    ensure
        Result = not (a => not b)
    end

or (a,b:BOOLEAN): BOOLEAN
    ensure
        Result = (not a => b)
    end

true: BOOLEAN
    ensure
        Result = (false=>false)
    end
