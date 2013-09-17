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
            -- ex_falso: false => a           -- really necessary??
            classic:  ((a=>false)=>false) => a
        end
end



feature    -- Some theorems with implication
    all(a:BOOLEAN)
        require
            a
        ensure
            a
        end

    all(a,b,c:BOOLEAN)
        require
            a
            c => b            -- does not succeed
            a => b
        ensure
            b
        end


    all(a,b,c:BOOLEAN)
        require
            a => b
            b => c
            a
        ensure
            c
        end


    all(a,b,c:BOOLEAN)
        require
            a => b
            b => c
        ensure
            a => c
        end


    all(a,b,c:BOOLEAN)
        require
            a => b
            a => b => c
        ensure
            a => c
        end


    all(a,b,c:BOOLEAN)
        ensure
            -- a => a
            a => (a=>b) => b
            (a=>b) => (b=>c) => (a=>c)
            (a=>b) => (a=>b=>c) => (a=>c)
        end


end


feature {NONE} -- Negation
    not (a:BOOLEAN): BOOLEAN
        ensure
            Result = (a=>false)
        end

    or (a,b:BOOLEAN): BOOLEAN
        ensure
            Result = (not a => b)
        end

    and (a,b:BOOLEAN): BOOLEAN
        ensure
            Result = not (a => not b)
        end


    all(a,b:BOOLEAN)
        require
            a and b
        check
            not a => false
        ensure
            a
        end

    all(a,b,c:BOOLEAN)
        require
            a or b
            a => c
            b => c
        check
            not c => false
        ensure
            c
        end

    all(a,b,c:BOOLEAN)
            -- provable without classical logic
        ensure
            a => a
            a or not a
            a and b => not not a
            a and b => not not b
            a => b => a and b
            a or b => (a=>c) => (b=>c) => c
            -- not not not a => not a
            -- not not (a or not a)
            -- ((a or not a) => not b) => not b
        end

    all(a,b:BOOLEAN)
        require
            not not a => a
            not not b => b
        ensure
            a and b => a
            a and b => b
            a => b => a and b
            a and b => b and a
        end



end

feature   -- Negation
    not (a:BOOLEAN): BOOLEAN

    all(a:BOOLEAN)
        ensure
            refutation:    (a => false)     => not a
            contradiction: not a => a => false
            indirect:      (not a => false) => a
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
