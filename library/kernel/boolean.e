immutable class
    BOOLEAN
end


feature   -- Basic functions and axioms
    => (a,b:BOOLEAN): BOOLEAN
        note built_in end

    false: BOOLEAN
        note built_in end

    all(a:BOOLEAN)
        note built_in ensure
            ((a=>false)=>false) => a
        end
end


feature {NONE}    -- Function definitions
    true: BOOLEAN
        ensure
            Result = (false => false)
        end

    not (a:BOOLEAN): BOOLEAN
        ensure
            Result = (a => false)
        end

    and (a,b:BOOLEAN): BOOLEAN
        ensure
            Result = not (a => not b)
        end

    or (a,b:BOOLEAN): BOOLEAN
        ensure
            Result = (not a => b)
        end

    = (a,b:BOOLEAN): BOOLEAN
        ensure
            Result = ((a => b) and (b => a))
        end

    all(a:BOOLEAN)
        ensure
            double_negation: not not a => a
        end
end

    lemma: all(a,b:BOOLEAN)
        require
            a or b
        check
            (a or b) => not b => not not a
        ensure
            b or a
        end

    all(a:BOOLEAN)
       ensure
           -- e00: a or (false => a)
           e01: a or (a => false)
           -- e0: a or false = a
           -- e1: a => true
           -- e2: a and (true => a)   -- loops in combination with 'e0' and 'e01'
           -- e3: a and (a => true)   -- loops in combination with 'e0' and 'e01'
           -- e4: a and true = a   -- loops in combination with 'e0' and 'e01'
       end



feature         -- Constants / Negation

    true: BOOLEAN

    false: BOOLEAN

    not (a:BOOLEAN): BOOLEAN

    all(a:BOOLEAN)
        ensure
            indirect:      (not a => false) => a
            refutation:    (a     => false) => not a
            contradiction: not a => a => false
        end

    all ensure
            true
            not false
        end
end


feature         -- Conjunction
    and (a,b:BOOLEAN): BOOLEAN

    and_elimination: all(a,b:BOOLEAN)
        require
            a and b
        check
            not a => false
            not b => false
        ensure
            a
            b
        end

    and_introduction: all(a,b:BOOLEAN)
        require
            a; b
        ensure
            a and b
        end

end




feature         -- Disjunction
    or (a,b:BOOLEAN): BOOLEAN

    or_elimination: all(a,b,c:BOOLEAN)
        require
            a or b
            a => c
            b => c
        check
            not c => false
        ensure
            c
        end

    or_introduction: all(a,b:BOOLEAN)
        check
            (not b => false) => b
        ensure
            a => a or b
            b => a or b
        end

end



feature              -- Boolean equivalence
    = (a,b:BOOLEAN): BOOLEAN

    equal_elimination:  all(a,b:BOOLEAN)
        require
            a = b
        ensure
            a => b
            b => a
        end

    equal_introduction:  all(a,b:BOOLEAN)
        require
            a => b
            b => a
        ensure
            a = b
        end

    reflexivity:  all(a:BOOLEAN)
        ensure
            a = a
        end

    symmetry:     all(a,b:BOOLEAN)
        ensure
            a = b => b = a
        end

    transitivity: all(a,b,c:BOOLEAN)
        ensure
            a = b => b = c => a = c
        end

end


feature              -- Boolean algebra

    and_commutativity: all(a,b:BOOLEAN)
        ensure
            (a and b) = (b and a)
        end

    and_associativity: all(a,b,c:BOOLEAN)
        ensure
            (a and b and c) = (a and (b and c))
        end

    lemma: all(a,b:BOOLEAN)
        require
            a or b
        check
            (a or b) => not b => not not a
        ensure
            b or a
        end

    or_commutativity:  all(a,b:BOOLEAN)
        ensure
            (a or b) = (b or a)
        end

    or_associativity:  all(a,b,c:BOOLEAN)
        ensure
            (a or b or c) = (a or (b or c))
        end

    all(a,b,c:BOOLEAN)
        require
            a and (b or c)
        ensure
            (a and b) or (a and c)
        end

    all(a,b,c:BOOLEAN)
        require
            (a and b) or (a and c)
        ensure
            (a and b) or (a and c)
            => ((a and b) => a and (b or c))
            => ((a and c) => a and (b or c))
            => (a and (b or c))
            a and (b or c)
        end

    and_distributivity:
    all(a,b,c:BOOLEAN)
        ensure
            (a and (b or c)) =  ((a and b) or (a and c))
        end

    or_distributivity:
    all(a,b,c:BOOLEAN)
        ensure
            (a or (b and c)) = ((a or b) and (a or c))
        end

    all(a:BOOLEAN)
        ensure
           (a or false)  =  a
           (a and true)  =  a
           (a and not a) =  false
           (a or not a)  =  true
        end
end
