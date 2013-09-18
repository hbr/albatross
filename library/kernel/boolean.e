immutable class
    BOOLEAN
end


feature   -- Basic functions
    => (a,b:BOOLEAN): BOOLEAN
        note built_in end

    false: BOOLEAN
        note built_in end

end


feature {NONE}    -- Function definitions and axiom
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
        note built_in ensure
            double_negation: not not a => a
        end
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
        check
            a or b => (a => b or a) => (b => b or a) => b or a
        ensure
            (a or b) => (b or a)
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
end
