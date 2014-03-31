feature     -- Basic functions and axioms
    false: BOOLEAN
        note built_in end

    true: BOOLEAN
        note built_in end

    =>  (a,b:BOOLEAN): BOOLEAN
        note built_in end

    not (a:BOOLEAN): BOOLEAN
        note built_in end

    and (a,b:BOOLEAN): BOOLEAN
        note built_in end

    or  (a,b:BOOLEAN): BOOLEAN
        note built_in end

    =  (a,b:BOOLEAN): BOOLEAN
        note built_in end

    all(a:BOOLEAN)
        note built_in ensure
            truth:         true
            indirect:      (not a => false) => a
            refutation:    (a => false)     => not a
            contradiction: not a => a => false
        end

    all(a,b:BOOLEAN)
        note
            built_in
        ensure
            a and b => a
            a and b => b
            a => b => a and b
        end

    all(a,b:BOOLEAN)
        note
            built_in
        ensure
            a => a or b
            b => a or b
        end

    all(a,b,c:BOOLEAN)
        note
            built_in
        ensure
            a or b => (a => c) => (b => c) => c
        end

    all(a:BOOLEAN)
        note built_in ensure
            a = a
        end

    all(a,b:BOOLEAN)
        note
            built_in
        ensure
            a = b => a => b
            a = b => b => a
            (a => b) => (b => a) => a = b
        end
end


feature                  -- Commutativity and associativity of 'and' / 'or'
    all(a,b:BOOLEAN)
        ensure
            (a and b) = (b and a)
        end

    all(a,b,c:BOOLEAN)
        ensure
            (a and b and c) = (a and (b and c))
        end

    all(a,b:BOOLEAN)
        require
            a or b
        check
            (a => b or a) => (b => b or a) => b or a
        ensure
            b or a
        end

    all(a,b:BOOLEAN)
        ensure
            (a or b) = (b or a)
        end


    lemma: all(a,b,c:BOOLEAN)
        require
            a or b
        check
            (a => a or (b or c))
            => (b => a or (b or c))
            => a or (b or c)
        ensure
            a or (b or c)
        end

    lemma: all(a,b,c:BOOLEAN)
        require
            (a or b) or c
        check
            ((a or b) or c)
            => (a or b => a or (b or c))
            => (c => a or (b or c))
            => a or (b or c)
        ensure
            a or (b or c)
        end

    all(a,b,c:BOOLEAN)
        ensure
            (a or b or c) = ((a or b) or c)
        end
end


feature     -- Distributivity of "and"

    lemma: all(a,b,c:BOOLEAN)
        require
           a and (b or c)
        check
           (b => (a and b) or (a and c))
           => (c => (a and b) or (a and c))
           => (a and b) or (a and c)
        ensure
           (a and b) or (a and c)
        end

    lemma: all(a,b,c:BOOLEAN)
        require
           (a and b) or (a and c)
        check
           (a and b => a)
           => (a and c => a)
           => a

           (a and b => b or c)
           => (a and c => b or c)
           => b or c
        ensure
           a and (b or c)
        end

    all(a,b,c:BOOLEAN)
        ensure
           (a and (b or c)) = ((a and b) or (a and c))
        end

end


feature     -- Distributivity of "or"

    lemma: all(a,b,c:BOOLEAN)
        require
            a or (b and c)
        check
            (a => (a or b) and (a or c))
            => ((b and c) => (a or b) and (a or c))
            => (a or b) and (a or c)
        ensure
            (a or b) and (a or c)
        end

    lemma: all(a,b,c:BOOLEAN)
        require
            a or b
            a or c
        check
            (a => a or (b and c))
            => (b => a or (b and c))
            => a or (b and c)

            (a => a or (b and c))
            => (c => a or (b and c))
            => a or (b and c)
        ensure
            a or (b and c)
        end

    all(a,b,c:BOOLEAN)
        ensure
            (a or (b and c)) = ((a or b) and (a or c))
        end

    some_test: all(c,b,a:BOOLEAN)
        ensure
            (a or (b and c)) = ((a or b) and (a or c))
        end

end


feature                       -- top and bottom
    lemma: all(a:BOOLEAN)
        require
            a
        ensure
            a or false
        end

    lemma: all(a:BOOLEAN)
        require
            a or false
        check
            not a => a => false

            (a or false)
            => (a     => not a => false)
            => (false => not a => false)
            => not a => false

            not a => false
        ensure
            a
        end

    all(a:BOOLEAN)
        ensure
           (a or false)  =  a
           (a and true)  =  a
        end


    all(a:BOOLEAN)
        check
            false => not a => false
            false => not not a => false
            false => a
            false => not a

            not a => a => false
        ensure
           (a and not a) =  false
        end

    lemma: all(a,b:BOOLEAN)
        require
            not a => not b
            b
        check
            not b => b => false
            (not a => false) => a
        ensure
            a
        end

    lemma: all(a,b:BOOLEAN)
        require
            a => b
            not b
        check
            not b => b => false
            (a => false) => not a
        ensure
            not a
        end

    all(a:BOOLEAN)
        check
           a => a or not a
           not a => a or not a

           not (a or not a) => not a
           not (a or not a) => not not a
           not not a => not a => false

           not (a or not a) => false
        ensure
           (a or not a)  =  true
        end
end
