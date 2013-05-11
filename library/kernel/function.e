A: ANY
B: ANY

immutable class
    FUNCTION[A,B]
inherit
    ghost UPCOMPLETE_PARTIAL_ORDER
end


feature   -- Basic functions and axioms
    domain(f:CURRENT): ghost A?
            -- The domain of the function f.
        note built_in end

    () (f:CURRENT, a:A): B
            -- The value of the function f at the argument a.
        require
            a in f.domain
        note built_in end

    <= (f,g:CURRENT): ghost BOOLEAN
            -- Is the function f contained in the function g (functions
            -- viewed as sets of key value pairs)?
        ensure
            Result = ( f.domain<=g.domain
                       and
                       all(a:A) a in f.domain => f(a)=g(a) )
        end

    = (f,g:CURRENT): ghost BOOLEAN
            -- Are the functions f and g equal?
        ensure
            Result = (f<=g and g<=f)
        end

    all(f,g,h:CURRENT)
        ensure
            reflexive:       f<=f
            transitive:      f<=g => g<=h => f<=h
            antisymmetric:   f<=g => g<=f => f=g
        end
end