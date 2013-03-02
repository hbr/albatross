immutable class
    BOOLEAN
end

=> (a,b:BOOLEAN): BOOLEAN
    note built_in end

false: BOOLEAN
    note built_in end

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
