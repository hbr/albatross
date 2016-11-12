use
    any
    boolean_logic
end


G: ANY

class PREDICATE[G] end

(in)  (e:G, p:{G}): BOOLEAN
(/in) (a:G, p:{G}): BOOLEAN -> not p(a)

(<=) (p,q:{G}): ghost BOOLEAN -> all(x) p(x) ==> q(x)


(=) (p,q:{G}): ghost BOOLEAN -> p <= q and q <= p



all(p:{G}) ensure p = p end


class
    PREDICATE[G]
inherit
    ghost ANY
end


all(a,b:G)
        -- leibniz rule
    require  a = b
    ensure   all(p:{G}) p(a) ==> p(b)
    note     axiom end


all(a,b:G)
        -- symmetry of equality
    require
        a = b
    ensure
        b = a
        assert
            b in {x: x = a}
    end

all(a,b,c:G)
        -- transitivity of equality
    require
        a = b
        b = c
    ensure
        a = c
    end





{: Empty and universal set
   ======================= :}

has_some (p:{G}): ghost BOOLEAN
    -> some(x) x in p

is_empty (p:{G}): ghost BOOLEAN
        -- Is the set 'p' empty?
    -> not p.has_some

is_universal (p:{G}): ghost BOOLEAN
        -- Is the set 'p' the universal set?
    -> all(x) x in p

all(p:{G})
    require
        p.is_empty
    ensure
        all(a) a /in p
    end


empty:{G}     = {x: false}

universal:{G} = {x: true}


{: Indirect Proof
   ==============
:}


all(a:G, p:{G})
    require
        a /in p ==> false
    ensure
        a in p
    via require
        not (a in p)
    end
