G: ANY

immutable class
    PREDICATE[G]    
inherit
    ghost ANY
end

in (e:G, p:CURRENT): BOOLEAN
        -- Is `e' contained in the set `p'?
    note
        built_in
    end

<= (p,q:CURRENT): ghost BOOLEAN
        -- Is `p' a subset of `q'?
    ensure
        Result = all(e) e in p => e in q
    end

= (p,q:CURRENT): ghost BOOLEAN
        -- Does `p' have the same elements as `q'?
    ensure
        Result = (p<=q and q<=p)
    end

all(p,q:CURRENT)
    ensure
        (p=q) = (all(e) e in p = e in q)
    end


0: CURRENT
        -- The empty set
    ensure
        Result = {e: false}
    end

1: CURRENT
        -- The universal set
    ensure
        Result = {e: true}
    end


+ (p,q:CURRENT): CURRENT
        -- The union of the sets `p' and `q'.
    ensure
        Result = {e: e in p or e in q}
    end

* (p,q:CURRENT): CURRENT
        -- The intersection of the sets `p' and `q'.
    ensure
        Result = {e: e in p and e in q}
    end


- (p:CURRENT): CURRENT
        -- The complement of the set `p'.
    ensure
        Result = {e: e /in p}
    end


+ (p:CURRENT, e:G): CURRENT
        -- The set `p' with the element `e'.
    ensure
        Result = {v: v in p or v=e}
    end

- (p,q:CURRENT): CURRENT
        -- The set `p' without the elements of the set `q'.
    ensure
        Result = p*(-q)
    end
