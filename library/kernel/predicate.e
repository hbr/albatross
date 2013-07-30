G: ANY

immutable class
    PREDICATE[G]    
inherit
    ghost BOOLEAN_LATTICE
        redefine <= end
    ghost COMPLETE_PARTIAL_ORDER
        redefine <= end
end


feature    -- Basic functions
    in (e:G, p:CURRENT): BOOLEAN
            -- Is `e' contained in the set `p'?
        note
            built_in
        end

    all(p:G?, e:BOOLEAN)
        note built_in ensure
            exist_intro:   all(x) x in p => some(y) y in p
            exist_elim:    (some(x) x in p)
                           => (all(x) x in p => e)
                           => e
        end

    all(a:G, e:BOOLEAN)
        note built_in ensure
            -- Not necessary???
            in_1: e[x:=a]     =>   a in {x:e}
            in_2: a in {x:e}  =>   e[x:=a]
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
end



feature   -- Boolean algebra
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
end



feature   -- Infimum and supremum
    infimum(pp:CURRENT?): ghost CURRENT
            -- The infimum of all sets in pp.
        ensure
            Result = {e:G: all(p:CURRENT) p in pp => e in p}
        end

    supremum(pp:CURRENT?): ghost CURRENT
            -- The supremum of all sets in pp.
        ensure
            Result = {e:G: some(p:CURRENT) p in pp and e in p}
        end
end

