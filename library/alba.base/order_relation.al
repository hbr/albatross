use
    endorelation
    function_logic
end

A: ANY
B: ANY


{:
# Preorder, partial order and linear order
:}

is_preorder(r:{A,A}): ghost BOOLEAN
    -> r.is_reflexive and
       r.is_transitive


is_partial_order(r:{A,A}): ghost BOOLEAN
    -> r.is_reflexive and
       r.is_transitive and
       r.is_antisymmetric


is_linear_order(r:{A,A}): ghost BOOLEAN
    -> r.is_partial_order and
       r.is_dichotomic


all(r,s:{A,A})
    require
        r.is_partial_order
        s.is_partial_order
    ensure
        (r*s).is_partial_order
    end





{:
# Upper and lower bounds
:}


is_lower_bound(a:A, p:{A}, r:{A,A}): ghost BOOLEAN
        -- Is 'a' a lower bound for the set 'p' with respect to the relation 'r'?
    -> a in r.carrier and all(x) x in p ==> r(a,x)

is_upper_bound(a:A, p:{A}, r:{A,A}): ghost BOOLEAN
        -- Is 'a' an upper bound for the set 'p' with respect to the relation 'r'?
    -> a in r.carrier and all(x) x in p ==> r(x,a)

has_lower_bound(p:{A}, r:{A,A}): ghost BOOLEAN
        -- Does the set 'p' have a lower bound in 'r'?
    -> some(a) a.is_lower_bound(p,r)

has_upper_bound(p:{A}, r:{A,A}): ghost BOOLEAN
        -- Does the set 'p' have an upper bound in 'r'?
    -> some(a) a.is_upper_bound(p,r)

lower_bounds(p:{A}, r:{A,A}): ghost {A}
        -- The set of all lower bounds of the set 'p' with respect to the
        -- relation 'r'.
    -> {a: a.is_lower_bound(p,r)}

upper_bounds(p:{A}, r:{A,A}): ghost {A}
        -- The set of all upper bounds of the set 'p' with respect to the
        -- relation 'r'.
    -> {a: a.is_upper_bound(p,r)}


all(a:A, p:{A}, r:{A,A})
        -- Duality
    require
        a.is_lower_bound(p,r.inverse)
    ensure
        a.is_upper_bound(p,r)
    assert
        all(x)
            require
                x in p
            ensure
                r(x,a)
            assert
                (r.inverse)(a,x)
            end
    end


all(a:A, p:{A}, r:{A,A})
        -- Duality
    require
        a.is_upper_bound(p,r.inverse)
    ensure
        a.is_lower_bound(p,r)
    assert
        all(x)
            require
                x in p
            ensure
                r(a,x)
            assert
                (r.inverse)(x,a)
            end
    end



all(a,b:A, p:{A}, r:{A,A})
        -- Transitivity of a lower bound
    require
        r.is_partial_order
        r(a,b)
        b.is_lower_bound(p,r)
    ensure
        a.is_lower_bound(p,r)
    end


all(a,b:A, p:{A}, r:{A,A})
        -- Transitivity of an upper bound
    require
        r.is_partial_order
        r(a,b)
        a.is_upper_bound(p,r)
    ensure
        b.is_upper_bound(p,r)
    assert
        all(x)
            require
                x in p
            ensure
                r(x,b)
            assert
                r(x,a)
            end
    end







{:
# Least elements
:}

is_least(a:A, p:{A}, r:{A,A}): ghost BOOLEAN
        -- Is 'a' the least element of set 'p' with respect to the relation 'r'?
    -> a in p and a.is_lower_bound(p,r)

has_least(p:{A}, r:{A,A}): ghost BOOLEAN
        -- Does the set 'p' have a least element?
    -> some(x) x.is_least(p,r)


least(p:{A}, r:{A,A}): ghost A
        -- The least element of the set 'p' in the partial order 'r'.
    require
        r.is_partial_order
        p.has_least(r)
    ensure
        Result.is_least(p,r)
    end


is_least(a:A,r:{A,A}): ghost BOOLEAN
        -- Is 'a' the least element of the carrier of 'r'?
    -> all(x) r(a,x)


has_least(r:{A,A}): ghost BOOLEAN
        -- Does the carrier of 'r' have a least element?
    -> some(a) a.is_least(r)


least(r:{A,A}): ghost A
        -- The least element of the carrier of 'r'.
    require
        r.is_partial_order
        r.has_least
    ensure
        Result.is_least(r)
    end





{:
# Greatest elements
:}

is_greatest(a:A, p:{A}, r:{A,A}): ghost BOOLEAN
        -- Is 'a' the greatest element of set 'p' with respect to the relation 'r'?
    -> a in p and a.is_upper_bound(p,r)

has_greatest(p:{A}, r:{A,A}): ghost BOOLEAN
        -- Does the set 'p' have a greatest element?
    -> some(x) x.is_greatest(p,r)



greatest(p:{A}, r:{A,A}): ghost A
        -- The greatest element of the set 'p' in the partial order 'r'.
    require
        r.is_partial_order
        p.has_greatest(r)
    ensure
        Result.is_greatest(p,r)
    end


all(a:A, p:{A}, r:{A,A})
    require
        a.is_greatest(p,r)
    ensure
        a.is_least(p,r.inverse)
    end

all(a:A, p:{A}, r:{A,A})
    require
        a.is_least(p,r)
    ensure
        a.is_greatest(p,r.inverse)
    end




{:
# Infimum and supremum
:}

is_infimum(a:A, p:{A}, r:{A,A}): ghost BOOLEAN
        -- Is 'a' an infimum i.e. a greatest lower bound of the set 'p' with
        -- respect to the relation 'r'
    -> a.is_greatest(p.lower_bounds(r),r)

is_supremum(a:A, p:{A}, r:{A,A}): ghost BOOLEAN
        -- Is 'a' a supremum i.e. a least upper bound of the set 'p' with
        -- respect to the relation 'r'
    -> a.is_least(p.upper_bounds(r),r)

has_infimum(p:{A}, r:{A,A}): ghost BOOLEAN
        -- Does the set 'p' have a greatest lower bound?
    -> some(a) a.is_infimum(p,r)

has_supremum(p:{A}, r:{A,A}): ghost BOOLEAN
        -- Does the set 'p' have a least upper bound?
    -> some(a) a.is_supremum(p,r)

infimum(p:{A}, r:{A,A}): ghost A
        -- The greatest lower bound of the set 'p' in the partial order 'r'.
    require
        r.is_partial_order
        p.has_infimum(r)
    ensure
        Result.is_infimum(p,r)
    end

supremum(p:{A}, r:{A,A}): ghost A
        -- The least upper bound of the set 'p' in the partial order 'r'.
    require
        r.is_partial_order
        p.has_supremum(r)
    ensure
        Result.is_supremum(p,r)
    end



all(a:A, p:{A}, r:{A,A})
    require
        a.is_infimum(p,r)
    ensure
        a.is_supremum(p,r.inverse)
    assert
        a.is_greatest(p.lower_bounds(r), r)

        p.lower_bounds(r) = p.upper_bounds(r.inverse)

        a.is_least(p.upper_bounds(r.inverse), r.inverse)
    end





{:
# Up- and downclosed sets
:}

is_downclosed(p:{A}, r:{A,A}): ghost BOOLEAN
    -> p <= r.carrier
       and
       all(x,y) r(x,y) ==> y in p ==> x in p

is_upclosed(p:{A}, r:{A,A}): ghost BOOLEAN
    -> p <= r.carrier
       and
       all(x,y) r(x,y) ==> x in p ==> y in p



all(ps:{{A}}, r:{A,A})
        -- An arbitrary union of downclosed sets is downclosed
    require
        all(p) p in ps ==> p.is_downclosed(r)
    ensure
        (+ ps).is_downclosed(r)

    assert
        all(x)
                -- + ps <= r.carrier
            require
                x in + ps
            ensure
                x in r.carrier
            via
                some(p) p in ps and x in p
                assert
                    p.is_downclosed(r)
            end

        all(x,y)
                -- (+ ps).is_downclosed(r)
            require
                r(x,y)
                y in + ps
            ensure
                x in + ps
            via
                some(p) p in ps and y in p
                assert
                    p.is_downclosed(r)
                    p in ps and x in p
            end
    end





{:
# Upper and lower set
:}


upper_set(a:A, r:{A,A}): ghost {A}
        -- The set of all elements above 'a' in the relation 'r'.
    -> {x: r(a,x)}


lower_set(a:A, r:{A,A}): ghost {A}
        -- The set of all elements below 'a' in the relation 'r'.
    -> {(p): a in r.carrier ==> a in p,
             all(x,y) r(x,y) ==> y in p ==> x in p}


lower_sets(r:{A,A}): ghost {{A}}
        -- The collection of all lower sets of the relation 'r'.
    -> {p: some(a) p = a.lower_set(r)}



strict_lower_set(a:A, r:{A,A}): ghost {A}
        -- The set of all elements strictly below 'a' in the relation 'r'.
    -> {x: x in a.lower_set(r) and x /= a}




all(a,b:A, r:{A,A})
        -- All elements of a lower set are in the carrier.
    require
        b in a.lower_set(r)
    ensure
        b in r.carrier

    inspect
        b in a.lower_set(r)
    end



all(ps:{{A}}, r:{A,A})
        -- The union of all lower sets is the carrier.
    require
        ps = {p: some(a) a in r.carrier and p = a.lower_set(r)}
    ensure
        + ps = r.carrier
    assert
        all(x)
            require
                x in + ps
            ensure
                x in r.carrier
            via some(p) p in ps and x in p
            via some(a) a in r.carrier and p = a.lower_set(r)
            end

        all(x)
            require
                x in r.carrier
            ensure
                x in + ps
            assert
                x in r.carrier and x.lower_set(r) = x.lower_set(r)

                x.lower_set(r) in ps and x in x.lower_set(r)

                some(p) p in ps and x in p
            end
    end


all(a,b:A, r:{A,A})
    require
        r.is_partial_order
        a in b.lower_set(r)
    ensure
        r(a,b)

    inspect
        a in b.lower_set(r)
    end


all(a,b:A, r:{A,A})
    require
        r.is_partial_order
        r(a,b)
    ensure
        a.lower_set(r) <= b.lower_set(r)
    assert
        all(x)
            require
                x in a.lower_set(r)
            ensure
                x in b.lower_set(r)
            inspect
                x in a.lower_set(r)
            end
    end




{:
# Directed sets
:}

is_updirected(d:{A}, r:{A,A}): ghost BOOLEAN
    -> d.has_some
       and
       all(x,y)
           {x,y} <= d ==>
           some(z) z.is_upper_bound({x,y},r)





{:
# Monotonic functions

A monotonic function is between two order relations is a function which
preserves the order.


:}


is_monotonic(f:A->B, r1:{A,A}, r2:{B,B}): ghost BOOLEAN
    -> f.is_total(r1)
       and
       all(x,y)
           {x,y} <= r1.carrier
           ==>
           r1(x,y)
           ==>
           r2(f(x), f(y))


is_monotonic(f:A->A, r:{A,A}): ghost BOOLEAN
    -> f.is_monotonic(r,r)



is_reflecting(f:A->B, r:{A,A}, s:{B,B}): ghost BOOLEAN
    -> f.is_total(r)
       and
       all(x,y)
           {x,y} <= r.carrier ==>
           s(f(x),f(y)) ==>
           r(x,y)


is_embedding(f:A->B, r:{A,A}, s:{B,B}): ghost BOOLEAN
    -> f.is_total(r)
       and
       f.is_injective
       and
       f.is_monotonic(r,s)
       and
       f.inverse.is_monotonic(s,r)




all(f:A->B, r:{A,A}, s:{B,B})
    require
        r.is_partial_order
        s.is_partial_order
        f.is_monotonic(r,s)
        f.is_reflecting(r,s)
        f.domain = r.carrier
    ensure
        f.is_injective
    assert
        all(x,y)
            require
                x in f.domain
                y in f.domain
                f(x) = f(y)
            ensure
                x = y
            assert
                r(x,x)
                f(y) in {z: s(f(x),z)}
                s(f(x),f(y))
            end
    end


{:
# Continuous functions

An upcontinuous function preserves suprema i.e.

    x.is_supremum(p,r1) ==> f(x).is_supremum(f[p],r2)

and a downcontiunous function presevers infima

    x.is_infimum(p,r1) ==> f(x).is_infimum(f[p],r2)
:}

is_upcontinuous(f:A->B, r1:{A,A}, r2:{B,B}): ghost BOOLEAN
    -> r1.carrier <= f.domain
       and
       all(p,s)
           s.is_supremum(p,r1)
           ==>
           f(s).is_supremum(f[p],r2)


is_upcontinuous(f:A->A, r:{A,A}): ghost BOOLEAN
    -> f.is_upcontinuous(r,r)

is_prefixpoint(a:A, f:A->A, r:{A,A}): ghost BOOLEAN
    -> a in f.domain and r(a,f(a))

is_increasing(f:A->A, r:{A,A}): ghost BOOLEAN
    -> f.is_total(r) and all(x) x in r.carrier ==> r(x,f(x))


{:
# Complete partial order
:}

is_complete_partial_order(r:{A,A}): ghost BOOLEAN
    -> r.is_partial_order
       and
       all(d) d.is_updirected(r) ==> d.has_supremum(r)




{:
# Wellorder
:}


is_wellorder(r:{A,A}): ghost BOOLEAN
        -- Is 'r' a wellorder i.e. a linear order where every nonempty set
        -- has a least element?
    -> r.is_linear_order
       and
       all(p) p <= r.carrier ==> p.has_some ==> p.has_least(r)




{:
# Wellfounded
:}


accessibles (r:{A,A}): ghost {A}
        -- The elements which are accessible by the relation 'r' i.e. all
        -- elements in the carrier of 'r' which have no predecessor or whose
        -- predecessors are all accessible.
    -> {(p): all(y) y in r.carrier ==> (all(x) r(x,y) ==> x in p) ==> y in p}


is_wellfounded (r:{A,A}): ghost BOOLEAN
        -- Is the relation 'r' wellfounded i.e. are all its elements accessible?
    -> r.carrier <= r.accessibles


all(r:{A,A})
    ensure
        r.accessibles <= r.carrier
    assert
        all(a)
            require
                a in r.accessibles
            ensure
                a in r.carrier
            inspect
                a in r.accessibles
            end
    end




{:
# Closure system

A closure system in a partial order is a subset of the carrier such that all
subsets of the closure system have an infimum in the closure system. I.e. the
closure system is "closed" with respect to the infimum operation.

Because of this property it is always possible to find a least element in the
closure system which is above another element of the carrier.

A weak closure system is not completely closed with respect to the infimum
operation. Empty subsets of the closure system are excluded. However a weak
closure system must be big enough to contain arbitrarily large elements. The
last property is implicit in a normal closure system.

:}

is_weak_closure_system (p:{A}, r:{A,A}): ghost BOOLEAN
    -> r.is_partial_order
       and
       p <= r.carrier
       and
       (all(x)
            x in r.carrier ==>
            (p * x.upper_set(r)).has_some)  -- p is sufficiently large
       and
       all(q)
           q <= p ==> q.has_some
           ==>
           some(x) x.is_infimum(q,r) and x in p



is_closure_system (p:{A}, r:{A,A}): ghost BOOLEAN
    -> r.is_partial_order
       and
       p <= r.carrier
       and
       all(q)
           q <= p
           ==>
           some(x) x.is_infimum(q,r) and x in p


is_closure_map (f:A->A, r:{A,A}): ghost BOOLEAN
    -> f.is_total(r) and
       f.is_increasing(r) and
       f.is_monotonic(r) and
       f.is_idempotent


all(a:A, p:{A}, r:{A,A})
        -- For all elements there is always a least element in the closure system
        -- system above the element.
    require
        p.is_weak_closure_system(r)
        a in r.carrier
    ensure
        (p * a.upper_set(r)).has_least(r)

    assert
        all(q)
            require
                q = p * a.upper_set(r)  -- q represents all elements which are in
                                        -- the closure system above a
            ensure
                q.has_least(r)

            assert
                q <= p
                q.has_some
            via some(x) x.is_infimum(q,r) and x in p
            assert
                q.has_some
                x.is_least(q,r)
                {: x is the infimum of q i.e. the greatest lower bound. a is a
                   lower bound of q. Therefore r(a,x) must be valid and x must
                   be in q. An infimum which is in a set is the least element
                   of the set.  :}
            end
    end



all(p:{A}, r:{A,A})
        -- A closure system is a weak closure system.
    require
        p.is_closure_system(r)
    ensure
        p.is_weak_closure_system(r)

    assert
        all(x)
            require
                x in r.carrier
            ensure
                (p * x.upper_set(r)).has_some
            assert
                x in x.upper_set(r)
            via some(z) z.is_infimum(empty,r) and z in p -- p is a closure system
            assert
                z in p * x.upper_set(r)
                {: The lower bounds of the empty set consists of the whole carrier
                   of the relation. Therefore the infimum of the empty set is the
                   greatest element of the carrier which is certainly in the upper
                   set of 'x'. :}
            end
    end




closed(a:A, p:{A}, r:{A,A}): ghost A
        -- The least element above 'a' of the closure system 'p' in the
        -- partial order 'r'.
    require
        p.is_weak_closure_system(r)
        a in r.carrier
    ensure
        -> least (p * a.upper_set(r), r)
    end



{:# Interior systems
:}


is_interior_system (p:{A}, r:{A,A}): ghost BOOLEAN
    -> r.is_partial_order
       and
       p <= r.carrier
       and
       all(q) q <= p ==> some(x) x.is_supremum(q,r) and x in p


is_weak_interior_system (p:{A}, r:{A,A}): ghost BOOLEAN
    -> r.is_partial_order
       and
       p <= r.carrier
       and
       (all(x) x in r.carrier ==> (p * x.lower_set(r)).has_some)
       and
       all(q)
           q <= p ==> q.has_some
           ==>
           some(x) x.is_supremum(q,r) and x in p


all(p:{A}, r:{A,A})
        -- Duality
    require
        p.is_interior_system(r)
    ensure
        p.is_closure_system(r.inverse)
    assert
        all(q)
            require
                q <= p
            ensure
                some(x) x.is_infimum(q,r.inverse) and x in p
            via
                some(x) x.is_supremum(q,r) and x in p
            assert
                x.is_infimum(q,r.inverse) and x in p
            end
    end
