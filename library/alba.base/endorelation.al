use
    predicate_logic
    relation
end

A: ANY

{: Carrier
   ======= :}
carrier (r:{A,A}): ghost {A} -> domain(r) + range(r)

identity: {A,A} = {x,y: x = y}

diagonal(p:{A}): {A,A}
    -> {x,y: x = y and x in p}


{: Closure
   ======= :}


closed(a:A, r:{A,A}): ghost {A}
    -> {(p): a in p, all(x,y) x in p ==> r(x,y) ==> y in p}


closed(p:{A}, r:{A,A}): ghost {A}
    -> {(q): all(x) x in p ==> x in q,
             all(x,y) x in q ==> r(x,y) ==> y in q}


all(a:A, r:{A,A})
    ensure
        a.closed(r) <= {a}.closed(r)
        assert
            all(x)
                require
                    x in a.closed(r)
                ensure
                    x in {a}.closed(r)
                    inspect x in a.closed(r)
                end
    end


all(a:A, r:{A,A})
    ensure
        {a}.closed(r) <= a.closed(r)
        assert
            all(x)
                require
                    x in {a}.closed(r)
                ensure
                    x in a.closed(r)
                    inspect x in {a}.closed(r)
                    case all(x) x in {a} ==> x in {a}.closed(r)
                        assert
                            a = x
                            a in a.closed(r)
                end
    end





{: Reflexivity
   =========== :}


is_reflexive (r:{A,A}): ghost BOOLEAN
    -> (all(x,y) r(x,y) ==> r(x,x)) and
       (all(x,y) r(x,y) ==> r(y,y))


all(r:{A,A})
    require
        r.is_reflexive
    ensure
        r.domain  = r.range
    assert
        all(x) require x in r.domain
               ensure  x in r.range
                       via some(y) r(x,y)
                           assert
                               r(x,x)
               end

        all(y) require y in r.range
               ensure  y in r.domain
                       via some(x) r(x,y)
                           assert
                               r(y,y)
               end
        r.domain = r.range
    end


all(r:{A,A})
    require
        r.is_reflexive
    ensure
        r.domain  = r.range
    assert
        all(x) require x in r.domain
               ensure  x in r.range
                       via some(y) r(x,y)
                           assert
                               r(x,x)
               end

        all(y) require y in r.range
               ensure  y in r.domain
                       via some(x) r(x,y)
                           assert
                               r(y,y)
               end
        r.domain = r.range
    end


all(r:{A,A})
    require
        r.is_reflexive
    ensure
        r.domain <= r.range
    assert
        all(x) require x in r.domain
               ensure  x in r.range
                       via some(y) r(x,y)
                           assert
                               r(x,x)
               end
    end

all(r:{A,A})
    require
        r.is_reflexive
    ensure
        r.range <= r.domain
    assert
        all(y) require y in r.range
               ensure  y in r.domain
                       via some(x) r(x,y)
                           assert
                               r(y,y)
               end
    end


all(r:{A,A})
    require
        r.is_reflexive
    ensure
        r.carrier <= r.domain
    assert
        all(x)
        require
            x in r.carrier
        ensure
            x in r.domain
            if x in r.domain orif x in r.range
        end
    end

all(r:{A,A})
    require
        r.is_reflexive
    ensure
        r.carrier <= r.range
    assert
        all(a)
            require
                a in r.carrier
            ensure
                a in r.range
                if a in r.domain orif a in r.range
            end
    end





to_reflexive (p:{A}): {A,A}
    -> {x,y: x=y and p(x)}

all(p:{A})
    ensure
        inverse(p.to_reflexive) = p.to_reflexive
    end

all(p:{A})
    ensure
        domain(p.to_reflexive) = p
    assert
        all(x) require x in p
               ensure  x in domain(p.to_reflexive)
               assert   (p.to_reflexive)(x,x) end

        all(x) require x in domain(p.to_reflexive)
               ensure  x in p
               assert   some(y) (p.to_reflexive)(x,y)
                       all(y)  require (p.to_reflexive)(x,y)
                               ensure  x in p end
               end
    end


all(p:{A})
    ensure
        range(p.to_reflexive) = p
    assert
        p.to_reflexive.inverse = p.to_reflexive

        range(p.to_reflexive) = domain(p.to_reflexive.inverse)
    end

all(p:{A})
    ensure
        carrier(p.to_reflexive) = p
    assert
        domain(p.to_reflexive) = p
        range (p.to_reflexive) = p
    end



reflexive (r:{A,A}): ghost {A,A}
    -> {(s): all(a,b) r(a,b) ==> s(a,b),
             all(a,b) r(a,b) ==> s(a,a),
             all(a,b) r(a,b) ==> s(b,b)}


all(a,b:A, r:{A,A})
    require
        (r.reflexive)(a,b)
    ensure
        (r.reflexive)(a,a)

        inspect (r.reflexive)(a,b)
    end

all(a,b:A, r:{A,A})
    require
        (r.reflexive)(a,b)
    ensure
        (r.reflexive)(b,b)

        inspect (r.reflexive)(a,b)
    end






all(r:{A,A})
    ensure
        r.reflexive.is_reflexive
    end



{: Symmetry
   ======== :}

symmetric (r:{A,A}): {A,A}
    -> r + r.inverse





{: Transitivity
   ============ :}

is_transitive(r:{A,A}): ghost BOOLEAN
        -- Is the relation 'r' transitive?
    -> all(a,b,c) r(a,b) ==> r(b,c) ==> r(a,c)

(+) (r:{A,A}): ghost {A,A}
        -- The least transitive relation which contains 'r'.
    -> {(s): all(x,y)   r(x,y) ==> s(x,y),
             all(x,y,z) s(x,y) ==> r(y,z) ==> s(x,z)}


all(a,b,c:A, r:{A,A})
    require
        (+r)(b,c)
    ensure
        (+r)(a,b) ==> (+r)(a,c)
    inspect
        (+r)(b,c)
    case all(a,b,c) (+r)(a,b) ==> r(b,c) ==> (+r)(a,c)
    assert
        all(a) (+r)(a,b) ==> (+r)(a,c)
        all(a)
        require (+r)(a,b)
        ensure  (+r)(a,c) end
    end

all(r:{A,A})
    ensure
        (+r).is_transitive
    end



{: Reflexive transitive closure
   ============================ :}


(*) (r:{A,A}): ghost {A,A}
        -- The least reflexive transitive relation which contains 'r'.
    -> {x,y: y in x.closed(r)}





{: Equivalence
   =========== :}

equivalence (r:{A,A}): ghost {A,A}
    -> + r.reflexive.symmetric
