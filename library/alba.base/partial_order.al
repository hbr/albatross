use
    predicate_logic
    function
    tuple
end

deferred class PARTIAL_ORDER end

PO:  PARTIAL_ORDER
PO2: PARTIAL_ORDER


(<=) (a,b:PO): BOOLEAN   deferred end

(=)  (a,b:PO): BOOLEAN   deferred end

all(a,b,c:PO)
    ensure
        a = a
        a <= a                               -- reflexive
        (a <= b) ==> (b <= a) ==> (a = b)    -- antisymmetric
        (a <= b) ==> (b <= c) ==> (a <= c)   -- transitive
    deferred
    end


deferred class PARTIAL_ORDER
inherit        ANY end



(<)  (a,b:PO): BOOLEAN  -> a /= b and a <= b

(>=) (a,b:PO): BOOLEAN  -> b <= a

(>)  (a,b:PO): BOOLEAN  -> b < a

is_lower_bound (a:PO, p:{PO}): ghost BOOLEAN -> all(x) p(x) ==> a <= x

is_upper_bound (a:PO, p:{PO}): ghost BOOLEAN -> all(x) p(x) ==> x <= a

is_least (a:PO, p:{PO}): ghost BOOLEAN    -> p(a) and a.is_lower_bound(p)

is_greatest (a:PO, p:{PO}): ghost BOOLEAN -> p(a) and a.is_upper_bound(p)

is_minimal (a:PO, p:{PO}): ghost BOOLEAN  -> p(a) and all(x) x < a ==> not p(x)

is_maximal (a:PO, p:{PO}): ghost BOOLEAN  -> p(a) and all(x) a < x ==> not p(x)

has_least (p:{PO}): ghost BOOLEAN -> some(x) x.is_least(p)

has_greatest (p:{PO}): ghost BOOLEAN -> some(x) x.is_greatest(p)

upper_bounds (p:{PO}): ghost {PO} -> {x: x.is_upper_bound(p)}

lower_bounds (p:{PO}): ghost {PO} -> {x: x.is_lower_bound(p)}

is_infimum (a:PO, p:{PO}): ghost BOOLEAN  -> a.is_greatest(p.lower_bounds)

is_supremum (a:PO, p:{PO}): ghost BOOLEAN -> a.is_least(p.upper_bounds)

has_infimum (p:{PO}): ghost BOOLEAN -> some(x) x.is_infimum(p)

has_supremum (p:{PO}): ghost BOOLEAN -> some(x) x.is_supremum(p)

is_monotonic(f:PO->PO2): ghost BOOLEAN ->
    all(a,b:PO) {a,b} <= f.domain ==> a <= b ==> f(a) <= f(b)

is_antitonic(f:PO->PO2): ghost BOOLEAN ->
    all(a,b:PO) {a,b} <= f.domain ==> a <= b ==> f(b) <= f(a)

is_ascending(f:PO->PO): ghost BOOLEAN ->
    all(a) (f.domain)(a) ==> a <= f(a)

is_descending(f:PO->PO): ghost BOOLEAN ->
    all(a) (f.domain)(a) ==> f(a) <= a



all(a,b:PO, p:{PO}) require a.is_least(p)
                           b.is_least(p)
                   ensure  a = b end

all(a,b:PO, p:{PO}) require a.is_greatest(p)
                           b.is_greatest(p)
                   ensure  a = b end

all(a,b:PO, p:{PO})
    ensure
        a.is_infimum(p)  ==> b.is_infimum(p)  ==> a = b
    end



all(a,b:PO, p:{PO})
    ensure
        a.is_supremum(p) ==> b.is_supremum(p) ==> a = b
    end



least(p:{PO}): ghost PO
    require
        some(x) x.is_least(p)
    ensure
        Result.is_least(p)
    end



greatest(p:{PO}): ghost PO
    require
        some(x) x.is_greatest(p)
    ensure
        Result.is_greatest(p)
    end


(*) (p:{PO}): ghost PO
    require
        some(x) x.is_infimum(p)
    ensure
        Result.is_infimum(p)
    end

(+) (p:{PO}):  ghost PO
    require
        some(x) x.is_supremum(p)
    ensure
        Result.is_supremum(p)
    end


all(a,b,c:PO)
    require
        a < b
        b <= c
    ensure
        a /= c
    proof
        require a = c
        ensure  false
        proof   c = a
                a in {x: b <= x}
        end
    end


all(a,b,c:PO)
    require
        a <= b
        b < c
    ensure
        a /= c
    proof
        require a = c
        ensure  false
        proof   c in {x: x <= b}
        end
    end

all(a,b,c:PO)
    require
        a < b
        b < c
    ensure
        a < c
    end

all(a,b,c:PO)
    require
        a = b
        b <= c
    ensure
        a <= c
    proof
        b = a
        a in {x: x <= c}
    end


all(a,b,c:PO)
    require
        a <= b
        b = c
    ensure
        a <= c
    end


all(a,b:PO, p:{PO})
    require
       a <= b
       b.is_lower_bound(p)
    ensure
       a.is_lower_bound(p)
    end


all(a:PO)
    ensure
        a.is_lower_bound({a})
    proof
        all(x) require  {a}(x)
               ensure   a <= x
               proof    x = a
                        {y: y <= x}(a)
               end
    end


all(x:PO, p,q:{PO})
    require
        x.is_lower_bound(p)
        x.is_lower_bound(q)
    ensure
        ((p + q).lower_bounds)(x)
    proof
        all(y) require (p + q)(y)
               ensure  x <= y
               proof   p(y) ==> x <= y
               end
    end



all(x:PO, p,q:{PO})
    require
        ((p + q).lower_bounds)(x)
    ensure
        x.is_lower_bound(p)
    end


all(x:PO, p,q:{PO})
    require
        ((p + q).lower_bounds)(x)
    ensure
        x.is_lower_bound(q)
    end


all(a,b:PO, p,q:{PO})
    require
        a.is_infimum(p)
        b.is_infimum(q)
        p <= q
    ensure
        b <= a
    proof
        b.is_lower_bound(p)
    end


all(a:PO, p:{PO})
    require
        a.is_least(p)
    ensure
        a.is_infimum(p)
    proof
        all(x) require x.is_lower_bound(p)
               ensure  x <= a
               proof   all(y) p(y) ==> x <= y
                       p(a)
               end
    end


all(a:PO, p:{PO})
    require
        a.is_infimum(p)
        a in p
    ensure
        a.is_least(p)
    end


all(a:PO)
    ensure
        a.is_infimum({x: a <= x})
    proof
        a.is_least({x: a <= x})
    end



all(p:{PO})
    require
        some(x) x.is_infimum(p)
    ensure
        (*p).is_infimum(p)
    end



all(x:PO, p:{PO})
    require
        some(x) x.is_infimum(p)
        x.is_infimum(p)
    ensure
        x = *p
    end

all(p,q:{PO})
    require
        p.has_infimum
        q.has_infimum
        p <= q
    ensure
        (*q) <= *p
    proof
        (*q).is_infimum(q)
        (*p).is_infimum(p)
    end



all(p,q:{PO})
    require
        p.has_least
        q.has_least
        p <= q
    ensure
        least(q) <= least(p)
    proof
        least(q).is_least(q)
        least(p).is_least(p)
    end


{: Directed Sets and Continuous Functions
   ======================================
:}

is_directed (d:{PO}): ghost BOOLEAN
    -> d.has_some
       and
       all(a,b)  {a,b} <= d
                 ==>
                 some(x) x in d
                         and
                         x.is_upper_bound({a,b})


is_up_continuous (f:PO->PO2): ghost BOOLEAN
    -> all(set,sup)
           set <= f.domain
           ==>
           sup in f.domain
           ==>
           sup.is_supremum(set)
           ==>
           f(sup).is_supremum(set.image(f))


{:
all(a:PO, f:PO->PO)
    require
        f.is_closure_map
    proof
        f(a).is_fixpoint(f)

        all(x)
            require
                x.is_fixpoint(f)   -- 'is_fixpoint' is not inherited!!
                a <= x
            proof
                f(a) <= f(x)
                f(x) = x
            ensure
                f(a) <= x
            end
    ensure
        f(a).is_least({x: x.is_fixpoint(f) and a <= x})
    end
:}

G: ANY

immutable class predicate.PREDICATE[G]
inherit   ghost PARTIAL_ORDER
end
