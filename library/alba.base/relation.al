use
    predicate_logic
    tuple
end

A: ANY
B: ANY


all(r,s:{A,B})
    require
        all(a,b) r(a,b) ==> s(a,b)
    ensure
        r <= s
    assert
        all(t)
            ensure  r(t) ==> s(t)
            inspect t end
    end


{: Domain and range
   ================ :}

domain (r:{A,B}): ghost {A}         -> {a: some(b) r(a,b)}
range  (r:{A,B}): ghost {B}         -> {b: some(a) r(a,b)}



{: Domain and range restriction
   ============================ :}

(|) (p:{A}, r:{A,B}): {A,B}
    -> {x,y: x in p and r(x,y)}

(|) (r:{A,B}, q:{B}): {A,B}
    -> {x,y: r(x,y) and y in q}


{: Image and preimage
   ================== :}

[] (r:{A,B}, p:{A}): ghost {B}
    -> {b: some(a) a in p and r(a,b)}

image    (p:{A}, r:{A,B}): ghost {B} -> {b: some(a) a in p and r(a,b)}
preimage (p:{B}, r:{A,B}): ghost {A} -> {a: some(b) b in p and r(a,b)}





{: Inverse of a relation
   ===================== :}


inverse (r:{A,B}): {B,A}          -> {b,a: r(a,b)}


all(r:{A,B})
    ensure
        range(r)  = domain(inverse(r))
    end

all(r:{A,B})
    ensure
        domain(r) = range (inverse(r))
    end

all(r:{A,B})
    ensure
        range (inverse(r))  = domain(r)
    end

all(r:{A,B})
    ensure
        domain(inverse(r))  = range (r)
    end




{: Relations which are functions
   ============================= :}

is_function(r:{A,B}): ghost BOOLEAN
    -> all(x,y1,y2) r(x,y1) ==> r(x,y2) ==> y1 = y2



[] (r:{A,B}, x:A): ghost B
    require
        r.is_function
        x in r.domain
    ensure
        r(x,Result)
    end
