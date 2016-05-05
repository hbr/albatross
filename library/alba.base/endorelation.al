{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}


use
    predicate_logic
    relation
end

A: ANY

{: Carrier
   ======= :}
carrier (r:(A,A)?): ghost A? -> domain(r) + range(r)





{: Reflexivity
   =========== :}


is_reflexive: ghost (A,A)??
    = {r: (all(x,y) r(x,y) ==> r(x,x)) and
          (all(x,y) r(x,y) ==> r(y,y))}

all(r:(A,A)?)
    require
        r in is_reflexive
    proof
       all(x) require x in r.domain
              proof   some(y) r(x,y)
                      all(y) require r(x,y)
                             proof   r(x,x)
                                     some(y) r(y,x)
                             ensure  x in r.range end
              ensure  x in r.range end

        all(y) require y in r.range
               proof   some(x) r(x,y)
                       all(x)  require r(x,y)
                               proof   r(y,y)
                                       some(x) r(y,x)
                               ensure  y in r.domain end
               ensure  y in r.domain end
        r.domain = r.range
        r.domain + r.range = r.domain
    ensure
        r.domain  = r.range
        r.carrier = r.domain
        r.carrier = r.range
    end




to_reflexive (p:A?): (A,A)?
    -> {x,y: x=y and p(x)}

all(p:A?)
    ensure
        inverse(p.to_reflexive) = p.to_reflexive
    end

all(p:A?)
    proof
        all(x) require x in p
               proof   (p.to_reflexive)(x,x)
               ensure  x in domain(p.to_reflexive) end

        all(x) require x in domain(p.to_reflexive)
               proof   some(y) (p.to_reflexive)(x,y)
                       all(y)  require (p.to_reflexive)(x,y)
                               ensure  x in p end
               ensure  x in p end
    ensure
        domain(p.to_reflexive) = p
    end


all(p:A?)
    proof
        p.to_reflexive.inverse = p.to_reflexive

        range(p.to_reflexive) = domain(p.to_reflexive.inverse)
    ensure
        range(p.to_reflexive) = p
    end

all(p:A?)
    proof
        domain(p.to_reflexive) = p
        range (p.to_reflexive) = p
    ensure
        carrier(p.to_reflexive) = p
    end



reflexive (r:(A,A)?): ghost (A,A)?
    -> {(s): all(a,b) r(a,b) ==> s(a,b),
             all(a,b) r(a,b) ==> s(a,a),
             all(a,b) r(a,b) ==> s(b,b)}


all(a,b:A, r:(A,A)?)
    proof
        all(a,b) require (r.reflexive)(a,b)
                 proof   inspect s(a,b): r.reflexive
                         ensure  (r.reflexive)(a,a) end

                         inspect s(a,b): r.reflexive
                         ensure  (r.reflexive)(b,b) end
                 ensure  (r.reflexive)(a,a)
                         (r.reflexive)(b,b) end
    ensure
        (r.reflexive)(a,b) ==> (r.reflexive)(a,a)
        (r.reflexive)(a,b) ==> (r.reflexive)(b,b)
        r.reflexive in is_reflexive
    end




{: Symmetry
   ======== :}

symmetric (r:(A,A)?): (A,A)?
    -> r + r.inverse





{: Transitivity
   ============ :}

is_transitive: ghost (A,A)??
        -- The collection of all transitive relations.
    = {r: all(a,b,c) r(a,b) ==> r(b,c) ==> r(a,c)}

(+) (r:(A,A)?): ghost (A,A)?
        -- The least transitive relation which contains 'r'.
    -> {(s): all(x,y)   r(x,y) ==> s(x,y),
             all(x,y,z) s(x,y) ==> r(y,z) ==> s(x,z)}


all(a,b,c:A, r:(A,A)?)
    require
        (+r)(b,c)
    proof
        inspect s(b,c): +r
        case all(a,b,c) s(a,b) ==> r(b,c) ==> s(a,c) proof
            all(a) (+r)(a,b) ==> (+r)(a,c)
            all(a)
            require (+r)(a,b)
            ensure  (+r)(a,c) end
        ensure  all(a) (+r)(a,b) ==> (+r)(a,c) end
    ensure
        (+r)(a,b) ==> (+r)(a,c)
    end

all(r:(A,A)?)
    ensure
        +r in is_transitive
    end


(*) (r:(A,A)?): ghost (A,A)?
        -- The least reflexive transitive relation which contains 'r'.
    -> + r.reflexive





{: Equivalence
   =========== :}

equivalence (r:(A,A)?): ghost (A,A)?
    -> + r.reflexive.symmetric





{: Confluence
   ========== :}

diamond: ghost (A,A)??
    = {r: all(a,b,c) r(a,b) ==> r(a,c) ==> some(d) r(b,d) and r(c,d)}


{:
In the following we prove that any relation transfers the diamond property to
its reflexive and transitive closures.

In order to prove that a closure 's' has the diamond property we have to prove

    s(a,b) ==> s(a,c) ==> some(d) s(b,d) and s(c,d)

Because of the two premises we can do two induction proofs and we usually have
to use two nested induction proofs to prove the desired property. In order to
simplify matters we use an intermediate lemma where 'r' is the original
relation and 's' is the corresponding closure:

    s(a,b) ==> r(b,c) ==> some(d) r(b,d) and s(c,d)

        a ---> c          --->  r
        .      .          ...>  s
        .      .
        v      v
        b ---> d

This requires one induction proof. In the second step we prove the desired
property with another induction proof.

All closures (reflexive and transitive) have a base rule of the form

    r(x,y) ==> s(x,y)

which states that the closure contains the original relation. This case
requires in both cases the same proof for the intermediate lemma. Therefore we
factor out this proof in another lemma.

:}



all(a,b,c:A, r,s:(A,A)?)
        -- Base case for both intermediate lemmas
    require
        r in diamond
        r <= s
        r(a,b)
        r(a,c)
    proof some(d) r(b,d) and r(c,d)
          all(d) require r(b,d) and r(c,d)
                 proof   r(b,d) and s(c,d)
                 ensure  some(d) r(b,d) and s(c,d) end
    ensure
        some(d) r(b,d) and s(c,d)
    end



{: Theorem: If 'r' is a diamond relation then its reflexive closure is a
            diamond as well.

   We use an intermediate lemma to prove the claim:

   Lemma: (r.reflexive)(a,b) ==> r(a,c) ==> some(d) r(b,d) and (r.reflexive)(d,b)

            a ---> c         --->  r
            .      .         ...>  r.reflexive
            .      .
            v      v
            b ---> d

:}

all(a,b,c:A, r:(A,A)?)
    require
        r in diamond
        (r.reflexive)(a,b)
        r(a,c)
    proof
        inspect s(a,b): r.reflexive
        case all(a,b) r(a,b) ==> s(a,b) proof
            r <= r.reflexive
        case all(a,b) r(a,b) ==> s(a,a) proof
            all(c) require r(a,c)
                   proof   r(a,c) and (r.reflexive)(c,c)
                   ensure  some(d) r(a,d) and (r.reflexive)(c,d) end
        case all(a,b) r(a,b) ==> s(b,b) proof
            all(c) require r(b,c)
                   proof   r(b,c) and (r.reflexive)(c,c)
                   ensure  some(d) r(b,d) and (r.reflexive)(c,d) end
        ensure
            all(c) r(a,c) ==> some(d) r(b,d) and (r.reflexive)(c,d)
        end
    ensure
        some(d) r(b,d) and (r.reflexive)(c,d)
    end


all(a,b,c:A, r:(A,A)?)
    require
        r in diamond
        (r.reflexive)(a,c)
    proof
        inspect s(a,c): r.reflexive
        case all(a,c) r(a,c) ==> s(a,c) proof
            all(b)
            require (r.reflexive)(a,b)
            proof
                some(d) r(b,d) and (r.reflexive)(c,d)
                all(d)
                    require r(b,d) and (r.reflexive)(c,d)
                    proof   (r.reflexive)(b,d) and (r.reflexive)(c,d)
                    ensure
                        some(d) (r.reflexive)(b,d) and (r.reflexive)(c,d)
                    end
            ensure  some(d) (r.reflexive)(b,d) and (r.reflexive)(c,d) end
        case all(a,c) r(a,c) ==> s(a,a) proof
            all(b)
            require (r.reflexive)(a,b)
            proof
                some(d) r(b,d) and (r.reflexive)(c,d)
                all(d)
                require r(b,d) and (r.reflexive)(c,d)
                proof
                    (r.reflexive)(b,b) and (r.reflexive)(a,b)
                ensure
                    some(d) (r.reflexive)(b,d) and (r.reflexive)(a,d)
                end
            ensure
                some(d) (r.reflexive)(b,d) and (r.reflexive)(a,d) end
        case all(a,c) r(a,c) ==> s(c,c) proof
            all(b)
                require (r.reflexive)(c,b)
                proof   (r.reflexive)(b,b) and (r.reflexive)(c,b)
                ensure  some(d) (r.reflexive)(b,d) and (r.reflexive)(c,d) end
        ensure
            all(b) (r.reflexive)(a,b)
                   ==> some(d) (r.reflexive)(b,d) and (r.reflexive)(c,d)
        end
    ensure
        (r.reflexive)(a,b)
        ==> some(d) (r.reflexive)(b,d) and (r.reflexive)(c,d)
    end


all(r:(A,A)?)
    ensure
        r in diamond  ==>  r.reflexive in diamond
    end

{: Theorem: If 'r' is a diamond relation then its transitive closure is a
            diamond as well.

   We use an intermediate lemma to prove the claim:

   Lemma: (+r)(a,b) ==> r(a,c) ==> some(d) r(b,d) and (+r)(d,b)

            a ---> c         --->  r
            .      .         ...>  +r
            .      .
            v      v
            b ---> d
:}


all(a,b,c:A, r:(A,A)?)
         -- Intermediate lemma for the transitive closure.
    require
        r in diamond
        (+r)(a,b)
    proof
        inspect
            s(a,b): +r
        case
            all(a,b) r(a,b) ==> s(a,b)
        proof
            r <= +r

        case
            all(a,b,c) s(a,b) ==> r(b,c) ==> s(a,c)
            {:      a ----> d           --->        r
                    .       .           ...>       +r
                    .       .
                    v       v
                    b ----> e
                    |       |
                    v       v
                    c ----> f
            :}
        proof
            all(d) r(a,d) ==> some(e) r(b,e) and (+r)(d,e)  -- ind. hypo
            all(d)
            require r(a,d)
            proof   some(e) r(b,e) and (+r)(d,e)
                    all(e) require r(b,e) and (+r)(d,e)
                           proof   r(b,c)
                                   some(f) r(c,f) and r(e,f)
                                   all(f)
                                   require r(c,f) and r(e,f)
                                   proof   r(c,f) and (+r)(d,f)
                                   ensure  some(f) r(c,f) and (+r)(d,f) end
                           ensure some(f) r(c,f) and (+r)(d,f) end
            ensure  some(f) r(c,f) and (+r)(d,f) end
        ensure
            all(c) r(a,c) ==> some(d) r(b,d) and (+r)(c,d)
        end
    ensure
        r(a,c) ==> some(d) r(b,d) and (+r)(c,d)
    end


all(a,b,c:A, r:(A,A)?)
    require
        r in diamond
        (+r)(a,c)
    proof
        inspect s(a,c): +r
        case all(a,c) r(a,c) ==> s(a,c) proof
            all(b) require (+r)(a,b)
                   proof   r(a,c)
                           some(d) r(b,d) and (+r)(c,d)
                           all(d)
                           require r(b,d) and (+r)(c,d)
                           proof   (+r)(b,d) and (+r)(c,d)
                           ensure  some(d) (+r)(b,d) and (+r)(c,d) end
                   ensure  some(d) (+r)(b,d) and (+r)(c,d) end
        case all(a,c,e) s(a,c) ==> r(c,e) ==> s(a,e) proof
            {:  a . . .> c ---> e           --->        r
                .        .      .           ...>       +r
                .        .      .
                v        v      v
                b . . .> d ---> f
            :}
            all(b) (+r)(a,b) ==> some(d) (+r)(b,d) and (+r)(c,d) -- ind. hypo
            all(b)
            require (+r)(a,b)
            proof   some(d) (+r)(b,d) and (+r)(c,d)
                    all(d) require (+r)(b,d) and (+r)(c,d)
                           proof
                               some(f) r(d,f) and (+r)(e,f)
                               all(f) require r(d,f) and (+r)(e,f)
                                      proof   (+r)(b,f) and (+r)(e,f)
                                      ensure  some(f) (+r)(b,f) and (+r)(e,f) end
                           ensure  some(f) (+r)(b,f) and (+r)(e,f) end
            ensure  some(f) (+r)(b,f) and (+r)(e,f) end
        ensure
            all(b) (+r)(a,b) ==> some(d) (+r)(b,d) and (+r)(c,d)
        end
    ensure
        (+r)(a,b) ==> some(d) (+r)(b,d) and (+r)(c,d)
    end

all(r:(A,A)?) ensure r in diamond ==> +r in diamond end




confluent: ghost (A,A)??
        -- The collection of all confluent relations, i.e. of all relations whose
        -- transitive closures have the (strong) diamond property.
    = {r: +r in diamond}
