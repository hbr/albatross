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
    ensure
        r.domain  = r.range
    proof
       all(x) require x in r.domain
              ensure  x in r.range
              proof   some(y) r(x,y)
                      all(y) require r(x,y)
                             ensure  x in r.range
                             proof   r(x,x)
                                     some(y) r(y,x)  end
              end

        all(y) require y in r.range
               ensure  y in r.domain
               proof   some(x) r(x,y)
                       all(x)  require r(x,y)
                               ensure  y in r.domain
                               proof   r(y,y)
                                       some(x) r(y,x)
                               end
               end
        r.domain = r.range
    end


all(r:(A,A)?)
    require
        r in is_reflexive
    ensure
        r.carrier = r.domain
    proof
        r.domain = r.range
        r.domain + r.range = r.domain
    end

all(r:(A,A)?)
    require
        r in is_reflexive
    ensure
        r.carrier = r.range
    proof
        r.domain = r.range
        all(a)
            require
                a in r.carrier
            ensure
                a in r.range
            if a in r.domain orif a in r.range
            end
    end





to_reflexive (p:A?): (A,A)?
    -> {x,y: x=y and p(x)}

all(p:A?)
    ensure
        inverse(p.to_reflexive) = p.to_reflexive
    end

all(p:A?)
    ensure
        domain(p.to_reflexive) = p
    proof
        all(x) require x in p
               ensure  x in domain(p.to_reflexive)
               proof   (p.to_reflexive)(x,x) end

        all(x) require x in domain(p.to_reflexive)
               ensure  x in p
               proof   some(y) (p.to_reflexive)(x,y)
                       all(y)  require (p.to_reflexive)(x,y)
                               ensure  x in p end
               end
    end


all(p:A?)
    ensure
        range(p.to_reflexive) = p
    proof
        p.to_reflexive.inverse = p.to_reflexive

        range(p.to_reflexive) = domain(p.to_reflexive.inverse)
    end

all(p:A?)
    ensure
        carrier(p.to_reflexive) = p
    proof
        domain(p.to_reflexive) = p
        range (p.to_reflexive) = p
    end



reflexive (r:(A,A)?): ghost (A,A)?
    -> {(s): all(a,b) r(a,b) ==> s(a,b),
             all(a,b) r(a,b) ==> s(a,a),
             all(a,b) r(a,b) ==> s(b,b)}


all(a,b:A, r:(A,A)?)
    ensure
        (r.reflexive)(a,b) ==> (r.reflexive)(a,a)
    proof
        all(a,b) require (r.reflexive)(a,b)
                 ensure  (r.reflexive)(a,a)
                 inspect s(a,b): r.reflexive
                 end
    end



all(a,b:A, r:(A,A)?)
    ensure
        (r.reflexive)(a,b) ==> (r.reflexive)(b,b)
    proof
        all(a,b) require (r.reflexive)(a,b)
                 ensure  (r.reflexive)(b,b)
                 inspect s(a,b): r.reflexive
                 end
    end



all(r:(A,A)?)
    ensure
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
    ensure
        (+r)(a,b) ==> (+r)(a,c)
    inspect s(b,c): +r
    case all(a,b,c) s(a,b) ==> r(b,c) ==> s(a,c) proof
        all(a) (+r)(a,b) ==> (+r)(a,c)
        all(a)
        require (+r)(a,b)
        ensure  (+r)(a,c) end
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
    ensure
        some(d) r(b,d) and s(c,d)
    proof
        some(d) r(b,d) and r(c,d)
        all(d) require r(b,d) and r(c,d)
               ensure  some(d) r(b,d) and s(c,d)
               proof   r(b,d) and s(c,d) end
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
    ensure
        some(d) r(b,d) and (r.reflexive)(c,d)
    proof
        ensure
            all(c) r(a,c) ==> some(d) r(b,d) and (r.reflexive)(c,d)
        inspect s(a,b): r.reflexive
        case all(a,b) r(a,b) ==> s(a,b) proof
            r <= r.reflexive
        case all(a,b) r(a,b) ==> s(a,a) proof
            all(c) require r(a,c)
                   ensure  some(d) r(a,d) and (r.reflexive)(c,d)
                   proof   r(a,c) and (r.reflexive)(c,c) end
        case all(a,b) r(a,b) ==> s(b,b) proof
            all(c) require r(b,c)
                   ensure  some(d) r(b,d) and (r.reflexive)(c,d)
                   proof   r(b,c) and (r.reflexive)(c,c) end
        end
    end



all(a,b,c:A, r:(A,A)?)
    require
        r in diamond
        (r.reflexive)(a,c)
    ensure
        (r.reflexive)(a,b)
        ==> some(d) (r.reflexive)(b,d) and (r.reflexive)(c,d)
    proof
        ensure
            all(b) (r.reflexive)(a,b)
                   ==> some(d) (r.reflexive)(b,d) and (r.reflexive)(c,d)
        inspect s(a,c): r.reflexive
        case all(a,c) r(a,c) ==> s(a,c) proof
            all(b)
            require (r.reflexive)(a,b)
            ensure  some(d) (r.reflexive)(b,d) and (r.reflexive)(c,d)
            proof
                some(d) r(b,d) and (r.reflexive)(c,d)
                all(d)
                    require r(b,d) and (r.reflexive)(c,d)
                    ensure
                        some(d) (r.reflexive)(b,d) and (r.reflexive)(c,d)
                    proof   (r.reflexive)(b,d) and (r.reflexive)(c,d)
                    end
            end
        case all(a,c) r(a,c) ==> s(a,a) proof
            all(b)
            require (r.reflexive)(a,b)
            ensure
                some(d) (r.reflexive)(b,d) and (r.reflexive)(a,d)
            proof
                some(d) r(b,d) and (r.reflexive)(c,d)
                all(d)
                require r(b,d) and (r.reflexive)(c,d)
                ensure
                    some(d) (r.reflexive)(b,d) and (r.reflexive)(a,d)
                proof
                    (r.reflexive)(b,b) and (r.reflexive)(a,b)
                end
            end
        case all(a,c) r(a,c) ==> s(c,c) proof
            all(b)
                require (r.reflexive)(c,b)
                ensure  some(d) (r.reflexive)(b,d) and (r.reflexive)(c,d)
                proof   (r.reflexive)(b,b) and (r.reflexive)(c,b)
                end
        end
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
    ensure
        r(a,c) ==> some(d) r(b,d) and (+r)(c,d)
    proof
        ensure
            all(c) r(a,c) ==> some(d) r(b,d) and (+r)(c,d)
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
            ensure  some(f) r(c,f) and (+r)(d,f)
            proof   some(e) r(b,e) and (+r)(d,e)
                    all(e) require r(b,e) and (+r)(d,e)
                           ensure some(f) r(c,f) and (+r)(d,f)
                           proof   r(b,c)
                                   some(f) r(c,f) and r(e,f)
                                   all(f)
                                   require r(c,f) and r(e,f)
                                   ensure  some(f) r(c,f) and (+r)(d,f)
                                   proof   r(c,f) and (+r)(d,f)
                                   end
                           end
            end
        end
    end


all(a,b,c:A, r:(A,A)?)
    require
        r in diamond
        (+r)(a,c)
    ensure
        (+r)(a,b) ==> some(d) (+r)(b,d) and (+r)(c,d)
    proof
        ensure
            all(b) (+r)(a,b) ==> some(d) (+r)(b,d) and (+r)(c,d)
        inspect s(a,c): +r
        case all(a,c) r(a,c) ==> s(a,c) proof
            all(b) require (+r)(a,b)
                   ensure  some(d) (+r)(b,d) and (+r)(c,d)
                   proof   r(a,c)
                           some(d) r(b,d) and (+r)(c,d)
                           all(d)
                           require r(b,d) and (+r)(c,d)
                           ensure  some(d) (+r)(b,d) and (+r)(c,d)
                           proof   (+r)(b,d) and (+r)(c,d)
                           end
                   end
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
            ensure  some(f) (+r)(b,f) and (+r)(e,f)
            proof   some(d) (+r)(b,d) and (+r)(c,d)
                    all(d) require (+r)(b,d) and (+r)(c,d)
                           ensure  some(f) (+r)(b,f) and (+r)(e,f)
                           proof
                               some(f) r(d,f) and (+r)(e,f)
                               all(f) require r(d,f) and (+r)(e,f)
                                      ensure  some(f) (+r)(b,f) and (+r)(e,f)
                                      proof   (+r)(b,f) and (+r)(e,f)
                                      end
                           end
            end
        end
    end

all(r:(A,A)?) ensure r in diamond ==> +r in diamond end




confluent: ghost (A,A)??
        -- The collection of all confluent relations, i.e. of all relations whose
        -- transitive closures have the (strong) diamond property.
    = {r: +r in diamond}
