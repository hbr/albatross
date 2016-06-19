use
    boolean_logic
    predicate_logic
    function
    tuple
    natural
end

G:ANY
H:ANY

case class
    LIST[G]
create
    []
    (^) (head:G, tail:[G])   -- [G] is a shorthand for LIST[G]
end


all(x:G,a:[G])
        -- Inversion
    ensure
       []  = x^a  ==>  false
    end

all(x:G,a:[G])
        -- Inversion
    ensure
       x^a = []   ==>  false
    end




head (a:[G]): G
    require
        a as x ^ t
    ensure
        -> inspect a
           case h ^ _ then h
    end



tail (a:[G]): [G]
    require
        a as x ^ t
    ensure
        -> inspect a
           case _ ^ t then t
    end


all(x,y:G, a,b:[G])
        -- Injection
    require
        x^a = y^b
    ensure
        x = y
    proof
        y^b in {l: l as _^_ and l.head = x and l.tail = a}
    end


all(x,y:G, a,b:[G])
        -- Injection
    require
        x^a = y^b
    ensure
        x = y
    end




size (a:[G]): NATURAL
    -> inspect a
       case []  then 0
       case h^t then t.size.successor




{: List Content
   ============ :}


(in) (x:G, a:[G]): BOOLEAN
    -> inspect a
       case []  then false
       case h^t then x = h  or  x in t

elements (l:[G]): G? -> {x: x in l}


all_in (a:[G], p:G?): BOOLEAN
    -> inspect a
       case []  then true
       case h^t then h in p and t.all_in(p)


all(x:G, a:[G], p:G?)
    require
        x in a
        a.all_in(p)
    ensure
        x in p
    proof
        ensure
            x in a ==> a.all_in(p) ==> x in p
        inspect a
        case y^a proof
            require x in y^a
                    (y^a).all_in(p)
            ensure  x in p
            proof   y in p
                    a.all_in(p)
                    x = y or x in a
                    require x = y
                    ensure  x in p
                    proof   y = x
                    end
            end
        end
    end


all(a:[G], p,q:G?)
    require
        a.all_in(p)
        p <= q
    ensure
        a.all_in(q)
    proof
        ensure a.all_in(p) ==> p <= q ==> a.all_in(q)
        inspect a end
    end


all_in (a,b:[G]): BOOLEAN
    -> a.all_in(elements(b))


all(p:G?, a,b:[G])
    require
        a.all_in(b)
        b.all_in(p)
    ensure
        a.all_in(p)
    proof
        a.elements <= b.elements
    end



all(a,b:[G])
    ensure
        a.elements <= b.elements  ==> a.all_in(b)
    inspect a
    case x^a proof
        require (x^a).elements <= b.elements
        ensure  (x^a).all_in(b)
        proof   a.elements <= b.elements
        end
    end


all(a,b:[G])
    ensure
        a.all_in(b) ==> a.elements <= b.elements
    proof
        all(x,y:G, a:[G])
            require
                a.all_in(b) ==> a.elements <= b.elements
                (x^a).all_in(b)
                y in (x^a).elements
            ensure
                y in b.elements
            proof
                y = x or y in a

                require y = x
                ensure  y in b
                proof   x = y; x in b; y in {z: z in b}
                end

                require y in a
                ensure  y in b
                proof   y in a.elements
                        a.all_in(b)
                        y in b.elements
                end

                y in b
            end
        [] in {a: a.all_in(b) ==> a.elements <= b.elements}
        a  in {a: a.all_in(b) ==> a.elements <= b.elements}
    end


same_elements (a,b:[G]): BOOLEAN
    -> a.all_in(b) and b.all_in(a)

all(a:[G])
    ensure
        same_elements(a,a)
    end


all(a,b:[G])
    ensure
        same_elements(a,b) ==> same_elements(b,a)
    end


all(a,b,c:[G])
    ensure
        same_elements(a,b) ==> same_elements(b,c) ==> same_elements(a,c)
    end



{: Permutation
   =========== :}

permutation (a,b:[G]): ghost BOOLEAN
    -> a.size = b.size and same_elements(a,b)

all(a:[G])
    ensure
        permutation(a,a)
    end

all(a,b:[G])
    ensure
        permutation(a,b) ==> permutation(b,a)
    end

all(a,b,c:[G])
    ensure
        permutation(a,b) ==> permutation(b,c) ==> permutation(a,c)
    end

all(x,y:G, a:[G])
    ensure
        permutation(x^y^a, y^x^a)
    proof
        all(x,y) (x^y^a).all_in(y^x^a)
    end

all(x:G, a,b:[G])
    require
        permutation(a,b)
    ensure
        permutation(x^a, x^b)
    proof
        (x^a).all_in({z: z in x^b})
        (x^b).all_in({z: z in x^a})
    end



{: Prefix
   ====== :}
is_prefix (a,b:[G]): BOOLEAN
    -> inspect a, b
       case [] , _   then true
       case _  , []  then false
       case x^a, y^b then x = y and a.is_prefix(b)





{: List concatenation
   ================== :}


(+) (a,b: [G]): [G]
    -> inspect a
       case []    then b
       case h ^ t then h ^ (t + b)

all(a:[G])
    ensure
        a + []  = a
    inspect a end


all(a,b,c:[G])
    ensure
        (a + b) + c = a + (b + c)
    inspect a end





{: List reversal
   ============= :}

(-) (a:[G]): [G]
    -> inspect a
       case []    then []
       case h ^ t then -t + h ^ []

all(a,b:[G])
    ensure
       -(a + b) = -b + -a
    inspect a
    case x^a proof
        (- (x^a + b))       =   -(a + b) + [x]    -- def '+', '-'
        (- (a + b)) + [x]   =   -b + -a + [x]     -- ind hypo
        (-b) + -a + [x]     =   -b + (-a + [x])   -- assoc '+'
        (-b) + (-a + [x] )  =   -b + - x^a        -- def '-'
    end


all(a:[G])
    ensure
        -(-a) = a
    inspect a
    case x^a proof
            -(-x^a) = - (-a + [x])

            ;- (-a + [x]) = -[x] + -(-a)

            ensure -[x] + -(-a) = [x] + a
            proof  -[x] = [x]
            end

            [x] + a = x^a
    end


all(x:G, a:[G])
    ensure
        x ^ (-a) = - (a + [x])
    proof
        - - a = a

        x ^ (-a)            = - - x ^ (-a)
    end





{: List folding
   ============ :}

folded (f:(G,H)->H, b:H, l:[G]): H
    require
        f.is_total
    ensure
        -> inspect l
           case []  then b
           case h^t then f.folded(f(h,b),t)
    end

all(a,b:[G])
    ensure
        -a + b = (^).folded(b,a)
    proof
        ensure
            all(b) -a + b = (^).folded(b,a)
        inspect a
        case x^a proof
            all(b) -a + b = (^).folded(b,a)

            all(b)
            ensure
                -x^a + b = (^).folded(b,x^a)
            proof
                (^).folded(b,x^a) = (^).folded(x^b,a)
                (^).folded(x^b,a) = -a + (x^b)
                (-a) + (x^b)      = -a + ([x] + b)
                (-a) + ([x] + b)  = -a + [x] + b
                (-a) + [x] + b    = -x^a + b
            end
        end
    end




all(a,b:[G])
    ensure
        a + b = (^).folded(b,-a)
    proof
        ensure a + b = -(-a) + b
        proof  -(-a) = a
        end

        (-(-a)) + b = (^).folded(b,-a)
    end
