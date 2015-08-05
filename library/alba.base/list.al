{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}

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


all(a:[G], p:[G]?)
        -- Induction
    require
        p([])
        all(a,x) p(a) ==> p(x^a)
    ensure
        p(a)
    end

all(x:G,a:[G])
        -- Inversion
    ensure
       []  = x^a  ==>  false
       x^a = []   ==>  false
    end




head (a:[G]): G
    require
        a as x ^ t
    ensure
        Result = inspect a
                 case h ^ _ then h
                 end
    end



tail (a:[G]): [G]
    require
        a as x ^ t
    ensure
        Result = inspect a
                 case _ ^ t then t
                 end
    end


all(x,y:G, a,b:[G])
        -- Injection
    require
        x^a = y^b
    proof
        y^b in {l: l as _^_ and l.head = x and l.tail = a}
    ensure
        x = y
        a = b
    end




size (a:[G]): NATURAL
    -> inspect a
       case []  then 0
       case h^t then t.size.successor
       end




{: List Content
   ============ :}


(in) (x:G, a:[G]): BOOLEAN
    -> inspect a
       case []  then false
       case h^t then x = h  or  x in t
       end

elements (l:[G]): G? -> {x: x in l}


all_in (a:[G], p:G?): BOOLEAN
    -> inspect a
       case []  then true
       case h^t then h in p and t.all_in(p)
       end

all(x:G, a:[G], p:G?)
    require
        x in a
        a.all_in(p)
    proof
        []  in {a: x in a ==> a.all_in(p) ==> x in p}

        all(y:G, a:[G])
            require
                x in a  ==> a.all_in(p) ==> x in p
                x in y^a
                (y^a).all_in(p)
            proof
                y in p
                a.all_in(p)
                x = y or x in a
                require x = y
                proof   y = x
                ensure  x in p end
            ensure
                x in p
            end

        a in {a: x in a ==> a.all_in(p) ==> x in p}
    ensure
        x in p
    end



all(a:[G], p,q:G?)
    require
        a.all_in(p)
        p <= q
    proof
        []  in {a: a.all_in(p) ==> p <= q ==> a.all_in(q)}

        a in {a: a.all_in(p) ==> p <= q ==> a.all_in(q)}
    ensure
        a.all_in(q)
    end


all_in (a,b:[G]): BOOLEAN
    -> a.all_in(elements(b))


all(p:G?, a,b:[G])
    require
        a.all_in(b)
        b.all_in(p)
    proof
        a.elements <= b.elements
    ensure
        a.all_in(p)
    end



all(a,b:[G])
    proof
        all(x:G, a:[G])
            require
                a.elements <= b.elements ==> a.all_in(b)
                (x^a).elements <= b.elements
            proof
                a.elements <= b.elements
            ensure
                (x^a).all_in(b)
            end

        [] in {a: a.elements <= b.elements  ==> a.all_in(b)}
        a  in {a: a.elements <= b.elements  ==> a.all_in(b)}
    ensure
        a.elements <= b.elements  ==> a.all_in(b)
    end


all(a,b:[G])
    proof
        all(x,y:G, a:[G])
            require
                a.all_in(b) ==> a.elements <= b.elements
                (x^a).all_in(b)
                y in (x^a).elements
            proof
                y = x or y in a

                require y = x
                proof   x = y; x in b; y in {z: z in b}
                ensure  y in b end

                require y in a
                proof   y in a.elements
                        a.all_in(b)
                        y in b.elements
                ensure  y in b end

                y in b
            ensure
                y in b.elements
            end
        [] in {a: a.all_in(b) ==> a.elements <= b.elements}
        a  in {a: a.all_in(b) ==> a.elements <= b.elements}
    ensure
        a.all_in(b) ==> a.elements <= b.elements
    end


same_elements (a,b:[G]): BOOLEAN
    -> a.all_in(b) and b.all_in(a)

all(a,b,c:[G])
    ensure
        same_elements(a,a)
        same_elements(a,b) ==> same_elements(b,a)
        same_elements(a,b) ==> same_elements(b,c) ==> same_elements(a,c)
    end



{: Permutation
   =========== :}

permutation (a,b:[G]): ghost BOOLEAN
    -> a.size = b.size and same_elements(a,b)

all(a,b,c:[G])
    ensure
        permutation(a,a)
        permutation(a,b) ==> permutation(b,a)
        permutation(a,b) ==> permutation(b,c) ==> permutation(a,c)
    end

all(x,y:G, a:[G])
    proof
        all(x,y) (x^y^a).all_in(y^x^a)
    ensure
        permutation(x^y^a, y^x^a)
    end

all(x:G, a,b:[G])
    require
        permutation(a,b)
    proof
        (x^a).all_in({z: z in x^b})
        (x^b).all_in({z: z in x^a})
    ensure
        permutation(x^a, x^b)
    end



{: Prefix
   ====== :}
is_prefix (a,b:[G]): BOOLEAN
    -> inspect a, b
       case [] , _   then true
       case _  , []  then false
       case x^a, y^b then x = y and a.is_prefix(b)
       end





{: List concatenation
   ================== :}


(+) (a,b: [G]): [G]
    -> inspect a
       case []    then b
       case h ^ t then h ^ (t + b)
       end

all(a:[G])
    proof
        []  in {a: a + []  = a}
        a   in {a: a + []  = a}
    ensure
        a + []  = a
    end


all(a,b,c:[G])
    proof
        []  in {a: a + b + c = a + (b + c)}
        a   in {a: a + b + c = a + (b + c)}
    ensure
        a + b + c = a + (b + c)
    end





{: List reversal
   ============= :}

(-) (a:[G]): [G]
    -> inspect a
       case []    then []
       case h ^ t then -t + h ^ []
       end

all(a,b:[G])
    proof
        proof   (-b) + []  = -b
                (-([] + b)) = -b + -[]
        ensure  [] in {a: -(a + b) = -b + -a} end

        all(x,a)
            require
                -(a + b) = -b + -a
            proof
                (- (x^a + b))       =   -(a + b) + [x]    -- def '+', '-'

                (- (a + b)) + [x]   =   -b + -a + [x]     -- ind hypo

                (-b) + -a + [x]     =   -b + (-a + [x])   -- assoc '+'

                (-b) + (-a + [x] )  =   -b + - x^a        -- def '-'
            ensure
                -(x^a + b) = -b + -x^a
            end

        a in {a: -(a + b) = -b + -a}
    ensure
       -(a + b) = -b + -a
    end


all(a:[G])
    proof
        []  in {a: -(-a) = a}

        all(x:G,a:[G])
            require
                -(-a) = a
            proof
                -(-x^a) = - (-a + [x])

                ;- (-a + [x]) = -[x] + -(-a)

                proof  -[x] = [x]
                ensure -[x] + (-(-a)) = [x] + a end

                [x] + a = x^a
            ensure
                -(-x^a) = x^a
            end
        a  in {a: -(-a) = a}
    ensure
        -(-a) = a
    end




{: List folding
   ============ :}

folded (f:(G,H)->H, b:H, l:[G]): H
    -> inspect l
       case []  then b
       case h^t then f.folded(f(h,b),t)
       end

all(a,b:[G])
    proof
        []  in {a: all(b:[G]) -a + b = (^).folded(b,a)}

        all(x,a)
            require
                all(b:[G]) -a + b = (^).folded(b,a)
            proof
                all(b:[G]) -a + b = (^).folded(b,a)

                all(b:[G])
                proof
                    (^).folded(b,x^a) = (^).folded(x^b,a)

                    (^).folded(x^b,a) = -a + (x^b)

                    (-a) + (x^b)      = -a + ([x] + b)

                    (-a) + ([x] + b)  = -a + [x] + b

                    (-a) + [x] + b    = -x^a + b
                ensure
                    -x^a + b = (^).folded(b,x^a)
                end
            ensure
                all(b:[G]) -x^a + b = (^).folded(b,x^a)
            end

        a in {a: all(b:[G]) -a + b = (^).folded(b,a)}
    ensure
        -a + b = (^).folded(b,a)
    end




all(a,b:[G])
    proof
        proof  -(-a) = a
        ensure a + b = -(-a) + b end

        (-(-a)) + b = (^).folded(b,-a)
    ensure
        a + b = (^).folded(b,-a)
    end
