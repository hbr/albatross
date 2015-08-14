{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}

use
    boolean_logic
    predicate_logic
    tuple
end


case class
    NATURAL
create
    0
    successor (predecessor:NATURAL)
end

1: NATURAL = 0.successor
2: NATURAL = 1.successor
3: NATURAL = 2.successor
4: NATURAL = 3.successor


{: Successor
   ========= :}

all(a:NATURAL)
    require
        some(x) a = successor(x)
    proof
        all(x)
            require
                a = successor(x)
            proof
                successor(x) = a
                a in {a: a /= 0}
            ensure
                a /= 0
            end
    ensure
        a /= 0
    end

all(a:NATURAL)
    require
        a /= 0
    proof
        0 in {a: a /= 0 ==> some(x) a = successor(x)}
        all(a) proof
                   successor(a) = successor(a)
               ensure
                   some(x) successor(a) = successor(x)
               end
        a in {a: a /= 0 ==> some(x) a = successor(x)}
    ensure
        some(x) a = successor(x)
    end

predecessor (n:NATURAL): NATURAL
    require
        n as _.successor
    ensure
        Result = inspect n
                 case    m.successor then m
                 end
    end





{: Addition
   ======== :}


(+) (a,b: NATURAL): NATURAL
    -> inspect b
       case 0           then a
       case n.successor then (a + n).successor
       end


all(a,b:NATURAL)
    ensure
        a + 0 = a
        a + b.successor = (a + b).successor
        a + 1 = a.successor
    end



all(a,b,c:NATURAL)
    proof
        0 in {n: a + b + n = a + (b + n)}
        c in {n: a + b + n = a + (b + n)}
    ensure
        a + b + c  =  a + (b + c)
    end


all(n:NATURAL)
    proof
        0 in {n:NATURAL: 0 + n = n}
        n in {n: 0 + n = n}
    ensure
        0 + n = n
    end


all(a,b:NATURAL) -- commutativity of successor
    proof
       0 in {n: a + n.successor = a.successor + n}
       b in {n: a + n.successor = a.successor + n}
    ensure
       a + b.successor = a.successor + b
    end


all(a,b:NATURAL)
        -- commutativity of addition
    proof
        proof  0 + a = a
        ensure 0 in {n: a + n = n + a} end

        all(n)
            require
                a + n = n + a
            proof
                a + n.successor   = (a + n).successor  -- def '+'
                (a + n).successor = (n + a).successor  -- induction hypothesis
                (n + a).successor = n + a.successor    -- def '+'
                n + a.successor   = n.successor + a    -- commutativity successor
            ensure
                a + n.successor = n.successor + a
            end
        b in {n: a + n = n + a}
    ensure
        a + b = b + a
    end



all(a,b,x:NATURAL)
    proof
        0 in {x: a + x = b + x ==> a = b}
        x in {x: a + x = b + x ==> a = b}
    ensure
        a + x = b + x ==> a = b
    end

all(a,b,x:NATURAL)
    require
        x + a = x + b
    proof
        proof  a + x = x + a
        ensure a + x = b + x end
    ensure
        a = b
    end

all(a,x:NATURAL)
    proof
        0 in {a: a = a.successor ==> false}
        a in {a: a = a.successor ==> false}
    ensure
        a = a.successor ==> false
    end

all(a,x:NATURAL)
    proof
        require a + x = a
        proof   x + a = a + x
                a + x = a
                a = 0 + a
        ensure  x + a = 0 + a end
    ensure
        a + x = a  ==>  x = 0
    end




{: Order structure
   =============== :}


(<=) (a,b:NATURAL): BOOLEAN
    -> inspect a, b
       case    0, _ then true
       case    _, 0 then false
       case    successor(a), successor(b) then a <= b
       end

(<)  (a,b:NATURAL): BOOLEAN -> a <= b and a /= b


all(a:NATURAL)
    proof
        0 in {a:NATURAL: a <= a}
        a in {a:NATURAL: a <= a}
    ensure
        a <= a
    end

all(a:NATURAL)
    proof
        0 in {a:NATURAL: a <= 0 ==> a = 0}
        a in {a: a <= 0 ==> a = 0}
    ensure
        a <= 0 ==> a = 0
    end

all(a:NATURAL)
    ensure
       successor(a) <= 0 ==> false
    end

{: Difference
   ========== :}




all(a,b:NATURAL)
    proof
        proof
            require
                b <= 0
                (0:NATURAL,b) as (0,successor(_))
            proof
                b = 0
                0 in {b: (0:NATURAL,b) as (0,successor(_))}
            ensure
                false
            end
        ensure
            0 in {a: b <= a ==> not ((a,b) as (0,successor(_)))}
        end

        all(a)
            ensure
                not ((successor(a),b) as (0,successor(_)))
            end

        a in {a: b <= a ==> not ((a,b) as (0,successor(_)))}
    ensure
        b <= a  ==>  not ((a,b) as (0,successor(_)))
    end


all(a,b,n,m:NATURAL)
    require
        b <= a
        (a,b) = (successor(n),successor(m))
    proof
        (successor(n),successor(m)) in {x,y: y <= x}
    ensure
        m <= n
    end


(-)  (a,b:NATURAL): NATURAL
    require b <= a
    ensure  Result = inspect a,b
                     case    _, 0 then a
                     case    successor(a), successor(b) then a - b
                     end
    end



{: Multiplication
   ============== :}

(*) (a,b:NATURAL): NATURAL
    -> inspect a
       case 0           then 0
       case n.successor then n*b + b
       end


all(a,b:NATURAL)
    ensure
        0 * b = 0
        a.successor * b = a*b + b
    end



all(a:NATURAL)
    proof
       0 in {n:NATURAL: n * 0 = 0}
       a in {n: n * 0 = 0}
    ensure
       a * 0 = 0
    end

all(a:NATURAL)
    proof
        0 + a = a
    ensure
        1 * a = a
    end

all(a,b,c:NATURAL) -- distributivity
    proof
        all(a,b,c,d:NATURAL)  -- lemma
            {: Note: This lemma is needed as long as the special treatment of
                     commutative and associative operators is not implemented :}
            proof
               a + b + (c + d)   = a + (b + (c + d))

               proof  b + (c + d) = b + c + d
               ensure a + (b + (c + d)) = a + (b + c + d) end

               proof  b + c = c + b
               ensure a + (b + c + d) = a + (c + b + d) end

               proof  c + b + d = c + (b + d)
               ensure a + (c + b + d) = a + (c + (b + d)) end
            ensure
               a + b + (c + d) = a + c + (b + d)
            end

        0 in {n: n * (b + c) = n*b + n*c}

        all(a)
            require
                a * (b + c) = a*b + a*c
            proof
                a.successor * (b + c) = a*(b + c) + (b + c)
                a*(b + c) + (b + c)   = a*b + a*c + (b + c)
                a*b + a*c + (b + c)   = a*b + b + (a*c + c)
                a*b + b + (a*c + c)   = a.successor*b + a.successor*c
            ensure
                a.successor * (b + c) = a.successor*b + a.successor*c
            end

        a in {n: n * (b + c) = n*b + n*c}
    ensure
        a * (b + c) = a*b + a*c
    end


{: Exponentiation
   ============== :}

(^) (a,b:NATURAL): NATURAL
    -> inspect b
       case 0           then 1
       case n.successor then a^n * a
       end

all(a,b:NATURAL)
    ensure
        a^0 = 1
        a ^ b.successor = a^b * a
    end



all ensure
    1 + 1 = 2
    1 + 2 = 3
    1 * 2 = 2
    2 * 2 = 4
    2 ^ 2 = 4
end
