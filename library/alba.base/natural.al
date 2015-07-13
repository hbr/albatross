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

predecessor (n:NATURAL): NATURAL
    require
        n as _.successor
    ensure
        Result = inspect n
                 case    m.successor then m
                 end
    end


(+) (a,b: NATURAL): NATURAL
    -> inspect b
       case 0           then a
       case n.successor then (a + n).successor
       end

(*) (a,b:NATURAL): NATURAL
    -> inspect a
       case 0           then 0
       case n.successor then n*b + b
       end


(^) (a,b:NATURAL): NATURAL
    -> inspect b
       case 0           then 1
       case n.successor then a^n * a
       end

(<=) (a,b:NATURAL): BOOLEAN
    -> inspect a, b
       case    0, _  then true
       case    _, 0  then false
       case    n.successor, m.successor then n <= m
       end




all(a,b:NATURAL)
    ensure
        a + 0 = a
        a + b.successor = (a + b).successor
        a + 1 = a.successor

        0 * b = 0
        a.successor * b = a*b + b

        a^0 = 1
        a ^ b.successor = a^b * a
    end



all ensure
    1 + 1 = 2
    1 + 2 = 3
    1 * 2 = 2
    2 * 2 = 4
    2 ^ 2 = 4
    1 <= 2
    2 <= 4
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


all(a,b:NATURAL)
        -- commutativity of addition
    proof
        all(a,b:NATURAL) -- lemma
            proof
               0 in {n: a + n.successor = a.successor + n}
               b in {n: a + n.successor = a.successor + n}
            ensure
               a + b.successor = a.successor + b
            end

        proof  0 + a = a
        ensure 0 in {n: a + n = n + a} end

        all(n)
            require
                n in {n: a + n = n + a}
            proof
                a + n.successor   = (a + n).successor  -- def '+'
                (a + n).successor = (n + a).successor  -- induction hypothesis
                (n + a).successor = n + a.successor    -- def '+'
                n + a.successor   = n.successor + a    -- lemma
            ensure
                n.successor in {n: a + n = n + a}
            end
    ensure
        a + b = b + a
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
                a in {n: n * (b + c) = n*b + n*c}
            proof
                a.successor * (b + c) = a*(b + c) + (b + c)
                a*(b + c) + (b + c)   = a*b + a*c + (b + c)
                a*b + a*c + (b + c)   = a*b + b + (a*c + c)
                a*b + b + (a*c + c)   = a.successor*b + a.successor*c
            ensure
                a.successor in {n: n * (b + c) = n*b + n*c}
            end
    ensure
        a * (b + c) = a*b + a*c
    end
