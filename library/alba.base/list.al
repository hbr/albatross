{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}

use
    predicate_logic
end

G:ANY

case class
    LIST[G]
create
    nil
    (^) (head:G, tail:[G])   -- [G] is a shorthand for LIST[G]
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


(+) (a,b: [G]): [G]
    -> inspect a
       case nil   then b
       case h ^ t then h ^ (t + b)
       end

(-) (a:[G]): [G]
    -> inspect a
       case nil   then nil
       case h ^ t then -t + h ^ nil
       end


all(a:[G], p:[G]?)
    require
        p(nil)
        all(a,x) p(a) ==> p(x^a) 
    ensure
        p(a)
    end

all(x:G,a:[G])
    ensure
       nil = x^a  ==>  false
       x^a = nil  ==>  false
    end




all(x,y:G, a,b:[G])
    require
        x^a = y^b
    proof
        y^b in {l: l as _^_ and l.head = x and l.tail = a}
    ensure
        x = y
        a = b
    end


all(x:G, a,b:[G])
    ensure
        nil + b = b
        x^a + b = x^(a + b)

        (-nil = nil)
        (-[x] = [x])
        (-x^a = -a + [x])
    end

all(a,b,c:[G])
    proof
        nil in {a: a + b + c = a + (b + c)}
        a   in {a: a + b + c = a + (b + c)}
    ensure
        a + b + c = a + (b + c)
    end

all(a:[G])
    proof
        nil in {a: a + nil = a}
        a   in {a: a + nil = a}
    ensure
        a + nil = a
    end


all(a,b:[G])
    proof
        proof   (-b) + nil = -b
                (-(nil + b)) = -b + -nil
        ensure  nil in {a: -(a + b) = -b + -a} end

        all(x,a)
            require
                a in {a: -(a + b) = -b + -a}
            proof
                (- (x^a + b))       =   -(a + b) + [x]    -- def '+', '-'

                (- (a + b)) + x^nil =   -b + -a + [x]     -- ind hypo

                (-b) + -a + x^nil   =   -b + (-a + [x])   -- assoc '+'

                (-b) + (-a + x^nil) =   -b + - x^a        -- def '-'
            ensure
                x^a in {a: -(a + b) = -b + -a}
            end
    ensure
       -(a + b) = -b + -a
    end
