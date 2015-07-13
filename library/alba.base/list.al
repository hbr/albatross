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
    (^) (head:G, tail:LIST[G])
end

head (a:LIST[G]): G
    require
        a as x ^ t
    ensure
        Result = inspect a
                 case h ^ _ then h
                 end
    end



tail (a:LIST[G]): LIST[G]
    require
        a as x ^ t
    ensure
        Result = inspect a
                 case _ ^ t then t
                 end
    end


(+) (a,b: LIST[G]): LIST[G]
    -> inspect a
       case nil   then b
       case h ^ t then h ^ (t + b)
       end

(-) (a:LIST[G]): LIST[G]
    -> inspect a
       case nil   then nil
       case h ^ t then -t + h ^ nil
       end


all(a:LIST[G], p:LIST[G]?)
    require
        p(nil)
        all(a,x) p(a) ==> p(x^a) 
    ensure
        p(a)
    end

all(x:G,a:LIST[G])
    ensure
       nil = x^a  ==>  false
       x^a = nil  ==>  false
    end




all(x,y:G, a,b:LIST[G])
    require
        x^a = y^b
    proof
        y^b in {l: l as _^_ and l.head = x and l.tail = a}
    ensure
        x = y
        a = b
    end


all(x:G, a,b:LIST[G])
    ensure
        nil + b = b
        x^a + b = x^(a + b)

        (-nil = nil)
        (-[x] = [x])
        (-x^a = -a + [x])
    end

all(a,b,c:LIST[G])
    proof
        nil in {a: a + b + c = a + (b + c)}
        a   in {a: a + b + c = a + (b + c)}
    ensure
        a + b + c = a + (b + c)
    end

all(a:LIST[G])
    proof
        nil in {a: a + nil = a}
        a   in {a: a + nil = a}
    ensure
        a + nil = a
    end


all(a,b:LIST[G])
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
