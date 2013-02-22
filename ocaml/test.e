-- This is a comment


class
    ANY
end

case class LIST end

immutable class BOOLEAN end


G: kernel.ANY   -- All classnames can be fully qualified

H: LIST[ARRAY[kernel.INTEGER],NATURAL]

J: a.A -> b.B

immutable class
    FUNCTION
end



all(a:A) ensure [a,b] end

all(a,b,c,d) deferred ensure (a+b)=[x,y] and not b end

all(a,b,c,d:A, e,f:E, g,h,i)
    require 
        a[i]=5; r1; r2
        a+f(i) = ff(k)(l)+b
        (i)
        [j]
        a<b=c<=d
        (<=) (a,b)
        if c1 then e11;e12;e13 elseif c2 then e2 else e3 end
        if c then e end
        inspect list case nil then nilexp case f::t then oexp end
    check
        x -> a+b*c :T :U, a, b
        a+b = c
        a and b = c
        {a,b,c} = x
        {x: f(x)=z} = 0
        x := 5+3*7
        exp[e:=i+j]
    ensure
        tag1: e1; tag2: e2
        tag3: p||q
        tag4: a|b
    end