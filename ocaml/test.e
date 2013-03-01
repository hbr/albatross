-- --------------------------------------------------------------------

deferred class
    ANY
end

= (a,b:CURRENT): BOOLEAN
   deferred
   end

all(a,b:CURRENT, e:BOOLEAN)
   deferred
   ensure
       reflexivity: a=a
       rewrite:     a=b => e => e[a:=b]
   end

-- --------------------------------------------------------------------

immutable class
    BOOLEAN
end

=> (a,b:BOOLEAN): BOOLEAN
    note built_in end

false: BOOLEAN
    note built_in end

=  (a,b:BOOLEAN): BOOLEAN
    note built_in end

all(a,b,e:BOOLEAN)
    note built_in ensure
        equal_reflexive:  a=a
        equal_rewrite:    a=b => e => e[a:=b]
        antisymmetric:    (a=>b) => (b=>a) => (a=b)
        classic:          ((a=>false)=>false) => a
    end

not (a:BOOLEAN): BOOLEAN
    ensure
        Result = (a=>false)
    end

and (a,b:BOOLEAN): BOOLEAN
    ensure
        Result = not (a => not b)
    end

or (a,b:BOOLEAN): BOOLEAN
    ensure
        Result = (not a => b)
    end



-- --------------------------------------------------------------------

immutable class
    PREDICATE[G]
end

in (a:G, p:G?): BOOLEAN
    note built_in end

all(a:G, exp:BOOLEAN)
    note
        built_in
    ensure
        in_1:  a in {x:exp} => exp[x:=a]
        in_2:  exp[x:=a]    => a in {x:exp}
    end

-- --------------------------------------------------------------------

-- module: any
all(a,b:CURRENT)
    require
        r1: a=b
    check
        c1: a=a               -- reflexivity
        c2: a in {x: x=a}     -- c1, in_2
        c3: all(p:CURRENT?)
                require
                    r2: a in p
                ensure
                    b in p    -- r1,r2,rewrite
                end
        c4: b in {x: x=a}     -- c2,c3
    ensure
        b=a                   -- c4,in_2
    end


-- --------------------------------------------------------------------

nat_val: NATURAL

func_assign(i:NATURAL)
    do
       nat_val := i
       a       := b
    ensure
       nat_val = i
    end

G: kernel.ANY   -- All classnames can be fully qualified

H: LIST[ARRAY[kernel.INTEGER],NATURAL]

J: ghost a.A -> ghost b.B

immutable class
    FUNCTION
end


some_event
    require a ensure b end

some_feature(a:A)
    require
        r
    ensure
        e
    end

some_proc! (a:A, tuple:[A,B]): RT
    ensure e end

some_func(a:A): ghost B
    ensure Result = exp end


feature{NONE}          -- a private feature block
    class A_PRIVATE_CLASS end

    a_private_function(a:A): B
        ensure
            Result = a
        end
end

G:ANY

case class
    LIST[G]
create
    nil
    :: (first:G, tail:CURRENT)
end


+ (a:LIST[G], e:G): LIST[G]
    ensure
        Result = inspect a
                 case nil  then e::nil
                 case f::t then f::(t+e)
                 end
    end

+ (a,b:LIST[G]): LIST[G]
   ensure
       Result = inspect a
                case nil  then b
                case f::t then f::(t+b)
                end
   end



deferred class
    ABSTRACT_ARRAY[G]
feature
    count: NATURAL
        deferred end
    [] (i:NATURAL): G
        require
             i < count
        deferred
        end
end

class
     BUFFER[G]
feature
     count: NATURAL
     capacity: NATURAL
     [] (i:NATURAL): G
         require
             i < count
         note
             built_in
         end
invariant
     count <= capacity
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
        some(x) x=5 => true
        all(a) require apre check acheck ensure apost end
        all(a,b) a => a and b
    local
        a,b := aexp,bexp
        -- fun(a) ensure Result = a*a end
    check
        require r local l1; l2:=exp check c ensure e end
        require r local l1 do proc ensure e end
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