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

all(a,b:CURRENT)
    require
        r1: a=b
    check
        c1: a=a                             -- reflexivity
        c2: a in {x: x=a}                   -- c1, in_1
        c3: all(p:CURRENT?)
                require
                    r2: a in p
                check
                    c4: a in p => b in p    -- r1,rewrite
                ensure
                    b in p    -- r2,c4
                end
        c5: a in {x: x=a} => b in {x: x=a}   -- c3,deduction
        c6: b in {x: x=a}                    -- c2,c5
    ensure
        b=a                                  -- c5,in_2
    end

