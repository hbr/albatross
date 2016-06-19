use
    boolean_logic
    partial_order
end


deferred class LINEAR_ORDER end

LO: LINEAR_ORDER

(=)  (a,b:LO): BOOLEAN    deferred end
(<=) (a,b:LO): BOOLEAN    deferred end

all(a,b,c:LO)
    ensure
        a = a
        a <= b or b <= a
        a <= b  ==>  b <= a  ==>  a = b
        a <= b  ==>  b <= c  ==>  a <= c
    deferred
    end


all(a:LO)
    ensure
        a <= a
    proof
        a <= a or a <= a
    end


deferred class LINEAR_ORDER
inherit        PARTIAL_ORDER end


all(a,b:LO)
    require
        not (a <= b)
    ensure
        b < a
    proof
        a <= b  or  b <= a

        require  b = a
        ensure   false
        proof    a in {x: x <= b}
        end
    end

all(a,b:LO)
    require
        not (a < b)
    ensure
        b <= a
    proof
        require  not (b <= a)
        ensure   false
        proof    a < b
        end
    end



all(a,b:LO)
    require
        a /= b
    ensure
        a < b  or  b < a
    proof
        require
            not (a < b)
        ensure
            b < a
        end
    end



{: Maximum and Minimum
   =================== :}

min (a,b:LO): LO  -> if a <= b then a else b
max (a,b:LO): LO  -> if a <= b then b else a


all(a,b:LO)
    ensure
        min(a,b).is_least({a,b})
    proof
        ensure min(a,b) in {a,b}
        proof  a <= b  or  not (a <= b)
               a <= b  ==> min(a,b) in {a,b}
        end

        all(x) require x in {a,b}
               ensure  min(a,b) <= x
               proof   a <= b  or  not (a <= b)
                       a <= b        ==> min(a,b) <= x
                       not (a <= b)  ==> min(a,b) <= x
               end
    end




all(a,b:LO)
    ensure
        max(a,b).is_greatest({a,b})
    proof
        ensure max(a,b) in {a,b}
        proof  a <= b  or  not (a <= b)
               a <= b  ==> max(a,b) in {a,b}
        end

        all(x)
            require
                x in {a,b}
            ensure
                x <= max(a,b)
            proof
                x = a  or x = b
                a <= b or not (a <= b)
                require
                    x = a
                ensure
                    x <= max(a,b)
                proof
                    a <= b       ==> x <= max(a,b)
                    not (a <= b) ==> x <= max(a,b)
                end

                require
                    x = b
                ensure
                    x <= max(a,b)
                proof
                    a <= b  ==>  x <= max(a,b)
                    not (a <= b) ==> x <= max(a,b)
                end
            end
    end
