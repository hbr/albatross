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
5: NATURAL = 4.successor
6: NATURAL = 5.successor
7: NATURAL = 6.successor
8: NATURAL = 7.successor
9: NATURAL = 8.successor


{: Successor
   ========= :}

all(a:NATURAL)
    require
        some(x) a = successor(x)
    ensure
        a /= 0
    proof
        all(x)
            require
                a = successor(x)
            ensure
                a /= 0
            proof
                successor(x) = a
                a in {a: a /= 0}
            end
    end



all(a:NATURAL)
    require
        a /= 0
    ensure
        some(x) a = successor(x)
    proof
        ensure
            a /= 0 ==> some(x) a = successor(x)
        inspect a
        case successor(a) proof
            successor(a) = successor(a)
        end
    end



predecessor (n:NATURAL): NATURAL
    require
        n as _.successor
    ensure
        -> inspect n
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


all(a:NATURAL)
    ensure
        a + 0 = a
    end



all(a,b:NATURAL)
    ensure
        a + b.successor = (a + b).successor
    end



all(a:NATURAL)
    ensure
        a + 1 = a.successor
    end



all(a,b,c:NATURAL)
    ensure
        a + b + c  =  a + (b + c)
    inspect c
    end


all(n:NATURAL)
    ensure
        0 + n = n
    inspect
        n
    end


all(a,b:NATURAL) -- commutativity of successor
    ensure
        a + b.successor = a.successor + b
    inspect
        b
    end


all(a,b:NATURAL)
        -- commutativity of addition
    ensure
        a + b = b + a
    inspect b
    case b.successor proof
        a + b.successor   = (a + b).successor  -- def '+'
        (a + b).successor = (b + a).successor  -- ind hypo
        (b + a).successor = b + a.successor    -- def '+'
        b + a.successor   = b.successor + a    -- commutativity of successor
    end



all(a,b,x:NATURAL)
    ensure
        a + x = b + x ==> a = b
    inspect
        x
    end



all(a,b,x:NATURAL)
    require
        x + a = x + b
    ensure
        a = b
    proof
        ensure a + x = b + x
        proof  a + x = x + a
        end
    end


all(a:NATURAL)
    ensure
        a = a.successor ==> false
    inspect
        a
    end

all(a,x:NATURAL)
    ensure
        a + x = a  ==>  x = 0
    proof
        require a + x = a
        ensure  x + a = 0 + a
        proof   x + a = a + x
                a + x = a
                a = 0 + a
        end
    end


all(a,b:NATURAL)
    ensure
        a + b = 0  ==> a = 0
    inspect a
    case successor(a) proof
        require successor(a) + b = 0
        ensure  a.successor = 0
        proof   successor(a) + b  = a + b.successor
                a + b.successor   = (a + b).successor
                (a + b).successor = 0
                false
        end
    end




all(a,b:NATURAL)
    require
        a + b = 0
    ensure
        b = 0
    proof
        b + a = a + b
        b + a = 0
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
    ensure
        a <= a
    inspect a end


all(a:NATURAL)
    ensure
        a <= 0 ==> a = 0
    inspect a end



all(a:NATURAL)
    ensure
       successor(a) <= 0 ==> false
    end


all(a,b:NATURAL)
    require
        a <= b  ==> a < successor(b)
        successor(a) <= successor(b)
    ensure
        successor(a) < b.successor.successor
    proof
        a <= b
    end


all(a,b:NATURAL)
    ensure
        a <= b  ==>  a < b.successor
    proof
        ensure
            all(b) a <= b  ==>  a < b.successor
        inspect a
        case successor(a) proof
            all(b)
                ensure
                    a.successor <= b  ==>  a.successor < b.successor
                proof
                    ensure a.successor <= b  ==>  a.successor < b.successor
                    inspect b
                    end
                end
        end
    end


all(a,b:NATURAL)
    require
        a <= b
    ensure
        a < b + 1
    proof
        a < b.successor
    end


all(a,b:NATURAL)
    ensure
        a.successor <= b ==>  a < b
    inspect b end


all(a,b:NATURAL)
    require
        a + 1 <= b
    ensure
        a < b
    end



all(a,b:NATURAL)
    ensure
        a <= b ==> some(x) a + x = b
    proof
        ensure
            all(a) a <= b ==> some(x) a + x = b
        inspect b
        case 0 proof
            all(a:NATURAL)
                require
                    a <= 0
                ensure
                    some(x) a + x = 0
                proof
                    0 = a
                    a + 0 = 0
                end
        case successor(b) proof
            all(a)
            ensure
                a <= b.successor ==> some(x) a + x = b.successor
            proof
                ensure
                    a <= b.successor ==> some(x) a + x = b.successor
                inspect a
                case 0 proof
                    0 + b.successor = b.successor
                case a.successor proof
                    require a.successor <= b.successor
                    ensure some(x) a.successor + x = b.successor
                    proof  a <= b
                           all(x) require a + x = b
                                  ensure  some(x) a.successor + x = b.successor
                                  proof   a.successor + x   = a + x.successor
                                          a.successor + x   =  b.successor
                                  end
                    end
                end
            end
        end
    end



all(a,b:NATURAL)
    ensure
        (some(x) a + x = b) ==> a <= b
    proof
        ensure
            all(a) (some(x) a + x = b) ==> a <= b
        inspect b
        case 0 proof
            all(a:NATURAL)
            require  some(x) a + x = 0
            ensure   a <= 0
            proof    all(x) require a + x = 0
                            ensure  a <= 0
                            proof   0 = a
                                    a in {a: a <= 0}
                            end
            end
        case b.successor proof
            all(a) (some(x) a + x = b) ==> a <= b
            all(a)
            ensure
                (some(x) a + x = b.successor) ==> a <= b.successor
            proof
                ensure  (some(x) a + x = b.successor) ==> a <= b.successor
                inspect a
                case successor(a) proof
                    require some(x) a.successor + x = b.successor
                    ensure  a.successor <= b.successor
                    proof   all(x) require a.successor + x = b.successor
                                   ensure  a.successor <= b.successor
                                   proof   (a + x).successor = a + x .successor
                                           a + x.successor = a.successor + x
                                           (a + x).successor = b.successor
                                           a + x = b
                                           some(x) a + x = b
                                           a <= b
                                   end
                    end
                end
            end
            all(a) (some(x) a + x = b.successor) ==> a <= b.successor
        end
    end



all(a,b:NATURAL)
    require
        a <= b
        b <= a
    ensure
        a = b
    proof
        some(x) a + x = b
        some(y) b + y = a
        all(x)
            require
                a + x = b
            ensure
                a = b
            proof
                all(y)
                    require
                        b + y = a
                    ensure
                        a = b
                    proof
                        a + (x + y) = (a + x) + y
                        a + x + y = b + y

                        a + (x + y) = a

                        x + y = 0
                        x = 0
                        0 in {x: a + x = b}
                    end
            end
    end




all(a,b,c:NATURAL)
    require
        a <= b
        b <= c
    ensure
        a <= c
     proof
        all(x)
            require
                a + x = b
            ensure
                a <= c
            proof
                all(y)
                    require
                        b + y = c
                    ensure
                        a <= c
                    proof
                        a + (x + y) = (a + x) + y
                        a + x + y   = b + y

                        a + (x + y) = c
                    end
            end
    end





all(a:NATURAL)
    ensure
        a <= a.successor
    inspect a end



all(a:NATURAL)
    ensure
        a < a.successor
    end


all(a:NATURAL)
    ensure
        a < a + 1
    end



all(a,b:NATURAL)
    require
        a < b
    ensure
        a.successor <= b
    proof
        some(x) a + x = b
        all(x)
            require
                a + x = b
            ensure
                a.successor <= b
            proof
                require
                    x = 0
                ensure
                    false
                proof
                    0 = x
                    x in {x: a = a + x}
                    a = b
                end
                x /= 0
                some(y) x = y.successor
                all(y)
                    require
                        x = y.successor
                    ensure
                        a.successor <= b
                    proof
                        y.successor in {x: a + x = b}
                        a.successor + y = a + y.successor
                        a.successor + y = b
                    end
            end
    end


all(a,b:NATURAL)
    require
        a < b
    ensure
        a + 1 <= b
    end




all(a,b:NATURAL)
    require
        a < b + 1
    ensure
        a <= b
    end


all(a,b:NATURAL)
    ensure
        a <= b or b <= a
    inspect a
    case successor(a) proof
        ensure
            a.successor <= b or b <= a.successor
        if a <= b proof
            ensure
                a.successor <= b or b <= a.successor
            if a = b proof
                a <= a.successor
                b in {x: x <= a.successor}
                b <= a.successor
            else proof
                a < b
                a.successor <= b
            end
        orif b <= a
        end
    end


all(a,b:NATURAL)
    require
        not (a <= b)
    ensure
        b <= a
    proof
        a <= b or b <= a
    end



all(a,b:NATURAL)
    ensure
        a <= b or b < a
    proof
        a = b or a /= b
        require  a = b
        ensure   a <= b or b < a
        proof    b in {x: a <= x}
        end

        require  a /= b
        ensure   a <= b or b < a
        proof    a <= b or b <= a
                 a <= b ==> a <= b or b < a
                 require  b <= a
                 ensure   a <= b or b < a
                 proof    b /= a
                 end
        end
    end



all(a,b,n:NATURAL)
    require a <= b
    ensure  a + n <= b + n
    inspect n end



all(a,b,n:NATURAL)
    ensure  a + n <= b + n ==> a <= b
    inspect n end




{: Difference
   ========== :}




all(a,b:NATURAL)
    ensure
        b <= a  ==>  not ((a,b) as (0,successor(_)))
    inspect a
    case 0 proof
        require
            b <= 0
            (0:NATURAL,b) as (0,successor(_))
        ensure
            false
        proof
            b = 0
            0 in {b: (0:NATURAL,b) as (0,successor(_))}
        end
    end


all(a,b,n,m:NATURAL)
    require
        b <= a
        (a,b) = (successor(n),successor(m))
    ensure
        m <= n
    proof
        (successor(n),successor(m)) in {x,y: y <= x}
    end




(-)  (a,b:NATURAL): NATURAL
    require b <= a
    ensure  -> inspect a,b
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


all(a:NATURAL)
    ensure
        0 * a = 0
    end

all(a,b:NATURAL)
    ensure
        a.successor * b = a*b + b
    end



all(a:NATURAL)
    ensure
       a * 0 = 0
    inspect a end

all(a:NATURAL)
    ensure
        1 * a = a
    proof
        0 + a = a
    end


all(a,b,c:NATURAL) -- distributivity
    ensure
        a * (b + c) = a*b + a*c
    proof
        all(a,b,c,d:NATURAL)  -- lemma
            {: Note: This lemma is needed as long as the special treatment of
                     commutative and associative operators is not yet implemented :}
            ensure
               a + b + (c + d) = a + c + (b + d)
            proof
               a + b + (c + d)   = a + (b + (c + d))

               ensure a + (b + (c + d)) = a + (b + c + d)
               proof  b + (c + d) = b + c + d
               end

               ensure a + (b + c + d) = a + (c + b + d)
               proof  b + c = c + b
               end

               ensure a + (c + b + d) = a + (c + (b + d))
               proof  c + b + d = c + (b + d)
               end
            end

        ensure
            a * (b + c) = a*b + a*c
        inspect a
        case successor(a) proof
            a.successor * (b + c) = a*(b + c) + (b + c)
            a*(b + c) + (b + c)   = a*b + a*c + (b + c)
            a*b + a*c + (b + c)   = a*b + b + (a*c + c)
            a*b + b + (a*c + c)   = a.successor*b + a.successor*c
        end
    end


{: Exponentiation
   ============== :}

(^) (a,b:NATURAL): NATURAL
    -> inspect b
       case 0           then 1
       case n.successor then a^n * a
       end

all(a:NATURAL)
    ensure
        a^0 = 1
    end

all(a,b:NATURAL)
    ensure
        a ^ b.successor = a^b * a
    end



all ensure
    1 + 1 = 2
end

all ensure
    1 + 2 = 3
end

all ensure
    1 * 2 = 2
end

all ensure
    2 * 2 = 4
end

all ensure
    2 ^ 2 = 4
end
