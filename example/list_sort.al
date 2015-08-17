use
    alba.base.boolean_logic
    alba.base.predicate_logic
    alba.base.linear_order
    alba.base.list
end

L: LINEAR_ORDER


{: Lower Bound
   =========== :}

is_lower_bound (x:L, a:[L]): BOOLEAN
    -> a.all_in({y: x <= y})

all(x,y:L, a:[L])
        -- transitivity
    require
        x <= y
        y.is_lower_bound(a)
    proof
        {z: y <= z} <= {z: x <= z}
    ensure
        x.is_lower_bound(a)
    end
        

all(x:L, a,b:[L])
    require
        x.is_lower_bound(a)
        permutation(a,b)
    ensure
        x.is_lower_bound(b)
    end




{: Sorted Lists
   ============ :}

is_sorted (l:[L]): BOOLEAN
    -> inspect l
       case []    then true
       case [_]   then true
       case x^y^a then x <= y and (y^a).is_sorted
       end

all(x:L, a:[L])
        -- sorted 1
    proof
        all(y:L,a:[L])
            require
                (y^a).is_sorted ==> a.is_sorted
                (x^y^a).is_sorted
            ensure
                (y^a).is_sorted
            end
        []  in {a: (x^a).is_sorted ==> a.is_sorted}
        a   in {a: (x^a).is_sorted ==> a.is_sorted}
    ensure
        (x^a).is_sorted ==> a.is_sorted
    end


all(x:L, a:[L])
        -- sorted 2
    proof
        []  in {a: all(x) (x^a).is_sorted ==> x.is_lower_bound(a)}
        a   in {a: all(x) (x^a).is_sorted ==> x.is_lower_bound(a)}
    ensure
        (x^a).is_sorted ==> x.is_lower_bound(a)
    end


all(x:L, a:[L])
        -- sorted 3
    require
        x.is_lower_bound(a)
        a.is_sorted
    proof
        []  in {a: x.is_lower_bound(a)  ==>  a.is_sorted  ==> (x^a).is_sorted}
        a   in {a: x.is_lower_bound(a)  ==>  a.is_sorted  ==> (x^a).is_sorted}
    ensure
        (x^a).is_sorted
    end




{: Element Insertion
   ================= :}


into (x:L, a:[L]): [L]
    -> inspect a
       case []  then [x]
       case y^a then
           if x <= y then x^y^a else y ^ x.into(a) end
       end

all(x:L)
    proof
        x.into([]) = [x]
    ensure
        permutation ([x], x.into([]))
    end

all(x,y:L, a:[L])
    require
        permutation(x^a, x.into(a))
        x <= y
    proof
         x.into(y^a) = x^y^a
    ensure
        permutation(x^y^a, x.into(y^a))
    end


all(x,y:L, a:[L])
    require
        permutation(x^a, x.into(a))
        not (x <= y)
    proof
        permutation(x^y^a, y^x^a)        -- module list
        permutation(y^x^a, y^x.into(a))  -- ind hypo/list
        proof
            x.into(y^a) = y^x.into(a)
            y^x.into(a) in {l: permutation(l,x.into(y^a))}
        ensure
            permutation(y^x.into(a), x.into(y^a))
        end
    ensure
        permutation(x^y^a, x.into(y^a))
    end


all(x:L, a:[L])
    proof
        [] in {a: permutation (x^a, x.into(a))}

        all(y:L, a:[L])
            require
                permutation(x^a, x.into(a))
            proof
                x <= y or not (x <= y)

                x <= y       ==> permutation(x^y^a, x.into(y^a))
                not (x <= y) ==> permutation(x^y^a, x.into(y^a))
            ensure
                permutation(x^y^a, x.into(y^a))
            end

        a in {a: permutation (x^a, x.into(a))}
    ensure
        permutation (x^a, x.into(a))
    end


all(x:L, a:[L])
    proof
        []  in {a: a.is_sorted ==> x.into(a).is_sorted}

        all(x,y:L, a:[L])
            require
                a.is_sorted ==> x.into(a).is_sorted
                (y^a).is_sorted
            proof
                x <= y or not (x <= y)

                require x <= y
                ensure  x.into(y^a).is_sorted end

                require not (x <= y)
                proof   y.is_lower_bound(x^a)
                        permutation(x^a, x.into(a))
                        (y^x.into(a)).is_sorted
                ensure  x.into(y^a).is_sorted end                
            ensure
                x.into(y^a).is_sorted
            end
            
        a in {a: a.is_sorted ==> x.into(a).is_sorted}
    ensure
        a.is_sorted ==> x.into(a).is_sorted
    end



{: Insertion Sort
   ============= :}

sorted (a:[L]): [L]
    -> inspect a
       case []  then [] 
       case h^t then h.into(t.sorted)
       end


all(a:[L])
    proof
        [] in {a: permutation(a, a.sorted)}
        all(x:L, a:[L])
            require
                permutation(a, a.sorted)
            proof
                permutation(x^a, x^a.sorted)
                permutation(x^a.sorted, x.into(a.sorted))
                proof  x.into(a.sorted) = (x^a).sorted
                ensure permutation(x.into(a.sorted), (x^a).sorted) end
            ensure
                permutation(x^a, (x^a).sorted)
            end
        a in {a: permutation(a, a.sorted)}
    ensure
        permutation(a, a.sorted)
    end

all(a:[L])
    proof
        [] in {a: a.sorted.is_sorted}

        all(x:L,a:[L])
            require
                a.sorted.is_sorted
            proof
                x.into(a.sorted).is_sorted
            ensure
                (x^a).sorted.is_sorted
            end
        
        a in {a: a.sorted.is_sorted}
    ensure
        a.sorted.is_sorted
    end

