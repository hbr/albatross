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
    ensure
        x.is_lower_bound(a)
    proof
        {z: y <= z} <= {z: x <= z}
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
    -> inspect
           l
       case [] then
           true
       case [_] then
           true
       case x^y^a then
           x <= y and (y^a).is_sorted

all(x:L, a:[L])
        -- sorted 1
    ensure (x^a).is_sorted ==> a.is_sorted
    inspect a end



all(x:L, a:[L])
        -- sorted 2
    ensure
        (x^a).is_sorted ==> x.is_lower_bound(a)
    proof
        ensure
            all(x) (x^a).is_sorted ==> x.is_lower_bound(a)
        inspect a end
    end



all(x:L, a:[L])
        -- sorted 3
    require
        x.is_lower_bound(a)
        a.is_sorted
    ensure
        (x^a).is_sorted
    proof
        ensure
            x.is_lower_bound(a)  ==>  a.is_sorted  ==> (x^a).is_sorted
        inspect a end
    end




{: Element Insertion
   ================= :}


into (x:L, a:[L]): [L]
    -> inspect
           a
       case []  then
           [x]
       case y^a then
           if x <= y then
               x^y^a
           else
               y ^ x.into(a)

all(x:L)
    ensure
        permutation ([x], x.into([]))
    proof
        x.into([]) = [x]
    end



all(x,y:L, a:[L])
    require
        permutation(x^a, x.into(a))
        x <= y
    ensure
        permutation(x^y^a, x.into(y^a))
    proof
         x.into(y^a) = x^y^a
    end


all(x,y:L, a:[L])
    require
        permutation(x^a, x.into(a))
        not (x <= y)
    ensure
        permutation(x^y^a, x.into(y^a))
    proof
        permutation(x^y^a, y^x^a)        -- module list
        permutation(y^x^a, y^x.into(a))  -- ind hypo/list
        ensure
            permutation(y^x.into(a), x.into(y^a))
        proof
            x.into(y^a) = y^x.into(a)
            y^x.into(a) in {l: permutation(l,x.into(y^a))}
        end
    end


all(x:L, a:[L])
    ensure
        permutation (x^a, x.into(a))
    proof
        all(y:L, a:[L])
            require
                permutation(x^a, x.into(a))
            ensure
                permutation(x^y^a, x.into(y^a))
            proof
                x <= y or not (x <= y)

                x <= y       ==> permutation(x^y^a, x.into(y^a))
                not (x <= y) ==> permutation(x^y^a, x.into(y^a))
            end


        ensure permutation (x^a, x.into(a))
        inspect a end
    end


all(x:L, a:[L])
    ensure
        a.is_sorted ==> x.into(a).is_sorted
    inspect
        a
    case y^a proof
        require
            (y^a).is_sorted
        ensure
            x.into(y^a).is_sorted
        proof
            ensure x.into(y^a).is_sorted
            if x <= y
            else proof y.is_lower_bound(x^a)
                       permutation(x^a, x.into(a))
                       (y^x.into(a)).is_sorted
            end
        end
    end



{: Insertion Sort
   ============= :}

sorted (a:[L]): [L]
    -> inspect a
       case []  then []
       case h^t then h.into(t.sorted)


all(a:[L])
    ensure
        permutation(a, a.sorted)
    inspect a
    case x^a proof
        permutation(x^a, x^a.sorted)
        permutation(x^a.sorted, x.into(a.sorted))

        ensure permutation(x.into(a.sorted), (x^a).sorted)
        proof  x.into(a.sorted) = (x^a).sorted
        end
    end

all(a:[L])
    ensure
        a.sorted.is_sorted
    inspect a
    case x^a proof
        x.into(a.sorted).is_sorted
    end
