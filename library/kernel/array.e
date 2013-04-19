class
    ARRAY[G]
create
    with_capacity(c:NATURAL)
            -- Create an array with the capacity to store `c' elements.
        note
            built_in
        ensure
            domain   = 0
            capacity = c
        end
feature
    capacity: ghost NATURAL
            -- The allocated capacity of the array.

    domain: ghost NATURAL?
            -- The set of positions of elements which have been initialized.

    [] (i:NATURAL): G
            -- Element at position `i'.
        require
            i in domain
        note
            built_in
        end
feature
    put(i:NATURAL, e:G)
            -- Update (or set) the element `e' at position `i'.
        require
            i < capacity
        note
            built_in
        ensure
            domain = old (domain + {i})
            Current[i] = e
        end
invariant
    domain <= {i: i<capacity}
end
