G: ANY

ITER: ABSTRACT_ITERATOR

deferred class
    ABSTRACT_SEQUENCE[G]
feature
    count: NATURAL
            -- Number of items in the sequence
        deferred
        end

    [] (i:NATURAL): G
            -- Item at position i.
        require
            i < count
        deferred
        end

    list: ghost LIST[G]
        ensure
            Result.count = count
            all(i) i<count => Result[i] = Current[i]
        end

    extend_rear(e:G)
        deferred
        ensure
            list = old (list+e)
        end

    extend_front(e:G)
        deferred
        ensure
            list = old (e::list)
        end

    remove_first
        require
            not is_empty
        deferred
        ensure
            list = old list.tail
        end
        
    remove_last
        require
            not is_empty
        deferred
        ensure
            list = old list.last_removed
        end

    iterator!: ITER
        deferred
        ensure
            Result.sequence = Current
            Result.prefix   = nil
            Result.suffix   = list
        end
end

deferred class
    ABSTRACT_ITERATOR
feature
    sequence: ghost CURRENT
    prefix:   ghost LIST[G]
    suffix:   ghost LIST[G]

    is_valid: ghost BOOLEAN
        ensure
            prefix + suffix = sequence.list
        end

     position: ghost NATURAL
        deferred
        end
end

feature
end