use boolean end


all(a:BOOLEAN)
    require
        false
    proof
        not a ==> false
    ensure
        a
    end

all(a,b:BOOLEAN)
    require
        not (a or b)
    ensure
        not a
        not b
    end


all(a,b:BOOLEAN)
    require
        not a
        not b
    ensure
        not (a or b)
    end

all(a,b:BOOLEAN)
    require
        not (a and b)
    proof
        not (not a or not b) ==> false
    ensure
        not a or not b
    end


all(a,b:BOOLEAN)
    require
        not a or not b
    proof
        not a  ==>  not (a and b)
        not b  ==>  not (a and b)
    ensure
        not (a and b)
    end


all(a:BOOLEAN)
    proof
        require
            not (a or not a)
        ensure
            false
        end
    ensure
        a or not a
    end


all(a:BOOLEAN)
    require
        a or a
    proof
        a ==> a
    ensure
        a
    end

all(a,b:BOOLEAN)
    require
        a or b
    proof
        a  ==>  b or a
        b  ==>  b or a
    ensure
        b or a
    end

all(a,b,c:BOOLEAN)
    require
        a or b or c
    proof
        require a or b
        proof   a  ==> a or (b or c)
        ensure  a or (b or c) end
    ensure
        a or (b or c)
    end

all(a,b,c:BOOLEAN)
    require
        a or (b or c)
    ensure
        a or b or c
    end

all(a,b:BOOLEAN)
    require
        not a ==> b
    proof
        a or not a
        a     ==> a or b
        not a ==> a or b
    ensure
        a or b
    end


all(a,b:BOOLEAN)
    require
        a or b
        not a
    proof
        a ==> b
    ensure
        b
    end