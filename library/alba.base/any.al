use boolean end

deferred class G:ANY end

(=)  (a,b:G): BOOLEAN    deferred end

(/=) (a,b:G): BOOLEAN -> not (a = b)

all(a:G) ensure a = a deferred end


all(a:G)
    require
        a /= a
    ensure
        false
    end

all(a,b:G)
    ensure
        a = b or a /= b
    if a = b
    else
    end



class
    BOOLEAN
inherit
    ANY
end
