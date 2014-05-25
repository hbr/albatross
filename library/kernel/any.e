deferred class
    ANY
end

G: ANY

= (a,b:G): BOOLEAN
   deferred
   end

all(a:G) deferred ensure
    a = a
end

-- all(a,b,c:G)
--    deferred
--    ensure
--        a=a
--        a=b => b=a
--        a=b => b=c => a=c
--    end
