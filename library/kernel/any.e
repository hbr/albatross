feature
    deferred class
        ANY
    end

    G: ANY

    = (a,b:G): BOOLEAN
       deferred
       end

    all(a,b,c:G)
       deferred
       ensure
           reflexivity:  a=a
           symmetry:     a=b => b=a
           transitivity: a=b => b=c => a=c
       end
end
