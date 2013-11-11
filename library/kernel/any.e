export
    deferred class
        ANY
    end


    = (a,b:CURRENT): BOOLEAN
       deferred
       end

    all(a,b,c:CURRENT)
       deferred
       ensure
           reflexivity:  a=a
           symmetry:     a=b => b=a
           transitivity: a=b => b=c => a=c
       end
end