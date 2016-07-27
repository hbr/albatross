use predicate end

A: ANY
B: ANY

class
    TUPLE[A,B]
create
    tuple(first:A, second:B)
end



first (t:(A,B)): A
    -> inspect t
       case (a,_) then a

second (t:(A,B)): B
    -> inspect t
       case (_,b) then b
