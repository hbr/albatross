{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}

use
    predicate_logic
    partial_order
end


PO: PARTIAL_ORDER


above (p:PO?, a:PO): PO?
    -> {x: p(x) and a <= x}


is_closure_system (p:PO?):  ghost BOOLEAN
    -> (all(a) p.above(a) /= 0) and
       all(q) q <= p  ==> q /= 0 ==> (some(x) x.is_infimum(q)) and *q in p


is_closure_map(f:PO->PO): ghost BOOLEAN ->
    f.is_total and
    f.is_ascending and
    f.is_monotonic and
    f.is_idempotent



all(a:PO, p:PO?)
    require
        p.is_closure_system
    proof
        (some(x) x.is_infimum(p.above(a))) and * p.above(a) in p
    ensure
        some(x) x.is_infimum(p.above(a))
    end


all(a:PO, p:PO?)
    require
        p.is_closure_system
    proof
        (some(x) x.is_infimum(p.above(a))) and * p.above(a) in p
    ensure
        (* p.above(a)) in p
    end

all(a:PO, p:PO?)
    require
        p.is_closure_system
    proof
        (* p.above(a)).is_infimum(p.above(a))
        (* p.above(a)) in p
        (* p.above(a)).is_least(p.above(a))
    ensure
        some(x) x.is_least(p.above(a))
    end




closed (a:PO, p:PO?): ghost PO
    require
        p.is_closure_system
    ensure
        -> least(p.above(a))
    end



all(a:PO, p:PO?)
    require
        p.is_closure_system
    proof
        a in lower_bounds(p.above(a))
        least(p.above(a)).is_least(p.above(a))
    ensure
        a <= a.closed(p)
    end



all(a,b:PO, p:PO?)
    require
        p.is_closure_system
        a <= b
    proof
        least(p.above(a)) <= least(p.above(b))
    ensure
        a.closed(p) <= b.closed(p)
    end


all(a:PO, p:PO?)
    require
        p.is_closure_system
    ensure
        a.closed(p) <= a.closed(p).closed(p)
    end
