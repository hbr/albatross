{: Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation. :}

use
    predicate_logic
end

G:ANY

case class
    OPTION[G]
create
    none
    value(item:G)
end

item (o:OPTION[G]): G
    require
        o as value(v)
    ensure
        Result = (inspect o
                 case value(v) then v
                 end)
    end
