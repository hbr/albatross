open Container
open Term

type 'a t = {
    table: Term_table0.t;
    count: int;
    nbenv: int;
    data:  (int * 'a) IntMap.t
  }




let global = {table = Term_table0.empty;
              count = 0; nbenv = 0;
              data = IntMap.empty}

let local (nb:int) (t: 'a t): 'a t =
  {t with nbenv = t.nbenv+nb}


let count (t: 'a t): int = t.count

let count_environment (t: 'a t): int = t.nbenv

let data  (i:int) (t:'a t): int * 'a =
  assert (i < count t);
  IntMap.find i t.data


let term (idx:int) (table:'a t): term =
  (* The term associated with index 'idx' in the table represented by the
     root node 'tab'
   *)
  assert (idx < count table);
  let nargs,_ = data idx table in
  Term_table0.term idx nargs table.table





let unify (t:term) (nbt:int) (table:'a t)
    :  (int * int * 'a * Term_sub.t) list =
  (* Unify the term 't' which comes from an environment with 'nbt' bound
     variables with the terms in the table 'table'.

     The result is a list of tuples (nargs,idx,data,sub) where the unified
     term 'ut' has 'nargs' arguments, it has the index 'idx', it is associated
     with the data 'data' and applying the substitution 'sub' to 'ut' yields
     the term 't'.
   *)
  try
    let lst = Term_table0.unify t nbt table.table in
    let res =
      List.fold_left
        (fun res_lst (i,sub) ->
          let nargs,data = IntMap.find i table.data in
          (nargs,i,data,sub)::res_lst
        )
        []
        lst
    in
    res
  with Not_found ->
    raise Not_found








let add (t:term) (nargs:int) (dat:'a) (table:'a t): 'a t =
  (* Add the term 't' which has 'nargs' arguments to the table 'table' and
     associate with it the data 'dat'.
   *)
  let idx = count table
  in
  let table =
    {table with
     table = Term_table0.add t nargs table.nbenv idx table.table;
     count = table.count + 1;
     data  = IntMap.add idx (nargs,dat) table.data}
  in
  assert ((nargs,dat) = data ((count table)-1) table);
  table
