include Stdlib.Array



let take (n:int) (arr:'a array): 'a array =
  assert (n <= length arr);
  sub arr 0 n


let remove_last (n: int) (arr: 'a array): 'a array =
  let len = length arr in
  assert (n <= len);
  take (len - n) arr


let put (i:int) (a:'a) (arr:'a array): 'a array =
  assert (i < length arr);
  let res = copy arr in
  set res i a;
  res

let push (a:'a) (arr:'a array): 'a array =
  let len = length arr in
  init
    (len + 1)
    (fun i ->
      if i < len then
        get arr i
      else
        a)
