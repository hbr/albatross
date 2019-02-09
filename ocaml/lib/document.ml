type t =
  | Nil
  | Concat of t * t
  | Nest of int * t
  | Text of string
  | Line of string
  | Union of t * t

let empty = Nil

let (^) (a:t) (b:t): t = Concat(a,b)

let nest (i:int) (a:t): t = Nest(i,a)

let text (s:string): t = Text s

let space: t = Line " "

let cut: t   = Line ""

let optional (s:string): t = Line s

let rec flatten (d:t): t =
  (* replace line breaks by spaces, whole doc on one line *)
  match d with
  | Nil -> Nil
  | Concat (d1,d2) ->
     Concat (flatten d1, flatten d2)
  | Nest (i,d) ->
     flatten d (*Nest (i, flatten d)*)
  | Text s ->
     Text s
  | Line s ->
     Text s (* remove line breaks and replace it by the corresponding string,
               i.e. an empty string, a space or some other optional
               replacement text. *)
  | Union(x,_) ->
     (* Invariant: All docs in a union flatten to the same doc. Therefore we
        can choose the most flattened and flatten it completely. *)
     flatten x

let group (x:t): t = Union (flatten x,x)




(* Utility functions *)
let (^+) (a:t) (b:t): t =
  a ^ text " " ^ b

let (^/) (a:t) (b:t): t =
  a ^ space ^ b

let rec fold (f:t->t->t) (l:t list): t =
  match l with
  | [] ->
     Nil
  | [x] ->
     x
  | x :: xs ->
     f x (fold f xs)

let spread = fold (^+)
let stack = fold (^/)

let bracket (indent:int) (l:string) (x:t) (r:string): t =
  group (text l ^ (nest indent (cut ^ x)) ^ cut ^ text r)






type layout =
  | LNil                     (* empty layout *)
  | LText of string * layout (* string of text followed by a layout *)
  | LLine of int * layout    (* New line, subsequent indentiation, remaining
                                layout *)

let rec fits (w:int) (x:layout): bool =
  if w < 0 then
    false
  else
    match x with
    | LNil ->
       true
    | LText (s,x) ->
       fits (w - String.length s) x
    | LLine (i,x) ->
       true

let best (w:int) (x:t): layout =
  let better k x y =
    if fits (w-k) x then x else y
  in
  let rec be
            (k:int)  (* number of characters already on the line *)
            (lst: (int*t) list) (* list of documents with indentations *)
          : layout =
    match lst with
    | [] ->
       LNil

    | (i,Nil) :: z ->
       be k z

    | (i,Concat(x,y)) :: z ->
       be k ((i,x) :: (i,y) :: z)

    | (i,Nest(j,x)) :: z ->
       be k ((i+j,x) :: z)

    | (i,Text s) :: z ->
       LText(s, be (k + String.length s) z)

    | (i,Line _) :: z ->
       LLine (i, be i z)

    | (i,Union(x,y)) :: z ->
       better k
         (be k ((i,x) :: z))
         (be k ((i,y) :: z))
  in
  be 0 [0,x]




module type PRINTER =
  sig
    include Monad.MONAD
    val putc: char -> unit t
    val put_string: string -> unit t
    val put_substring: int -> int -> string -> unit t
    val fill: char -> int -> unit t
  end



module type PRETTY =
  functor (P:PRINTER) ->
  sig
    val print: int -> t -> unit P.t
  end


module String_printer:
sig
  include PRINTER
  val run: int -> 'a t -> string
end =
  struct
    include Monad.String_buffer
  end


module Pretty (P:PRINTER) =
  struct
    let print (width:int) (d:t): unit P.t =
      let rec pr x =
        let open P in
        match x with
        | LNil ->
           make ()
        | LText (s, x) ->
           put_string s >>= fun _ ->
           pr x
        | LLine (i, x) ->
           putc '\n' >>= fun _ ->
           fill ' ' i >>= fun _ ->
           pr x
      in
      pr (best width d)
  end


let string_of (width:int) (d:t): string =
  let module PP = Pretty (String_printer) in
  String_printer.run 200 (PP.print width d)



module Test_tree =
  struct
    type doc = t
    type t =
      | Node of string * t list

    let rec show_tree (t:t): doc =
      match t with
      | Node (s,ts) ->
         group (text s ^ nest (String.length s) (show_bracket ts))

    and show_bracket (ts:t list): doc =
      match ts with
      | [] ->
         Nil
      | ts ->
         text "[" ^ (nest 1 (show_trees ts) ^ text "]")

    and show_trees (ts:t list): doc =
      match ts with
      | [] ->
         assert false (* illegal call *)
      | [t] ->
         show_tree t
      | t :: ts ->
         show_tree t ^ text "," ^ cut ^ show_trees ts


    let rec show_tree2 (t:t): doc =
      match t with
      | Node (s,ts) ->
         text s ^ show_bracket2 ts
    and show_bracket2 (ts:t list): doc =
      match ts with
      | [] ->
         Nil
      | ts ->
         bracket 2 "[" (show_trees2 ts) "]"
    and show_trees2 (ts:t list): doc =
      match ts with
      | [] ->
         assert false (* illegal call *)
      | [t] ->
         show_tree2 t
      | t :: ts ->
         show_tree2 t ^ text "," ^ cut ^ show_trees2 ts

    let test (): unit =
      let t =
        Node ("a",
              [Node ("b", [Node("c",[]); Node ("d",[]) ]);
               Node ("e", []);
               Node ("f", [Node ("g",  []);
                           Node ("h", []);
                           Node ("i",  [])])
          ])
      in
      assert (string_of 15 (show_tree t)
              = "a[b[c,d],\n  e,\n  f[g,h,i]]");
      assert (string_of 15 (show_tree2 t)
              = "a[\n  b[c,d],\n  e,\n  f[g,h,i]\n]")
  end




let test (): unit =
  Printf.printf "test document\n";
  Test_tree.test()
