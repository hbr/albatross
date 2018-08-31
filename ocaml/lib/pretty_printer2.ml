open Printf



module type DOCUMENT =
  sig
    type t
    val empty: t
    val (^): t -> t -> t
    val nest: int -> t -> t
    val text: string -> t
    val space: t
    val cut: t
    val optional: string -> t
    val group: t -> t
    val (^+): t -> t -> t
    val (^/): t -> t -> t
    val fold: (t -> t -> t) -> t list -> t
    val spread: t list -> t
    val stack:  t list -> t
    val bracket: int -> string -> t -> string -> t
  end

module Document =
  struct
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
      (* replace line breaks by spaces *)
      match d with
      | Nil -> Nil
      | Concat (d1,d2) ->
         Concat (flatten d1, flatten d2)
      | Nest (i,d) ->
         Nest (i, flatten d)
      | Text s ->
         Text s
      | Line s ->
         Text s (* remove line breaks *)
      | Union(x,_) ->
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
  end (* Document *)






module type LAYOUT =
  sig
    type t
    val best: int -> Document.t -> t
    val to_string: t -> string
    val pretty: int -> Document.t -> string
  end




module Layout: LAYOUT =
  struct
    type t =
      | LNil
      | LText of string * t
      | LLine of int * t

    let rec fits (w:int) (x:t): bool =
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

    let rec to_string (x:t): string =
      match x with
      | LNil -> ""
      | LText (s,x) -> s ^ to_string x
      | LLine (i,x) -> "\n" ^  String.make i ' ' ^  to_string x

    let best (w:int) (x:Document.t): t =
      let better w k x y =
        if fits (w-k) x then x else y
      in
      let rec be (w:int) (k:int) (lst: (int*Document.t) list): t =
        let open Document in
        match lst with
        | [] ->
           LNil
        | (i,Nil) :: z ->
           be w k z
        | (i,Concat(x,y)) :: z ->
           be w k ((i,x) :: (i,y) :: z)
        | (i,Nest(j,x)) :: z ->
           be w k ((i+j,x) :: z)
        | (i,Text s) :: z ->
           LText(s, be w (k + String.length s) z)
        | (i,Line _) :: z ->
           LLine (i, be w i z)
        | (i,Union(x,y)) :: z ->
           better w k
             (be w k ((i,x) :: z))
             (be w k ((i,y) :: z))
      in
      be w 0 [0,x]

    let pretty (w:int) (x:Document.t): string =
      to_string (best w x)
  end




module Test_tree =
  struct
    type t =
      | Node of string * t list

    let rec show_tree (t:t): Document.t =
      match t with
      | Node (s,ts) ->
         let open Document in
         group (text s ^ nest (String.length s) (show_bracket ts))

    and show_bracket (ts:t list): Document.t =
      let open Document in
      match ts with
      | [] ->
         Nil
      | ts ->
         text "[" ^ (nest 1 (show_trees ts) ^ text "]")

    and show_trees (ts:t list): Document.t =
      let open Document in
      match ts with
      | [] ->
         assert false (* illegal call *)
      | [t] ->
         show_tree t
      | t :: ts ->
         show_tree t ^ text "," ^ cut ^ show_trees ts


    let rec show_tree2 (t:t): Document.t =
      let open Document in
      match t with
      | Node (s,ts) ->
         text s ^ show_bracket2 ts
    and show_bracket2 (ts:t list): Document.t =
      let open Document in
      match ts with
      | [] ->
         Nil
      | ts ->
         bracket 2 "[" (show_trees2 ts) "]"
    and show_trees2 (ts:t list): Document.t =
      let open Document in
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
      assert (Layout.pretty 15 (show_tree t)
              = "a[b[c,d],\n  e,\n  f[g,h,i]]");
      assert (Layout.pretty 15 (show_tree2 t)
              = "a[\n  b[c,d],\n  e,\n  f[g,h,i]\n]")
  end




let test (): unit =
  printf "test pretty printer 2\n";
  Test_tree.test()
