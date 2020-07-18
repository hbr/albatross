open Module_types


module Gadt (Key: SORTABLE) =
struct
    type zero =
      | Z

    type 'a succ =
      | S of 'a


    type _ nat =
      | Zero: zero nat
      | Succ: 'a nat -> 'a succ nat


    type red =
      | R

    type black =
      | B

    type color =
      | Red of red
      | Black of black



    type (_,_) rbt =
      | Empty: (black, zero nat) rbt

      | RNode:
            (black, 'h nat) rbt * Key.t * (black, 'h nat) rbt
            -> (red, 'h nat) rbt

      | BNode:
            (_, 'h nat) rbt * Key.t * (_, 'h nat) rbt
            -> (black, 'h succ nat) rbt
end







module Map (Key: SORTABLE) =
struct

    (* Basics *)
    (**********)

    type 'a pair =
      Key.t * 'a

    let compare (key: Key.t) (p: 'a pair): int =
        Key.compare key (fst p)


    type color =
        | Red
        | Black

    type 'a t =
        (* A tree of type ['a t] always satisfies the red and the black
         * invariant. *)
        | Empty
        | Node of
            color
            * 'a t      (* left subtree *)
            * 'a pair   (* key value pair *)
            * 'a t      (* right subtree *)

    let empty: 'a t =
        Empty

    let node
            (color: color) (left: 'a t) (p: 'a pair) (right: 'a t)
            : 'a t =
        Node (color, left, p, right)


    let maybe_find (k: Key.t) (tree: 'a t): 'a option =
        let rec find tree =
            match tree with
            | Empty ->
                None
            | Node (_, left, x, right) ->
                let cmp = compare k x
                in
                if cmp < 0 then
                    find left
                else if cmp = 0 then
                    Some (snd x)
                else
                    find right
        in
        find tree




    let rec check_invariant (t: 'a t): (int * color) option =
        match t with
        | Empty ->
            Some (0, Black)
        | Node (color, left, _, right) ->
            Option.(
                check_invariant left  >>= fun (h1, c1) ->
                check_invariant right >>= fun (h2, c2) ->
                if h1 = h2 then
                    match color, c1, c2 with
                    | Red, Black, Black ->
                        Some (h1, Red)
                    | Red, _, _ ->
                        None
                    | Black, _, _ ->
                        Some (h1 + 1, Black)
                else
                    None
            )



    let is_balanced (t: 'a t): bool =
        match check_invariant t with
        | None ->
            false
        | Some _ ->
                true





    (* Insertion *)
    (*************)



    type 'a almost =
      | AOk of (* Root color unchanged, no violation. *)
            color * 'a t * 'a pair * 'a t

      | BROk of (* Root color changed from black to red, no violation *)
            'a t * 'a pair * 'a t

      | RVio of
            (* Root color remains red, red violation present because on of the
             * children has been red already. All nodes have the original black
             * height. *)
            'a t * 'a pair * 'a t * 'a pair * 'a t

    let almost_ok color a x b =
        AOk (color, a, x, b)

    let almost_black_to_red a x b =
        BROk (a, x, b)

    let almost_violated a x b y c =
        RVio (a, x, b, y, c)



    let use_almost
            (ok1: color -> 'a t -> 'a pair -> 'a t -> 'b)
            (ok2: 'a t -> 'a pair -> 'a t -> 'b)
            (vio: 'a t -> 'a pair -> 'a t -> 'a pair -> 'a t -> 'b)
            : 'a almost -> 'b =
        function
        | AOk (color, left, x, right) ->
            ok1 color left x right
        | BROk (left, x, right) ->
            ok2 left x right
        | RVio (a, x, b, y, c) ->
            vio a x b y c


    let rbt_of_almost (almost: 'a almost): 'a t =
        use_almost
            node
            (node Red)
            (fun a x b y c ->
                 node Black (node Red a x b) y c)
            almost


    let balance_left color left z d =
        use_almost
            (fun c0 a x b ->
                 (* c0 unchanged, no violation *)
                 almost_ok color (node c0 a x b) z d)
            (fun left p right ->
                 (* Root color of (left,p,right) changed from black to red, no
                  * violation. *)
                 match color with
                 | Black ->
                     almost_ok color (node Red left p right) z d

                 | Red ->
                     (* red violation *)
                     almost_violated left p right z d)
            (fun a x b y c ->
                 assert (color = Black);
                 almost_black_to_red
                     (node Black a x b)
                     y
                     (node Black c z d))
            left


    let balance_right color a x right =
        use_almost
            (fun c0 b y c ->
                 (* c0 unchanged, no violation *)
                 almost_ok color a x (node c0 b y c))
            (fun left p right ->
                 (* Root color of (left,p,right) changed from black to red, no
                  * violation. *)
                 match color with
                 | Black ->
                     almost_ok color a x (node Red left p right)

                 | Red ->
                     (* red violation *)
                     almost_violated a x left p right)
            (fun b y c z d ->
                 assert (color = Black);
                 almost_black_to_red
                     (node Black a x b)
                     y
                     (node Black c z d))
            right





    let rec add (k: Key.t) (v: 'a) (rbt: 'a t): 'a t =
        rbt_of_almost (ins k v rbt)

    and ins (k: Key.t) (v: 'a): 'a t -> 'a almost =
        function
        | Empty ->
            BROk (Empty, (k, v), Empty)

        | Node (color, left, x, right) ->
            let cmp = compare k x
            in
            if cmp < 0 then
                balance_left color (ins k v left) x right

            else if cmp = 0 then
                AOk (color, left, (k,v), right)

            else
                balance_right color left x (ins k v right)




    (* Deletion  *)
    (*************)

    type 'a removed =
      | ROk of
            (* The tree has the same height as before the removal and the same
             * color or its color has been changed to black. *)
            'a t * 'a pair

      | RMinus of
            (* The tree has a reduced black height. Its color is black and has
             * not been changed. *)
            'a t * 'a pair


    let swap_pair
            (pnew: 'a pair) (rtree: 'a removed)
            : 'a removed * 'a pair =
        match rtree with
        | ROk (r, p) ->
            ROk (r, pnew), p

        | RMinus (r, p) ->
            RMinus (r, pnew), p


    let use_left_sibling
            (black1: 'a t -> 'a pair -> 'a t -> 'b)
            (black2: 'a t -> 'a pair -> 'a t -> 'a pair -> 'a t -> 'b)
            (red1:  'a t -> 'a pair -> 'a t -> 'a pair -> 'a t -> 'b)
            (red2:  'a t -> 'a pair -> 'a t -> 'a pair -> 'a t ->
                    'a pair -> 'a t -> 'b)
            (tree: 'a t)
        : 'b =
        (* [tree] is the left sibling of a height reduced right node. The right
         * node has black height [h] and therefore the sibling must have black
         * height [h + 1]. Otherwise the tree had not been a valid red black
         * tree before the removal of a node.
         *
         * The function splits up the sibling into the ordered sequence
         *
         *      a x b y c z d
         *
         *  where at least [a x b] is present. All subtrees have black height
         *  [h] except in the red case where the subtree [a] which has black
         *  height [h + 1].
         *
         * [tree] is black:
         *
         *          Bx                          Bx
         *      a       Bb                  a        Ry
         *                                        Bb    Bc
         *
         *  [tree] is red:
         *
         *          Rx                          Rx
         *      Ba+     By                  Ba+     By
         *            b    Bc                     b     Rz
         *                                            Bc   Bd
         *)
        match tree with
        | Empty ->
            (* Cannot happen. [tree] has black height [h+1]. An empty node is
             * not possible. *)
            assert false

        | Node (Black, a, x, right) ->
            (
                match right with
                | Node (Red, b, y, c) ->
                    black2 a x b y c
                | _ ->
                    black1 a x right
            )

        | Node (Red, a, x, right) ->
            (
                match right with
                | Node (Black, b, y, Node (Red, c, z, d)) ->
                    red2 a x b y c z d
                | Node (Black, b, y, c) ->
                    red1 a x b y c
                | _ ->
                    (* Cannot happen. [right] must be black, because its parent
                     * is red. Since the black height is [h+1], [right] cannot
                     * be empty either. *)
                    assert false
            )


    let use_left_sibling_black_parent
        (left: 'a t) (p: 'a pair) (reduced: 'a t) (deleted: 'a pair)
        : 'a removed
        =
        (* black_height(left):      h + 1
         * black_height(reduced):   h
         * black height goal:       h + 2 *)
        use_left_sibling
            (fun a x b_black ->
                 RMinus ( (* black height h + 1 *)
                     Node (
                         Black,
                         a,
                         x,
                         Node (Red, b_black, p, reduced)
                     ),
                     deleted
                 ))
            (fun a x b y c ->
                 ROk ( (* black height: h + 2 *)
                     Node (
                         Black,
                         Node (Black, a, x, b),
                         y,
                         Node (Black, c, p, reduced)),
                     deleted))
            (fun aplus x b y c_black ->
                 ROk ( (* black height: h + 2 *)
                     Node (Black, aplus, x,
                           Node (Black, b, y,
                                 Node (Red, c_black, p, reduced))),
                     deleted
                 ))
            (fun aplus x b y c z d ->
                 ROk (  (* black height: h + 2 *)
                     Node (Black, aplus, x,
                           Node (Red,
                                 Node (Black, b, y, c),
                                 z,
                                 Node (Black, d, p, reduced))),
                     deleted))
            left



    let removed_left
            (_: color) (_: 'a removed) (_: 'a pair) (_: 'a t)
            : 'a removed =
        assert false





    let removed_right
            (color: color) (left: 'a t) (p: 'a pair) (reduced: 'a removed)
            : 'a removed =
        match reduced with
        | ROk (right, x) ->
            ROk (Node (color, left, p, right), x)

        | RMinus (reduced, deleted) ->
            match color with
            | Black ->
                use_left_sibling_black_parent
                    left
                    p
                    reduced
                    deleted

            | Red ->
                (* black_height(left):      h + 1
                 * black_height(reduced):   h
                 * black height goal:       h + 1 *)
                use_left_sibling
                    (fun _ _ _ -> assert false)
                    (fun _ _ _ _ ->
                         assert false)
                    (fun _ _ _ _ ->
                         (* Cannot be red. *)
                         assert false)
                    (fun _ _ _ _ _ ->
                         (* Cannot be red. *)
                         assert false)
                    left




    let remove_leftmost (_: 'a t): 'a removed option =
        assert false


    let remove_bottom (color: color) (x: 'a pair) (child: 'a t): 'a removed =
        (* Remove a bottom node with [color] and [x] which has at most one
         * [child]. *)
        match color, child with
        | Black, Empty ->
            RMinus (Empty, x)

        | Black, Node (Red, Empty, p, Empty) ->
            ROk (Node (Black, Empty, p, Empty), x)

        | Black, _ ->
            (* Cannot happen. If a black node has one child, the child must be
             * red. *)
            assert false

        | Red, Empty ->
            ROk (Empty, x)

        | Red, _ ->
            (* Cannot happen. A red node has either no children or two black
             * children. *)
            assert false



    let rec remove_aux (k: Key.t) (tree: 'a t): 'a removed option =
        match tree with
        | Empty ->
            None

        | Node (color, left, x, right) ->
            let cmp = compare k x
            in
            if cmp < 0 then
                Option.map
                    (fun left -> removed_left color left x right)
                    (remove_aux k left)

            else if cmp = 0 then
                match remove_leftmost right with
                | None ->
                    Some (remove_bottom color x left)
                | Some rtree ->
                    let tree, p = swap_pair x rtree in
                    Some (removed_right color left p tree)

            else
                Option.map
                    (fun right -> removed_right color left x right)
                    (remove_aux k right)


    let remove (key: Key.t) (tree: 'a t): 'a t =
        match remove_aux key tree with
        | None ->
            tree
        | Some (ROk (tree, _))
        | Some (RMinus (tree, _)) ->
            tree
end (* Map *)










module Set (Element: SORTABLE) =
struct
    module Map = Map (Element)

    type t = unit Map.t

    let empty: t =
        Map.empty

    let add (e: Element.t) (set: t): t =
        Map.add e () set
end



(* ------------------------------------------------------------------*)
(* Unit Tests *)
(* ------------------------------------------------------------------*)

module M = Map (Int)

let insert (n: int): int M.t =
    let rec ins i map =
        if i = n then
            map
        else
            ins (i + 1) (M.add i i map)
    in
    ins 0 M.empty

let rec check (n: int) (map: int M.t): bool =
    if n = 0 then
        true
    else
        let n = n - 1 in
        let res = M.maybe_find n map in
        match res with
        | None ->
            Printf.printf "nothing found for %d\n" n;
            false
        | Some k ->
            if n <> k then
                Printf.printf "found wrong pair %d %d\n" n k;
            check n map


let%test _ =
    check 100 (insert 100)

let%test _ =
    M.is_balanced (insert 100)
