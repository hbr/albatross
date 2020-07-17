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


    type red

    type black

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




    type 'a almost =
      (* A non empty tree which might violate the red invariant at the top. I.e.
       * if its color is red it might have a red child. *)
      | AT of
            (* Tree might have a violation of the red invariant *)
            color * 'a t * 'a pair * 'a t
      | OT of
            (* Red tree without violation *)
            'a t * 'a pair * 'a t


    let use_almost
            (ok: color -> 'a t -> 'a pair -> 'a t -> 'b)
            (vio1: 'a t -> 'a pair -> 'a t -> 'a pair -> 'a t -> 'b)
            (vio2: 'a t -> 'a pair -> 'a t -> 'a pair -> 'a t -> 'b)
            : 'a almost -> 'b =
        function
        | AT (Red, Node (Red, a, x, b), y, c) ->
            vio1 a x b y c

        | AT (Red, a, x, (Node (Red, b, y, c))) ->
            vio2 a x b y c

        | AT (color, a, x, b) ->
            ok color a x b

        | OT (a, x, b) ->
            ok Red a x b


    let rbt_of_almost (almost: 'a almost): 'a t =
        use_almost
            node
            (fun a x b y c ->
                Node (Black, Node (Red, a, x, b), y, c))
            (fun a x b y c ->
                Node (Black, a, x, Node (Red, b, y, c)))
            almost


    let balance_left
            (color: color) (left: 'a almost) (z: 'a pair) (d: 'a t)
            : 'a almost =
        (* [left] might have a violation of the red invariant. In that case the
         * violation is repaired by using the black parent. If there is no
         * violation, there is nothing to repair. But a new red violation might
         * be generated, because either [left] or [d] might have a red root and
         * the color of the parent might be red. *)
        let repair a x b y c =
            assert (color = Black);
            OT (
                Node (Black, a, x, b),
                y,
                Node (Black, c, z, d)
            )
        and ok c0 a x b =
            AT (
                color,
                node c0 a x b,
                z,
                d
            )
        in
        use_almost ok repair repair left


    let balance_right
            (color: color) (a: 'a t) (x: 'a pair) (right: 'a almost)
            : 'a almost =
        (* Symmetric case to [balance_left]. *)
        let repair b y c z d =
            assert (color = Black);
            OT (
                Node (Black, a, x, b),
                y,
                Node (Black, c, z, d)
            )
        and ok c0 b y c =
            AT (
                color,
                a,
                x,
                node c0 b y c
            )
        in
        use_almost ok repair repair right



    let rec add (k: Key.t) (v: 'a) (rbt: 'a t): 'a t =
        rbt_of_almost (ins k v rbt)

    and ins (k: Key.t) (v: 'a): 'a t -> 'a almost =
        function
        | Empty ->
            OT (Empty, (k, v), Empty)

        | Node (color, left, x, right) ->
            let cmp = compare k x
            in
            if 0 < cmp then
                balance_left color (ins k v left) x right

            else if cmp = 0 then
                AT (color, left, (k,v), right)

            else
                balance_right color left x (ins k v right)
end






module Set (Element: SORTABLE) =
struct
    module Map = Map (Element)

    type t = unit Map.t

    let empty: t =
        Map.empty

    let add (e: Element.t) (set: t): t =
        Map.add e () set
end
