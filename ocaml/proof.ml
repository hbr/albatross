open Container
open Term
open Printf

type reduction =
    RVar of int
  | RApply of int (* nargs *)
  | RLam of int * int array  (* nargs, names *)
  | RBeta
  | RExpand
  | REqual of int  (* index of the equality assertion *)



type proof_term =
    Axiom      of term
  | Assumption of term
  | Detached   of int * int  (* modus ponens *)
  | Specialize of int * term array
  | Expand     of int        (* index of term which is expanded *)
  | Expand_bwd of term       (* term which is backward expanded *)
  | Reduce     of int        (* index of term which is reduced  *)
  | Reduce_bwd of term       (* term which is backward reduced  *)
  | Witness    of int * int array * term * term array
        (* term [i] is a witness for [some (a,b,...) t] where
           [a,b,..] in [t] are substituted by the arguments in the term array *)
  | Someelim   of int        (* index of the existenially quantified term *)
  | Inherit    of int * int  (* assertion, descendant class *)
  | Subproof   of int        (* nargs *)
                * int array  (* names *)
                * int        (* res *)
                * proof_term array


module Proof_term: sig
  type t = proof_term

  val adapt: int -> int -> t -> t

  val remove_unused: int -> int -> t array -> int * t array

  val used_variables: int -> t array -> IntSet.t

  val remove_unused_variables: term array -> int -> t array -> t array

  val normalize_pair: int -> int array -> term -> t array
    -> int * int array * term * t array

  val print_pt_arr:  string -> int -> t array -> unit

  val term_up: int -> t -> t

  val split_subproof: t -> int * int array * int * t array

  val is_subproof: t -> bool

end = struct

  type t = proof_term

  let adapt (start:int) (delta:int) (pt:t): t =
    (* Shift the assertion indices from [start] on up by [delta]. *)
    let index (i:int): int =
      if i < start then i else i + delta
    in
    let rec adapt (pt:t): t =
      match pt with
        Axiom _ | Assumption _ -> pt
      | Detached (a,b) ->
          Detached (index a, index b)
      | Specialize (i,args) ->
          Specialize (index i, args)
      | Inherit (i,cls) ->
          Inherit (index i, cls)
      | Expand i     -> Expand (index i)
      | Expand_bwd t -> Expand_bwd t
      | Reduce i     -> Reduce (index i)
      | Reduce_bwd t -> Reduce_bwd t
      | Witness (i,nms,t,args) ->
          Witness (index i,nms,t,args)
      | Someelim i   -> Someelim (index i)
      | Subproof (nargs,names,res,pt_arr) ->
          Subproof (nargs,names, index res, Array.map adapt pt_arr)
    in
    if delta = 0 then pt else adapt pt


  let count_assumptions (pt_array: t array): int =
    let n = Array.length pt_array in
    let rec count (i:int): int =
      assert (i <= n);
      if i = n then n
      else
        match pt_array.(i) with
          Assumption _ -> count (i+1)
        | _ -> i
    in
    count 0


  let used (k:int) (start:int) (pt_arr:t array): IntSet.t =
    (* The set of used proof terms in [pt_arr] which are needed to proof the
       term [k].  The index [k] is absolute, numbering in [pt_arr] starts at
       [start]. The returned set contains absolute numbers. *)
    let rec usd
        (k:int)
        (start_inner:int)
        (extern:bool)  (* look for used terms below [start_inner] *)
        (pt_arr: t array)
        (set:IntSet.t)
        : IntSet.t =
      let n = Array.length pt_arr in
      assert (k < start_inner + n);
      if k < start then
        set
      else if k < start_inner then
        if extern then IntSet.add k set else set
      else
        let set = if extern then set else IntSet.add k set
        in
        match pt_arr.(k-start_inner) with
          Axiom _ | Assumption _ | Reduce_bwd _ | Expand_bwd _ ->
            set
        | Detached (i,j) ->
            assert (i < k);
            assert (j < k);
            let set = usd i start_inner extern pt_arr set in
            usd j start_inner extern pt_arr set
        | Specialize (i,_) | Expand i | Reduce i | Witness (i,_,_,_) | Someelim i ->
            assert (i < k);
            usd i start_inner extern pt_arr set
        | Subproof (_,_,k1,pt_arr1) ->
            let usd2 = usd k1 k true pt_arr1 IntSet.empty in
            let set =
            IntSet.fold
              (fun i set -> usd i start_inner extern pt_arr set)
              usd2
              set in
            set
        | Inherit (i,cls) ->
            assert false
    in
    usd k start false pt_arr IntSet.empty


  let reindex (start:int) (map: (int*int) array) (k:int) (pt_arr:t array)
      : int * t array =
    (* Remove unused proof terms and reindex the proof terms in the array [pt_arr]

       start: index of the first proof term in [pt_arr]

       n_rem: number of removed terms

       map: old index -> new index,n_removed (-1: indicates that the term is unused)
            n_removed: number of removed terms below [old_index]
            note: indices in map are relative
     *)
    let n = Array.length pt_arr in
    assert (n = Array.length map);
    let rec reidx (start_inner:int) (below:int) (n_rem:int) (k:int) (pt_arr:t array)
        : int * t array =
      assert (n_rem <= n);
      let is_inner = below <= start_inner in
      assert (is_inner || start = start_inner);
      let index (i:int): int =
        if i < start then i
        else if i < below then
          (let idx,_ = map.(i-start) in
          assert (idx <> -1);
          idx + start)
        else
          i - n_rem
      in
      let transform (i:int) (pt:proof_term): proof_term =
        match pt with
          Axiom _ | Assumption _ | Reduce_bwd _ | Expand_bwd _ ->
            pt
        | Detached (i,j) -> Detached (index i, index j)
        | Expand i       -> Expand (index i)
        | Reduce i       -> Reduce (index i)
        | Specialize (i,args) -> Specialize (index i, args)
        | Witness (i,nms,t,args)  -> Witness (index i, nms, t, args)
        | Someelim i -> Someelim (index i)
        | Subproof (nargs,nms,k,pt_arr1) ->
            let start_inner = start_inner + i in
            let below = if is_inner then below else start_inner in
            let n_rem = if is_inner then n_rem else snd map.(i) in
            let k,pt_arr = reidx start_inner below n_rem k pt_arr1 in
            assert (k < start_inner + Array.length pt_arr);
            Subproof (nargs, nms, k, pt_arr)
        | Inherit (i,cls) ->
            assert false
      in
      let lst,i =
        Array.fold_left
          (fun (lst,i) pt ->
            assert (is_inner || i < n);
            let add = is_inner || (fst map.(i)) <> -1 in
            if add then
              (transform i pt)::lst, i+1
            else
              lst, i+1)
          ([],0)
          pt_arr
      in
      assert (i = Array.length pt_arr);
      (index k), Array.of_list (List.rev lst)
    in
    reidx start (start+n) 0 k pt_arr



  let remove_unused (k:int) (start:int) (pt_arr:t array): int * t array =
    let n = Array.length pt_arr in
    assert (0 < n);
    assert (k < start + n);
    let usd  = used k start pt_arr
    and nreq = count_assumptions pt_arr
    and map  = Array.make n (-1,0)
    in
    let pos   = ref nreq
    in
    for i = 0 to nreq-1 do (* all assumptions *)
      map.(i) <- i, 0
    done;
    let n_rem = ref 0
    and next  = ref nreq in
    IntSet.iter
      (fun i ->
        assert (i < start + n);
        if start + nreq <= i then begin (* used, but not assumption *)
          let i_rel = i - start in
          assert (!next <= i_rel);
          assert (!n_rem <= n);
          n_rem := !n_rem + (i_rel - !next);
          map.(i_rel) <- !pos, !n_rem;
          pos   := !pos + 1;
          next  := i_rel + 1
        end)
      usd;
    reindex start map k pt_arr




  let used_in_term (nb:int) (nargs:int) (t:term) (set:IntSet.t): IntSet.t =
    Term.fold
      (fun set ivar ->
        if ivar < nb || nb + nargs <= ivar then
          set
        else
          IntSet.add (ivar-nb) set
      )
      set
      t



  let used_variables (nargs:int) (pt_arr: t array): IntSet.t =
    let rec uvars (nb:int) (pt_arr: t array) (set:IntSet.t): IntSet.t =
      let uvars_term (t:term) (set:IntSet.t): IntSet.t =
        used_in_term nb nargs t set
      in
      let uvars_args (args: term array) (set:IntSet.t): IntSet.t =
        Array.fold_left
          (fun set t -> uvars_term t set)
          set
          args
      in
      Array.fold_left
        (fun set pt ->
          match pt with
            Axiom t
          | Assumption t
          | Expand_bwd t
          | Reduce_bwd t ->
              uvars_term t set
          | Detached (i,_)
          | Expand i
          | Reduce i
          | Someelim i ->
              set
          | Specialize (i,args)
          | Witness (i,_,_,args) ->
              uvars_args args set
          | Subproof (nb1,nms,i,pt_arr) ->
              uvars (nb+nb1) pt_arr set
          | Inherit (i,cls) ->
              assert false
        )
          set
        pt_arr
      in
    if nargs = 0 then
      IntSet.empty
    else
      uvars 0 pt_arr IntSet.empty


  let remove_unused_variables
      (args:term array)
      (nargs: int)
      (pt_arr:t array)
      : t array =
    (* Remove unused variables in [pt_arr]. The array of proof term [pt_arr]
       has [args.length] variables only [nargs] of them are unused. The [args]
       array maps variables to their new names ([i -> Variable j]: i: old
       variable, j: new variable). The unused variable map to [Variable
       (-1)]. *)
    assert (nargs <= Array.length args);
    let rec shrink (nb:int) (pt_arr:t array): t array =
      let shrink_inner (t:term) (nb1:int): term =
        Term.sub_from t (nb+nb1) args nargs
      in
      let shrink_term (t:term): term =
        shrink_inner t 0
      in
      let shrink_args (args:term array): term array =
        Array.map shrink_term args
      in
      Array.map
        (fun pt ->
          match pt with
            Axiom t ->
              Axiom (shrink_term t)
          | Assumption t ->
              Assumption (shrink_term t)
          | Detached (i,j) ->
              pt
          | Specialize (i,args) ->
              Specialize (i, shrink_args args)
          | Expand i ->
              Expand i
          | Expand_bwd t ->
              Expand_bwd (shrink_term t)
          | Reduce i ->
              pt
          | Reduce_bwd t ->
              Reduce_bwd (shrink_term t)
          | Witness (i,nms,t,args) ->
              let nargs = Array.length args in
              let args  = shrink_args args in
              let t = shrink_inner t nargs in
              Witness (i,nms,t,args)
          | Someelim i ->
              Someelim i
          | Subproof (nb1,nms,i,pt_arr) ->
              Subproof (nb1,nms,i, shrink (nb+nb1) pt_arr)
          | Inherit (i,cls) ->
              assert false
        )
        pt_arr
    in
    shrink 0 pt_arr


  let normalize_pair (nargs:int) (nms:int array) (t:term) (pt_arr: t array)
      : int * int array * term  * t array =
    let uvars_t = Term.used_variables t nargs in
    let nargs1  = List.length uvars_t in
    assert (nargs1 <= nargs);
    let uvars_pt = used_variables nargs pt_arr in
    if not (nargs1 = IntSet.cardinal uvars_pt &&
            List.for_all (fun i -> IntSet.mem i uvars_pt) uvars_t)
    then
      raise Not_found;
    let args = Array.make nargs (Variable (-1))
    and nms1 = Array.make nargs1 (-1) in
    List.iteri
      (fun pos i -> assert (i < nargs);
        let pos1 = nargs1 - pos - 1 in
        args.(i)   <- Variable pos1;
        nms1.(pos1) <- nms.(i))
      uvars_t;
    let t      = Term.sub t args nargs1
    and pt_arr = remove_unused_variables args nargs1 pt_arr
    in
    nargs1, nms1, t, pt_arr




  let term_up (n:int) (pt:t): t =
    (* Shift all terms used in the proof term [pt] up by [n]. *)
    let rec trm_up nb pt =
      let up t = Term.upbound n nb t in
      let upargs args = Array.map up args in
      match pt with
        Axiom t        -> Axiom (up t)
      | Assumption t   -> Assumption (up t)
      | Detached (i,j) -> pt
      | Specialize (i,args) -> Specialize (i, upargs args)
      | Expand i       -> pt
      | Expand_bwd t   -> Expand_bwd (up t)
      | Reduce i       -> pt
      | Reduce_bwd t   -> Reduce_bwd (up t)
      | Witness (i,nms,t,args) ->
          let t = up t
          and args = upargs args in
          Witness (i,nms,t,args)
      | Someelim i     -> pt
      | Subproof (nb1,nms,i,pt_arr) ->
          let pt_arr = Array.map (fun pt -> trm_up (nb+nb1) pt) pt_arr in
          Subproof (nb1,nms,i,pt_arr)
      | Inherit (i,cls)-> pt
    in
    if n = 0 then pt else trm_up 0 pt


  let split_subproof (pt:t): int * int array * int * t array =
    match pt with
      Subproof (nb,nms,i,pt_arr) -> nb,nms,i,pt_arr
    | _ -> raise Not_found

  let is_subproof (pt:t): bool =
    try let _ = split_subproof pt in true
    with Not_found -> false


  let rec print_pt_arr (prefix:string) (start:int) (pt_arr: t array): unit =
    let n = Array.length pt_arr in
    for k = 0 to n-1 do
      let print_prefix () = printf "%s%3d " prefix (start+k) in
      match pt_arr.(k) with
        Axiom t             -> print_prefix (); printf "Axiom\n"
      | Assumption t        -> print_prefix (); printf "Assumption\n"
      | Detached (i,j)      -> print_prefix (); printf "Detached %d %d\n" i j
      | Specialize (i,args) -> print_prefix (); printf "Specialize %d\n" i
      | Expand i            -> print_prefix (); printf "Expand %d\n" i
      | Expand_bwd t        -> print_prefix (); printf "Expand_bwd\n"
      | Reduce i            -> print_prefix (); printf "Reduce %d\n" i
      | Reduce_bwd t        -> print_prefix (); printf "Reduce_bwd\n"
      | Witness (i,_,t,args)-> print_prefix (); printf "Witness %d\n" i
      | Someelim i          -> print_prefix (); printf "Someelim %d\n" i
      | Subproof (nb,nms,i,pt_arr) ->
          print_prefix (); printf "Subproof nb %d, i %d\n" nb i;
          print_pt_arr (prefix^"  ") (start+k) pt_arr
      | Inherit (i,cls)     -> print_prefix (); printf "Inherit %d\n" i
    done
end
