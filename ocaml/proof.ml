(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Container
open Term
open Printf


module Eval = struct
  type t =
      Term of term
    | Expand of int (* idx of function *)
    | Apply of t * t array * bool
    | Lam of int * int array * t * bool
    | Beta of t
    | Simpl of t * int * term array  (* e, idx of simplifying equality assertion,
                                        specialization arguments *)
end


type proof_term =
    Axiom      of term
  | Assumption of term
  | Detached   of int * int  (* modus ponens *)
  | Specialize of int * term array
  | Eval       of int*Eval.t  (* index of the term evaluated,evaluation *)
  | Eval_bwd   of term*Eval.t (* term which is backward evaluated, evaluation *)
  | Witness    of int * int array * term * term array
        (* term [i] is a witness for [some (a,b,...) t] where
           [a,b,..] in [t] are substituted by the arguments in the term array *)
  | Someelim   of int        (* index of the existenially quantified term *)
  | Inherit    of int * int * int (* assertion, base/descendant class *)
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

  val print_pt: string -> int -> t -> unit

  val term_up: int -> t -> t

  val split_subproof: t -> int * int array * int * t array

  val is_subproof: t -> bool

  val short_string: t -> string

end = struct

  type t = proof_term

  let adapt (start:int) (delta:int) (pt:t): t =
    (* Shift the assertion indices from [start] on up by [delta]. *)
    let index (i:int): int =
      if i < start then i else i + delta
    in
    let rec adapt_eval (e:Eval.t): Eval.t =
      match e with
        Eval.Term t   -> e
      | Eval.Expand i -> e
      | Eval.Apply (f,args,pr) ->
          let f = adapt_eval f
          and args = Array.map (fun e -> adapt_eval e) args in
          Eval.Apply (f,args,pr)
      | Eval.Lam (n,nms,e,pr) ->
          Eval.Lam (n, nms, adapt_eval e, pr)
      | Eval.Beta e -> Eval.Beta (adapt_eval e)
      | Eval.Simpl (e,eq_idx,args) ->
          Eval.Simpl (adapt_eval e, index eq_idx, args)
    in
    let rec adapt (pt:t): t =
      match pt with
        Axiom _ | Assumption _ -> pt
      | Detached (a,b) ->
          Detached (index a, index b)
      | Specialize (i,args) ->
          Specialize (index i, args)
      | Inherit (i,bcls,cls) ->
          Inherit (index i, bcls, cls)
      | Eval (i,e)    -> Eval (index i, adapt_eval e)
      | Eval_bwd (t,e)-> Eval_bwd (t, adapt_eval e)
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
      let rec usd_eval (e:Eval.t) (set:IntSet.t): IntSet.t =
        match e with
          Eval.Term t   -> set
        | Eval.Expand i -> set
        | Eval.Apply (f,args,_)   ->
            let set = usd_eval f set in
            Array.fold_left (fun set e -> usd_eval e set) set args
        | Eval.Lam (n,nms,e,_)  -> usd_eval e set
        | Eval.Beta e           -> usd_eval e set
        | Eval.Simpl (e,i,args) ->
            let set = usd i start_inner extern pt_arr set in
            usd_eval e set
      in
      if k < start then
        set
      else if k < start_inner then
        if extern then IntSet.add k set else set
      else
        let set = if extern then set else IntSet.add k set
        in
        match pt_arr.(k-start_inner) with
          Axiom _ | Assumption _ -> set
        | Detached (i,j) ->
            assert (i < k);
            assert (j < k);
            let set = usd i start_inner extern pt_arr set in
            usd j start_inner extern pt_arr set
        | Specialize (i,_) | Witness (i,_,_,_)| Someelim i ->
            assert (i < k);
            usd i start_inner extern pt_arr set
        | Eval (i,e) ->
            assert (i < k);
            let set = usd i start_inner extern pt_arr set in
            usd_eval e set
        | Eval_bwd (t,e) ->
            usd_eval e set
        | Subproof (_,_,k1,pt_arr1) ->
            let usd2 = usd k1 k true pt_arr1 IntSet.empty in
            let set =
            IntSet.fold
              (fun i set -> usd i start_inner extern pt_arr set)
              usd2
              set in
            set
        | Inherit (i,bcls,cls) ->
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
      let rec transform_eval (e:Eval.t): Eval.t =
        match e with
          Eval.Term _
        | Eval.Expand _ ->  e
        | Eval.Apply (f,args,pr) ->
            Eval.Apply (transform_eval f, Array.map transform_eval args,pr)
        | Eval.Lam (n,nms,e,pr) -> Eval.Lam (n,nms,transform_eval e,pr)
        | Eval.Beta e           -> Eval.Beta (transform_eval e)
        | Eval.Simpl (e,i,args) -> Eval.Simpl (transform_eval e, index i,args)
      in
      let transform (i:int) (pt:proof_term): proof_term =
        match pt with
          Axiom _ | Assumption _  ->
            pt
        | Detached (i,j) -> Detached (index i, index j)
        | Eval (i,e)     -> Eval   (index i, transform_eval e)
        | Eval_bwd (t,e) -> Eval_bwd (t, transform_eval e)
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
        | Inherit (i,bcls,cls) ->
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
          | Eval_bwd (t,_) ->
              uvars_term t set
          | Detached (i,_)
          | Eval   (i,_)
          | Someelim i ->
              set
          | Specialize (i,args)
          | Witness (i,_,_,args) ->
              uvars_args args set
          | Subproof (nb1,nms,i,pt_arr) ->
              uvars (nb+nb1) pt_arr set
          | Inherit (i,bcls,cls) ->
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
       has [args.length] variables and only [nargs] of them are unused. The [args]
       array maps variables to their new names ([i -> Variable j]: i: old
       variable, j: new variable). The unused variables map to [Variable
       (-1)].

       Note: It might be possible that no variables are removed, but that the
       variables are just permuted. *)
    assert (nargs <= Array.length args);
    let rec shrink (nb:int) (pt_arr:t array): t array =
      let shrink_inner (t:term) (nb1:int): term =
        Term.sub_from t (nb+nb1) args nargs
      in
      let shrink_term (t:term): term = shrink_inner t 0
      in
      let shrink_args_inner (args:term array) (nb:int): term array =
        Array.map (fun a -> shrink_inner a nb) args
      in
      let shrink_args (args:term array): term array = shrink_args_inner args 0
      in
      let shrink_eval (e:Eval.t): Eval.t =
        let var t =
          assert (Term.is_variable t);
          Term.variable t
        in
        let rec shrnk e nb =
          match e with
            Eval.Term t ->
              Eval.Term (shrink_inner t nb)
          | Eval.Expand idx ->
              Eval.Expand (var (shrink_inner (Variable idx) nb))
          | Eval.Apply(f,args,pr) ->
              let f = shrnk f nb
              and args = Array.map (fun e -> shrnk e nb) args in
              Eval.Apply (f,args,pr)
          | Eval.Lam (n,nms,e,pr) ->
              Eval.Lam (n,nms,shrnk e (nb+n),pr)
          | Eval.Beta e ->
              Eval.Beta (shrnk e nb)
          | Eval.Simpl (e,idx,args) ->
              Eval.Simpl (shrnk e nb, idx, shrink_args_inner args nb)
        in
        shrnk e 0
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
          | Eval (i,e)     -> Eval (i, shrink_eval e)
          | Eval_bwd (t,e) -> Eval_bwd (shrink_term t, shrink_eval e)
          | Witness (i,nms,t,args) ->
              let nargs = Array.length args in
              let args  = shrink_args args in
              let t = shrink_inner t nargs in
              Witness (i,nms,t,args)
          | Someelim i ->
              Someelim i
          | Subproof (nb1,nms,i,pt_arr) ->
              Subproof (nb1,nms,i, shrink (nb+nb1) pt_arr)
          | Inherit (i,bcls,cls) ->
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
      let up_inner t nb1 = Term.upbound n (nb1+nb) t in
      let up t = up_inner t 0 in
      let upargs_inner args nb =
        Array.map (fun a -> up_inner a nb) args
      in
      let upargs args = Array.map up args in
      let var t =
        assert (Term.is_variable t);
        Term.variable t
      in
      let rec upeval e nb =
        match e with
          Eval.Term t ->
            Eval.Term (up_inner t nb)
        | Eval.Expand idx ->
            Eval.Expand (var (up_inner (Variable idx) nb))
	| Eval.Apply(f,args,pr) ->
            let f = upeval f nb
            and args = Array.map (fun e -> upeval e nb) args in
            Eval.Apply(f,args,pr)
        | Eval.Lam (n,nms,e,pr) ->
            Eval.Lam (n, nms, upeval e (n+nb), pr)
        | Eval.Beta e ->
            Eval.Beta (upeval e nb)
        | Eval.Simpl (e,idx,args) ->
            Eval.Simpl (upeval e nb, idx, upargs_inner args nb)
      in
      let upeval_0 e = upeval e 0
      in
      match pt with
        Axiom t        -> Axiom (up t)
      | Assumption t   -> Assumption (up t)
      | Detached (i,j) -> pt
      | Specialize (i,args) -> Specialize (i, upargs args)
      | Eval (i,e)     -> Eval (i, upeval_0 e)
      | Eval_bwd (t,e) -> Eval_bwd (up t, upeval_0 e)
      | Witness (i,nms,t,args) ->
          let t = up t
          and args = upargs args in
          Witness (i,nms,t,args)
      | Someelim i     -> pt
      | Subproof (nb1,nms,i,pt_arr) ->
          let pt_arr = Array.map (fun pt -> trm_up (nb+nb1) pt) pt_arr in
          Subproof (nb1,nms,i,pt_arr)
      | Inherit (i,bcls,cls)-> pt
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
        Axiom t             ->
          print_prefix (); printf "Axiom %s\n" (Term.to_string t)
      | Assumption t        ->
          print_prefix (); printf "Assumption %s\n" (Term.to_string t)
      | Detached (i,j)      ->
          print_prefix (); printf "Detached %d %d\n" i j
      | Specialize (i,args) ->
          print_prefix (); printf "Specialize %d\n" i
      | Eval (i,_)          -> print_prefix (); printf "Eval %d\n" i
      | Eval_bwd (t,_)      ->
          print_prefix (); printf "Eval_bwd %s\n" (Term.to_string t)
      | Witness (i,_,t,args)-> print_prefix (); printf "Witness %d\n" i
      | Someelim i          -> print_prefix (); printf "Someelim %d\n" i
      | Subproof (nb,nms,i,pt_arr) ->
          print_prefix (); printf "Subproof nb %d, i %d\n" nb i;
          print_pt_arr (prefix^"  ") (start+k) pt_arr
      | Inherit (i,bcls,cls)  -> print_prefix (); printf "Inherit %d\n" i
    done

  let print_pt (prefix:string) (start:int) (pt:t): unit =
    print_pt_arr prefix start [|pt|]


  let short_string (pt:t): string =
    match pt with
      Axiom _  -> "ax"
    | Assumption _ -> "ass"
    | Detached (i,j) -> "mp " ^ (string_of_int i) ^ " " ^ (string_of_int j)
    | Specialize (i,args) -> "spec " ^ (string_of_int i)
    | Inherit (i,bcls,cls)     -> "inh " ^ (string_of_int i)
    | Eval (i,_)          -> "eval " ^ (string_of_int i)
    | Eval_bwd _          -> "eval"
    | Witness (i,nms,t,args) -> "wit " ^ (string_of_int i)
    | Someelim i             -> "selim " ^ (string_of_int i)
    | Subproof (nargs,names,res,pt_arr) -> "sub"
end
