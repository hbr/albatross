(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Container
open Term
open Printf

exception Limit_exceeded of int
exception Proof_failed of string

module Eval = struct
  type t =
      Term of term
    | Exp of (int * t array * t) (* idx of function, eval args, eval of expansion *)
    | VApply of int * t array
    | Apply of t * t array * bool
    | Lam of int * int array * term list * t * bool
    | QExp of int * int array * t * bool
    | Beta of t
    | Simpl of t * int * term array  (* e, idx of simplifying equality assertion,
                                        specialization arguments *)
    | Flow of flow * t array
    | If of (bool * int * t array) (* cond, idx cond, args *)
    | As of bool * t array
    | Inspect of (term * t * int * int * t)
          (* uneval, eval insp, case, nvars, eval res *)
  let rec print (prefix:string) (e:t): unit =
    let print_args args =
      let prefix = prefix ^ "  " in
      Array.iter (fun e -> print prefix e) args
    in
    match e with
      Term t -> printf "%s term %s\n" prefix (Term.to_string t)
    | Exp (i,args,e) ->
        printf "%s expand %d\n" prefix i;
        print (prefix ^ "    ") e
    | VApply (i,args) ->
        printf "%s apply %d\n" prefix i;
        print_args args
    | Apply (f,args,pr) ->
        printf "%s apply %s\n" prefix (if pr then "predicate" else "function");
        print (prefix ^ "    ") f;
        print_args args
    | Lam (n,nms,pres,e,pr) ->
        printf "%s lambda %s\n" prefix (if pr then "predicate" else "function");
        print (prefix ^ "    ") e
    | QExp (n,nms,e,is_all) ->
        printf "%s qexp %s\n" prefix (if is_all then "all" else "some");
        print (prefix ^ "    ") e
    | Beta e ->
        printf "%s beta\n" prefix;
        print (prefix ^ "    ") e
    | Simpl (e,idx,args) ->
        printf "%s simpl eq_idx %d\n" prefix idx;
        print (prefix ^ "    ") e
    | Flow (ctrl,args) ->
        printf "%s flow <%s>\n" prefix (string_of_flow ctrl);
        print_args args
    | If (cond,idx,args) ->
        printf "%s \"if\" %b idx %d\n" prefix cond idx;
        print_args args
    | As (cond,args) ->
        printf "%s \"as\" %b\n" prefix cond;
        print_args args
    | Inspect (t,inspe,icase,nvars,rese) ->
        printf "%s \"inspect\" case %d\n" prefix icase

end


type proof_term =
    Axiom      of term
  | Assumption of term
  | Funprop    of
      int * int * term array (* idx of function,
                                idx of postcondition,
                                arguments *)
  | Indset_rule of term * int
  | Indset_ind  of term
  | Indtype    of int (* cls *)
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

  val normalize_pair: int -> int array -> int -> term -> t array
    -> int * int array * term * t array

  val print_pt_arr:  string -> int -> t array -> unit

  val print_pt: string -> int -> t -> unit

  val term_up: int -> t -> t

  val split_subproof: t -> int * int array * int * t array

  val is_subproof: t -> bool

  val short_string: t -> string

end = struct

  type t = proof_term



  let rec print_pt_arr (prefix:string) (start:int) (pt_arr: t array): unit =
    let n = Array.length pt_arr in
    for k = 0 to n-1 do
      let print_prefix () = printf "%s%3d " prefix (start+k) in
      match pt_arr.(k) with
        Axiom t             ->
          print_prefix (); printf "Axiom %s\n" (Term.to_string t)
      | Assumption t        ->
          print_prefix (); printf "Assumption %s\n" (Term.to_string t)
      | Funprop (idx,i,_)  ->
          print_prefix (); printf "Funprop %d %d\n" idx i
      | Indset_rule (t,i) ->
          print_prefix (); printf "Rule %d of %s\n" i (Term.to_string t)
      | Indset_ind t ->
          print_prefix (); printf "Set induction law %s\n" (Term.to_string t)
      | Indtype cls ->
          print_prefix (); printf "Induction law cls %d\n" cls;
      | Detached (i,j)      ->
          print_prefix (); printf "Detached %d %d\n" i j
      | Specialize (i,args) ->
          print_prefix (); printf "Specialize %d\n" i
      | Eval (i,e)          ->
          print_prefix (); printf "Eval %d\n" i;
          Eval.print (prefix ^ "    ") e
      | Eval_bwd (t,e)      ->
          print_prefix ();
          printf "Eval_bwd %s\n" (Term.to_string t);
          Eval.print (prefix ^ "    ") e
      | Witness (i,_,t,args)-> print_prefix (); printf "Witness %d\n" i
      | Someelim i          -> print_prefix (); printf "Someelim %d\n" i
      | Subproof (nb,nms,i,pt_arr) ->
          print_prefix (); printf "Subproof nb %d, i %d\n" nb i;
          print_pt_arr (prefix^"  ") (start+k) pt_arr
      | Inherit (i,bcls,cls)  -> print_prefix (); printf "Inherit %d\n" i
    done

  let print_pt (prefix:string) (start:int) (pt:t): unit =
    print_pt_arr prefix start [|pt|]


  let adapt (start:int) (delta:int) (pt:t): t =
    (* Shift the assertion indices from [start] on up by [delta]. *)
    let index (i:int): int =
      if i < start then i else i + delta
    in
    let rec adapt_eval (e:Eval.t): Eval.t =
      let adapt_args args = Array.map (fun e -> adapt_eval e) args
      in
      match e with
        Eval.Term t   -> e
      | Eval.Exp (i,args,e) ->
          Eval.Exp (i, adapt_args args, adapt_eval e)
      | Eval.VApply (i,args) ->
          Eval.VApply (i, adapt_args args)
      | Eval.Apply (f,args,pr) ->
          let f = adapt_eval f
          and args = adapt_args args in
          Eval.Apply (f,args,pr)
      | Eval.Lam (n,nms,pres,e,pr) ->
          Eval.Lam (n, nms, pres, adapt_eval e, pr)
      | Eval.QExp (n,nms,e,is_all) ->
          Eval.QExp (n, nms, adapt_eval e, is_all)
      | Eval.Beta e -> Eval.Beta (adapt_eval e)
      | Eval.Simpl (e,eq_idx,args) ->
          Eval.Simpl (adapt_eval e, index eq_idx, args)
      | Eval.Flow (ctrl,args) ->
          Eval.Flow (ctrl, adapt_args args)
      | Eval.If (cond,idx,args) ->
          Eval.If (cond, index idx, adapt_args args)
      | Eval.As (cond,args) ->
          Eval.As (cond, adapt_args args)
      | Eval.Inspect (t,inspe,icase,nvars,rese) ->
          Eval.Inspect (t, adapt_eval inspe, icase, nvars, adapt_eval rese)

    in
    let rec adapt (pt:t): t =
      match pt with
        Axiom _ | Assumption _ | Funprop _
      | Indset_rule _ | Indset_ind _ | Indtype _ ->
          pt
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





  let rec used_below (start:int) (k:int) (below:int) (pt_arr:t array) (set:IntSet.t)
      : IntSet.t =
    (* The set of used proof terms in [pt_arr] which are below the index
       [below] added to the set [set], the indices in [pt_arr] start at
       [start]. It is assumed that [pt_arr] has no unused proof term.  *)
    let add_idx i set =
      if i < below then IntSet.add i set
      else set
    in
    let rec used_eval (e:Eval.t) (set:IntSet.t): IntSet.t =
      let used_args set args =
        Array.fold_left (fun set e -> used_eval e set) set args in
      match e with
        Eval.Term t -> set
      | Eval.Exp (i,args,e)    -> used_eval e (used_args set args)
      | Eval.VApply(i,args)    -> used_args set args
      | Eval.Apply (f,args,_)  -> used_args (used_eval f set) args
      | Eval.Lam (n,nms,_,e,_) | Eval.QExp (n,nms,e,_) -> used_eval e set
      | Eval.Beta e            -> used_eval e set
      | Eval.Simpl (e,i,args)  -> used_eval e (add_idx i set)
      | Eval.Flow (ctrl,args)  -> used_args set args
      | Eval.If (cond,idx,args)-> used_args (add_idx idx set) args
      | Eval.As (cond,args)    -> used_args set args
      | Eval.Inspect (t,inspe,icase,nvars,rese) ->
          used_eval rese (used_eval inspe set)
    in
    let set = add_idx k set in
    let i,set = Array.fold_left
        (fun (k,set) pt ->
          let set =
            match pt with
              Axiom _ | Assumption _ | Funprop _
            | Indset_rule _ | Indset_ind _ | Indtype _ ->
                set
            | Detached (i,j) ->
                add_idx i (add_idx j set)
            | Specialize (i,_) | Witness (i,_,_,_) | Someelim i ->
                add_idx i set
            | Eval (i,e) ->
                let set = add_idx i set in
                used_eval e set
            | Eval_bwd (t,e) ->
                used_eval e set
            | Subproof (_,_,k1,pt_arr1) ->
                used_below k k1 below pt_arr1 set
            | Inherit (i,bcls,cls) ->
                assert false
          in
          k+1, set)
        (0,set)
        pt_arr
    in
    assert (i = Array.length pt_arr);
    set



  let used (k:int) (start:int) (pt_arr:t array): IntSet.t =
    (* The set of used proof terms in [pt_arr] which are needed to proof the
       term [k].  The index [k] is absolute, numbering in [pt_arr] starts at
       [start]. The returned set contains absolute numbers. *)
    let rec usd (k:int) (pt_arr: t array) (set:IntSet.t): IntSet.t =
      let n = Array.length pt_arr in
      assert (k < start + n);
      let rec usd_eval (e:Eval.t) (set:IntSet.t): IntSet.t =
        let usd_args set args =
          Array.fold_left (fun set e -> usd_eval e set) set args in
        match e with
          Eval.Term t   -> set
        | Eval.Exp (i,args,e)    -> usd_eval e (usd_args set args)
        | Eval.VApply (i,args)   -> usd_args set args
        | Eval.Apply (f,args,_) ->
            let set = usd_eval f set in
            usd_args set args
        | Eval.Lam (n,nms,_,e,_) | Eval.QExp(n,nms,e,_) -> usd_eval e set
        | Eval.Beta e           -> usd_eval e set
        | Eval.Simpl (e,i,args) ->
            let set = usd i pt_arr set in
            usd_eval e set
        | Eval.Flow (ctrl,args) -> usd_args set args
        | Eval.If (cond,idx,args) -> usd_args (usd idx pt_arr set) args
        | Eval.As (cond,args)   -> usd_args set args
        | Eval.Inspect(t,inspe,icase,nvars,rese) ->
            usd_eval rese (usd_eval inspe set)
      in
      if k < start then
        set
      else
        let set = IntSet.add k set in
        match pt_arr.(k-start) with
          Axiom _ | Assumption _ | Funprop _
        | Indset_rule _ | Indset_ind _ | Indtype _ ->
            set
        | Detached (i,j) ->
            assert (i < k);
            assert (j < k);
            let set = usd i pt_arr set in
            usd j pt_arr set
        | Specialize (i,_) | Witness (i,_,_,_)| Someelim i ->
            assert (i < k);
            usd i pt_arr set
        | Eval (i,e) ->
            assert (i < k);
            let set = usd i pt_arr set in
            usd_eval e set
        | Eval_bwd (t,e) ->
            usd_eval e set
        | Subproof (_,_,k1,pt_arr1) ->
            let set1 = used_below k k1 k pt_arr1 IntSet.empty in
            IntSet.fold
              (fun i set -> usd i pt_arr set)
              set1
              set
        | Inherit (i,bcls,cls) ->
            assert false
    in
    usd k pt_arr IntSet.empty


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
          Eval.Term _ -> e
        | Eval.Exp (i,args,e) ->
            Eval.Exp(i, Array.map transform_eval args, transform_eval e)
        | Eval.VApply (i,args) ->
            Eval.VApply (i, Array.map transform_eval args)
        | Eval.Apply (f,args,pr) ->
            Eval.Apply (transform_eval f, Array.map transform_eval args,pr)
        | Eval.Lam (n,nms,pres,e,pr) -> Eval.Lam (n,nms,pres,transform_eval e,pr)
        | Eval.QExp (n,nms,e,ia)-> Eval.QExp (n,nms,transform_eval e,ia)
        | Eval.Beta e           -> Eval.Beta (transform_eval e)
        | Eval.Simpl (e,i,args) -> Eval.Simpl (transform_eval e, index i,args)
        | Eval.Flow (ctrl,args) -> Eval.Flow (ctrl, Array.map transform_eval args)
        | Eval.If (cond,i,args) -> Eval.If(cond,index i, Array.map transform_eval args)
        | Eval.As (cond,args)   -> Eval.As(cond,Array.map transform_eval args)
        | Eval.Inspect (t,inspe,icase,nvars,rese) ->
            Eval.Inspect (t, transform_eval inspe, icase, nvars, transform_eval rese)
      in
      let transform (i:int) (pt:proof_term): proof_term =
        match pt with
          Axiom _ | Assumption _  | Funprop _
        | Indset_rule _ | Indset_ind _ | Indtype _ ->
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
          | Indset_rule (t,_)
          | Indset_ind t
          | Eval_bwd (t,_) ->
              uvars_term t set
          | Indtype _
          | Detached _
          | Eval _
          | Someelim _ ->
              set
          | Funprop (_,_,args)
          | Specialize (_,args)
          | Witness (_,_,_,args) ->
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
      and shrink_list_inner (lst:term list) (nb:int): term list =
        List.map (fun a -> shrink_inner a nb) lst
      in
      let shrink_args (args:term array): term array = shrink_args_inner args 0
      in
      let shrink_eval (e:Eval.t): Eval.t =
        let var t =
          assert (Term.is_variable t);
          Term.variable t
        in
        let rec shrnk e nb =
          let shrnk_eargs args = Array.map (fun e -> shrnk e nb) args in
          match e with
            Eval.Term t ->
              Eval.Term (shrink_inner t nb)
          | Eval.Exp (idx,args,e) ->
              let idx  = var (shrink_inner (Variable idx) nb)
              and args = shrnk_eargs args
              and e    = shrnk e nb in
              Eval.Exp (idx,args,e)
          | Eval.VApply(i,args) ->
              let i = var (shrink_inner (Variable i) nb)
              and args = shrnk_eargs args in
              Eval.VApply (i,args)
          | Eval.Apply(f,args,pr) ->
              let f = shrnk f nb
              and args = shrnk_eargs args in
              Eval.Apply (f,args,pr)
          | Eval.Lam (n,nms,pres,e,pr) ->
              Eval.Lam (n,nms,shrink_list_inner pres (1+nb),shrnk e (1+nb),pr)
          | Eval.QExp (n,nms,e,is_all) ->
              Eval.QExp (n,nms,shrnk e (nb+n),is_all)
          | Eval.Beta e ->
              Eval.Beta (shrnk e nb)
          | Eval.Simpl (e,idx,args) ->
              Eval.Simpl (shrnk e nb, idx, shrink_args_inner args nb)
          | Eval.Flow (ctrl,args) -> Eval.Flow (ctrl, shrnk_eargs args)
          | Eval.If(cond,idx,args)-> Eval.If(cond,idx,shrnk_eargs args)
          | Eval.As(cond,args)    -> Eval.As(cond,shrnk_eargs args)
          | Eval.Inspect(t,inspe,icase,nvars,rese) ->
              let t = shrink_inner t nb
              and inspe = shrnk inspe nb
              and rese  = shrnk rese  nb in
              Eval.Inspect(t,inspe,icase,nvars,rese)
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
          | Indset_rule (t,i) ->
              Indset_rule(shrink_term t,i)
          | Indset_ind t ->
              Indset_ind(shrink_term t)
          | Indtype _
          | Detached _ ->
              pt
          | Funprop(idx,i,args) ->
              Funprop(idx,i,shrink_args args)
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


  let normalize_pair
      (nargs:int) (nms:int array) (start:int) (t:term) (pt_arr: t array)
      : int * int array * term  * t array =
    assert (nargs = Array.length nms);
    let usd,pos = Term.used_variables_transform t nargs in
    let nargs1 = Array.length usd in
    let uvars_pt = used_variables nargs pt_arr in
    if not (nargs1 = IntSet.cardinal uvars_pt &&
            interval_for_all (fun i -> IntSet.mem usd.(i) uvars_pt) 0 nargs1)
    then begin
      printf "normalize_pair\n";
      printf "   nargs %d, nargs1 %d, card uvars_pt %d, nms %s\n"
        nargs nargs1 (IntSet.cardinal uvars_pt)
        ("(" ^ (String.concat ","
                  (List.map Support.ST.string (Array.to_list nms))) ^ ")");
      raise Not_found end;
    let args = Array.map (fun i -> Variable i) pos
    and nms1 = Array.init nargs1 (fun i -> nms.(usd.(i))) in
    let t      = Term.sub t args nargs1
    and pt_arr = remove_unused_variables args nargs1 pt_arr in
    nargs1, nms1, t, pt_arr




  let term_up (n:int) (pt:t): t =
    (* Shift all terms used in the proof term [pt] up by [n]. *)
    let rec trm_up nb pt =
      let up_inner t nb1 = Term.upbound n (nb1+nb) t in
      let up t = up_inner t 0 in
      let upargs_inner args nb =
        Array.map (fun a -> up_inner a nb) args
      and uplist_inner lst nb =
        List.map (fun a -> up_inner a nb) lst
      in
      let upargs args = Array.map up args in
      let var t =
        assert (Term.is_variable t);
        Term.variable t
      in
      let rec upeval e nb =
        let upeval_args args = Array.map (fun e -> upeval e nb) args in
        match e with
          Eval.Term t ->
            Eval.Term (up_inner t nb)
        | Eval.Exp (idx,args,e) ->
            let idx  = var (up_inner (Variable idx) nb)
            and args = upeval_args args
            and e    = upeval e nb in
            Eval.Exp (idx,args,e)
	| Eval.VApply(i,args) ->
            let i    = var (up_inner (Variable i) nb)
            and args = upeval_args args in
            Eval.VApply(i,args)
	| Eval.Apply(f,args,pr) ->
            let f = upeval f nb
            and args = upeval_args args in
            Eval.Apply(f,args,pr)
        | Eval.Lam (n,nms,pres,e,pr) ->
            Eval.Lam (n, nms, uplist_inner pres (1+nb), upeval e (1+nb), pr)
        | Eval.QExp (n,nms,e,is_all) ->
            Eval.QExp (n, nms, upeval e (n+nb),is_all)
        | Eval.Beta e ->
            Eval.Beta (upeval e nb)
        | Eval.Simpl (e,idx,args) ->
            Eval.Simpl (upeval e nb, idx, upargs_inner args nb)
        | Eval.Flow (ctrl,args) -> Eval.Flow (ctrl, upeval_args args)
        | Eval.If(cond,idx,args)-> Eval.If(cond,idx,upeval_args args)
        | Eval.As(cond,args)    -> Eval.As(cond,upeval_args args)
        | Eval.Inspect(t,inspe,icase,nvars,rese) ->
            let t = up_inner t nb
            and inspe = upeval inspe nb
            and rese  = upeval rese  nb in
            Eval.Inspect(t,inspe,icase,nvars,rese)
      in
      let upeval_0 e = upeval e 0
      in
      match pt with
        Axiom t        -> Axiom (up t)
      | Assumption t   -> Assumption (up t)
      | Indset_rule (t,i) -> Indset_rule (up t,i)
      | Indset_ind t      -> Indset_ind (up t)
      | Indtype  _
      | Detached _ -> pt
      | Funprop (idx,i,args) -> Funprop(idx,i, upargs args)
      | Specialize (i,args)  -> Specialize (i, upargs args)
      | Eval (i,e)     -> Eval (i, upeval_0 e)
      | Eval_bwd (t,e) -> Eval_bwd (up t, upeval_0 e)
      | Witness (i,nms,t,args) ->
          let n = Array.length nms in
          let t    = up_inner t n
          and args = upargs_inner args n in
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
  let short_string (pt:t): string =
    match pt with
      Axiom _  -> "ax"
    | Assumption _ -> "ass"
    | Funprop _ -> "prop"
    | Indset_rule (_,_) -> "rule"
    | Indset_ind _ -> "indset"
    | Indtype _    -> "ind"
    | Detached (i,j) -> "mp " ^ (string_of_int i) ^ " " ^ (string_of_int j)
    | Specialize (i,args) -> "spec " ^ (string_of_int i)
    | Inherit (i,bcls,cls)     -> "inh " ^ (string_of_int i)
    | Eval (i,_)          -> "eval " ^ (string_of_int i)
    | Eval_bwd _          -> "eval"
    | Witness (i,nms,t,args) -> "wit " ^ (string_of_int i)
    | Someelim i             -> "selim " ^ (string_of_int i)
    | Subproof (nargs,names,res,pt_arr) -> "sub"
end
