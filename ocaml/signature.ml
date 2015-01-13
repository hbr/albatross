(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Container
open Term


module Term_sub_arr: sig

  type t
  val empty:          t
  val make:           int -> t
  val count:          t -> int
  val get:            int -> t -> term
  val flags:          t -> bool array
  val args:           t -> term array
  val has:            int -> t -> bool
  val anchor:         int -> t -> int
  val add_new:        int -> term -> t -> unit
  val update:         int -> term -> t -> unit
  val up_above_top:   int -> t -> t
  val down_above_top: int -> t -> t
  val add_top:        int -> t -> t
  val add_bottom:     int -> t -> t
  val remove_bottom:  int -> t -> t

  val sub_star:       term -> t -> term
      (** [sub_star t s] applies to the term [t] the substitution [s] until no
          more substitutions are possible.  *)

  val get_star:       int -> t -> term
    (** [get_star i s] gets the [i]th substitution term and applies the
        substitution [s] until no more substitutions are possible.  *)

  val subs:           t -> (int*term*term) list

end = struct

  type t = {
      args:  term array;
      flags: bool array;
      used: int list array (* a list of used type variables for each
                              substitution *)
    }

  let flags (s:t): bool array = s.flags
  let args  (s:t): term array = s.args


  let make (n:int): t =
    {args  = Array.init n (fun i -> Variable i);
     flags = Array.make n false;
     used  = Array.make n []}

  let empty: t = make 0

  let count (s:t): int = Array.length s.args

  let has (i:int) (s:t): bool =
    assert (i < count s);
    s.flags.(i)

  let get (i:int) (s:t): term =
    assert (i < (count s));
    s.args.(i)


  let is_used (i:int) (j:int) (s:t): bool =
    (* Is the type variable [i] used directly or indirectly in the
       substitution of the type variable [j] *)
    assert (i < count s);
    let rec isused_in (j:int) (n:int): bool =
      assert (0 < n);
      assert (j < count s);
      List.exists (fun k -> k = i || isused_in k (n-1)) s.used.(j)
    in
    isused_in j (count s)

  let to_string (s:t): string =
    let str = ref ""
    and nsub = ref 0 in
    for i = 0 to count s - 1 do
      if s.flags.(i) then begin
        if 0 < !nsub then str := !str ^ ",";
        nsub := 1 + !nsub;
        str := !str ^ (string_of_int i) ^ "~>" ^ (Term.to_string s.args.(i))
      end
    done;
    "[" ^ !str ^ "]"


  let sub_star (t:term) (s:t): term =
    (* Apply to the term [t] the substitution [s] until no more substitutions
       are possible.  *)
    let cnt = count s in
    let rec gstar (i:int) (n:int): term =
      (* n: number of substitutions still possible *)
      assert (0 < n);
      if s.flags.(i) then sub (get i s) (n-1)
      else                Variable i
    and sub (t:term) (n:int): term =
      match t with
        Variable j when j < cnt -> gstar j n
      | Variable _ -> t
      | Application (c,args) ->
          Application (sub c n, Array.map (fun t -> sub t n) args)
      | Lam (n,nms,t) ->
          Lam (n,nms, sub t n)
    in
    sub t cnt


  let get_star (i:int) (s:t): term =
    (* Get the [i]th substitution term and apply the substitution [s] until no
       more substitutions are possible.  *)
    assert (i < count s);
    sub_star (get i s) s




  let anchor (i:int) (s:t): int =
    (* Find the anchor of the type variable [i] following substitutions until
       there is no more substitution or the substitution is no type variable. *)
    assert (i < count s);
    let cnt = count s
    in
    let rec find (i:int) (n:int): int =
      assert (n <= cnt);  (* infinite recursion breaker *)
      if not s.flags.(i) then
        i
      else
        let t = s.args.(i) in
        match t with
          Variable j when j < cnt ->
            find j (n+1)
        | _ -> i
    in
    find i 0




  let add_new (i:int) (t:term) (s:t): unit =
    (* Add the new substitution [i~>t] to the substitutions [s]. Raise
       [Not_found] if the insertion would create circularity *)
    assert (not (has i s));
    let cnt = count s in
    assert (i < cnt);
    let used = Term.bound_variables t cnt in
    let lst = IntSet.fold
        (fun j lst ->
          if i=j || is_used i j s then
            raise Not_found
          else
            j::lst)
        used []
    in
    s.args.(i)  <- t;
    s.flags.(i) <- true;
    s.used.(i)  <- lst



  let set_of_list (lst:int list): IntSet.t =
    List.fold_left
      (fun set i -> IntSet.add i set)
      IntSet.empty
      lst


  let update (i:int) (t:term) (s:t): unit =
    (* Update the [i]th substitution with [i~>t]. Raise [Not_found] if the new
       term [t] uses different type variables than the already existing
       term. *)
    assert (i < count s);
    assert (has i s);
    let used = Term.bound_variables t (count s) in
    let set  = set_of_list s.used.(i)
    in
    if set = used then
      s.args.(i) <- t
    else
      raise Not_found


  let up_above_top (n:int) (s:t): t =
    (* Shift all variables above the top in the substitutions up by [n]. This
        is necessary because new formal generics can be introduced.  *)
    if n = 0 then
      s
    else begin
      let args = Array.copy s.args
      and cnt  = count s
      in
      for i = 0 to cnt - 1 do
        args.(i) <- Term.upbound n cnt args.(i)
      done;
      {args = args; flags = s.flags; used = s.used}
    end


  let down_above_top (n:int) (s:t): t =
    (* Shift all variables above the top in the substitutions down by [n]. This
        is necessary because formal generics can be removed.  *)
    if n = 0 then
      s
    else begin
      let args = Array.copy s.args
      and cnt  = count s
      in
      for i = 0 to cnt - 1 do
        try
          args.(i) <- Term.down_from n cnt args.(i)
        with Term_capture ->
          assert false (* cannot happen *)
      done;
      {args = args; flags = s.flags; used = s.used}
    end


  let add_top (n:int) (s:t): t =
    (** Introduce [n] new variables at the top, i.e. all substitution terms
        above [count s] are shifted up by [n] and just copied into the new
        larger substitution.
     *)
    let sn   = count s in
    let args = Array.map (fun t -> Term.upbound n sn t) s.args in
    let snew = make (n+sn) in
    Array.blit args    0  snew.args  0  sn;
    Array.blit s.flags 0  snew.flags 0  sn;
    Array.blit s.used  0  snew.used  0  sn;
    snew


  let add_bottom (n:int) (s:t): t =
    (** Introduce [n] new variables at the bottom, i.e. shift all
        terms up by [n].
     *)
    let sn   = count s in
    let snew = make (n+sn) in
    for i = 0 to sn-1 do
      snew.args.(i+n) <- Term.up n s.args.(i);
      snew.used.(i+n) <- List.map (fun j -> j+n) s.used.(i)
    done;
    Array.blit s.flags 0 snew.flags n  sn;
    snew



  let remove_bottom (n:int) (s:t): t =
    (** Remove [n] variables from the bottom, i.e. shift all terms down by
        [n].  *)
    let sn = count s in
    assert (n <= sn);
    let args_bot = Array.sub s.args 0 n
    and snew = make (sn-n) in
    Array.blit s.flags n   snew.flags 0   (sn-n);
    for i = 0 to sn-n-1 do
      if snew.flags.(i) then begin
        let tp   = Term.sub s.args.(i+n) args_bot n in
        let tp   =
          try Term.down n tp
          with Not_found -> assert false
        in
        let used = Term.bound_variables tp (sn-n) in
        let lst  = IntSet.fold (fun j lst -> j::lst) used [] in
        snew.args.(i) <- tp;
        snew.used.(i) <- lst
      end
    done;
    snew

  let subs (s:t): (int*term*term) list =
    let lst = ref []  in
    for i = 0 to count s - 1 do
      if not s.flags.(i) then
        ()
      else
        lst := (i, s.args.(i), get_star i s) :: !lst
    done;
    List.rev !lst
  end (* Term_sub_arr *)






module TVars_sub: sig

  type t
  val empty:        t
  val count_fgs:    t -> int
  val count_all:    t -> int
  val fgconcepts:   t -> type_term array
  val fgnames:      t -> int array
  val has_fg:       int -> t -> bool
  val count:        t -> int
  val has:          int -> t -> bool
  val get:          int -> t -> term
  val count_global: t -> int
  val count_local:  t -> int
  val concept:      int -> t -> term
  val concepts:     t -> term array
  val tvars:        t -> Tvars.t
  val sub:          t -> Term_sub_arr.t
  val args:         t -> term array
  val add_sub:      int -> term -> t -> unit
  val update_sub:   int -> term -> t -> unit
  val add_fgs:      int -> t -> t -> t
  val add_global:   type_term array -> t -> t
  val add_local:    int -> t -> t
  val remove_local: int -> t -> t
  val augment:      int -> int array -> type_term array -> t -> t
  val update_subs:  t -> t -> unit
  val sub_star:     term -> t -> term
      (** [sub_star t s]: applies to the term [t] the substitution [s] until no
          more substitutions are possible.  *)

  val get_star:       int -> t -> term
    (** [get_star i s] gets the [i]th substitution term and applies the
        substitution [s] until no more substitutions are possible.  *)

  val anchor:       int -> t -> int

  val subs: t -> (int*term*term) list
end = struct

  type t = {vars: Tvars.t;
            sub:  Term_sub_arr.t}

  let empty: t =
    {vars = Tvars.empty; sub = Term_sub_arr.empty}

  let count_fgs (tvs:t): int =
    Tvars.count_fgs tvs.vars

  let fgconcepts (tvs:t): type_term array =
    Tvars.fgconcepts tvs.vars

  let fgnames (tvs:t): int array =
    Tvars.fgnames tvs.vars

  let has_fg (name:int) (tvs:t): bool =
    Tvars.has_fg name tvs.vars

  let count (tvars:t): int = Tvars.count tvars.vars

  let has (i:int) (tvars:t): bool =
    Term_sub_arr.has i tvars.sub

  let get (i:int) (tvars:t): term =
    assert (i < (count tvars));
    Term_sub_arr.get i tvars.sub

  let get_star (i:int) (tvars:t): term =
    assert (i < (count tvars));
    Term_sub_arr.get_star i tvars.sub

  let anchor (i:int) (tvars:t): int =
    assert (i < (count tvars));
    Term_sub_arr.anchor i tvars.sub

  let count_global (tv:t): int =
    Tvars.count_global tv.vars

  let count_local (tv:t): int =
    Tvars.count_local tv.vars

  let count_all (tv:t): int =
    Tvars.count_all tv.vars

  let concept (i:int) (tv:t): term =
    assert (count_local tv <= i);
    assert (i < count_all tv);
    Tvars.concept i tv.vars

  let concepts (tv:t): term array = Tvars.concepts tv.vars

  let tvars (tv:t): Tvars.t = tv.vars

  let sub (tv:t): Term_sub_arr.t = tv.sub


  let add_sub (i:int) (t:term) (tv:t): unit =
    assert (not (has i tv));
    Term_sub_arr.add_new i t tv.sub

  let update_sub (i:int) (t:term) (tv:t): unit =
    Term_sub_arr.update i t tv.sub


  let args (tv:t): term array = Term_sub_arr.args tv.sub

  let add_fgs (nfgs:int) (tv_new:t) (tv:t): t =
    let n = count_fgs tv_new - count_fgs tv in
    assert (n = nfgs);
    {vars = Tvars.add_fgs nfgs tv_new.vars tv.vars;
     sub  = Term_sub_arr.up_above_top n tv.sub}

  let add_global (cs:type_term array) (tv:t): t =
    {vars = Tvars.add_global cs tv.vars;
     sub  = Term_sub_arr.add_top (Array.length cs) tv.sub}

  let add_local (n:int) (tv:t): t =
    (** Add [n] local (fresh) type variables without constraints to [tv]
        and shift all type variables up by [n].
     *)
    {vars = Tvars.add_local n tv.vars;
     sub  = Term_sub_arr.add_bottom n tv.sub}

  let remove_local (n:int) (tv:t): t =
    (** Remove [n] local type variables (without constraints) from [tv] and
        shift all type variables down by [n].
     *)
    {vars = Tvars.remove_local n tv.vars;
     sub  = Term_sub_arr.remove_bottom n tv.sub}

  let augment
      (ntvs:int)
      (fgnames: int array)
      (fgconcepts:type_term array)
      (tv:t): t =
    let n  = Array.length fgnames in
    assert (n = Array.length fgconcepts);
    let tv = add_local ntvs tv in
    {vars = Tvars.augment_fgs fgnames fgconcepts tv.vars;
     sub  = Term_sub_arr.up_above_top n tv.sub}



  let update_subs (tv:t) (tvnew:t): unit =
    (* Update the type variables in [tv] with the type variables in [tvnew].

       This requires that [tv] and [tvnew] have the same number of local type
       variables and formal generics and [tvnew] might have more globals than
       [tv]

       tv:    loc              fgs
       tvnew: loc  glob   garb fgs
     *)
    assert (count tv     <= count tvnew);
    assert (count_fgs tv <= count_fgs tvnew);
    assert (count_local tv = count_local tvnew);
    assert (count_global tv = 0);
    let nloc  = count_local tv
    and nglob = count_global tvnew
    and ngarb = count_fgs tvnew - count_fgs tv
    in
    let ndown = nglob + ngarb in
    for i=0 to nloc-1 do
      if Term_sub_arr.has i tvnew.sub &&
        not (Term_sub_arr.has i tv.sub)
      then
        Term_sub_arr.add_new
          i
          (Term.down_from ndown nloc (get_star i tvnew))
          tv.sub
      else
        assert ((get i tv) = (Term.down_from ndown nloc (get_star i tvnew)))
    done
    (*assert (count tv <= count tvnew);
    assert (count_local tv = count_local tvnew);
    assert (count_global tv = 0);
    assert ((count_fgs tv) = (count_fgs tvnew));
    let nloc  = count_local tv
    and ndown = (count_global tvnew) - (count_global tv)
    in
    for i=0 to nloc-1 do
      if Term_sub_arr.has i tvnew.sub &&
        not (Term_sub_arr.has i tv.sub)
      then
        Term_sub_arr.add_new
          i
          (Term.down_from ndown nloc (get_star i tvnew))
          tv.sub
      else
        assert ((get i tv) = (Term.down_from ndown nloc (get_star i tvnew)))
    done*)


  let sub_star (t:type_term) (s:t): term =
    Term_sub_arr.sub_star t s.sub

  let get_star (i:int) (s:t): term =
    Term_sub_arr.get_star i s.sub

  let subs (s:t): (int*term*term) list = Term_sub_arr.subs s.sub

end (* TVars_sub *)



module Result_type: sig

  type t
  val empty:        t
  val normal:       t -> t
  val make_func:    type_term -> t
  val make_ghost:   type_term -> t
  val make_proc:    type_term -> t
  val make:         type_term -> bool -> bool -> t
  val has_result:   t -> bool
  val result:       t -> type_term
  val is_procedure: t -> bool
  val is_ghost:     t -> bool
  val to_ghost:     t -> t
  val up_from:      int -> int -> t -> t
  val up:           int -> t -> t
  val sub:          t -> type_term array -> int -> t
  val involved_classes: Tvars.t -> t -> IntSet.t
  val transform:    (type_term->type_term) -> t -> t
end = struct

  type t = (type_term * bool * bool) option
  let empty = None
  let make_func (tp:type_term): t = Some (tp,false,false)
  let make_ghost(tp:type_term): t = Some (tp,false,true)
  let make_proc (tp:type_term): t = Some (tp,true,false)
  let make (tp:type_term) (proc:bool) (ghost:bool): t = Some (tp,proc,ghost)

  let normal (rt:t): t =
    match rt with
      None -> rt
    | Some(tp,_,_) -> Some(tp,false,false)

  let has_result (rt:t): bool = Option.has rt

  let result(rt:t): type_term =
    assert (has_result rt);
    match rt with
      None -> assert false
    | Some (tp,_,_) -> tp

  let  is_procedure (rt:t): bool =
    match rt with
      None            -> true
    | Some (_,proc,_) -> proc

  let is_ghost (rt:t): bool =
    match rt with
      None             -> false
    | Some (_,_,ghost) -> ghost

  let to_ghost (rt:t): t =
    assert (has_result rt);
    match rt with
      None -> assert false
    | Some (tp,proc,ghost) -> Some (tp,proc,true)

  let up_from (n:int) (start:int) (rt:t): t =
    match rt with
      None -> None
    | Some (tp,proc,ghost) -> Some (Term.upbound n start tp, proc, ghost)

  let up (n:int) (rt:t): t = up_from n 0 rt

  let sub (rt:t) (sub_arr:type_term array) (ntvs:int): t =
    match rt with
      None -> None
    | Some (tp,proc,ghost) -> Some(Term.sub tp sub_arr ntvs,proc,ghost)

  let involved_classes (tvs:Tvars.t) (rt:t): IntSet.t =
    match rt with
      None -> IntSet.empty
    | Some (tp,_,_)  ->
        Tvars.involved_classes tp tvs IntSet.empty

  let transform (f:type_term->type_term) (rt:t): t =
    match rt with
      None -> None
    | Some (tp,proc,ghost) ->
        Some(f tp, proc, ghost)
end





module Sign: sig
  type t
  val empty:       t
  val make:        type_term array -> Result_type.t -> t
  val make_func:   type_term array -> type_term -> t
  val make_ghost:  type_term array -> type_term -> t
  val make_proc:   type_term array -> type_term -> t
  val make_const:  type_term -> t
  val make_args:   type_term array -> t
  val normal:      t -> t
  val to_string:   t -> string
  val arity:       t -> int
  val is_constant: t -> bool
  val arguments:   t -> type_term array
  val arg_type:    int -> t -> type_term
  val argument:    int -> t -> t
  val result_type: t -> Result_type.t
  val has_result:  t -> bool
  val is_binary:   t -> bool
  val is_unary:    t -> bool
  val result:      t -> type_term
  val is_procedure:t -> bool
  val is_ghost:    t -> bool
  val to_ghost:    t -> t
  val up_from:     int -> int -> t -> t
  val up:          int -> t -> t
  val up2:         int -> int -> int -> t -> t
  val to_function: int -> t -> t
  val sub:         t -> type_term array -> int -> t
  val substitute:  t -> TVars_sub.t -> t
  val involved_classes_arguments: Tvars.t -> t -> IntSet.t
  val involved_classes: Tvars.t -> t -> IntSet.t
  val transform:   (type_term->type_term) -> t -> t
end = struct

  type t = {args: type_term array;
            rt:   Result_type.t}

  let empty: t = {args = [||]; rt = Result_type.empty (*result = None*)}

  let make (args: type_term array) (rt:Result_type.t): t =
    {args = args; rt = rt}

  let make_func (args: type_term array) (result:type_term): t =
    {args = args; rt = Result_type.make_func result}

  let make_ghost (args: type_term array) (result:type_term): t =
    {args = args; rt = Result_type.make_ghost result}

  let make_args (args: type_term array): t =
    {args = args; rt = Result_type.empty}

  let make_const (result:type_term): t =
    {args = [||]; rt = Result_type.make_func result}

  let make_proc (args: type_term array) (result:type_term): t =
    {args = args; rt = Result_type.make_proc result}

  let normal (s:t): t = make s.args (Result_type.normal s.rt)

  let arity (s:t): int = Array.length s.args

  let is_constant (s:t): bool = (arity s) = 0

  let arguments (s:t): type_term array = s.args

  let arg_type (i:int) (s:t): type_term =
    assert (i < (arity s));
    s.args.(i)

  let argument (i:int) (s:t): t =
    assert (i < (arity s));
    make_func [||] s.args.(i)

  let result_type (s:t): Result_type.t = s.rt

  let has_result (s:t): bool = Result_type.has_result s.rt

  let is_binary (s:t): bool = (has_result s) && ((arity s) = 2)
  let is_unary  (s:t): bool = (has_result s) && ((arity s) = 1)

  let result (s:t): type_term =
    assert (has_result s);
    Result_type.result s.rt

  let is_procedure (s:t): bool = Result_type.is_procedure s.rt

  let is_ghost     (s:t): bool = Result_type.is_ghost     s.rt

  let to_ghost (s:t): t =
    assert (has_result s);
    {s with rt = Result_type.to_ghost s.rt}

  let to_string (s:t): string =
    let argsstr =
      if (arity s) = 0 then ""
      else
        "("
        ^ (String.concat
             ","
             (List.map Term.to_string (Array.to_list s.args)))
        ^ ")"
        ^ (if has_result s then ":" else "")
    and retstr =
      if has_result s then Term.to_string (result s)
      else ""
    in
    argsstr ^ retstr

  let up_from (n:int) (start:int) (s:t): t =
    (** Shift all types up by [n] starting from [start].
     *)
    {args = Array.map (fun t -> Term.upbound n start t) s.args;
     rt   = Result_type.up_from n start s.rt}


  let up (n:int) (s:t): t =
    (** Shift all types up by [n].
     *)
    up_from n 0 s


  let up2 (n1:int) (start:int) (n2:int) (s:t): t =
    (** Shift all types up by [n1] starting from type [start] and then
        shift all types up by [n2] i.e. the operation creates a hole
        of [n1] starting from [start+n2] and a hole of [n2] starting from
        0.
     *)
    up n2 (up_from n1 start s)



  let to_function (nargs:int) (s:t): t =
    (** Convert the constant signature [s] into a function signature with
        [nargs] arguments. The [nargs] argument types are fresh type variables.
     *)
    assert (has_result s);
    assert (is_constant s);
    {s with args   = Array.init nargs (fun i -> Variable i)}

  let sub (s:t) (sub_arr:type_term array) (ntvs:int): t =
    let args = Array.map (fun tp -> Term.sub tp sub_arr ntvs) s.args
    and rt   = Result_type.sub s.rt sub_arr ntvs in
    make args rt

  let substitute (s:t) (tvars_sub:TVars_sub.t): t =
    let args = TVars_sub.args tvars_sub in
    let ntvs = Array.length args in
    sub s args ntvs


  let involved_classes_arguments (tvs:Tvars.t) (s:t): IntSet.t =
    Array.fold_left
      (fun set tp ->
        Tvars.involved_classes tp tvs set)
      IntSet.empty
      s.args

  let involved_classes (tvs:Tvars.t) (s:t): IntSet.t =
    let set = Result_type.involved_classes tvs s.rt in
    Array.fold_left
      (fun set tp ->
        Tvars.involved_classes tp tvs set)
      set
      s.args

  let transform (f:type_term->type_term) (s:t): t =
    let args = Array.map f s.args
    and rt   = Result_type.transform f s.rt in
    make args rt
end (* Sign *)
