open Support
open Container
open Type
open Term
open Proof


type descriptor = {
    names: int array;
    types: typ array;
    term:  term;
    nterm: term;
    chain: (term list * term) list;
    fwd_opt: term option;
    elim_opt: term option; (* !!! *)
    pt_opt: proof_term option}

type t  = {seq: descriptor seq}


let count (at:t): int = Seq.count at.seq

let assertion_to_string
    (d:descriptor)
    (ct:Class_table.t)
    (ft:Feature_table.t): string =
  "all"
  ^ (Class_table.arguments_to_string d.names d.types ct)
  ^ " "
  ^ (Feature_table.term_to_string d.term d.names ft)


let to_string
    (i:int)
    (ct:Class_table.t)
    (ft:Feature_table.t)
    (at:t): string =
  assert (i < Seq.count at.seq);
  assertion_to_string (Seq.elem at.seq i) ct ft



(* Public functions *)

let empty (): t =  {seq = Seq.empty () }

let find_backward
    (t:term)
    (nb:int)
    (ft:Feature_table.t)
    (at:t)
    : (proof_pair * int) list =
  (* Find a list of proof pairs such that the term has the form

         'a=>b=>...=>t'         (the set of premises might be empty)

     The proof term has the form

         Specialize (Theorem idx, args)

     which proves ass[idx](args) = (a=>b=>...=>t)
   *)
  let res = ref []
  in
  begin
    Seq.iteri
      (fun i desc ->
        let n = Array.length desc.types in
        List.iter
          (fun (premises,target) ->
            (*if premises=[] then*)
              try
                let args,flags = Term.unify t nb target n in
                let tt = Term.sub desc.nterm args nb in
                res := ((tt,Specialize (Theorem i, args)),i) :: !res
              with Not_found ->
                ()
            (*else
              ()*)
          )
          desc.chain
      )
      at.seq
  end;
  !res






let consequences (t:term) (nb:int) (ft:Feature_table.t) (at:t)
    :(proof_pair * int) list * (term * int * term array * int) list =
  (* The direct consequences of the term 't' in an enviroment with 'nb' bound
     variables, i.e. if the assertion table has a proved assertion of the form
     'a=>b' and 'a' can be unified with the term 't' and 'b' is not more
     complex than 'a' then 'b' transformed into the environment of term 't'
     is a direct consequence of 't'.

     a) direct consequences
         If

              ass[idx](args) = (t=>u)

         then the proof pair is

              t=>u, Specialize (Theorem idx, args)

     b) eliminations

          There is a an assertion variable i and arguments args so
          that

          for all c
              args.(nb_ass-1-i ) <- c
              ass[idx](args) = (t => ... => c)

          ass[idx], i, args, idx
   *)
  let res  = ref []
  and res2 = ref []
  in
  begin
    Seq.iteri
      (fun i desc ->
        let n = Array.length desc.types in
        begin
          match desc.fwd_opt with
            None -> ()
          | Some fwd ->
              try
                let args,_ = Term.unify t nb fwd n in
                let tt = Term.sub desc.nterm args nb in
                res := ((tt,Specialize (Theorem i, args)),i) :: !res
              with Not_found ->
                ()
        end;
        begin
          match desc.elim_opt with
            None -> ()
          | Some elim ->
              try
                let args,arbitrary = Term.unify t nb elim n in
                match arbitrary with
                  [tgt_var] ->
                    res2 :=
                      ((Seq.elem at.seq i).term, i, args, tgt_var)
                      :: !res2
                | _ ->
                    assert false (* Cannot happen *)
              with Not_found ->
                ()
        end
      )
      at.seq
  end;
  !res, !res2







let put_assertion
    (names: int array)
    (types: typ array)
    (term:  term)
    (pt_opt: proof_term option)
    (ft:    Feature_table.t)
    (at:    t)
    : unit =
  let nb  = Array.length types in
  let nterm = Feature_table.normalize_term term nb ft in
  let chn = Feature_table.implication_chain nterm nb ft in
  assert (chn<>[]);
  let chn2 =
    List.filter
      (fun (premises,target) ->
        let bvars_tgt = Term.bound_variables target nb
        and n_tgt     = Term.nodes target
        in
        List.for_all
          (fun p ->
           (p<>target) &&
            let bvars = Term.bound_variables p nb
            and n     = Term.nodes p
            in
            n <= n_tgt &&  (* Has to be refined to allow distributivity *)
            IntSet.subset bvars bvars_tgt
          )
          premises
      )
      chn
  in
  let fwd_opt =
    try
      let a,b = Feature_table.split_implication nterm nb ft in
      let bvars_a = Term.bound_variables a nb
      and bvars_b = Term.bound_variables b nb
      and n_a     = Term.nodes a
      and n_b     = Term.nodes b
      and distributes a b = false (* Algorithm needed for distributivity *)
      in
      if n_b <= n_a && a<>b && IntSet.subset bvars_b bvars_a then
        (Printf.printf "Simplification rule found\n";
         Some a)
      else if (Term.depth a) = (Term.depth b)
          && distributes a b then
        None
      else
        None
    with Not_found ->
      None
  in

  let elim_opt =
    let premises,target = List.hd (List.rev chn)
    in
    match premises with
      [] -> None
    | p0::tl -> begin
        let bvars_p0, fvars_p0  = Term.split_variables p0 nb
        and bvars_tgt,fvars_tgt = Term.split_variables target nb
        in
        let elim_vars (): IntSet.t =
          List.fold_left
            (fun set p ->
              IntSet.diff set (Term.free_variables p nb))
                (IntSet.diff fvars_p0 fvars_tgt)
            tl
        in
        match target with
          Variable i_tgt when
            not (IntSet.mem i_tgt bvars_p0)
              && (IntSet.cardinal bvars_p0) + 1 = nb
              && not (IntSet.is_empty (elim_vars ()))
          ->
            begin
              (Printf.printf "Elimination rule found\n";
               Some p0)
            end
        | _ ->
            None
    end
  in

  Seq.push
    at.seq
    {names    = names;
     types    = types;
     term     = term;
     nterm    = nterm;
     pt_opt   = pt_opt;
     chain    = chn2;
     fwd_opt  = fwd_opt;
     elim_opt = elim_opt}




let put_axiom
    (names: int array)
    (types: typ array)
    (term:  term)
    (ft:    Feature_table.t)
    (at:    t)
    : unit =
  (* Put an axiom into the table *)
  put_assertion names types term None ft at


let put_proved
    (names: int array)
    (types: typ array)
    (term:  term)
    (pt:    proof_term)
    (ft:    Feature_table.t)
    (at:    t)
    : unit =
  (* Put a proved assertion into the table *)
  put_assertion names types term (Some pt) ft at


let print (ct:Class_table.t) (ft:Feature_table.t) (at:t): unit =
  Seq.iter
    (fun desc -> Printf.printf "%s\n" (assertion_to_string desc ct ft))
    at.seq






(*
-----------------------------------------------------------------------------
   Experimental
-----------------------------------------------------------------------------
*)




module Term_sub: sig
  type t
end = struct
  type t = term IntMap.t

  let singleton (i:int) (t:term): t =
    IntMap.add i t IntMap.empty

  let find (i:int) (sub:t): term =
    IntMap.find i sub

  let mem (i:int) (sub:t): bool =
    IntMap.mem i sub

  let add (i:int) (t:term) (sub:t): t =
    assert (not (mem i sub));
    assert false
end




module Term_table: sig
end = struct
  type substitution = term IntMap.t

  type table = {
      bvar: int  IntMap.t;  (* idx -> argument variable *)
      ovar: int  IntMap.t;  (* idx -> other variable (free or bound) *)
      fapp: (table * table array) IntMap.t;
      lam:  (typ array * table) IntMap.t
    }

  exception Term_found of term

  let has_index (idx:int) (tab:table): bool =
    (IntMap.mem idx tab.bvar) ||
    (IntMap.mem idx tab.ovar) ||
    (IntMap.mem idx tab.fapp) ||
    (IntMap.mem idx tab.lam)



  let empty_table = {
    bvar = IntMap.empty;
    ovar = IntMap.empty;
    fapp = IntMap.empty;
    lam  = IntMap.empty
  }


  let merge_sub (sub1: substitution) (sub2: substitution)
      : substitution =
    IntMap.fold
      (fun bvar t1 res ->
        try
          let t2 = IntMap.find bvar sub2 in
          if t1=t2 then res
          else raise Not_found  (* No merge possible *)
        with Not_found ->
          IntMap.add bvar t1 res
      )
      sub1 (* map to fold *)
      sub2 (* start map   *)



  let merge_map (m1: substitution IntMap.t) (m2: substitution IntMap.t)
      : substitution IntMap.t =
    IntMap.fold
      (fun idx sub1 res ->
        try
          let sub2 = IntMap.find idx m2 in
          let sub  = merge_sub sub1 sub2 in
          IntMap.add idx sub res
        with Not_found ->
          res
      )
      m1
      IntMap.empty




  let unify (t:term) (nbt:int) (tab:table)
      :  substitution IntMap.t =
    (* Return a set of term indices together with substitutions i.e. a mapping
       from the bound variables of the corresponding term to subterms of 't'.
     *)
    let rec uni (t:term) (nb:int) (tab:table): substitution IntMap.t =
      match t with
        Variable i when nb<=i && i<nbt ->
          (* The term 't' is an argument variable of the toplevel term to
             be unified *)
          IntMap.map
            (fun i2 ->
              IntMap.add i2 t (IntMap.empty)
            )
            tab.bvar
      | Variable i ->
          (* The term 't' is either a bound variable or a free variable of
             the toplevel term to be unified *)
          IntMap.fold
            (fun idx ovar res ->
              if ovar=i then
                IntMap.add idx IntMap.empty res
              else
                res
            )
            tab.ovar
            IntMap.empty
      | Application (f,args) ->
          let len = Array.length args in
          IntMap.fold
            (fun idx (ftab,argstab) res ->
              let lentab = Array.length argstab in
              if len=lentab then
                let fu = uni f nb ftab
                and argsu =
                  Array.mapi (fun i t -> uni t nb argstab.(i)) args
                in
                Array.fold_left
                  (fun res map -> merge_map res map)
                  fu
                  argsu
              else
                res
            )
            tab.fapp
            IntMap.empty
      | Lam(tarr,t) ->
          assert false; (* NYI: unification of lambda terms *)
    in

    uni t 0 tab


  let term (idx:int) (tab:table): term =
    let rec termrec (nb:int) (tab:table): term =
      let var_term (vmap: int IntMap.t): unit =
        try
          let i = IntMap.find idx vmap in
          raise (Term_found (Variable i))
        with Not_found ->
          ()
      and fapp_term (fappmap: (table * table array) IntMap.t): unit =
        try
          let ftab,argstab = IntMap.find idx fappmap in
          let f = termrec nb ftab
          and args = Array.map (fun tab -> termrec nb tab) argstab
          in
          raise (Term_found (Application (f,args)))
        with Not_found ->
          ()
      and lam_term (lammap: (typ array * table) IntMap.t): unit =
        try
          let tarr,tab = IntMap.find idx lammap in
          let n = Array.length tarr in
          let t = termrec (nb+n) tab in
          raise (Term_found (Lam (tarr,t)))
        with Not_found ->
          ()
      in
      try
        var_term  tab.bvar;
        var_term  tab.ovar;
        fapp_term tab.fapp;
        lam_term  tab.lam;
        raise Not_found
      with Term_found t ->
        t
    in
    termrec 0 tab

  let has_term (idx:int) (tab:table): bool =
    try
      let _ = term idx tab in
      true
    with Not_found ->
      false



  let rec add (t:term) (nbt:int) (idx:int) (tab:table): table =
    (* Add the term 't' which has 'nbt' bound variables and the index 'idx' to
       the table 'tab'.
     *)
    assert (not (has_term idx tab));
    let rec addrec (t:term) (nb:int) (tab:table): table =
      match t with
        Variable i when nb<=i && i<nb+nbt ->
          (* variable is a formal argument which can be substituted *)
            {tab with bvar = IntMap.add idx i tab.bvar}
      | Variable i ->
            {tab with ovar = IntMap.add idx i tab.ovar}
        (*
          if i<nb then
            assert false
          else if i<nbt then
            {tab with bvar = IntMap.add idx i tab.bvar}
          else
            {tab with ovar = IntMap.add idx (i-nbt) tab.ovar}*)
      | Application (f,args) ->
          let ftab = addrec f nb empty_table
          and argstab = Array.map (fun t -> addrec t nb empty_table) args
          in
          {tab with fapp = IntMap.add idx (ftab,argstab) tab.fapp}
      | Lam (tarr,t) ->
          let len = Array.length tarr in
          let ttab = addrec t (nb+len) empty_table in
          {tab with lam = IntMap.add idx (tarr,ttab) tab.lam}
    in
    let tab = addrec t 0 tab in
    assert (t = term idx tab);
    tab
end
