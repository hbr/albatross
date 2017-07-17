(*
  Induction law:

      all(p:{T},x:T) pp1 ==> pp2 ==> ... ==> x in p

      ppi: all(a1,...) cond ==> ra1 in p ==> ... ==> ci(a1,...) in p

          cond: optional and sometimes necessary to make the cases non overlap

      T must be in its most general form

  Case recognizer:

     all(x:T) exp = some(a1:A1,...) cond and x = ci(a1,...)

     Signature of ci: (A1,...): T in its most general form

  Projector:

     all(a1,.,aj:Aj,..) proj_ij(ci(a1,...)) = aj

     Signature of projector: T -> Aj

  Wellfounded induction law

      Form a:
      all(p:{T},y:T)
          (all(y) (all(x) x < y ==> x in p) ==> y in p)
          ==>
          y in p

      Form b:
      all(p:{T},y:T)
          (all(y) cond ==> y in p)
          ==>
          (all(y) not cond ==> (all(x) x < y ==> x in p) ==> y in p)
          ==>
          y in p

 *)

open Term
open Container
open Signature
open Printf

let is_tracing (ft:Feature_table.t): bool =
  Feature_table.verbosity ft > 1


let has_all_recursive_arguments
      (rec_args:IntSet.t)
      (c:int)
      (args: term array)
      (fc:Feature_context.t)
    : bool =
  (* Are all recursive arguments of [c] contained in recargs? *)
  let ft = Feature_context.feature_table fc
  and nargs = Array.length args
  and nvars = Feature_context.count_variables fc in
  let tvs,s = Feature_table.signature0 (c-nvars) ft in
  assert (Sign.has_result s);
  let rt = Sign.result s in
  interval_for_all
    (fun i ->
      if Term.equivalent (Sign.arg_type i s) rt then
        match args.(i) with
        | Variable j when j < nargs ->
          IntSet.mem j rec_args
        | _ ->
           assert false (* cannot happen *)
      else
        true
    )
    0 (Sign.arity s)


let split_constructor_rule (pp:term) (fc:Feature_context.t): term list * int =
  (* Check if [pp] is a constructor rule of the form

         all(a1,...) pp1 ==> ... ==> c(a1,...) in p

     where each premise ppi is either a general condition not containing [p]
     or has the form [rai in p] where [rai] is a recursive argument of the
     constructor [c]. In case of success return the list of preconditions and
     the constructor. Otherwise raise Not_found.
   *)
  let open Feature_context in
  let n,(nms,tps),(fgnms,fgtps),ps_rev,t0 =
    split_general_implication_chain pp fc
  in
  if Array.length fgtps > 0 then
    raise Not_found;
  let fc1 = push nms tps fgnms fgtps fc in
  match t0 with
  | Application(Variable n,[|VAppl(c,args,_,_)|],_)
       when Term.is_permutation args
            && Array.length args = n ->
     let pres,recargs =
       List.fold_left
         (fun (pres,recargs) pp ->
           match pp with
           | Application (Variable n,[|Variable rai|],_) when rai < n ->
              if IntSet.mem rai recargs then
                raise Not_found;
              pres, IntSet.add rai recargs
           | _ ->
              (* extract a precondition *)
              if Term.is_all_quantified pp then
                raise Not_found;
              try
                let pre = Term.shift_from (-2) n 0 0  pp in
                pre :: pres, recargs
              with Term_capture ->
                raise Not_found
         )
         ([],IntSet.empty)
         ps_rev
     in
     if has_all_recursive_arguments recargs c args fc1 then
       pres, c - count_variables fc1
     else
       raise Not_found;
  | _ ->
     raise Not_found





let put_potential_induction_law
      (idx:int) (t:term) (ps_rev: term list) (fc:Feature_context.t)
    : unit =
  (* A law of the form

         all(p,x) pp1 ==> ... ==> x in p has been

     encountered. Analyze if its a normal induction law i.e. that each
     premise in [ps_rev] is a constructor rule of the form

         all(a1,..) cond ==> ra1 in p ==> ... ==> c(a1,...) in p

     Note: - [p] is always the variable 0 and [x] the variable 1 in the
             context.
           - multiple preconditions might occur

    In case of a normal induction law store the law index and the constructors
    as an induction law within the corresponding class and mark the
    constructors.  *)
  try
    let open Feature_context in
    let tp = variable_type 1 fc in
    let cls = Tvars.principal_class tp (tvars fc) in
    let lst =
      List.fold_left
        (fun lst pp ->
          let pres,c = split_constructor_rule pp fc in
          if List.for_all (fun (_,c0) -> c <> c0) lst then
            (pres,c) :: lst
          else
            raise Not_found
        )
        []
        ps_rev
    in
    if is_tracing (feature_table fc) then
      begin
        printf "\nnormal induction law\n";
        printf "   %s\n\n" (string_of_term t (pop fc));
      end;
    let ct = Feature_context.class_table fc in
    Class_table.add_induction_law idx lst cls ct
  with Not_found ->
    ()





let recognizer_condition_constructor
      (t:term) (n:int) (ft:Feature_table.t)
    : term option * int =
  (* Try to match [t] with one of

         x = c(a1,...)
         cond and x = c(a1,...)

     which is the inner part of

         all(x) exp = some(a1,...) t

     in case of success return the optional condition and the
     constructor. Otherwise raise Not_found.
   *)
  let constructor (t:term): int =
    (* Find x = c(a1,...) *)
    match t with
    | VAppl(eq, [|Variable n;VAppl (c,args,_,_)|],_,_)
         when is_standard_substitution args
              && not (Feature_table.is_ghost_function (c-1-n) ft) ->
       c - 1 - n
    | VAppl(eq, [|VAppl (c,args,_,_);Variable n|],_,_)
         when is_standard_substitution args
              && not (Feature_table.is_ghost_function (c-1-n) ft) ->
       c - 1 - n
    | _ ->
       raise Not_found
  in
  try
    None, constructor t
  with Not_found ->
       match t with
       | VAppl(andidx, [|cond;c|], _, _)
            when andidx = Constants.and_index+1+n ->
          Some cond, constructor c
       | _ ->
          raise Not_found








let put_assertion (idx:int) (t:term) (ft:Feature_table.t): unit =
  (* Analyze the assertion [t] which has been entered at [idx]. Find out if it
     is an induction law, it defines a projector or it defines a case recognizer
     and store the corresponding information. *)
  let n,(nms,tps),(fgnms,fgtps),ps_rev,t0 =
    Term.split_general_implication_chain t Constants.implication_index
  in
  let fc = Feature_context.make_from_arguments nms tps fgnms fgtps ft
  in
  (* Induction law all(p,x) pp1 ==> pp2 ==> ... ==> x in p *)
  match t0 with
  | Application(Variable 0, [|Variable 1|],_)
       when n = 2
            && ps_rev <> []
            && List.for_all
                 (fun pp ->
                   try (* premises must not contain the induction variable *)
                     ignore(Term.shift_from (-1) 1 0 0 pp);
                     true
                   with Term_capture ->
                        false)
                 ps_rev
    ->
     put_potential_induction_law idx t ps_rev fc

  (* Projector all(a1,..) proj_ij(ci(a1,..) = aj *)
  | VAppl(eq,[|VAppl(proj,[|VAppl(c,cargs,_,_)|],_,_);Variable i|],_,_)
       when ps_rev = []
            && proj <> c
            && i < n
            && Feature_table.is_equality_index (eq - n) ft
            && not (Feature_table.is_ghost_function (proj - n) ft)
            && not (Feature_table.is_ghost_function (c - n) ft)
            && is_standard_substitution cargs ->
     if is_tracing ft then
       begin
         let open Feature_table in
         printf "\nprojector found\n";
         printf "   constructor: %s\n" (string_of_signature (c-n) ft);
         printf "   projector:   %s\n" (string_of_signature (proj-n) ft);
         printf "   variable:    %d\n\n" i
       end;
     Feature_table.set_projector (proj-n) i (c-n) ft;

  (* Case recognizer: all(x) exp = some(a1,...) cond and c(a1,...) *)
  | VAppl(eq,[|exp; QExp(n2,(nms2,tps2),(fgnms2,fgtps2),t02,false)|],_,_)
       when n = 1
            && ps_rev = []
            && Feature_table.is_equality_index (eq - n) ft
            && not (Feature_table.is_ghost_term exp n ft) ->
     begin
       try
         let cond,c = recognizer_condition_constructor t02 n2 ft in
         if is_tracing ft then
           begin
             let open Feature_context in
             let open Feature_table in
             printf "\nrecognizer found for %s\n" (string_of_signature c ft);
             printf "  recognizer     %s\n" (string_of_term exp fc);
             printf "  equivalent to  %s\n\n"
                    (string_of_term
                       (QExp(n2,(nms2,tps2),(fgnms2,fgtps2),t02,false))
                       fc);
           end;
         Feature_table.set_recognizer exp cond c ft
       with Not_found ->
            ()
     end
  | _ ->
     ()
