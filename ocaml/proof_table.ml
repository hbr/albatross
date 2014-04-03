open Term
open Container


type proof_term =
    Axiom      of term
  | Assumption of term
  | Detached   of int * int  (* modus ponens *)
  | Specialize of int * term array
  | Subproof   of int        (* nargs *)
        * int array  (* used  *)
        * int        (* res *)
        * proof_term array

type desc = {nbenv0:     int;
             term:       term;
             proof_term: proof_term}

type entry = {nbenv:  int;
              names:  int array;
              imp_id: int;
              all_id: int;
              mutable count:   int;
              mutable req:     int list}

type t = {seq: desc Seq.sequence;
          mutable entry: entry;
          mutable stack: entry list}

let depth (at:t): int =
  List.length at.stack

let is_global (at:t): bool =
  at.stack = []

let is_local (at:t): bool =
  not (is_global at)

let is_toplevel (at:t): bool =
  Mylist.is_singleton at.stack

let count (at:t): int =
  Seq.count at.seq


let count_previous (at:t): int =
  if is_global at then
    0
  else
    (List.hd at.stack).count


let nbenv (at:t): int = at.entry.nbenv

let nbenv_local (at:t): int =
  at.entry.nbenv - if at.stack = [] then 0 else (List.hd at.stack).nbenv

let names (at:t): int array =
  at.entry.names

let imp_id (at:t): int =
  at.entry.imp_id

let all_id (at:t): int =
  at.entry.all_id

let make (imp_id:int) (all_id:int): t =
  {seq   = Seq.empty ();
   entry = {count   = 0;
            names   = [||];
            nbenv   = 0;
            req     = [];
            imp_id  = imp_id;
            all_id  = all_id};
   stack = []}


let push (nbenv:int) (names: int array) (at:t): unit =
  assert (let len = Array.length names in len=0 || len=nbenv);
  at.entry.count <- Seq.count at.seq;
  at.stack       <- at.entry :: at.stack;
  at.entry       <-
    {at.entry with
     nbenv  = at.entry.nbenv + nbenv;
     names  = names;
     imp_id = at.entry.imp_id + nbenv;
     all_id = at.entry.all_id + nbenv}


let pop (at:t): unit =
  assert (is_local at);
  at.entry  <- List.hd at.stack;
  at.stack  <- List.tl at.stack;
  Seq.keep at.seq at.entry.count


let implication (i:int) (at:t): term =
  (** The [i]th term of the current environment with all assumptions
      discharged.
   *)
  List.fold_left
    (fun term i_req ->
      Term.binary
        at.entry.imp_id
        (Seq.elem at.seq i_req).term
        term)
    (Seq.elem at.seq i).term
    at.entry.req



let local_term (i:int) (at:t): term =
  (** The [i]th proved term in the local environment.
   *)
  assert (i < count at);
  let desc = Seq.elem at.seq i in
  let n_up = at.entry.nbenv - desc.nbenv0
  in
  Term.up n_up desc.term




let add (t:term) (pt:proof_term) (at:t): unit =
  (** Add the term [t] and its proof term [pt] to the table.
   *)
  let raw_add () =
    Seq.push at.seq {nbenv0 = at.entry.nbenv;
                     term   = t;
                     proof_term = pt}
  in
  match pt with
    Assumption _ ->
      let idx = count at in
      raw_add ();
      at.entry.req     <- idx :: at.entry.req;
  | _ -> raw_add ()



let add_axiom (t:term) (at:t): unit =
  add t (Axiom t) at

let add_assumption (t:term) (at:t): unit =
  add t (Assumption t) at



let rec term_of_pt (pt:proof_term) (at:t): term =
  (** Construct a term from the proof term [pt].
   *)
  let seq = at.seq in
  let cnt = Seq.count seq in
  match pt with
    Axiom t  -> t
  | Assumption t -> t
  | Detached (a,b) ->
      if cnt <= a || cnt <= b then raise Not_found;
      let ta = local_term a at
      and tb = local_term b at
      in
      let b1,b2 = Term.binary_split tb (imp_id at) in
      if ta <> b1 then raise Not_found
      else b2
  | Specialize (i,args) ->
      if cnt <= i then raise Not_found;
      let nargs = Array.length args
      and t = local_term i at
      in
      let n,nms,t0 = Term.quantifier_split t (all_id at) in
      let tsub =
        if n < nargs then raise Not_found
        else Term.part_sub t0 n args 0
      in
      if nargs < n then
        let imp_id0 = (imp_id at)           in
        let imp_id1 = imp_id0 + (n-nargs)   in
        let a,b = Term.binary_split tsub imp_id1 in
        Term.binary
          imp_id0
          (try Term.down (n-nargs) a
          with Term_capture -> raise Not_found)
          (Term.quantified
             (all_id at)
             (n-nargs)
             (Array.sub nms nargs (n-nargs))
             b)
      else
        tsub
  | Subproof (nargs,used,res_idx,pt_arr) ->
      push nargs [||] at;
      let pt_len = Array.length pt_arr
      in
      if pt_len <= res_idx then raise Not_found;
      Array.iter
        (fun pt -> add (term_of_pt pt at) pt at)
        pt_arr;
      let term = implication res_idx at in
      pop at;  (* bug: verify that no unused argument has
                  been used in the proof terms! *)

      if used <> (Term.used_args term nargs) then
        raise Not_found;
      let term = Term.keep_used used term nargs in
      let nused = Array.length used             in
      if nused = 0 then
        term
      else
        Term.quantified (all_id at) nused [||] term



let rec used_assertions (i:int) (at:t) (lst:int list): int list =
  (** The assertions of the local context which are needed to prove
      assertion [i] in [at] cumulated to list [lst].

      The list includes [i] if it is in the current context.
   *)
  assert (i < (count at));
  let cnt0 = count_previous at in

  let used (lst:int list): int list =
    assert (cnt0 <= i);
    let desc = Seq.elem at.seq i in
    match desc.proof_term with
      Axiom _
    | Assumption _       -> lst
    | Specialize (j,_)   -> used_assertions j at lst
    | Subproof (_,_,_,_) -> lst
    | Detached (i,j) ->
        let used_i = used_assertions i at lst in
        used_assertions j at used_i
  in
  if i < cnt0 then lst
  else used (i::lst)



let discharged (i:int) (at:t): int * int array * term * proof_term =
  (** The [i]th term (with number and names of arguments) of the current
      environment with all assumptions discharged together with
      its proof term.
   *)
  let cnt0 = count_previous at
  and axiom = List.exists
      (fun i ->
        assert (i < (count at));
        match (Seq.elem at.seq i).proof_term with
          Axiom _ -> true
        | _       -> false)
      (used_assertions i at [])
  and term  = implication i at
  and nargs = nbenv_local at
  and nms   = names at
  in
  let used_args = Term.used_args term nargs in
  let term      = Term.keep_used used_args term nargs
  and nused     = Array.length used_args
  and nnames    = Array.length nms
  in
  let nms       =
    if nnames=0 then nms
    else
      (assert (nnames=nargs);
       Array.init nused (fun i -> nms.(i)))
  in
  let pt =
    if axiom then
      Axiom term
    else
      let pt_arr =
        Array.init
          (i-cnt0)
          (fun j -> (Seq.elem at.seq (j+cnt0)).proof_term)
      in
      Subproof (nargs, used_args,i,pt_arr)
  in
  nused, nms, term, pt
