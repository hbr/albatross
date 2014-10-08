open Term
open Container
open Support
open Printf

type proof_term =
    Axiom      of term
  | Assumption of term
  | Detached   of int * int  (* modus ponens *)
  | Specialize of int * term array
  | Expand     of int        (* index of term which is expanded *)
  | Expand_bwd of term       (* term which is backward expanded *)
  | Reduce     of int        (* index of term which is reduced  *)
  | Reduce_bwd of term       (* term which is backward reduced  *)
  | Witness    of int * term * term array
        (* term [i] is a witness for [some (a,b,...) term] where
           [a,b,..] are substituted by the arguments in the term array *)
  | Inherit    of int * int  (* assertion, descendant class *)
  | Subproof   of int        (* nargs *)
                * int array  (* names *)
                * int        (* res *)
                * proof_term array

type desc = {nbenv0:     int;
             term:       term;
             proof_term: proof_term;}

type entry = {nbenv:  int;
              names:  int array;
              imp_id: int;
              all_id: int;
              mutable count: int;
              mutable nreq:  int   (* number of local assumptions *)
            }

type t = {seq:  desc Seq.t;
          mutable entry: entry;
          mutable stack: entry list;
          c: Context.t}

let context (at:t): Context.t = at.c
let class_table (at:t):   Class_table.t   = Context.class_table at.c
let feature_table (at:t): Feature_table.t = Context.feature_table at.c


let is_private (at:t): bool = Context.is_private at.c
let is_public  (at:t): bool = Context.is_public  at.c
let is_interface_use   (at:t): bool = Context.is_interface_use  at.c
let is_interface_check (at:t): bool = Context.is_interface_check  at.c


let add_used_module (name:int*int list) (used:IntSet.t) (at:t): unit =
  Context.add_used_module name used at.c

let add_current_module (name:int) (used:IntSet.t) (at:t): unit =
  Context.add_current_module name used at.c

let set_interface_check (pub_used:IntSet.t) (at:t): unit =
  Context.set_interface_check pub_used at.c


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


let count_global (pt:t): int =
  let rec count (lst: entry list): int =
    match lst with
      []     -> assert false
    | [e]    -> e.count
    | _::lst -> count lst
  in
  if pt.stack = []
  then
    Seq.count pt.seq
  else
    count pt.stack


let count_last_local (pt:t): int =
  (count pt) - (count_previous pt)

let nbenv (at:t): int = at.entry.nbenv

let nbenv_local (at:t): int =
  at.entry.nbenv - if at.stack = [] then 0 else (List.hd at.stack).nbenv

let names (at:t): int array =
  at.entry.names

let imp_id (at:t): int =
  at.entry.imp_id

let all_id (at:t): int =
  at.entry.all_id

let some_id (at:t): int =
  nbenv at + Feature_table.some_index

let split_implication (t:term) (at:t): term * term =
  Term.binary_split t at.entry.imp_id

let split_all_quantified (t:term) (at:t): int * int array * term =
  Term.quantifier_split t at.entry.all_id

let split_some_quantified (t:term) (at:t): int * int array * term =
  Term.quantifier_split t (some_id at)

let implication (a:term) (b:term) (at:t): term =
  Term.binary at.entry.imp_id a b

let implication_chain (ps: term list) (tgt:term) (at:t): term =
  Term.make_implication_chain ps tgt (imp_id at)

let split_implication_chain (t:term) (at:t): term list * term =
  Term.split_implication_chain t (imp_id at)

let all_quantified (nargs:int) (names:int array) (t:term) (at:t): term =
  Term.quantified at.entry.all_id nargs names t

let some_quantified (nargs:int) (names:int array) (t:term) (at:t): term =
  Term.quantified (some_id at) nargs names t

let all_quantified_outer (t:term) (at:t): term =
  let nargs  = nbenv_local at          in
  let all_id = at.entry.all_id - nargs in
  Term.quantified all_id nargs at.entry.names t

let rec stacked_counts (pt:t): int list =
  List.map (fun e -> e.count) pt.stack


let string_of_term (t:term) (at:t): string =
  Context.string_of_term t 0 at.c


let make (): t =
  {seq   = Seq.empty ();
   entry = {count   = 0;
            names   = [||];
            nbenv   = 0;
            nreq    = 0;
            imp_id  = Feature_table.implication_index;
            all_id  = Feature_table.all_index};
   stack = [];
   c = Context.make ()}


let push0 (nbenv:int) (names: int array) (at:t): unit =
  assert (nbenv = Array.length names);
  at.entry.count <- Seq.count at.seq;
  at.stack       <- at.entry :: at.stack;
  at.entry       <-
    {at.entry with
     nreq   = 0;
     nbenv  = at.entry.nbenv + nbenv;
     names  = names;
     imp_id = at.entry.imp_id + nbenv;
     all_id = at.entry.all_id + nbenv}



let push (entlst:entities list withinfo) (at:t): unit =
  let c = context at in
  assert (depth at = Context.depth c);
  Context.push entlst None c;
  let nbenv = Context.arity c
  and names = Context.local_fargnames c in
  assert (nbenv = Array.length names);
  push0 nbenv names at


let push_untyped (names:int array) (at:t): unit =
  let c = context at in
  Context.push_untyped names c;
  let nbenv = Context.arity c in
  assert (nbenv = Array.length names);
  assert (names = Context.local_fargnames c);
  push0 nbenv names at



let keep (cnt:int) (at:t): unit =
  assert (count_previous at <= cnt);
  Seq.keep cnt at.seq


let pop (at:t): unit =
  assert (is_local at);
  assert (depth at = Context.depth (context at));
  Context.pop (context at);
  at.entry  <- List.hd at.stack;
  at.stack  <- List.tl at.stack;
  Seq.keep at.entry.count at.seq



let term (i:int) (at:t): term * int =
  (** The [i]th proved term with the number of variables of its environment.
   *)
  assert (i < count at);
  let desc = Seq.elem i at.seq in
  desc.term, desc.nbenv0


let nbenv_term (i:int) (at:t): int =
  (** The number of variables of the environment of the  [i]th proved term.
   *)
  assert (i < count at);
  (Seq.elem i at.seq).nbenv0



let local_term (i:int) (at:t): term =
  (** The [i]th proved term in the local environment.
   *)
  assert (i < count at);
  let desc = Seq.elem i at.seq in
  let n_up = at.entry.nbenv - desc.nbenv0
  in
  Term.up n_up desc.term


let variant (i:int) (cls:int) (at:t): term =
  let ft = feature_table at in
  let t,nbenv = term i at   in
  let t = Feature_table.variant_term t nbenv cls ft in
  t



let discharged_term (i:int) (at:t): term =
  (** The [i]th term of the current environment with all local variables and
      assumptions discharged.
   *)
  let cnt0 = count_previous at
  and tgt = local_term i at
  in
  let tref = ref tgt in
  for k = cnt0 + at.entry.nreq - 1 downto cnt0 do
    tref := implication (local_term k at) !tref at
  done;
  all_quantified_outer !tref at


let is_assumption (i:int) (at:t): bool =
  assert (i < count at);
  let desc = Seq.elem i at.seq in
  match desc.proof_term with
    Assumption _ -> true
  | _            -> false


let add_proved_0 (t:term) (pt:proof_term) (at:t): unit =
  (** Add the term [t] and its proof term [pt] to the table.
   *)
  let raw_add () =
    Seq.push {nbenv0 = at.entry.nbenv;
              term   = t;
              proof_term = pt} at.seq
  in
  match pt with
    Assumption _ ->
      let idx = count at in
      assert (idx = count_previous at + at.entry.nreq);
      raw_add ();
      at.entry.nreq <- at.entry.nreq + 1
  | _ ->
      raw_add ()


exception Illegal_proof_term

let term_of_mp (a:int) (b:int) (at:t): term =
  assert (a < count at);
  assert (b < count at);
  let ta = local_term a at
  and tb = local_term b at
  in
  let b1,b2 =
    try Term.binary_split tb (imp_id at)
    with Not_found ->
      printf "tb is not an implication\n";
      printf "  ta %d:%s\n" a (string_of_term ta at);
      printf "  tb %d:%s\n" b (string_of_term tb at);
      raise Illegal_proof_term
  in
  let ok = Term.equal_wo_names ta b1 in
  if not ok then begin
    printf "antecedent of tb does not conincide with ta (ok %b)\n" ok;
      printf "  ta %d:%s\n" a (string_of_term ta at);
      printf "  tb %d:%s\n" b (string_of_term tb at);
    raise Illegal_proof_term
  end;
  b2


let expand_term (t:term) (at:t): term =
  let ft = feature_table at
  and nb = nbenv at in
  try
    Feature_table.expand_focus_term t nb ft
  with Not_found ->
    raise Illegal_proof_term

let reduce_term (t:term) (at:t): term =
  try Term.reduce_top t
  with Not_found -> raise Illegal_proof_term


let term_of_expand (i:int) (at:t): term =
  expand_term (local_term i at) at

let term_of_expand_bwd (t:term) (at:t): term =
  implication (expand_term t at) t at


let term_of_reduce (i:int) (at:t): term =
  reduce_term (local_term i at) at

let term_of_reduce_bwd (t:term) (at:t): term =
  implication (reduce_term t at) t at


let term_of_specialize (i:int) (args:term array) (at:t): term =
  assert (i < count at);
  let nargs = Array.length args
  and t = local_term i at
  in
  let n,nms,t0 =
    try Term.quantifier_split t (all_id at)
    with Not_found -> assert false
  in
  assert (nargs <= n);
  let tsub = Term.part_sub t0 n args 0
  in
  if nargs < n then
    let imp_id0 = (imp_id at)           in
    let imp_id1 = imp_id0 + (n-nargs)   in
    try
      let a,b = Term.binary_split tsub imp_id1 in
      Term.binary
        imp_id0
        (Term.down (n-nargs) a)
        (Term.quantified
           (all_id at)
           (n-nargs)
           (Array.sub nms nargs (n-nargs))
           b)
    with Term_capture ->
      printf "term capture\n";
      raise Illegal_proof_term
    | Not_found ->
        printf "not found\n";
        raise Illegal_proof_term
  else
    tsub


let term_of_witness (i:int) (t:term) (args:term array) (at:t): term =
  let nargs = Array.length args in
  let some_term = some_quantified nargs [||] t at in
  let ti  = local_term i at in
  let wt  = Term.apply t args in
  if Term.equal_wo_names ti wt then ()
  else begin
    printf "illegal witness ti %s, wt %s, for %s\n"
      (string_of_term ti at)
      (string_of_term wt at)
      (string_of_term some_term at);
    raise Illegal_proof_term
  end;
  implication ti some_term at



let count_assumptions (pt_arr:proof_term array): int =
  let p (pt:proof_term): bool =
    match pt with
      Assumption _ -> false | _ -> true
  in
  try
    Search.array_find_min p pt_arr
  with Not_found ->
    Array.length pt_arr




let arguments_string (at:t): string =
  let names = Array.to_list at.entry.names in
  let str = String.concat "," (List.map ST.string names) in
  if str = "" then str
  else "(" ^ str ^ ")"




let adapt_proof_term (cnt:int) (delta:int) (pt:proof_term): proof_term =
  assert (delta <= cnt);
  let base = cnt - delta in
  let index (i:int): int =
    if i < base then i else i + delta
  in
  let rec adapt (pt:proof_term): proof_term =
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
    | Witness (i,t,args) ->
        Witness (index i,t,args)
    | Subproof (nargs,names,res,pt_arr) ->
        Subproof (nargs,names, index res, Array.map adapt pt_arr)
  in
  if delta = 0 then pt else adapt pt



let reconstruct_term (pt:proof_term) (trace:bool) (at:t): term =
  let depth_0 = depth at
  and cnt0    = count at
  in
  let prefix (d:int): string = String.make (4*(d-depth_0)) ' '
  in
  let print (t:term) =
    printf "%s%3d %s"
      (prefix (depth at)) (count at) (string_of_term t at)
  and print_all () =
    let pre = prefix (depth at - 1) in
    printf "%s%3d all%s\n%s    require\n"
      pre (count at) (arguments_string at) pre
  and print_str (str:string):unit =
    let pre = prefix (depth at - 1) in
    printf "%s    %s\n" pre str
  in
  let print0 (t:term) = print t; printf "\n"
  and print1 (t:term) (i:int) = print t; printf "\t{%d}\n" i
  and print2 (t:term) (i:int) (j:int) = print t; printf "\t{%d,%d}\n" i j
  in
  let rec reconstruct (pt:proof_term): term =
    let cnt = count at in
    match pt with
      Axiom t | Assumption t ->
        if trace then print0 t;
        t
    | Detached (a,b) ->
        let t = term_of_mp a b at in
        if trace then print2 t a b;
        t
    | Specialize (i,args) ->
        let t = term_of_specialize i args at in
        if trace then print1 t i;
        t
    | Expand i ->
        let t = term_of_expand i at in
        if trace then print1 t i;
        t
    | Expand_bwd t ->
        let t = term_of_expand_bwd t at in
        if trace then print0 t;
        t
    | Reduce i ->
        let t = term_of_reduce i at in
        if trace then print1 t i;
        t
    | Reduce_bwd t ->
        let t = term_of_reduce_bwd t at in
        if trace then print0 t;
        t
    | Witness (idx,t,args) ->
        let t = term_of_witness idx t args at in
        if trace then print0 t;
        t
    | Inherit (idx,cls) ->
        let t =  variant idx cls at in
        if trace then print1 t idx;
        t
    | Subproof (nargs,names,res_idx,pt_arr) ->
        push_untyped names at;
        let pt_len = Array.length pt_arr in
        let pt_nass =
          if trace then count_assumptions pt_arr else 0
        in
        assert (res_idx < cnt + pt_len);
        if trace then print_all ();
        for i = 0 to pt_len - 1 do
          if trace && i = pt_nass then print_str "check";
          let t = reconstruct pt_arr.(i) in
          add_proved_0 t pt_arr.(i) at
        done;
        if trace then begin
          print_str "ensure";
          print1 (local_term res_idx at) res_idx;
          print_str "end";
        end;
        let term = discharged_term res_idx at in
        pop at;
        term
  in
  try
    reconstruct pt
  with Illegal_proof_term ->
    for k = depth_0 to depth at - 1 do pop at done;
    keep cnt0 at;
    raise Illegal_proof_term




let term_of_pt (pt:proof_term) (at:t): term =
  (** Construct a term from the proof term [pt].
   *)
  reconstruct_term pt false at


let print_pt (pt:proof_term) (at:t): unit =
  let _ = reconstruct_term pt true at in ()



let is_proof_pair (t:term) (pt:proof_term) (at:t): bool =
  try
    let t_pt = term_of_pt pt at in
    let res = Term.equal_wo_names t t_pt in
    if not res then begin
      printf "unequal t    %s\n" (string_of_term t at);
      printf "        t_pt %s\n" (string_of_term t_pt at)
    end;
    res
  with Illegal_proof_term ->
    printf "Illegal proof term\n";
    print_pt pt at;
    false


let add_proved (t:term) (pt:proof_term) (delta:int) (at:t): unit =
  (** Add the term [t] and its proof term [pt] to the table.
   *)
  let cnt = count at in
  let pt = adapt_proof_term cnt delta pt in
  assert (not (is_global at) || is_proof_pair t pt at);
  add_proved_0 t pt at


let add_axiom (t:term) (at:t): unit =
  let pt = Axiom t in
  add_proved_0 t pt at


let add_assumption (t:term) (at:t): unit =
  let pt = Assumption t in
  add_proved_0 t pt at


let add_inherited (t:term) (idx:int) (cls:int) (at:t): unit =
  assert (is_global at);
  let pt = Inherit (idx,cls) in
  add_proved_0 t pt at


let add_mp (t:term) (i:int) (j:int) (at:t): unit =
  let pt = Detached (i,j) in
  add_proved_0 t pt  at


let add_specialize (t:term) (i:int) (args:term array) (at:t): unit =
  let pt = Specialize (i,args) in
  add_proved_0 t pt  at


let add_expand (t:term) (i:int) (at:t): unit =
  add_proved_0 t (Expand i) at


let add_expand_backward (t:term) (impl:term) (at:t): unit =
  (* [impl = (texpanded => t)] *)
  add_proved_0 impl (Expand_bwd t) at


let add_reduce (t:term) (i:int) (at:t): unit =
  add_proved_0 t (Reduce i) at


let add_reduce_backward (t:term) (impl:term) (at:t): unit =
  (* [impl = (tred => t)] *)
  add_proved_0 impl (Reduce_bwd t) at


let add_witness (impl:term) (i:int) (t:term) (args:term array) (at:t): unit =
  add_proved_0 impl (Witness (i,t,args)) at

let rec used_assertions (i:int) (at:t) (lst:int list): int list =
  (** The assertions of the local context which are needed to prove
      assertion [i] in [at] cumulated to list [lst].

      The list includes [i] if it is in the current context.
   *)
  assert (i < (count at));
  let cnt0 = count_previous at
  in
  let used (lst:int list): int list =
    assert (cnt0 <= i);
    let desc = Seq.elem i at.seq in
    match desc.proof_term with
      Axiom _
    | Assumption _
    | Expand_bwd _       -> lst
    | Reduce_bwd _       -> lst
    | Specialize (j,_)   -> used_assertions j at lst
    | Witness (i,_,_)
    | Expand i
    | Reduce i           -> used_assertions i at lst
    | Subproof (_,_,_,_) -> lst
    | Detached (i,j) ->
        let used_i = used_assertions i at lst in
        used_assertions j at used_i
    | Inherit (idx,cls) ->
        assert false
  in
  if i < cnt0 then lst
  else used (i::lst)




let discharged (i:int) (at:t): term * proof_term =
  (** The [i]th term of the current environment with all local variables and
      assumptions discharged together with its proof term.
   *)
  let cnt0 = count_previous at
  and axiom = List.exists
      (fun i ->
        assert (i < (count at));
        match (Seq.elem i at.seq).proof_term with
          Axiom _ -> true
        | _       -> false)
      (used_assertions i at [])
  and term  = discharged_term i at
  and nargs = nbenv_local at
  and nms   = names at
  in
  let pterm =
    if axiom then
      Axiom term
    else
      let narr =
        if cnt0 + at.entry.nreq <= i then
          i + 1 - cnt0
        else
          at.entry.nreq
      in
      assert (0 <= narr);
      if nargs = 0 && narr = 1 && at.entry.nreq = 0 then
        (Seq.elem cnt0 at.seq).proof_term
      else
        let pt_arr =
          Array.init
            narr
            (fun j -> (Seq.elem (cnt0+j) at.seq).proof_term)
        in
        Subproof (nargs,nms,i,pt_arr)
  in
  term, pterm
