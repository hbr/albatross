open Container
open Term

type type_term   = term
type constraints = type_term array




module TVars: sig
  type t
  val make: int -> constraints -> t
  val count_local: t -> int
  val count_global: t -> int
  val count: t -> int
  val constraints: t -> constraints
  val add_global: constraints -> t -> t
  val add_local:  int -> t -> t
  val remove_local: int -> t -> t
end = struct

  type t = {nlocal:int; constraints: constraints}

  let make (nf:int) (cs:constraints): t = {nlocal=nf;constraints=cs}
  let count_local (tvs:t): int = tvs.nlocal
  let count_global (tvs:t): int = Array.length tvs.constraints
  let count (tvs:t): int = tvs.nlocal + (count_global tvs)
  let constraints (tvs:t): constraints = tvs.constraints
  let add_global (cs:constraints) (tvs:t): t =
    {tvs with constraints = Array.append tvs.constraints cs}
  let add_local (n:int) (tvs:t): t =
    {tvs with nlocal = tvs.nlocal + n}
  let remove_local (n:int) (tvs:t): t =
    assert (n <= (count_local tvs));
    {tvs with nlocal = tvs.nlocal - n}
end




module TVars_sub: sig
  type t
  val count: t -> int
  val count_global: t -> int
  val count_local:   t -> int
  val tvars: t -> TVars.t
  val sub:   t -> Term_sub_arr.t
  val add_global:       constraints -> t -> t
  val add_local:             int -> t -> t
  val remove_local:         int -> t -> t
end = struct

  type t = {vars: TVars.t;
            sub:  Term_sub_arr.t}
  let count (tvars:t): int = TVars.count tvars.vars

  let count_global (tv:t): int =
    TVars.count_global tv.vars

  let count_local (tv:t): int =
    TVars.count_local tv.vars

  let tvars (tv:t): TVars.t = tv.vars

  let sub (tv:t): Term_sub_arr.t = tv.sub

  let add_global (cs:constraints) (tv:t): t =
    {vars = TVars.add_global cs tv.vars;
     sub  = Term_sub_arr.extend (Array.length cs) tv.sub}

  let add_local (n:int) (tv:t): t =
    (** Add [n] local (fresh) type variables without constraints to [tv]
        and shift all type variables up by [n].
     *)
    {vars = TVars.add_local n tv.vars;
     sub  = Term_sub_arr.extend_bottom n tv.sub}

  let remove_local (n:int) (tv:t): t =
    (** Remove [n] local type variables (without constraints) from [tv] and
        shift all type variables down by [n].
     *)
    {vars = TVars.remove_local n tv.vars;
     sub  = Term_sub_arr.remove_bottom n tv.sub}
end






module Sign: sig
  type t
  val make_func:   type_term array -> type_term -> t
  val make_const:  type_term -> t
  val arity:       t -> int
  val is_constant: t -> bool
  val argument:    int -> t -> t
  val has_result:  t -> bool
  val result:      t -> type_term
  val up_from:     int -> int -> t -> t
  val up:          int -> t -> t
  val up2:         int -> int -> int -> t -> t
  val to_function: int -> t -> t
  val unify:       t -> t -> TVars_sub.t -> unit
  (*val apply:       Term_sub_arr.t -> t -> t*)
end = struct
  type t = {args: type_term array;
            result: type_term option}

  let make_func (args: type_term array) (result:type_term): t =
    {args = args; result = Some result}

  let make_const (result:type_term): t =
    {args = [||]; result = Some result}

  let arity (s:t): int = Array.length s.args

  let is_constant (s:t): bool = (arity s) = 0

  let argument (i:int) (s:t): t =
    assert (i < (arity s));
    make_func [||] s.args.(i)

  let has_result (s:t): bool =
    Option.has s.result

  let result (s:t): type_term =
    assert (has_result s);
    Option.value s.result

  let up_from (n:int) (start:int) (s:t): t =
    (** Shift all types up by [n] starting from [start].
     *)
    {args = Array.map (fun t -> Term.upbound n start t) s.args;
     result = match s.result with
       None   -> None
     | Some t -> Some (Term.upbound n start t)}


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
        [nargs] arguments. The [nargs] argument types are fresh type variables,
        therefore the result type of [s] has to be shifted up by [nargs].
     *)
    assert (has_result s);
    assert (is_constant s);
    {args   = Array.init nargs (fun i -> Variable i);
     result = Some (Term.up nargs (result s))}



  let unify (s1:t) (s2:t) (tvars_sub: TVars_sub.t): unit =
    let n,has_res = (arity s1), (has_result s1) in
    if not (n = (arity s2) && has_res = (has_result s2)) then
      raise Not_found;

    let subst = TVars_sub.sub tvars_sub in
    if has_res then
      Term_sub_arr.unify (result s1) (result s2) subst;
    Array.iteri (fun i t -> Term_sub_arr.unify t s2.args.(i) subst) s1.args


  let apply (sub:Term_sub_arr.t) (s:t): t =
    (** Apply the substitution [sub] to the signature [s]
     *)
    assert false
end
