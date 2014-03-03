open Container
open Term

type type_term   = term
type constraints = type_term array




module TVars: sig

  type t
  val make: int -> constraints -> t
  val make_local: int -> t
  val count_local: t -> int
  val count_global: t -> int
  val count: t -> int
  val constraints: t -> constraints
  val add_global: constraints -> t -> t
  val add_local:  int -> t -> t
  val remove_local: int -> t -> t

end = struct

  type t = {nlocal:int; constraints: constraints}

  let make (ntvs:int) (cs:constraints): t = {nlocal=ntvs;constraints=cs}
  let make_local (ntvs:int) : t           = {nlocal=ntvs;constraints=[||]}
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
end (* TVars *)




module TVars_sub: sig

  type t
  val make:         int -> t
  val count:        t -> int
  val get:          int -> t -> term
  val count_global: t -> int
  val count_local:  t -> int
  val tvars:        t -> TVars.t
  val sub:          t -> Term_sub_arr.t
  val add_global:   constraints -> t -> t
  val add_local:    int -> t -> t
  val remove_local: int -> t -> t
  val update:       t -> t -> unit
end = struct

  type t = {vars: TVars.t;
            sub:  Term_sub_arr.t}

  let make (ntvs: int): t =
    {vars = TVars.make_local ntvs; sub = Term_sub_arr.make ntvs}

  let count (tvars:t): int = TVars.count tvars.vars

  let get (i:int) (tvars:t): term =
    assert (i < (count tvars));
    Term_sub_arr.get i tvars.sub

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

  let update (tv:t) (tvnew:t): unit =
    (** Update the type variables in [tv] with the type variables in [tvnew].

        This requires that [tv] and [tvnew] have the same number of local type
        variables and [tvnew] might have more globals than [tv]
     *)
    assert ((count tv) <= (count tvnew));
    assert ((count_local tv) = (count_local tvnew));
    let nloc  = count_local tv
    and ndown = (count_global tvnew) - (count_global tv)
    in
    let rec updt (i:int): unit =
      if i = nloc then ()
      else begin
        Term_sub_arr.add
          i
          (Term.down_from ndown nloc (Term_sub_arr.args tvnew.sub).(i))
          tv.sub;
        updt (i+1)
      end
    in updt 0

end (* TVars_sub *)






module Sign: sig
  type t
  val empty:       t
  val make_func:   type_term array -> type_term -> t
  val make_proc:   type_term array -> type_term -> t
  val make_const:  type_term -> t
  val make_args:   type_term array -> t
  val to_string:   t -> string
  val arity:       t -> int
  val is_constant: t -> bool
  val arguments:   t -> type_term array
  val arg_type:    int -> t -> type_term
  val argument:    int -> t -> t
  val has_result:  t -> bool
  val is_binary:   t -> bool
  val is_unary:    t -> bool
  val result:      t -> type_term
  val is_procedure:t -> bool
  val up_from:     int -> int -> t -> t
  val up:          int -> t -> t
  val up2:         int -> int -> int -> t -> t
  val to_function: int -> t -> t
  val unify:       t -> t -> TVars_sub.t -> unit

end = struct

  type t = {args: type_term array;
            result: (type_term*bool) option}

  let empty: t = {args = [||]; result = None}

  let make_func (args: type_term array) (result:type_term): t =
    {args = args; result = Some (result,false)}

  let make_args (args: type_term array): t =
    {args = args; result = None}

  let make_const (result:type_term): t =
    {args = [||]; result = Some (result,false)}

  let make_proc (args: type_term array) (result:type_term): t =
    {args = args; result = Some (result,true)}

  let arity (s:t): int = Array.length s.args

  let is_constant (s:t): bool = (arity s) = 0

  let arguments (s:t): type_term array = s.args

  let arg_type (i:int) (s:t): type_term =
    assert (i < (arity s));
    s.args.(i)

  let argument (i:int) (s:t): t =
    assert (i < (arity s));
    make_func [||] s.args.(i)

  let has_result (s:t): bool =
    Option.has s.result

  let is_binary (s:t): bool = (has_result s) && ((arity s) = 2)
  let is_unary  (s:t): bool = (has_result s) && ((arity s) = 1)

  let result (s:t): type_term =
    assert (has_result s);
    let r,_ = Option.value s.result in r

  let is_procedure (s:t): bool =
    match s.result with
      None -> true
    | Some (r,proc) -> proc


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
     result = match s.result with
       None   -> None
     | Some (t,proc) -> Some (Term.upbound n start t,proc)}


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
     result = Some (Term.up nargs (result s),false)}



  let unify (s1:t) (s2:t) (tvars_sub: TVars_sub.t): unit =
    let n,has_res = (arity s1), (has_result s1) in
    if not (n = (arity s2) && has_res = (has_result s2)) then
      raise Not_found;

    let subst = TVars_sub.sub tvars_sub in
    if has_res then
      Term_sub_arr.unify (result s1) (result s2) subst;
    Array.iteri (fun i t -> Term_sub_arr.unify t s2.args.(i) subst) s1.args
end (* Sign *)
