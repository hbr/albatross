open Alba2_common
open Container
open Printf

module Term = Term2

module type CONTEXT =
  sig
    type t
    val empty: t
    val push: Feature_name.t option -> Term.typ -> t -> t
    val push_simple: string option -> Term.typ -> t -> t
    val push_arguments: Term.arguments -> t -> t
    val push_fixpoint: Term.fixpoint -> t -> t
    val is_valid: int -> t -> bool
    val name: int -> t -> Feature_name.t option
    (*val shadow_level: int -> t -> int
    val type_: int -> t -> Term.*)
  end

module Raw_context =
  struct
    type t = unit
    let empty: t = ()
    let push (_:Feature_name.t option) (_:Term.typ) (c:t): t = c
    let push_simple (_:string option) (_:Term.typ) (c:t): t = c
    let push_arguments (args:Term.arguments) (c:t): t = c
    let push_fixpoint (fp:Term.fixpoint) (c:t): t = c
    let is_valid (i:int) (c:t): bool =
      true
    let name (i:int) (c:t): Feature_name.t option =
      some_feature_name (string_of_int i)
  end

(*
  Basics
  ------

  ((((f a) b) c) ... z)    ~>  f(a,b,c,...,z)

  all(a:A) all(b:B) ... t  ~>  all(a:A,b:B,...) t

  (a:A) := (b:B) := ... e  ~>  (a:A,b:B,...) := e


  Function term f can be a variable, lambda term, ...

  ((x,y) := exp)(a,b):
        exp                           let
          where                         x := a
             x := a                     y := b
             y := b                   then
          end                           exp

   derivable type arguments are supressed

   Fix(idx, (nm,tp,decr,term), ....)

      let mutual
        f1(args):tp := t
        f2(....) ...
        ...
      end then
        fi


  Parentheses:

  1) outer operator has higher precedence than inner operator

  2) same precedence, same left assoc and inner is right operand
     e.g. a + (b + c)

  3) same precedence, some right assoc and inner is left operand
     e.g. (a ^ b) ^ c

  4) same precedence, different assoc

  5) inspect, lambda and all have lower precedence than all operators (must be
     parenthesized if they occur as operand) but higher precedece than comma
     and colon.

  6) oo-dot binds stronger than application, application binds stronger than
     usual operators. 'tgt.f(args)' does not need '(tgt.f)(args)',
     'tgt.f(args) + ...' does not need parentheses. But '(+r)(a,b)' needs
     parentheses around '+r'.

  7) assignment binds stronger than comma i.e. f(...) := (a,b)  needs parentheses
     around 'a,b'.
 *)

module type S =
  sig
    type context
    val print: Term.t -> context -> Pretty_printer2.Document.t
    val print_fixpoint: Term.fixpoint -> context -> Pretty_printer2.Document.t
  end


module Make (C:CONTEXT)
  =
  struct
    open Pretty_printer2

    type context = C.t

    let print_name (nme:Feature_name.t option): Document.t =
      let open Feature_name in
      let open Document in
      match nme with
      | None ->
         text "_"
      | Some nme ->
         begin
           match nme with
           | Name s ->
              text s
           | Operator op ->
              let str,_,_ = Operator.data op in
              text "(" ^ text str ^ text ")"
           | Bracket ->
              text "[]"
           | True ->
              text "true"
           | False ->
              text "false"
           | Number i ->
              text (string_of_int i)
         end

    let rec print (t:Term.t) (c:C.t): Document.t =
      let open Term in
      match t with
      | Sort s ->
         print_sort s
      | Variable i ->
         print_variable i c
      | Application (f,z,oo) ->
         print_application f z c
      | Lambda (nme,tp,t) ->
         print_lambda nme tp t c
      | All(nme,tp,t) ->
         print_product nme tp t c
      | Inspect (e,m,f) ->
         print_inspect e m f c
      | Fix (i,arr) ->
         assert false

    and print_sort s =
      let open Term in
      let open Document in
      match s with
      | Sorts.Proposition ->
         text "Proposition"
      | Sorts.Any ->
         text "Any"
      | Sorts.Box ->
         text "Box"


    and print_variable i c =
      let open Feature_name in
      let open Document in
      if C.is_valid i c then
        match C.name i c with
        | None ->
           text Pervasives.("v#" ^ string_of_int i)
        | Some nme ->
           print_name (Some nme)
      else
        text Pervasives.("(v#" ^ string_of_int i ^ "?)")


    and print_application f z c =
      let open Document in
      let f,args = Term.split_application f [z] in
      let rec print_args args =
        match args with
        | [] ->
           assert false (* cannot happen *)
        | [a] ->
           print a c
        | a :: args ->
           print a c ^ text "," ^ cut ^ print_args args
      in
      print f c ^ bracket 2 "(" (print_args args) ")"


    and print_formal_args (args:Term.argument_list) (c:context)
        : Document.t * context =
      let open Document in
      let print_arg nme a c =
        print_name nme ^ text ":" ^ print a c,
        C.push nme a c
      in
      match args with
      | [] ->
         assert false (* cannot happen *)
      | [nme,a] ->
         let nme = some_feature_name_opt nme in
         print_arg nme a c
      | (nme,a) :: args ->
         let nme = some_feature_name_opt nme in
         let doc1,c = print_arg nme a c in
         let doc2,c = print_formal_args args c in
         doc1 ^ text "," ^ doc2, c


    and print_lambda nme tp t c =
      let open Document in
      let t,args_rev = Term.split_lambda0 (-1) t 1 [nme,tp] in
      let docargs,c = print_formal_args (List.rev args_rev) c in
      bracket 2 "(" docargs ")"
      ^ text " :="
      ^ group (nest 2 (space ^ print t c))

    and print_product nme tp t c =
      let open Document in
      let tp,args_rev = Term.split_product0 t [nme,tp] in
      let docargs,c = print_formal_args (List.rev args_rev) c in
      text "all" ^ bracket 2 "(" docargs ")"
      ^ group (nest 2 (space ^ print tp c))


    (* inspect
           e
           res
       case
           c1(args) := f1
           ...
       end*)
    and print_inspect e res f c =
      let open Document in
      let ncases = Array.length f in
      let print_case i =
        let co,def = f.(i) in
        let args,co = Term.split_lambda co in
        let c1 = C.push_arguments args c in
        let def,_ = Term.split_lambda0 (Array.length args) def 0 [] in
        group (print co c1 ^ text " :="
               ^ nest 2 (space ^ print def c1))
      in
      let rec print_cases doc n =
        if n = 0 then
          doc
        else
          let i = n - 1 in
          print_cases
            (print_case i
             ^ if n = ncases then doc else optional "; " ^ doc)
            i
      in
      group (
          text "inspect"
          ^ nest 2 (space ^ print e c ^ optional "; " ^ print res c)
          ^ space ^ text "case"
          ^ nest 2 (space ^ print_cases empty ncases)
          ^ space ^ text "end"
        )

    and print_formal_arguments args c =
      let open Document in
      let nargs = Array.length args in
      let doc,c1 =
        interval_fold
          (fun (doc,c) i ->
            let doc = if i = 0 then doc else doc ^ text ","
            and nme,tp = args.(i) in
            let nme = some_feature_name_opt nme
            in
            doc ^ print_name nme
            ^ text ":" ^ print tp c,
            C.push nme tp c)
          (empty,c) 0 nargs
      in
      text "(" ^ doc ^ text ")",
      c1


    and print_one_fixpoint i fp c =
      let open Document in
      let nme,typ,decr,t = fp.(i) in
      let e,args_rev = Term.split_lambda0 (-1) t 0 [] in
      let docargs,c1 = print_formal_args (List.rev args_rev) c in
      print_name nme
      ^ bracket 2 "(" docargs ")"
      ^ text " :="
      ^ group (nest 2 (space ^ print e c1))

    and print_fixpoint fp c =
      let open Document in
      let n = Array.length fp in
      assert (0 < n);
      let c1 = C.push_fixpoint fp c in
      let rec print_below i doc =
        if i = 0 then
          doc
        else
          let br = if i = 1 then empty else optional "; " in
          print_below
            (i-1)
            (br ^ print_one_fixpoint (i-1) fp c1)
      in
      if n = 1 then
        print_below n empty
      else
        assert false (* nyi: mutual fixpoints *)
  end (* Make *)


let string_of_term (t:Term.t): string =
  let module PR = Make (Raw_context) in
  let open Pretty_printer2 in
  Layout.pretty 50 (PR.print t Raw_context.empty)


let test (): unit =
  Printf.printf "test term printer2\n";
  let open Term in
  let print = string_of_term in
  assert
    begin
      print variable1 = "1"
    end;
  assert
    begin
      print (apply2 variable0 variable1 variable2) = "0(1,2)"
    end;
  ();
  assert
    begin
      let str =
      print (push_product [|Some "a", variable0;
                            Some "b", variable1|] variable2)
      in
      printf "%s\n" str;
      str = "all(a:0,b:1) 2"
    end
