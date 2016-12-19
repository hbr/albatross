(* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*)

open Support
open Term
open Container
open Signature
open Printf


module TB = Term_builder

type ident =
    IDVar of int
  | IDFun of int list



type eterm0 =
    EVar of int
  | EGlAppl of (int list * eterm array * application_mode)
  | EAppl of (eterm * eterm array * application_mode)
  | ELam  of (eterm list * eterm * bool)  (* preconditions, term ,is_pred *)
  | EQExp of (eterm * bool)  (* is_all *)
  | EInspect of (eterm * (eterm*eterm) list)
  | EIf of (eterm * eterm * eterm)
  | EIndset of eterm list

and eterm = {
    info: info;
    context: Context.t;
    term: eterm0
  }

type max_numbers = {
    max_locs: int;
    max_fgs: int;
    max_globs: int
  }


let prefix (level:int): string =
  String.make (2+2*level) ' '




let used_variables (nargs:int) (et:eterm): IntSet.t =
  let rec used et nb set =
    let used_args args nb set =
      Array.fold_left
        (fun set et -> used et nb set)
        set
        args
    in
    let used_list args nb set =
      List.fold_left
        (fun set et -> used et nb set)
        set
        args
    in
    match et.term with
      EVar i ->
        if i < nargs then
          IntSet.add i set
        else
          set
    | EGlAppl (_,args,_) ->
        used_args args nb set
    | EAppl (f,args,_) ->
        let set = used f nb set in
        used_args args nb set
    | ELam (pres,et0,is_pred) ->
        let nb = nb + Context.count_last_variables et0.context in
        let set = used_list pres nb set in
        used et0 nb set
    | EQExp (et0,_) ->
        let nb = nb + Context.count_last_variables et0.context in
        used et0 nb set
    | EInspect (insp,cases) ->
        let set = used insp nb set in
        List.fold_left
          (fun set (pat,res) ->
            assert (pat.context == res.context);
            let nb = nb + Context.count_last_variables pat.context in
            used pat nb (used res nb set)
          )
          set
          cases
    | EIf (c,e1,e2) ->
        let set = used c nb set in
        let set = used e1 nb set in
        used e2 nb set
    | EIndset rules ->
        assert (rules <> []);
        let c0 = (List.hd rules).context in
        List.fold_left
          (fun set rule ->
            assert (rule.context == c0);
            used rule nb set)
          set
          rules
  in
  used et 0 IntSet.empty


let max_globs_of_features (flst:int list) (c:Context.t): int =
  List.fold_left
    (fun nglobs fidx ->
      let tvs,_ = Context.feature_signature fidx c in
      max nglobs (Tvars.count_fgs tvs)
    )
    0
    flst




let find_identifier (info:info) (id:int) (c:Context.t): ident =
  try
    let i = Context.variable_index id c in
    IDVar i
  with Not_found ->
    let flst = Context.find_features (FNname id) c in
    if flst = [] then
      error_info info ("Unknown \"" ^ ST.string id ^ "\"");
    IDFun flst


let find_features (info:info) (fn:feature_name) (c:Context.t): int list =
  let flst = Context.find_features fn c
  in
  if flst = [] then
    error_info
      info
      ("Unknow function \"" ^ feature_name_to_string fn ^ "\"");
  flst


let is_constant_constructor (nme:int) (c:Context.t): bool =
  let nvars = Context.count_variables c
  and ft = Context.feature_table c in
  try
    let lst   = Context.find_identifier nme 0 c in
    let lst = List.filter
        (fun (idx,_,_) ->
          nvars <= idx && Feature_table.is_constructor (idx-nvars) ft
        )
        lst in
    lst <> []
  with Not_found ->
    false

let case_variables
    (info:info) (e:expression) (dups:bool) (c:Context.t)
    : expression * int array =
  let rec vars (e:expression) (nanon:int) (lst:int list)
      : expression * int * int list =
    let fvars f nanon lst =
      match f with
        Identifier nme -> f,nanon,lst
      | _ -> vars f nanon lst
    in
    match e with
      Expnumber _ | Exptrue | Expfalse | Expop _ ->
        e, nanon, lst
    | Identifier nme | Typedexp(Identifier nme,_)->
        let lst =
          if is_constant_constructor nme c then
            lst
          else if dups && List.mem nme lst then
            lst
          else
            nme :: lst in
        e,nanon,lst
    | Expanon ->
        let nme = ST.symbol ("$" ^ (string_of_int nanon)) in
        Identifier nme, 1+nanon, nme :: lst
    | Typedexp (Expanon,tp) ->
        let nme = ST.symbol ("$" ^ (string_of_int nanon)) in
        Typedexp(Identifier nme,tp), 1+nanon, nme :: lst
    | Funapp(f,args,am) ->
        let f,nanon,lst = fvars f nanon lst in
        let arglst,nanon,lst =
          List.fold_left
            (fun (arglst,nanon,lst) e ->
              let e,nanon,lst = vars e nanon lst in
              e::arglst, nanon, lst)
            ([],nanon,lst)
            args in
        Funapp(f, List.rev arglst, am), nanon, lst
    | Tupleexp (e1,e2) ->
        let e1,nanon,lst = vars e1 nanon lst in
        let e2,nanon,lst = vars e2 nanon lst in
        Tupleexp (e1,e2), nanon, lst
    | Expparen e ->
        vars e nanon lst
    | _ ->
        printf "case_variables %s\n" (string_of_expression e);
        raise Not_found
  in
  try
    let e, nanon, lst = vars e 0 [] in
    if (not dups) && Mylist.has_duplicates lst then
      error_info info ("Duplicate variable in pattern \"" ^
                       (string_of_expression e) ^ "\"");
    let nms = Array.of_list (List.rev lst) in
    e, nms
  with Not_found ->
    error_info info ("Cannot extract variables from pattern \"" ^
                     (string_of_expression e) ^ "\"")


let first_pass
    (info:info)
    (e:expression)
    (c:Context.t)
    : max_numbers * eterm
    =
  let rec first
      (info:info)
      (e:expression)
      (mn:max_numbers)
      (c:Context.t)
      : max_numbers * eterm
      =
    match e with
      Identifier id ->
        identifier info id mn c
    | Expanon ->
        not_yet_implemented info ("Expanon Typing of "^ (string_of_expression e))
    | Expnumber num ->
        assert false
    | ExpResult ->
        begin
          try
            let i = Context.variable_index (ST.symbol "Result") c in
            mn, {info = info; context = c; term = EVar i}
          with Not_found ->
            error_info info "There is no variable \"Result\" in this context";
        end
    | Exptrue ->
        global_application_fn info FNtrue [] AMmath mn c
    | Expfalse ->
        global_application_fn info FNfalse [] AMmath mn c
    | Expparen e ->
        first info e mn c
    | Exparrow (entlst,e) ->
        assert false
    | Expagent (entlst,rt,pres,exp) ->
        lambda info entlst false rt pres exp mn c
    | Expop op ->
        global_application_fn info (FNoperator op) [] AMmath mn c
    | Funapp (f,args,am) ->
        application info f args am mn c
    | Expset e ->
        assert false
    | Exppred (entlst,e) ->
        lambda info entlst true None [] e mn c
    | Expindset (entlst,rules) ->
        let c_new = Context.push entlst None false false false c in
        let nargs = Context.count_last_arguments c_new
        and nlocs = Context.count_local_type_variables c_new in
        if nargs <> 1 then
          not_yet_implemented entlst.i "Multiple inductive sets";
        assert (nlocs <= 1);
        let mn =
          {mn with
           max_globs = mn.max_globs + nlocs;
           max_locs  = max mn.max_locs (Context.count_type_variables c_new)}
        in
        let mn, rules =
          List.fold_left
            (fun (mn,rules) e ->
              let mn,et = first info e mn c_new in
              mn, et :: rules
            )
            (mn,[])
            rules
        in
        mn,
        {info = info;
         context = c;
         term = EIndset (List.rev rules)}
    | Tupleexp (e1,e2) ->
        global_application_fn info (FNname ST.tuple) [e1;e2] AMmath mn c
    | Typedexp (e,tp) ->
        assert false
    | Expcolon (e1,e2) ->
        assert false
    | Expif (cond,e1,e2) ->
        let mn, cond = first info cond mn c in
        let mn, e1   = first info e1 mn c in
        let mn, e2   = first info e2 mn c in
        mn,
        {info = info;
         context = c;
         term = EIf (cond,e1,e2)}
    | Expas (e,pat) ->
        assert false
    | Expinspect (insp, cases) ->
        inspect info insp cases mn c
    | Expquantified (q,entlst,exp) ->
        quantified info q entlst exp mn c

  and application info f args am mn c =
    match f with
      Identifier id ->
        begin
          match find_identifier info id c with
            IDVar i ->
              let fterm = {info = info; context = c; term = EVar i} in
              term_application info fterm args am mn c
          | IDFun flst ->
              global_application_flst info flst args am mn c
        end
    | Expop op ->
        global_application_fn info (FNoperator op) args am mn c
    | _ ->
        let mn,f_et = first info f mn c in
        term_application info f_et args am mn c

  and term_application
      (info:info)
      (f:eterm)
      (args:expression list)
      (am:application_mode)
      (mn:max_numbers)
      (c:Context.t)
      : max_numbers * eterm
      =
    let mn,args = arguments info args mn c in
    {mn with max_globs = 2 + List.length args + mn.max_globs},
    {info = info;
     context = c;
     term = EAppl (f,Array.of_list args,am)}

  and global_application_fn
      (info:info)
      (fn:feature_name)
      (args:expression list)
      (am:application_mode)
      (mn:max_numbers)
      (c:Context.t)
      : max_numbers * eterm
      =
    let flst = find_features info fn c in
    global_application_flst info flst args am mn c

  and global_application_flst info flst args am mn c =
    let nglobs_f = max_globs_of_features flst c in
    let mn = {mn with max_globs = nglobs_f + mn.max_globs} in
    let mn,args = arguments info args mn c in
    mn,
    {info = info;
     context = c;
     term = EGlAppl(flst, Array.of_list args, am)}

  and arguments
      (info:info)
      (args:expression list)
      (mn:max_numbers)
      (c:Context.t)
      : max_numbers * eterm list
      =
    let mn,lst =
      List.fold_left
        (fun (mn,lst) arg ->
          let mn,et =
            first info arg mn c
          in
          mn, et::lst
        )
        (mn,[])
        args
    in
    mn, List.rev lst

  and identifier
      (info:info)
      (id:int)
      (mn:max_numbers)
      (c:Context.t)
      : max_numbers * eterm
      =
    match find_identifier info id c with
      IDVar i ->
        mn, {info = info; context = c; term = EVar i}
    | IDFun flst ->
        global_application_flst info flst [] AMmath mn c

  and lambda
      (info:info)
      (entlst:entities list withinfo)
      (is_pred:bool)
      (rt: return_type)
      (pres: compound)
      (e:expression)
      (mn: max_numbers)
      (c:Context.t)
      : max_numbers * eterm
      =
    let c_new = Context.push entlst rt is_pred (not is_pred) false c in
    let mn =
      {mn with
       max_locs  = max mn.max_locs (Context.count_type_variables c_new);
       max_globs = mn.max_globs + Context.count_local_type_variables c_new
     }
    in
    let pres_rev,mn =
      List.fold_left
        (fun (pres_rev,mn) e ->
          let mn,et = first e.i e.v mn c_new in
          et :: pres_rev, mn
        )
        ([],mn)
        pres
    in
    let mn, et0 = first info e mn c_new in
    mn,
    {info = info;
     context = c;
     term = ELam (List.rev pres_rev, et0, is_pred)}

  and quantified
      (info:info)
      (q:quantifier)
      (entlst:entities list withinfo)
      (exp:expression)
      (mn: max_numbers)
      (c:Context.t)
      : max_numbers * eterm
      =
    let c_new = Context.push entlst None false false false c in
    let nargs = Context.count_last_variables c_new in
    let mn =
      {mn with
       max_locs = max mn.max_locs (Context.count_type_variables c_new)}
    in
    let mn, et0 = first info exp mn c_new
    and is_all =
      begin
        match q with
          Existential -> false
        | Universal -> true
      end
    in
    let used = used_variables nargs et0 in
    if IntSet.cardinal used <> nargs then begin
      let names = Context.local_argnames c_new
      and unused =
        List.rev
          (interval_fold
             (fun unused i ->
               if not (IntSet.mem i used) then
                 i :: unused
               else
                 unused
             ) [] 0 nargs)
      in
      error_info
        info
        ("Unused variables\nThe quantified expression\n\n\t" ^
         string_of_expression e ^
         "\n\nhas the following unused " ^
         (if List.length unused = 1 then "variable" else "variables") ^
         "\n\n\t" ^
         String.concat
           ", "
           (List.map (fun i -> ST.string names.(i)) unused)
         ^
             "\n")
    end;
    mn,
    {info = info;
     context = c;
     term = EQExp (et0,is_all)}

  and inspect
      (info:info)
      (insp:expression)
      (cases: (expression*expression) list)
      (mn: max_numbers)
      (c:Context.t)
      : max_numbers * eterm
      =
    let ninspected = expression_list_length insp in
    let mn = {mn with max_globs = mn.max_globs + 1} in
    let mn,einsp = first info insp mn c in
    let mn,ecases =
      List.fold_left
        (fun (mn,ecases) (pat,res) ->
          if ninspected > expression_list_length pat then
            error_info
              info
              ("Illegal pattern\n" ^
               "The pattern\n\n\t" ^
               (string_of_expression pat) ^
               "\n\ndoes not have " ^
               (string_of_int ninspected) ^
               " subpattern and therefore cannot be matched against the\n" ^
               "inspected expression\n\n\t" ^
               (string_of_expression insp) ^
               "\n");
          let pat,names = case_variables info pat false c in
          let c_new = Context.push_untyped names c in
          let mn =
            {mn with
             max_locs = max mn.max_locs (Context.count_type_variables c_new)}
          in
          let mn, epat = first info pat mn c_new in
          let mn, eres = first info res mn c_new in
          mn, (epat,eres) :: ecases
        )
        (mn,[])
        cases
    in
    let ecases = List.rev ecases in
    mn,
    {info = info;
     context = c;
     term = EInspect (einsp,ecases)}

  in

  first
    info
    e
    {max_locs  = Context.count_type_variables c;
     max_globs = 0;
     max_fgs   = 0}
    c


let replicate_tbs (tbs:TB.t list) (flst:int list): (int * TB.t list) list =
  (* Provide all global functions in the list [lst] with an own copy of the
     tbs.
   *)
  let copies tbs = List.rev_map TB.copy tbs
  in
  match flst with
    [] ->
      assert false (* cannot happen; at least one global function must be present. *)
  | fidx :: rest ->
      (fidx,tbs) :: (List.map (fun fidx -> fidx, copies tbs) rest)


let trace_head_terms (level:int) (c:Context.t) (tbs:TB.t list): unit =
  let len = List.length tbs in
  List.iteri
    (fun i tb ->
      let istr = if len = 1 then "" else (string_of_int i) ^ ": " in
      printf "%s%s%s\n"
        (prefix level)
        istr
        (TB.string_of_complete_head_term tb)
    )
    tbs


let string_of_required_types (tbs:TB.t list): string =
  (if List.length tbs = 1 then
    "the required type"
  else
    "any of the required types") ^
  "\n\n\t" ^
  String.concat
    "\n\t"
    (List.map TB.string_of_required_type tbs) ^
  "\n"


let filter_global_functions
    (info:info)
    (flst:int list)            (* The possible global functions *)
    (nargs:int)                (* The actual number of arguments *)
    (tbs:TB.t list)
    : TB.t list
    =
  (* Analyze the possible global functions [flst] unify the result type with the
     required type and return each global function with a proper type context.

     Report an error if no function can be unified with any of the required
     return types.
   *)
  let flst1 = replicate_tbs tbs flst in
  let tbs1 =
    List.fold_left
      (fun tbs1 (fidx,tbs) ->
        let ftbs =
          List.fold_left
            (fun ftbs tb ->
              try
                TB.start_global_application fidx nargs tb;
                tb :: ftbs
              with Reject ->
                ftbs
            )
            []
            tbs
        in
        List.append tbs1 ftbs
      )
      []
      flst1
  in
  if tbs1 = [] then
    error_info
      info
      (let one = List.length flst = 1 in
      "Type mismatch\n" ^
       (if one then
         "The function\n\n\t"
       else "None of the functions\n\n\t") ^
      (let c = TB.context (List.hd tbs) in
       String.concat
         "\n\n\t"
         (List.map (fun fidx -> Context.string_of_feature_signature fidx c) flst)
      ) ^ "\n\n" ^
      (if one then "cannot " else "can ") ^
      "accept " ^ (string_of_int nargs) ^
      " argument(s) and return an object matching\n" ^
      string_of_required_types tbs);
  tbs1


let variable_type_mismatch
    (info:info) (i:int) (c:Context.t) (tbs:TB.t list)
    : unit
    =
  error_info
    info
    ("Type mismatch\n" ^
     "The variable \"" ^ ST.string (Context.variable_name i c) ^
     "\" has type\n\n\t" ^
     Context.string_of_type (Context.variable_type i c) c ^
     "\n\nwhich does not match " ^
     string_of_required_types tbs)







let analyze_eterm
    (et_outer:eterm)
    (tbs:TB.t list)
    (level:int)
    (trace:bool)
    : TB.t list
    =
  let rec analyze
      (et:eterm)
      (tbs:TB.t list)
      (level:int)
      : TB.t list
      =
    match et.term with
      EVar i ->
        variable et i tbs level
    | EGlAppl (flst,args,am) ->
        global_application et flst args am tbs level
    | EAppl (f,args,am) ->
        term_application et f args am tbs level
    | ELam (pres,et0,is_pred) ->
        if trace then begin
          printf "%s%s expression\n"
            (prefix level)
            (if is_pred then "predicate" else "function");
          printf "%sinner term\n" (prefix level)
        end;
        List.iter
          (fun tb -> TB.start_lambda et0.context is_pred tb)
          tbs;
        let tbs1 = analyze et0 tbs (level+1)
        in
        let npres = List.length pres in
        if trace && npres > 0 then
          printf "%spreconditions\n" (prefix level);
        let tbs2 =
          List.fold_left
            (fun tbs et ->
              List.iter TB.expect_boolean tbs;
              analyze et tbs (level+1))
            tbs1
            pres
        in
        List.iter
          (fun tb -> TB.complete_lambda is_pred (List.length pres) tb)
          tbs2;
        if trace then
          trace_head_terms level et.context tbs2;
        tbs2
    | EQExp (et0,is_all) ->
        if trace then
          printf "%s%s quantification\n"
            (prefix level)
            (if is_all then "universal" else "existential");
        let tbs1 =
          List.fold_left
            (fun tbs tb ->
              try
                TB.start_quantified et0.context tb;
                tb :: tbs
              with Reject ->
                tbs
            )
            []
            tbs
        in
        if tbs1 = [] then
          assert false;
        let tbs2 = analyze et0 tbs1 (level+1) in
        List.iter
          (fun tb -> TB.complete_quantified is_all tb)
          tbs2;
        if trace then
          trace_head_terms level et.context tbs2;
        tbs2
    | EIf (cond,e1,e2) ->
        if trace then begin
          printf "%sif\n" (prefix level);
          printf "%sthen expression\n" (prefix level)
        end;
        let tbs1 = analyze e1 tbs (level+1)
        in
        if trace then
          printf "%selse expression\n" (prefix level);
        List.iter TB.expect_else_expression tbs1;
        let tbs2 = analyze e2 tbs1 (level+1)
        in
        if trace then
          printf "%scondition\n" (prefix level);
        List.iter TB.expect_boolean tbs2;
        let tbs3 = analyze cond tbs2 (level+1)
        in
        List.iter TB.complete_if_expression tbs3;
        if trace then
          trace_head_terms level et.context tbs3;
        tbs3
    | EInspect (insp,cases) ->
        if trace then
          printf "%sinspect\n" (prefix level);
        List.iter TB.start_inspect tbs;
        let tbs1 = analyze insp tbs (level+1) in
        List.iter TB.start_cases tbs1;
        let tbs2 =
          List.fold_left
            (fun tbs (pat,res) ->
              assert (pat.context == res.context);
              if trace then begin
                printf "%scase\n" (prefix level);
                printf "%spattern\n" (prefix (level+1))
              end;
              List.iter (fun tb -> TB.start_case pat.context tb) tbs;
              let tbs1 = analyze pat tbs  (level+2) in
              if trace then
                printf "%sresult\n" (prefix (level+1));
              List.iter TB.expect_case_result tbs1;
              let tbs2 = analyze res tbs1 (level+2) in
              List.iter TB.complete_case tbs2;
              tbs2
            )
            tbs1
            cases
        in
        let ncases = List.length cases in
        List.iter (fun tb -> TB.complete_inspect ncases tb) tbs2;
        if trace then
          trace_head_terms level et.context tbs2;
        tbs2
    | EIndset rules ->
        if trace then
          printf "%sinductive set\n" (prefix level);
        assert (rules <> []);
        let c0 = (List.hd rules).context in
        let tbs1 =
          List.fold_left
            (fun tbs tb ->
              try
                TB.start_inductive_set c0 tb;
                tb :: tbs
              with Reject ->
                tbs
            )
            []
            tbs
        in
        let tbs2,nrules =
          List.fold_left
            (fun (tbs,i) rule ->
              if trace then
                printf "%srule %d\n" (prefix level) i;
              List.iter TB.expect_boolean tbs;
              let tbs = analyze rule tbs (level+1) in
              tbs, i+1
            )
            (tbs1,0)
            rules
        in
        List.iter (fun tb -> TB.complete_inductive_set nrules tb) tbs2;
        if trace then
          trace_head_terms level et.context tbs2;
        tbs2

  and variable et i tbs level =
    let tbs1 =
      List.fold_left
        (fun tbs1 tb ->
          try
            TB.add_variable i tb;
            tb :: tbs1
          with Reject ->
            tbs1
        )
        []
        tbs
    in
    if tbs1 = [] then
      variable_type_mismatch et.info i et.context tbs;
    if trace then
      trace_head_terms level et.context tbs1;
    tbs1

  and term_application et f args am tbs level =
    if trace then
      printf "%sfunction term\n" (prefix level);
    let nargs = Array.length args in
    List.iter (fun tb -> TB.start_term_application nargs tb) tbs;
    let tbs1 = analyze f tbs (level+1) in
    let tbs2 = arguments args tbs1 level in
    List.iter (fun tb -> TB.complete_application am tb) tbs2;
    if trace then
      trace_head_terms level et.context tbs2;
    tbs2

  and global_application et flst args am tbs level =
    if trace then begin
      let len = List.length flst
      in
      List.iteri
        (fun i fidx ->
          let istr = if len = 1 then "" else (string_of_int i) ^ ": " in
          printf "%s%s%s\n"
            (prefix level)
            istr
            (Context.string_of_feature_signature fidx et.context)
        )
        flst
    end;
    let nargs = Array.length args in
    let tbs1 =
      filter_global_functions et.info flst nargs tbs
    in
    let tbs2 = arguments args tbs1 (level+1)
    in
    List.iter (fun tb -> TB.complete_application am tb) tbs2;
    if trace then
      trace_head_terms level et.context tbs2;
    tbs2

  and arguments args tbs level =
    let nargs = Array.length args in
    interval_fold
      (fun tbs i ->
        if trace then
          printf "%sargument %d\n" (prefix level) i;
        List.iter (fun tb -> TB.expect_argument i tb) tbs;
        analyze args.(i) tbs (level+1)
      )
      tbs 0 nargs
  in

  analyze et_outer tbs level







let get_different_globals (t1:term) (t2:term) (c:Context.t): string * string =
  let nvars = Context.count_variables c
  and ft    = Context.feature_table c
  in
  let vars1 = List.rev (Term.used_variables_from t1 nvars true)
  and vars2 = List.rev (Term.used_variables_from t2 nvars true) in
  let lst   = Mylist.combine vars1 vars2 in
  let i,j =
    try List.find (fun (i,j) -> i<>j) lst
    with Not_found -> assert false (* cannot happen *) in
  let str1 = Feature_table.string_of_signature (i-nvars) ft
  and str2 = Feature_table.string_of_signature (j-nvars) ft in
  str1, str2


let undefined_formal_generics (info:info) (ft:Feature_table.t) (tb:TB.t): unit =
  let lst = TB.undefined_globals tb
  and tstr = TB.string_of_head_term tb
  in
  printf "undefined_formal_generics %d\n" (List.length lst);
  let fstring fidx lst =
    let fstr = Feature_table.string_of_signature fidx ft
    and tvs,s = Feature_table.signature0 fidx ft
    in
    let fgnames = Tvars.fgnames tvs
    and nfgs = Tvars.count_fgs tvs in
    let undefs =
      String.concat
        ","
        (List.map
           (fun i -> assert (i < nfgs); ST.string fgnames.(i))
           lst)
    in
    fstr ^ " undefined: " ^ undefs
  in
  let undefstr =
    String.concat
      "\n\t"
      (List.rev_map
         (fun (fidx,lst) ->
           fstring fidx lst
         )
         lst)
  in
  error_info
    info
    ("Undefined formal generics\n" ^
     "Not all formal generics of functions/constants could be determined\n" ^
     "in the expression\n\n\t" ^
     tstr ^ "\n\n" ^
     "undefind formal generics:\n\n\t" ^
     undefstr ^
     "\n"
    )



let general_term
    (ie:info_expression) (tp:type_term option) (c:Context.t)
    : term =
  let trace = true (*Context.verbosity c >= 5*) in
  if trace then
    printf "\ntyper analyze expression\n\n\t%s\n\n" (string_of_expression ie.v);
  let mn,et = first_pass ie.i ie.v c in
  let tb = TB.make tp mn.max_locs mn.max_globs mn.max_fgs c in
  assert (TB.context tb == c);
  let lst = analyze_eterm et [tb] 0 trace
  in
  if trace then
    printf "typer end analysis\n\n";
  match lst with
    [] ->
      assert false (* Cannot happen; at least one term is returned, otherwise an
                      error is reported *)
  | [tb] ->
      if TB.has_undefined_globals tb then
        undefined_formal_generics
          ie.i
          (Context.feature_table c)
          tb;
      TB.update_context c tb;
      let t = TB.result_term tb in
      assert (Context.is_well_typed t c);
      t
  | tb1 :: tb2 :: _ ->
      let t1 = TB.head_term tb1
      and t2 = TB.head_term tb2 in
      let str1, str2 = get_different_globals t1 t2 c in
      let estr = string_of_expression ie.v in
      error_info
        ie.i
        ("The expression\n\n\t" ^ estr ^ "\n\nis ambiguous\n\n\t" ^
         str1 ^ "\n\t" ^ str2)




let typed_term (ie:info_expression) (tp:type_term) (c:Context.t): term =
  assert (not (Context.is_global c));
  general_term ie (Some tp) c



let untyped_term (ie:info_expression) (c:Context.t): term =
  assert (not (Context.is_global c));
  general_term ie None c



let boolean_term (ie: info_expression) (c:Context.t): term =
  assert (not (Context.is_global c));
  general_term ie (Some (Context.boolean c)) c


let result_term (ie:info_expression) (c:Context.t): term =
  assert (not (Context.is_global c));
  assert (Context.has_result c);
  let tp = Context.result_type c in
  typed_term ie tp c
