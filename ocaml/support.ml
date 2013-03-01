(*
-----------------------------------------------------------------------------
   Exceptions
-----------------------------------------------------------------------------
*)

exception Exit_error of string


(*
-----------------------------------------------------------------------------
   Line and column info
-----------------------------------------------------------------------------
*)

type info = FINFO of int*int | UNKNOWN

type 'a withinfo = {i: info; v: 'a}

let create_info l c = FINFO(l,c)

let withinfo i v = {i=i; v=v}

let noinfo v = {i=UNKNOWN; v=v}

let info_string (name:string) (i:info) =
  match i with
    FINFO(l,c) ->
      name ^ ":" ^ (string_of_int l) ^ ":" ^ (string_of_int c) ^ ":"
  | UNKNOWN    ->
      name ^":"

let info_from_position pos =
  let l = pos.Lexing.pos_lnum
  and c = pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1
  in
  create_info l c


(*
-----------------------------------------------------------------------------
   Syntax error function
-----------------------------------------------------------------------------
*)
let parse_error_fun : (string->unit) ref =
  ref (fun str -> Printf.eprintf "%s\n" str;  failwith "Syntax error")



(*
-----------------------------------------------------------------------------
   Symbol table
-----------------------------------------------------------------------------
*)

type symbol_table = {mutable st_count: int;
                     mutable st_arr:   string array;
                     st_map:           (string,int) Hashtbl.t}

let symbol_table = {st_count=0;
                    st_arr= Array.make 1 "";
                    st_map = Hashtbl.create 53}

let added_symbol str =
  let st = symbol_table
  in
  let cnt = st.st_count
  in
  let _ =
    if Array.length st.st_arr = cnt then
      let narr = Array.make (2*cnt) ""
      in
      Array.blit st.st_arr 0  narr 0 cnt;
      st.st_arr <- narr
    else
      ()
  in
  assert (cnt < Array.length st.st_arr);
  Hashtbl.add st.st_map str cnt;
  st.st_arr.(cnt) <- str;
  st.st_count <- cnt + 1;
  cnt


let symbol str =
  try
    Hashtbl.find symbol_table.st_map str
  with
    Not_found ->
      added_symbol str

let symbol_string (s:int) =
  assert (s < symbol_table.st_count);
  symbol_table.st_arr.(s)




(*
-----------------------------------------------------------------------------
   Parsing types
-----------------------------------------------------------------------------
*)

(* Utility functions *)

let rec string_of_path (p: int list) =
  match p with
    [] -> ""
  | f::t -> (symbol_string f) ^ "." ^ (string_of_path t)


let rec string_of_list (l: 'a list) (sfun: 'a -> string) (sep: string) =
  match l with
    [] -> ""
  | f::t ->
      (sfun f) ^ (List.fold_left (fun str el -> str ^ sep ^ (sfun el))"" t)


let rec split_list (l: 'a list) (sep: 'a -> bool) =
  match l with
    [] -> []
  | f::t ->
      let res = split_list t sep
      in
      match res with
        [] -> [[f]]
      | f1::t1 ->
          if sep f
          then [f]::res
          else (f::f1)::t1



(* Classes and types *)


type header_mark = No_hmark | Case_hmark | Immutable_hmark | Deferred_hmark

type class_t =  {hmark:header_mark withinfo; cname: int withinfo}

type type_t =
    Normal_type of int list * int * type_t list   (* kernel.ANY,
                                                 kernel.ARRAY[NATURAL] *)
  | Current_type of type_t list
  | Arrow_type of type_t * type_t        (* A -> B              *)
  | Ghost_type of type_t
  | Tuple_type of type_t list
  | QMark_type of type_t


let rec string_of_type (t:type_t) =
  let actuals l =
    match l with
      [] -> ""
      | _::_ ->
          "["
          ^ (string_of_list l string_of_type ",")
          ^ "]"
  in
  match t with
    Normal_type (p,n,l) ->
      let ps = string_of_path p
      in
      ps ^ (symbol_string n) ^ (actuals l)
  | Current_type l -> "CURRENT" ^ (actuals l)
  | Arrow_type (t1,t2) ->
      (string_of_type t1) ^ "->" ^ (string_of_type t2)
  | Ghost_type t ->
      "ghost " ^  (string_of_type t)
  | Tuple_type l -> actuals l
  | QMark_type t -> (string_of_type t) ^ "?"



(* Formal arguments *)

type entities =
    Untyped_entities of int list
  | Typed_entities   of int list * type_t


let string_of_entities (args: entities) =
  match args with
    Typed_entities (l,t) ->
      (string_of_list l symbol_string ",") ^ ":" ^ string_of_type t
  | Untyped_entities l -> string_of_list l symbol_string ","


let string_of_formals (args: entities list) =
  string_of_list args string_of_entities ","




(* Expressions *)

type quantifier =
    Universal
  | Existential

type operator =
    Plusop
  | Minusop
  | Timesop
  | Divideop
  | Caretop
  | Eqop
  | NEqop
  | Eqvop
  | NEqvop
  | LTop
  | LEop
  | GTop
  | GEop
  | Andop
  | Orop
  | Notop
  | Barop
  | DBarop
  | Arrowop
  | Bracketop
  | DArrowop
  | DColonop
  | Inop
  | Notinop
  | Freeop  of int
  | RFreeop of int

type associativity = Left | Right | Nonassoc

let opdata op =
  match op with
    Plusop    -> "+",   45,  Left
  | Minusop   -> "-",   45,  Left
  | Timesop   -> "*",   50,  Left
  | Divideop  -> "/",   50,  Left
  | Caretop   -> "^",   55,  Right
  | Eqop      -> "=",   35,  Left
  | NEqop     -> "/=",  35,  Left
  | Eqvop     -> "~",   35,  Left
  | NEqvop    -> "/~",  35,  Left
  | LTop      -> "<",   35,  Left
  | LEop      -> "<=",  35,  Left
  | GTop      -> ">",   35,  Left
  | GEop      -> ">=",  35,  Left
  | Andop     -> "and", 25,  Left
  | Orop      -> "or",  25,  Left
  | Notop     -> "not", 65,  Nonassoc
  | Barop     -> "|",   40,  Left
  | DBarop    -> "||",  40,  Left
  | Arrowop   -> "->",  20,  Right
  | Bracketop -> "[]",  1000, Nonassoc
  | DArrowop  -> "=>",  20,  Right
  | DColonop  -> "::",  55,  Right
  | Inop      -> "in",  60,  Nonassoc
  | Notinop      -> "/in",  60, Nonassoc
  | Freeop  i -> symbol_string i, 60,  Left
  | RFreeop i -> symbol_string i, 61,  Right


let is_letter ch =
  let ic = Char.code ch
  in
  ((Char.code 'A') <= ic && ic <= (Char.code 'Z')) ||
  ((Char.code 'a') <= ic && ic <= (Char.code 'z'))


let rstring_of_op op =
  let s,_,_ = opdata op in s

let string_of_op op =
  match op with
    Andop ->  " and "
  | Orop  ->  " or "
  | Notop ->  "not "
  | Inop  ->  " in "
  | Notinop -> " /in "
  | _     ->
      let s,_,_ = opdata op
      in
      s



type expression =
    Identifier    of int
  | Number        of string
  | ExpResult
  | ExpCurrent
  | Exptrue
  | Expfalse
  | Expparen      of expression
  | Expbracket    of expression
  | Expop         of operator
  | Funapp        of expression * expression
  | Bracketapp    of expression * expression
  | Expset        of expression
  | Binexp        of operator * expression * expression
  | Unexp         of operator * expression
  | Typedexp      of expression * type_t
  | Taggedexp     of expression * expression
  | Explist       of expression list
  | Expassign     of expression * expression
  | Expif         of (info_expression * compound) list * compound option
  | Expinspect    of
      info_expression
        * (info_expression * compound) list
  | Expproof      of compound * implementation option * compound
  | Expquantified of quantifier * entities list * expression

and
      info_expression = expression withinfo
and
      compound        = info_expression list
and
      implementation  =
    Impdeferred
  | Impbuiltin
  | Impevent
  | Impdefined of locals option * bool * compound

and local_declaration =
    Unassigned of entities list
  | Assigned   of entities list * expression

and locals          = local_declaration list

let rec string_of_expression  ?(wp=false) (e:expression) =
  let strexp e         = string_of_expression ~wp:wp e
  and withparen str wp = if wp then "(" ^ str ^ ")" else str
  in
  match e with
    Identifier id -> symbol_string id
  | Number num    -> num
  | ExpResult     -> "Result"
  | ExpCurrent    -> "Current"
  | Exptrue       -> "true"
  | Expfalse      -> "false"
  | Expparen e   -> "(" ^ (strexp e) ^")"
  | Expbracket e -> "[" ^ (strexp e) ^"]"
  | Expop op     -> "(" ^ (rstring_of_op op) ^ ")"
  | Funapp (f,args) ->
      (strexp f) ^ "(" ^ (strexp args) ^ ")"
  | Bracketapp (tgt,args) ->
      (strexp tgt) ^ "[" ^ (strexp args) ^ "]"
  | Expset s ->
      "{" ^  (strexp s) ^ "}"
  | Binexp (op,e1,e2) ->
      withparen ((strexp e1) ^ (string_of_op op) ^ (strexp e2)) wp
  | Unexp (op,e) ->
      withparen ((string_of_op op) ^ (strexp e)) wp

  | Taggedexp (t,e) ->
      withparen((strexp t) ^ ":" ^ (strexp e)) wp
  | Typedexp (e,t) ->
      withparen ((strexp e) ^ ":" ^ (string_of_type t)) wp
  | Explist l ->
      withparen (string_of_list l strexp ",") wp

  | Expassign (e1,e2) ->
      withparen ((strexp e1) ^ ":=" ^ (strexp e2)) wp

  | Expif (thenlist,elsepart) ->
      "if "
      ^ (string_of_list
           thenlist
           (fun tp ->
             let cond,comp = tp
             in
             (string_of_expression cond.v)
             ^ " then "
             ^ (string_of_compound comp))
           " elseif ")
      ^ (
        match elsepart with
          None -> ""
        | Some e -> " else " ^ (string_of_compound e))
      ^ " end"
  | Expinspect (inspexp,caselist) ->
      "inspect "
      ^ (string_of_expression inspexp.v)
      ^ (string_of_list
           caselist
           (fun ce ->
             let pat,comp = ce
             in
             " case " ^ (string_of_expression pat.v)
             ^ " then " ^  (string_of_compound comp))
           "")
      ^ " end"
  | Expproof (req,imp_opt,ens) ->
      "require " ^ (string_of_compound req)
      ^
        (match imp_opt with
          Some imp -> " " ^ string_of_implementation imp
        | None     -> "")
      ^ " ensure " ^ (string_of_compound ens) ^ " end"

  | Expquantified (q,elist,exp) ->
      (match q with Universal -> "all" | Existential -> "some")
      ^ "(" ^ (string_of_formals elist) ^ ") "  ^ (string_of_expression exp)

and string_of_compound comp =
  string_of_list comp (fun ie -> string_of_expression ie.v) ";"

and string_of_locals loc =
  string_of_list
    loc
    (fun el ->
      match el with
        Unassigned elist -> string_of_formals elist
      | Assigned (elist,exp) ->
          (string_of_formals elist) ^ ":=" ^ (string_of_expression exp))
    ";"

and string_of_implementation imp =
  match imp with
    Impdeferred -> "deferred"
  | Impbuiltin  -> "note built_in"
  | Impevent    -> "note event"
  | Impdefined (loc_opt,dochk,comp) ->
      (match loc_opt with
        None -> ""
      | Some loc -> "local " ^ (string_of_locals loc) ^ " ")
      ^
        (if dochk then "do " else "check ")
      ^
        (string_of_compound comp)










(* Modules *)

type module_t = {classes: class_t list;
                 formal_generics: (int withinfo * type_t withinfo) list;
                 features: int list}


let empty_module = {classes=[]; features=[]; formal_generics=[]}

let class_added (c:class_t) (m:module_t) = {m with classes = c::m.classes}


let formal_generic_added (n:int withinfo) (t:type_t withinfo)  (m:module_t)
    = {m with formal_generics = (n,t)::m.formal_generics}




