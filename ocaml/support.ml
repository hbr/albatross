(*
-----------------------------------------------------------------------------
   Command line options
-----------------------------------------------------------------------------
*)

module Options: sig
  val is_prover_basic:    unit -> bool
  val is_prover_forward:  unit -> bool
  val is_prover_backward: unit -> bool
  val set_prover_basic:   unit -> unit
  val set_prover_forward: unit -> unit

  val is_tracing_failed_proof: unit -> bool
  val is_tracing_proof:        unit -> bool
  val trace_level:             unit -> int
  val set_trace_failed_proof:  unit -> unit
  val set_trace_proof:         unit -> unit
  val set_trace_level:         int  -> unit

  val is_statistics:           unit -> bool
  val set_statistics:          unit -> unit

  val has_goal_limit:   unit -> bool
  val goal_limit:       unit -> int
  val set_goal_limit:   int  -> unit
  val set_no_limit:     unit -> unit
end = struct

  let glimit = ref (Some 200)

  let has_goal_limit (): bool =
    match !glimit with None -> false | Some _ -> true

  let goal_limit (): int =
    assert (has_goal_limit ());
    match !glimit with
      None -> assert false
    | Some n -> n

  let set_goal_limit (i:int): unit =
    glimit := Some i

  let set_no_limit () : unit =
    glimit := None

  let prover   = ref 10

  let is_prover_basic ()    = (0 <= !prover)
  let is_prover_forward ()  = (1 <= !prover)
  let is_prover_backward () = (1 <  !prover)

  let set_prover_basic   () = prover := 0
  let set_prover_forward () = prover := 1

  let trace    = ref 0
  let tr_level = ref 0

  let is_tracing_failed_proof () = (1 <= !trace)
  let is_tracing_proof ()        = (2 <= !trace)
  let trace_level ()             = !tr_level
  let set_trace_failed_proof ()  = trace := 1
  let set_trace_proof ()         = trace := 2
  let set_trace_level (i:int)    = tr_level := i

  let statistics = ref false
  let is_statistics () = !statistics
  let set_statistics () = statistics := true
end


(*
-----------------------------------------------------------------------------
   Statistics
-----------------------------------------------------------------------------
*)

module Statistics: sig
  val n_goals:       unit -> int
  val max_goals:     unit -> int
  val average_goals: unit -> int
  val n_proofs:      unit -> int

  val proof_done:    int -> int -> unit

  val write: unit -> unit
end = struct
  let n       = ref 0
  let nf      = ref 0
  let max     = ref 0
  let maxf    = ref 0
  let np      = ref 0

  let n_goals ()        = !n
  let max_goals ()      = !max
  let n_proofs ()       = !np
  let average_goals ()  = if !np<>0 then !n  / !np else 1
  let average_failed () = if !np<>0 then !nf / !np else 1

  let proof_done (i:int) (ifailed:int): unit =
    assert (0 < i);
    n  := !n  + i;
    nf := !nf + ifailed;
    np := !np + 1;
    begin
      if !max  < i       then max  := i else ();
      if !maxf < ifailed then maxf := ifailed else ()
    end

  let write (): unit =
    if Options.is_statistics () then
      Printf.printf "\
Statistics
    proofs %4d
    goals (failed)
        per proof  max %d(%d), avg %d(%d)
        total %d(%d)
"
        !np
        !max  !maxf (average_goals ()) (average_failed ())
        !n !nf
    else
      ()

end


(*
-----------------------------------------------------------------------------
   Exceptions
-----------------------------------------------------------------------------
*)

exception Exit_error of string
exception Tohandle of string
exception Eiffel_error of string


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

let info_string (name:string) (i:info): string =
  match i with
    FINFO(l,c) ->
      name ^ ":" ^ (string_of_int l) ^ ":" ^ (string_of_int c) ^ ":"
  | UNKNOWN    ->
      name ^":"

let info_from_position (pos:Lexing.position) =
  let l = pos.Lexing.pos_lnum
  and c = pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1
  in
  create_info l c


exception Error_info of info*string
exception Error_fileinfo of string*info*string

let error_info (i:info) (str:string) =
  raise (Error_info (i,str))

let not_yet_implemented (i:info) (str:string) =
  error_info i (str ^ " not yet implemented")


(*
-----------------------------------------------------------------------------
   Syntax error function
-----------------------------------------------------------------------------
*)
let parse_error_fun : (string->unit) ref =
  ref (fun str -> Printf.eprintf "%s\n" str;  failwith "Syntax error")


module Parse_info: sig

  val file_name:     unit -> string
  val last_position: unit -> Lexing.position
  val is_use_interface:   unit -> bool
  val is_check_interface: unit -> bool
  val is_interface:       unit -> bool
  val is_module:          unit -> bool

  val set_file_name:     string -> unit
  val set_last_position: Lexing.position -> unit
  val set_use_interface:   unit -> unit
  val set_check_interface: unit -> unit
  val set_module:          unit -> unit

  val print_error:  Lexing.position -> string -> unit
  val print_unexpected: unit -> unit

end = struct

  let fname:string ref              = ref ""
  let last_pos: Lexing.position ref = ref (Lexing.dummy_pos)
  let uiface: bool ref              = ref false
  let ciface: bool ref              = ref false

  let file_name (): string =
    !fname

  let last_position (): Lexing.position =
    !last_pos

  let is_use_interface   (): bool = !uiface
  let is_check_interface (): bool = !ciface
  let is_interface ():       bool = !uiface || !ciface
  let is_module(): bool     = not (!uiface || !ciface)
  let set_use_interface (): unit =
    uiface := true; ciface := false
  let set_check_interface (): unit =
    uiface := false; ciface := true
  let set_module (): unit =
    uiface := false; ciface := false

  let set_file_name (fn: string): unit =
    fname := fn

  let set_last_position (pos: Lexing.position): unit =
    last_pos := pos

  let print_error (pos:Lexing.position) (str:string): unit =
    let line = pos.Lexing.pos_lnum
    and col  = pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1
    in
    Printf.eprintf "%s:%d:%d: %s\n" !fname line col str

  let print_unexpected (): unit =
    print_error !last_pos "Syntax error: Unexpected token"
end (* Parse_info *)


(*
-----------------------------------------------------------------------------
   Symbol tables
-----------------------------------------------------------------------------
*)

module ST : sig
  val symbol: string -> int
  val string: int    -> string
  val count:  unit   -> int
end = struct
  open Container
  let kt                   = Key_table.empty ()
  let symbol (str:string)  = Key_table.index (String.copy str) kt
  let string (i:int)       = Key_table.key   i   kt
  let count ()             = Key_table.count kt
end


(*
-----------------------------------------------------------------------------
   Parsing types
-----------------------------------------------------------------------------
*)

(* Utility functions *)

let rec string_of_path (p: int list) =
  match p with
    [] -> ""
  | f::t -> (ST.string f) ^ "." ^ (string_of_path t)

let string_of_option  (o: 'a option) (sfun: 'a -> string) =
  match o with
    None -> ""
  | Some e -> sfun e

let rec string_of_list (l: 'a list) (sfun: 'a -> string) (sep: string) =
  String.concat sep (List.map sfun l)

(* more efficient but more complicated
let rec string_of_list (l: 'a list) (sfun: 'a -> string) (sep: string) =
  match l with
    [] -> ""
  | f::t ->
      (sfun f) ^ (List.fold_left (fun str el -> str ^ sep ^ (sfun el))"" t)
*)


let rec split_list (l: 'a list) (sep: 'a -> bool): 'a list list =
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



(* Types *)

type type_t =
    Normal_type of (int list) * int * type_t list   (* kernel.ANY,
                                                kernel.ARRAY[NATURAL] *)
  | Current_type of type_t list
  | Arrow_type of type_t * type_t        (* A -> B              *)
  | Ghost_type of type_t
  | Tuple_type of type_t list
  | QMark_type of type_t
  | Paren_type of type_t


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
      ps ^ (ST.string n) ^ (actuals l)
  | Current_type l -> "CURRENT" ^ (actuals l)
  | Arrow_type (t1,t2) ->
      (string_of_type t1) ^ "->" ^ (string_of_type t2)
  | Ghost_type t ->
      "ghost " ^  (string_of_type t)
  | Tuple_type l -> actuals l
  | QMark_type t -> (string_of_type t) ^ "?"
  | Paren_type t -> "(" ^ (string_of_type t) ^ ")"


type return_type = (type_t*bool*bool) withinfo option


(* Formal arguments *)

type entities =
    Untyped_entities of int list
  | Typed_entities   of int list * type_t


let string_of_entities (args: entities) =
  match args with
    Typed_entities (l,t) ->
      (string_of_list l ST.string ",") ^ ":" ^ string_of_type t
  | Untyped_entities l -> string_of_list l ST.string ","


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
  | Oldop
  | Notop
  | Barop
  | DBarop
  | Arrowop
  | Bracketop
  | Parenop
  | DArrowop
  | DColonop
  | Inop
  | Notinop
  | Allop
  | Someop
  | Freeop  of int
  | RFreeop of int

type associativity = Left | Right | Nonassoc

let operator_data op =
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
  | Oldop     -> "old", 65,  Nonassoc
  | Notop     -> "not", 65,  Nonassoc
  | Barop     -> "|",   40,  Left
  | DBarop    -> "||",  40,  Left
  | Arrowop   -> "->",  13,  Right
  | Parenop   -> "()",  1000, Nonassoc
  | Bracketop -> "[]",  1000, Nonassoc
  | DArrowop  -> "=>",  20,  Right
  | DColonop  -> "::",  55,  Right
  | Inop      -> "in",  60,  Nonassoc
  | Notinop   -> "/in", 60, Nonassoc
  | Allop     -> "all",  8,  Nonassoc
  | Someop    -> "some", 8, Nonassoc
  | Freeop  i -> ST.string i, 60,  Left
  | RFreeop i -> ST.string i, 61,  Right


let is_binary (op:operator): bool =
  match op with
    Plusop | Minusop | Timesop | Divideop | Caretop | Eqop | NEqop
  | Eqvop  | NEqvop  | LTop    | LEop     | GTop    | GEop | Andop
  | Orop   | Barop   | DBarop  | Inop     | Notinop
  | DArrowop -> true
  | Freeop i | RFreeop i -> true
  | _ -> false


let is_unary (op:operator): bool =
  match op with
    Plusop | Minusop | Notop | Oldop | Allop | Someop -> true
  | Freeop i | RFreeop i -> true
  | _ -> false


let is_nary (op:operator): bool =
  match op with
    Parenop | Bracketop -> true
  | _ -> false




let is_letter ch =
  let ic = Char.code ch
  in
  ((Char.code 'A') <= ic && ic <= (Char.code 'Z')) ||
  ((Char.code 'a') <= ic && ic <= (Char.code 'z'))


let operator_to_rawstring op =
  let s,_,_ = operator_data op in s

let operator_to_string op =
  match op with
    Andop ->  " and "
  | Orop  ->  " or "
  | Oldop ->  "old "
  | Notop ->  "not "
  | Inop  ->  " in "
  | Notinop -> " /in "
  | _     ->
      let s,_,_ = operator_data op
      in
      s


type is_do_block = bool


type expression =
    Identifier    of int
  | Expnumber     of int
  | ExpResult
  | ExpCurrent
  | Exptrue
  | Expfalse
  | Expparen      of expression
  | Expbracket    of expression
  | Exparrow      of entities list * expression
  | Expop         of operator
  | Funapp        of expression * expression
  | Bracketapp    of expression * expression
  | Expdot        of expression * expression
  | Expset        of expression
  | Exppred       of entities list withinfo * expression
  | Binexp        of operator * expression * expression
  | Unexp         of operator * expression
  | Tupleexp      of expression * expression
  | Typedexp      of expression * type_t
  | Taggedexp     of int * expression
  | Explist       of expression list
  | Expcolon      of expression * expression
  | Expassign     of expression * expression
  | Expif         of (info_expression * compound) list * compound option
  | Expinspect    of
      info_expression
        * (info_expression * compound) list
  | Expproof      of compound * implementation option * compound
  | Expquantified of quantifier * entities list withinfo * expression

and
      info_expression = expression withinfo
and
      compound        = info_expression list
and
      implementation  =
    Impdeferred
  | Impbuiltin
  | Impevent
  | Impdefined of locals option * is_do_block * compound

and local_declaration =
    Unassigned of entities list
  | Assigned   of entities list * expression
  | Local_feature of int * entities list * return_type * feature_body

and locals          = local_declaration list

and feature_body = compound option * implementation option * compound option


let rec string_of_expression  ?(wp=false) (e:expression) =
  let strexp e         = string_of_expression ~wp:wp e
  and withparen str wp = if wp then "(" ^ str ^ ")" else str
  in
  match e with
    Identifier id -> ST.string id

  | Expnumber num  -> ST.string num

  | ExpResult     -> "Result"

  | ExpCurrent    -> "Current"

  | Exptrue       -> "true"

  | Expfalse      -> "false"

  | Expparen e   -> "(" ^ (strexp e) ^")"

  | Expbracket e -> "[" ^ (strexp e) ^"]"

  | Exparrow  (l,e) ->
      (string_of_formals l) ^ "->" ^ (string_of_expression e)

  | Expop op     -> "(" ^ (operator_to_rawstring op) ^ ")"

  | Funapp (f,args) ->
      (strexp f) ^ "(" ^ (strexp args) ^ ")"

  | Bracketapp (tgt,args) ->
      (strexp tgt) ^ "[" ^ (strexp args) ^ "]"

  | Expdot (t,f) ->
      withparen ((strexp t) ^ "." ^ (strexp f)) wp

  | Expset s ->
      "{" ^  (strexp s) ^ "}"

  | Exppred (elist,exp) ->
      "{" ^ (string_of_formals elist.v) ^ ":" ^ (string_of_expression exp)^ "}"

  | Binexp (op,e1,e2) ->
      withparen ((strexp e1) ^ (operator_to_string op) ^ (strexp e2)) wp

  | Unexp (op,e) ->
      withparen ((operator_to_string op) ^ (strexp e)) wp

  | Taggedexp (t,e) ->
      withparen ((ST.string t) ^ ":" ^ (strexp e)) wp

  | Typedexp (e,t) ->
      withparen ((strexp e) ^ ":" ^ (string_of_type t)) wp

  | Tupleexp (e1,e2) ->
      "(" ^ (strexp e1) ^ "," ^ (strexp e2) ^ ")"

  | Explist l ->
      withparen (string_of_list l strexp ",") wp

  | Expcolon (e1,e2) ->
      withparen ((strexp e1) ^ ":" ^ (strexp e2)) wp

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
      ^ "(" ^ (string_of_formals elist.v) ^ ") "  ^ (string_of_expression exp)

and string_of_compound comp =
  string_of_list comp (fun ie -> string_of_expression ie.v) ";"

and string_of_locals loc =
  string_of_list
    loc
    (fun el ->
      match el with
        Unassigned elist -> string_of_formals elist
      | Assigned (elist,exp) ->
          (string_of_formals elist) ^ ":=" ^ (string_of_expression exp)
      | Local_feature (id,elist,rt,body) ->
          (ST.string id) ^ "(" ^ (string_of_formals elist) ^")"
          ^
          (match rt with Some t ->
            let tp,exclam,ghost = t.v
            in
            (if exclam then "!:" else ":")
            ^ (if ghost then " ghost " else "")
            ^ (string_of_type tp)
          | None -> "")
          ^ " " ^ (string_of_body body)
    )
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

and string_of_body b =
  let rl,imp_opt,el = b in
  (string_of_option rl (function e -> " require " ^ (string_of_compound e)))
  ^
    (match imp_opt with
      Some imp -> (string_of_implementation imp)
    | None -> "")
  ^ (string_of_option rl (function e -> " ensure " ^ (string_of_compound e)))
  ^ " end"




(* Header mark *)

type header_mark = No_hmark | Case_hmark | Immutable_hmark | Deferred_hmark

let hmark2string (hm:header_mark) =
  match hm with
    No_hmark -> ""
  | Case_hmark -> "case"
  | Immutable_hmark -> "immutable"
  | Deferred_hmark  -> "deferred"

let hmark2string_wblank (hm:header_mark) =
  let str = hmark2string hm in
  if str = "" then str
  else str ^ " "




(* Features *)

type classname = int withinfo

type formal_generics = int list withinfo

type feature_name =
    FNname of int
  | FNoperator of operator
  | FNtrue
  | FNfalse
  | FNnumber of int



let feature_name_to_string (fn:feature_name): string =
  match fn with
    FNname i | FNnumber i -> ST.string i
  | FNoperator op -> operator_to_rawstring op
  | FNtrue ->  "true"
  | FNfalse -> "false"

type name_sig = feature_name * type_t list

type rename_item = name_sig * feature_name

type adaptation_clause =
    Rename of rename_item list
  | Redefine of name_sig list
  | Undefine of name_sig list

type parent = type_t withinfo * adaptation_clause list

type inherit_clause = parent list


type declaration =
    Assertion_feature of int option * entities list withinfo * feature_body
  | Named_feature of
      feature_name withinfo
        * entities list withinfo
        * return_type
        * feature_body option
  | Formal_generic of int withinfo * type_t withinfo
  | Class_declaration of
      header_mark withinfo
        * classname
        * formal_generics
        * inherit_clause list


type use_block = int withinfo list

type module_declaration = use_block * declaration list
