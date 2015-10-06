/* Copyright (C) Helmut Brandl  <helmut dot brandl at gmx dot net>

   This file is distributed under the terms of the GNU General Public License
   version 2 (GPLv2) as published by the Free Software Foundation.
*/

%{
open Support
open Printf
open Container



(* The generated parser calls [parse_error "syntax error"] if it reaches an
   error state *)
let parse_error (_:string): unit =
  raise Parsing.Parse_error

let filename (): string =
  (Parsing.symbol_start_pos ()).Lexing.pos_fname

let symbol_info (): info =
  info_from_position (Parsing.symbol_start_pos ())

let rhs_info (i:int): info =
  info_from_position (rhs_start_pos i)

let cinfo (i:info): string =  info_string (filename ()) i


let syntax_error () = raise (Parsing.Parse_error)


let expression_from_dotted_id (l: int list): expression =
  match List.rev l with
    f::t ->
      let func e i = Expdot (e, Identifier i)
      in
      List.fold_left func (Identifier f) t
  | _    -> assert false


let set_of_expression_list (lst:expression list): expression =
  let singleton = Identifier (ST.singleton)
  in
  let singl (e:expression) = Funapp (singleton,e)
  in
  match List.rev lst with
    [] -> assert false (* cannot happen, list has at least the element [e] *)
  | hd::tl ->
      List.fold_left
        (fun res e ->
          Binexp (Plusop, res, singl e))
        (singl hd)
        tl


let entities_of_expression (info:info) (lst: expression list): entities list =
  let rec entlist lst idlst entlst =
    match lst with
      [] ->
        begin match idlst with
          [] -> entlst
        | _  -> Untyped_entities (List.rev idlst) :: entlst
        end
    | (Identifier id)::lst ->
        entlist lst (id::idlst) entlst
    | (Typedexp (Identifier id,tp))::lst ->
        let idlst = List.rev (id::idlst) in
        let entlst = (Typed_entities (idlst,tp.v))::entlst in
        entlist lst [] entlst
    | e::lst ->
        error_info info ("\"" ^ (string_of_expression e) ^ "\" is not an argument")
  in
  List.rev (entlist lst [] [])


(*
   {a,b,c,...}            -- enumerated
   {a:A,b:B,... : expr}   -- predicate: [arglist,colon expression]
                          --   arglist:  the arguments without the last
                          --   colonexp: lastarg, expr
   {(p): r0, r1, ... }
*)
let predicate_of_expression (info:info) (e:expression): expression =
  match e with
    Expcolon(Expparen(args),pexp) ->
      (* inductively defined set *)
      let lst = expression_list args
      and rules = expression_list pexp in
      let entlst = entities_of_expression info lst in
      Expindset(withinfo info entlst, rules)
  | Expcolon(args,pexp) ->
      (* predicate *)
      let lst = expression_list args in
      let entlst = entities_of_expression info lst in
      Exppred (withinfo info entlst,pexp)
  | _ -> (* enumerated set *)
      set_of_expression_list (expression_list_rev e)


type feature_body1 =
    Body1 of feature_body
  | Body2 of (compound * info_expression)


let body_exp (fb:feature_body1 option): feature_body option * info_expression option =
  match fb with
    None -> None, None
  | Some (Body1 bdy)      -> Some bdy, None
  | Some (Body2 (req,ie)) -> Some(req,None,[]), Some ie

 %}



%token KWCURRENT KWCurrent
%token KWNONE
%token KWPrecursor KWProcess
%token KWResult

%token KWagent     KWall          KWand        KWas         KWassert
%token KWcase      KWclass        KWcheck      KWcreate
%token KWdeferred  KWdo
%token KWelse      KWelseif       KWend        KWensure
%token KWfalse     KWfeature      KWfrom
%token KWghost
%token KWif        KWimmutable    KWimport     KWin
       KWinherit   KWinspect      KWinvariant
%token KWlocal
%token KWnot       KWnote
%token KWold       KWor           KWorif
%token KWproof
%token KWredefine  KWrename       KWrequire
%token KWsome
%token KWthen      KWtrue
%token KWundefine  KWuse
%token KWvariant
%token KWwhile

%token ARROW
%token ASSIGN
%token BAR
%token CARET
%token COLON
%token COMMA
%token DARROW
%token DBAR
%token DCOLON
%token DIVIDE
%token DOT
%token EOF
%token EQ
%token EQV
%token EXCLAM
%token GE
%token GT
%token HIGHEST_PREC
%token LBRACE
%token LBRACKET
%token LE
%token LPAREN
%token LT
%token LOWEST_PREC
%token MINUS
%token NEQ
%token NEQV
%token NEWLINE
%token NOTIN
%token PLUS
%token QMARK
%token RBRACE
%token RBRACKET
%token RPAREN
%token SEMICOL
%token TIMES
%token UMINUS
%token USCORE

%token <int>    UIDENTIFIER
%token <int>    LIDENTIFIER
%token <int>    OPERATOR
%token <int>    ROPERATOR
%token <int>    NUMBER


/*  0 */ %nonassoc LOWEST_PREC  KWghost
/*  5 */ %nonassoc ASSIGN
/*  8 */ %nonassoc KWall     KWsome  /* greedy */
/* 10 */ %right    SEMICOL
/* 13 */ %right    ARROW     /* ??? */
/* 15 */ %left     COLON /* greedy ???*/
/* 18 */ %right    COMMA
/* 20 */ %right    DARROW
/* 25 */ %left     KWand     KWor
/* 35 */ %nonassoc EQ        NEQ       EQV     NEQV
                   LE        LT        GE      GT
                   KWin      NOTIN     KWas
/* 40 */ %left     BAR       DBAR
/* 45 */ %left     PLUS      MINUS
/* 50 */ %left     TIMES     DIVIDE
/* 55 */ %right    CARET     DCOLON
/* 60 */ %left     OPERATOR
/* 61 */ %right    ROPERATOR
/* 65 */ %nonassoc KWnot     KWold     QMARK
/* 66 */ %left     DOT
/* 80 */ %nonassoc LPAREN    LBRACKET  LBRACE
/* 90 */ %nonassoc UMINUS
/*100 */ %nonassoc HIGHEST_PREC        KWdeferred

%start file use_block_opt
%type <Support.module_declaration> file
%type <Support.use_block> use_block_opt




%%
/* ------------------------------------------------------------------------- */
/*  file structure  */
/* ------------------------------------------------------------------------- */

file:
  use_block optsemi decls {$1, List.rev $3}
| decls {[], List.rev $1 }

decls:
    { [] }
|   decls optsemi decl { $3::$1 }

decl:
    class_declaration { $1 }
|   named_feature     { $1 }
|   formal_generic    { $1 }
|   ass_feat          { $1 }
|   class_list        { $1 }
|   feature_list      { $1 }


use_block_opt:
    { [] }
| decl { [] }
| use_block { $1 }


use_block:
    KWuse module_list KWend { List.rev $2 }

module_list:
    one_module  { [$1] }
|   one_module separator module_list { $1 :: $3 }

one_module: dotted_id_list  {
  withinfo (rhs_info 1) (List.hd $1, List.tl $1)
}


/* ------------------------------------------------------------------------- */
/* Formal generics */
/* ------------------------------------------------------------------------- */

formal_generic:
  UIDENTIFIER COLON type_nt { Formal_generic (withinfo (rhs_info 1) $1,
                                              withinfo (rhs_info 3) $3) }



/* ------------------------------------------------------------------------- */
/*  assertions  */
/* ------------------------------------------------------------------------- */

ass_feat: proof_all_expr {
  let entlst, req, impl, ens = $1 in
  let bdy = req, Some impl, ens in
  Assertion_feature (None, entlst, bdy)
}

ass_req:
    KWrequire ass_seq { List.rev $2 }
|   KWrequire ass_seq SEMICOL { List.rev $2 }

ass_req_opt:
    { [] }
|   ass_req { $1 }

ass_proof: KWproof proof_seq separator { List.rev $2 }


ass_ens: KWensure ass_seq { List.rev $2 }

ass_seq:
    info_expr_1                         { [$1] }
|   ass_seq SEMICOL info_expr_1       { $3::$1 }


proof_seq:
    proof_expr { [$1] }
|   proof_seq SEMICOL proof_expr { $3::$1 }


proof_expr:
    info_expr_1 { $1 }
|   proof_inner { $1 }
|   proof_all_inner {
  let quant, entlst,req,impl,ens = $1 in
  let exp = Expquantified (quant,
                           entlst,
                           Expproof(req, Some impl, ens)) in
  withinfo (rhs_info 1) exp
}
|   proof_if { $1 }

|   proof_guarded_if { $1 }

|   proof_inspect { $1 }


proof_all_expr: KWall formal_arguments_opt opt_nl
                ass_req_opt
                ass_imp
                ass_ens KWend {
  let entlst = withinfo (rhs_info 2) $2 in
  entlst, $4, $5, $6
}


proof_all_inner:
    KWall formal_arguments opt_nl
       ass_req_opt
       ass_imp
       ass_ens
    KWend {
  let entlst = withinfo (rhs_info 2) $2 in
  Universal, entlst, $4, $5, $6
}
|   KWsome formal_arguments opt_nl
       ass_req_opt
       ass_imp
       ass_ens
    KWend {
  let entlst = withinfo (rhs_info 2) $2 in
  Existential, entlst, $4, $5, $6
}


proof_inner:
    ass_req ass_proof ass_ens KWend{
  let is_do = false in
  let impl  = Impdefined (None,is_do,$2) in
  let exp   = Expproof ($1, Some impl, $3) in
  withinfo (rhs_info 1) exp
}
|   ass_proof ass_ens KWend {
  let is_do = false in
  let impl  = Impdefined (None,is_do,$1) in
  let exp   = Expproof ([], Some impl, $2) in
  withinfo (rhs_info 1) exp
}
|   ass_req ass_ens KWend {
  let exp   = Expproof ($1, None, $2) in
  withinfo (rhs_info 1) exp
}


ass_imp:
    { Impdefined (None,false,[]) }
|   ass_proof           { Impdefined (None,false,$1) }
|   KWdeferred          { Impdeferred }
|   implementation_note {
  match $1 with
    Impbuiltin -> $1
  | _ ->
      error_info (rhs_info 1) "Not allowed in assertions"
}

proof_inspect:
    KWinspect expr_1 proof_inspect_rest KWend {
  let lst,ens = $3 in
  withinfo (rhs_info 1) (Proofinspect ($2,lst,ens))
}

proof_inspect_rest:
    optsemi KWensure info_expr { [], $3 }
|   KWcase info_expr KWproof proof_seq proof_inspect_rest {
  let lst,ens = $5 in
  ($2,List.rev $4)::lst, ens
   }


proof_if:
    KWif ass_then_part_list proof_if_rest KWend {
  let else_cmp, ens = $3 in
  withinfo (rhs_info 1) (Proofif ($2,else_cmp,ens)) }


ass_then_part_list:
    ass_then_part { [$1] }
|   ass_then_part KWelseif ass_then_part_list { $1::$3 }

ass_then_part:
    expr_1 { withinfo (rhs_info 1) $1, [] }
|   expr_1 KWproof proof_seq { withinfo (rhs_info 1) $1, List.rev $3 }


proof_if_rest:
    KWelse optsemi KWensure info_expr { withinfo (rhs_info 1) [], $4 }
|   KWelse KWproof proof_seq optsemi KWensure info_expr {
  withinfo (rhs_info 1) (List.rev $3), $6 }



proof_guarded_if:
    KWif ass_then_part
    proof_guarded_if_rest
    KWend {
  let ie,cmp = $2 in
  let lst,ens = $3 in
  withinfo (rhs_info 1) (Proofgif ((ie,cmp)::lst,ens))
}


proof_guarded_if_rest:
    KWorif info_expr_1 optsemi KWensure info_expr { [$2,[]], $5}
|   KWorif info_expr_1 KWproof proof_seq optsemi KWensure info_expr {
  [$2,List.rev $4], $7
}
|   KWorif info_expr_1 proof_guarded_if_rest {
  let lst,ens = $3 in
  ($2,[])::lst, ens
}
|   KWorif info_expr_1 KWproof proof_seq proof_guarded_if_rest {
  let lst,ens = $5 in
  ($2,List.rev $4)::lst,ens
}


/* ------------------------------------------------------------------------- */
/* Classes */
/* ------------------------------------------------------------------------- */



header_mark:
  { No_hmark }
| KWimmutable { Immutable_hmark }
| KWcase      { Case_hmark }
| KWdeferred  { Deferred_hmark  }




class_declaration:
  header_mark KWclass class_name class_generics
  create_clause
  inherit_clause
  KWend {
  Class_declaration( withinfo (rhs_info 3) $1,
                     withinfo (rhs_info 3) $3,
                     withinfo (rhs_info 4) $4,
                     $5,
                     $6)
}

class_name:
    UIDENTIFIER { [], $1 }
|   path UIDENTIFIER { $1, $2 }


class_generics:
    { [] }
|   LBRACKET uidentifier_list RBRACKET { $2 }


class_list0:
    class_declaration { [$1] }
|   class_declaration optsemi class_list0 { $1::$3 }

class_list: KWfeature class_list0 KWend { Class_list(withinfo (rhs_info 1) $2) }


/* ------------------------------------------------------------------------- */
/* Inheritance */
/* ------------------------------------------------------------------------- */

inherit_clause:
    { [] }
| KWinherit parent_list { $2 }

parent_list:
    parent { [$1] }
|   parent optsemi parent_list { $1::$3 }

parent: optghost type_nt feature_adaptation { $1, withinfo (rhs_info 2) $2, $3 }

feature_adaptation:
    { [] }
|   KWrename rename_list KWend { $2 }


rename_list:
    rename_item  { [$1] }
|   rename_item  optsemi rename_list { $1::$3 }

rename_item:
    name_sig KWas nameopconst  { $1,$3 }

name_sig:
    nameopconst { $1,[],None }
|   nameopconst LPAREN type_list RPAREN { $1,$3,None }
|   nameopconst LPAREN type_list RPAREN COLON type_nt { $1,$3, Some $6 }



/* ------------------------------------------------------------------------- */
/* Create clauses */
/* ------------------------------------------------------------------------- */

create_clause:
    { withinfo UNKNOWN [] }
| KWcreate constructor_list { withinfo (rhs_info 1) $2 }

constructor_list:
    constructor { [$1] }
|   constructor separator constructor_list { $1::$3 }


constructor: nameopconst_info formal_arguments_opt {
  $1, $2
   }


/* ------------------------------------------------------------------------- */
/* Types */
/* ------------------------------------------------------------------------- */



path: dotted_id_list DOT { $1 }


dotted_id_list:
    LIDENTIFIER  %prec LOWEST_PREC { [$1] }
|   dotted_id_list DOT LIDENTIFIER { $3::$1 }




type_nt:
    elem_type     %prec LOWEST_PREC { $1 }
|   arrow_type    { $1 }



elem_type:
    simple_type  { $1 }
|   tuple_type   { $1 }
|   qmark_type   { $1 }
|   star_type    { $1 }
|   list_type    { $1 }
|   LPAREN type_nt RPAREN { Paren_type $2 }



simple_type:
    UIDENTIFIER actual_generics {
  Normal_type ([],$1,$2)
}
|    path UIDENTIFIER actual_generics {  (* No parentheses needed? *)
  Normal_type ($1,$2,$3)
}


actual_generics:
    %prec LOWEST_PREC {[]}
|   LBRACKET type_list RBRACKET { $2 }




arrow_type: elem_type ARROW type_nt {
  Arrow_type ($1,$3)
}


qmark_type: elem_type QMARK   { QMark_type $1 }

star_type:  elem_type TIMES   { Star_type $1 }

list_type:  LBRACKET elem_type RBRACKET { List_type $2 }


tuple_type:  LPAREN type_list_min2  RPAREN { Tuple_type $2 }


type_list_min2:
  type_nt COMMA type_nt { [$1;$3] }
| type_nt COMMA type_list_min2 { $1::$3 }


type_list:
  type_nt { [$1]}
| type_list_min2 { $1 }






/* ------------------------------------------------------------------------- */
/* Features */
/* ------------------------------------------------------------------------- */

feature_list: KWfeature feature_list0 KWend {
  Feature_list (withinfo (rhs_info 1) $2)
}

feature_list0:
    named_feature { [$1] }
|   named_feature optsemi feature_list0 { $1 :: $3 }

named_feature:
    nameopconst_info
    formal_arguments_info
    return_type_opt
    optsemi
    feature_body_opt {
  let bdy,exp = body_exp $5 in
  Named_feature ($1, $2, $3, false, bdy, exp)
}
|   nameopconst_info
    return_type
    optsemi
    feature_body_opt {
  let bdy,exp = body_exp $4 in
  Named_feature ($1, noinfo [], Some $2, false, bdy, exp)
}
|   nameopconst_info
    formal_arguments_info
    return_type_opt
    ARROW
    info_expr {
  Named_feature ($1, $2, $3, true, None, Some $5)
}
|   nameopconst_info
    return_type
    EQ
    info_expr {
  Named_feature ($1, noinfo [], Some $2, false, None, Some $4)
}

nameopconst_info: nameopconst { withinfo (rhs_info 1) $1 }

nameopconst:
    LIDENTIFIER        { FNname $1 }
|   featopconst        { $1 }


featopconst:
    LPAREN operator RPAREN { FNoperator $2}
|   LBRACKET RBRACKET      { FNoperator Bracketop }
|   KWtrue                 { FNtrue }
|   KWfalse                { FNfalse }
|   NUMBER                 { FNnumber $1 }


return_type:
    COLON elem_type         { withinfo (rhs_info 2) ($2,false,false) }
|   COLON KWghost elem_type { withinfo (rhs_info 3) ($3,false,true)  }
|   EXCLAM COLON elem_type  { withinfo (rhs_info 3) ($3,true,false)  }


return_type_opt:
    { None }
|   return_type { Some $1 }


feature_body_opt:
    %prec LOWEST_PREC { None }
|   feature_body      { Some $1 }

feature_body:
    require_block feature_implementation ensure_block KWend
    { Body1($1, Some $2, $3) }
|   require_block feature_implementation KWend  { Body1($1, Some $2, []) }
|   feature_implementation ensure_block KWend   { Body1([], Some $1, $2) }
|   require_block ensure_block KWend            { Body1($1, None,    $2) }
|   require_block KWend                         { Body1($1, None,    []) }
|   feature_implementation KWend                { Body1([], Some $1, []) }
|   ensure_block KWend                          { Body1([], None,    $1) }
|   require_block KWensure ARROW info_expr KWend { Body2 ($1, $4) }
|   KWensure ARROW info_expr KWend { Body2 ([], $3) }



feature_implementation:
    KWdeferred           { Impdeferred }
|   implementation_note  { $1 }



require_block: ass_req { $1 }

require_block_opt: ass_req_opt { $1 }


ensure_block: ass_ens  { $1 }





implementation_note: KWnote LIDENTIFIER optsemi {
  let str = ST.string $2
  in
  if str = "built_in" || str = "axiom" then Impbuiltin
  else if str = "event" then Impevent
  else
    error_info (rhs_info 1) "must be one of {built_in,axiom,event}"
}




entity_list:
    entity_group { [$1] }
|   entity_group COMMA entity_list { $1::$3 }

entity_group:
    identifier_list { Untyped_entities $1 }
|   identifier_list COLON type_nt { Typed_entities ($1,$3) }


identifier_list:
    LIDENTIFIER %prec LOWEST_PREC { [$1] }
|   LIDENTIFIER COMMA identifier_list { $1::$3 }



formal_arguments_info: formal_arguments { withinfo (rhs_info 1) $1 }

formal_arguments_opt:
    { [] }
|   formal_arguments { $1 }

formal_arguments: LPAREN entity_list RPAREN { $2 }





/* ------------------------------------------------------------------------- */
/*  expressions  */
/* ------------------------------------------------------------------------- */

info_expr: expr %prec LOWEST_PREC { withinfo (rhs_info 1) $1 }

info_expr_1: expr_1 %prec LOWEST_PREC { withinfo (rhs_info 1) $1 }


expr:
    expr_1  %prec LOWEST_PREC { $1 }
|   expr_2  { $1 }

expr_1:
    atomic_expr                   { $1 }
|   operator_expr                 { $1 }
|   LPAREN expr RPAREN            { Expparen $2 }
|   LPAREN operator RPAREN        { Expop $2 }
|   LBRACKET RBRACKET             { Expop Bracketop}
|   LBRACKET expr RBRACKET        {
  let lst = expression_list $2 in
  let rec brexp lst =
    match lst with
      []   -> Expop Bracketop (*Identifier (ST.symbol "nil")*)
    | h::t ->
        Binexp (Caretop, h, brexp t)
  in
  brexp lst
}
|   expr_1 LPAREN expr RPAREN       { Funapp ($1,$3) }
|   expr_1 LBRACKET expr RBRACKET   { Bracketapp ($1,$3) }
|   expr_1 DOT LIDENTIFIER          { Expdot ($1, Identifier $3) }
|   expr_1 DOT LBRACE expr RBRACE   {
  Expdot($1, predicate_of_expression (rhs_info 4) $4)
}
|   dotted_id_list DOT LPAREN expr RPAREN   {
  Expdot (expression_from_dotted_id $1, $4) }

|   dotted_id_list DOT LBRACE expr RBRACE   {
  Expdot(expression_from_dotted_id $1, predicate_of_expression (rhs_info 4) $4)
}
|   expr_1 COLON type_nt        { Typedexp ($1, withinfo (rhs_info 3) $3) }

|   KWall  formal_arguments opt_nl expr {
  Expquantified (Universal, withinfo (rhs_info 2) $2, $4) }

|   KWsome formal_arguments opt_nl expr {
  Expquantified (Existential, withinfo (rhs_info 2) $2, $4) }

|   LBRACE expr RBRACE            {
  predicate_of_expression (rhs_info 2) $2
}
|   LPAREN expr RPAREN ARROW expr {
  let lst  = expression_list $2
  and info = rhs_info 2 in
  let entlst = entities_of_expression info lst in
  Exparrow (withinfo info entlst,$5)
}
|   KWagent formal_arguments_info return_type_opt optsemi
    require_block_opt
    KWensure ARROW expr
    KWend {
  Expagent ($2,$3,$5,$8)
}
|   LIDENTIFIER ARROW expr {
  let info = rhs_info 1 in
  let entlst = entities_of_expression info [Identifier $1] in
  Exparrow (withinfo info entlst, $3)
}


expr_2:
   exp_conditional { $1 }
|  exp_inspect     { $1 }
/*|  expr COMMA expr { Tupleexp ($1,$3) }*/


atomic_expr:
    KWResult                      { ExpResult }
|   NUMBER                        { Expnumber $1 }
|   KWfalse                       { Expfalse }
|   KWtrue                        { Exptrue }
|   USCORE                        { Expanon }
|   dotted_id_list %prec LOWEST_PREC {
  expression_from_dotted_id $1
}

operator_expr:
    expr_1 PLUS expr_1                { Binexp (Plusop,$1,$3) }

|   expr_1 MINUS expr_1               { Binexp (Minusop,$1,$3) }

|   PLUS expr_1                       { Unexp (Plusop,$2) }

|   MINUS expr_1                      { Unexp (Minusop,$2) }

|   expr_1 TIMES expr_1               { Binexp (Timesop,$1,$3) }

|   TIMES expr_1                      { Unexp (Timesop,$2) }

|   expr_1 DIVIDE expr_1              { Binexp (Divideop,$1,$3) }

|   expr_1 CARET  expr_1              { Binexp (Caretop,$1,$3) }

|   expr_1 KWin expr_1                { Binexp (Inop,$1,$3) }

|   expr_1 NOTIN expr_1               { Binexp (Notinop,$1,$3) }

|   expr_1 EQ  expr_1                 { Binexp (Eqop,$1,$3) }

|   expr_1 NEQ  expr_1                { Binexp (NEqop,$1,$3) }

|   expr_1 LT  expr_1                 { Binexp (LTop,$1,$3) }

|   expr_1 LE  expr_1                 { Binexp (LEop,$1,$3) }

|   expr_1 GT  expr_1                 { Binexp (GTop,$1,$3) }

|   expr_1 GE  expr_1                 { Binexp (GEop,$1,$3) }

|   expr_1 KWas expr_1                { Binexp (Asop,$1,$3) }

|   expr_1 KWand  expr_1              { Binexp (Andop,$1,$3) }

|   expr_1 KWor   expr_1              { Binexp (Orop,$1,$3)  }

|   expr_1 OPERATOR expr_1            { Binexp (Freeop $2,$1,$3) }

|   expr_1 ROPERATOR expr_1           { Binexp (RFreeop $2,$1,$3) }

|   KWnot   expr_1                    { Unexp (Notop,$2) }

|   KWold   expr_1                    { Unexp (Oldop,$2) }

|   expr_1 DCOLON expr_1              { Binexp (DColonop,$1,$3) }

|   expr_1 COLON expr_1               { Expcolon ($1,$3) }

|   expr_1 COMMA expr_1               { Tupleexp ($1,$3) }

|   expr_1 BAR  expr_1                { Binexp (Barop,$1,$3) }

|   expr_1 DBAR expr_1                { Binexp (DBarop,$1,$3) }

|   expr_1 DARROW expr_1              { Binexp (DArrowop,$1,$3) }






/* ------------------------------------------------------------------------- */
/*  operators  */
/* ------------------------------------------------------------------------- */



operator:
    PLUS      { Plusop }
|   MINUS     { Minusop }
|   TIMES     { Timesop }
|   DIVIDE    { Divideop }
|   EQ        { Eqop }
|   EQV       { Eqvop }
|   NEQ       { NEqop }
|   NEQV      { NEqvop }
|   LT        { LTop }
|   LE        { LEop }
|   GT        { GTop }
|   GE        { GEop }
|   CARET     { Caretop }
|   KWand     { Andop }
|   KWor      { Orop }
|   KWnot     { Notop }
|   KWin      { Inop  }
|   NOTIN     { Notinop }
|   BAR       { Barop }
|   DBAR      { DBarop }
|   DARROW    { DArrowop }
|   DCOLON    { DColonop }
|   OPERATOR  { Freeop $1 }
|   ROPERATOR { RFreeop $1 }



/* ------------------------------------------------------------------------- */
/*  general rules  */
/* ------------------------------------------------------------------------- */


optghost:
    { false }
| KWghost { true }

optsemi:
    %prec LOWEST_PREC {()}
|   SEMICOL {()}


uidentifier_list:
    UIDENTIFIER { [$1] }
|   UIDENTIFIER COMMA uidentifier_list { $1::$3 }


opt_nl:
    {()}
|   SEMICOL {()}
|   NEWLINE {()}

separator:
    SEMICOL  {()}
|   NEWLINE  {()}


/* ------------------------------------------------------------------------- */
/*  old grammar rules  */
/* ------------------------------------------------------------------------- */

/* ------------------------------------------------------------------------- */
/* Flow control */
/* ------------------------------------------------------------------------- */

exp_conditional:
    KWif exp_then_part_list exp_else_part KWend { Expif ($2,$3) }

exp_then_part_list:
    exp_then_part { [$1] }
|   exp_then_part KWelseif exp_then_part_list  { $1::$3 }

exp_then_part:
    expr_1 KWthen expr { $1, $3 }

exp_else_part:
    { None }
|   KWelse expr { Some $2 }


exp_inspect:
    KWinspect expr exp_case_list KWend {
  Expinspect ($2,$3)
    }

exp_case_list:
    exp_case { [$1] }
|   exp_case exp_case_list { $1 :: $2 }

exp_case: KWcase expr KWthen expr { $2, $4 }
