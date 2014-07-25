%{
open Support



(* The generated parser calls [parse_error "syntax error"] if it reaches an
   error state *)
let parse_error (_:string): unit =
  Parse_info.print_unexpected ()

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


let rec formals_from_expression (e:expression) =
  let rec entlist (l: expression list) =
    match l with
      [Typedexp ((Identifier id),t)] -> Typed_entities ([id],t)
    | [(Identifier id)] -> Untyped_entities [id]
    | (Identifier id)::t ->
        (let u = entlist t
        in
        match u with
          Untyped_entities l -> Untyped_entities (id::l)
        | Typed_entities (l,t) -> Typed_entities ((id::l),t)
        )
    | _ ->
        (match l with
          [] -> Printf.eprintf "entlist failure: empty expression list\n"
        | _::_ ->
            Printf.eprintf
              "entlist failure with %s\n"
              (string_of_expression (Explist l)));
        failwith "entlist"
  in
  match e with
  | Explist l  ->
      let ll = split_list
          l
          (fun el ->
            match el with
              Typedexp (_,_) -> true | _ -> false)
      in
      List.map entlist ll
  | _ -> [entlist [e]]


let formals_from_expression2 (e:expression)(i:info) =
  try
    formals_from_expression e
  with
    Failure _ ->
      Printf.eprintf "%s %s is not an argument list\n"
        (cinfo i)
        (string_of_expression e);
      syntax_error ()

(*
let expression_from_entities entlist =
  let egroup grp =
    match grp with
      Typed_entities (l,tp) ->
        let lr = List.rev l
        in
        (match lr with
          f::t ->
            let lrmapped =
              (Typedexp ((Identifier f),tp))
              :: (List.map (function id -> Identifier id) t)
            in
            List.rev lrmapped
        | _ -> assert false)
    | Untyped_entities l ->
        List.map (function id -> Identifier id) l
  in
  Explist (List.concat (List.map egroup entlist))
*)
%}

%token KWCURRENT KWCurrent
%token KWNONE
%token KWPrecursor KWProcess
%token KWResult

%token KWall       KWand          KWas
%token KWcase      KWclass        KWcheck      KWcreate
%token KWdeferred  KWdo
%token KWelse      KWelseif       KWend        KWensure
%token KWfalse     KWfeature
%token KWghost
%token KWif        KWimmutable    KWimport     KWin
       KWinherit   KWinspect      KWinvariant
%token KWlocal
%token KWnot       KWnote
%token KWold       KWor
%token KWredefine  KWrename       KWrequire
%token KWsome
%token KWthen      KWtrue
%token KWundefine  KWuse

%token ARROW
%token ASSIGN
%token BAR
%token BRACKETOP
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
%token PARENOP
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
/* 15 */ %left     COLON
/* 18 */ %right    COMMA
/* 20 */ %right    DARROW
/* 25 */ %left     KWand     KWor
/* 35 */ %left     EQ        NEQ       EQV     NEQV
                   LE        LT        GE      GT
/* 40 */ %left     BAR       DBAR
/* 45 */ %left     PLUS      MINUS
/* 50 */ %left     TIMES     DIVIDE
/* 55 */ %right    CARET     DCOLON
/* 60 */ %left     OPERATOR  KWin      NOTIN
/* 61 */ %right    ROPERATOR
/* 65 */ %nonassoc KWnot     KWold     QMARK
/* 66 */ %left     DOT
/* 80 */ %nonassoc LPAREN    LBRACKET  LBRACE
/* 90 */ %nonassoc UMINUS
/*100 */ %nonassoc HIGHEST_PREC        KWdeferred

%start file
%type <Support.module_declaration> file




%%
/* ------------------------------------------------------------------------- */
/*  file structure  */
/* ------------------------------------------------------------------------- */

file: use_block decls {$1, List.rev $2}

decls:
    { [] }
|   decls optsemi decl { $3::$1 }

decl:
    class_declaration { $1 }
|   named_feature     { $1 }
|   formal_generic    { $1 }
|   ass_feat          { $1 }


use_block:
  { [] }
| KWuse module_list KWend { List.rev $2 }

module_list:
    one_module  { [$1] }
|   one_module module_list { $1 :: $2 }

one_module: LIDENTIFIER  { withinfo (rhs_info 1) $1 }


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
  let bdy = Some req, Some impl, Some ens in
  Assertion_feature (None, entlst, bdy)
}

ass_req: KWrequire ass_seq { List.rev $2 }

ass_req_opt:
    { [] }
|   ass_req { $1 }

ass_check: KWcheck proof_seq { List.rev $2 }


ass_ens: KWensure ass_seq { List.rev $2 }

ass_seq:
    info_expr                           { [$1] }
|   ass_seq separator info_expr         { $3::$1 }

proof_seq:
    proof_expr { [$1] }
|   proof_seq separator proof_expr { $3::$1 }


proof_expr:
    info_expr { $1 }
|   proof_all_expr_inner {
  let entlst,req,impl,ens = $1 in
  let exp = Expquantified (Universal,
                           entlst,
                           Expproof(req, Some impl, ens)) in
  withinfo (rhs_info 1) exp
}
|   ass_req ass_check ass_ens KWend {
  let is_do = false in
  let impl  = Impdefined (None,is_do,$2) in
  let exp   = Expproof ($1, Some impl, $3) in
  withinfo (rhs_info 1) exp
}

proof_all_expr: KWall formal_arguments_opt opt_nl
                ass_req_opt
                ass_imp
                ass_ens KWend {
  let entlst = withinfo (rhs_info 2) $2 in
  entlst, $4, $5, $6
}


proof_all_expr_inner:
    KWall formal_arguments opt_nl
       ass_req_opt
       ass_imp
       ass_ens
    KWend {
  let entlst = withinfo (rhs_info 2) $2 in
  entlst, $4, $5, $6
}

ass_imp:
    { Impdefined (None,false,[]) }
|   ass_check           { Impdefined (None,false,$1) }
|   KWdeferred          { Impdeferred }
|   implementation_note {
  match $1 with
    Impbuiltin -> $1
  | _ ->
      Printf.eprintf "%s Not allowed in assertions\n" (cinfo (rhs_info 1));
      syntax_error ()
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
  header_mark KWclass UIDENTIFIER class_generics
  inheritance
  KWend {
  Class_declaration( withinfo (rhs_info 1) $1,
                     withinfo (rhs_info 3) $3,
                     withinfo (rhs_info 4) $4,
                     $5)
}


class_generics:
    { [] }
|   LBRACKET uidentifier_list RBRACKET { $2 }


inheritance:
    { [] }
|   inherit_clause inheritance { $1::$2 }



/* ------------------------------------------------------------------------- */
/* Inheritance */
/* ------------------------------------------------------------------------- */

inherit_clause: KWinherit optsemi parent_list { $3 }

parent_list:
    parent { [$1] }
|   parent parent_list { $1::$2 }

parent: type_nt feature_adaptation { withinfo (rhs_info 1) $1, $2 }

feature_adaptation:
    { [] }
|   adaptation_list KWend { $1 }

adaptation_list:
    adaptation_clause  { [$1] }
|   adaptation_clause adaptation_list { $1::$2 }

adaptation_clause:
    KWrename rename_list         { Rename $2   }
|   KWredefine feature_name_list { Redefine $2 }
|   KWundefine feature_name_list { Undefine $2 }

feature_name_list:
    name_sig   { [$1] }
|   name_sig  COMMA feature_name_list { $1::$3 }


rename_list:
    rename_item  { [$1] }
|   rename_item  COMMA rename_list { $1::$3 }

rename_item:
    name_sig KWas nameopconst  { $1,$3 }

name_sig:
    nameopconst { $1,[] }
|   nameopconst LPAREN type_list RPAREN { $1,$3 }





/* ------------------------------------------------------------------------- */
/* Types */
/* ------------------------------------------------------------------------- */



path: dotted_id_list DOT { $1 }


dotted_id_list:
    LIDENTIFIER  %prec LOWEST_PREC { [$1] }
|   dotted_id_list DOT LIDENTIFIER { $3::$1 }


type_nt:
  simple_type  { $1 }
| current_type { $1 }
| arrow_type   { $1 }
| tuple_type   { $1 }
| qmark_type   { $1 }
| LPAREN type_nt RPAREN { Paren_type $2 }


type_list_min2:
  type_nt COMMA type_nt { [$1;$3] }
| type_nt COMMA type_list_min2 { $1::$3 }


type_list:
  type_nt { [$1]}
| type_list_min2 { $1 }



actual_generics:
    %prec LOWEST_PREC {[]}
|   LBRACKET type_list RBRACKET { $2 }




simple_type:
    UIDENTIFIER actual_generics {
  Normal_type ([],$1,$2)
}
|   path UIDENTIFIER actual_generics {
  Normal_type (List.rev $1,$2,$3)
}



current_type: KWCURRENT actual_generics { Current_type $2 }


arrow_type: type_nt ARROW type_nt {
  Arrow_type ($1,$3)
}


tuple_type:  LPAREN type_list_min2  RPAREN { Tuple_type $2 }


qmark_type: type_nt QMARK   { QMark_type $1 }



/* ------------------------------------------------------------------------- */
/* Features */
/* ------------------------------------------------------------------------- */

named_feature:
    nameopconst formal_arguments return_type_opt optsemi feature_body_opt {
  Named_feature ((withinfo (rhs_info 1) $1),
                 (withinfo (rhs_info 2) $2),
                 $3,
                 $5)
}
|
    name_rtype optsemi feature_body_opt {
  let name,rt = $1
  in
  Named_feature (name,
                 (noinfo []),
                 rt,
                 $3)
}

name_rtype:
    LIDENTIFIER {
  (withinfo (rhs_info 1) (FNname $1)),
  None
}
|   LIDENTIFIER  COLON type_nt {
  (withinfo (rhs_info 1) (FNname $1)),
  (Some (withinfo (rhs_info 3) ($3,false,false)))
}
|   LIDENTIFIER  EXCLAM COLON type_nt {
  (withinfo (rhs_info 1) (FNname $1)),
  (Some (withinfo (rhs_info 4) ($4,true,false)))
}
|   featopconst return_type_opt {
  (withinfo (rhs_info 1) $1),
  $2
}


nameopconst:
    LIDENTIFIER        { FNname $1 }
|   featopconst        { $1 }


featopconst:
    operator           { FNoperator $1}
|   KWtrue             { FNtrue }
|   KWfalse            { FNfalse }
|   NUMBER             { FNnumber $1 }


return_type:
    COLON type_nt         { withinfo (rhs_info 2) ($2,false,false) }
|   COLON KWghost type_nt { withinfo (rhs_info 3) ($3,false,true)  }
|   EXCLAM COLON type_nt  { withinfo (rhs_info 3) ($3,true,false)  }


return_type_opt:
    { None }
|   return_type { Some $1 }


feature_body_opt:
    %prec LOWEST_PREC { None }
|   feature_body      { Some $1 }

feature_body:
    require_block feature_implementation ensure_block KWend
    { Some $1, Some $2, Some $3 }
|   require_block feature_implementation KWend  { Some $1, Some $2, None }
|   feature_implementation ensure_block KWend   { None   , Some $1, Some $2 }
|   require_block ensure_block KWend            { Some $1, None,    Some $2 }
|   require_block KWend                         { Some $1, None,    None }
|   feature_implementation KWend                { None,    Some $1, None }
|   ensure_block KWend                          { None,    None,    Some $1 }



feature_implementation:
    KWdeferred           { Impdeferred }
|   implementation_note  { $1 }
|   implementation_block { $1 }


implementation_block:
    local_block do_block    { Impdefined($1,true, $2) }
|   local_block check_block { Impdefined($1,false,$2) }


require_block:
    KWrequire compound { $2 }

check_block:
    KWcheck compound { $2 }

do_block: KWdo compound { $2 }


local_block:
    { None }
|   KWlocal local_list { Some $2 }

local_list:
    local_declaration { [$1] }
|   local_declaration SEMICOL local_list { $1::$3}


local_declaration:
    entity_list { Unassigned $1 }
|   entity_list ASSIGN expr { Assigned ($1,$3) }
|   LIDENTIFIER LPAREN entity_list RPAREN return_type_opt feature_body {
  Local_feature ($1,$3,$5,$6)
}




implementation_note: KWnote LIDENTIFIER {
  let str = ST.string $2
  in
  if str = "built_in" || str = "axiom" then Impbuiltin
  else if str = "event" then Impevent
  else
    (Printf.eprintf
       "%s Syntax error: must be one of {built_in,axiom,event}\n"
       (cinfo (rhs_info 1));
     syntax_error ())
}


ensure_block:
    KWensure compound { $2 }




entity_list:
    entity_group { [$1] }
|   entity_group COMMA entity_list { $1::$3 }

entity_group:
    identifier_list { Untyped_entities $1 }
|   identifier_list COLON type_nt { Typed_entities ($1,$3) }


identifier_list:
    LIDENTIFIER %prec LOWEST_PREC { [$1] }
|   LIDENTIFIER COMMA identifier_list { $1::$3 }



formal_arguments_opt:
    { [] }
|   formal_arguments { $1 }

formal_arguments: LPAREN entity_list RPAREN { $2 }



/* todo: distinguish between expressions which can occur within expressions
         only and expressions which can occur in imperative constructs to
         avoid the check ambiguity !!!
*/

compound: compound_list { $1 }


compound_list:
    info_expr  optsemi { [$1] }
|   info_expr SEMICOL compound_list { $1::$3 }






/* ------------------------------------------------------------------------- */
/*  expressions  */
/* ------------------------------------------------------------------------- */

info_expr: expr { withinfo (rhs_info 1) $1 }



expr:
    atomic_expr                   { $1 }
|   operator_expr                 { $1 }
|   LPAREN expr RPAREN            { Expparen $2 }
|   LPAREN operator RPAREN        { Expop $2 }
|   LBRACKET expr RBRACKET        { Expbracket $2 }
|   expr COMMA expr               { Tupleexp ($1,$3) }
|   expr LPAREN expr RPAREN       { Funapp ($1,$3) }
|   expr LBRACKET expr RBRACKET   { Bracketapp ($1,$3) }
|   expr DOT LIDENTIFIER          { Expdot ($1, Identifier $3) }
|   expr COLON type_nt            { Typedexp ($1,$3) }

|   KWall  formal_arguments opt_nl expr {
  Expquantified (Universal, withinfo (rhs_info 2) $2, $4) }

|   KWsome formal_arguments opt_nl expr {
  Expquantified (Existential, withinfo (rhs_info 2) $2, $4) }

|   LBRACE expr RBRACE            {
  match $2 with
    Expcolon (fargs,exp) ->
      let elist = formals_from_expression2 fargs (rhs_info 2)
      in
      Exppred (withinfo (rhs_info 2) elist, exp)
  | _ -> assert false
}



atomic_expr:
    KWResult                      { ExpResult }
|   NUMBER                        { Number $1 }
|   KWfalse                       { Expfalse }
|   KWtrue                        { Exptrue }
|   dotted_id_list %prec LOWEST_PREC {
  expression_from_dotted_id $1
}

operator_expr:
    expr PLUS expr                { Binexp (Plusop,$1,$3) }

|   expr MINUS expr               { Binexp (Minusop,$1,$3) }

|   MINUS expr                    { Unexp (Minusop,$2) }

|   expr TIMES expr               { Binexp (Timesop,$1,$3) }

|   expr DIVIDE expr              { Binexp (Divideop,$1,$3) }

|   expr CARET  expr              { Binexp (Caretop,$1,$3) }

|   expr KWin expr                { Binexp (Inop,$1,$3) }

|   expr NOTIN expr               { Binexp (Notinop,$1,$3) }

|   expr EQ  expr                 { Binexp (Eqop,$1,$3) }

|   expr LT  expr                 { Binexp (LTop,$1,$3) }

|   expr LE  expr                 { Binexp (LEop,$1,$3) }

|   expr GT  expr                 { Binexp (GTop,$1,$3) }

|   expr GE  expr                 { Binexp (GEop,$1,$3) }

|   expr KWand  expr              { Binexp (Andop,$1,$3) }

|   expr KWor   expr              { Binexp (Orop,$1,$3)  }

|   KWnot   expr                  { Unexp (Notop,$2) }

|   KWold   expr                  { Unexp (Oldop,$2) }

|   expr DCOLON expr              { Binexp (DColonop,$1,$3) }

|   expr COLON expr               { Expcolon ($1,$3) }

|   expr BAR  expr                { Binexp (Barop,$1,$3) }

|   expr DBAR expr                { Binexp (DBarop,$1,$3) }

|   expr DARROW expr              { Binexp (DArrowop,$1,$3) }






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
|   ARROW     { Arrowop }
|   DARROW    { DArrowop }
|   DCOLON    { DColonop }
|   OPERATOR  { Freeop $1 }
|   ROPERATOR { RFreeop $1 }
|   PARENOP   { Parenop }
|   BRACKETOP { Bracketop }



/* ------------------------------------------------------------------------- */
/*  general rules  */
/* ------------------------------------------------------------------------- */



optsemi:
    %prec LOWEST_PREC {()}
|   optsemi SEMICOL {()}


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

/*   UNUSED!!!
conditional:
    KWif then_part_list else_part KWend { Expif ($2,$3) }

then_part_list:
    then_part { [$1] }
|   then_part KWelseif then_part_list  { $1::$3 }

then_part:
    expr KWthen compound { withinfo (rhs_info 1) $1, $3 }

else_part:
    { None }
|   KWelse compound { Some $2 }



inspect:
    KWinspect info_expr case_list KWend { Expinspect ($2, $3) }

case_list:
    case_part { [$1] }
|   case_part case_list { $1::$2 }

case_part:  KWcase info_expr KWthen compound { $2,$4 }
*/







/* ------------------------------------------------------------------------- */
/* Expressions */
/* ------------------------------------------------------------------------- */

/*    UNUSED!!!
expression:
    pexpression %prec LOWEST_PREC  { $1 }
|   cexpression %prec LOWEST_PREC  { $1 }





pexpression: dotted_id_list %prec LOWEST_PREC {
  expression_from_dotted_id $1
}


cexpression:
    KWResult                       { ExpResult }

|   NUMBER                         { Number $1 }

|   KWCurrent                      { ExpCurrent }

|   KWfalse                        { Expfalse }

|   KWtrue                         { Exptrue }

|   LPAREN expression RPAREN       { Expparen $2 }

|   LPAREN operator RPAREN         { Expop $2 }

|   LBRACKET expression RBRACKET   { Expbracket $2 }

|   LBRACE expression RBRACE {
  match $2 with
    Expcolon(fargs,exp) ->
      let elist = formals_from_expression2 fargs (rhs_info 2)
      in
      let _ =
        Printf.printf "%s predicate {%s:%s}\n"
          (cinfo (rhs_info 1))
          (string_of_formals elist)
          (string_of_expression exp)
      in
      Exppred (elist, exp)
  | _ ->
      Expset $2
}


|   cexpression LBRACKET expression RBRACKET { Bracketapp ($1,$3) }


|   pexpression LBRACKET expression RBRACKET { 
  Bracketapp ($1,$3)
}


|   cexpression LPAREN expression RPAREN     { Funapp ($1,$3) }

|   pexpression LPAREN expression RPAREN     { Funapp ($1,$3) }


|   path LPAREN expression RPAREN  {
  let e = expression_from_dotted_id $1 in
  Expdot (e, Expparen $3)
}

|   cexpression DOT LIDENTIFIER { Expdot ($1, Identifier $3) }

|   cexpression DOT LPAREN expression RPAREN { Expdot ($1,Expparen $4) }

|   conditional { $1 }

|   inspect     { $1 }

|   require_block ensure_block KWend { Expproof ($1,None,$2) }

|   require_block implementation_block ensure_block KWend {
  Expproof ($1,Some $2, $3)
}

|   implementation_block ensure_block KWend {
  Expproof ([],Some $1, $2)
}

|   expression COMMA expression {
  match $3 with
    Explist l -> Explist ($1::l)
  | _ -> Explist [$1;$3]
}

|   quantifier LPAREN entity_list RPAREN optsemi expression %prec COLON {
  Expquantified ($1, withinfo (rhs_info 3) $3, $6) }

|   expression PLUS expression   { Binexp (Plusop,$1,$3) }

|   expression MINUS expression  { Binexp (Minusop,$1,$3) }

|   MINUS expression       { Unexp (Minusop,$2) }

|   expression TIMES expression  { Binexp (Timesop,$1,$3) }

|   expression DIVIDE expression { Binexp (Divideop,$1,$3) }

|   expression CARET  expression { Binexp (Caretop,$1,$3) }

|   expression KWin expression   { Binexp (Inop,$1,$3) }

|   expression NOTIN expression  { Binexp (Notinop,$1,$3) }

|   expression EQ  expression    { Binexp (Eqop,$1,$3) }

|   expression LT  expression    { Binexp (LTop,$1,$3) }

|   expression LE  expression    { Binexp (LEop,$1,$3) }

|   expression GT  expression    { Binexp (GTop,$1,$3) }

|   expression GE  expression    { Binexp (GEop,$1,$3) }

|   expression KWand  expression { Binexp (Andop,$1,$3) }

|   expression KWor   expression { Binexp (Orop,$1,$3)  }

|   KWnot   expression     { Unexp (Notop,$2) }

|   KWold   expression     { Unexp (Oldop,$2) }

|   expression DCOLON expression { Binexp (DColonop,$1,$3) }

|   expression COLON expression  { Expcolon ($1,$3) }

|   expression BAR  expression   { Binexp (Barop,$1,$3) }

|   expression DBAR expression   { Binexp (DBarop,$1,$3) }


|   arrow_exp expression
    %prec LOWEST_PREC {
  let l = formals_from_expression2 $1 (rhs_info 1) in
  Printf.printf "%s arrowexp: %s\n"
    (cinfo (rhs_info 1))
    (string_of_expression (Exparrow(l,$2)));
  Exparrow (l,$2)
}

|   arrow_exp type_nt
    %prec LOWEST_PREC   {
  match $1 with
    Typedexp (e,t) -> Typedexp (e, Arrow_type(t,$2))
  | _ ->
      Printf.eprintf "%s Unexpected type %s\n"
        (cinfo (rhs_info 2))
        (string_of_type $2);
      syntax_error ()
}

|   expression DARROW expression { Binexp (DArrowop,$1,$3) }

|   expression COLON type_nt     { Typedexp ($1,$3) }

|   expression ASSIGN expression { Expassign ($1,$3) }


arrow_exp: expression ARROW { $1 }




info_expression: tagged_expression {
  (*Printf.printf "%s exp: %s\n"
    (cinfo (rhs_info 1))
    (string_of_expression ~wp:false $1);*)
  withinfo (rhs_info 1) $1
}



tagged_expression:
    expression {
  match $1 with
    Expcolon (e1,e2) ->
      (match e1 with
        Identifier id ->
          Taggedexp (id,e2)
      | _ ->
          Printf.eprintf "%s %s is not a valid tag\n"
            (cinfo (rhs_info 1))
            (string_of_expression e1);
          syntax_error ()
      )
  | _ ->
      $1
}
*/
