%{

let parse_error str = !Support.parse_error_fun str

open Support

let filename ()    =  (symbol_start_pos ()).Lexing.pos_fname
let symbol_info () =  info_from_position (symbol_start_pos ())
let rhs_info i     =  info_from_position (rhs_start_pos i)

let cinfo (i:info) =  info_string (filename ()) i

let syntax_error () = raise (Parsing.Parse_error)

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




%}

%token KWCURRENT KWCurrent
%token KWNONE
%token KWPrecursor KWProcess
%token KWResult

%token KWall       KWand
%token KWcase      KWclass        KWcheck      KWcreate
%token KWdeferred  KWdo
%token KWelse      KWelseif       KWend        KWensure
%token KWfalse     KWfeature
%token KWghost
%token KWif        KWimmutable    KWin         KWinspect
       KWinvariant
%token KWlocal
%token KWnot       KWnote
%token KWor
%token KWrequire
%token KWsome
%token KWthen      KWtrue

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
%token <string> NUMBER


/*  0 */ %nonassoc LOWEST_PREC  KWghost
/*  5 */ %nonassoc ASSIGN
/* 10 */ %right    COMMA     SEMICOL
/* 15 */ %right    COLON
/* 20 */ %right    ARROW     DARROW
/* 25 */ %left     KWand     KWor
/* 35 */ %left     EQ        NEQ       EQV     NEQV
                   LE        LT        GE      GT
/* 40 */ %left     BAR       DBAR
/* 45 */ %left     PLUS      MINUS
/* 50 */ %left     TIMES     DIVIDE
/* 55 */ %right    CARET     DCOLON
/* 60 */ %left     OPERATOR  KWin      NOTIN
/* 61 */ %right    ROPERATOR
/* 65 */ %nonassoc KWnot     QMARK
/* 66 */ %left     DOT
/* 80 */ %nonassoc LPAREN    LBRACKET
/* 90 */ %nonassoc UMINUS
/*100 */ %nonassoc HIGHEST_PREC        KWdeferred

%start main
%type <Support.module_t> main

%%



main:module_nt { $1 }

module_nt:
    { empty_module }
|   module_nt optsemi declaration { $1 }
|   module_nt declaration_block KWend { $1 }


/* ------------------------------------------------------------------------- */
/* Declaration blocks */
/* ------------------------------------------------------------------------- */

declaration_block: block_type visibility optsemi declarations {()}

block_type:
    KWfeature   { () }
|   KWcreate    { () }
|   KWinvariant { () }


visibility:
    {()}
|   LBRACE KWNONE RBRACE {()}

declarations:
    %prec LOWEST_PREC {()}
|   declarations optsemi declaration {()}


declaration:
    class_declaration {()}
|   named_feature     {()}
|   assertion_feature {()}
|   formal_generic    {()}



/* ------------------------------------------------------------------------- */
/* Formal generics */
/* ------------------------------------------------------------------------- */

formal_generic:
  UIDENTIFIER COLON type_nt { withinfo (rhs_info 1) $1,
                              withinfo (rhs_info 3) $3 }



/* ------------------------------------------------------------------------- */
/* Classes and types */
/* ------------------------------------------------------------------------- */



header_mark:
  { No_hmark }
| KWimmutable { Immutable_hmark }
| KWcase      { Case_hmark }
| KWdeferred  { Deferred_hmark  }




class_declaration:
  header_mark KWclass UIDENTIFIER actual_generics
  class_blocks
  KWend {
  {hmark= withinfo (rhs_info 1) $1; cname=withinfo (rhs_info 3) $3}
}


class_blocks:
    {()}
|   class_blocks declaration_block {()}




path:
  { [] }
| LIDENTIFIER DOT path { $1::$3 }


type_nt:
  simple_type  { $1 }
| current_type { $1 }
| arrow_type   { $1 }
| ghost_type   { $1 }
| tuple_type   { $1 }
| qmark_type   { $1 }


type_list:
  type_nt { [$1]}
| type_nt COMMA type_list {
  $1::$3
}


actual_generics:
    %prec LOWEST_PREC {[]}
|   LBRACKET type_list RBRACKET { $2 }



simple_type:
    path UIDENTIFIER actual_generics { Normal_type ($1,$2,$3)}

current_type: KWCURRENT actual_generics { Current_type $2 }


arrow_type: type_nt ARROW type_nt {
  Arrow_type ($1,$3)
}


ghost_type: KWghost type_nt { Ghost_type $2 }


tuple_type: LBRACKET type_list RBRACKET { Tuple_type $2 }

qmark_type: type_nt QMARK   { QMark_type $1 }




/* ------------------------------------------------------------------------- */
/* Features */
/* ------------------------------------------------------------------------- */


assertion_feature:
    KWall formal_arguments optsemi feature_body {
  Printf.printf "Formal arguments: %s\n" (string_of_formals $2);
}

named_feature:
    nameopconst formal_arguments rettype optsemi feature_body_opt {
  Printf.printf "Formal arguments: %s\n" (string_of_formals $2)
}


nameopconst:
    operator {()}
|   KWtrue   {()}
|   KWfalse  {()}
|   NUMBER   {()}
|   LIDENTIFIER {()}
|   LIDENTIFIER EXCLAM {()}


rettype:
    {()}
|   COLON type_nt {()}

feature_body_opt:
    %prec LOWEST_PREC {()}
|   feature_body { $1 }

feature_body:
    require_list feature_implementation ensure_list KWend {()}
|   require_list feature_implementation KWend {()}
|   feature_implementation ensure_list KWend {()}
|   require_list ensure_list KWend {()}
|   require_list KWend {()}
|   feature_implementation KWend {()}
|   ensure_list KWend {()}



feature_implementation:
    KWdeferred {()}
|   implementation_note {()}
|   implementation_block {()}


implementation_block:
    local_block do_block    { Impdefined($1,true, $2) }
|   local_block check_block { Impdefined($1,false,$2) }


require_list:
    require_block {()}
|   require_block require_list {()}



ensure_list:
    ensure_block {()}
|   ensure_block ensure_list {()}



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
|   entity_list ASSIGN expression { Assigned ($1,$3) }
|   LIDENTIFIER LPAREN variable_list RPAREN feature_body {
  assert false}



implementation_note: note_block {
  let prerror () =
    (Printf.eprintf
       "%s Syntax error: only \"note built_in\" or \"note event\" possible here\n"
       (cinfo (rhs_info 1));
     syntax_error ())
  in
  match $1 with
    [e] ->
      (match e.v with
        Identifier id ->
          let str = symbol_string id in
          if str = "built_in"   then Impbuiltin
          else if str = "event" then Impevent
          else prerror ()
      | _ -> prerror ())
  | _ -> prerror ()
}


note_block:
    KWnote compound {
  let _ =
    Printf.printf "%s compound: %s\n"
      (cinfo (rhs_info 2))
      (string_of_compound $2)
  in
  $2
}

ensure_block:
    KWensure compound { $2 }







entity_list: variable_list { formals_from_expression (Explist $1) }

variable_list:
    variable { [$1] }
|   variable COMMA variable_list { $1::$3 }

variable:
    LIDENTIFIER  { Identifier $1 }
|   LIDENTIFIER COLON type_nt  { Typedexp ((Identifier $1), $3) }


formal_arguments:
    { [] }
|   LPAREN entity_list RPAREN { $2 }




/* ------------------------------------------------------------------------- */
/* Flow control */
/* ------------------------------------------------------------------------- */

conditional:
    KWif then_part_list else_part KWend { Expif ($2,$3) }

then_part_list:
    then_part { [$1] }
|   then_part KWelseif then_part_list  { $1::$3 }

then_part:
    expression KWthen compound { withinfo (rhs_info 1) $1, $3 }

else_part:
    { None }
|   KWelse compound { Some $2 }



inspect:
    KWinspect info_expression case_list KWend { Expinspect ($2, $3) }

case_list:
    case_part { [$1] }
|   case_part case_list { $1::$2 }

case_part:  KWcase info_expression KWthen compound { $2,$4 }






/* ------------------------------------------------------------------------- */
/* Expressions */
/* ------------------------------------------------------------------------- */

compound: compound_list {
  let _ =
    Printf.printf "%s compound: %s\n"
      (cinfo (rhs_info 1))
      (string_of_compound $1)
  in
  $1
}


compound_list:
    info_expression  optsemi { [$1] }
|   info_expression SEMICOL compound_list { $1::$3 }


info_expression: expression {
  Printf.printf "%s exp: %s\n"
    (cinfo (rhs_info 1))
    (string_of_expression ~wp:false $1);
  withinfo (rhs_info 1) $1
}

expression:
    uexp %prec COMMA { $1 }

|   uexp COLON expression { Taggedexp ($1,$3) }

|   expression COMMA expression {
  match $3 with
    Explist l -> Explist ($1::l)
  | _ -> Explist [$1;$3]
}

|   quantifier LPAREN entity_list RPAREN optsemi expression %prec COLON {
  Expquantified ($1,$3,$6) }


quantifier:
    KWall  { Universal   }
|   KWsome { Existential }



uexp:
    atomic_expression           { $1 }

|   uexp PLUS uexp   { Binexp (Plusop,$1,$3) }

|   uexp MINUS uexp  { Binexp (Minusop,$1,$3) }

|   MINUS uexp       { Unexp (Minusop,$2) }

|   uexp TIMES uexp  { Binexp (Timesop,$1,$3) }

|   uexp DIVIDE uexp { Binexp (Divideop,$1,$3) }

|   uexp CARET  uexp { Binexp (Caretop,$1,$3) }

|   uexp KWin uexp   { Binexp (Inop,$1,$3) }

|   uexp NOTIN uexp  { Binexp (Notinop,$1,$3) }

|   uexp EQ  uexp    { Binexp (Eqop,$1,$3) }

|   uexp LT  uexp    { Binexp (LTop,$1,$3) }

|   uexp LE  uexp    { Binexp (LEop,$1,$3) }

|   uexp GT  uexp    { Binexp (GTop,$1,$3) }

|   uexp GE  uexp    { Binexp (GEop,$1,$3) }

|   uexp KWand  uexp { Binexp (Andop,$1,$3) }

|   uexp KWor   uexp { Binexp (Orop,$1,$3)  }

|   KWnot   uexp     { Unexp (Notop,$2) }

|   uexp DCOLON uexp { Binexp (DColonop,$1,$3) }

|   uexp BAR  uexp   { Binexp (Barop,$1,$3) }

|   uexp DBAR uexp   { Binexp (DBarop,$1,$3) }

|   uexp ARROW  uexp { Binexp (Arrowop,$1,$3) }

|   uexp DARROW uexp { Binexp (DArrowop,$1,$3) }

|   uexp COLON type_nt     { Typedexp ($1,$3) }

|   uexp ASSIGN uexp { Expassign ($1,$3) }




atomic_expression:
    LIDENTIFIER  %prec LOWEST_PREC { Identifier $1 }

|   KWResult                       { ExpResult }

|   NUMBER                         { Number $1 }

|   KWCurrent                      { ExpCurrent }

|   KWfalse                        { Expfalse }

|   KWtrue                         { Exptrue }

|   LPAREN expression RPAREN       { Expparen $2 }

|   LPAREN operator RPAREN         { Expop $2 }

|   LBRACKET expression RBRACKET   { Expbracket $2 }

|   LBRACE  expression RBRACE      { Expset $2 }

|   atomic_expression LPAREN expression RPAREN     { Funapp ($1,$3) }

|   atomic_expression LBRACKET expression RBRACKET { Bracketapp ($1,$3) }

|   atomic_expression DOT atomic_expression {
  Printf.printf "%s.%s encountered\n"
    (string_of_expression $1) (string_of_expression $3);
  Expdot ($1,$3)
}

|   conditional { $1 }

|   inspect     { $1 }

|   require_block ensure_block KWend { Expproof ($1,None,$2) }

|   require_block implementation_block ensure_block KWend {
  Expproof ($1,Some $2, $3)
}



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
|   LBRACKET RBRACKET {Bracketop}



/* ------------------------------------------------------------------------- */
/*  General rules  */
/* ------------------------------------------------------------------------- */



optsemi:
    %prec LOWEST_PREC {()}
|   optsemi SEMICOL {()}
