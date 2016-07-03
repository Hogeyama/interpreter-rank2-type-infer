%{  open Syntax  (* ここに書いたものは，ExampleParser.mliに入らないので注意 *)
  let mkFun args0 e =
    let f arg e = EFun(arg, e)
    in List.fold_right f args0 e
  let parse_strliteral s =
    let r = Str.regexp "^\"\\(.*\\)\"$" in
    Str.replace_first r "\\1" s;;
  let tyvar_of_string s = TV(Right s)
  let tyvars_of_strings = List.map tyvar_of_string
%}

%token <int>    INT
%token <bool>   BOOL
%token <string> ID
%token <string> STRING
%token LET IN AND
%token PLUS TIMES MINUS DIV
%token EQ LT
%token IF THEN ELSE
%token LPAR RPAR
%token FUN ARROW
%token INTTY BOOLTY FORALL
%token REC
%token LBRACKET RBRACKET CONS COMMA
%token MATCH WITH BAR
%token SEMISEMI SHARP COLON DOT

%start toplevel
%type <Syntax.command> toplevel
%%

toplevel:
  | expr SEMISEMI     { CExp $1    }
  | declare SEMISEMI  { CDecl $1   }
  | SHARP var STRING SEMISEMI { CDirect ($2,[parse_strliteral $3]) }
;

declare: /* : declare */
  | LET     let_declare             { [Decl $2]        }
  | LET REC let_rec_declare         { [RecDecl $3]     }
  | LET     let_declare     declare { (Decl $2)::$3    }
  | LET REC let_rec_declare declare { (RecDecl $3)::$4 }
;

let_declare: /* : (name * expr) list */
  | var args0 EQ expr                 { [($1, mkFun $2 $4)]   }
  | var args0 EQ expr AND let_declare { ($1, mkFun $2 $4)::$6 }
;

let_rec_declare: /* : (name * name * expr) list */
  | var var args0 EQ expr                     { [($1, $2, mkFun $3 $5)]   }
  | var var args0 EQ expr AND let_rec_declare { ($1, $2, mkFun $3 $5)::$7 }
;

expr:
  | LET var COLON type_schema EQ expr IN expr { ELetTy([$2,$4,$6],$8) }
  | LET let_declare IN expr         { ELet($2, $4)    }
  | LET REC let_rec_declare IN expr { ELetRec($3, $5) }
  | IF expr THEN expr ELSE expr     { EIf($2,$4,$6)   }
  | FUN args1 ARROW expr            { mkFun $2 $4     }
  | arith_expr EQ arith_expr        { EEq($1,$3)      }
  | arith_expr LT arith_expr        { ELt($1,$3)      }
  | MATCH expr WITH cases           { EMatch($2, $4)  }
  | MATCH expr WITH BAR cases       { EMatch($2, $5)  }
  | list_expr                       { $1              }
;

cases:
  | pattern ARROW expr           { [($1, $3)] }
  | pattern ARROW expr BAR cases { ($1, $3) :: $5 }
;

pattern:
  | atomic_pattern CONS pattern      { PCons($1,$3) }
  | atomic_pattern                   { $1 }
;

atomic_pattern:
  | INT                              { PInt($1) }
  | BOOL                             { PBool($1) }
  | var                              { PVar($1) }
  | LPAR pattern COMMA pattern RPAR  { PPair($2, $4) }
  | LBRACKET RBRACKET                { PNil }
  | LPAR pattern RPAR                { $2 }
;

list_expr:
  | arith_expr CONS list_expr { ECons($1, $3) }
  | arith_expr                { $1 }
;

arith_expr:
  | arith_expr PLUS factor_expr  { EAdd($1,$3) }
  | arith_expr MINUS factor_expr { ESub($1,$3) }
  | factor_expr                  { $1 }
;

factor_expr:
  | factor_expr TIMES app_expr { EMul($1,$3) }
  | factor_expr DIV app_expr   { EDiv($1,$3) }
  | app_expr                   { $1 }
;

app_expr:
  | app_expr atomic_expr { EApp($1, $2) }
  | atomic_expr          { $1 }

atomic_expr:
  | INT               { EConstInt($1) }
  | BOOL              { EConstBool($1) }
  | LPAR expr COMMA expr RPAR { EPair($2, $4) }
  | LBRACKET RBRACKET { ENil }
  | ID                { EVar($1) }
  | LPAR expr RPAR    { $2 }
;

var:
  | ID { $1 }
;

args0:
  |       { [] }
  | args1 { $1 }
;

args1:
  | var args0 { $1::$2 }
;

type_schema:
  | type_schema_sub { $1 }
  | LPAR type_schema_sub RPAR ARROW type_schema { TsArrow ($2, $5)}

type_schema_sub:
  | ty { TsLift $1 }
  | FORALL args1 DOT type_schema_sub      { TsForall (tyvars_of_strings $2, $4) }
;

ty:
  | ty_sub { $1 }
  | ty_sub ARROW ty { TyArrow($1,$3) }
;
ty_sub:
  | INTTY        { TyInt                      }
  | BOOLTY       { TyBool                     }
  | LPAR ty RPAR { $2                         }
  | var          { TyVar (tyvar_of_string $1) }
;
