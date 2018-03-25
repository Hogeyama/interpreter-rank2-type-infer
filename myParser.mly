%{
  open Syntax
  (* ここに書いたものは，ExampleParser.mliに入らないので注意 *)

  let mkFun args0 e =
    let f arg e = EFun(arg, e)
    in List.fold_right f args0 e
%}

%token <int>    INT
%token <bool>   BOOL
%token <string> ID
%token LET IN
%token PLUS TIMES MINUS DIV
%token EQ LT
%token IF THEN ELSE
%token LPAR RPAR
%token FUN ARROW
%token REC MACRO
%token SEMISEMI

%start toplevel
%type <Syntax.command> toplevel
%%

toplevel:
  | expr SEMISEMI                          { CExp $1                      }
  | LET var args0 EQ expr SEMISEMI         { CDecl ($2, mkFun $3 $5)      }
  | LET REC var var args0 EQ expr SEMISEMI { CRecDecl ($3,$4,mkFun $5 $7) }
  ;

expr:
  | LET var args0 EQ expr IN expr         { ELet($2, mkFun $3 $5, $7)     }
  | LET MACRO var args0 EQ expr IN expr   { EMacro($3, mkFun $4 $6, $8)   }
  | LET REC var var args0 EQ expr IN expr { ELetRec($3,$4,mkFun $5 $7,$9) }
  | IF expr THEN expr ELSE expr           { EIf($2,$4,$6)                 }
  | FUN args1 ARROW expr                  { mkFun $2 $4                   }
  | arith_expr EQ arith_expr              { EEq($1,$3)                    }
  | arith_expr LT arith_expr              { ELt($1,$3)                    }
  | arith_expr                            { $1                            }
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
  | INT            { EConstInt($1) }
  | BOOL           { EConstBool($1) }
  | ID             { EVar($1) }
  | LPAR expr RPAR { $2 }
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

