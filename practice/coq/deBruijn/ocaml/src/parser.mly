%{
  open Eval
  open Print
%}
%token <string> ID
%token LPAREN RPAREN
%token ABS DOT
%token SEMI

%start toplevel
%type <namelambda> toplevel
%%

toplevel:
  Expr SEMI { $1 }

Expr:
| ABS AbsExpr { $2 }
| AppExpr { $1 }

AbsExpr:
| x=ID l=AbsExpr { Abs0 (string_to_char_list x, l) }
| x=ID DOT e=Expr { Abs0 (string_to_char_list x, e) }

AppExpr:
| e1=AppExpr e2=AExpr { App0 (e1, e2) }
| AExpr { $1 }

AExpr:
| x=ID { Var0 (string_to_char_list x) }
| LPAREN e=Expr RPAREN { e }
