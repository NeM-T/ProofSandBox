%{
  open Eval
  open Print
%}


%token LPAREN RPAREN SEMI DOT
%token ABS 
%token <string> ID

%start toplevel
%type <Eval.namelambda> toplevel
%%

toplevel :
  e=Expr SEMI {e}

Expr :
  t1=Expr t2=Expr  {App0 (t1, t2)}
  | e=AExpr {e}

AExpr :
  ABS x=ID DOT e=Expr {Abs0 ((string_to_char_list x), e)}
  | e=VExpr {e}

VExpr :
  x = ID  {Var0 (string_to_char_list x)}
  | LPAREN e=Expr RPAREN {e}
