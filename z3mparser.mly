%{
  open Globals
  open Z3m
%}

%token <int> INT_LIT
%token <float> FLOAT_LIT
%token <string> ID
%token OPAREN CPAREN
%token MODEL DEFFUN INT TOINT MINUS MULT DIV EOF

%start input
  %type <(string * Z3m.z3m_val) list> input
%%

input:
  OPAREN MODEL sol_list CPAREN { $3 }
;

sol_list:
    sol { [$1] }
	| sol sol_list { [$1] @ $2 }
  ;

sol:
    OPAREN DEFFUN ID OPAREN CPAREN INT z3m_val CPAREN { ($3, $7) }
;

z3m_val:
    prim_val { $1 }
  | TOINT prim_val { $2 }
  | MULT z3m_val z3m_val { z3m_val_mult $2 $3 }
  | OPAREN z3m_val CPAREN { $2 }
  ;

prim_val:
    int_val { $1 }
  | frac_val { $1 } 
  | OPAREN prim_val CPAREN { $2 }
  | MINUS prim_val { z3m_val_neg $2 }
  ;

int_val: INT_LIT { Z3_Int $1 }
;

frac_val: DIV FLOAT_LIT FLOAT_LIT { Z3_Frac ($2, $3) }
;

%%

