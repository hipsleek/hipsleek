%{
  open Globals
%}

%token <int> INT_LIT
%token <float> FLOAT_LIT
%token <string> ID
%token OPAREN CPAREN
%token MODEL DEFFUN INT TOINT MINUS MULT DIV EOF

%start input
  %type <(string * Globals.z3m_val) list> input
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
    int_val { Z3_Int $1 }
  | TOINT OPAREN DIV float_val float_val CPAREN { Z3_Frac ($4, $5) }
  | MULT z3m_val z3m_val { z3m_val_mult $2 $3 }
  | OPAREN z3m_val CPAREN { $2 }

int_val:
    INT_LIT { $1 }
  | MINUS INT_LIT { -$2 }
;

float_val:
    FLOAT_LIT { $1 }
  | MINUS FLOAT_LIT { -.$2 }
;

%%

