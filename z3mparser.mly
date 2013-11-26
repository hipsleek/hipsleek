%{
  open Globals
%}

%token <int> INT_LIT
%token <string> ID
%token OPAREN CPAREN
%token MODEL DEFFUN INT MINUS EOF

%start input
  %type <(string * int) list> input
%%

input:
  OPAREN MODEL sol_list CPAREN { $3 }
;

sol_list:
    sol { [$1] }
	| sol sol_list { [$1] @ $2 }
;

sol:
    OPAREN DEFFUN ID OPAREN CPAREN INT int_val CPAREN { ($3, $7) }
;

int_val:
		INT_LIT { $1 }
	|	OPAREN MINUS INT_LIT CPAREN { -$3 }

%%

