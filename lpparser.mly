%{
  open Globals
%}

%token <int> INT_LIT
%token <string> ID
%token OPTIMAL OVAL MINUS EOF

%start input
  %type <(string * int) list> input
%%

input:
  OPTIMAL OVAL int_val sol_list { $4 }
;

sol_list:
    sol { [$1] }
	| sol sol_list { [$1] @ $2 }
  ;

sol:
  INT_LIT ID int_val int_val { ($2, $3) } 
;

int_val: 
    INT_LIT { $1 }
  | MINUS INT_LIT { -$2 }
;


%%

