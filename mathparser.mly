%{
  open Globals
%}

%token <int> INT_LIT
%token <string> ID
%token OBRACE CBRACE OSQUARE CSQUARE
%token ARROW EQ MINUS COMMA EOF

%start input
  %type <(string * int) list> input
%%

input:
		ID OSQUARE INT_LIT CSQUARE EQ instances EOF { $6 }
;

instances:
		OBRACE CBRACE { [] }
	| OBRACE OBRACE sol_list CBRACE CBRACE { $3 }
;

sol_list:
    sol { [$1] }
	| sol COMMA sol_list { [$1] @ $3 }
;

sol:
    ID ARROW int_val { ($1, $3) }
;

int_val:
		INT_LIT { $1 }
	|	MINUS INT_LIT { -$2 }

%%

