%{
 module Eqs = Shares_z3_lib.Eqs
%}

%token <string> IDENTIFIER
%token EOF 
%token EQ 
%token COMMA
%token STAR
%token OPAREN
%token CPAREN
%token HASH
%token DOT
%token SAT
%token IMPL

%start eq_systs
%type <Shares_z3_lib.cmd> eq_systs

%%
eq_systs: 
	SAT eq_syst {Shares_z3_lib.Sat $2}
	| IMPL eq_syst eq_syst {Shares_z3_lib.Imply ($2,$3)};
	
eq_syst: var_list var_list pv_list vc_list eq_list {Eqs.mkEqS $1 $2 $3 $4 $5};	

var : IDENTIFIER {Eqs.mkVar $1};

pv : IDENTIFIER EQ IDENTIFIER {Eqs.mkVar $1,Eqs.mkVar $3};

vec : IDENTIFIER EQ shc {Eqs.mkVar $1,$3};

pv_list : DOT {[]}
	| pv DOT {[$1]}
	| pv COMMA pv_list {$1::$3};
	
vc_list : DOT {[]}
	| vec DOT {[$1]}
	| vec COMMA vc_list {$1::$3};
	
var_list:
	DOT {[]}
	| var DOT {[$1]}
	| var COMMA var_list {$1::$3};
	
eq_list:
	| DOT {[]}
	| eq DOT {[$1]}
	| eq COMMA eq_list {$1::$3};   
	
eq: vc vc vc {Eqs.mkEq $1 $2 $3};

vc: shc {Eqs.mkpcCnst $1} 
	| var {Eqs.mkpcVar $1};
			
shc:
   HASH {Eqs.mkcFull}
   | OPAREN shc COMMA CPAREN {Eqs.mkcNode $2 Eqs.mkcEmpty}
   | OPAREN COMMA shc CPAREN {Eqs.mkcNode Eqs.mkcEmpty $3}
   | OPAREN shc COMMA shc CPAREN {Eqs.mkcNode $2 $4};
%%
