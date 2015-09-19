%{
  open Globals
  open Z3m
%}

%token <int> INT_LIT
%token <float> FLOAT_LIT
%token <string> ID
%token OPAREN CPAREN
%token MODEL DEFFUN INT REAL TOINT MINUS MULT DIV EOF
%token SAT UNSAT UNK
%token COLON QUOTATION

%start output
  %type <Z3m.z3m_res> output
  /* %type <(string * Z3m.z3m_val) list> output */

%start output_unsat_core
  %type <Z3m.z3m_res> output_unsat_core
%%

output:
    sat_unk model { Z3m.Sat_or_Unk $2 }
  | UNSAT z3_message { Z3m.Unsat [] }
  ;

output_unsat_core:
    sat_unk z3_message { Z3m.Sat_or_Unk [] }
  | UNSAT unsat_core { Z3m.Unsat $2 }

z3_message:
    {}
  | OPAREN discardable_tokens CPAREN {}

discardable_tokens:
    discardable_tokens discardable_token {}
  | discardable_token {}
  ;

discardable_token:
    MODEL {}
  | ID {}
  | INT_LIT {}
  | COLON {}
  | QUOTATION {}
  | SAT {}
  | UNSAT {}
  | UNK {}
  ;

sat_unk:
    SAT {}
  | UNK {}
  ;

/*
output: model { $1 }
  ;
*/

model:
    OPAREN MODEL sol_list CPAREN { $3 }
  ;

sol_list:
    sol { [$1] }
	| sol_list sol { $1 @ [$2] }
  ;

sol:
    OPAREN DEFFUN ID OPAREN CPAREN z3m_typ z3m_val CPAREN { ($3, $7) }
  ;

unsat_core:
    OPAREN id_list CPAREN { $2 }

id_list:
    ID { [$1] }
  | id_list ID { $1 @ [$2] }

z3m_typ:
    INT {}
  | REAL {}
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

int_val: INT_LIT { Int $1 }
  ;

frac_val: 
    DIV FLOAT_LIT FLOAT_LIT { Frac ($2, $3) }
  | FLOAT_LIT { Frac ($1, 1.0) }
  ;

%%

