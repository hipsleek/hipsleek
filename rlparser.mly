%{
  open Globals
  open VarGen
  module CP = Cpure
  
  let is_prmd id = 
    try
      let prmd = String.sub id ((String.length id) - 4) 4 in
      String.compare prmd "prmd" == 0
    with _ -> false
   
  let get_id id = 
    if is_prmd id then
      let id = String.sub id 0 (((String.length id) - 4)) in
      (id, Primed)
    else (id, Unprimed)
%}

%token <int> INT_LIT

%token <string> ID
%token TRUE FALSE
%token FORALL EXISTS
%token OPAREN CPAREN
%token COMMA ENDF
%token OR AND NOT IMPLY
%token GT GTE LT LTE EQ NEQ
%token PLUS MINUS STAR POW

%left IMPLY
%left OR
%left AND
%right NOT
%left GT GTE LT LTE EQ NEQ
%left PLUS MINUS
%left STAR

%start input
  %type <Cpure.formula> input

%%

input:
  | formula ENDF { $1 }
;

formula: 
  | bformula { CP.BForm ($1, None) }
  | formula OR formula { CP.mkOr $1 $3 None no_pos }
  | formula AND formula { CP.mkAnd $1 $3 no_pos }
  | NOT formula { CP.mkNot $2 None no_pos }
  | FORALL OPAREN ID COMMA formula CPAREN { 
      let id, prmd = get_id $3 in
      let sv = CP.SpecVar (Int, id, prmd) in
      CP.Forall (sv, $5, None, no_pos) 
    }
  | EXISTS OPAREN ID COMMA formula CPAREN {
      let id, prmd = get_id $3 in
      let sv = CP.SpecVar (Int, id, prmd) in
      CP.Exists (sv, $5, None, no_pos) 
    }
  | OPAREN formula CPAREN { $2 }
;

bformula: pformula { ($1, None) }

pformula:
    TRUE { CP.BConst (true, no_pos) }
  | FALSE { CP.BConst (false, no_pos) }
  | ID {
      let id, prmd = get_id $1 in 
      CP.mkBVar id prmd no_pos }
  | exp GT exp { CP.mkGt $1 $3 no_pos }
  | exp GTE exp { CP.mkGte $1 $3 no_pos }
  | exp LT exp { CP.mkLt $1 $3 no_pos }
  | exp LTE exp { CP.mkLte $1 $3 no_pos }
  | exp EQ exp { CP.mkEq $1 $3 no_pos }
  | exp NEQ exp { CP.mkNeq $1 $3 no_pos }
;

exp:
  | INT_LIT { CP.IConst ($1, no_pos) }
  | ID { 
      let id, prmd = get_id $1 in 
      CP.mkVar (CP.SpecVar (Int, id, prmd)) no_pos }
  | exp PLUS exp { CP.mkAdd $1 $3 no_pos}
  | exp MINUS exp { CP.mkSubtract $1 $3 no_pos }
  | exp STAR exp { CP.mkMult $1 $3 no_pos }
  | exp POW exp { CP.mkMult $1 $1 no_pos }
;

%%
