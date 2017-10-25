%{
open Array_pred
 
%}
%token EOL
%token EOF
%token IMPLY
%token EXIST
%token DOT
%token RPAREN LPAREN
%token COMMA
%token STAR
%token AND
%token VBAR
%token <string>VAR
%token <int>CONST
%token ADD
%token MINUS

%token POINTTO
%token ARRAY

%token RESULT
%token VALID
%token INVALID


%token EQUAL
%token NEQ
%token GT
%token GTE
%token LT
%token LTE

%start main
%type < (string * Array_pred.entailment) > main
%%

main:
    result entailment EOF { ($1, $2) }
;

result:
    VALID { "Valid" }
    | INVALID { "Fail" }
;    

entailment:
    formula IMPLY formula_list { ($1, $3) }
;

pair:
    LPAREN exp COMMA exp RPAREN { ($2, $4) }
;

exp:
    VAR { Var $1 }
    | CONST { Const $1 }
    | exp ADD exp { match $1, $3 with
                    | Const num, _ when num = 0 ->
		      $3
		    | _, Const num when num = 0 -> $1
		    | _, _ ->
                      Add ($1, $3) }
    | exp MINUS exp { match $1, $3 with
		    | _, Const 0 -> $1
		    | _, _ ->
                      Minus ($1, $3) }
;

arr_term:
    exp POINTTO pair { let (a, b) = $3 in Arrf (Pto ($1, a, b)) }
    | ARRAY pair { let (a, b) = $2 in Arrf (Aseg (a, b))}
;


pure_term:
    exp LT exp { Puref (Lt ($1, $3))}
    | exp LTE exp { Puref (Lte ($1, $3))}
    | exp GT exp { Puref (Gt ($1, $3))}
    | exp GTE exp { Puref (Gte ($1, $3))}
    | exp EQUAL exp { Puref (Eq ($1, $3))}
    | exp NEQ exp { Puref (Neq ($1, $3))}		
;

term_list:
    arr_term { [$1] }
    | pure_term { [$1] }
    | arr_term  STAR term_list { $1 :: $3 }
    | pure_term AND term_list { $1 :: $3 }
; 

formula:
    term_list { let (plst, hlst) = List.partition (function Puref _ -> true | _ -> false) $1 in And ([], plst, hlst)}
    | exists term_list { let (plst, hlst) = List.partition (function Puref _ -> true | _ -> false) $2 in (And ($1, plst, hlst)) }
;

formula_list:
    formula { [$1] }
    | formula VBAR formula_list { $1 :: $3 }
;    

var_list:
    VAR { [$1] }
    | VAR COMMA var_list { $1 :: $3 }
;

exists:
    EXIST var_list DOT { $2 }
;