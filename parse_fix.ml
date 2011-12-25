open Camlp4.PreCast
open Cpure
open Globals
open Lexing

let loc = no_pos;;

let typ = ref "";;

let expression = Gram.Entry.mk "expression";;

let formula = Gram.Entry.mk "formula";;

let pformula = Gram.Entry.mk "pformula";;

let exp = Gram.Entry.mk "exp";;

let specvar = Gram.Entry.mk "specvar";;

EXTEND Gram
GLOBAL: expression formula pformula exp specvar;
  expression:
  [ "expression" NONA
    [ OPT "("; x = formula; OPT ")" -> typ := "node"; x ]
  ];

  formula:
  [ "formula" LEFTA
    [ x = SELF; "&&"; y = SELF -> And (x, y, loc) 
    | x = pformula -> BForm ((x, None), None) ]			
  ];

  pformula:
  [ "pformula" LEFTA
    [ "self"; "<="; INT -> Eq (Var(SpecVar(Named (!typ), self, Unprimed), loc), Null loc, loc)
    | "self"; ">="; INT -> Neq (Var(SpecVar(Named (!typ), self, Unprimed), loc), Null loc, loc)
    | INT; ">="; "self" -> Eq (Var(SpecVar(Named (!typ), self, Unprimed), loc), Null loc, loc)
    | INT; "<="; "self" -> Neq (Var(SpecVar(Named (!typ), self, Unprimed), loc), Null loc, loc)
    |	x = exp; "<"; y = exp -> Gt (y, x, loc) 
    | x = exp; "<="; y = exp -> Gte (y, x, loc) 
    | x = exp; ">"; y = exp -> Lt (y, x, loc) 
    | x = exp; ">="; y = exp -> Lte (y, x, loc) 
    | x = exp; "="; y = exp -> Eq (x, y, loc) 
    ]
  ]; 
      
  exp:
  [ "exp" LEFTA
    [ x = specvar -> Var (x, loc) 
    | x = INT -> IConst (int_of_string x, loc) 
    ]
  ]; 
		
  specvar:
  [ "specvar" NONA
    [ x = LIDENT -> SpecVar (Int, x, Unprimed)]
  ]; 

END
	
let parse_fix s = Gram.parse_string expression (Loc.mk "<string>") s
