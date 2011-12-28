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
    [ x = formula -> typ := "node"; x ]
  ];

  formula:
  [ "formula" LEFTA
    [ "("; x = SELF; "&&"; y = SELF; ")" -> And (x, y, loc) 
    | x = pformula -> BForm ((x, None), None) ]			
  ];

  pformula:
  [ "pformula" LEFTA
    [ x = INT; "="; y = INT ->
      if int_of_string x = int_of_string y then BConst (true,loc) else BConst(false,loc)
    |	x = exp; "<"; y = exp -> Lt (x, y, loc) 
    | x = exp; ">"; y = exp -> Gt (x, y, loc) 
    | x = exp; "<="; y = exp ->
      if is_self_var x then Eq (Var(SpecVar(Named (!typ), self, Unprimed), loc), Null loc, loc)
      else
      if is_self_var y then Neq (Var(SpecVar(Named (!typ), self, Unprimed), loc), Null loc, loc)
      else Lte (x, y, loc)
    | x = exp; ">="; y = exp ->
      if is_self_var x then Neq (Var(SpecVar(Named (!typ), self, Unprimed), loc), Null loc, loc)
      else
      if is_self_var y then Eq (Var(SpecVar(Named (!typ), self, Unprimed), loc), Null loc, loc)
      else Gte (x, y, loc)
    | x = exp; "="; y = exp -> Eq (x, y, loc)
    | x = exp; "!="; y = exp -> Neq (x, y, loc)
    ]
  ]; 
      
  exp:
  [ "exp" LEFTA
    [ x = SELF; "+"; y = SELF -> Add(x, y, loc)
    | x = SELF; "-"; y = SELF -> Subtract(x, y, loc)
    | x = specvar -> Var (x, loc)
    | x = INT -> IConst (int_of_string x, loc) 
    ]
  ]; 
		
  specvar:
  [ "specvar" NONA
    [ x = LIDENT -> SpecVar (Int, x, Unprimed)]
  ]; 

END
	
let parse_fix s = Gram.parse_string expression (Loc.mk "<string>") s
