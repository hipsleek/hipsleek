open Camlp4.PreCast
open Cpure
open Globals
open Lexing
open Gen

module H = Hashtbl
module AS = Astsimp

let loc = no_pos;;

let stab = ref (H.create 103)

let expression = Gram.Entry.mk "expression";;

let or_formula = Gram.Entry.mk "or_formula";;

let formula = Gram.Entry.mk "formula";;

let pformula = Gram.Entry.mk "pformula";;

let exp = Gram.Entry.mk "exp";;

let specvar = Gram.Entry.mk "specvar";;

let get_var var stab = if is_substr "PRI" var 
  then AS.get_spec_var_ident stab (String.sub var 3 (String.length var - 3)) Primed
  else AS.get_spec_var_ident stab var Unprimed

let change_name var name = match var with
  | SpecVar (t,id,p) -> SpecVar (t,name ^ id,p)

let is_node var = match var with 
  | Var (SpecVar (_,id,_), _) -> is_substr "NOD" id
  | _ -> false

let get_node var = match var with 
  | Var (SpecVar (_,id,_), _) -> String.sub id 3 (String.length id - 3)
  | _ -> report_error no_pos "Expecting node var"

let is_rec_node var = match var with 
  | Var (SpecVar (_,id,_), _) -> is_substr "RECNOD" id
  | _ -> false

let get_rec_node var = match var with 
  | Var (SpecVar (_,id,_), _) -> String.sub id 6 (String.length id - 6)
  | _ -> report_error no_pos "Expecting rec node var"

let is_int c = '0' <= c && c <= '9'

EXTEND Gram
GLOBAL: expression or_formula formula pformula exp specvar;
  expression:
  [ "expression" NONA
    [ x = LIST1 or_formula -> x ]
  ];

  or_formula:
  [ "or_formula" LEFTA
    [ x = SELF; "||"; y = SELF -> mkOr x y None loc
    | x = formula -> x ]
  ];

  formula:
  [ "formula" LEFTA
    [ x = SELF; "&&"; y = SELF -> mkAnd x y loc
    | x = pformula -> x (*BForm ((x, None), None)*) ]
  ];

  pformula:
  [ "pformula" LEFTA
    [ _ = NATIVEINT; "="; _ = exp -> mkTrue loc
    | _ = exp; "="; _ = NATIVEINT -> mkTrue loc
    | _ = NATIVEINT; "="; _ = NATIVEINT -> mkTrue loc
    | _ = NATIVEINT; "<="; _ = exp -> mkTrue loc
    | _ = exp; "<="; _ = NATIVEINT -> mkTrue loc
    | _ = NATIVEINT; "<="; _ = NATIVEINT -> mkTrue loc
    | _ = NATIVEINT; ">="; _ = exp -> mkTrue loc
    | _ = exp; ">="; _ = NATIVEINT -> mkTrue loc
    | _ = NATIVEINT; ">="; _ = NATIVEINT -> mkTrue loc
    | _ = NATIVEINT; "<"; _ = exp -> mkTrue loc
    | _ = exp; "<"; _ = NATIVEINT -> mkTrue loc
    | _ = NATIVEINT; "<"; _ = NATIVEINT -> mkTrue loc
    | _ = NATIVEINT; ">"; _ = exp -> mkTrue loc
    | _ = exp; ">"; _ = NATIVEINT -> mkTrue loc
    | _ = NATIVEINT; ">"; _ = NATIVEINT -> mkTrue loc
    | _ = NATIVEINT; "!="; _ = exp -> mkTrue loc
    | _ = exp; "!="; _ = NATIVEINT -> mkTrue loc
    | _ = NATIVEINT; "!="; _ = NATIVEINT -> mkTrue loc
    | x = INT; "="; y = INT ->
      let tmp = if int_of_string x = int_of_string y then BConst (true,loc) else BConst(false,loc) in
      BForm ((tmp, None), None)
    |	x = exp; "<"; y = exp ->
      if is_res_var y && is_zero x then BForm ((BVar (get_var "res" !stab, loc), None), None) else
      if is_res_var x && is_one y then Not (BForm ((BVar (get_var "res" !stab, loc), None), None), None, loc) else
      let tmp = 
        if is_node y & is_zero x then Neq (Var(get_var (get_node y) !stab, loc), Null loc, loc)
        else
        if is_node x & is_one y then Eq (Var(get_var (get_node x) !stab, loc), Null loc, loc)
        else
        if is_self_var y then Neq (Var(get_var "self" !stab, loc), Null loc, loc)
        else Lt (x, y, loc) 
      in BForm ((tmp, None), None)
    | x = exp; ">"; y = exp ->
      if is_res_var x && is_zero y then BForm ((BVar (get_var "res" !stab, loc), None), None) else
      if is_res_var y && is_one x then Not (BForm ((BVar (get_var "res" !stab, loc), None), None), None, loc) else
      let tmp = 
        if is_node x && is_zero y then Neq (Var(get_var (get_node x) !stab, loc), Null loc, loc)
        else 
        if is_node y && is_one x then Eq (Var(get_var (get_node y) !stab, loc), Null loc, loc)
        else 
        if is_self_var x then Neq (Var(get_var "self" !stab, loc), Null loc, loc)
        else Gt (x, y, loc) 
      in BForm ((tmp, None), None)
    | x = exp; "<="; y = exp ->
      if is_res_var x && is_zero y then Not (BForm ((BVar (get_var "res" !stab, loc), None), None), None, loc) else
      if is_res_var y && is_one x then BForm ((BVar (get_var "res" !stab, loc), None), None) else
      let tmp = 
        if is_node x & is_zero y then Eq (Var(get_var (get_node x) !stab, loc), Null loc, loc)
        else
        if is_node y & is_one x then Neq (Var(get_var (get_node y) !stab, loc), Null loc, loc)
        else
        if is_self_var x then Eq (Var(get_var "self" !stab, loc), Null loc, loc)
        else Lte (x, y, loc)
      in BForm ((tmp, None), None)
    | x = exp; ">="; y = exp ->
      if is_res_var y && is_zero x then Not (BForm ((BVar (get_var "res" !stab, loc), None), None), None, loc) else
      if is_res_var x && is_one y then BForm ((BVar (get_var "res" !stab, loc), None), None) else
      let tmp = 
        if is_node y & is_zero x then Eq (Var(get_var (get_node y) !stab, loc), Null loc, loc)
        else
        if is_node x & is_one y then Neq (Var(get_var (get_node x) !stab, loc), Null loc, loc)
        else
        if is_self_var y then Eq (Var(get_var "self" !stab, loc), Null loc, loc)
        else Gte (x, y, loc)
      in BForm ((tmp, None), None)
    | x = exp; "="; y = exp -> 
      let tmp = 
        if is_node x && is_node y then 
          Eq (Var(get_var (get_node x) !stab, loc), Var(get_var (get_node y) !stab, loc), loc)
        else
        if is_node x && is_rec_node y then 
          Eq (Var(get_var (get_node x) !stab, loc), Var(change_name (get_var (get_rec_node y) !stab) "REC", loc), loc)
        else
        if is_node y && is_rec_node x then 
          Eq (Var(get_var (get_node y) !stab, loc), Var(change_name (get_var (get_rec_node x) !stab) "REC", loc), loc)
        else
        if is_rec_node x && is_rec_node y then 
          Eq (Var(change_name (get_var (get_rec_node x) !stab) "REC", loc), Var(change_name (get_var (get_rec_node y) !stab) "REC", loc), loc)
        else Eq (x, y, loc)
      in BForm ((tmp, None), None)
    | x = exp; "!="; y = exp -> 
      let tmp = Neq (x, y, loc) in
      BForm ((tmp, None), None)
    ]
  ]; 
      
  exp:
  [ "exp" LEFTA
    [ x = SELF; "+"; y = SELF -> Add(x, y, loc)
    | x = SELF; "-"; y = SELF -> Subtract(x, y, loc)
    | x = specvar -> Var (x, loc)
    | x = INT -> IConst (int_of_string x, loc) 
    | _ = NATIVEINT -> Var (SpecVar (Named "abc", "abc", Unprimed),loc)
    ]
  ]; 
		
  specvar:
  [ "specvar" NONA
    [ x = LIDENT -> get_var x !stab
    | x = UIDENT -> if is_substr "REC" x 
      then change_name (get_var (String.sub x 3 (String.length x - 3)) !stab) "REC"
      else get_var x !stab
    ]
  ]; 

END
	
let parse_fix s = Gram.parse_string expression (Loc.mk "<string>") s
