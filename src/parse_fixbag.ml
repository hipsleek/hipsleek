open VarGen
open Camlp4.PreCast
open Cpure
open Globals
open Lexing
open Gen

module H = Hashtbl
(* module AS = Astsimp *)

let loc = no_pos;;

let tlist=[]

let expression = Gram.Entry.mk "expression";;

let or_formula = Gram.Entry.mk "or_formula";;

let formula = Gram.Entry.mk "formula";;

let pformula = Gram.Entry.mk "pformula";;

let exp = Gram.Entry.mk "exp";;

let specvar = Gram.Entry.mk "specvar";;

let get_var var tl = 
  if String.contains_from var 0 '_' then 
    let sv = String.sub var 1 (String.length var - 1) in
    Typeinfer.get_spec_var_ident tl sv Unprimed
  else if is_substr "PRI" var 
  then Typeinfer.get_spec_var_ident tl (String.sub var 3 (String.length var - 3)) Primed
  else Typeinfer.get_spec_var_ident tl var Unprimed

let is_node var = match var with 
  | Var (SpecVar (_,id,_), _) -> is_substr "NOD" id || id=self
  | _ -> false

let get_node var = match var with 
  | Var (SpecVar (_,id,_), _) -> 
    if id=self then id else 
      String.sub id 3 (String.length id - 3)
  | _ -> report_error no_pos "Expected a pointer variable"

           (*let change_name var name = match var with*)
           (*  | SpecVar (t,id,p) -> SpecVar (t,name ^ id,p)*)
           (*  | _ -> report_error no_pos "Error in change_name"*)

           (*let is_node var = match var with *)
           (*  | Var (SpecVar (_,id,_), _) -> is_substr "NOD" id*)
           (*  | _ -> false*)

           (*let get_node var = match var with *)
           (*  | Var (SpecVar (_,id,_), _) -> String.sub id 3 (String.length id - 3)*)
           (*  | _ -> report_error no_pos "Expecting node var"*)

           (*let is_rec_node var = match var with *)
           (*  | Var (SpecVar (_,id,_), _) -> is_substr "RECNOD" id*)
           (*  | _ -> false*)

           (*let get_rec_node var = match var with *)
           (*  | Var (SpecVar (_,id,_), _) -> String.sub id 6 (String.length id - 6)*)
           (*  | _ -> report_error no_pos "Expecting rec node var"*)

           (*let is_int c = '0' <= c && c <= '9'*)

           EXTEND Gram
           GLOBAL: expression or_formula formula pformula exp specvar;
    expression:
      [ "expression" NONA
          [ x = LIST1 or_formula -> x
          ]
      ];

    or_formula:
      [ "or_formula" LEFTA
          [ x = SELF; "||"; y = SELF -> mkOr x y None loc
                          | x = formula -> x
                          | "true" -> mkTrue loc 
          ]
      ];

    formula:
      [ "formula" LEFTA
          [ x = SELF; "&&"; y = SELF -> mkAnd x y loc
                          | x = pformula -> x 
          ]
      ];

    pformula:
      [ "pformula" LEFTA
          [ x = exp; "<="; y = exp -> 
            begin
              if is_res_var x && is_zero y then 
                Not (BForm ((BVar (get_var "res" tlist, loc), None), None), None, loc) 
              else if is_res_var y && is_one x then 
                BForm ((BVar (get_var "res" tlist, loc), None), None) 
              else
                let tmp = 
                  if is_node x && is_zero y then 
                    BForm((Eq (Var(get_var (get_node x) tlist, loc), Null loc, loc),None),None)
                  else if is_node y && is_one x then 
                    BForm((Neq (Var(get_var (get_node y) tlist, loc), Null loc, loc),None),None)
                  else if is_self_var x then 
                    BForm((Eq (Var(get_var "self" tlist, loc), Null loc, loc) ,None),None)
                  else 
                    match (x,y) with
                    | (Var _, Var _) -> BForm ((BagSub (x, y, loc), None), None)
                    | (Bag _, Var _) -> BForm ((BagSub (x, y, loc), None), None)
                    | _ -> mkTrue loc
                in tmp
            end
                         | x = exp; ">="; y = exp -> 
            begin
              if is_res_var y && is_zero x then 
                Not (BForm ((BVar (get_var "res" tlist, loc), None), None), None, loc) 
              else
              if is_res_var x && is_one y then 
                BForm ((BVar (get_var "res" tlist, loc), None), None) 
              else
                let tmp = 
                  if is_node y && is_zero x then 
                    BForm((Eq (Var(get_var (get_node y) tlist, loc), Null loc, loc),None),None)
                  else
                  if is_node x && is_one y then 
                    BForm((Neq (Var(get_var (get_node x) tlist, loc), Null loc, loc),None),None)
                  else
                  if is_self_var y then 
                    BForm((Eq (Var(get_var "self" tlist, loc), Null loc, loc),None),None)
                  else 
                    match (x,y) with
                    | (Var _, Var _) -> BForm ((BagSub (y, x, loc), None), None)
                    | (Var _, Bag _) -> BForm ((BagSub (y, x, loc), None), None)
                    | _ -> mkTrue loc
                in tmp
            end
                                        | x = exp; "="; y = exp -> 
            begin
              match (x,y) with
              | (FConst _, _) -> mkTrue loc
              | (_, FConst _) -> mkTrue loc
              | _ -> BForm ((Eq (x, y, loc), None), None)
            end
                                                      | x = exp; "!="; y = exp -> BForm ((Neq (x, y, loc), None), None)
                                                                     | "forall"; x = exp; "in"; y = exp; ":"; z = pformula ->
            begin
              match (x,z) with
              | (Var (v1,_), BForm ((Neq(Var(v2,_),Var(v3,_),_),_),_)) -> 
                let res = 
                  if eq_spec_var v1 v2 then BagNotIn (v3,y,loc) else
                  if eq_spec_var v1 v3 then BagNotIn (v2,y,loc) else BConst(true,loc)
                in BForm ((res,None),None)
              | (Var (v1,_), BForm ((Eq(Var(v2,_),Var(v3,_),_),_),_)) -> 
                if eq_spec_var v1 v2 then mkForall [v1]
                    (mkOr (BForm ((BagNotIn (v1,y,loc),None),None)) 
                       (BForm ((Eq (Var (v1,loc),Var (v3,loc),loc),None),None)) None loc) None loc else
                if eq_spec_var v1 v3 then mkForall [v1]
                    (mkOr (BForm ((BagNotIn (v1,y,loc),None),None)) 
                       (BForm ((Eq (Var (v1,loc),Var (v2,loc),loc),None),None)) None loc) None loc else mkTrue loc
              | _ -> mkTrue loc
            end
                                                                                                            | "exists"; x = exp; "in"; y = exp; ":"; z = pformula ->
            let res = begin
              match (x,z) with
              | (Var (v1,_), BForm ((Eq(Var(v2,_),Var(v3,_),_),_),_)) -> 
                if eq_spec_var v1 v2 then BagIn (v3,y,loc) else
                if eq_spec_var v1 v3 then BagIn (v2,y,loc) else BConst(true,loc)
              | _ -> BConst(true,loc)
            end
            in BForm ((res,None),None)
          ]
      ]; 

    exp:
      [ "exp" LEFTA
          [ x = SELF; "+"; y = SELF -> BagUnion([x; y], loc)
                         | x = specvar -> Var (x,loc)
                         | "|"; x = specvar; "|" -> FConst (0.0,loc) (* Do not care, return anything *)
                                           | "{"; x = LIST0 exp SEP ","; "}" -> Bag (x, loc)
                                                                       | x = INT -> IConst (int_of_string x, loc) 
          ]
      ]; 

    specvar:
      [ "specvar" NONA
          [ x = UIDENT -> get_var x tlist
          | x = LIDENT -> get_var x tlist
          ]
      ]; 

    END

let parse_fix s = Gram.parse_string expression (Loc.mk "<string>") s
