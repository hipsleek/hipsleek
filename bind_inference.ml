#include "xdebug.cppo"
open VarGen
open Ast 
open Lexing
open Globals

exception FieldNotFound ;;


(********************************************)
(*********** PRINTING FUNCTIONS *************)
(********************************************)


(* function to print a boolean value *)
let print_bool =
  function  true  -> print_string "true"
          | false -> print_string "false"
;;

(* function to print a list of strings l separated by sep*)
let rec print_string_list l sep =
  match l with 
    []       -> print_string ""
  | h::[]    -> print_string h
  | h::rest  -> print_string (h ^ sep);
    print_string_list rest sep
;; 

(* function to print the name of a type t (being primitive or not) *)
let print_typ t = print_string (get_type_name t)
;;

(* function to print a data declaration *)
let print_data_decl d = 
  print_string ("\n" ^ d.data_name ^ " = {"); 
  let rec print_fields fields =
    match fields with 
      []                     ->  print_string ""
    | (typ,field)::[]        ->  print_string (field ^ " : ");
      print_typ typ;
      print_string "}"
    | (typ,field)::rest      ->  print_string (field ^ " : ");
      print_typ typ;
      print_string ", ";
      print_fields rest 
  in print_fields d.fields 
;;

(* function to print an expression (except Assert, While) and without printing the Lexing objects *) 
let rec print_exp e = 
  match e with 
    Assert (c, co, _)               -> print_string ("Assert")
  | Assign (id,exp,_)               -> print_string (id ^ " <- "); 
    print_exp exp 
  | BConst (b,_)                    -> print_bool b 
  | Bind (id, idl, exp,_)           -> print_string ("bind " ^ id ^ " to ("); 
    print_string_list idl ",";
    print_string ") in {\n";
    print_exp exp;
    print_string " }" 
  | Call (id, idl, _)               -> print_string (id ^ "(");
    print_string_list idl ",";
    print_string ")"
  | Cond (id, expi, expe, _)        -> print_string ("if " ^ id ^ " then {\n");
    print_exp expi;
    print_string "\n}\nelse {\n";
    print_exp expe;  
    print_string "\n}"
  | Debug (b,_)                     -> print_string "Debug "; 
    print_bool b 
  | FConst (f,_)                    -> print_float f 
  | IConst (i,_)                    -> print_int i 
  | New (id, idl,_)                 -> print_string (id ^ " = new("); 
    print_string_list idl ",";
    print_string ")"
  | Null _                          -> print_string "null"
  | Print (i,_)                     -> print_string "Print ";
    print_int i
  | Seq (e1, e2,_)                  -> print_exp e1; 
    print_string " ; \n";
    print_exp e2
  | Var (id,_)                      -> print_string id
  | Unit _                          -> print_string "Unit" 
  | While (id, exp, c1, c2, idl, _) -> print_string "While"
  | Field (id, idl, _)              -> print_string (id ^ ".");
    print_string_list idl "."
;;

(* function to print a list of type (ident * typ) -> the envirnoment *)
let print_environment envi = 
  let rec print_environmentR env  = match env with 
      []               ->  print_string ""
    | (id,typ)::[]     ->  print_string (id ^ ":");
      print_typ typ;
      print_string "}\n"
    | (id,typ)::rest   ->  print_string (id ^ ":");
      print_typ typ;
      print_string ",";    
      print_environmentR rest
  in print_string "\nEnvironment = {";
  print_environmentR envi
;;


(********************************************)
(*********** UTILITY FUNCTIONS **************)
(********************************************)


(* returns the index of the first element in a list which satisfies a predicate p *)
let index_element p l = 
  let rec index p l i = match l with 
      [] -> (-1) 
    | h::rest -> if p h then i+1 else index p rest (i+1)
  in index p l (-1)
;;

(* if we have an element of type 'a * 'b, return the first (the one of type 'a) *)
let return_first (x, _) = x
;; 

(* if we have an element of type 'a * 'b, return the second (the one of type 'b) *)
let return_second (_, y) = y 
;;

(* function that returns a fresh variable with the name preceded by var_name *)
let fresh_variable_name var_name = (var_name ^ "_" ^ (string_of_int (fresh_int ())))
;;

(* functions that returns a number of n fresh variables *) 
let fresh_variable_names n var_name = 
  let names = ref ([] : string list) in
  for i = 1 to n do
    names := (fresh_variable_name var_name) :: !names
  done;
  !names

(********************************************)
(************** MAIN FUNCTIONS **************)
(********************************************)

(* function to replace the field acceses by the corresponding bind expression *)
let rec insert_bind (e:exp) (gamma:type_env) (defs : type_decl list) = match e with 
    Field (id, idl, pos) ->
    (* we look for the variable id in the environment; it is returned the name of the type of this variable, or NotFound exception is raised *)
    let typeV = look_up_raw id gamma in 
    (* we take the declaration of the type; Notfound exception is raised if the declaration  is not found *)
    let data_decl = x_add look_up_data_def_raw defs (get_type_name typeV) in 
    (* now we search the name of the field in the list of the fields of the data type *)
    let index_field = (index_element (function (_,y) -> y = List.hd idl) data_decl.fields) in 
    if index_field = (-1) then raise FieldNotFound
    else 	
      (* we generate a list of size = number of fields of fresh variables *) 
      let fresh_vars = fresh_variable_names (List.length data_decl.fields) id in 
      (* we add the new variable to the environment *) 
      let new_gamma = ((List.nth fresh_vars index_field), (return_first (List.nth data_decl.fields index_field)))::gamma in 
      (* print_environment new_gamma;*)
      let expr = 
        (* if idl=[], that is we have only id.f, then we exp is just a variable *)
        match (List.tl idl) with
          [] -> Var ((List.nth fresh_vars index_field),pos)
        | h::rest -> 
          let  f = Field (List.nth fresh_vars index_field, (List.tl idl), pos)
          in insert_bind f new_gamma defs
      in Bind (id, fresh_vars, expr, pos)
  | Assign (id, exp, pos)              -> let exp_new = insert_bind exp gamma defs 
    in Assign (id, exp_new, pos)
  | Cond (id, exp1, exp2, pos)         -> let exp_new1 = insert_bind exp1 gamma defs 
    in let exp_new2 = insert_bind exp2 gamma defs 
    in Cond (id, exp_new1, exp_new2, pos)
  | Seq (exp1, exp2, pos)              -> let exp_new1 = insert_bind exp1 gamma defs
    in let exp_new2 = insert_bind exp2 gamma defs 
    in Seq (exp_new1, exp_new2, pos)
  | While (id1, exp, c1, c2, idl, pos) -> let exp_new = insert_bind exp gamma defs
    in While (id1, exp_new, c1, c2, idl, pos)
  | _ -> e 
;;


(* function to float bind as outwards as possible *) 
let rec float_bind (e:exp) = match e with 
    _ -> e 
;;


(********************************************)
(**************** TO CHECK ******************)
(********************************************)

(*
(*let a = ["1";"2";"3"] in print_string_list a ;;*)
let pos = { pos_fname = "x"; pos_lnum = 1; pos_bol = 2; pos_cnum = 3 } ;;
(*let t = Prim Int in print_typ t ;;*)
let node = {data_name = "node"; fields = [(Prim Int , "val") ; (VType "node", "next")]} ;;
let environment = [("a",(Prim Int)); ("b",(VType "node")); ("c",(VType "node"))];;
(*let environment = [("a",(Prim Int)); ("b",(VType "node"))] in print_environment environment;;*)
let e = Field ("b",["next";"next";"val"],pos) ;;
let defs = [Data node] ;;
let e1 = Bind ("x",["v";"n"],(Assign ("y",(BConst (true,pos)),pos)),pos);;
let e2 = Call ("func",["x:int"; "y:bool"],pos);;
let e3 = Cond ("true",e1,(New ("y", ["1"; "2"],pos)),pos);;
let e4 = Seq ((Field ("v", ["f1";"f2"], pos)), (Seq (e, e3,pos)), pos) (*in print_exp e4 ; print_string "\n\n" ;; *);;
let e5 = Seq (Assign ("c",(Var ("b",pos)), pos), e, pos ) ;; 
let e6 = Cond ("true",e5,e,pos) ;;
let x = 1 in print_string "%%%% Exp before %%%%\n";
             print_exp e6;
             print_string "\n%%%% Exp after %%%%\n";
             print_exp (insert_bind e6 environment defs); 
             print_string "\n"
;;
*)


(*type program_decl = {
  type_decls : type_decl list;
  proc_decls : proc_decl list
  }

  and type_decl =
    Data of data_decl
  | View of view_decl

  and data_decl = {
  data_name : string;
  fields : (typ * ident) list
  }

  and prim_type =
    Int
  | Bool
  | Float
  | Void

  and typ = 
    Prim of prim_type
  | VType of ident *)
