type exp =
  | Const of int
  | Var of string
  | Add of (exp * exp)
  | Minus of (exp * exp)
;;

type arr_term =
  | Aseg of (exp * exp)
  | Pto of (exp * exp * exp)
;;

type pure_term =
  | Eq of (exp * exp)
  | Neq of (exp * exp)
  | Lt of (exp * exp)
  | Lte of (exp * exp)
  | Gt of (exp * exp)
  | Gte of (exp * exp)
;;
  
type term =
  | Puref of pure_term
  | Arrf of arr_term
;;

type formula =
  | And of (string list * term list * term list)
;;

type entailment =
  (formula * formula list)
;;

let mkAdd e1 e2 =
  match e1, e2 with
  | Const 0, _ -> e2
  | _, Const 0 -> e1
  | _, _ -> Add (e1, e2)
;;

let add_one e =
  match e with
  | Add (e1, Const num) -> Add (e1, Const (num+1))
  | Add (Const num, e1) -> Add (e1, Const (num+1))
  | _ -> Add (e, Const 1)
;;
  
let str_list printer delimiter lst =
  match lst with
  | h :: tail ->
     List.fold_left
       (fun r item -> r ^ delimiter ^ (printer item))
       (printer h) tail
  | [] -> ""
;;

let rec str_exp = function
  | Const num -> string_of_int num
  | Var name -> name
  | Add (e1, e2) -> (str_exp e1)^"+"^(str_exp e2)
  | Minus (e1, e2) -> (str_exp e1)^"-"^(str_exp e2)
;;

let rec str_arr_term = function
  | Aseg (e1, e2) -> "base::AsegNE<" ^ (str_exp e1) ^ ", " ^ (str_exp (add_one e2)) ^ ">"
  | Pto (e1, e2, e3) -> "base::Elem<" ^ (str_exp e1) ^ ", " ^ (str_exp e2) ^ ", " ^ (str_exp e3) ^ ">"
;;

let rec str_pure_term = function
  | Eq (e1, e2) -> (str_exp e1) ^ "=" ^ (str_exp e2)
  | Neq (e1, e2) -> (str_exp e1) ^ "!=" ^ (str_exp e2)
  | Lt (e1, e2) -> (str_exp e1) ^ "<" ^ (str_exp e2)
  | Lte (e1, e2) -> (str_exp e1) ^ "<=" ^ (str_exp e2)
  | Gt (e1, e2) -> (str_exp e1) ^ ">" ^ (str_exp e2)
  | Gte (e1, e2) -> (str_exp e1) ^ ">=" ^ (str_exp e2)
;;
  
let str_term = function
  | Arrf arr_term -> str_arr_term arr_term
  | Puref pure_term -> str_pure_term pure_term
;;

let str_formula = function
  | And (elst, plst, hlst) ->
     let exists =
       if List.length elst = 0
       then ""
       else "exists " ^ (str_list (fun x->x) "," elst) ^ (" : ")
     in

     exists ^ (str_list str_term " * " hlst) ^
       (if List.length plst > 0 && List.length hlst > 0 then " & " else "" ) ^
         (str_list str_term " & " plst)
;;

let str_formula_lhs = function
  | And (elst, plst, hlst) ->
     (str_list str_term " * " hlst) ^
       (if List.length plst > 0 && List.length hlst > 0 then " & " else "" ) ^
         (str_list str_term " & " plst)
;;
  
let str_entailment = function
  | (lhs, rhs) ->
     "infer[@arr_en] " ^
     (str_formula lhs) ^
       " |- " ^
         (str_list (fun item ->  (str_formula item) ) " or "rhs) ^ "."
;;
