open Cpure
open VarGen
open Cformula
       
type arrPred =
  | Aseg of (exp * exp * exp)
  | Gap of (exp * exp * exp)
  | Elem of (exp * exp)
;;

let mkAseg b s e =
  Aseg (b,s,e)
;;

let mkGap b s e =
  Gap (b,s,e)
;;

let mkElem b s =
  Elem (b,s)
;;

let isEq s1 e1 pf =
  (* pf |= s1 == e1 *)
  let rhsf = mkEqExp s1 e1 no_pos in
  !tp_imply pf rhsf
;;

let isGt s1 e1 pf =
  (* pf |= s1 > e1 *)
  let rhsf = mkGtExp s1 e1 no_pos in
  !tp_imply pf rhsf
;;

let incOne e =
  Add (e,IConst (1,no_pos),no_pos)
;;

let str_exp = print_exp
;;

let str_cformula = Cformula.print_formula
;;

let str_pformula = Cpure.print_formula
;;
  
let str_arrPred apred =
  match apred with
  | Aseg (b,s,e) ->
     "Aseg("^(!str_exp b)^","^(!str_exp s)^","^(!str_exp e)^")"
  | Gap (b,s,e)->
     "Gap("^(!str_exp b)^","^(!str_exp s)^","^(!str_exp e)^")"
  | Elem (b,s) ->
     "Elem("^(!str_exp b)^","^(!str_exp s)^")"
;;
  
let str_list =
  Gen.Basic.pr_list
;;

let str_pair=
  Gen.Basic.pr_pair
;;

let str_seq seq =
  str_list str_arrPred seq
;;

let rec flatten_heap_star_formula cf =
  match cf with
  | Star f ->
     (flatten_heap_star_formula f.h_formula_star_h1)@(flatten_heap_star_formula f.h_formula_star_h2)
  | ViewNode _ -> [cf]
  | _ -> failwith "flatten_heap_star_formula: Invalid input"
;;

let isAsegPred cf =
  match cf with
  | ViewNode f ->
     String.equal f.h_formula_view_name  "Aseg"
  | _ -> false
;;

let pred_var_to_arrPred_exp sv =
  Var (sv,no_pos)
;;
  
let getAsegBase cf =
  match cf with
  | ViewNode f ->
     pred_var_to_arrPred_exp f.h_formula_view_node
  | _ -> failwith "getAsegBase: Invalid input"
;;
  
let getAsegStart cf =
  match cf with
  | ViewNode f ->
     pred_var_to_arrPred_exp (List.nth f.h_formula_view_arguments 0)
  | _ -> failwith "getAsegStart: Invalid input"
;;

let getAsegEnd cf =
  match cf with
  | ViewNode f ->
     pred_var_to_arrPred_exp (List.nth f.h_formula_view_arguments 1)
  | _ -> failwith "getAsegEnd: Invalid input"
;;

let getElemBase cf =
  match cf with
  | ViewNode f ->
     pred_var_to_arrPred_exp f.h_formula_view_node
  | _ -> failwith "getElemBase: Invalid input"
;;
  
let getElemStart cf =
  match cf with
  | ViewNode f ->
     pred_var_to_arrPred_exp (List.nth f.h_formula_view_arguments 0)
  | _ -> failwith "getElemStart: Invalid input"
;;

let isElemPred cf =
  match cf with
  | ViewNode f ->
     String.equal f.h_formula_view_name "Elem"
  | _ -> false
;;

  
let one_pred_to_arrPred cf=
  if isAsegPred cf
  then mkAseg (getAsegBase cf) (getAsegStart cf) (getAsegEnd cf)
  else
    if isElemPred cf
    then mkElem (getElemBase cf) (getElemStart cf)
    else failwith "one_pred_to_arrPred: Invalid input"
;;

let formula_to_arrPred cf =
  match cf with
  | Base f ->
     let pred_list = flatten_heap_star_formula f.formula_base_heap in
     List.map one_pred_to_arrPred pred_list
  | Or f-> failwith "TO BE IMPLEMENTED"
  | Exists f -> failwith "TO BE IMPLEMENTED"
;;
  
let formula_to_arrPred cf =
  Debug.no_1 "formula_to_arrPred" !str_cformula str_seq formula_to_arrPred cf
;;
  
let biabduction (plhs,seqLHS) (prhs,seqRHS) =
  let rec helper seqLHS seqRHS antiframe frame =
    match seqLHS, seqRHS with
    | h1::tail1, h2::tail2 ->
       (
         match h1, h2 with
         | Aseg (b1, s1, e1), Aseg (b2, s2, e2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame
            else
              if isEq s2 e2 plhs
              then helper seqLHS tail2 antiframe frame
              else                (* Neither sides are empty *)
                if isEq s1 s2 plhs
                then
                  if isGt e1 e2 plhs  (* e1>e2 *)
                  then
                    helper ((mkAseg b1 e2 e1)::tail1) tail2 antiframe frame
                  else            (* e1<e2 *)
                    helper tail1 ((mkAseg b1 e1 e2)::tail2) antiframe frame
                else
                  if isGt s1 s2 plhs
                  then helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame
                  else helper seqLHS ((mkGap b2 s1 s2)::seqRHS) antiframe frame                  
         | Aseg (b1, s1, e1), Elem (b2, s2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame
            else
              if isEq s1 s2 plhs
              then
                helper ((mkAseg b1 (incOne s1) e1)::tail1) tail2 antiframe frame
              else
                if isGt s1 s2 plhs  (* s1>s2 *)
                then
                  helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame
                else            (* s1<s2 *)
                  helper seqLHS ((mkGap b1 s1 s2)::seqRHS) antiframe frame
         | Aseg (b1, s1, e1), Gap (b2, s2, e2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame
            else
              if isEq s1 s2 plhs
              then
                if isGt e1 e2 plhs  (* e1>e2 *)
                then helper ((mkAseg b1 e2 e1)::tail1) tail2 antiframe ((mkAseg b1 s1 e2)::frame)
                else helper tail1 ((mkGap b2 e1 e2)::tail2) antiframe ((mkAseg b1 s1 e1)::frame)
              else
                if isGt s1 s2 plhs  (* s1>s2 *)
                then helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame
                else helper seqLHS ((mkGap b2 s1 e2)::tail2) antiframe frame
         | Elem (b1, s1), Elem (b2, s2) ->
            if isEq s1 s2 plhs
            then helper tail1 tail2 antiframe frame
            else
              if isGt s1 s2 plhs
              then helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame
              else helper seqLHS ((mkGap b2 s1 s2)::seqRHS) antiframe frame
         | Elem (b1, s1), Aseg (b2, s2, e2) ->
            if isEq s2 e2 plhs
            then helper seqLHS tail2 antiframe frame
            else
              if isEq s1 s2 plhs
              then helper tail1 ((mkAseg b2 (incOne s2) e2)::tail2) antiframe frame
              else
                if isGt s1 s2 plhs
                then helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame
                else helper seqLHS ((mkGap b2 s1 s2)::seqRHS) antiframe frame                            
         | Elem (b1, s1), Gap (b2, s2, e2) ->
            if isEq s2 e2 plhs
            then helper seqLHS tail2 antiframe frame
            else
              if isEq s1 s2 plhs
              then helper tail1 ((mkGap b2 (incOne s2) e2)::tail2) antiframe ((mkElem b1 s1)::frame)
              else
                if isGt s1 s2 plhs
                then helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame
                else helper seqLHS ((mkGap b2 s1 e2)::tail2) antiframe frame (* Just make the gap bigger *)
         | Gap (b1, s1, e1), Gap (b2, s2, e2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame
            else
              if isEq s2 e2 plhs
              then helper seqLHS tail2 antiframe frame
              else                (* Neither sides are empty *)
                if isEq s1 s2 plhs
                then
                  if isGt e1 e2 plhs  (* e1>e2 *)
                  then
                    helper ((mkGap b1 e2 e1)::tail1) tail2 antiframe frame
                  else            (* e1<e2 *)
                    helper tail1 ((mkGap b1 e1 e2)::tail2) antiframe frame
                else
                  if isGt s1 s2 plhs
                  then helper ((mkGap b1 s2 e1)::tail1) seqRHS antiframe frame
                  else helper seqLHS ((mkGap b2 s1 e2)::tail2) antiframe frame                  
         | Gap (b1, s1, e1), Elem (b2, s2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame
            else
              if isEq s1 s2 plhs
              then helper ((mkGap b1 (incOne s1) e1)::tail1) tail2 ((mkElem b2 s2)::antiframe) frame
              else
                if isGt s1 s2 plhs
                then helper ((mkGap b1 s2 e1)::tail1) seqRHS antiframe frame (* Just make the gap bigger *)
                else helper seqLHS ((mkGap b2 s1 s2)::seqRHS) antiframe frame
         | Gap (b1, s1, e1), Aseg (b2, s2, e2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame
            else
              if isEq s2 e2 plhs
              then helper seqLHS tail2 antiframe frame
              else
                if isEq s1 s2 plhs
                then
                  if isGt e1 e2 plhs
                  then helper ((mkGap b1 e2 e1)::tail1) tail2 ((mkAseg b2 s2 e2)::antiframe) frame
                  else helper tail1 ((mkAseg b2 e1 e2)::tail2) ((mkAseg b2 s2 e1)::antiframe) frame
                else
                  if isGt s1 s2 plhs
                  then helper ((mkGap b1 s2 e1)::tail1) seqRHS antiframe frame
                  else helper seqLHS ((mkGap b2 s1 e2)::tail2) antiframe frame
       )                              
    | h1::tail1, [] ->
       (antiframe,seqLHS@frame)
    | [], h2::tail2 ->
       (seqRHS@antiframe,frame)
    | [],[] ->
       (antiframe, frame)
  in
  helper seqLHS seqRHS [] []
;;

let biabduction (plhs,seqLHS) (prhs,seqRHS) =
  let pr_input = str_pair !str_pformula str_seq in
  Debug.no_2 "biabduction" pr_input pr_input (str_pair str_seq str_seq) biabduction (plhs,seqLHS) (prhs,seqRHS)
;;

let cf_biabduction ante conseq =
  let lhs_p = get_pure ante in
  let rhs_p = get_pure conseq in
  let ante_seq = formula_to_arrPred ante in
  let conseq_seq = formula_to_arrPred conseq in
  biabduction (lhs_p,ante_seq) (rhs_p,conseq_seq)
;;
  
