#include "xdebug.cppo"

open Cpure
open VarGen
open Cformula
       
type 'exp arrPred =
  | Aseg of ('exp * 'exp * 'exp)
  | Gap of ('exp * 'exp * 'exp)
  | Elem of ('exp * 'exp)
;;

  
let map_op_list (f:('a -> 'b)) (lst:('a option list)) =
  List.fold_left
    (fun r item ->
      match item with
      | Some a -> (f a)::r
      | None -> r)
    [] lst
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

let isGte s1 e1 pf =
  (* pf |= s1 >= e1 *)
  let rhsf = mkGteExp s1 e1 no_pos in
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
     String.equal f.h_formula_view_name "Aseg"
  | _ -> false
;;

let isElemPred cf =
  match cf with
  | ViewNode f ->
     String.equal f.h_formula_view_name "Elem"
  | _ -> false
;;

let isEmpty cf =
  false
;;

class arrPredTransformer initcf = object(self)
  val cf = initcf               (* cf is Cformula.formula *)
  val mutable eqmap = ([]: (spec_var * exp) list)
      
  method find_in_eqmap sv =
    try
      let (_,e1) = List.find (fun (v,e) -> (compare_sv sv v)=0) eqmap
      in
      Some e1
    with _ ->
      None
          
  method pred_var_to_arrPred_exp sv =
    match (self#find_in_eqmap sv) with
    | None ->
       Var (sv,no_pos)
    | Some e ->
       e
         
  method getAsegBase cf =
    match cf with
    | ViewNode f ->
       self#pred_var_to_arrPred_exp f.h_formula_view_node
    | _ -> failwith "getAsegBase: Invalid input"
    
  method getAsegStart cf =
    match cf with
    | ViewNode f ->
       self#pred_var_to_arrPred_exp (List.nth f.h_formula_view_arguments 0)
    | _ -> failwith "getAsegStart: Invalid input"

  method getAsegEnd cf =
    match cf with
    | ViewNode f ->
       self#pred_var_to_arrPred_exp (List.nth f.h_formula_view_arguments 1)
    | _ -> failwith "getAsegEnd: Invalid input"
  
  method getElemBase cf =
    match cf with
    | ViewNode f ->
       self#pred_var_to_arrPred_exp f.h_formula_view_node
    | _ -> failwith "getElemBase: Invalid input"
 
  method getElemStart cf =
    match cf with
    | ViewNode f ->
       self#pred_var_to_arrPred_exp (List.nth f.h_formula_view_arguments 0)
    | _ -> failwith "getElemStart: Invalid input"

  method formula_to_arrPred =
    let one_pred_to_arrPred cf=
      if isAsegPred cf
      then Some (mkAseg (self#getAsegBase cf) (self#getAsegStart cf) (self#getAsegEnd cf))
      else
        if isElemPred cf
        then Some (mkElem (self#getElemBase cf) (self#getElemStart cf))
        else
          if isEmpty cf
          then None
          else failwith "one_pred_to_arrPred: Invalid input"
    in    
    let build_eqmap pf evars=
      let eqlst = find_eq_at_toplevel pf in
      let evarsContains evars sv =
        try 
          List.exists (fun v -> (compare_sv v sv)=0) evars
        with _ ->
          false
      in
      let helper (e1,e2) =
        match e1,e2 with
        | Var (sv1,_) , Var (sv2,_) ->
           if evarsContains evars sv1 && evarsContains evars sv2
           then [(sv1,e2);(sv2,e1)]
           else
             if evarsContains evars sv1
             then [(sv1,e2)]
             else [(sv2,e1)]
        | Var (sv,_), e
          | e, Var (sv,_) ->
           if evarsContains evars sv
           then [(sv,e2)]
           else []
        | _,_ -> []
      in
      List.fold_left (fun r ee -> (helper ee)@r) [] eqlst
    in
    match cf with
    | Base f ->
       let pred_list = flatten_heap_star_formula f.formula_base_heap in
       map_op_list (fun x->x) (List.map one_pred_to_arrPred pred_list)       
    | Or f-> failwith "TO BE IMPLEMENTED"
    | Exists f ->
       let pf = Mcpure.pure_of_mix f.formula_exists_pure in
       let evars = f.formula_exists_qvars in
       let () = eqmap <- build_eqmap pf evars in
       let pred_list = flatten_heap_star_formula f.formula_exists_heap in
       map_op_list (fun x->x) (List.map one_pred_to_arrPred pred_list)
end
;;
    
  
(* let formula_to_arrPred cf = *)
(*   Debug.no_1 "formula_to_arrPred" !str_cformula str_seq formula_to_arrPred cf *)
(* ;; *)
  
let biabduction (plhs,seqLHS) (prhs,seqRHS) =
  let rec helper seqLHS seqRHS antiframe frame prooftrace =
    let prooftrace = (seqLHS,seqRHS)::prooftrace in
    match seqLHS, seqRHS with
    | h1::tail1, h2::tail2 ->
       (
         match h1, h2 with
         | Aseg (b1, s1, e1), Aseg (b2, s2, e2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame prooftrace
            else
              if isEq s2 e2 plhs
              then helper seqLHS tail2 antiframe frame prooftrace
              else                (* Neither sides are empty *)
                if isEq s1 s2 plhs
                then
                  if isGt e1 e2 plhs  (* e1>e2 *)
                  then
                    helper ((mkAseg b1 e2 e1)::tail1) tail2 antiframe frame prooftrace
                  else            (* e1<e2 *)
                    helper tail1 ((mkAseg b1 e1 e2)::tail2) antiframe frame prooftrace
                else
                  if isGt s1 s2 plhs
                  then helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame prooftrace
                  else helper seqLHS ((mkGap b2 s1 s2)::seqRHS) antiframe frame prooftrace       
         | Aseg (b1, s1, e1), Elem (b2, s2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame prooftrace
            else
              if isEq s1 s2 plhs
              then
                helper ((mkAseg b1 (incOne s1) e1)::tail1) tail2 antiframe frame prooftrace
              else
                if isGt s1 s2 plhs  (* s1>s2 *)
                then
                  helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame prooftrace
                else            (* s1<s2 *)
                  helper seqLHS ((mkGap b1 s1 s2)::seqRHS) antiframe frame prooftrace
         | Aseg (b1, s1, e1), Gap (b2, s2, e2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame prooftrace
            else
              if isEq s1 s2 plhs
              then
                if isGt e1 e2 plhs  (* e1>e2 *)
                then helper ((mkAseg b1 e2 e1)::tail1) tail2 antiframe ((mkAseg b1 s1 e2)::frame) prooftrace
                else helper tail1 ((mkGap b2 e1 e2)::tail2) antiframe ((mkAseg b1 s1 e1)::frame) prooftrace
              else
                if isGt s1 s2 plhs  (* s1>s2 *)
                then helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame prooftrace
                else helper seqLHS ((mkGap b2 s1 e2)::tail2) antiframe frame prooftrace
         | Elem (b1, s1), Elem (b2, s2) ->
            if isEq s1 s2 plhs
            then helper tail1 tail2 antiframe frame prooftrace
            else
              if isGt s1 s2 plhs
              then helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame prooftrace
              else helper seqLHS ((mkGap b2 s1 s2)::seqRHS) antiframe frame prooftrace
         | Elem (b1, s1), Aseg (b2, s2, e2) ->
            if isEq s2 e2 plhs
            then helper seqLHS tail2 antiframe frame prooftrace
            else
              if isEq s1 s2 plhs
              then helper tail1 ((mkAseg b2 (incOne s2) e2)::tail2) antiframe frame prooftrace
              else
                if isGte s1 s2 plhs
                then helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame prooftrace
                else helper seqLHS ((mkGap b2 s1 s2)::seqRHS) antiframe frame prooftrace               
         | Elem (b1, s1), Gap (b2, s2, e2) ->
            if isEq s2 e2 plhs
            then helper seqLHS tail2 antiframe frame prooftrace
            else
              if isEq s1 s2 plhs
              then helper tail1 ((mkGap b2 (incOne s2) e2)::tail2) antiframe ((mkElem b1 s1)::frame) prooftrace
              else
                if isGt s1 s2 plhs
                then helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame prooftrace
                else helper seqLHS ((mkGap b2 s1 e2)::tail2) antiframe frame prooftrace(* Just make the gap bigger *)
         | Gap (b1, s1, e1), Gap (b2, s2, e2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame prooftrace
            else
              if isEq s2 e2 plhs
              then helper seqLHS tail2 antiframe frame prooftrace
              else                (* Neither sides are empty *)
                if isEq s1 s2 plhs
                then
                  if isGt e1 e2 plhs  (* e1>e2 *)
                  then
                    helper ((mkGap b1 e2 e1)::tail1) tail2 antiframe frame prooftrace
                  else            (* e1<e2 *)
                    helper tail1 ((mkGap b1 e1 e2)::tail2) antiframe frame prooftrace
                else
                  if isGt s1 s2 plhs
                  then helper ((mkGap b1 s2 e1)::tail1) seqRHS antiframe frame prooftrace
                  else helper seqLHS ((mkGap b2 s1 e2)::tail2) antiframe frame prooftrace       
         | Gap (b1, s1, e1), Elem (b2, s2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame prooftrace
            else
              if isEq s1 s2 plhs
              then helper ((mkGap b1 (incOne s1) e1)::tail1) tail2 ((mkElem b2 s2)::antiframe) frame prooftrace
              else
                if isGt s1 s2 plhs
                then helper ((mkGap b1 s2 e1)::tail1) seqRHS antiframe frame prooftrace(* Just make the gap bigger *)
                else helper seqLHS ((mkGap b2 s1 s2)::seqRHS) antiframe frame prooftrace
         | Gap (b1, s1, e1), Aseg (b2, s2, e2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame prooftrace
            else
              if isEq s2 e2 plhs
              then helper seqLHS tail2 antiframe frame prooftrace
              else
                if isEq s1 s2 plhs
                then
                  if isGt e1 e2 plhs
                  then helper ((mkGap b1 e2 e1)::tail1) tail2 ((mkAseg b2 s2 e2)::antiframe) frame prooftrace
                  else helper tail1 ((mkAseg b2 e1 e2)::tail2) ((mkAseg b2 s2 e1)::antiframe) frame prooftrace
                else
                  if isGt s1 s2 plhs
                  then helper ((mkGap b1 s2 e1)::tail1) seqRHS antiframe frame prooftrace
                  else helper seqLHS ((mkGap b2 s1 e2)::tail2) antiframe frame prooftrace
       )                              
    | h1::tail1, [] ->
       (
         match h1 with
           Aseg (b,s,e) 
         | Gap (b,s,e) when isEq s e plhs ->
            helper tail1 seqRHS antiframe frame prooftrace
         | _ ->
            (antiframe,seqLHS@frame,prooftrace)
       )
    | [], h2::tail2 ->
       (
         match h2 with
           Aseg (b,s,e)
         | Gap (b,s,e) when isEq s e plhs->
            helper seqLHS tail2 antiframe frame prooftrace
         | _ ->
            (seqRHS@antiframe,frame,prooftrace)            
       )       
    | [],[] ->
       (antiframe, frame,prooftrace)
  in
  helper seqLHS seqRHS [] [] []
;;

let biabduction (plhs,seqLHS) (prhs,seqRHS) =
  let pr_input = str_pair !str_pformula str_seq in
  let pr_result (a,f,t) =
    (str_pair str_seq str_seq) (a,f)
  in
  Debug.no_2 "biabduction" pr_input pr_input pr_result biabduction (plhs,seqLHS) (prhs,seqRHS)
;;

let rec clean_gap seq =
  match seq with
  | (Gap _)::tail ->
     clean_gap tail
  | h::tail ->
     h::(clean_gap tail)
  | [] -> []
;;

type 'a rect =
  | Rect of (unit -> ('a * ('a rect)) option)
;;
  
let enumerate_solution_seed vlst =
  let length = List.length vlst in
  let updateSeed seed seed_i = seed_i::seed in
  let empty_seed = [] in
  let do_biabduction seed =
    ()
  in
  let rec innerk_orig level curi seed ((Rect k):('a rect)) () =
    if level = length
    then
      Some (seed, Rect k)
    else
      if curi = 3
      then k ()        
      else
        innerk_orig (level+1) 0 (updateSeed seed (curi+1)) (Rect (innerk_orig level (curi+1) seed (Rect k))) ()
  in
  let rec helper cur seed (Rect innerk) k () =
    if cur = length
    then
      let _ = do_biabduction seed in
      k ()
    else
      match innerk () with
      | None ->
         k ()
      | Some (seed_i,Rect inner_i) ->
         let newseed = updateSeed seed seed_i in
         helper (cur+1) newseed (Rect (innerk_orig (cur+1) 0 empty_seed (Rect (fun ()->None)))) (helper cur seed (Rect inner_i) k) ()
  in
  
  helper 0 empty_seed (Rect (innerk_orig 1 0 empty_seed (Rect (fun ()->None)))) (fun x->x) ()
;;
  
  
let cf_biabduction ante conseq =
  let lhs_p = get_pure ante in
  let rhs_p = get_pure conseq in
  let ante_seq = (new arrPredTransformer ante)#formula_to_arrPred in
  let conseq_seq = (new arrPredTransformer conseq)#formula_to_arrPred in  
  let (antiframe,frame,prooftrace) = biabduction (lhs_p,ante_seq) (rhs_p,conseq_seq) in
  let (cantiframe,cframe) = (clean_gap antiframe,clean_gap frame) in
  let str_trace_pair (alst,clst) =
    "  "^(str_seq alst)^" |= "^(str_seq clst)
  in
  let str_trace trace =
    List.fold_left (fun r pair -> (str_trace_pair pair)^"\n"^r) "" trace
  in
  
  print_endline"############## Results of Bi-Abduction Inference ################";
  print_endline ("# pure: "^(!str_pformula lhs_p));
  print_endline ("# anti-frame: "^(str_seq cantiframe));
  print_endline ("# frame: "^(str_seq cframe));
  print_endline "############## ####### Proof Trace ###########  ################";
  print_endline (str_trace prooftrace);
  ()
  (* print_endline "############## ####### ########### ###########  ################"             *)
;;
