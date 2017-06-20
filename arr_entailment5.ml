#include "xdebug.cppo"
open Arr_biabduction_extend

(* This version early check pure formula in LHS *)
(* This version handle existential in a wrapping manner *)

       
(* Heap term for arrays *)
type asegPred =
  | Aseg of (Cpure.exp * Cpure.exp)
  | AsegNE of (Cpure.exp * Cpure.exp)
  | Pointsto of (Cpure.exp * Cpure.exp)
  | Emp
;;

  
(* Not sure whether this is necessary *)
let mkAsegNE f t = AsegNE (f,t);;
let mkAseg f t = Aseg (f,t);;
let mkPointsto t v = Pointsto (t,v);;

(* Formula *)
type arrF =
  (* existential vars * pure formulas * heap formulas *)
  (Cpure.exp list) * (puref list) * (asegPred list)
;;

(* This may increase readability *)
let mkArrF e p h = (e,p,h);;

let unfold_AsegNE t m =  
  [mkPointsto t (mkVar (global_get_new_var ()));mkAseg (incOne t) m]
;;

let contains_evar elst v =
  List.exists (fun item -> is_same_exp item v) elst
;;

let str_asegPred aseg =
  match aseg with
  | Aseg (s,e) ->
     (* "Aseg("^(!str_exp b)^","^(!str_exp s)^","^(!str_exp e)^")" *)
     "Aseg("^(!str_exp s)^","^(!str_exp e)^")"
  | AsegNE (s,e)->
     (* "Gap("^(!str_exp b)^","^(!str_exp s)^","^(!str_exp e)^")" *)
     "AsegNE("^(!str_exp s)^","^(!str_exp e)^")"
  | Pointsto (t,v)->
     (* "Gap("^(!str_exp b)^","^(!str_exp s)^","^(!str_exp e)^")" *)
     (!str_exp t)^" -> "^(!str_exp v)
  | Emp ->
     (* "Elem("^(!str_exp b)^","^(!str_exp s)^")" *)
     "EMP"
;;
  
let str_arrF (e,p,h) =
  (* (str_list !str_pformula p)^":"^(str_list str_asegPred h) *)
  (str_list !str_exp e)^(str_list !str_pformula p)^":"^(str_list str_asegPred h)
;;

let str_disj_arrF flst =
  "{" ^
    (match flst with
     | h::tail ->
        List.fold_left
          (fun r item ->
            (str_arrF item)^" \/ "^r)
          (str_arrF h) tail
     | [] -> "" )
    ^ "}"
;;

let print_and_return f indent =
  let f = simplify f in
  let () =
    if true(* not (isValid f) *)
    then
      print_endline (print_indent indent ("==> "^(!str_pformula f )))
    else
      ()
  in
  f                         
;;
  
(* input: heap formulas (with AsegNE only), output: a pure formula with sorted information  *)
let get_sorted_puref arrPredlst =
  let rec helper lst lastm flst =
    match lst with
    | [] -> mkAndlst flst
    | h::tail ->
       ( match h with
         | AsegNE (t,m) ->
            helper tail m ([mkLte lastm t;mkLt t m]@flst)
         | Pointsto (t,v) ->
            helper tail (incOne t) ((mkLte lastm t)::flst)
         | _ -> failwith "get_sorted_puref: Invalid input" )
  in
  match arrPredlst with
  | [] -> mkTrue ()
  | h::tail ->
     ( match h with
       | AsegNE (t,m) ->
          helper tail m []
       | Pointsto (t,v) ->
          helper tail (incOne t) []
       | _ -> failwith "get_sorted_puref: Invalid input" )
;;

(* input: heap formulas, output: a pure formula with sorted information  *)  
let get_sorted_puref_general arrPredlst =
  let rec helper lst lastm flst =
    match lst with
    | [] -> mkAndlst flst
    | h::tail ->
       ( match h with
         | AsegNE (t,m) ->
            helper tail m ([mkLte lastm t;mkLt t m]@flst)
         | Pointsto (t,v) ->
            helper tail (incOne t) ((mkLte lastm t)::flst)
         | Aseg (t,m) ->
            mkOr
              (helper tail lastm ((mkEq t m)::flst))
              (helper tail m ([mkLte lastm t;mkLt t m]@flst))
         | _ -> failwith "get_sorted_puref: Invalid input" )
  in

  let rec helper_entry arrPredlst flst =
    match arrPredlst with
    | [] -> mkAndlst flst
    | h::tail ->
       ( match h with
         | AsegNE (t,m) ->
            helper tail m [mkLt t m]
         | Pointsto (t,v) ->
            helper tail (incOne t) []
         | Aseg (t,m) ->
            mkOr
              (helper_entry tail ((mkEq t m)::flst))
              (helper tail m ((mkLt t m)::flst))
         | _ -> failwith "get_sorted_puref: Invalid input" )
  in
  helper_entry arrPredlst []
;;  

let generic_get_permutation lst =
  let rec insert k lst =
    match lst with
    | h::tail -> 
       (k::lst)::(List.map (fun item -> h::item) (insert k tail))
    | [] -> [[k]]
  in
  let rec helper lst =
    let () = print_endline ("call helper here " ^ (str_list str_asegPred lst)) in
    match lst with
    | [] -> [[]]
    | h::tail -> List.flatten (List.map (insert h) (helper tail))
  in
  let r = helper lst in
  if List.length r = 0
  then failwith "empty list 2"
  else r
;;

let get_permutation arrPredlst =
  let rec helper head lst flst =
    match lst with
    | (Aseg (t,m))::tail ->
       (helper head tail ((mkEq t m)::flst))@(helper ((AsegNE (t,m))::head) tail ((mkLt t m)::flst))
    | h::tail -> helper (h::head) tail flst
    | [] ->
       List.map (fun item -> ((get_sorted_puref item)::flst,item)) (generic_get_permutation head)
  in
  let r = helper [] arrPredlst [] in
  if List.length r = 0
  then failwith "empty list 1"
  else r
;;
  
(* What about the pure formulas?  *)
let expand_disj_with_permutation disj =
  let r =List.concat
           (List.map
              (fun (e,p,h) ->
                List.map (fun (np,nh) -> (e,np@p,nh)) (get_permutation h)) disj) in
  if List.length r = 0
  then failwith "empty list"
  else r
;;
  
      
(* Translation from data structure in arr_biabduction.ml *)
let arrPred_to_asegPred arrPred_lst_lst =
  let helper_heap_translation_one h =
    match h with
    | Arr_biabduction_extend.Aseg (b,f,t) -> Aseg (f,t)
    | Arr_biabduction_extend.AsegNE (b,f,t) -> AsegNE (f,t)
    | Arr_biabduction_extend.Elem (b,t,v) -> Pointsto (t,v)
    | _ -> failwith "arrPred_to_asegPred: Invalid input"
  in
  List.map
    (fun (e,plst,hlst) ->
      (e,plst,List.map helper_heap_translation_one hlst)) arrPred_lst_lst
;;

(* Translation from cformula *)
let cformula_to_arrF cf =
  let trans = new arrPredTransformer cf in
  arrPred_to_asegPred (trans#formula_to_general_formula)
;;

  
  
(* lhs: arrF list *)
(* rhs: arrF list *)
let array_entailment lhs rhs =
  let helper_pure lhs_p rhs indent =
    let rec aux_helper_pure lhs_p rhs plst =
      match rhs with
      | (rhs_e,rhs_p,rhs_h)::tail ->
         if (List.exists
               (fun item ->
                 match item with
                 | AsegNE _ | Aseg _ | Pointsto _-> true
                 | Emp -> false) rhs_h)
         then aux_helper_pure lhs_p tail plst
         else aux_helper_pure lhs_p tail ((mkExists (List.map exp_to_var rhs_e) (mkAndlst rhs_p))::plst)
      | [] ->       
         mkImply (mkAndlst lhs_p) (mkOrlst plst)
    in
    let f = aux_helper_pure lhs_p rhs [] in
    print_and_return f indent
  in
  let remove_emp rhs =
    let rec helper_remove_emp r (rhs_e,rhs_p,rhs_h) =
      match rhs_h with
      | [] -> r
      | Emp::tail ->
         helper_remove_emp r (rhs_e,rhs_p,tail)
      | _ -> (rhs_e,rhs_p,rhs_h)::r
    in
    List.fold_left helper_remove_emp [] rhs
  in
  let rhs_align lhsf rhs = 
    let align_head_address rhs =
      List.map
        (fun (rhs_e,rhs_p,rhs_h) ->
          match rhs_h with
          | (AsegNE (f,t))::tail ->
             if not (is_same_exp f lhsf)
             then (rhs_e,(mkEq f lhsf)::rhs_p,(mkAsegNE lhsf t)::tail)
             else (rhs_e,rhs_p,rhs_h)
          | (Pointsto (t,v))::tail ->
             if not (is_same_exp t lhsf)
             then (rhs_e,(mkEq t lhsf)::rhs_p,(mkPointsto lhsf v)::tail)
             else (rhs_e,rhs_p,rhs_h)
          | [] -> (rhs_e,rhs_p,rhs_h)
          | _ -> failwith "align_head_address: Invalid input") rhs
    in
    align_head_address rhs
  in
  
  let exists_asegne_with_existential_var rhs lhs_m =
    let rec helper_exists_asegne_with_existential_var head tail =
      match tail with
      | ((rhs_e,rhs_p,rhs_h) as disj)::rest ->         
         ( match rhs_h with
           | (AsegNE (t,m))::tail1 ->
              if contains_evar rhs_e m
              then
                let mc = mkVar (global_get_new_var ()) in
                let rhs1 = head@[mkArrF rhs_e ([mkLt m lhs_m;mkEq mc m]@rhs_p) ((mkAsegNE t mc)::tail1)]@rest in
                let rhs2 = head@[mkArrF rhs_e ((mkLt lhs_m m)::rhs_p) ([mkAsegNE t lhs_m;mkAsegNE lhs_m m]@tail1)]@rest in
                let rhs3 = head@[mkArrF rhs_e ([mkEq m lhs_m]@rhs_p) ((mkAsegNE t lhs_m)::tail1)]@rest in
                Some (mc, rhs1, rhs2,rhs3)
              else helper_exists_asegne_with_existential_var (disj::head) rest
           | _ -> helper_exists_asegne_with_existential_var (disj::head) rest)
      | [] -> None
    in
    helper_exists_asegne_with_existential_var [] rhs
  in
  
  let exists_aseg_with_existential_var rhs =
    let rec helper_exists_aseg_with_existential_var head tail =
      match tail with
      | ((rhs_e,rhs_p,rhs_h) as disj)::rest ->         
         ( match rhs_h with           
           | (Aseg (t,m))::tail1 ->
              if (contains_evar rhs_e t)||(contains_evar rhs_e m)
              then Some ((head@[mkArrF rhs_e ((mkEq t m)::rhs_p) tail1]@rest), (head@[mkArrF rhs_e ((mkLt t m)::rhs_p) ((mkAsegNE t m)::tail1)]@rest))
              else helper_exists_aseg_with_existential_var (disj::head) rest
           | _ -> helper_exists_aseg_with_existential_var (disj::head) rest)           
           (* | _ -> failwith "exists_existential_var: Invalid input") *)
      | [] -> None
    in
    helper_exists_aseg_with_existential_var [] rhs
  in
  
  let exists_aseg rhs =
    let rec helper_exists_aseg head tail =
      match tail with
      | ((rhs_e,rhs_p,rhs_h) as disj)::rest ->         
         (match rhs_h with
          | (Aseg (t,m))::tail1 ->
             Some (((mkEq t m),head@[mkArrF rhs_e rhs_p tail1]@rest),((mkLt t m),head@[mkArrF rhs_e rhs_p ((mkAsegNE t m)::tail1)]@rest))
          | _ -> helper_exists_aseg (disj::head) rest)
      | [] -> None
    in
    helper_exists_aseg [] rhs
  in

  let exists_points_to rhs =
    List.exists
      (fun (_,_,rhs_h) ->
        match rhs_h with
        | h::tail ->
           ( match h with
             | Pointsto _ -> true
             | _ -> false )
        | [] -> false) rhs
  in
      
  let expose_points_to t v rhs =
    List.map
      (fun (rhs_e,rhs_p,rhs_h) ->
        match rhs_h with
        | h::tail ->
           ( match h with
             | Pointsto (nt,nv) -> (rhs_e,[mkEq t nt;mkEq v nv]@rhs_p,tail)
             | AsegNE (nt,nm) -> (rhs_e,[mkEq t nt]@rhs_p,(mkAseg (incOne nt) nm)::tail)
             | _ -> failwith "expose_points_to: Invalid input" )
        | [] -> failwith "expose_points_to: Invalid input")
      rhs
  in

  let rec helper_qf ((lhs_e,lhs_p,lhs_h) as lhs) rhs vset indent =
    let () = print_endline (print_indent indent ((str_arrF lhs)^" |- "^(str_disj_arrF rhs))) in
    match rhs with
    | [(rhs_e,rhs_p,rhs_h)] ->
       ( match lhs_h, rhs_h with
         | (Aseg (f,t))::ltail,_ ->
            print_and_return
                   (mkAnd
                      (helper_qf (mkArrF lhs_e ((mkGte f t)::lhs_p) ltail) rhs vset (indent+1))
                      (helper_qf (mkArrF lhs_e ((mkLt f t)::lhs_p) ((mkAsegNE f t)::ltail)) rhs vset (indent+1)))
                   indent
         | _, (Aseg (rt,rm))::rtail ->
            print_and_return
              (mkAnd
                 (helper_qf (mkArrF lhs_e ([mkGte rt rm]@lhs_p) lhs_h) [(mkArrF rhs_e rhs_p rtail)] vset (indent+1))
                 (helper_qf (mkArrF lhs_e ([mkLt rt rm]@lhs_p) lhs_h) [(mkArrF rhs_e rhs_p ((mkAsegNE rt rm)::rtail))] vset (indent+1)))
              indent
         | lh::ltail, rh::rtail ->
            ( match lh, rh with
              | Aseg (f,t), _ ->
                 failwith "helper_qf: Invalid case"
              | _, Aseg (rt,rm) ->
                 failwith "helper_qf: Invalid case"
              | Pointsto (t,v), _ ->
                 let exposed_pointsto_rhs = expose_points_to t v rhs in
                 helper_qf (mkArrF lhs_e lhs_p ltail) exposed_pointsto_rhs vset (indent+1)
              | AsegNE (t,m), Pointsto (rt,rv) ->
                 helper_qf (mkArrF lhs_e lhs_p ((unfold_AsegNE t m)@ltail)) rhs vset (indent+1)
              | AsegNE (t,m), AsegNE (rt,rm) ->
                 print_and_return
                   (mkAnd
                      (helper_qf (mkArrF lhs_e ([mkLte m rm]@lhs_p) ltail) [(mkArrF rhs_e ([mkEq rt t]@rhs_p) ((mkAseg m rm)::rtail))] vset (indent+1))
                      (helper_qf (mkArrF lhs_e ([mkLt rm m]@lhs_p) ((mkAsegNE rm m)::ltail)) [(mkArrF rhs_e ([mkEq rt t]@rhs_p) rtail)] vset (indent+1)))
                   indent
              | _,_ -> failwith "helper_qf: Invalid case"
            )            
         | [], _ ->
            helper_pure lhs_p rhs indent
         | _, [] -> 
            print_and_return (mkNot (mkAndlst lhs_p)) indent )
       (* (match rhs_h with *)
       (*  | (Aseg (rt,rm))::rtail -> *)
       (*     print_and_return *)
       (*       (mkAnd *)
       (*          (helper_qf (mkArrF lhs_e ([mkEq rt rm]@lhs_p) lhs_h) [(mkArrF rhs_e rhs_p rtail)] vset (indent+1)) *)
       (*          (helper_qf (mkArrF lhs_e ([mkLt rt rm]@lhs_p) lhs_h) [(mkArrF rhs_e rhs_p ((mkAsegNE rt rm)::rtail))] vset (indent+1))) *)
       (*       indent *)
       (*  | _ -> *)
       (*     ( *)
       (*       match lhs_h with *)
       (*       | [] ->        *)
       (*          helper_pure lhs_p rhs indent *)
       (*       | h::tail -> *)
       (*          ( match h with *)
       (*            | Aseg (f,t) -> *)
       (*               print_and_return *)
       (*                 (mkAnd *)
       (*                    (helper_qf (mkArrF lhs_e ((mkEq f t)::lhs_p) tail) rhs vset (indent+1)) *)
       (*                    (helper_qf (mkArrF lhs_e ((mkLt f t)::lhs_p) ((mkAsegNE f t)::tail)) rhs vset (indent+1))) *)
       (*                 indent *)
       (*            | Pointsto (t,v) -> *)
       (*               let exposed_pointsto_rhs = expose_points_to t v rhs in *)
       (*               helper_qf (mkArrF lhs_e lhs_p tail) exposed_pointsto_rhs vset (indent+1) *)
       (*            | AsegNE (t,m) -> *)
       (*               ( match rhs with *)
       (*                 | [rhs_one] -> *)
       (*                    ( let (rhs_e,rhs_p,rhs_h) = rhs_one in *)
       (*                      ( match rhs_h with *)
       (*                        | rh::rtail -> *)
       (*                           ( match rh with *)
       (*                             | Pointsto (t,v) -> *)
       (*                                helper_qf (mkArrF lhs_e lhs_p ((unfold_AsegNE t m)@tail)) rhs vset (indent+1) *)
       (*                             | AsegNE (rt,rm) -> *)
       (*                                print_and_return *)
       (*                                  (mkAnd *)
       (*                                     (helper_qf (mkArrF lhs_e ([mkLte m rm]@lhs_p) tail) [(mkArrF rhs_e ([mkEq rt t]@rhs_p) ((mkAseg m rm)::rtail))] vset (indent+1)) *)
       (*                                     (helper_qf (mkArrF lhs_e ([mkLt rm m]@lhs_p) ((mkAsegNE rm m)::tail)) [(mkArrF rhs_e ([mkEq rt t]@rhs_p) rtail)] vset (indent+1))) *)
       (*                                  indent         *)
       (*                             | _ -> failwith "helper_qf: Invalid RHS") *)
       (*                        | [] -> print_and_return (mkNot (mkAndlst lhs_p)) indent *)
       (*                    )) *)
       (*                 | _ -> failwith "TO BE IMPLEMENTED: disjunctions in RHS" *)
       (*               ) *)
       (*            | _ -> failwith "helper_qf: Invalid LHS" *)
       (*          ) *)
       (*     ) *)
       (* ) *)
    | _ -> failwith "TO BE IMPLEMENTED: disjunctions in RHS"
  in

  let helper_unwrap_exists lhs rhs indent=
    match rhs with
    | [(rhs_e,rhs_p,rhs_h)] ->
       helper_qf lhs rhs rhs_e indent
    | _ -> failwith "helper_unwrap_exists: TO BE IMPLEMENTED"
  in

  let helper_sorted lhs rhs =
    let sorted flst =
      match flst with
      | [(e,p,h)] ->
         [(e,(get_sorted_puref_general h)::p,h)]
      | _ -> failwith "helper_sorted: TO BE IMPLEMENTED"
    in
    (sorted lhs, sorted rhs)
  in
    
  let (lhs,rhs)  = helper_sorted lhs rhs in  
  let () = print_endline (str_disj_arrF lhs) in
  mkAndlst
    (List.map
       (fun item ->
         helper_unwrap_exists item rhs 0) lhs)
;;


let array_entailment_and_print lhs rhs =  
  let ante = cformula_to_arrF lhs in
    (* match cformula_to_arrF lhs with *)
  (*   | [ante] -> [ante] *)
  (*   | _ -> failwith "array_entailment_and_print: Invalid LHS" *)
  (* in *)
  
  let conseq = cformula_to_arrF rhs in    
  let f = array_entailment ante conseq in
  let () = print_endline (!str_pformula f) in
  mkCtxWithPure (simplify f)
  (* if (isSat (mkNot f)) *)
  (* then (false,mkEmptyFailCtx (),[]) *)
  (* else (true,mkEmptySuccCtx (),[]) *)
;;  
  
