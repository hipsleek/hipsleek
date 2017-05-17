#include "xdebug.cppo"
open Arr_biabduction

(* Heap term for arrays *)
type asegPred =
  | Aseg of (Cpure.exp * Cpure.exp)
  | AsegNE of (Cpure.exp * Cpure.exp)
  | Emp
;;

  
(* Not sure whether this is necessary *)
let mkAsegNE f t = AsegNE (f,t);;
let mkAseg f t = Aseg (f,t);;    

(* Formula *)
type arrF =
  (* existential vars * pure formulas * heap formulas *)
  (Cpure.exp list) * (puref list) * (asegPred list)
;;

(* This may increase readability *)
let mkArrF e p h = (e,p,h);;

let str_asegPred aseg =
  match aseg with
  | Aseg (s,e) ->
     (* "Aseg("^(!str_exp b)^","^(!str_exp s)^","^(!str_exp e)^")" *)
     "Aseg("^(!str_exp s)^","^(!str_exp e)^")"
  | AsegNE (s,e)->
     (* "Gap("^(!str_exp b)^","^(!str_exp s)^","^(!str_exp e)^")" *)
     "AsegNE("^(!str_exp s)^","^(!str_exp e)^")"
  | Emp ->
     (* "Elem("^(!str_exp b)^","^(!str_exp s)^")" *)
     "EMP"
;;
  
let str_arrF (e,p,h) =
  (str_list !str_pformula p)^":"^(str_list str_asegPred h)
;;

  
(* Translation from data structure in arr_biabduction.ml *)
let arrPred_to_asegPred arrPred_lst_lst =
  let helper_heap_translation_one h =
    match h with
    | Arr_biabduction.Aseg (b,f,t) -> AsegNE (f,t)
    | _ -> failwith "Invalid input"
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

  
(* lhs: arrF *)
(* rhs: arrF list *)
let array_entailment lhs rhs =
  let helper_pure lhs_p rhs =
    let rec aux_helper_pure lhs_p rhs plst =
      match rhs with
      | (rhs_e,rhs_p,rhs_h)::tail ->
         if (List.exists
               (fun item ->
                 match item with
                 | AsegNE _ | Aseg _ -> true
                 | Emp -> false) rhs_h)
         then aux_helper_pure lhs_p tail plst
         else aux_helper_pure lhs_p tail ((mkExists rhs_e (mkAndlst rhs_p))::plst)
      | [] ->       
         mkImply (mkAndlst lhs_p) (mkOrlst plst)
    in
    aux_helper_pure lhs_p rhs []
  in
  let rhs_aseg_to_AsegNE_and_align lhsf rhs =
    let rec helper_Aseg_to_AsegNE (rhs_e,rhs_p,rhs_h) =
      match rhs_h with
      | h::tail ->
         ( match h with
           | Aseg (f,t) ->
              (mkArrF rhs_e ((mkLt f t)::rhs_p) ((mkAsegNE f t)::tail))::(helper_Aseg_to_AsegNE (rhs_e,(mkEq f t)::rhs_p, tail))
           | AsegNE _ ->
              [(rhs_e,rhs_p, rhs_h)]
           | Emp -> helper_Aseg_to_AsegNE (rhs_e,rhs_p,tail))
      | [] -> []
    in
    let align_head_address rhs =
      List.map
        (fun (rhs_e,rhs_p,rhs_h) ->
          match rhs_h with
          | (AsegNE (f,t))::tail ->
             if not (is_same_exp f lhsf)
             then (rhs_e,(mkEq f lhsf)::rhs_p,(mkAsegNE lhsf t)::tail)
             else (rhs_e,rhs_p,rhs_h)
          | _ -> failwith "align_head_address: Invalid input") rhs
    in
    align_head_address
      (List.fold_left
         (fun r item ->
           (helper_Aseg_to_AsegNE item)@r) [] rhs)
  in
  let exists_existential_var rhs =
    let rec helper_exists_existential_var head tail =
      match tail with
      | ((rhs_e,rhs_p,rhs_h) as disj)::rest ->         
         ( match rhs_h with
           | (AsegNE (t,m))::tail1 ->
              if false          (* TO BE IMPLEMENTED *)
              then Some (disj,head@rest)
              else helper_exists_existential_var (disj::head) rest
           | _ -> failwith "exists_existential_var: Invalid input")
      | [] -> None
    in
    helper_exists_existential_var [] rhs
  in
  let rec helper ((lhs_e,lhs_p,lhs_h) as lhs) rhs =
    let () = print_endline ((str_arrF lhs)^"|-"^(str_list str_arrF rhs)) in
    let helper_match lhs rhs mlst =
      let split_rhs mj rhs =
        List.map
          (fun item ->
            match item with
            | (e,p,(AsegNE (t,m))::tail) ->
            (* (e,p,[mkAsegNE t mj; mkAsegNE mj m]@tail) *)
               (e,p,[mkAseg mj m]@tail)
            | _ -> failwith "split_rhs: Invalid input")
          rhs
      in
      let rec visit head tail flst=
        match tail with
        | ((rhs_e,rhs_p,rhs_h) as h)::tail1 ->
           ( match lhs_h, rhs_h with
             | (AsegNE (t,m))::lhtail,(AsegNE (ti,mi))::rhtail ->
                let newlhs = mkArrF lhs_e ((mkEq mi (mkMin mlst))::lhs_p) ([mkAseg mi m]@lhtail) in
                let newrhs = h::(split_rhs mi (head@tail)) in
                let newf = helper newlhs newrhs in
                visit (h::head) tail1 (newf::flst)
             | _ -> failwith "visit: Invalid input")
        | [] -> flst
      in
      visit [] rhs []
    in
    match lhs_h with
    | [] -> helper_pure lhs_p rhs
    | h::tail ->
       (
         match h with
         | Emp -> helper (mkArrF lhs_e lhs_p tail) rhs
         | Aseg (f,t) ->
            if is_same_exp f t
            then helper (mkArrF lhs_e lhs_p tail) rhs
            else
              mkAnd
                (helper (mkArrF lhs_e ((mkEq f t)::lhs_p) tail) rhs)
                (helper (mkArrF lhs_e ((mkLt f t)::lhs_p) ((mkAsegNE f t)::tail)) rhs)
         | AsegNE (t,m) ->
            let norm_rhs = rhs_aseg_to_AsegNE_and_align t rhs in
            ( match (exists_existential_var norm_rhs) with
              | Some ((n_rhs_e,n_rhs_p, n_rhs_h),rest) ->
                 ( match n_rhs_h with
                   | (AsegNE (nt,nm))::ntail ->
                      let mc = mkVar (global_get_new_var ()) in
                      mkOr
                        (helper (mkArrF n_rhs_e
                                        ([mkLte t mc;mkLte mc m]@lhs_p)
                                        ([mkAsegNE t mc;mkAseg mc m]@tail))
                                ((mkArrF n_rhs_e
                                         ([mkEq nm mc;mkLte nm m;]@n_rhs_p)
                                         ((mkAsegNE nt mc)::ntail))::rest))
                        (helper lhs
                                ((mkArrF n_rhs_e
                                        ((mkLt m nm)::n_rhs_p)
                                        (([mkAsegNE nt m;mkAsegNE m nm]@ntail)))::rest))
                   | _ -> failwith "Invalid output from rhs_aseg_to_AsegNE_and_align" )
              | None ->
                 let (all_m, split_rhs) =
                   List.fold_left
                     (fun (mlst,srhs) item ->
                       match item with
                       | (e,p,(AsegNE (ti,mi))::taili) ->
                          if is_same_exp mi m
                          then (mi::mlst, item::srhs)
                          else
                            (mi::mlst, (mkArrF e p ((mkAseg m mi)::taili))::srhs)
                       | _ -> failwith "AsegNE cannot match")
                     ([],[]) norm_rhs
                 in
                 let f_lhs_min = helper (mkArrF lhs_e (mkEq m (mkMin (m::all_m))::lhs_p) tail) split_rhs in
                 mkAndlst (f_lhs_min::(helper_match lhs norm_rhs all_m)) ))
  in
  helper lhs rhs
;;

let array_entailment_and_print lhs rhs =  
  let ante =
    match cformula_to_arrF lhs with
    | [ante] -> ante
    | _ -> failwith "array_entailment_and_print: Invalid LHS"
  in
  let conseq = cformula_to_arrF rhs in    
  let f = array_entailment ante conseq in
  print_endline (!str_pformula f)
;;
  
       (* let non_emp_rhs_h = List.fold_left *)
    (*                          (fun r item -> *)
    (*                            match item with *)
    (*                            | Emp -> r *)
    (*                            | _ -> *)
    (*    (match rhs_h with *)
    (*     | [] -> helper_pure lhs tail (rhs_p plst) *)
    (*     | h1::tail1 -> *)
    (*        (match h1 with *)
    (*         | Emp -> helper_pure lhs ((rhs_p,tail1)::tail) plst (\* This will be the place why we need call/cc *\) *)
    (*         | AsegNE _ | Aseg _ -> *)
    (*            helper_pure lhs tail plst)) *)
    (* | [] -> *)
    (*    let (lhs_p,_) = lhs in *)
               (*    mkImply (mkAnd lhs_p) (mkOrLst processedlst) *)

       
