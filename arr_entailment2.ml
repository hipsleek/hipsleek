#include "xdebug.cppo"
open Arr_biabduction_extend

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
  (* let () = *)
  (*   if not (isValid f) *)
  (*   then *)
  (*     print_endline (print_indent indent ("==> "^(!str_pformula f ))) *)
  (*   else *)
  (*     () *)
  (* in *)
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
            helper tail m ((mkLte lastm t)::flst)
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
          
  let rec helper ((lhs_e,lhs_p,lhs_h) as lhs) rhs indent =    
    (* let () = print_endline (print_indent indent ((str_arrF lhs)^" |- "^(str_disj_arrF rhs))) in *)
    let helper_match lhs rhs mlst indent =
      let split_rhs mj rhs =
        List.map
          (fun item ->
            match item with
            | (e,p,(AsegNE (t,m))::tail) ->
               (* (e,p,[mkAsegNE t mj; mkAsegNE mj m]@tail) *)
               if is_same_exp m mj
               then (e,p,tail)
               else
                 (e,p,[mkAseg mj m]@tail)
            | _ -> failwith "split_rhs: Invalid input")
          rhs
      in
      let rec visit head tail flst=
        match tail with
        | ((rhs_e,rhs_p,rhs_h) as h)::tail1 ->
           ( match lhs_h, rhs_h with
             | (AsegNE (t,m))::lhtail,(AsegNE (ti,mi))::rhtail ->
                (* let newlhs = mkArrF lhs_e ((mkEq mi (mkMin mlst))::lhs_p) ([mkAseg mi m]@lhtail) in *)
                let newlhs = mkArrF lhs_e ((mkMin_raw mi mlst)::lhs_p) ([mkAseg mi m]@lhtail) in
                let newrhs = (split_rhs mi head)@[(mkArrF rhs_e rhs_p rhtail)]@(split_rhs mi tail1) in
                let newf = helper newlhs newrhs indent in
                visit (h::head) tail1 (newf::flst)
             | _ -> failwith "visit: Invalid input")
        | [] -> flst
      in
      visit [] rhs []
    in

    let norm_rhs = rhs in
    (match (exists_aseg_with_existential_var norm_rhs) with
     | Some (rhs1,rhs2) ->
        mkOr (helper lhs rhs1 (indent+1)) (helper lhs rhs2 (indent+1))
     | None ->
        ( match (exists_aseg norm_rhs) with
          | Some ((p1,rhs1),(p2,rhs2)) ->
             mkAnd (helper (lhs_e,p1::lhs_p,lhs_h) rhs1 (indent+1)) (helper (lhs_e,(p2::lhs_p),lhs_h) rhs2 (indent+1))
          | None ->
             ( match lhs_h with
               | [] -> helper_pure lhs_p rhs indent
               | h::tail ->
                  (
                    match h with                    
                    | Aseg (f,t) ->
                       if is_same_exp f t
                       then helper (mkArrF lhs_e lhs_p tail) rhs (indent+1)
                       else
                         print_and_return
                           (mkAnd
                              (helper (mkArrF lhs_e ((mkEq f t)::lhs_p) tail) rhs (indent+1))
                              (helper (mkArrF lhs_e ((mkLt f t)::lhs_p) ((mkAsegNE f t)::tail)) rhs (indent+1)))
                           indent
                    | Pointsto (t,v) ->
                       let norm_rhs = rhs_align t (remove_emp norm_rhs) in
                       let exposed_pointsto_rhs = expose_points_to t v norm_rhs in
                       helper (mkArrF lhs_e lhs_p tail) exposed_pointsto_rhs (indent+1)
                    | AsegNE (t,m) ->
                       if exists_points_to norm_rhs
                       then helper (mkArrF lhs_e lhs_p ((unfold_AsegNE t m)@tail)) norm_rhs (indent+1)
                       else
                         ( match (exists_asegne_with_existential_var norm_rhs m) with
                           | Some (mc,rhs1,rhs2,rhs3) ->                            
                              mkOrlst [(helper (mkArrF lhs_e
                                                       ([mkLt t mc;mkLte mc m]@lhs_p)
                                                       ([mkAsegNE t mc;mkAseg mc m]@tail)) rhs1 (indent+1));
                                       (helper lhs rhs2 (indent+1));
                                       (helper lhs rhs3 (indent+1))]
                           | None ->
                              let norm_rhs = rhs_align t (remove_emp norm_rhs) in
                              let (all_m, split_rhs) =
                                List.fold_left
                                  (fun (mlst,srhs) item ->
                                    match item with
                                    | (e,p,(AsegNE (ti,mi))::taili) ->
                                       (mi::mlst, (mkArrF e p ((mkAseg m mi)::taili))::srhs)
                                    | _ -> failwith "AsegNE cannot match")
                                  ([],[]) norm_rhs
                              in
                              (* let f_lhs_min = helper (mkArrF lhs_e (mkEq m (mkMin (m::all_m))::lhs_p) tail) split_rhs in *)
                              let f_lhs_min = helper (mkArrF lhs_e ((mkMin_raw m (m::all_m))::lhs_p) tail) split_rhs (indent+1) in
                              print_and_return (mkAndlst (f_lhs_min::(helper_match lhs norm_rhs (m::all_m) (indent+1)))) indent)
                    | _ -> failwith "Invalid input when exposing LHS"))))
  in
  let lhs = expand_disj_with_permutation lhs in
  let rhs = expand_disj_with_permutation rhs in
  let () = print_endline (str_disj_arrF lhs) in
  mkAndlst
    (List.map
       (fun item ->
         helper item rhs 0) lhs)
;;


let array_entailment_and_print lhs rhs =  
  let ante = cformula_to_arrF lhs in
    (* match cformula_to_arrF lhs with *)
  (*   | [ante] -> [ante] *)
  (*   | _ -> failwith "array_entailment_and_print: Invalid LHS" *)
  (* in *)
  
  let conseq = cformula_to_arrF rhs in    
  let f = array_entailment ante conseq in
  (* let () = print_endline (!str_pformula f) in *)
  if (isSat (mkNot f))
  then (false,mkEmptyFailCtx (),[])
  else (true,mkEmptySuccCtx (),[])
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

(* If written like this, this k is actually not a continuation *)
(* let rec pass_remove_aseg rhs k = *)
(*   match rhs with *)
(*   | ((rhs_e,rhs_p,rhs_h) as disj)::rhs_tail -> *)
(*      ( match rhs_h with *)
(*        | h::tail -> *)
(*           match h with *)
(*           | AsegNE _ -> *)
(*              pass_remove_aseg rhs_tail (fun x -> k (disj::x) (fun x1 -> x1)) *)
(*           | Aseg (t,m) -> *)
(*              (\* mkAnd (callcc pass... ) (callcc pass...) *\) *)
(*              pass_remove_aseg ((mkArrF rhs_e (mkEq t m) tail)::rhs_tail) *)
(*                               (fun x -> *)
(*                                 k x ( fun x1 -> *)
(*                                       k x1 ( fun x2 -> mkAnd x1 x2 ))) *)
(*           | _ -> failwith "TO BE IMPLEMENTED") *)
(*   | _ -> failwith "TO BE IMPLEMENTED" *)
(* ;; *)
          
                                
(* let rec pass_remove_aseg rhs k = *)
(*   match rhs with *)
(*   | ((rhs_e,rhs_p,rhs_h) as disj)::rhs_tail -> *)
(*      ( match rhs_h with *)
(*        | h::tail -> *)
(*           match h with *)
(*           | AsegNE _ -> *)
(*              pass_remove_aseg rhs_tail (fun x -> k (disj::x) (fun x1 -> x1)) *)
(*           | Aseg (t,m) -> *)
(*              (\* mkAnd (callcc pass... ) (callcc pass...) *\) *)
(*              pass_remove_aseg ((mkArrF rhs_e (mkEq t m) tail)::rhs_tail) *)
(*                               (fun x -> *)
(*                                 k x ( fun x1 -> *)
(*                                       k x1 ( fun x2 -> mkAnd x1 x2 ))) *)
(*           | _ -> failwith "TO BE IMPLEMENTED") *)
(*   | _ -> failwith "TO BE IMPLEMENTED" *)
(* ;; *)
          
                                
  
