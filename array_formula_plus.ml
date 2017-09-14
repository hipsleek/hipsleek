#include "xdebug.cppo"
open Array_formula

(* This version early check pure formula in LHS *)
(* This version handle existential in a wrapping manner *)

type asegPredplus =
  | Aseg_p of (Cpure.spec_var * Cpure.spec_var)
  | AsegNE_p of (Cpure.spec_var * Cpure.spec_var)
  | Pointsto_p of (Cpure.spec_var * Cpure.spec_var)
  | Gap_p of (Cpure.spec_var * Cpure.spec_var)
;;

let str_list_delimeter_raw str lst d emp =
    let helper lst =
      match lst with
      | [] -> emp
      | [h] -> str h
      | h::tail -> List.fold_left (fun r item -> r^d^(str item)) (str h) tail
    in
    helper lst
;;
  
let str_list_delimeter str lst d emp =
  "["^(str_list_delimeter_raw str lst d emp)^"]"
;;
  
let str_asegPredplus aseg =
  match aseg with
  | Aseg_p (s,e) ->
     "Aseg<"^(!str_sv s)^","^(!str_sv e)^">"
  | AsegNE_p (s,e) ->
     "AsegNE<"^(!str_sv s)^","^(!str_sv e)^">"
  | Gap_p (s,e)->
     "Gap<"^("_")^","^(!str_sv s)^","^(!str_sv e)^">"
  | Pointsto_p (s,v) ->
     (!str_sv s)^" -> "^(!str_sv v)
;;

let str_asegPredplus_lst hf =
  str_list_delimeter str_asegPredplus hf "*" "EMP"
;;
let str_asegplusF (pf,hf) =
  (str_list !str_pformula pf)^"/\\"^(str_asegPredplus_lst hf)
;;

  
let mkAsegNE_p a b =
  AsegNE_p (a,b)
;;

let mkAseg_p a b =
  Aseg_p (a,b)
;;

let mkGap_p a b =
  Gap_p (a,b)
;;

let mkPointsto_p t v =
  Pointsto_p (t,v)
;;

let is_same_asegPredplus a1 a2 =
  match a1, a2 with
  | Aseg_p (s1,e1), Aseg_p (s2,e2)
    | AsegNE_p (s1,e1), AsegNE_p (s2,e2)
    | Pointsto_p (s1,e1), Pointsto_p (s2,e2)
    | Gap_p (s1,e1), Gap_p (s2,e2) ->
     (is_same_sv s1 s2) && (is_same_sv e1 e2)
  | _, _ -> false
;;

let compare_list l1 l2 cmp =
  let rec compare_helper l1 l2 =
    match l1, l2 with
    | h1::tail1, h2::tail2 ->
       (cmp h1 h2)&&(compare_helper tail1 tail2)
    | [],h2::tail2 -> false
    | h1::tail1,[] -> false
    | [],[] -> true
  in
  compare_helper l1 l2
;;

let get_disjoint_pure hlst =
  let helper_two a1 a2 =
    match a1, a2 with
    | Aseg_p (s1,e1), Aseg_p (s2,e2)
      | AsegNE_p (s1,e1), AsegNE_p (s2,e2)
      | Aseg_p (s1,e1), AsegNE_p (s2,e2)
      | AsegNE_p (s1,e1), Aseg_p (s2,e2) ->
       mkOr (mkLteSv e1 s2) (mkLteSv e2 s1)
    | Pointsto_p (s1,_), Pointsto_p (s2,_) ->
       mkNeqSv s1 s2
    | Pointsto_p (s1,_), Aseg_p (s2,e2)
      | Pointsto_p (s1,_), AsegNE_p (s2,e2)
      | Aseg_p (s2,e2),Pointsto_p (s1,_)
      | AsegNE_p (s2,e2),Pointsto_p (s1,_) ->
       mkOr (mkLteSv e2 s1) (mkLtSv s1 s2)
    | _,_ ->
       failwith "get_disjoint_pure: TO BE IMPLEMENTED"
  in
  generic_get_disjointness helper_two hlst
;;

let get_segment_pure hlst =
  List.fold_left
    (fun r item ->
      match item with
      | Aseg_p (s,e) ->  (mkLteSv s e)::r
      | AsegNE_p (s,e) -> (mkLtSv s e)::r
      | _ -> r
    )
    [] hlst
;;
                                  

let compare_asegPredplus_lst l1 l2 =
  compare_list l1 l2 is_same_asegPredplus
;;

let compare_sv_lst svlst1 svlst2 =
  compare_list svlst2 svlst2 is_same_sv
;;

let aPredF_to_asegF aPredF =
  let aPred_to_aseg h =
    match h with
    | Aseg (_,a,b) -> mkAseg_p (exp_to_var a) (exp_to_var b)
    | AsegNE (_,a,b) -> mkAsegNE_p (exp_to_var a) (exp_to_var b)
    | Gap (_,a,b) -> mkGap_p (exp_to_var a) (exp_to_var b)
    | Elem (_,t,v) -> mkPointsto_p (exp_to_var t) (exp_to_var v)
  in
  match aPredF with
  | [(evars, pf, hf)] -> (evars,pf,List.map aPred_to_aseg hf)
  | _ -> failwith "aPredF_to_asegF: Disjunctions"
;;
