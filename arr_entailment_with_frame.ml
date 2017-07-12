#include "xdebug.cppo"
open Arr_biabduction_extend

(* This version early check pure formula in LHS *)
(* This version handle existential in a wrapping manner *)



let mkEqSv a b =
  mkEq (mkVar a) (mkVar b)
;;

let mkNeqSv a b =
  mkNeq (mkVar a) (mkVar b)
;;  

let mkLtSv a b =
  mkLt (mkVar a) (mkVar b)
;;

let mkLteSv a b =
  mkLte (mkVar a) (mkVar b)
;;

let mkGtSv a b =
  mkGt (mkVar a) (mkVar b)
;;  

let mkGteSv a b =
  mkGte (mkVar a) (mkVar b)
;;

type asegPredplus =
  | Aseg_p of (Cpure.spec_var * Cpure.spec_var)
  | AsegNE_p of (Cpure.spec_var * Cpure.spec_var)
  | Pointsto_p of (Cpure.spec_var * Cpure.spec_var)
  | Gap_p of (Cpure.spec_var * Cpure.spec_var)
;;

let str_list_delimeter str lst d emp=
    let helper lst =
      match lst with
      | [] -> emp
      | [h] -> str h
      | h::tail -> List.fold_left (fun r item -> r^d^(str item)) (str h) tail
    in
    "["^helper lst^"]"
;;
  
let str_asegPredplus aseg =
  match aseg with
  | Aseg_p (s,e) ->
     "Aseg("^(!str_sv s)^","^(!str_sv e)^")"
  | AsegNE_p (s,e) ->
     "AsegNE("^(!str_sv s)^","^(!str_sv e)^")"
  | Gap_p (s,e)->
     "Gap("^("_")^","^(!str_sv s)^","^(!str_sv e)^")"
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
  
  
type frameFormula =
  | FBase of (Cpure.formula list * asegPredplus list)
  | FExists of (Cpure.spec_var list * frameFormula)
  | FForall of (Cpure.spec_var list * frameFormula)
  | FAnd of (frameFormula list)
  | FOr of (frameFormula list)
  | FNot of frameFormula
;;

let frameFormula_to_pure f =
  let rec helper f =
    match f with
    | FBase (plst,hlst) ->
       mkAndlst plst       
    | FExists (vset, nf) ->
       if List.length vset = 0
       then helper nf
       else mkExists vset (helper nf)
    | FForall (vset, nf) ->
       if List.length vset = 0
       then helper nf
       else mkForall vset (helper nf)
    | FAnd flst ->
       mkAndlst (List.map helper flst)
    | FOr flst ->
       mkOrlst (List.map helper flst)       
    | FNot nf ->
       mkNot (helper nf)
  in
  simplify (helper f)
;;

let check_validity f =
  let pf = frameFormula_to_pure f in
  isValid pf
;;

let mkFBase (plst,hlst) =
  let pf = [simplify (mkAndlst plst)] in
  FBase (pf,hlst)
;;

let rec str_frameFormula f =  
  match f with
  | FBase (plst,hlst) ->     
     (str_list !str_pformula plst)^"/\\"^(str_asegPredplus_lst hlst)
  | FExists (vset, nf) ->
     if List.length vset = 0
     then str_frameFormula nf
     else "Exists "^(str_list !str_sv vset)^": "^(str_frameFormula nf)
  | FForall (vset, nf) ->
     if List.length vset = 0
     then str_frameFormula nf
     else "Forall "^(str_list !str_sv vset)^": "^(str_frameFormula nf)
  | FAnd flst ->
     str_list_delimeter str_frameFormula flst "/\\" ""
  | FOr flst ->
     str_list_delimeter str_frameFormula flst "\\/" ""  
  | FNot nf ->
     "not("^(str_frameFormula nf)^")"
;;

let array_entailment_classical lhs rhs =
  let mkUsetandVsetprime set vset =
    let uset = List.filter (fun item -> List.exists (fun item1 -> is_same_sv item item1) set)  vset in
    let vsetprime = List.filter (fun item -> not (List.exists (fun item1 -> is_same_sv item item1) uset)) vset in
    (uset,vsetprime)
  in

  let print_and_return f indent =
    let () = print_endline (print_indent indent ("=>"^(str_frameFormula f))) in
    f
  in

  (* input: heap formulas, output: a pure formula with sorted information  *)  
  let get_sorted_puref_general arrPredlst =
    let rec helper lst lastm flst =
      match lst with
      | [] -> mkAndlst flst
      | h::tail ->
         ( match h with
           | AsegNE_p (t,m) ->
              helper tail (mkVar m) ([mkLte lastm (mkVar t);mkLtSv t m]@flst)
           | Pointsto_p (t,v) ->
              helper tail (incOne (mkVar t)) ((mkLte lastm (mkVar t))::flst)
           | Aseg_p (t,m) ->
              mkOr
                (helper tail lastm ((mkEqSv t m)::flst))
                (helper tail (mkVar m) ([mkLte lastm (mkVar t);mkLtSv t m]@flst))
           | _ -> failwith "get_sorted_puref: Invalid input" )
    in

    let rec helper_entry arrPredlst flst =
      match arrPredlst with
      | [] -> mkAndlst flst
      | h::tail ->
         ( match h with
           | AsegNE_p (t,m) ->
              helper tail (mkVar m) [mkLtSv t m]
           | Pointsto_p (t,v) ->
              helper tail (incOne (mkVar t)) []
           | Aseg_p (t,m) ->
              mkOr
                (helper_entry tail ((mkEqSv t m)::flst))
                (helper tail (mkVar m) ((mkLtSv t m)::flst))
           | _ -> failwith "get_sorted_puref: Invalid input" )
    in
    helper_entry arrPredlst []
  in
    
  let rec helper ((lhs_p,lhs_h) as lhs) ((rhs_p,rhs_h) as rhs) vset k indent =
    let () = print_endline (""^(print_indent indent ((str_asegplusF lhs)^" |"^(str_list !str_sv vset)^"- "^(str_asegplusF rhs)))) in
    if not(isSat (mkAndlst (lhs_p@rhs_p)))
    then
      print_and_return (FExists (vset, (FNot (mkFBase (lhs_p,[]))))) indent
    else
      match lhs_h, rhs_h with
      | (Aseg_p (la,lb))::ltail, _ ->
         let (uset,vsetprime) = mkUsetandVsetprime [la;lb] vset in            
         let f1 = helper ((mkEqSv la lb)::lhs_p,ltail) rhs vsetprime k (indent+1) in
         let f2 = helper ((mkLtSv la lb)::lhs_p,(mkAsegNE_p la lb)::ltail) rhs vsetprime k (indent+1) in
         print_and_return (FExists (uset,FAnd [f1;f2])) indent
      | _ ,(Aseg_p (a,b))::rtail ->
         let f1 = helper lhs ((mkEqSv a b)::rhs_p,rtail) vset k (indent+1) in
         let f2 = helper lhs ((mkLtSv a b)::rhs_p,(mkAsegNE_p a b)::rtail) vset k (indent+1) in
         print_and_return (FOr [f1;f2]) indent
      | _, [] ->
         print_and_return (FExists (vset, FOr [FNot (mkFBase (lhs_p,List.rev (lhs_h@k)));mkFBase (rhs_p,[])])) indent
                          
      | [], _ ->
         print_and_return (FExists (vset, (FNot (mkFBase (lhs_p,[]))))) indent
      
      | lh::ltail, rh::rtail ->
       ( match lh, rh with
         | Aseg_p (la,lb), _ ->
            let (uset,vsetprime) = mkUsetandVsetprime [la;lb] vset in            
            let f1 = helper ((mkEqSv la lb)::lhs_p,ltail) rhs vsetprime k (indent+1) in
            let f2 = helper ((mkLtSv la lb)::lhs_p,(mkAsegNE_p la lb)::ltail) rhs vsetprime k (indent+1) in
            print_and_return (FExists (uset,FAnd [f1;f2])) indent
                    
         | _, Aseg_p (ra,rb) ->
            let f1 = helper lhs ((mkEqSv ra rb)::rhs_p,rtail) vset k (indent+1) in
            let f2 = helper lhs ((mkLtSv ra rb)::rhs_p,(mkAsegNE_p ra rb)::rtail) vset k (indent+1) in
            print_and_return (FOr [f1;f2]) indent
                
         | Pointsto_p (ls,lv),Pointsto_p (rs,rv) ->
            let (uset,vsetprime) = mkUsetandVsetprime [ls;rs] vset in            
            let f1 = helper ((mkEqSv ls rs)::lhs_p, ltail) ((mkEqSv lv rv)::rhs_p, rtail) vsetprime k (indent+1) in
            let f2 = FExists (vsetprime, mkFBase ([mkNot (mkAndlst ((mkNeqSv ls rs)::lhs_p))],[])) in
            print_and_return (FExists (uset, FAnd [f1;f2])) indent

         | AsegNE_p (la,lb), AsegNE_p (ra,rb) ->
            (* let (uset,vsetprime) = mkUsetandVsetprime [lb;rb] vset in             *)
            if is_same_sv la ra
            then
              let (uset,vsetprime) = mkUsetandVsetprime [lb;rb] vset in
              let f1 = helper ((mkGtSv rb lb)::lhs_p,ltail) (rhs_p, (mkAsegNE_p lb rb)::rtail) vsetprime k (indent+1) in
              let f2 = helper ((mkLteSv rb lb)::lhs_p,(mkAseg_p rb lb)::ltail) (rhs_p, rtail) vsetprime k (indent+1) in
              print_and_return (FExists (uset, FAnd [f1;f2])) indent
            else
              let (uset,vsetprime) = mkUsetandVsetprime [la;ra] vset in
              let f1 = helper ((mkEqSv la ra)::lhs_p, lhs_h) (rhs_p, (mkAsegNE_p la rb)::rtail) vsetprime k (indent+1) in
              let f2 = FExists (vsetprime, mkFBase ([mkNot (mkAndlst ((mkNeqSv la ra)::lhs_p))],[])) in
              print_and_return (FExists (uset, FAnd [f1;f2;(FExists (vsetprime, (mkFBase ([(mkNot (mkAndlst ((mkGtSv la ra)::lhs_p)))],[])))) ])) indent
                      
         (* | AsegNE_p (la,lb), Gap_p (ra,rb) ->   *)
         (* if is_same_sv la ra *)
         (* then *)
         (*   let (uset,vsetprime) = mkUsetandVsetprime [lb;rb] vset in             *)
         (*   let f1 = helper ((mkLtSv lb rb)::lhs_p, ltail) (rhs_p, rtail) vsetprime (lh::k) (indent+1) in *)
         (*   let f2 = helper ((mkGteSv lb rb)::lhs_p, (Aseg_p (rb,lb))::ltail) (rhs_p, rtail) vsetprime ((mkAsegNE_p la rb)::k) (indent+1) in *)
         (*   print_and_return (FExists (uset, FAnd [f1;f2])) indent *)
         (* else *)
         (*   failwith "AsegNE v.s Gap: Not aligned" *)

         | AsegNE_p (la,lb), Pointsto_p (rs,rv) ->
            let (uset,vsetprime) = mkUsetandVsetprime [la] vset in
            let fresh_c = global_get_new_var () in
            let fresh_u = global_get_new_var () in
            let f = helper ((mkEq (mkVar fresh_c) (incOne (mkVar la)))::lhs_p,([mkPointsto_p la fresh_u; mkAseg_p fresh_c lb]@ltail))
                           rhs vsetprime k (indent+1) in
            print_and_return (FExists (uset,(FForall ([fresh_c;fresh_u],f)))) indent

         | Pointsto_p (ls,lv),AsegNE_p (ra,rb) ->
            let fresh_c = global_get_new_var () in
            let fresh_u = global_get_new_var () in
            print_and_return (helper lhs
                                     ((mkEq (mkVar fresh_c) (incOne (mkVar ra)))::rhs_p,([mkPointsto_p ra fresh_u; mkAseg_p fresh_c rb]@ltail))
                                     ([fresh_c;fresh_u]@vset) k (indent+1)) indent
         | _, Gap_p _ -> failwith "Gap_p"
         | Gap_p _,_ -> failwith "Gap_p"
       )
  in
  let helper_entry (lhs_e,lhs_p,lhs_h) (rhs_e,rhs_p,rhs_h) =
    FForall (lhs_e,helper ((get_sorted_puref_general lhs_h)::lhs_p,lhs_h) ((get_sorted_puref_general rhs_h)::rhs_p,rhs_h) rhs_e [] 0)
  in
  let transAnte = new arrPredTransformer_orig lhs in
  let transConseq = new arrPredTransformer_orig rhs in
  let f = helper_entry (aPredF_to_asegF (transAnte#formula_to_general_formula)) (aPredF_to_asegF (transConseq#formula_to_general_formula)) in
  let () = print_endline (str_frameFormula f) in
  f
;;
  
let array_entailment_frame lhs rhs =
  let mkUsetandVsetprime set vset =
    let uset = List.filter (fun item -> List.exists (fun item1 -> is_same_sv item item1) set)  vset in
    let vsetprime = List.filter (fun item -> not (List.exists (fun item1 -> is_same_sv item item1) uset)) vset in
    (uset,vsetprime)
  in

  let print_and_return f indent =
    let () = print_endline (print_indent indent ("=>"^(str_frameFormula f))) in
    f
  in

  (* input: heap formulas, output: a pure formula with sorted information  *)  
  let get_sorted_puref_general arrPredlst =
    let rec helper lst lastm flst =
      match lst with
      | [] -> mkAndlst flst
      | h::tail ->
         ( match h with
           | AsegNE_p (t,m) ->
              helper tail (mkVar m) ([mkLte lastm (mkVar t);mkLtSv t m]@flst)
           | Pointsto_p (t,v) ->
              helper tail (incOne (mkVar t)) ((mkLte lastm (mkVar t))::flst)
           | Aseg_p (t,m) ->
              mkOr
                (helper tail lastm ((mkEqSv t m)::flst))
                (helper tail (mkVar m) ([mkLte lastm (mkVar t);mkLtSv t m]@flst))
           | _ -> failwith "get_sorted_puref: Invalid input" )
    in

    let rec helper_entry arrPredlst flst =
      match arrPredlst with
      | [] -> mkAndlst flst
      | h::tail ->
         ( match h with
           | AsegNE_p (t,m) ->
              helper tail (mkVar m) [mkLtSv t m]
           | Pointsto_p (t,v) ->
              helper tail (incOne (mkVar t)) []
           | Aseg_p (t,m) ->
              mkOr
                (helper_entry tail ((mkEqSv t m)::flst))
                (helper tail (mkVar m) ((mkLtSv t m)::flst))
           | _ -> failwith "get_sorted_puref: Invalid input" )
    in
    helper_entry arrPredlst []
  in
    
  let rec helper ((lhs_p,lhs_h) as lhs) ((rhs_p,rhs_h) as rhs) vset k indent =
    let () = print_endline (""^(print_indent indent ((str_asegplusF lhs)^" |"^(str_list !str_sv vset)^"- "^(str_asegplusF rhs)))) in
    if not(isSat (mkAndlst (lhs_p@rhs_p)))
    then
      print_and_return (FExists (vset, (FNot (mkFBase (lhs_p,[]))))) indent
    else
      match lhs_h, rhs_h with
      | (Aseg_p (la,lb))::ltail, _ ->
         let (uset,vsetprime) = mkUsetandVsetprime [la;lb] vset in            
         let f1 = helper ((mkEqSv la lb)::lhs_p,ltail) rhs vsetprime k (indent+1) in
         let f2 = helper ((mkLtSv la lb)::lhs_p,(mkAsegNE_p la lb)::ltail) rhs vsetprime k (indent+1) in
         print_and_return (FExists (uset,FAnd [f1;f2])) indent
      | _ ,(Aseg_p (a,b))::rtail ->
         let f1 = helper lhs ((mkEqSv a b)::rhs_p,rtail) vset k (indent+1) in
         let f2 = helper lhs ((mkLtSv a b)::rhs_p,(mkAsegNE_p a b)::rtail) vset k (indent+1) in
         print_and_return (FOr [f1;f2]) indent
      | _, [] ->
         print_and_return (FExists (vset, FOr [FNot (mkFBase (lhs_p,List.rev (lhs_h@k)));mkFBase (rhs_p,[])])) indent
                          
      | [], _ ->
         print_and_return (FExists (vset, (FNot (mkFBase (lhs_p,[]))))) indent
      
      | lh::ltail, rh::rtail ->
       ( match lh, rh with
         | Aseg_p (la,lb), _ ->
            let (uset,vsetprime) = mkUsetandVsetprime [la;lb] vset in            
            let f1 = helper ((mkEqSv la lb)::lhs_p,ltail) rhs vsetprime k (indent+1) in
            let f2 = helper ((mkLtSv la lb)::lhs_p,(mkAsegNE_p la lb)::ltail) rhs vsetprime k (indent+1) in
            print_and_return (FExists (uset,FAnd [f1;f2])) indent
                    
         | _, Aseg_p (ra,rb) ->
            let f1 = helper lhs ((mkEqSv ra rb)::rhs_p,rtail) vset k (indent+1) in
            let f2 = helper lhs ((mkLtSv ra rb)::rhs_p,(mkAsegNE_p ra rb)::rtail) vset k (indent+1) in
            print_and_return (FOr [f1;f2]) indent
                
         | Pointsto_p (ls,lv),Pointsto_p (rs,rv) ->
            let (uset,vsetprime) = mkUsetandVsetprime [ls;rs] vset in            
            let f1 = helper ((mkEqSv ls rs)::lhs_p, ltail) ((mkEqSv lv rv)::rhs_p, rtail) vsetprime k (indent+1) in
            let f2 = helper ((mkLtSv ls rs)::lhs_p, ltail) rhs vsetprime (lh::k) (indent+1) in
            let f3 = helper ((mkGtSv ls rs)::lhs_p, ltail) ([mkFalse ()],[]) vsetprime k (indent+1) in
            print_and_return (FExists (uset, FAnd [f1;f2;f3])) indent

         | AsegNE_p (la,lb), AsegNE_p (ra,rb) ->
            let (uset,vsetprime) = mkUsetandVsetprime [lb;rb] vset in            
            if is_same_sv la ra
            then
              let f1 = helper ((mkGtSv rb lb)::lhs_p,ltail) (rhs_p, (mkAsegNE_p lb rb)::rtail) vsetprime k (indent+1) in
              let f2 = helper ((mkLteSv rb lb)::lhs_p,(mkAseg_p rb lb)::ltail) (rhs_p, rtail) vsetprime k (indent+1) in
              print_and_return (FExists (uset, FAnd [f1;f2])) indent
            else
              let f1 = helper ((mkEqSv la ra)::lhs_p, lhs_h) (rhs_p, (mkAsegNE_p la rb)::rtail) vsetprime k (indent+1) in
              let f2 = helper ((mkLtSv la ra)::lhs_p, lhs_h) (rhs_p, (mkGap_p la ra)::rhs_h) vsetprime k (indent+1) in
              print_and_return (FExists (uset, FAnd [f1;f2;(FExists (vsetprime, (mkFBase ([(mkNot (mkAndlst ((mkGtSv la ra)::lhs_p)))],[])))) ])) indent
                      
         | AsegNE_p (la,lb), Gap_p (ra,rb) ->
            if is_same_sv la ra
            then
              let (uset,vsetprime) = mkUsetandVsetprime [lb;rb] vset in            
              let f1 = helper ((mkLtSv lb rb)::lhs_p, ltail) (rhs_p, rtail) vsetprime (lh::k) (indent+1) in
              let f2 = helper ((mkGteSv lb rb)::lhs_p, (Aseg_p (rb,lb))::ltail) (rhs_p, rtail) vsetprime ((mkAsegNE_p la rb)::k) (indent+1) in
              print_and_return (FExists (uset, FAnd [f1;f2])) indent
            else
              failwith "AsegNE v.s Gap: Not aligned"

         | AsegNE_p (la,lb), Pointsto_p (rs,rv) ->
            let fresh_c = global_get_new_var () in
            let fresh_u = global_get_new_var () in
            let f = helper ((mkEq (mkVar fresh_c) (incOne (mkVar la)))::lhs_p,([mkPointsto_p la fresh_u; mkAseg_p fresh_c lb]@ltail))
                           rhs vset k (indent+1) in
            print_and_return (FForall ([fresh_c;fresh_u],f)) indent

         | Pointsto_p (ls,lv),AsegNE_p (ra,rb) ->
            let fresh_c = global_get_new_var () in
            let fresh_u = global_get_new_var () in
            print_and_return (helper lhs
                                     ((mkEq (mkVar fresh_c) (incOne (mkVar ra)))::rhs_p,([mkPointsto_p ra fresh_u; mkAseg_p fresh_c rb]@ltail))
                                     ([fresh_c;fresh_u]@vset) k (indent+1)) indent
         | _, Gap_p _ ->
            print_and_return (helper lhs (rhs_p,rtail) vset k (indent+1)) indent
         | Gap_p _,_ -> failwith "Gap_p in LHS"
       )
  in
  let helper_entry (lhs_e,lhs_p,lhs_h) (rhs_e,rhs_p,rhs_h) =
    FForall (lhs_e,helper ((get_sorted_puref_general lhs_h)::lhs_p,lhs_h) ((get_sorted_puref_general rhs_h)::rhs_p,rhs_h) rhs_e [] 0)
  in
  let transAnte = new arrPredTransformer_orig lhs in
  let transConseq = new arrPredTransformer_orig rhs in
  let f = helper_entry (aPredF_to_asegF (transAnte#formula_to_general_formula)) (aPredF_to_asegF (transConseq#formula_to_general_formula)) in
  let () = print_endline (str_frameFormula f) in
  f
;;

let array_entailment_classical_interface lhs rhs =
  let f = array_entailment_classical lhs rhs in
  (* let () = print_endline ("Frame: "^(str_frameFormula f)) in *)
  if check_validity f
  then
    (true,mkEmptySuccCtx (),[])
  else
    (false,mkEmptyFailCtx (),[])
;;

let array_entailment_classical_infer_interface lhs rhs =
  let f = frameFormula_to_pure (array_entailment_classical lhs rhs) in
  (true,mkCtxWithPure (simplify f),[])
;;
  
let array_entailment_frame_interface lhs rhs =
  let f = array_entailment_frame lhs rhs in
  let () = print_endline ("Frame: "^(str_frameFormula f)) in
  if check_validity f
  then
    mkEmptySuccCtx ()
  else
    mkEmptyFailCtx ()
;;


let array_entailment_biabduction lhs rhs =
  let mkUsetandVsetprime set vset =
    let uset = List.filter (fun item -> List.exists (fun item1 -> is_same_sv item item1) set)  vset in
    let vsetprime = List.filter (fun item -> not (List.exists (fun item1 -> is_same_sv item item1) uset)) vset in
    (uset,vsetprime)
  in

  let print_and_return f indent =
    let () = print_endline (print_indent indent ("=>"^(str_frameFormula f))) in
    f
  in

  (* input: heap formulas, output: a pure formula with sorted information  *)  
  let get_sorted_puref_general arrPredlst =
    let rec helper lst lastm flst =
      match lst with
      | [] -> mkAndlst flst
      | h::tail ->
         ( match h with
           | AsegNE_p (t,m) ->
              helper tail (mkVar m) ([mkLte lastm (mkVar t);mkLtSv t m]@flst)
           | Pointsto_p (t,v) ->
              helper tail (incOne (mkVar t)) ((mkLte lastm (mkVar t))::flst)
           | Aseg_p (t,m) ->
              mkOr
                (helper tail lastm ((mkEqSv t m)::flst))
                (helper tail (mkVar m) ([mkLte lastm (mkVar t);mkLtSv t m]@flst))
           | _ -> failwith "get_sorted_puref: Invalid input" )
    in

    let rec helper_entry arrPredlst flst =
      match arrPredlst with
      | [] -> mkAndlst flst
      | h::tail ->
         ( match h with
           | AsegNE_p (t,m) ->
              helper tail (mkVar m) [mkLtSv t m]
           | Pointsto_p (t,v) ->
              helper tail (incOne (mkVar t)) []
           | Aseg_p (t,m) ->
              mkOr
                (helper_entry tail ((mkEqSv t m)::flst))
                (helper tail (mkVar m) ((mkLtSv t m)::flst))
           | _ -> failwith "get_sorted_puref: Invalid input" )
    in
    helper_entry arrPredlst []
  in
  
  let rec helper ((lhs_p,lhs_h) as lhs) ((rhs_p,rhs_h) as rhs) vset k indent =
    let () = print_endline (""^(print_indent indent ((str_asegplusF lhs)^" |- "^(str_asegplusF rhs)))) in
    if not(isSat (mkAndlst (lhs_p@rhs_p)))
    then
      print_and_return (FExists (vset, (FNot (mkFBase (lhs_p,[]))))) indent
    else
      match lhs_h, rhs_h with
      | (Aseg_p (la,lb))::ltail, _ ->
         let (uset,vsetprime) = mkUsetandVsetprime [la;lb] vset in            
         let f1 = helper ((mkEqSv la lb)::lhs_p,ltail) rhs vsetprime k (indent+1) in
         let f2 = helper ((mkLtSv la lb)::lhs_p,(mkAsegNE_p la lb)::ltail) rhs vsetprime k (indent+1) in
         print_and_return (FExists (uset,FAnd [f1;f2])) indent
      | _ ,(Aseg_p (a,b))::rtail ->
         let f1 = helper lhs ((mkEqSv a b)::rhs_p,rtail) vset k (indent+1) in
         let f2 = helper lhs ((mkLtSv a b)::rhs_p,(mkAsegNE_p a b)::rtail) vset k (indent+1) in
         print_and_return (FOr [f1;f2]) indent
      | _, [] ->
         print_and_return (FExists (vset, FOr [FNot (mkFBase (lhs_p,List.rev (lhs_h@k)));mkFBase (rhs_p,[])])) indent
                          
      | [], _ ->
         print_and_return (FExists (vset, (FNot (mkFBase (lhs_p,[]))))) indent
                          
      | lh::ltail, rh::rtail ->
         ( match lh, rh with
           | Aseg_p (la,lb), _ ->
              let (uset,vsetprime) = mkUsetandVsetprime [la;lb] vset in            
              let f1 = helper ((mkEqSv la lb)::lhs_p,ltail) rhs vsetprime k (indent+1) in
              let f2 = helper ((mkLtSv la lb)::lhs_p,(mkAsegNE_p la lb)::ltail) rhs vsetprime k (indent+1) in
              print_and_return (FExists (uset,FAnd [f1;f2])) indent
                               
           | _, Aseg_p (ra,rb) ->
              let f1 = helper lhs ((mkEqSv ra rb)::rhs_p,rtail) vset k (indent+1) in
              let f2 = helper lhs ((mkLtSv ra rb)::rhs_p,(mkAsegNE_p ra rb)::rtail) vset k (indent+1) in
              print_and_return (FOr [f1;f2]) indent
                               
           | Pointsto_p (ls,lv),Pointsto_p (rs,rv) ->
              let (uset,vsetprime) = mkUsetandVsetprime [ls;rs] vset in            
              let f1 = helper ((mkEqSv ls rs)::lhs_p, ltail) ((mkEqSv lv rv)::rhs_p, rtail) vsetprime k (indent+1) in
              let f2 = helper ((mkLtSv ls rs)::lhs_p, ltail) rhs vsetprime (lh::k) (indent+1) in
              let f3 = helper ((mkGtSv ls rs)::lhs_p, ltail) ([mkFalse ()],[]) vsetprime k (indent+1) in
              print_and_return (FExists (uset, FAnd [f1;f2;f3])) indent

           | AsegNE_p (la,lb), AsegNE_p (ra,rb) ->
              let (uset,vsetprime) = mkUsetandVsetprime [lb;rb] vset in            
              if is_same_sv la ra
              then
                let f1 = helper ((mkGtSv rb lb)::lhs_p,ltail) (rhs_p, (mkAsegNE_p lb rb)::rtail) vsetprime k (indent+1) in
                let f2 = helper ((mkLteSv rb lb)::lhs_p,(mkAseg_p rb lb)::ltail) (rhs_p, rtail) vsetprime k (indent+1) in
                print_and_return (FExists (uset, FAnd [f1;f2])) indent
              else
                let f1 = helper ((mkEqSv la ra)::lhs_p, lhs_h) (rhs_p, (mkAsegNE_p la rb)::rtail) vsetprime k (indent+1) in
                let f2 = helper ((mkLtSv la ra)::lhs_p, lhs_h) (rhs_p, (mkGap_p la ra)::rhs_h) vsetprime k (indent+1) in
                print_and_return (FExists (uset, FAnd [f1;f2;(FExists (vsetprime, (mkFBase ([(mkNot (mkAndlst ((mkGtSv la ra)::lhs_p)))],[])))) ])) indent
                                 
           | AsegNE_p (la,lb), Gap_p (ra,rb) ->
              if is_same_sv la ra
              then
                let (uset,vsetprime) = mkUsetandVsetprime [lb;rb] vset in            
                let f1 = helper ((mkLtSv lb rb)::lhs_p, ltail) (rhs_p, rtail) vsetprime (lh::k) (indent+1) in
                let f2 = helper ((mkGteSv lb rb)::lhs_p, (Aseg_p (rb,lb))::ltail) (rhs_p, rtail) vsetprime ((mkAsegNE_p la rb)::k) (indent+1) in
                print_and_return (FExists (uset, FAnd [f1;f2])) indent
              else
                failwith "AsegNE v.s Gap: Not aligned"

           | AsegNE_p (la,lb), Pointsto_p (rs,rv) ->
              let fresh_c = global_get_new_var () in
              let fresh_u = global_get_new_var () in
              let f = helper ((mkEq (mkVar fresh_c) (incOne (mkVar la)))::lhs_p,([mkPointsto_p la fresh_u; mkAseg_p fresh_c lb]@ltail))
                             rhs vset k (indent+1) in
              print_and_return (FForall ([fresh_c;fresh_u],f)) indent

           | Pointsto_p (ls,lv),AsegNE_p (ra,rb) ->
              let fresh_c = global_get_new_var () in
              let fresh_u = global_get_new_var () in
              print_and_return (helper lhs
                                       ((mkEq (mkVar fresh_c) (incOne (mkVar ra)))::rhs_p,([mkPointsto_p ra fresh_u; mkAseg_p fresh_c rb]@ltail))
                                       ([fresh_c;fresh_u]@vset) k (indent+1)) indent
           | _, Gap_p _ ->
              print_and_return (helper lhs (rhs_p,rtail) vset k (indent+1)) indent
           | Gap_p _,_ -> failwith "Gap_p in LHS"
         )
  in
  let helper_entry (lhs_e,lhs_p,lhs_h) (rhs_e,rhs_p,rhs_h) =
    FForall (lhs_e,helper ((get_sorted_puref_general lhs_h)::lhs_p,lhs_h) ((get_sorted_puref_general rhs_h)::rhs_p,rhs_h) rhs_e [] 0)
  in
  let transAnte = new arrPredTransformer_orig lhs in
  let transConseq = new arrPredTransformer_orig rhs in
  let f = helper_entry (aPredF_to_asegF (transAnte#formula_to_general_formula)) (aPredF_to_asegF (transConseq#formula_to_general_formula)) in
  let () = print_endline (str_frameFormula f) in
  f
;;
  
                                

            
(* Heap term for arrays *)
type asegPred =
  | Aseg of (Cpure.exp * Cpure.exp)
  | AsegNE of (Cpure.exp * Cpure.exp)
  | Pointsto of (Cpure.exp * Cpure.exp)
  | Emp
;;



type frame =
  | False
  | Frame of (Cpure.formula * asegPred list)
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
  let newvar = global_get_new_var () in
  (newvar,[mkPointsto t (mkVar newvar);mkAseg (incOne t) m])
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

let str_frame frame =
  match frame with
  | False -> "False"
  | Frame (p, hlst) -> ("Frame: "^(!str_pformula p)^"/\\"^(str_list str_asegPred hlst))
;;  
  
let str_arrF (e,p,h) =
  (* (str_list !str_pformula p)^":"^(str_list str_asegPred h) *)
  (str_list !str_exp (List.map mkVar e))^(str_list !str_pformula p)^":"^(str_list str_asegPred h)
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

let asegPred_to_h_formula arr =
  let bind_exp_to_var exp =
    match exp with
    | Cpure.Var (sv,_) -> (sv,[],[])                 
    | _ ->
       let newv = global_get_new_var () in
       (newv,[mkEq (mkVar newv) exp],[newv])
  in
  let one_arrPred_to_h_formula p =
    let basePtr = mkSV "base" in
    match p with
    | Aseg (s,e) ->
       let (news,sf_lst,svlst) = bind_exp_to_var s in
       let (newe,se_lst,evlst) = bind_exp_to_var e in
       (mkViewNode basePtr "Aseg" [news;newe], sf_lst@se_lst,svlst@evlst)
    | AsegNE (s,e) ->
       let (news,sf_lst,svlst) = bind_exp_to_var s in
       let (newe,se_lst,evlst) = bind_exp_to_var e in
       (mkViewNode basePtr "AsegNE" [news;newe], sf_lst@se_lst,svlst@evlst)    
    | Pointsto (s,v) ->
       let (news,sf_lst,svlst) = bind_exp_to_var s in
       let (newv,vf_lst,vvlst) = bind_exp_to_var v in     
       (mkViewNode  basePtr "Elem" [news;newv], sf_lst@vf_lst,svlst@vvlst)
    | _ -> failwith "asegPred_to_h_formula: TO BE IMPLEMENTED"
  in
  let construct_h_formula plst =
    match (List.map (fun item -> one_arrPred_to_h_formula item) plst) with
    | h::tail -> List.fold_left (fun (h,p,v) (itemh,itemp,itemv) -> (mkStarH itemh h, itemp@p,itemv@v)) h tail
    | [] -> (HEmp,[],[])
  in
  construct_h_formula arr
;;
  

let print_and_return f indent =
  let sf = pairwisecheck (simplify f) in
  let () =
    if true(* not (isValid f) *)
    then
      let () =
        if !Globals.array_verbose (* --verbose-arr *)
        then print_endline (print_indent indent ("=o> "^(!str_pformula f )))
        else ()
      in
      print_endline (print_indent indent ("==> "^(!str_pformula sf )))
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
         else aux_helper_pure lhs_p tail ((mkAndlst rhs_p)::plst)
      | [] ->       
         mkImply (mkAndlst lhs_p) (mkOrlst plst)
    in
    let f = aux_helper_pure lhs_p rhs [] in
    print_and_return f indent
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
            if not( !Globals.array_proof_search && (List.exists (fun v -> (exp_contains_var rt v) || (exp_contains_var rm v)) vset))
            then
              print_and_return
                (mkAnd
                   (helper_qf (mkArrF lhs_e ([mkGte rt rm]@lhs_p) lhs_h) [(mkArrF rhs_e rhs_p rtail)] vset (indent+1))
                   (helper_qf (mkArrF lhs_e ([mkLt rt rm]@lhs_p) lhs_h) [(mkArrF rhs_e rhs_p ((mkAsegNE rt rm)::rtail))] vset (indent+1)))
                indent
            else
              print_and_return
                (mkOr
                   (helper_qf (mkArrF lhs_e lhs_p lhs_h) [(mkArrF rhs_e ([mkGte rt rm]@rhs_p) rtail)] vset (indent+1))
                   (helper_qf (mkArrF lhs_e lhs_p lhs_h) [(mkArrF rhs_e ([mkLt rt rm]@rhs_p) ((mkAsegNE rt rm)::rtail))] vset (indent+1)))
                indent
         | lh::ltail, rh::rtail ->
            ( match lh, rh with
              | Aseg (f,t), _ ->
                 failwith "helper_qf: Invalid case"
              | _, Aseg (rt,rm) ->
                 failwith "helper_qf: Invalid case"
              | Pointsto (t,v), AsegNE (rt,rm) ->
                 let (newvar,newpreds) = unfold_AsegNE rt rm in
                 mkExists [newvar] (helper_qf lhs [(mkArrF rhs_e rhs_p (newpreds@rtail))] (newvar::vset) (indent+1))
              | Pointsto (t,v), Pointsto (rt,rv) ->
                 helper_qf (mkArrF lhs_e lhs_p ltail) [(mkArrF rhs_e ([mkEq t rt; mkEq v rv]@rhs_p) rtail)] vset (indent+1)
              | AsegNE (t,m), Pointsto (rt,rv) ->
                 let (newvar,newpreds) = unfold_AsegNE t m in
                 helper_qf (mkArrF lhs_e lhs_p (newpreds@ltail)) rhs (newvar::vset) (indent+1)
              | AsegNE (t,m), AsegNE (rt,rm) ->
                 if not(!Globals.array_proof_search && (List.exists (fun v -> (exp_contains_var rt v) || (exp_contains_var rm v)) vset))
                 then
                   print_and_return
                     (mkAnd
                        (helper_qf (mkArrF lhs_e ([mkLte m rm]@lhs_p) ltail) [(mkArrF rhs_e ([mkEq rt t]@rhs_p) ((mkAseg m rm)::rtail))] vset (indent+1))
                        (helper_qf (mkArrF lhs_e ([mkLt rm m]@lhs_p) ((mkAsegNE rm m)::ltail)) [(mkArrF rhs_e ([mkEq rt t]@rhs_p) rtail)] vset (indent+1)))
                     indent
                 else
                   print_and_return
                     (mkOr
                        (helper_qf (mkArrF lhs_e lhs_p ltail) [(mkArrF rhs_e ([mkLte m rm;mkEq rt t]@rhs_p) ((mkAseg m rm)::rtail))] vset (indent+1))
                        (helper_qf (mkArrF lhs_e lhs_p ((mkAsegNE rm m)::ltail)) [(mkArrF rhs_e ([mkLt rm m;mkEq rt t]@rhs_p) rtail)] vset (indent+1)))
                     indent
              | _,_ -> failwith "helper_qf: Invalid case"
            )            
         | [], _ ->
            helper_pure lhs_p rhs indent
         | _, [] -> 
            print_and_return (mkNot (mkAndlst lhs_p)) indent )
    | _ -> failwith "TO BE IMPLEMENTED: disjunctions in RHS"
  in

  let helper_unwrap_exists ((_,lhs_p,_) as lhs) rhs indent=
    match rhs with
    | [(rhs_e,rhs_p,rhs_h)] ->
       let f = (mkExists rhs_e (helper_qf lhs rhs rhs_e indent)) in
       let old_vars = get_fv_pure (mkAndlst lhs_p) in
       let new_vars = get_fv_pure f in
       let vars = List.filter (fun v -> not (List.exists (fun nv -> is_same_sv nv v) old_vars)) new_vars in
       print_and_return  (mkForall vars f) indent
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
  (* let () = print_endline (str_disj_arrF lhs) in *)
  mkAndlst
    (List.map
       (fun item ->
         helper_unwrap_exists item rhs 0) lhs)
;;

let array_entailment_with_frame lhs rhs =
  let andFrame frame1 frame2 =
    match frame1, frame2 with
    | None,_ | _,None -> None
    | Some f1, Some f2 ->
       ( match f1, f2 with
         | f,False | False,f -> Some f
         | _,_ -> failwith "andFrame: Both frames are not false")
  in

  let addFrame frame nf =
    match frame with
    | None -> None
    | Some f ->
       ( match f with
         | False -> Some False
         | Frame (fp,fh) ->
            Some (Frame (fp, nf::fh)))
  in
  
  (* Inferring frame only for quantifier-free cases *)
  let rec helper_qf_with_frame ((lhs_e,lhs_p,lhs_h) as lhs) ((rhs_e,rhs_p,rhs_h) as rhs) vset indent =
    let () = print_endline ("frame"^(print_indent indent ((str_arrF lhs)^" |- "^(str_arrF rhs)))) in
    if isValid (mkImply (mkAndlst lhs_p) (mkFalse ()))
    then Some False
    else
      match lhs_h, rhs_h with
      | (Aseg (f,t))::ltail, _ ->
         (andFrame
            (helper_qf_with_frame (mkArrF lhs_e ((mkGte f t)::lhs_p) ltail) rhs vset (indent+1))
            (helper_qf_with_frame (mkArrF lhs_e ((mkLt f t)::lhs_p) ((mkAsegNE f t)::ltail)) rhs vset (indent+1)))
      | _, (Aseg (rt,rm))::rtail ->
         (andFrame
            (helper_qf_with_frame (mkArrF lhs_e ([mkGte rt rm]@lhs_p) lhs_h) (mkArrF rhs_e rhs_p rtail) vset (indent+1))
            (helper_qf_with_frame (mkArrF lhs_e ([mkLt rt rm]@lhs_p) lhs_h) (mkArrF rhs_e rhs_p ((mkAsegNE rt rm)::rtail)) vset (indent+1)))         
      | [], [] ->
         let (new_lhs_p,new_rhs_p) = (mkAndlst lhs_p,mkAndlst rhs_p) in       
         if isValid (mkImply new_lhs_p new_rhs_p)
         then
           if isValid (mkImply new_lhs_p (mkFalse ()))
           then Some False
           else Some (Frame (new_lhs_p,[]))
         else None
      | [], _ -> None
      | _, [] ->
         let (new_lhs_p,new_rhs_p) = (mkAndlst lhs_p,mkAndlst rhs_p) in       
         if isValid (mkImply new_lhs_p new_rhs_p)
         then
           if isValid (mkImply new_lhs_p (mkFalse ()))
           then Some False
           else Some (Frame (new_lhs_p,lhs_h))
         else None       
      | lh::ltail, rh::rtail ->
         ( match lh, rh with
           | Aseg (f,t), _ ->
              failwith "helper_qf_with_frame: Invalid case"
           | _, Aseg (rt,rm) ->
              failwith "helper_qf_with_frame: Invalid case"
           | Pointsto (t,v), Pointsto (rt,rv) ->
              (andFrame
                 (helper_qf_with_frame (mkArrF lhs_e ((mkEq t rt)::lhs_p) ltail) (mkArrF rhs_e ([mkEq t rt; mkEq v rv]@rhs_p) rtail) vset (indent+1))
                 (addFrame (helper_qf_with_frame (mkArrF lhs_e ((mkLt t rt)::lhs_p) ltail) (mkArrF rhs_e rhs_p rtail) vset (indent+1)) (mkPointsto t v)))
           | Pointsto (t,v), AsegNE (rt,rm) ->
              let (newvar,newpreds) = unfold_AsegNE rt rm in
              helper_qf_with_frame lhs (mkArrF rhs_e rhs_p (newpreds@rtail)) (newvar::vset) (indent+1)
           | AsegNE (t,m), Pointsto (rt,rv) ->
              let (newvar,newpreds) = unfold_AsegNE t m in
              helper_qf_with_frame (mkArrF lhs_e lhs_p (newpreds@ltail)) rhs (newvar::vset) (indent+1)
           | AsegNE (t,m), AsegNE (rt,rm) ->
              if is_same_exp t rt
              then
                (andFrame
                   (helper_qf_with_frame (mkArrF lhs_e ([mkLte m rm]@lhs_p) ltail) (mkArrF rhs_e ([mkEq rt t]@rhs_p) ((mkAseg m rm)::rtail)) vset (indent+1))
                   (helper_qf_with_frame (mkArrF lhs_e ([mkLt rm m]@lhs_p) ((mkAsegNE rm m)::ltail)) (mkArrF rhs_e ([mkEq rt t]@rhs_p) rtail) vset (indent+1)))
              else
                (andFrame
                   (helper_qf_with_frame (mkArrF lhs_e ([mkEq t rt]@lhs_p) lhs_h) (mkArrF rhs_e rhs_p ((mkAseg t rm)::rtail)) vset (indent+1))
                   (addFrame (helper_qf_with_frame (mkArrF lhs_e ([mkLt t rt]@lhs_p) lhs_h) (mkArrF rhs_e rhs_p ((mkAseg t rm)::rtail)) vset (indent+1)) (mkAsegNE t rt)))
           | _, _ -> failwith "helper_qf_with_frame: Invalid input")
  in

  let helper_with_frame lhs rhs_disj =
    match lhs,rhs with
    | [(lhs_e,lhs_p,lhs_h)],[(rhs_e,rhs_p,rhs_h)] ->
       if List.length rhs_e = 0
       then helper_qf_with_frame (lhs_e,lhs_p,lhs_h) (rhs_e,rhs_p,rhs_h) [] 0
       else failwith "helper_with_frame: TO BE IMPLEMENTED"
    | _,_ -> failwith "helper_with_frame: TO BE IMPLEMENTED"
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
  let (lhs,rhs) = helper_sorted lhs rhs in
  helper_with_frame lhs rhs
;;

let array_entailment_and_print lhs rhs =  
  let ante = cformula_to_arrF lhs in  
  let conseq = cformula_to_arrF rhs in    
  let f = array_entailment ante conseq in
  let () = print_endline (!str_pformula f) in
  mkCtxWithPure (simplify f)
;;  

let array_entailment_with_frame_and_print lhs rhs =
  let ante = cformula_to_arrF lhs in
  let conseq = cformula_to_arrF rhs in
  let frame = array_entailment_with_frame ante conseq in
  match frame with
  | None ->
     mkEmptyFailCtx ()
  | Some f ->
     let () = print_endline (str_frame f) in
     ( match f with
       | False ->
          mkCtxWithPure (mkFalse ())
       | Frame (framep, frameh) ->
          let (h_frame,p_frame,svlst) = asegPred_to_h_formula frameh in
          mkCtxWithFrame (simplify (mkAndlst (framep::p_frame))) h_frame
     )
;;
          
