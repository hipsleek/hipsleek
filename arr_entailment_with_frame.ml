#include "xdebug.cppo"
open Arr_biabduction_extend

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
    let () =
      if !Globals.array_verbose
      then
        print_endline (print_indent indent ("=>"^(str_frameFormula f)))
      else
        ()
    in
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
    
  let rec helper ((lhs_p,lhs_h) as lhs) ((rhs_p,rhs_h) as rhs) vset indent =
    let () =
      if !Globals.array_verbose
      then
        print_endline (""^(print_indent indent ((str_asegplusF lhs)^" |"^(str_list !str_sv vset)^"- "^(str_asegplusF rhs))))
      else
        ()
    in
    if not(isSat (mkAndlst (lhs_p@rhs_p)))
    then
      print_and_return (FExists (vset, (FNot (mkFBase (lhs_p,[]))))) indent
    else
      match lhs_h, rhs_h with
      | (Aseg_p (la,lb))::ltail, _ ->
         let (uset,vsetprime) = mkUsetandVsetprime [la;lb] vset in            
         let f1 = helper ((mkEqSv la lb)::lhs_p,ltail) rhs vsetprime (indent+1) in
         let f2 = helper ((mkLtSv la lb)::lhs_p,(mkAsegNE_p la lb)::ltail) rhs vsetprime (indent+1) in
         print_and_return (FExists (uset,FAnd [f1;f2])) indent
                          
      | _ ,(Aseg_p (a,b))::rtail ->
         let f1 = helper lhs ((mkEqSv a b)::rhs_p,rtail) vset (indent+1) in
         let f2 = helper lhs ((mkLtSv a b)::rhs_p,(mkAsegNE_p a b)::rtail) vset (indent+1) in
         print_and_return (FOr [f1;f2]) indent
                          
      | lh::ltail, rh::rtail ->
       ( match lh, rh with
         | Aseg_p (la,lb), _ ->
            let (uset,vsetprime) = mkUsetandVsetprime [la;lb] vset in            
            let f1 = helper ((mkEqSv la lb)::lhs_p,ltail) rhs vsetprime (indent+1) in
            let f2 = helper ((mkLtSv la lb)::lhs_p,(mkAsegNE_p la lb)::ltail) rhs vsetprime (indent+1) in
            print_and_return (FExists (uset,FAnd [f1;f2])) indent
                    
         | _, Aseg_p (ra,rb) ->
            let f1 = helper lhs ((mkEqSv ra rb)::rhs_p,rtail) vset (indent+1) in
            let f2 = helper lhs ((mkLtSv ra rb)::rhs_p,(mkAsegNE_p ra rb)::rtail) vset (indent+1) in
            print_and_return (FOr [f1;f2]) indent
                
         | Pointsto_p (ls,lv),Pointsto_p (rs,rv) ->
            let (uset,vsetprime) = mkUsetandVsetprime [ls;rs] vset in            
            let f1 = helper ((mkEqSv ls rs)::lhs_p, ltail) ((mkEqSv lv rv)::rhs_p, rtail) vsetprime (indent+1) in
            let f2 = FExists (vsetprime, mkFBase ([mkNot (mkAndlst ((mkNeqSv ls rs)::lhs_p))],[])) in
            print_and_return (FExists (uset, FAnd [f1;f2])) indent

         | AsegNE_p (la,lb), AsegNE_p (ra,rb) -> 
            if is_same_sv la ra
            then
              let (uset,vsetprime) = mkUsetandVsetprime [lb;rb] vset in
              let f1 = helper ((mkGtSv rb lb)::lhs_p,ltail) (rhs_p, (mkAsegNE_p lb rb)::rtail) vsetprime (indent+1) in
              let f2 = helper ((mkLteSv rb lb)::lhs_p,(mkAseg_p rb lb)::ltail) (rhs_p, rtail) vsetprime (indent+1) in
              print_and_return (FExists (uset, FAnd [f1;f2])) indent
            else
              let (uset,vsetprime) = mkUsetandVsetprime [la;ra] vset in
              let f1 = helper ((mkEqSv la ra)::lhs_p, lhs_h) (rhs_p, (mkAsegNE_p la rb)::rtail) vsetprime (indent+1) in
              let f2 = FExists (vsetprime, mkFBase ([mkNot (mkAndlst ((mkNeqSv la ra)::lhs_p))],[])) in
              print_and_return (FExists (uset, FAnd [f1;f2;(FExists (vsetprime, (mkFBase ([(mkNot (mkAndlst ((mkGtSv la ra)::lhs_p)))],[])))) ])) indent

         | AsegNE_p (la,lb), Pointsto_p (rs,rv) ->
            let (uset,vsetprime) = mkUsetandVsetprime [la] vset in
            let fresh_c = global_get_new_var () in
            let fresh_u = global_get_new_var () in
            let f = helper ((mkEq (mkVar fresh_c) (incOne (mkVar la)))::lhs_p,([mkPointsto_p la fresh_u; mkAseg_p fresh_c lb]@ltail))
                           rhs vsetprime (indent+1) in
            print_and_return (FExists (uset,(FForall ([fresh_c;fresh_u],f)))) indent

         | Pointsto_p (ls,lv),AsegNE_p (ra,rb) ->
            let fresh_c = global_get_new_var () in
            let fresh_u = global_get_new_var () in
            print_and_return (helper lhs
                                     ((mkEq (mkVar fresh_c) (incOne (mkVar ra)))::rhs_p,([mkPointsto_p ra fresh_u; mkAseg_p fresh_c rb]@rtail))
                                     ([fresh_c;fresh_u]@vset) (indent+1)) indent
         | _, Gap_p _ -> failwith "Gap_p"
         | Gap_p _,_ -> failwith "Gap_p"
       )
      | [],[] -> print_and_return (FExists (vset, FOr [FNot (mkFBase (lhs_p,[]));mkFBase (rhs_p,[])])) indent
                                  
      | _, []
      | [], _ ->
         print_and_return (FExists (vset, (FNot (mkFBase (lhs_p,[]))))) indent

  in
  let helper_entry (lhs_e,lhs_p,lhs_h) (rhs_e,rhs_p,rhs_h) =
    FForall (lhs_e,helper ((get_sorted_puref_general lhs_h)::lhs_p,lhs_h) ((get_sorted_puref_general rhs_h)::rhs_p,rhs_h) rhs_e 0)
  in
  let transAnte = new arrPredTransformer_orig lhs in
  let transConseq = new arrPredTransformer_orig rhs in
  let f = helper_entry (aPredF_to_asegF (transAnte#formula_to_general_formula)) (aPredF_to_asegF (transConseq#formula_to_general_formula)) in
  (* let () = print_endline (str_frameFormula f) in *)
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
