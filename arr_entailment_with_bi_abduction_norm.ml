#include "xdebug.cppo"
open Arr_biabduction_extend
open Arr_entailment_with_frame
open Arr_entailment_with_bi_abduction
(* This version early check pure formula in LHS *)
(* This version handle existential in a wrapping manner *)
(* Bi-Abduction *)


       
type norm_pre_condition =
  | NormBaseNeg of (Cpure.spec_var list * Cpure.formula list *  Cpure.formula list)
  | NormBaseImply of (Cpure.spec_var list * Cpure.formula list * Cpure.formula list * Cpure.formula list * asegPredplus list * asegPredplus list)
  | NormOr of (Cpure.spec_var list * norm_pre_condition list)                
;;

let mkNormBaseNeg vset case pf =
  NormBaseNeg (vset,case,pf)
;;

let mkNormBaseImply vset case lhsp rhsp frame antiframe =
  NormBaseImply (vset,case,lhsp,rhsp,frame,antiframe)
;;

let mkNormOr vset nlst =
  NormOr (vset,nlst)
;;

let rec str_norm_pre_condition norm =
  match norm with
  | NormBaseNeg (vset,clst,pflst) ->
     if List.length vset = 0
     then ((str_list !str_pformula clst)^"/\\("^(str_list !str_pformula pflst)^"=>false)")
     else failwith "str_norm_pre_condition: TO BE IMPLEMENTED"
  | NormBaseImply (vset,clst,lhs_p,rhs_p,frame,antiframe) ->
     if List.length vset = 0
     then (str_list !str_pformula clst)^"/\\("^("{"^(str_list !str_pformula lhs_p)^"=>"^(str_list !str_pformula rhs_p)^" @"^(str_asegPredplus_lst frame)^" * "^(str_asegPredplus_lst antiframe)^"})")
     else failwith "str_norm_pre_condition: TO BE IMPLEMENTED"
  | NormOr (vset,nlst) ->
     if List.length vset = 0
     then str_list_delimeter str_norm_pre_condition nlst "\n" ""
     else failwith "str_norm_pre_condition: TO BE IMPLEMENTED"
;;
      

  
let combine_norm nlst clst =
  let rec enhance_with_case norm case =
    match norm with
    | NormBaseNeg (vset,clst,pf) ->
       [mkNormBaseNeg vset (case::clst) pf]
    | NormBaseImply (vset,clst,lhsp,rhsp,frame,antiframe) ->
       [mkNormBaseImply vset (case::clst) lhsp rhsp frame antiframe]
    | NormOr (vset,norlst) ->
       List.concat (List.map (fun item -> enhance_with_case item case) norlst)
  in
    
  try
    mkNormOr [] (List.concat (List.map2 (fun norm case -> enhance_with_case norm case) nlst clst))
  with Invalid_argument _->
    failwith "combine_norm: case number not matching"
;;

let simplify_pure_in_norm_pre_condition norm =
  let rec helper norm =
    match norm with
    | NormBaseNeg (vset,clst,pflst) ->
       mkNormBaseNeg vset [simplify (mkAndlst clst)] [simplify (mkAndlst pflst)]
    | NormBaseImply (vset,clst,lhs_p,rhs_p,frame,antiframe) ->
       mkNormBaseImply vset [simplify (mkAndlst clst)] [simplify (mkAndlst lhs_p)] [simplify (mkAndlst rhs_p)] frame antiframe
    | NormOr (vset,nlst) ->
       NormOr (vset, List.map helper nlst)
  in
  helper norm
;;
  
let merge_false_in_norm_pre_condition norm =
  let merge_helper fnormlst =
    let allcase = List.fold_left
                    (fun r item ->
                      match item with
                      | NormBaseNeg (vset,clst,pflst) -> mkOr (mkAndlst clst) r
                      | _ -> failwith "merge_false_in_norm_pre_condition: Invalid input")
                    (mkFalse ()) fnormlst
    in
    match fnormlst with
    | (NormBaseNeg (_,_,pflst))::tail ->
       mkNormBaseNeg [] [simplify allcase] pflst
    | _ -> failwith "merge_helper: Invalid input"
  in      
  match norm with
  | NormBaseNeg _
  | NormBaseImply _ ->
     norm
  | NormOr (vset,nlst) ->
     let (falselst, others) = List.partition
                             (function
                                NormBaseNeg _ -> true
                              | _ -> false) nlst
     in
     if List.length falselst = 0
     then norm
     else
       mkNormOr vset ((merge_helper falselst)::others)
;;


let simplify_norm_pre_condition norm =
  merge_false_in_norm_pre_condition (simplify_pure_in_norm_pre_condition norm)
;;
  
       

let array_entailment_biabduction_norm lhs rhs =
  let mkUsetandVsetprime set vset =
    let uset = List.filter (fun item -> List.exists (fun item1 -> is_same_sv item item1) set)  vset in
    let vsetprime = List.filter (fun item -> not (List.exists (fun item1 -> is_same_sv item item1) uset)) vset in
    (uset,vsetprime)
  in

  let print_and_return f indent =
    let () = print_endline (print_indent indent ("=>"^(str_biabFormula f))) in
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
  let helper_orig orig_lhs_p lhs orig_rhs_p rhs vset frame antiframe indent =
    let rec helper ((lhs_p,lhs_h) as lhs) ((rhs_p,rhs_h) as rhs) vset frame antiframe indent =
      let () = print_endline (""^(print_indent indent ((str_asegplusF lhs)^" |- "^(str_asegplusF rhs)))) in
      if not(isSat (mkAndlst (lhs_p@rhs_p)))
      then
        let norm = mkNormBaseNeg vset [] orig_lhs_p in
        (print_and_return (mkBExists (vset, (mkBBaseNeg lhs_p))) indent,norm)
      else
        match lhs_h, rhs_h with
        | (Aseg_p (la,lb))::ltail, _ ->
           let (uset,vsetprime) = mkUsetandVsetprime [la;lb] vset in
           let case1 = mkEqSv la lb in
           let case2 = mkLtSv la lb in
           let (f1,norm1) = helper (case1::lhs_p,ltail) rhs vsetprime frame antiframe (indent+1) in
           let (f2,norm2) = helper (case2::lhs_p,(mkAsegNE_p la lb)::ltail) rhs vsetprime frame antiframe (indent+1) in
           (print_and_return (mkBExists (uset,mkBAnd [f1;f2])) indent, combine_norm [norm1;norm2] [case1;case2])
             
        | _ ,(Aseg_p (a,b))::rtail ->
           if false
           then
             let (f1,norm1) = helper lhs ((mkEqSv a b)::rhs_p,rtail) vset frame antiframe (indent+1) in
             let (f2,norm2) = helper lhs ((mkLtSv a b)::rhs_p,(mkAsegNE_p a b)::rtail) vset frame antiframe (indent+1) in
             (print_and_return (BOr [f1;f2]) indent,mkNormOr [] [norm1;norm2])
           else           
             let (uset,vsetprime) = mkUsetandVsetprime [a;b] vset in
             let case1 = mkEqSv a b in
             let case2 = mkLtSv a b in
             let case3 = mkGtSv a b in
             let (f1,norm1) = helper (case1::lhs_p,lhs_h) (rhs_p,rtail) vsetprime frame antiframe (indent+1) in
             let (f2,norm2) = helper (case2::lhs_p,lhs_h) (rhs_p,(mkAsegNE_p a b)::rtail) vsetprime frame antiframe (indent+1) in
             let (f3,norm3) = helper (case3::lhs_p,lhs_h) rhs vsetprime frame antiframe (indent+1) in
             (print_and_return (mkBExists (uset,mkBAnd [f1;f2;f3])) indent,combine_norm [norm1;norm2;norm3] [case1;case2;case3])
               
        | [], [] ->
           let frame = List.rev frame in
           let antiframe = List.rev antiframe in
           let norm = mkNormBaseImply vset [] orig_lhs_p rhs_p frame antiframe in
           (print_and_return (mkBExists (vset, BBaseImply (lhs_p,rhs_p,frame,antiframe))) indent,norm)
             
        | [], _ ->
           let (f,norm) = helper lhs (rhs_p,[]) vset frame (rhs_h@antiframe) (indent+1) in
           (print_and_return f indent,norm)

        | _, [] ->
           let (f,norm) = helper (lhs_p,[]) rhs vset (lhs_h@frame) antiframe (indent+1) in
           (print_and_return f indent,norm)
             
        | lh::ltail, rh::rtail ->
           ( match lh, rh with
             | Aseg_p _, _              
               | _, Aseg_p _->
                failwith "Aseg_p: Invalid cases"
                         
             | Pointsto_p (ls,lv),Pointsto_p (rs,rv) ->
                if is_same_sv ls rs
                then
                  let f,norm = helper (lhs_p, ltail) ((mkEqSv lv rv)::rhs_p, rtail) vset frame antiframe (indent+1) in
                  (print_and_return f indent,norm)
                else
                  let (uset,vsetprime) = mkUsetandVsetprime [ls;rs] vset in
                  let case1 = mkEqSv ls rs in
                  let case2 = mkLtSv ls rs in
                  let case3 = mkGtSv ls rs in
                  let f1,norm1 = helper (case1::lhs_p, lhs_h) (rhs_p, (mkPointsto_p ls rv)::rtail) vsetprime frame antiframe (indent+1) in
                  let f2,norm2 = helper (case2::lhs_p, ltail) rhs vsetprime (lh::frame) antiframe (indent+1) in
                  let f3,norm3 = helper (case3::lhs_p, lhs_h) (rhs_p,rtail) vsetprime frame (rh::antiframe) (indent+1) in
                  (print_and_return (mkBExists (uset, mkBAnd [f1;f2;f3])) indent,combine_norm [norm1;norm2;norm3] [case1;case2;case3])

             | AsegNE_p (la,lb), AsegNE_p (ra,rb) ->              
                if is_same_sv la ra
                then
                  let (uset,vsetprime) = mkUsetandVsetprime [lb;rb] vset in
                  let case1 = mkGtSv rb lb in
                  let case2 = mkLteSv rb lb in
                  let f1,norm1 = helper (case1::lhs_p,ltail) (rhs_p, (mkAsegNE_p lb rb)::rtail) vsetprime frame antiframe (indent+1) in
                  let f2,norm2 = helper (case2::lhs_p,(mkAseg_p rb lb)::ltail) (rhs_p, rtail) vsetprime frame antiframe (indent+1) in
                  (print_and_return (mkBExists (uset, mkBAnd [f1;f2])) indent,combine_norm [norm1;norm2] [case1;case2])
                else
                  let (uset,vsetprime) = mkUsetandVsetprime [la;ra] vset in
                  let case1 = (mkEqSv la ra) in
                  let case2 = (mkLtSv la ra) in
                  let case3 = (mkGtSv la ra) in
                  let f1,norm1 = helper (case1::lhs_p, lhs_h) (rhs_p, (mkAsegNE_p la rb)::rtail) vsetprime frame antiframe (indent+1) in
                  let f2,norm2 = helper (case2::lhs_p, lhs_h) (rhs_p, (mkGap_p la ra)::rhs_h) vsetprime frame antiframe (indent+1) in
                  let f3,norm3 = helper (case3::lhs_p, (mkGap_p ra la)::lhs_h) (rhs_p, rhs_h) vsetprime frame antiframe (indent+1) in
                  (print_and_return (mkBExists (uset, mkBAnd [f1;f2;f3])) indent,combine_norm [norm1;norm2;norm3] [case1;case2;case3])
                    
             | AsegNE_p (la,lb), Gap_p (ra,rb) ->
                if is_same_sv la ra
                then
                  let (uset,vsetprime) = mkUsetandVsetprime [lb;rb] vset in
                  let case1 = (mkLtSv lb rb) in
                  let case2 = (mkGteSv lb rb) in
                  let f1,norm1 = helper (case1::lhs_p, ltail) (rhs_p, rtail) vsetprime (lh::frame) antiframe (indent+1) in
                  let f2,norm2 = helper (case2::lhs_p, (Aseg_p (rb,lb))::ltail) (rhs_p, rtail) vsetprime ((mkAsegNE_p la rb)::frame) antiframe (indent+1) in
                  (print_and_return (mkBExists (uset, mkBAnd [f1;f2])) indent,combine_norm [norm1;norm2] [case1;case2])
                else
                  failwith "AsegNE v.s Gap: Not aligned"

             | Gap_p (la,lb), AsegNE_p (ra,rb)->
                if is_same_sv la ra
                then
                  let (uset,vsetprime) = mkUsetandVsetprime [lb;rb] vset in
                  let case1 = (mkGtSv lb rb) in
                  let case2 = (mkLteSv lb rb) in
                  let f1,norm1 = helper (case1::lhs_p, ltail) (rhs_p, rtail) vsetprime frame ((mkAsegNE_p la rb)::antiframe) (indent+1) in
                  let f2,norm2 = helper (case2::lhs_p, (Aseg_p (rb,lb))::ltail) (rhs_p, rtail) vsetprime frame ((mkAsegNE_p la lb)::antiframe) (indent+1) in
                  (print_and_return (mkBExists (uset, mkBAnd [f1;f2])) indent,combine_norm [norm1;norm2] [case1;case2])
                else
                  failwith "AsegNE v.s Gap: Not aligned"                                                  

             | Pointsto_p (ls,lv), Gap_p (ra,rb) ->
                if is_same_sv ls ra
                then
                  let f,norm = helper (lhs_p,ltail) (rhs_p,rtail) vset (lh::frame) antiframe (indent+1) in
                  (print_and_return f indent,norm)
                else
                  failwith "Pointsto_p v.s Gap: Not aligned"

             | Gap_p (la,lb), Pointsto_p (rs,rv) ->
                if is_same_sv la rs
                then
                  let f,norm = helper (lhs_p,ltail) (rhs_p,rtail) vset frame (rh::antiframe) (indent+1) in
                  (print_and_return f indent,norm)
                else
                  failwith "Gap v.s Pointsto_p: Not aligned"

             | AsegNE_p (la,lb), Pointsto_p (rs,rv) ->
                failwith "AsegNE_p vs.s Pointsto_p: TO BE IMPLEMENTED"
             (* if is_same_sv la rs *)
             (* then *)
             (*   let fresh_c = global_get_new_var () in *)
             (*   let fresh_u = global_get_new_var () in *)
             (*   let f = helper ((mkEq (mkVar fresh_c) (incOne (mkVar la)))::lhs_p,([mkPointsto_p la fresh_u; mkAseg_p fresh_c lb]@ltail)) *)
             (*                  rhs vset frame antiframe (indent+1) in *)
             (*   print_and_return (mkBForall ([fresh_c;fresh_u],f)) indent *)
             (* else *)
             (*   let (uset,vsetprime) = mkUsetandVsetprime [la;rs] vset in *)
             (*   let f1 = helper ((mkEqSv la rs)::lhs_p, lhs_h) (rhs_p, (mkPointsto_p la rv)::rtail) vsetprime frame antiframe (indent+1) in *)
             (*   let f2 = helper ((mkLtSv la rs)::lhs_p, lhs_h) (rhs_p, (mkGap_p la rs)::rhs_h) vsetprime frame antiframe (indent+1) in *)
             (*   let f3 = helper ((mkGtSv la rs)::lhs_p, (mkGap_p rs la)::lhs_h) (rhs_p, rhs_h) vsetprime frame antiframe (indent+1) in *)
             (*   print_and_return (mkBExists (uset, mkBAnd [f1;f2;f3])) indent *)

             | Pointsto_p (ls,lv),AsegNE_p (ra,rb) ->
                if is_same_sv ls ra
                then
                  let fresh_c = global_get_new_var () in
                  let fresh_u = global_get_new_var () in
                  let f,norm = (helper lhs
                                       ((mkEq (mkVar fresh_c) (incOne (mkVar ra)))::rhs_p,([mkPointsto_p ra fresh_u; mkAseg_p fresh_c rb]@rtail))
                                       ([fresh_c;fresh_u]@vset) frame antiframe (indent+1))
                  in
                  (print_and_return f indent,norm)
                else
                  let (uset,vsetprime) = mkUsetandVsetprime [ls;ra] vset in
                  let case1 = (mkEqSv ls ra) in
                  let case2 = (mkLtSv ls ra) in
                  let case3 = (mkGtSv ls ra) in
                  let f1,norm1 = helper (case1::lhs_p, lhs_h) (rhs_p, (mkAsegNE_p ls rb)::rtail) vsetprime frame antiframe (indent+1) in
                  let f2,norm2 = helper (case2::lhs_p, lhs_h) (rhs_p, (mkGap_p ls ra)::rhs_h) vsetprime frame antiframe (indent+1) in
                  let f3,norm3 = helper (case3::lhs_p, (mkGap_p ra ls)::lhs_h) (rhs_p, rhs_h) vsetprime frame antiframe (indent+1) in
                  (print_and_return (mkBExists (uset, BAnd [f1;f2;f3])) indent,combine_norm [norm1;norm2;norm3] [case1;case2;case3])

             | Gap_p _, Gap_p _ ->
                failwith "Gap_p vs Gap_p: Invalid case"
           )
    in
    helper lhs rhs vset frame antiframe indent
  in
  let helper_entry (lhs_e,lhs_p,lhs_h) (rhs_e,rhs_p,rhs_h) =
    let orig_lhs_p = (get_sorted_puref_general lhs_h)::lhs_p in
    let orig_rhs_p = (get_sorted_puref_general rhs_h)::rhs_p in
    let f,norm = helper_orig orig_lhs_p (orig_lhs_p,lhs_h) orig_rhs_p (orig_rhs_p,rhs_h) rhs_e [] [] 0 in
    (mkBForall (lhs_e,f),norm)
  in
  let transAnte = new arrPredTransformer_orig lhs in
  let transConseq = new arrPredTransformer_orig rhs in
  helper_entry (aPredF_to_asegF (transAnte#formula_to_general_formula)) (aPredF_to_asegF (transConseq#formula_to_general_formula))
;;

let array_entailment_biabduction_interface lhs rhs =
  let (f,norm) = array_entailment_biabduction_norm lhs rhs in
  let () = print_endline ("=========== formatted pre-condition ==============") in
  let () = print_endline (str_pre_condition f) in
  let () = print_endline ("=========== Normalized pre-condition ==============") in
  let () = print_endline (str_norm_pre_condition norm) in
  let () = print_endline ("=========== Simplified Normalized pre-condition ==============") in
  let simp_norm = simplify_norm_pre_condition norm in
  let () = print_endline (str_norm_pre_condition simp_norm) in
  (true, mkEmptySuccCtx (),[])
;;
