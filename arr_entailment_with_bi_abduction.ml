#include "xdebug.cppo"
open Arr_biabduction_extend
open Arr_entailment_with_frame
(* This version early check pure formula in LHS *)
(* This version handle existential in a wrapping manner *)
(* Bi-Abduction *)

type biabFormula =
  | BBaseNeg of (Cpure.formula list)
  | BBaseImply of (Cpure.formula list * Cpure.formula list * asegPredplus list * asegPredplus list)
  | BExists of (Cpure.spec_var list * biabFormula)
  | BForall of (Cpure.spec_var list * biabFormula)
  | BAnd of (biabFormula list)
  | BOr of (biabFormula list)
  | BNot of biabFormula
;;

let mkBBaseNeg plst =
  BBaseNeg plst
;;

let mkBBaseImply lplst rplst frame antiframe =
  BBaseImply (lplst, rplst, frame, antiframe) 
;;

let mkBAnd flst =
  BAnd (List.fold_left
          (fun r item ->
            match item with
            | BAnd flst1 -> flst1@r
            | _ -> item::r )
          [] flst)
;;

let rec str_biabFormula f =  
  match f with
  | BBaseNeg plst ->
     "{NOT "^(str_list !str_pformula plst)^"}"
  | BBaseImply (lplst, rplst, frame, antiframe) ->
     "{"^(str_list !str_pformula lplst)^"==>"^(str_list !str_pformula rplst)^" @"^(str_asegPredplus_lst frame)^" * "^(str_asegPredplus_lst antiframe)^"}"
  | BExists (vset, nf) ->
     if List.length vset = 0
     then str_biabFormula nf
     else "Exists "^(str_list !str_sv vset)^": "^(str_biabFormula nf)
  | BForall (vset, nf) ->
     if List.length vset = 0
     then str_biabFormula nf
     else "Forall "^(str_list !str_sv vset)^": "^(str_biabFormula nf)
  | BAnd flst ->
     str_list_delimeter str_biabFormula flst "/\\" ""
  | BOr flst ->
     str_list_delimeter str_biabFormula flst "\\/" ""  
  | BNot nf ->
     "not("^(str_biabFormula nf)^")"
;;
  

let array_entailment_biabduction lhs rhs =
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
  
  let rec helper ((lhs_p,lhs_h) as lhs) ((rhs_p,rhs_h) as rhs) vset frame antiframe indent =
    let () = print_endline (""^(print_indent indent ((str_asegplusF lhs)^" |- "^(str_asegplusF rhs)))) in
    if not(isSat (mkAndlst (lhs_p@rhs_p)))
    then
      print_and_return (BExists (vset, (mkBBaseNeg lhs_p))) indent
    else
      match lhs_h, rhs_h with
      | (Aseg_p (la,lb))::ltail, _ ->
         let (uset,vsetprime) = mkUsetandVsetprime [la;lb] vset in            
         let f1 = helper ((mkEqSv la lb)::lhs_p,ltail) rhs vsetprime frame antiframe (indent+1) in
         let f2 = helper ((mkLtSv la lb)::lhs_p,(mkAsegNE_p la lb)::ltail) rhs vsetprime frame antiframe (indent+1) in
         print_and_return (BExists (uset,mkBAnd [f1;f2])) indent
      | _ ,(Aseg_p (a,b))::rtail ->
         let f1 = helper lhs ((mkEqSv a b)::rhs_p,rtail) vset frame antiframe (indent+1) in
         let f2 = helper lhs ((mkLtSv a b)::rhs_p,(mkAsegNE_p a b)::rtail) vset frame antiframe (indent+1) in
         print_and_return (BOr [f1;f2]) indent
      | [], [] ->
         print_and_return (BExists (vset, BBaseImply (lhs_p,rhs_p,List.rev frame,List.rev antiframe))) indent
                          
      | [], _ ->
         let f = helper lhs (rhs_p,[]) vset frame (rhs_h@antiframe) (indent+1) in
         print_and_return f indent

      | _, [] ->
         let f = helper (lhs_p,[]) rhs vset (lhs_h@frame) antiframe (indent+1) in
         print_and_return f indent
                          
      | lh::ltail, rh::rtail ->
         ( match lh, rh with
           | Aseg_p _, _              
           | _, Aseg_p _->
              failwith "Aseg_p: Invalid cases"
                               
           | Pointsto_p (ls,lv),Pointsto_p (rs,rv) ->
              let (uset,vsetprime) = mkUsetandVsetprime [ls;rs] vset in            
              let f1 = helper ((mkEqSv ls rs)::lhs_p, ltail) ((mkEqSv lv rv)::rhs_p, rtail) vsetprime frame antiframe (indent+1) in
              let f2 = helper ((mkLtSv ls rs)::lhs_p, ltail) rhs vsetprime (lh::frame) antiframe (indent+1) in
              let f3 = helper ((mkGtSv ls rs)::lhs_p, lhs_h) (rhs_p,rtail) vsetprime frame (rh::antiframe) (indent+1) in
              print_and_return (BExists (uset, mkBAnd [f1;f2;f3])) indent

           | AsegNE_p (la,lb), AsegNE_p (ra,rb) ->              
              if is_same_sv la ra
              then
                let (uset,vsetprime) = mkUsetandVsetprime [lb;rb] vset in
                let f1 = helper ((mkGtSv rb lb)::lhs_p,ltail) (rhs_p, (mkAsegNE_p lb rb)::rtail) vsetprime frame antiframe (indent+1) in
                let f2 = helper ((mkLteSv rb lb)::lhs_p,(mkAseg_p rb lb)::ltail) (rhs_p, rtail) vsetprime frame antiframe (indent+1) in
                print_and_return (BExists (uset, mkBAnd [f1;f2])) indent
              else
                let (uset,vsetprime) = mkUsetandVsetprime [la;ra] vset in
                let f1 = helper ((mkEqSv la ra)::lhs_p, lhs_h) (rhs_p, (mkAsegNE_p la rb)::rtail) vsetprime frame antiframe (indent+1) in
                let f2 = helper ((mkLtSv la ra)::lhs_p, lhs_h) (rhs_p, (mkGap_p la ra)::rhs_h) vsetprime frame antiframe (indent+1) in
                let f3 = helper ((mkGtSv la ra)::lhs_p, (mkGap_p ra la)::lhs_h) (rhs_p, rhs_h) vsetprime frame antiframe (indent+1) in
                print_and_return (BExists (uset, mkBAnd [f1;f2;f3])) indent
                                 
           | AsegNE_p (la,lb), Gap_p (ra,rb) ->
              if is_same_sv la ra
              then
                let (uset,vsetprime) = mkUsetandVsetprime [lb;rb] vset in            
                let f1 = helper ((mkLtSv lb rb)::lhs_p, ltail) (rhs_p, rtail) vsetprime (lh::frame) antiframe (indent+1) in
                let f2 = helper ((mkGteSv lb rb)::lhs_p, (Aseg_p (rb,lb))::ltail) (rhs_p, rtail) vsetprime ((mkAsegNE_p la rb)::frame) antiframe (indent+1) in
                print_and_return (BExists (uset, mkBAnd [f1;f2])) indent
              else
                failwith "AsegNE v.s Gap: Not aligned"

           | Pointsto_p (ls,lv), Gap_p (ra,rb) ->
              if is_same_sv ls ra
              then
                failwith "TO BE IMPLEMENTED"                         
              else
                failwith "TO BE IMPLEMENTED"

           | Gap_p (la,lb), AsegNE_p (ra,rb)->
              if is_same_sv la ra
              then
                let (uset,vsetprime) = mkUsetandVsetprime [lb;rb] vset in            
                let f1 = helper ((mkGtSv lb rb)::lhs_p, ltail) (rhs_p, rtail) vsetprime frame ((mkAsegNE_p la rb)::antiframe) (indent+1) in
                let f2 = helper ((mkLteSv lb rb)::lhs_p, (Aseg_p (rb,lb))::ltail) (rhs_p, rtail) vsetprime frame ((mkAsegNE_p la lb)::antiframe) (indent+1) in
                print_and_return (BExists (uset, mkBAnd [f1;f2])) indent
              else
                failwith "AsegNE v.s Gap: Not aligned"                         

           | AsegNE_p (la,lb), Pointsto_p (rs,rv) ->
              if is_same_sv la rs
              then
                let fresh_c = global_get_new_var () in
                let fresh_u = global_get_new_var () in
                let f = helper ((mkEq (mkVar fresh_c) (incOne (mkVar la)))::lhs_p,([mkPointsto_p la fresh_u; mkAseg_p fresh_c lb]@ltail))
                               rhs vset frame antiframe (indent+1) in
                print_and_return (BForall ([fresh_c;fresh_u],f)) indent
              else
                let (uset,vsetprime) = mkUsetandVsetprime [la;rs] vset in
                let f1 = helper ((mkEqSv la rs)::lhs_p, lhs_h) (rhs_p, (mkPointsto_p la rv)::rtail) vsetprime frame antiframe (indent+1) in
                let f2 = helper ((mkLtSv la rs)::lhs_p, lhs_h) (rhs_p, (mkGap_p la rs)::rhs_h) vsetprime frame antiframe (indent+1) in
                let f3 = helper ((mkGtSv la rs)::lhs_p, (mkGap_p rs la)::lhs_h) (rhs_p, rhs_h) vsetprime frame antiframe (indent+1) in
                print_and_return (BExists (uset, mkBAnd [f1;f2;f3])) indent

           | Pointsto_p (ls,lv),AsegNE_p (ra,rb) ->
              failwith "TO BE IMPLEMENTED"
              (* if is_same_sv ls ra *)
              (* then *)
              (*   let fresh_c = global_get_new_var () in *)
              (*   let fresh_u = global_get_new_var () in *)
              (*   print_and_return (helper lhs *)
              (*                            ((mkEq (mkVar fresh_c) (incOne (mkVar ra)))::rhs_p,([mkPointsto_p ra fresh_u; mkAseg_p fresh_c rb]@ltail)) *)
              (*                            ([fresh_c;fresh_u]@vset) k (indent+1)) indent *)
              (* else *)
              (*   let (uset,vsetprime) = mkUsetandVsetprime [ls;ra] vset in *)
              (*   let f1 = helper ((mkEqSv ls ra)::lhs_p, lhs_h) (rhs_p, (mkAsegNE_p ls rb)::rtail) vsetprime frame antiframe (indent+1) in *)
              (*   let f2 = helper ((mkLtSv ls ra)::lhs_p, lhs_h) (rhs_p, (mkGap_p ls ra)::rhs_h) vsetprime frame antiframe (indent+1) in *)
              (*   let f3 = helper ((mkGtSv ls ra)::lhs_p, (mkGap_p ra ls)::lhs_h) (rhs_p, rhs_h) vsetprime frame antiframe (indent+1) in *)
              (*   print_and_return (BExists (uset, BAnd [f1;f2;f3])) indent *)

           | _, Gap_p _ ->
              failwith "TO BE IMPLEMENTED"
              (* print_and_return (helper lhs (rhs_p,rtail) vset k (indent+1)) indent *)
                               
           | Gap_p _,_ -> failwith "Gap_p in LHS"
         )
  in
  let helper_entry (lhs_e,lhs_p,lhs_h) (rhs_e,rhs_p,rhs_h) =
    BForall (lhs_e,helper ((get_sorted_puref_general lhs_h)::lhs_p,lhs_h) ((get_sorted_puref_general rhs_h)::rhs_p,rhs_h) rhs_e [] [] 0)
  in
  let transAnte = new arrPredTransformer_orig lhs in
  let transConseq = new arrPredTransformer_orig rhs in
  let f = helper_entry (aPredF_to_asegF (transAnte#formula_to_general_formula)) (aPredF_to_asegF (transConseq#formula_to_general_formula)) in
  (* let () = print_endline (str_frameFormula f) in *)
  f
;;

let array_entailment_biabduction_interface lhs rhs =
  let f = array_entailment_biabduction lhs rhs in
  (true, mkEmptySuccCtx (),[])
;;
