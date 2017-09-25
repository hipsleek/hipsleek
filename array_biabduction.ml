#include "xdebug.cppo"
open Array_formula
open Array_biabduction_pre_condition

(* Global variables *)
let non_trivial = ref false     (* To indentify trivial cases *)
;;
(*  *)
type norm_pre_condition_base =
  | NormBaseNeg of (Cpure.spec_var list * Cpure.spec_var list * Cpure.formula list)
  | NormBaseImply of (Cpure.spec_var list *
                        Cpure.spec_var list *
                          Cpure.formula list *
                            Cpure.formula list * aseg_pred_plus list * aseg_pred_plus list)
;;

let mkNormBaseNeg uset eset pf =
  NormBaseNeg (uset, eset, pf)
;;
  
let mkNormBaseImply uset eset lhsp rhsp frame antiframe =
  NormBaseImply (uset, eset, lhsp, rhsp, frame, antiframe)
;;

let str_norm_pre_condition_base norm =
  match norm with
  | NormBaseNeg (uset, eset, pflst)->
     let inners = (str_list !str_pformula pflst) ^ "=>false)" in
     let s =
       if List.length eset = 0
       then inners
       else "Exists " ^ (str_list !str_sv eset) ^ ": " ^ inners
     in
     if List.length uset = 0
     then s
    else "Forall " ^ (str_list !str_sv uset) ^ " " ^ s
                                                 
  | NormBaseImply (uset, eset, lhs_p, rhs_p, frame, antiframe) ->
     let inners = (str_list !str_pformula lhs_p) ^ "=>"
                  ^ (str_list !str_pformula rhs_p)
                  ^ " @" ^ (str_aseg_pred_plus_lst frame)
                  ^ " * " ^ (str_aseg_pred_plus_lst antiframe) in
     let s =
       if List.length eset = 0
       then inners
       else "Exists " ^ (str_list !str_sv eset) ^ ": " ^ inners
     in
     if List.length uset = 0
     then s
     else "Forall " ^ (str_list !str_sv uset) ^ " " ^ s
;;
  
type norm_pre_condition =
  | NormOr of (Cpure.spec_var list * Cpure.formula list * norm_pre_condition_base) list
;;
  
let mkNormOr lst =
  NormOr lst
;;

let mkNormOr_base uqset_eq base =
  let neweset, newf = List.split (List.map (fun (v, e) -> (v, mkEq (mkVar v) e)) uqset_eq) in
  mkNormOr [(neweset, [], base)]
;;

let rec str_norm_pre_condition  = function
  | NormOr lst ->
     let printer =
       fun (eset, caselst, base) ->
         let inners =
           (str_list !str_pformula caselst) ^ "/\\" ^ (str_norm_pre_condition_base base)
         in
         if List.length eset = 0
         then inners
         else "Exists " ^ (str_list !str_sv eset) ^ ": " ^ inners
     in
     str_list_delimeter printer lst "\n" ""
;;

(* ex U. f1/\f2 *)
let combine_norm nlst clst eset=
  let rec enhance_with_case norm case eset =
    match norm with
    | NormOr lst ->
       (List.map (fun (eset_orig, case_orig, base)-> (eset@eset_orig, case::case_orig, base)) lst)
  in
  try
    mkNormOr (List.concat (List.map2 (fun norm case -> enhance_with_case norm case eset) nlst clst))
  with Invalid_argument _ ->
    failwith "combine_norm: case number not matching"
;;

let simplify_pure_in_norm_pre_condition =
  (function NormOr lst ->
            NormOr (List.map (function (vset,clst,base) ->
                                       (vset,[simplify (mkAndlst clst)],base)) lst))
;;

let simplify_norm_pre_condition norm =
  norm
  (* (simplify_pure_in_norm_pre_condition norm) *)
  (* merge_false_in_norm_pre_condition  *)
;;

let print_and_return f indent =
  (* let () = *)
  (*   print_endline_verbose (print_indent indent ("=>"^(str_biabFormula f))) *)
  (* in *)
  f
;;

let mkUsetandVsetprime set vset =
  let uset = List.filter (fun item -> List.exists (fun item1 -> is_same_sv item item1) set)  vset in
  let vsetprime = List.filter (fun item -> not (List.exists (fun item1 -> is_same_sv item item1) uset)) vset in
  (uset,vsetprime)
;;
  
  
let array_entailment_biabduction_norm lhs rhs =

  (* input: heap formulas, output: a pure formula with sorted information  *)  
  let get_sorted_puref_general arrPredlst =
    let rec helper lst lastm flst =
      match lst with
      | [] -> mkAndlst flst
      | h::tail ->
         begin match h with
         | AsegNE_p (t,m) ->
            helper tail (mkVar m) ([mkLte lastm (mkVar t);mkLtSv t m]@flst)
         | Pointsto_p (t,v) ->
            helper tail (incOne (mkVar t)) ((mkLte lastm (mkVar t))::flst)
         | Aseg_p (t,m) ->
            mkOr
              (helper tail lastm ((mkEqSv t m)::flst))
              (helper tail (mkVar m) ([mkLte lastm (mkVar t);mkLtSv t m]@flst))
         | _ -> failwith "get_sorted_puref: Invalid input"
         end
    in

    let rec helper_entry arrPredlst flst =
      match arrPredlst with
      | [] -> mkAndlst flst
      | h::tail ->
         begin match h with
         | AsegNE_p (t,m) ->
            helper tail (mkVar m) ((mkLtSv t m)::flst)
         | Pointsto_p (t,v) ->
            helper tail (incOne (mkVar t)) flst
         | Aseg_p (t,m) ->
            mkOr
              (helper_entry tail ((mkEqSv t m)::flst))
              (helper tail (mkVar m) ((mkLtSv t m)::flst))
         | _ -> failwith "get_sorted_puref: Invalid input"
         end
    in
    helper_entry arrPredlst []
  in

  let helper_sv_to_exp uqset_eq sv =
    try
      let nu,ne=
        List.find (fun (u,e) -> is_same_sv u sv) uqset_eq
      in
      ne
    with Not_found ->
      mkVar sv
  in

  let rec helper orig_lhs_p ((lhs_p,lhs_h) as lhs) ((rhs_p,rhs_h) as rhs) vset uqset uqset_eq frame antiframe indent =
    
    let current_sv_to_exp = helper_sv_to_exp uqset_eq in
    let mkEqSv a b = mkEq (current_sv_to_exp a) (current_sv_to_exp b) in
    let mkLtSv a b = mkLt (current_sv_to_exp a) (current_sv_to_exp b) in
    let mkLteSv a b = mkLte (current_sv_to_exp a) (current_sv_to_exp b) in
    let mkGtSv a b = mkGt (current_sv_to_exp a) (current_sv_to_exp b) in
    let mkGteSv a b = mkGte (current_sv_to_exp a) (current_sv_to_exp b) in
    let norm_uqset = List.filter (fun v -> (List.exists (fun (nv,_) -> is_same_sv nv v) uqset_eq)) uqset in
    let uqset_eq_f = mkAndlst (List.map (fun (v,e) -> mkEq (mkVar v) e) uqset_eq) in
    
    let () =
      print_endline_verbose (""^(print_indent indent ((str_asegplusF lhs)^" |- "^(str_asegplusF rhs))))      
    in
    if not(isSat (mkAndlst (lhs_p@rhs_p)))
    then
      let norm = mkNormOr_base uqset_eq (mkNormBaseNeg norm_uqset vset orig_lhs_p) in
      (print_and_return (mkBExists (vset, (mkBBaseNeg lhs_p))) indent,norm)
    else
      match lhs_h, rhs_h with
      | (Aseg_p (la,lb))::ltail, _ ->
         let (uset,vsetprime) = mkUsetandVsetprime [la;lb] vset in
         let case1 = mkEqSv la lb in
         let case2 = mkLtSv la lb in
         let (f1,norm1) = helper orig_lhs_p (case1::lhs_p,ltail) rhs vsetprime uqset uqset_eq frame antiframe (indent+1) in
         let (f2,norm2) = helper orig_lhs_p (case2::lhs_p,(mkAsegNE_p la lb)::ltail) rhs vsetprime uqset uqset_eq frame antiframe (indent+1) in
         (print_and_return (mkBExists (uset,mkBAnd [f1;f2])) indent, combine_norm [norm1;norm2] [case1;case2] uset)
           
      | _ ,(Aseg_p (a,b))::rtail ->
         if false
         then
           failwith "TO BE IMPLEMENTED"
                    (* let (f1,norm1) = helper orig_lhs_p lhs ((mkEqSv a b)::rhs_p,rtail) vset frame antiframe (indent+1) in *)
                    (* let (f2,norm2) = helper orig_lhs_p lhs ((mkLtSv a b)::rhs_p,(mkAsegNE_p a b)::rtail) vset frame antiframe (indent+1) in *)
                    (* (print_and_return (BOr [f1;f2]) indent,mkNormOr [] [norm1;norm2]) *)
         else           
           let (uset,vsetprime) = mkUsetandVsetprime [a;b] vset in
           let case1 = mkEqSv a b in
           let case2 = mkLtSv a b in
           let case3 = mkGtSv a b in
           let (f1,norm1) = helper orig_lhs_p (case1::lhs_p,lhs_h) (rhs_p,rtail) vsetprime uqset uqset_eq frame antiframe (indent+1) in
           let (f2,norm2) = helper orig_lhs_p (case2::lhs_p,lhs_h) (rhs_p,(mkAsegNE_p a b)::rtail) vsetprime uqset uqset_eq frame antiframe (indent+1) in
           let (f3,norm3) = helper orig_lhs_p (case3::lhs_p,lhs_h) rhs vsetprime uqset uqset_eq frame antiframe (indent+1) in
           (print_and_return (mkBExists (uset,mkBAnd [f1;f2;f3])) indent,combine_norm [norm1;norm2;norm3] [case1;case2;case3] uset)

      | [], [] ->
         let frame = List.rev frame in
         let antiframe = List.rev antiframe in
         let norm = mkNormOr_base uqset_eq (mkNormBaseImply norm_uqset vset (uqset_eq_f::orig_lhs_p) rhs_p frame antiframe) in
         (print_and_return (mkBExists (vset, BBaseImply (lhs_p,rhs_p,frame,antiframe))) indent,norm)
      (* | [], (Aseg_p (ra,rb))::rtail -> *)
         
           
      | [], _ ->
         if !Globals.array_entailment
         then
           let norm = mkNormOr_base uqset_eq (mkNormBaseNeg norm_uqset vset orig_lhs_p) in
           (print_and_return (mkBExists (vset, (mkBBaseNeg lhs_p))) indent,norm)
         else
           let (f,norm) = helper orig_lhs_p lhs (rhs_p,[]) vset uqset uqset_eq frame (rhs_h@antiframe) (indent+1) in
           (print_and_return f indent,norm)

      | _, [] ->
         if !Globals.array_entailment
         then
           let norm = mkNormOr_base uqset_eq (mkNormBaseNeg norm_uqset vset orig_lhs_p) in
           (print_and_return (mkBExists (vset, (mkBBaseNeg lhs_p))) indent,norm)
         else
           let (f,norm) = helper orig_lhs_p (lhs_p,[]) rhs vset uqset uqset_eq (lhs_h@frame) antiframe (indent+1) in
           (print_and_return f indent,norm)
           
      | lh::ltail, rh::rtail ->
         ( match lh, rh with
           | Aseg_p _, _              
             | _, Aseg_p _->
              failwith "Aseg_p: Invalid cases"
                       
           | Pointsto_p (ls,lv),Pointsto_p (rs,rv) ->
              if is_same_sv ls rs
              then
                let f,norm = helper orig_lhs_p (lhs_p, ltail) ((mkEqSv lv rv)::rhs_p, rtail) vset uqset uqset_eq frame antiframe (indent+1) in
                (print_and_return f indent,norm)
              else
                let (uset,vsetprime) = mkUsetandVsetprime [ls;rs] vset in
                let case1 = mkEqSv ls rs in
                let case2 = mkLtSv ls rs in
                let case3 = mkGtSv ls rs in
                let f1,norm1 = helper orig_lhs_p (case1::lhs_p, lhs_h) (rhs_p, (mkPointsto_p ls rv)::rtail) vsetprime uqset uqset_eq frame antiframe (indent+1) in
                let f2,norm2 = helper orig_lhs_p (case2::lhs_p, ltail) rhs vsetprime uqset uqset_eq (lh::frame) antiframe (indent+1) in
                let f3,norm3 = helper orig_lhs_p (case3::lhs_p, lhs_h) (rhs_p,rtail) vsetprime uqset uqset_eq frame (rh::antiframe) (indent+1) in
                (print_and_return (mkBExists (uset, mkBAnd [f1;f2;f3])) indent,combine_norm [norm1;norm2;norm3] [case1;case2;case3] uset)

           | AsegNE_p (la,lb), AsegNE_p (ra,rb) ->              
              if is_same_sv la ra
              then
                let (uset,vsetprime) = mkUsetandVsetprime [lb;rb] vset in
                let case1 = mkGtSv rb lb in
                let case2 = mkLteSv rb lb in
                let f1,norm1 = helper orig_lhs_p (case1::lhs_p,ltail) (rhs_p, (mkAsegNE_p lb rb)::rtail) vsetprime uqset uqset_eq frame antiframe (indent+1) in
                let f2,norm2 = helper orig_lhs_p (case2::lhs_p,(mkAseg_p rb lb)::ltail) (rhs_p, rtail) vsetprime uqset uqset_eq frame antiframe (indent+1) in
                (print_and_return (mkBExists (uset, mkBAnd [f1;f2])) indent,combine_norm [norm1;norm2] [case1;case2] uset)
              else
                let (uset,vsetprime) = mkUsetandVsetprime [la;ra] vset in
                let case1 = (mkEqSv la ra) in
                let case2 = (mkLtSv la ra) in
                let case3 = (mkGtSv la ra) in
                let f1,norm1 = helper orig_lhs_p (case1::lhs_p, lhs_h) (rhs_p, (mkAsegNE_p la rb)::rtail) vsetprime uqset uqset_eq frame antiframe (indent+1) in
                let f2,norm2 = helper orig_lhs_p (case2::lhs_p, lhs_h) (rhs_p, (mkGap_p la ra)::rhs_h) vsetprime uqset uqset_eq frame antiframe (indent+1) in
                let f3,norm3 = helper orig_lhs_p (case3::lhs_p, (mkGap_p ra la)::lhs_h) (rhs_p, rhs_h) vsetprime uqset uqset_eq frame antiframe (indent+1) in
                (print_and_return (mkBExists (uset, mkBAnd [f1;f2;f3])) indent,combine_norm [norm1;norm2;norm3] [case1;case2;case3] uset)
                  
           | AsegNE_p (la,lb), Gap_p (ra,rb) ->
              if is_same_sv la ra
              then
                let (uset,vsetprime) = mkUsetandVsetprime [lb;rb] vset in
                let case1 = (mkLtSv lb rb) in
                let case2 = (mkGteSv lb rb) in
                let f1,norm1 = helper orig_lhs_p (case1::lhs_p, ltail) (rhs_p, rtail) vsetprime uqset uqset_eq (lh::frame) antiframe (indent+1) in
                let f2,norm2 = helper orig_lhs_p (case2::lhs_p, (Aseg_p (rb,lb))::ltail) (rhs_p, rtail) vsetprime uqset uqset_eq ((mkAsegNE_p la rb)::frame) antiframe (indent+1) in
                (print_and_return (mkBExists (uset, mkBAnd [f1;f2])) indent,combine_norm [norm1;norm2] [case1;case2] uset)
              else
                failwith "AsegNE v.s Gap: Not aligned"

           | Gap_p (la,lb), AsegNE_p (ra,rb)->
              if is_same_sv la ra
              then
                let (uset,vsetprime) = mkUsetandVsetprime [lb;rb] vset in
                let case1 = (mkGtSv lb rb) in
                let case2 = (mkLteSv lb rb) in
                let f1,norm1 = helper orig_lhs_p (case1::lhs_p, ltail) (rhs_p, rtail) vsetprime uqset uqset_eq frame ((mkAsegNE_p la rb)::antiframe) (indent+1) in
                let f2,norm2 = helper orig_lhs_p (case2::lhs_p, (Aseg_p (rb,lb))::ltail) (rhs_p, rtail) vsetprime uqset uqset_eq frame ((mkAsegNE_p la lb)::antiframe) (indent+1) in
                (print_and_return (mkBExists (uset, mkBAnd [f1;f2])) indent,combine_norm [norm1;norm2] [case1;case2] uset)
              else
                failwith "AsegNE v.s Gap: Not aligned"                                                  

           | Pointsto_p (ls,lv), Gap_p (ra,rb) ->
              if is_same_sv ls ra
              then
                let f,norm = helper orig_lhs_p (lhs_p,ltail) (rhs_p,rtail) vset uqset uqset_eq (lh::frame) antiframe (indent+1) in
                (print_and_return f indent,norm)
              else
                failwith "Pointsto_p v.s Gap: Not aligned"

           | Gap_p (la,lb), Pointsto_p (rs,rv) ->
              if is_same_sv la rs
              then
                let f,norm = helper orig_lhs_p (lhs_p,ltail) (rhs_p,rtail) vset uqset uqset_eq frame (rh::antiframe) (indent+1) in
                (print_and_return f indent,norm)
              else
                failwith "Gap v.s Pointsto_p: Not aligned"

           | AsegNE_p (la,lb), Pointsto_p (rs,rv) ->
              if is_same_sv la rs
              then
                let subst_case_var (NormOr lst) subs =
                  NormOr
                    (List.map
                       (fun (eset,clst,base)->
                         (eset,List.map (Cpure.subs_var_with_exp subs) clst,base))
                       lst
                    )
                in
                let fresh_c = global_get_new_var () in (* c=la+1 *)
                let fresh_u = global_get_new_var () in
                let c_exp = incOne (mkVar la) in                
                let eq_c_exp = mkEq (mkVar fresh_c) c_exp in
                let subst = [(fresh_c,c_exp)]in
                let f,norm = helper orig_lhs_p (eq_c_exp::lhs_p,([mkPointsto_p la fresh_u; mkAseg_p fresh_c lb]@ltail))
                                    (rhs_p,rhs_h) (vset) ([fresh_u;fresh_c]@uqset) ((fresh_c,c_exp)::uqset_eq) frame antiframe (indent+1) in
                (print_and_return (mkBForall ([fresh_u;fresh_c],f)) indent,subst_case_var norm subst)
              else
                let (uset,vsetprime) = mkUsetandVsetprime [la;rs] vset in
                let case1 = (mkEqSv la rs) in
                let case2 = (mkLtSv la rs) in
                let case3 = (mkGtSv la rs) in
                let f1,norm1 = helper orig_lhs_p (case1::lhs_p, lhs_h) (rhs_p, (mkPointsto_p la rv)::rtail) vsetprime uqset uqset_eq frame antiframe (indent+1) in
                let f2,norm2 = helper orig_lhs_p (case2::lhs_p, lhs_h) (rhs_p, (mkGap_p la rs)::rhs_h) vsetprime uqset uqset_eq frame antiframe (indent+1) in
                let f3,norm3 = helper orig_lhs_p (case3::lhs_p, (mkGap_p rs la)::lhs_h) (rhs_p, rhs_h) vsetprime uqset uqset_eq frame antiframe (indent+1) in
                (print_and_return (mkBExists (uset, mkBAnd [f1;f2;f3])) indent,combine_norm [norm1;norm2;norm3] [case1;case2;case3] uset)

           | Pointsto_p (ls,lv),AsegNE_p (ra,rb) ->
              if is_same_sv ls ra
              then
                let fresh_c = global_get_new_var () in
                let fresh_u = global_get_new_var () in
                let f,norm = (helper orig_lhs_p lhs
                                     ((mkEq (mkVar fresh_c) (incOne (mkVar ra)))::rhs_p,([mkPointsto_p ra fresh_u; mkAseg_p fresh_c rb]@rtail))
                                     ([fresh_c;fresh_u]@vset) uqset uqset_eq
                                     frame antiframe (indent+1))
                in
                (print_and_return f indent,norm)
              else
                let (uset,vsetprime) = mkUsetandVsetprime [ls;ra] vset in
                let case1 = (mkEqSv ls ra) in
                let case2 = (mkLtSv ls ra) in
                let case3 = (mkGtSv ls ra) in
                let f1,norm1 = helper orig_lhs_p (case1::lhs_p, lhs_h) (rhs_p, (mkAsegNE_p ls rb)::rtail) vsetprime uqset uqset_eq frame antiframe (indent+1) in
                let f2,norm2 = helper orig_lhs_p (case2::lhs_p, lhs_h) (rhs_p, (mkGap_p ls ra)::rhs_h) vsetprime uqset uqset_eq frame antiframe (indent+1) in
                let f3,norm3 = helper orig_lhs_p (case3::lhs_p, (mkGap_p ra ls)::lhs_h) (rhs_p, rhs_h) vsetprime uqset uqset_eq frame antiframe (indent+1) in
                (print_and_return (mkBExists (uset, BAnd [f1;f2;f3])) indent,combine_norm [norm1;norm2;norm3] [case1;case2;case3] uset)

           | Gap_p _, Gap_p _ ->
              failwith "Gap_p vs Gap_p: Invalid case"
         )
  in
  (* Both LHS and RHS are given some order *)
  let helper_entry (lhs_e,lhs_p,lhs_h) (rhs_e,rhs_p,rhs_h) =
    let new_lhs_p = (get_sorted_puref_general lhs_h)::lhs_p in
    let orig_rhs_p = (get_sorted_puref_general rhs_h)::rhs_p in
    let f,norm = helper lhs_p (new_lhs_p,lhs_h) (orig_rhs_p,rhs_h) rhs_e [] [] [] [] 0 in
    (mkBForall (lhs_e,f),norm,mkAndlst lhs_p)
  in

  let get_sat_perm orig_pure hlst =
    List.fold_left
      (fun r perm ->
        let perm_pure = get_sorted_puref_general perm in
        if isSat (mkAndlst (perm_pure::orig_pure))
        then (perm_pure,perm)::r
        else r)
      [] (generic_get_permutation hlst)
  in

  (* LHS is given some order *)
  let helper_lhs_sorted (lhs_e,lhs_p,lhs_h) (rhs_e,rhs_p,rhs_h) =
    let rhs_perm = generic_get_permutation rhs_h in
    match (List.map
             (fun item ->
               helper_entry (lhs_e,lhs_p,lhs_h) (rhs_e,rhs_p,item))
             rhs_perm ) with
    | [h] -> h
    | h::tail ->
       (List.fold_left
          (fun (rf,NormOr rnorm,rlhsp) (nf,NormOr nnorm,nlhsp) ->
            (mkBOr [rf;nf], NormOr (rnorm@nnorm),rlhsp)))
         h tail
    | [] -> failwith "helper_lhs_sorted: Empty output"
  in


  (* Neither side is given any order *)
  let helper_lhs_unsorted (lhs_e,lhs_p,lhs_h) (rhs_e,rhs_p,rhs_h) =
    let lhs_p = (get_segment_pure lhs_h)@lhs_p in                                           
    let disjoint_lhs_pure = get_disjoint_pure lhs_h in
    let (lhs_perm_pure,lhs_perm) = List.split (get_sat_perm lhs_p lhs_h) in
    let (flst,normlst,lhs_p_lst) = split_list_3
                                     (List.map
                                        (fun item ->
                                          helper_lhs_sorted (lhs_e,lhs_p,item)
                                                            (rhs_e,rhs_p,rhs_h))
                                        lhs_perm)
    in
    (mkBAnd flst,combine_norm normlst lhs_perm_pure [],mkAndlst (disjoint_lhs_pure::lhs_p))
  in
  let transAnte = new arrPredTransformer_orig lhs in
  let transConseq = new arrPredTransformer_orig rhs in
  helper_lhs_unsorted (transAnte#formula_to_general_formula) (transConseq#formula_to_general_formula)
;;


type partial_sort_pred =
  | MatchForm of (aseg_pred_plus * partial_sort_pred)
  | StarForm of (aseg_pred_plus list)
;;

let rec str_partial_sort_pred = function
  | MatchForm (head, tail) -> "# "^(str_aseg_pred_plus head)^" # ; "^(str_partial_sort_pred tail)
  | StarForm lst -> str_aseg_pred_plus_lst lst
;;


let mkMatchForm h tail =
  MatchForm (h, tail)
;;

let mkStarForm lst =
  StarForm lst
;;
               
  
type pre_condition =
  {
    antiframe : aseg_pred_plus list;
    frame : aseg_pred_plus list;
    uqset_eq : (Cpure.spec_var * Cpure.exp) list;
    (* binding universal variables *)
    norm_uqset : Cpure.spec_var list;
    vset : Cpure.spec_var list;
    uqset_eq_f : Cpure.formula;
  }
;;

let add_antiframe pre_cond h =
  { pre_cond with antiframe = h::(pre_cond.antiframe)}
;;

let add_frame pre_cond h =
  { pre_cond with frame = h::(pre_cond.frame)}
;;

let update_vset pre_cond vset =
  { pre_cond with vset = vset}
;;

let add_uqset_eq pre_cond new_uqset_eq =
  { pre_cond with uqset_eq = new_uqset_eq @ pre_cond.uqset_eq }
;;

let add_pure (newf, orig_f) inputf =
  (* let () = non_trivial := true in                             *)
  (inputf::newf, orig_f)
;;

let add_pure_lst (newf, orig_f) lst =
  (lst@newf, orig_f)
;;

let present_pure (newf, orig_f) =
  mkAndlst (newf@orig_f)
;;

let get_new_pure = fst
;;

let str_pair_f (newf, orig_f) =
  str_list !str_pformula newf
;;

let array_biabduction_partial_order (lhs_e_lst, lhs_p, lhs_h) (rhs_e_lst, rhs_p, rhs_h) =

  let get_sorted plst hlst =
    let enumerate hlst =
      let enum_helper item lst =
        let order_plst =
          match item with
          | Aseg_p (a, b) | AsegNE_p (a, b) | Gap_p (a, b) ->
             List.map
               (fun nitem ->
                 match nitem with
                 | Aseg_p (na, _) | AsegNE_p (na, _)
                   | Gap_p (na, _) | Pointsto_p (na, _) ->
                    mkLteSv b na)
               lst
          | Pointsto_p (a, _) ->
             List.map
               (fun nitem ->
                 match nitem with
                 | Aseg_p (na, _) | AsegNE_p (na, _)
                   | Gap_p (na, _) | Pointsto_p (na, _) ->
                    mkLtSv a na)
               lst
        in
        (order_plst, mkMatchForm item (mkStarForm lst))
      in
      let rec helper hlst head =
        match hlst with
        | h::tail ->
           let (new_plst, item) = enum_helper h (head@tail) in
           if not(isSat (mkAndlst (new_plst @ plst)))
           then helper tail (h::head)
           else (new_plst, item)::(helper tail (h::head))
        | [] -> []
      in
      helper hlst []
    in
    (enumerate hlst)
  in
  
  let rec base_case0 indent lhs_p rhs_p pre_cond =
    let frame = List.rev pre_cond.frame in
    let antiframe = List.rev pre_cond.antiframe in
    let upset_eq_v, uqset_eq_f = List.split (List.map (fun (v, e) -> (v, mkEq (mkVar v) e)) pre_cond.uqset_eq) in
    (* let () = print_endline ("uqset_eq_f: " ^ (str_list !str_pformula uqset_eq_f)) in *)
    let norm = mkNormOr_base pre_cond.uqset_eq (mkNormBaseImply pre_cond.norm_uqset pre_cond.vset uqset_eq_f (get_new_pure rhs_p) frame antiframe) in
    (print_and_return (mkBExists (pre_cond.vset, BBaseImply ([present_pure lhs_p],[present_pure rhs_p],frame,antiframe))) indent, norm)
      
  and base_case1 indent lhs_p (rhs_p, rh, rtail) pre_cond =
    match rh with
    | Aseg_p (a,b) ->
       let (uset,vsetprime) = mkUsetandVsetprime [a;b] pre_cond.vset in
       let case1 = mkEqSv a b in
       let case2 = mkLtSv a b in
       let case3 = mkGtSv a b in
       let f1, norm1 = aux_entry indent (add_pure lhs_p case1, mkStarForm []) (rhs_p, rtail) pre_cond in
       let f2, norm2 = aux_entry indent (add_pure lhs_p case2, mkStarForm []) (rhs_p, rtail) (add_antiframe pre_cond (mkAsegNE_p a b)) in
       let f3, norm3 = aux_entry indent (add_pure lhs_p case3, mkStarForm []) (rhs_p, rtail) pre_cond in
       (print_and_return (mkBExists (uset,mkBAnd [f1;f2;f3])) indent,combine_norm [norm1;norm2;norm3] [case1;case2;case3] uset)
    | _ ->
       (* base_case1 indent lhs_p (rhs_p, rtail) (add_antiframe pre_cond rh) *)
       aux_entry indent (lhs_p, mkStarForm []) (rhs_p, rtail) (add_antiframe pre_cond rh)
                 
                 
  and base_case2 indent (lhs_p, lh, ltail) rhs_p pre_cond =
    match lh with
    | Aseg_p (la, lb) ->
       let (uset,vsetprime) = mkUsetandVsetprime [la;lb] pre_cond.vset in
       let case1 = mkEqSv la lb in
       let case2 = mkLtSv la lb in
       let f1, norm1 = aux_entry indent (add_pure lhs_p case1, ltail) (rhs_p, mkStarForm []) pre_cond in
       let f2, norm2 = aux_entry indent (add_pure lhs_p case2, ltail) (rhs_p, mkStarForm []) (add_frame pre_cond (mkAsegNE_p la lb)) in
       (print_and_return (mkBExists (uset,mkBAnd [f1;f2])) indent, combine_norm [norm1;norm2] [case1;case2] uset)
    | _ ->
       (* base_case2 indent (lhs_p, ltail) rhs_p (add_frame pre_cond lh)  *)
       aux_entry indent (lhs_p, ltail) (rhs_p, mkStarForm []) (add_frame pre_cond lh)

  and aux_entry indent (lhs_p, lhs_h) (rhs_p, rhs_h) pre_cond =
    let () =
      (* let str_f pf hf = (str_pair_f pf) ^ "/\\ " ^ (str_partial_sort_pred hf) in *)
      let str_f pf hf = (str_partial_sort_pred hf) in
      print_endline_verbose (""^(print_indent indent ((str_f lhs_p lhs_h)^" |- "^(str_f rhs_p rhs_h))))
    in
    if false (* not(isSat (mkAnd (present_pure lhs_p) (present_pure rhs_p))) *)
    then
      let norm = mkNormOr_base [] (mkNormBaseNeg [] [] [mkFalse ()]) in
      (print_and_return (mkBExists (pre_cond.vset, (mkBBaseNeg ([present_pure lhs_p])))) indent,norm)
    else
      match lhs_h, rhs_h with
      | StarForm [], StarForm [] -> base_case0 indent lhs_p rhs_p pre_cond
      | StarForm [], StarForm (rh::rtail) -> base_case1 indent lhs_p (rhs_p, rh, mkStarForm rtail) pre_cond
      | StarForm [], MatchForm (rh, rtail) -> base_case1 indent lhs_p (rhs_p, rh, rtail) pre_cond
      | StarForm (lh::ltail), StarForm [] -> base_case2 indent (lhs_p, lh, mkStarForm ltail) rhs_p  pre_cond
      | MatchForm (lh, ltail), StarForm [] -> base_case2 indent (lhs_p, lh, ltail) rhs_p  pre_cond
      | StarForm l_lst, _->
         let (caselst, sorted_lhs_lst) =
           List.fold_left
             (fun (r_caselst, r_lhs_lst) (order_plst, sorted_lhs)->
               ((mkAndlst order_plst) :: r_caselst, (add_pure_lst  lhs_p order_plst, sorted_lhs)::r_lhs_lst))
             ([], []) (get_sorted [present_pure lhs_p] l_lst)
         in
         let (flst, normlst) = List.split (List.map (fun item -> aux_entry (indent+1) item (rhs_p, rhs_h) pre_cond) sorted_lhs_lst) in
         (mkBAnd flst, combine_norm normlst caselst [])
      | MatchForm _, StarForm r_lst ->
         let sorted_rhs_lst = List.map (fun (order_plst, hlst) -> (add_pure_lst rhs_p order_plst, hlst)) (get_sorted [present_pure rhs_p] r_lst) in
         begin match List.map (fun item -> aux_entry (indent+1) (lhs_p, lhs_h) item pre_cond) sorted_rhs_lst with (* can use aux_sorted directly *)
         | h :: tail ->
            (List.fold_left
               (fun (rf, NormOr rnorm) (nf, NormOr nnorm) ->
                 (mkBOr [rf; nf], NormOr (rnorm @ nnorm))))
              h tail
         | [] -> failwith "aux_lhs_sorted: Empty output" end
      | MatchForm _, MatchForm _ ->
         aux_sorted indent (lhs_p, lhs_h) (rhs_p, rhs_h) pre_cond
                    
  and aux_sorted indent (lhs_p, lhs_h) (rhs_p, rhs_h) pre_cond =
    let (lh, ltail), (rh, rtail) = match lhs_h, rhs_h with
      | MatchForm (lh, ltail), MatchForm (rh, rtail) -> (lh, ltail), (rh, rtail)
      | _ -> failwith "aux_sorted: Invalid input"
    in
    (* let () = *)
    (*   let str_f pf hf = "sorted:: " ^ (str_list !str_pformula pf) ^ "/\\ " ^ (str_partial_sort_pred hf) in *)
    (*   print_endline_verbose (""^(print_indent indent ((str_f lhs_p lhs_h)^" |- "^(str_f rhs_p rhs_h)))) *)
    (* in *)
    match lh, rh with
    | Aseg_p (la, lb), _ ->
       let (uset,vsetprime) = mkUsetandVsetprime [la; lb] pre_cond.vset in
       let case1 = mkEqSv la lb in
       let case2 = mkLtSv la lb in
       let f1, norm1 = aux_entry (indent+1) (add_pure lhs_p case1, ltail) (rhs_p, rhs_h) pre_cond in
       let f2, norm2 = aux_entry (indent+1) (add_pure lhs_p case2, mkMatchForm (mkAsegNE_p la lb) ltail) (rhs_p, rhs_h) pre_cond in
       (print_and_return (mkBExists (uset, mkBAnd [f1; f2])) indent, combine_norm [norm1; norm2] [case1; case2] uset)
      
    | _, Aseg_p (a, b) ->
       let (uset,vsetprime) = mkUsetandVsetprime [a; b] pre_cond.vset in
       let case1 = mkEqSv a b in
       let case2 = mkLtSv a b in
       let case3 = mkGtSv a b in
       let pre_cond = update_vset pre_cond vsetprime in
       let f1, norm1 = aux_entry (indent+1) (add_pure lhs_p case1, lhs_h) (rhs_p, rtail) pre_cond in
       let f2, norm2 = aux_entry (indent+1) (add_pure lhs_p case2, lhs_h) (rhs_p, mkMatchForm (mkAsegNE_p a b) rtail) pre_cond in
       let f3, norm3 = (mkBExists (pre_cond.vset, (mkBBaseNeg ([present_pure lhs_p]))), mkNormOr_base [] (mkNormBaseNeg [] [] [mkFalse ()])) in
       (print_and_return (mkBExists (uset,mkBAnd [f1; f2; f3])) indent,combine_norm [norm1; norm2; norm3] [case1; case2; case3] uset)
      
    | Pointsto_p (ls, lv), Pointsto_p (rs, rv) ->
       if is_same_sv ls rs
       then
         (* let f,norm = helper orig_lhs_p (lhs_p, ltail) ((mkEqSv lv rv)::rhs_p, rtail) vset uqset uqset_eq frame antiframe (indent+1) in *)
         let f, norm = aux_entry indent (lhs_p, ltail) (add_pure rhs_p (mkEqSv lv rv), rtail) pre_cond in
         (print_and_return f indent,norm)
       else
         let (uset,vsetprime) = mkUsetandVsetprime [ls;rs] pre_cond.vset in
         let case1 = mkEqSv ls rs in
         let case2 = mkLtSv ls rs in
         let case3 = mkGtSv ls rs in
         let pre_cond = update_vset pre_cond vsetprime in
         let f1, norm1 = aux_entry indent (add_pure lhs_p case1, ltail) (add_pure rhs_p (mkEqSv lv rv), rtail) pre_cond in
         let f2, norm2 = aux_entry indent (add_pure lhs_p case2, ltail) (rhs_p, mkMatchForm rh rtail) (add_frame pre_cond lh) in
         let f3, norm3 = aux_entry indent (add_pure lhs_p case3, mkMatchForm lh ltail) (rhs_p, rtail) (add_antiframe pre_cond rh) in
         (print_and_return (mkBExists (uset, mkBAnd [f1; f2; f3])) indent, combine_norm [norm1; norm2; norm3] [case1; case2; case3] uset)

    | AsegNE_p (la,lb), AsegNE_p (ra,rb) ->
       if is_same_sv la ra
       then
         let (uset,vsetprime) = mkUsetandVsetprime [lb; rb] pre_cond.vset in
         let case1 = mkGtSv rb lb in
         let case2 = mkLtSv rb lb in
         let case3 = mkEqSv rb lb in
         let pre_cond = update_vset pre_cond vsetprime in
         let f1, norm1 = aux_entry (indent+1) (add_pure lhs_p case1, ltail) (rhs_p, mkMatchForm (mkAsegNE_p lb rb) rtail) pre_cond in
         let f2, norm2 = aux_entry (indent+1) (add_pure lhs_p case2, mkMatchForm (mkAsegNE_p rb lb) ltail) (rhs_p, rtail) pre_cond in
         let f3, norm3 = aux_entry (indent+1) (add_pure lhs_p case3, ltail) (rhs_p, rtail) pre_cond in
         (print_and_return (mkBExists (uset, mkBAnd [f1; f2])) indent,combine_norm [norm1; norm2; norm3] [case1; case2; case3] uset)
       else
         let (uset,vsetprime) = mkUsetandVsetprime [la;ra] pre_cond.vset in
         let case1 = (mkEqSv la ra) in
         let case2 = (mkLtSv la ra) in
         let case3 = (mkGtSv la ra) in
         let pre_cond = update_vset pre_cond vsetprime in
         let f1, norm1 = aux_entry (indent+1) (add_pure lhs_p case1, mkMatchForm lh ltail) (rhs_p, mkMatchForm (mkAsegNE_p la rb) rtail) pre_cond in
         let f2, norm2 = aux_entry (indent+1) (add_pure lhs_p case2, mkMatchForm lh ltail) (rhs_p, mkMatchForm (mkGap_p la ra) (mkMatchForm rh rtail)) pre_cond in
         let f3, norm3 = aux_entry (indent+1) (add_pure lhs_p case3, mkMatchForm (mkGap_p ra la) (mkMatchForm lh ltail)) (rhs_p, mkMatchForm rh rtail) pre_cond in
         (print_and_return (mkBExists (uset, mkBAnd [f1; f2; f3])) indent, combine_norm [norm1; norm2; norm3] [case1; case2; case3] uset)

    | AsegNE_p (la,lb), Gap_p (ra,rb) ->
       if is_same_sv la ra
       then
         let (uset,vsetprime) = mkUsetandVsetprime [lb; rb] pre_cond.vset in
         let case1 = (mkLteSv lb rb) in
         let case2 = (mkGtSv lb rb) in
         let pre_cond = update_vset pre_cond vsetprime in
         let f1, norm1 = aux_entry (indent+1) (add_pure lhs_p case1, ltail) (rhs_p, rtail) (add_frame pre_cond lh) in
         let f2, norm2 = aux_entry (indent+1) (add_pure lhs_p case2, mkMatchForm (mkAsegNE_p rb lb) ltail) (rhs_p, rtail) (add_frame pre_cond (mkAsegNE_p la rb)) in
         (print_and_return (mkBExists (uset, mkBAnd [f1; f2])) indent,combine_norm [norm1; norm2] [case1; case2] uset)
       else
         failwith "AsegNE v.s Gap: Not aligned"

    | Gap_p (la,lb), AsegNE_p (ra,rb)->
       if !Globals.array_entailment_frame
       then
         let norm = mkNormOr_base [] (mkNormBaseNeg [] [] [mkFalse ()]) in
         (print_and_return (mkBExists (pre_cond.vset, (mkBBaseNeg ([present_pure lhs_p])))) indent,norm)
       else if is_same_sv la ra
       then
         let (uset,vsetprime) = mkUsetandVsetprime [lb; rb] pre_cond.vset in
         let case1 = (mkGteSv lb rb) in
         let case2 = (mkLtSv lb rb) in
         let pre_cond = update_vset pre_cond vsetprime in
         let f1, norm1 = aux_entry (indent+1) (add_pure lhs_p case1, ltail) (rhs_p, rtail) (add_antiframe pre_cond (mkAsegNE_p la rb)) in
         let f2, norm2 = aux_entry (indent+1) (add_pure lhs_p case2, ltail) (rhs_p, mkMatchForm (mkAsegNE_p lb rb) rtail) (add_frame pre_cond (mkAsegNE_p la rb)) in
         (print_and_return (mkBExists (uset, mkBAnd [f1; f2])) indent,combine_norm [norm1; norm2] [case1; case2] uset)
       else
         failwith "AsegNE v.s Gap: Not aligned"

    | Pointsto_p (ls,lv), Gap_p (ra,rb) ->
       if is_same_sv ls ra
       then
         let f, norm = aux_entry (indent+1) (lhs_p, ltail) (rhs_p, rtail) (add_frame pre_cond lh) in
         (print_and_return f indent,norm)
       else
         failwith "Pointsto_p v.s Gap: Not aligned"

    | Gap_p (la,lb), Pointsto_p (rs,rv) ->
       if !Globals.array_entailment_frame
       then
         let norm = mkNormOr_base [] (mkNormBaseNeg [] [] [mkFalse ()]) in
         (print_and_return (mkBExists (pre_cond.vset, (mkBBaseNeg ([present_pure lhs_p])))) indent,norm)
       else if is_same_sv la rs
       then
         let f, norm = aux_entry (indent+1) (lhs_p, ltail) (rhs_p, rtail) (add_antiframe pre_cond rh) in
         (print_and_return f indent,norm)
       else
         failwith "Gap v.s Pointsto_p: Not aligned"

    | AsegNE_p (la,lb), Pointsto_p (rs,rv) ->
       if is_same_sv la rs
       then
         let subst_case_var (NormOr lst) subs =
           NormOr
             (List.map
                (fun (eset,clst,base)->
                  let new_base = match base with
                    | NormBaseImply (nuset, ueset, nlhsp, nrhsp, nframe, nantiframe) ->
                       (* let new_nlhsp = List.map (Cpure.subs_var_with_exp subs) nlhsp in *)
                       let new_nrhsp = List.map (Cpure.subs_var_with_exp subs) nrhsp in
                       NormBaseImply (nuset, ueset, nlhsp, new_nrhsp, nframe, nantiframe)
                    | NormBaseNeg (nuset, neset, pflst) ->
                       NormBaseNeg (nuset, neset, List.map (Cpure.subs_var_with_exp subs) pflst)
                  in
                  (eset,List.map (Cpure.subs_var_with_exp subs) clst,base))
                lst
             )
         in
         let fresh_c = global_get_new_var () in (* c=la+1 *)
         let fresh_u = global_get_new_var () in
         let c_exp = incOne (mkVar la) in
         let eq_c_exp = mkEq (mkVar fresh_c) c_exp in
         let subst = [(fresh_c, c_exp)] in
         let new_point_to = mkPointsto_p la fresh_u in
         let new_aseg = mkAseg_p fresh_c lb in
         let pre_cond = add_uqset_eq pre_cond subst in
         let f, norm = aux_entry (indent + 1) (add_pure lhs_p eq_c_exp, mkMatchForm new_point_to (mkMatchForm new_aseg ltail)) (rhs_p, rhs_h) pre_cond in
         (print_and_return (mkBForall ([fresh_u; fresh_c], f)) indent, subst_case_var norm subst)
       else
         let (uset,vsetprime) = mkUsetandVsetprime [la;rs] pre_cond.vset in
         let case1 = (mkEqSv la rs) in
         let case2 = (mkLtSv la rs) in
         let case3 = (mkGtSv la rs) in
         let pre_cond = update_vset pre_cond vsetprime in
         let f1, norm1 = aux_entry (indent+1) (add_pure lhs_p case1, lhs_h) (rhs_p, mkMatchForm (mkPointsto_p la rv) rtail) pre_cond in
         let f2, norm2 = aux_entry (indent+1) (add_pure lhs_p case2, lhs_h) (rhs_p, mkMatchForm (mkGap_p la rs) rhs_h) pre_cond in
         let f3, norm3 = aux_entry (indent+1) (add_pure lhs_p case3, mkMatchForm (mkGap_p rs la) lhs_h) (rhs_p, rhs_h) pre_cond in
         (print_and_return (mkBExists (uset, mkBAnd [f1;f2;f3])) indent,combine_norm [norm1;norm2;norm3] [case1;case2;case3] uset)
                  
    | Pointsto_p (ls,lv),AsegNE_p (ra,rb) ->
       if is_same_sv ls ra
       then
         let fresh_c = global_get_new_var () in
         let fresh_u = global_get_new_var () in
         let eq_pure = mkEq (mkVar fresh_c) (incOne (mkVar ra)) in
         let rhs_point_to = mkPointsto_p ra fresh_u in
         let rhs_aseg = mkAseg_p fresh_c rb in
         let pre_cond = update_vset pre_cond ([fresh_c;fresh_u]@pre_cond.vset) in
         let f, norm = aux_entry (indent+1) (lhs_p, lhs_h) (add_pure rhs_p eq_pure, mkMatchForm rhs_point_to (mkMatchForm rhs_aseg rtail)) pre_cond in
         (print_and_return f indent,norm)
       else
         let (uset,vsetprime) = mkUsetandVsetprime [ls;ra] pre_cond.vset in
         let case1 = (mkEqSv ls ra) in
         let case2 = (mkLtSv ls ra) in
         let case3 = (mkGtSv ls ra) in
         let pre_cond = update_vset pre_cond vsetprime in
         let f1, norm1 = aux_entry (indent+1) (add_pure lhs_p case1, (mkMatchForm lh ltail)) (rhs_p, (mkMatchForm (mkAsegNE_p ls rb) rtail)) pre_cond in
         let f2, norm2 = aux_entry (indent+1) (add_pure lhs_p case2, (mkMatchForm lh ltail)) (rhs_p, mkMatchForm (mkGap_p ls ra) (mkMatchForm rh rtail)) pre_cond in
         let f3, norm3 = aux_entry (indent+1) (add_pure lhs_p case3, (mkMatchForm (mkGap_p ra ls) (mkMatchForm lh ltail))) (rhs_p, mkMatchForm rh rtail) pre_cond in
         (print_and_return (mkBExists (uset, BAnd [f1; f2; f3])) indent,combine_norm [norm1;norm2;norm3] [case1;case2;case3] uset)

    | Gap_p _, Gap_p _ ->
       failwith "Gap_p vs Gap_p: Invalid case"    
  in

  let initial_pre_cond =
    {
      antiframe = [];
      frame = [];
      uqset_eq = [];
      norm_uqset = [];
      vset = rhs_e_lst;
      uqset_eq_f = mkTrue ();
    }
  in
  (* let lhs_p_lst = (get_segment_pure lhs_h_lst)@lhs_p_lst in *)
  (* let rhs_p_lst = (get_segment_pure rhs_h_lst)@rhs_p_lst in *)
  (* let f, norm = (aux_wrap_orig_pure lhs_p_lst) 0 (lhs_p_lst, mkStarForm lhs_h_lst) (rhs_p_lst, mkStarForm rhs_h_lst) initial_pre_cond in *)
(* (f, norm, mkAndlst ((get_disjoint_pure lhs_h_lst)::lhs_p_lst)) *)
  aux_entry 0 (lhs_p, lhs_h) (rhs_p, rhs_h) initial_pre_cond
;;

(* norm: normalized pre-condition, in the form of (Exists V0:forall V1:Exists V2: f*)
let extract_anti_frame_and_frame norm =
  let neg_to_pure eset clst base base_uset base_eset pflst =
    (mkExists eset
              (mkAndlst
                 (clst@
                    [(mkForall base_uset
                               (mkExists base_eset
                                         (mkNot
                                            (mkAndlst pflst))))])))
  in

  let extract_helper lst =    
    let rec merge_result imply_lst_after_removed_uv =
      let merge_helper (eset,lhs_p,rhs_p,afpure,antiframe,frame) lst =
        let (to_merge,rest)=
          List.partition
            (fun ((neset,_,_,_,nantiframe,nframe) as item) ->
              (compare_sv_lst eset neset) && (compare_asegPredplus_lst frame nframe) && (compare_asegPredplus_lst antiframe nantiframe))
            lst
        in
        ((fun (eset,lhs_p,rhs_p,pure,antiframe,frame) ->
          (eset,lhs_p,rhs_p,simplify_p pure,antiframe,frame))
           (List.fold_left
              (fun (reset,rlhs_p,rrhs_p,rpure,rantiframe,rframe) (neset,nlhs_p,nrhs_p,npure,nantiframe,nframe) ->
                (reset,rlhs_p,rrhs_p,mkOr rpure npure,rantiframe,rframe))
              (eset,lhs_p,rhs_p,afpure,antiframe,frame) to_merge),
         rest)
      in
      match imply_lst_after_removed_uv with
      | h::tail ->
         let (newh,rest) = merge_helper h tail in
         newh::(merge_result rest)
      | [] -> []
    in
    
    let remove_uv eset clst (iuset,ieset,lhs_p,rhs_p,frame,antiframe) =
      let inner_pure =
        (mkForall
           iuset
           (mkExists
              ieset
              (mkImply (mkAndlst lhs_p) (mkAndlst rhs_p))))
      in
      if isSat inner_pure && true
      then
        let anti_frame_pure =
          (* let f = get_gist (mkExists iuset (mkAndlst (clst@rhs_p))) (mkAndlst lhs_p) in *)
          let f = (mkExists iuset (mkAndlst (clst@rhs_p))) in
          f
        in
        Some (eset@ieset,lhs_p,rhs_p,anti_frame_pure,frame,antiframe)
      else
        None
    in

    let remove_aseg pure hlst =
      List.rev
        (List.fold_left
           (fun r item ->
             match item with
             | Aseg_p (a,b) ->
                if isValid (mkImply pure (mkEqSv a b))
                then r
                else item::r
             | _ -> item ::r)
           [] hlst)
    in
        
    let norm_imply_to_antiframe_frame (eset,lhs_p,rhs_p,afpure,frame,antiframe) =
      let state_pure = simplify (mkAndlst (afpure::lhs_p)) in
      let norm_af = (eset,afpure,remove_aseg state_pure antiframe) in
      let frame_pure = state_pure in
      let norm_f = (eset,frame_pure,remove_aseg state_pure frame) in
      (norm_af,norm_f)
    in
    
    let (imply,neg) =
      List.fold_left
        (fun (ir,nr) (eset,clst,base) ->
          match base with
          | NormBaseNeg (iuset,ieset,pf)-> (ir,(mkOr (neg_to_pure eset clst base iuset ieset pf) nr))
          | NormBaseImply (iuset,ieset,lhs_p,rhs_p,frame,antiframe) ->
             ( match remove_uv eset clst (iuset,ieset,lhs_p,rhs_p,frame,antiframe) with
               | Some norm_imply ->
                  (norm_imply::ir,nr)
               | None -> (ir,nr)
             )
        )
        ([],mkFalse ()) lst
    in
    (List.map norm_imply_to_antiframe_frame (merge_result imply),neg)
  in
  match norm with
  | NormOr lst ->
     extract_helper lst
;;

      

(* From asegPlus to h_formula *)
let arr_pred_plus_to_h_formula ?(root=None) hflst =  
  let one_arr_pred_plus_to_h_formula p =
    let basePtr =
      match root with
      | Some base -> base
      | None -> mkSV "base" in
    match p with
    | AsegNE_p (s,e) ->
       mkViewNode basePtr "AsegNE" [s;e]
    | Aseg_p (s,e) ->
       mkViewNode basePtr "Aseg" [s;e]
    | Pointsto_p (s,v) ->
       mkViewNode basePtr "Elem" [s;v]
    | _ -> failwith "arrPredPlus_to_h_formula: TO BE IMPLEMENTED"
  in
  let construct_h_formula plst =
    match (List.map one_arr_pred_plus_to_h_formula plst) with
    | h::tail -> Some (List.fold_left (fun r itemh -> mkStarH itemh r) h tail)
    | [] -> None
  in
  construct_h_formula hflst
;;


let construct_context_lst aflst neg =
  let construct_helper_imply ((aeset,apf,ahlst),(feset,fpf,phlst)) =
    let es = mkEmptyes () in
    let h_antiframe_lst =
      match arr_pred_plus_to_h_formula ahlst with
      | Some nh -> [nh]
      | None -> []
    in
    let h_frame =
      match arr_pred_plus_to_h_formula phlst with
      | Some nh -> nh
      | None -> HEmp
    in
    let () = y_tinfo_pp ("h_frame:"^(!Cformula.print_h_formula h_frame)) in
    let state =
      if List.length feset = 0
      then
        construct_base h_frame fpf
      else
        construct_exists h_frame fpf feset
    in
    let infer_pure = simplify (mkExists aeset apf) in
    mkCtx
      {es with
        es_formula = state ;
        es_infer_heap = h_antiframe_lst;
        es_infer_pure = [infer_pure];
      }
  in
  let construct_helper_neg pf =
    let es = mkEmptyes () in
    mkCtx
      {es with
        es_formula = construct_false ();
        es_infer_pure = [pf];
      }
  in
  let imply_ctx = List.map construct_helper_imply aflst in
  let neg_ctx = construct_helper_neg neg in
  if !Globals.array_entailment_frame
  then imply_ctx
  else
    if List.length imply_ctx > 0 && isFalse neg
    then imply_ctx
    else
      if List.length imply_ctx > 0
      then neg_ctx::imply_ctx
      else
        [neg_ctx]
;;

let merge_context_lst_for_frame clst lhs_p =
  match clst with
  | (Cformula.Ctx h)::tail ->
     let ctx =
       let (infer_f,state_f) =
         List.fold_left
           (fun (infer_f,state_f) item ->
             match item with
             | Cformula.Ctx es ->
                (mkOr infer_f (mkAndlst es.es_infer_pure),mkCformulaOr state_f es.es_formula)
             | _ -> failwith "merge_context_lst_for_frame: TO BE IMPLEMENTED")
           (mkAndlst h.Cformula.es_infer_pure,h.Cformula.es_formula) tail
       in
       let infer_f =  infer_f in
       let () = y_binfo_pp ("check frame "^(!str_pformula infer_f)) in
       let () = y_binfo_pp ("check frame "^(!str_pformula lhs_p)) in
       if isValid (simplify (mkImply lhs_p infer_f))
       then
         let () = y_binfo_pp ("check frame VALID") in
         let es = mkEmptyes () in
         (* Cformula.SuccCtx [Ctx {es with es_formula = state_f}] *)
         mkSuccCtx clst(* [(mkOCtx clst)] *)
       else
         mkEmptyFailCtx ()
     in
     let () = y_tinfo_pp ("List context: " ^(!Cformula.print_list_context ctx)) in
     ctx
  | _ -> mkEmptyFailCtx ()
;;

let rec merge_aseg_lst pf hlst =
  let is_eq v1 v2 =
    isValid (mkImply pf (mkEqSv v1 v2))
  in
  let rec helper_entry hlst =
    match hlst with
    | h :: tail ->
       begin match h with
       | AsegNE_p _ | Aseg_p _-> helper [] h tail
       | _-> h :: (helper_entry tail) end
    | [] -> []

  and helper head target hlst =
    match target with
    | AsegNE_p (ta, tb) ->
       begin match hlst with
       | h :: tail ->
          begin match h with
          | AsegNE_p (a, b) | Aseg_p (a, b) ->
             if is_eq tb a
             then
               helper_entry ((mkAsegNE_p ta b)::(head@tail))
             else if is_eq b ta
             then
               helper_entry ((mkAsegNE_p a tb)::(head@tail))
             else
               helper (h::head) target tail             
          | _ -> helper (h::head) target tail end
       | [] -> target::(helper_entry head) end
    | Aseg_p (ta, tb) ->
       begin match hlst with
       | h :: tail ->
          begin match h with
          | AsegNE_p (a, b) ->
             if is_eq tb a
             then
               helper_entry ((mkAsegNE_p ta b)::(head@tail))
             else if is_eq b ta
             then
               helper_entry ((mkAsegNE_p a tb)::(head@tail))
             else
               helper (h::head) target tail
          | Aseg_p (a, b) ->
             if is_eq tb a
             then
               helper_entry ((mkAseg_p ta b)::(head@tail))
             else if is_eq b ta
             then
               helper_entry ((mkAseg_p a tb)::(head@tail))
             else
               helper (h::head) target tail             
          | _ -> helper (h::head) target tail end
       | [] -> target::(helper_entry head) end
    | _ -> failwith "merge_aseg_lst: Invalid input"
  in
  helper_entry hlst
;;
         
    
         
                        
  
let valid_classical_entailment lhs implylst neg =
  isValid
    (mkImply
       lhs
       (List.fold_left
          (fun r ((aeset,afpure,antiframe),(eset,fpure,frame)) ->
            if List.length frame = 0 && List.length antiframe = 0
            then mkOr (mkExists aeset afpure) r
            else failwith "valid_classical_entailment: Invalid input")
          neg implylst))
;;

let drop_antiframe implylst =
  List.filter
    (fun ((aeset,afp,antiframe),(eset,fp,frame)) ->
      List.length antiframe = 0 (* && isValid (mkExists aeset afp) *))
    implylst
;;

let array_entailment_biabduction_get_norm (lhs_e, lhs_p, lhs_h) (rhs_e, rhs_p, rhs_h) =
  (* let () = print_endline_verbose ("=========== input LHS formula ==============") in *)
  (* let () = print_endline_verbose (!str_cformula lhs) in *)
  (* let () = print_endline_verbose ("=========== input RHS formula ==============") in *)
  (* let () = print_endline_verbose (!str_cformula rhs) in *)

  let (f,norm) = 
    if !Globals.array_full_order
    then
      (* array_entailment_biabduction_norm (lhs_p, lhs_h) (rhs_p, rhs_h) *)
      failwith "TO BE IMPLEMENTED"
    else
      array_biabduction_partial_order (lhs_e, lhs_p, lhs_h) (rhs_e, rhs_p, rhs_h)
  in
  let () = print_endline_verbose ("=========== formatted pre-condition ==============") in
  (* let () = print_endline_verbose (str_pre_condition f) in *)
  let () = print_endline_verbose ("=========== Normalized pre-condition ==============") in
  let () = print_endline_verbose (str_norm_pre_condition norm) in
  (* let simp_norm = simplify_norm_pre_condition norm in *)
  let simp_norm = norm in
  (f,simp_norm)    
;;

let trans_array_formula cf =
  let transF = new arrPredTransformer_orig cf in
  let (elst, plst, hlst) = transF#formula_to_general_formula in
  let hlst = merge_aseg_lst (mkAndlst plst) hlst in
  (transF#get_root, elst, (get_segment_pure hlst) @ [get_disjoint_pure hlst] @ plst, hlst)
;;

let norm_to_pure_for_classical_entailment (NormOr lst) rhs =
  (* let () = print_endline ("norm_to_pure_for_classical_entailment: here") in *)
  let helper_norm_pre_condition_base = function
    | NormBaseImply (uset, eset, lhs_p, rhs_p, frame, antiframe) ->
       if List.length frame > 0 || List.length antiframe > 0
       then None
       else
         Some (eset, mkAndlst rhs_p)
    | NormBaseNeg _ -> None
  in
  let f =
    mkOrlst
      ( List.fold_left
          (fun r (elst, clst, p) ->
            match helper_norm_pre_condition_base p with
            | Some (ne, np) -> (mkExists (elst@ne) (mkAndlst ([np; rhs] @ clst))) :: r
            | None -> r )
          [] lst )
  in
  (* let () = print_endline ("norm to pure " ^ (!str_pformula f)) in *)
  f
;;

let check_norm_validity norm lhs_p rhs_p =
  (* let () = print_endline "check_norm_validity" in *)
  (* let () = print_endline (!str_pformula lhs_p) in *)
  (* let () = print_endline (!str_pformula rhs_p) in *)
  (* Why isValid is not working? *)

  (isValid (mkImply lhs_p (norm_to_pure_for_classical_entailment norm rhs_p)))
  (* (imply lhs_p rhs_p) && *)
(* (imply lhs_p (norm_to_pure_for_classical_entailment norm rhs_p)) *)
;;

(* let array_entailment_classical_entailment_interface lhs rhs = *)
(*   let (f,simp_norm,lhs_p) = array_entailment_biabduction_get_norm lhs rhs in *)
(*   let (implylst,neg) = extract_anti_frame_and_frame simp_norm in *)
  
(*   (\* if valid_classical_entailment (mkTrue ()) implylst neg *\) *)
(*   if check_validity f *)
(*   then *)
(*     mkEmptySuccCtx () *)
(*   else *)
(*     mkEmptyFailCtx () *)
(* ;; *)

let array_entailment_classical_entailment_interface lhs rhs =
  let (lhs_root, lhs_e, lhs_p, lhs_h) = trans_array_formula lhs in
  let (rhs_root, rhs_e, rhs_p, rhs_h) = trans_array_formula rhs in
  (* Instantiate root *)
  let rhs_p =
    match lhs_root, rhs_root with
    | Some base1, Some base2 -> (mkEqSv base1 base2)::rhs_p
    | _, _ -> rhs_p
  in
  let (f, norm) = array_entailment_biabduction_get_norm (lhs_e, ([], lhs_p), mkStarForm lhs_h) (rhs_e, ([], rhs_p), mkStarForm rhs_h) in
  if check_norm_validity norm (mkAndlst lhs_p) (mkAndlst rhs_p)
  then
    mkEmptySuccCtx ()
  else
    mkEmptyFailCtx ()
;;
  
let array_entailment_biabduction_interface lhs rhs =
  failwith "TO BE IMPLEMENTED"
  (* let (f,simp_norm,_) = array_entailment_biabduction_get_norm lhs rhs in *)
  (* let (implylst,neg) = extract_anti_frame_and_frame simp_norm in *)
  (* mkSuccCtx (construct_context_lst implylst neg) *)
(* (true, mkEmptySuccCtx (),[]) *)
;;

let norm_to_pure_for_frame (NormOr lst) rhs =
  (* let () = print_endline ("norm_to_pure_for_classical_entailment: here") in *)
  let helper_norm_pre_condition_base = function
    | NormBaseImply (uset, eset, lhs_p, rhs_p, frame, antiframe) ->
       if List.length antiframe > 0
       then None
       else
         Some (eset, mkAndlst rhs_p)
    | NormBaseNeg _ -> None
  in
  let f =
    mkOrlst
      ( List.fold_left
          (fun r (elst, clst, p) ->
            match helper_norm_pre_condition_base p with
            | Some (ne, np) -> (mkExists (elst@ne) (mkAndlst ([np; rhs] @ clst))) :: r
            | None -> r )
          [] lst )
  in
  let () = print_endline ("norm to pure " ^ (!str_pformula f)) in
  f
;;

let extract_frame root (NormOr lst) lhs_p rhs_p=
  let extract_one_frame (elst, clst, norm_base) =
    match norm_base with      
    | NormBaseImply (iuset, ieset, ilhs_p, irhs_p, frame, antiframe) ->
       (* lhs_p is the formula for new introduced variables when unfolding LHS *)
       (* And need to add the uqset_eq *)
       if List.length antiframe > 0
       then None
       else
         let raw_state_pure = mkAndlst ([lhs_p; rhs_p] @ (ilhs_p @ (clst @ irhs_p))) in
         (* let () = print_endline ("raw_state_pure: " ^ (!str_pformula raw_state_pure)) in *)
         let state_pure = simplify raw_state_pure in
         (* let () = print_endline ("state_pure: " ^ (!str_pformula state_pure)) in *)
         if isSat state_pure
         then
           let new_elst = elst @ ieset in
           let h_frame =
             match arr_pred_plus_to_h_formula ~root:root frame with
             | Some nh -> nh
             | None -> HEmp
           in
           let state =
             if true (* List.length new_elst = 0 *)
             then construct_base h_frame state_pure
             else construct_exists h_frame state_pure new_elst
           in
           let ctx = (mkCtx
                        {(mkEmptyes ()) with
                          es_formula = state;
                     })
           in
           (* let () = print_endline ("ctx " ^ (!str_context ctx)) in *)
           Some ctx
         else
           None
    | NormBaseNeg _ -> None
  in
  mkSuccCtx (List.fold_left (fun r item ->
                 match extract_one_frame item with
                 | None -> r
                 | Some ctx -> ctx::r) [] lst)
;;


let array_entailment_frame_interface lhs rhs =
  let (lhs_root, lhs_e, lhs_p, lhs_h) = trans_array_formula lhs in
  let (rhs_root, rhs_e, rhs_p, rhs_h) = trans_array_formula rhs in
  
  let rhs_p =
    match lhs_root, rhs_root with
    | Some base1, Some base2 ->
       let () = print_endline "here" in
       (mkEqSv base1 base2)::rhs_p
    | _, _ -> rhs_p
  in
  let (f, norm) = array_entailment_biabduction_get_norm (lhs_e, ([], lhs_p), mkStarForm lhs_h) (rhs_e, ([], rhs_p), mkStarForm rhs_h) in
  let () = print_endline ("frame interface lhs_p: " ^ (str_list !str_pformula lhs_p)) in
  if isValid (mkImply (mkAndlst lhs_p) (norm_to_pure_for_frame norm (mkAndlst rhs_p)))
  then
    extract_frame lhs_root norm (mkAndlst lhs_p) (mkAndlst rhs_p)
  else
    mkEmptyFailCtx ()
;;
  (* let (implylst,neg) = extract_anti_frame_and_frame simp_norm in *)
  (* let dropped_implylst = construct_context_lst (drop_antiframe implylst) (mkTrue ()) in *)
  (* let list_ctx = merge_context_lst_for_frame dropped_implylst lhs_p in *)
  (* list_ctx *)
  (* (true, mkSuccCtx (construct_context_lst (drop_antiframe implylst) neg), []) *)
(* (true, mkEmptySuccCtx (),[]) *)
(* ;;   *)

  
