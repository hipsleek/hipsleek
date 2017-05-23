#include "xdebug.cppo"
open Arr_biabduction
       
type 'a arrf =
  | Match of (('a arrPred) * ('a arrf))
  | Basic of (('a arrPred))
  | Seq of (('a arrf) * ('a arrf))
  | Star of (('a arrf) * ('a arrf))
  | Emp
;;

(* type ansType = (arrPred list) array_formula *)
(* ;; *)

let mkAns antiframe frame =
  (antiframe,frame)
;;

  
let print_answer (antiframe,frame) =
  "antiframe: "^(str_array_formula str_arrPred_star_lst antiframe)^" frame: "^(str_array_formula str_arrPred_star_lst frame)
;;

let construct_context_lst_helper anslst =  
  let construct_context_helper antiframe frame =
    match antiframe,frame with
    | ABase (ap,ah), ABase (fp,fh) ->
       let es = Cformula.empty_es (Cformula.mkTrueFlow ()) Label_only.Lab2_List.unlabelled VarGen.no_pos in
       let (h_antiframe,plst_antiframe,svl_antiframe) = arrPred_to_h_formula ah in
       let (h_frame,plst_frame,svl_frame) = arrPred_to_h_formula fh in
       let state_f = construct_base h_frame (Mcpure.mix_of_pure (simplify (mkAndlst (fp::(plst_antiframe@plst_frame))))) in
       {es with
         es_formula = state_f;
         es_infer_heap = [h_antiframe];
         es_infer_pure = [ap];
         (* es_evars = svl_antiframe@svl_frame; *)
       }
    | ATrue, ABase (fp,fh) ->
       let es = Cformula.empty_es (Cformula.mkTrueFlow ()) Label_only.Lab2_List.unlabelled VarGen.no_pos in
       let (h_frame,plst_frame,svl_frame) = arrPred_to_h_formula fh in
       let state_f = construct_base h_frame (Mcpure.mix_of_pure (simplify (mkAndlst (fp::(plst_frame))))) in
       {es with
         es_formula = state_f;
         es_infer_heap = [];
         es_infer_pure = [];
         (* es_evars = svl_antiframe@svl_frame; *)
       }
    | ATrue, AFalse ->
       let es = Cformula.empty_es (Cformula.mkTrueFlow ()) Label_only.Lab2_List.unlabelled VarGen.no_pos in
       {es with
         es_formula = Cformula.mkFalse (Cformula.mkFalseFlow) VarGen.no_pos;
         es_infer_heap = [];
         es_infer_pure = [];
         (* es_evars = svl_antiframe@svl_frame; *)
       }
    | _,_ -> failwith "construct_context_lst_helper: TO BE IMPLEMENTED"
  in
  List.map
    (fun (antiframe,frame) ->
      Cformula.Ctx (construct_context_helper antiframe frame))
    anslst
;;
  


(* Only compare pure *)
let is_better_ans (a1,f1) (a2,f2) =
  match a1,a2 with
  | AFalse,_ -> false     
  | _,AFalse -> true     
  | ABase (ap1,_),ABase (ap2,_) ->
     imply ap2 ap1
  | _,_ -> false
;;

let compare_ans ans1 ans2 =
  if is_better_ans ans1 ans2
  then 1
  else
    if is_better_ans ans2 ans1
    then 2
    else
      3
;;

let extend_all_antiframe ans antiframe =
  List.map
    (fun (anti,frame) ->
      match anti with
      | ABase (p,h) ->
         (mkABase p (antiframe@h),frame)
      | ATrue ->
         (mkABase (mkTrue ()) antiframe,frame)
      | AFalse ->
         (anti,frame)
      | _ -> failwith "extend_all_antiframe: TO BE IMPLEMENTED")
    ans
;;

let extend_all_frame ans newframe =
  List.map
    (fun (anti,frame) ->
      match frame with
      | ABase (p,h) ->
         (anti,mkABase p (newframe@h))
      | ATrue ->
         (anti,mkABase (mkTrue ()) newframe)
      | AFalse ->
         (anti,frame)
      | _ -> failwith "extend_all_frame: TO BE IMPLEMENTED")
    ans
;;
  
let rec str_arrf arrf =
  match arrf with
  | Match (h,tail)-> ("Match ("^(str_arrPred h)^","^(str_arrf tail)^")")
  | Basic h -> "Basic ("^(str_arrPred h)^")"
  | Seq (l,r) -> "Seq ("^(str_arrf l)^","^(str_arrf r)^")"
  | Star (l,r) -> "Star ("^(str_arrf l)^","^(str_arrf r)^")"
  | Emp -> "Emp"
;;
  
let map_t f lst k =
  let rec helper lst k =
    match lst with
    | h::tail ->
       helper tail
              (fun xlst ->
                k ((f h)::xlst))
    | [] -> k []
  in
  helper lst k
;;

let flatten_arrf arrf =
  let rec helper arrf k =
    match arrf with
    | Match (h,tail) ->
       helper tail (fun xlst -> k (h::xlst))
    | Basic h -> k [h]
    | Seq (l,r) | Star (l,r)->
       helper l
              (fun xlst1 ->
                helper r
                       (fun xlst2 ->
                         k (xlst1@xlst2)))
    | Emp -> k []
  in
  helper arrf (fun x->x)
;;

let mkBasic h =
  Basic h
;;
            
let mkMatch h tail =
  Match (h,tail)
;;

let mkSeq f1 f2 =
  Seq (f1,f2)
;;

let mkStar f1 f2 =
  match f1,f2 with
  | Emp,Emp -> Emp
  | Emp,_ -> f2
  | _,Emp -> f1
  | _,_ -> Star (f1,f2)
;;

let equal e1 e2 =
  is_same_exp e1 e2
;;




class arrPredTransformer_v2 initcf = object(self)
  inherit arrPredTransformer initcf
  method formula_to_arrf =
    let rec helper lst arrf =
      match lst with    
      | [] -> arrf
      | h::tail ->
         helper tail (mkStar (mkBasic h) arrf)
    in
    match (self#formula_to_arrPred) with
    | h::tail -> helper tail (mkBasic h)
    | [] -> Emp
  
end
;;

let combine_search_ans ans1 ans2 =
  ans1@ans2
;;

let combine_case_ans ans1 ans2 =
  List.fold_left
    (fun r1 item1 ->
      (List.fold_left
        (fun r2 item2 ->
          (disj_ba_result item1 item2)::r2)
        [] ans2
      )@r1
    )
    [] ans1
;;
     
  

let biabduction ante conseq lhsp rhsp =
  (* The input of sort is still arrf *)
  let sort arrf k =    
    let rec sort_helper arrf k =      
      match arrf with
      | Basic h -> k [(Match (h,Emp),[])]
      | Match _ -> k [(arrf,[])]
      | Seq (l,r) ->
         sort_helper l
                     (fun xlst ->
                       map_t
                         (fun (x,p) ->
                           match x with
                           | Match (h,tail) ->
                              ((mkMatch h (mkSeq tail r)),p)
                           | _ -> failwith "sort: Invalid input")
                         xlst k)

      | Star (((Basic h1) as l),((Basic h2) as r)) ->
         (
           match h1,h2 with
           | Aseg (_,s1,e1),Aseg (_,s2,e2) ->
              let p1,r1 = [(mkLte e1 s2);(mkLt s1 e1);(mkLt s2 e2)],(mkMatch h1 r) in
              let p2,r2 = [(mkLte e2 s1);(mkLt s1 e1);(mkLt s2 e2)],(mkMatch h2 l) in
              let p3,r3 = [mkEq s1 e1],(mkMatch h1 Emp) in
              let p4,r4 = [mkEq s2 e2],(mkMatch h2 Emp) in
              k [(r1,p1);(r2,p2);(r3,p3);(r4,p4)]
           | Aseg (_,s1,e1),Elem (_,s2) ->
              let p1,r1 = [(mkLt s2 s1);(mkLt s1 e1)],(mkMatch h2 l) in
              let p2,r2 = [(mkLte e1 s2);(mkLt s1 e1)],(mkMatch h1 r) in
              let p3,r3 = [mkEq s1 e1],(mkMatch h2 Emp) in              
              k [(r1,p1);(r2,p2);(r3,p3)]
           | Elem (_,s1),Aseg (_,s2,e2) ->
              let p1,r1 = [(mkLte e2 s1);(mkLt s2 e2)],(mkMatch h2 l) in
              let p2,r2 = [(mkLt s1 s2);(mkLt s2 e2)],(mkMatch h1 r) in              
              let p3,r3 = [mkEq s2 e2],(mkMatch h1 Emp) in              
              k [(r1,p1);(r2,p2);(r3,p3)]
           | Elem (_,s1),Elem (_,s2) ->
              let p1,r1 = [(mkGt s1 s2)],(mkMatch h2 l) in
              let p2,r2 = [(mkGt s2 s1)],(mkMatch h1 r) in
              k [(r1,p1);(r2,p2)]
           | _,_ -> failwith "sort_helper: Invalid input"
         )
           
      | Star (l,r) -> sort_helper l
                                  (fun xlst1 ->
                                    sort_helper r
                                                (fun xlst2 ->
                                                  (List.fold_left
                                                     (fun r1 (x1,p1) ->
                                                       (List.fold_left
                                                          (fun r2 (x2,p2) ->
                                                            match x1,x2 with
                                                            | Match (h1,tail1),Match (h2,tail2) ->
                                                               sort_helper (mkStar (mkBasic h1) (mkBasic h2))
                                                                           (fun xlst3 ->
                                                                             (k (List.map
                                                                                   (fun (x3,p3) ->
                                                                                     match x3 with
                                                                                     | Match (h3,tail3) ->
                                                                                        (mkMatch h3 (mkStar tail3 (mkStar tail1 tail2)),p1@p2@p3)
                                                                                     | _ -> failwith "sort: Invalid input")
                                                                                   xlst3))@r2)
                                                            | _ -> failwith "sort: Invalid input")
                                                          [] xlst2)@r1)
                                                     [] xlst1)))
      | _ -> failwith "sort_helper: Invalid input Emp"
    in
    sort_helper arrf k
  in

  let rec entry_helper ante conseq lhsp rhsp k =    
    let lhsplst = mkAndlst lhsp in    
    if isSat lhsplst
    then      
      helper ante conseq lhsp rhsp k
    else k [mkAns (mkATrue ()) (mkAFalse ())]
  
  
  and helper ante conseq lhsp rhsp k =
    let () = print_endline ((str_arrf ante)^" |= "^(str_arrf conseq)^" lhsp: "^(str_list !str_pformula lhsp)^" rhsp: "^(str_list !str_pformula rhsp)) in
    let combine_ans r1a r2b p1 p2 lhsp k =
      let r1b =
        if (isSat (mkAndlst ((mkNot p1)::lhsp)))
        then [(mkAns (mkABase p1 []) (mkAFalse ()))]
        else [mkATrue (), mkAFalse ()]
      in
      let r2a =
        if (isSat (mkAndlst ((mkNot p2)::lhsp)))
        then [(mkAns (mkABase p2 []) (mkAFalse ()))]
        else [mkATrue (), mkAFalse ()]
      in
      k (combine_search_ans (combine_case_ans r1a r1b) (combine_case_ans r2b r2a))
    in
    let align ante conseq lhsp rhsp b1 s1 b2 s2 k =
      let p1 = mkGt s1 s2 in
      let p2 = mkLt s1 s2 in      
      entry_helper (mkMatch (mkGap b1 s2 s1) ante) conseq (p1::lhsp) (p1::rhsp)
                   (fun r1a ->
                     entry_helper ante (mkMatch (mkGap b2 s1 s2) conseq) (p2::rhsp) (p2::rhsp)
                                  (fun r2b ->                                    
                                    combine_ans r1a r2b p1 p2 lhsp k))
    in
    match ante,conseq with
    | Match (h1,rest1),Match (h2,rest2) ->
       (
         match h1,h2 with
         | Aseg (b1,s1,e1),Aseg (b2,s2,e2)->
            if equal s1 s2
            then
              let p1,p2 =
                if false
                then
                  mkLte e1 e2,mkGte e1 e2
                else
                  mkLt e1 e2,mkGte e1 e2
              in
              entry_helper rest1 (mkMatch (mkAseg b2 e1 e2) rest2) (p1::lhsp) (p1::rhsp)
                           (fun r1a ->
                             entry_helper (mkMatch (mkAseg b1 e2 e1) rest1) rest2 (p2::lhsp) (p2::rhsp)
                                          (fun r2b ->
                                            combine_ans r1a r2b p1 p2 lhsp k))
            else
              align ante conseq lhsp rhsp b1 s1 b2 s2 k
         
         | Aseg (b1,s1,e1),Elem (b2,s2) ->
            if equal s1 s2
            then
              let p1 = mkLt s1 e1 in
              let p2 = mkEq s1 e1 in
              entry_helper (mkMatch (mkAseg b2 (incOne s1) e1) rest1) rest2 (p1::lhsp) (p1::rhsp)
                           (fun r1a ->
                             entry_helper rest1 conseq (p2::lhsp) (p2::rhsp)
                                          (fun r2b ->
                                            combine_ans r1a r2b p1 p2 lhsp k))
            else
              align ante conseq lhsp rhsp b1 s1 b2 s2 k
         | Aseg (b1,s1,e1),Gap (b2,s2,e2)->
            if equal s1 s2
            then
              let p1,p2 =
                if false
                then
                  mkLte e1 e2,mkGte e1 e2
                else
                  mkLte e1 e2,mkGt e1 e2
              in
              entry_helper rest1 rest2 (p1::lhsp) (p1::rhsp)
                           (fun r1a ->
                             entry_helper (mkMatch (mkAseg b1 e2 e1) rest1) rest2 (p2::lhsp) (p2::rhsp)
                                          (fun r2b ->
                                            let r1a = extend_all_frame r1a [(mkAseg b1 s1 e1)] in
                                            let r2b = extend_all_frame r2b [(mkAseg b1 s1 e2)] in
                                            combine_ans r1a r2b p1 p2 lhsp k))
            else
              failwith "Aseg vs. Gap: Not aligned"
                       
         | Gap (b1,s1,e1),Aseg (b2,s2,e2) ->
            if equal s1 s2
            then
              let p1,p2 =
                if false
                then
                  mkLte e1 e2,mkGte e1 e2
                else
                  mkLt e1 e2,mkGte e1 e2
              in              
              
              entry_helper rest1 (mkMatch (mkAseg b2 e1 e2) rest2) (p1::lhsp) (p1::rhsp)
                           (fun r1a ->
                             entry_helper rest1 rest2 (p2::lhsp) (p2::rhsp)
                                          (fun r2b ->
                                            let r1a = extend_all_antiframe r1a [(mkAseg b2 s2 e1)] in
                                            let r2b = extend_all_antiframe r2b [(mkAseg b2 s2 e2)] in
                                            combine_ans r1a r2b p1 p2 lhsp k))
            else
              failwith "Gap vs. Aseg: Not aligned"
         
         | Elem (b1,s1),Aseg (b2,s2,e2) ->
            if equal s1 s2
            then
              let p1 = mkLt s2 e2 in
              let p2 = mkEq s2 e2 in
              entry_helper rest1 (mkMatch (mkAseg b2 (incOne s2) e2) rest2) (p1::lhsp) (p1::rhsp)
                     (fun r1a ->
                       entry_helper ante rest2 (p2::lhsp) (p2::rhsp)
                                    (fun r2b ->
                                      combine_ans r1a r2b p1 p2 lhsp k))
            else
              let p1 = mkEq s1 s2 in
              let p2 = mkNeq s1 s2 in
              entry_helper ante (mkMatch (mkAseg b2 s1 e2) rest2) (p1::lhsp) (p1::rhsp)
                           (fun r1a ->
                             align ante conseq (p2::lhsp) (p2::rhsp) b1 s1 b2 s2
                                   (fun r2b ->
                                     combine_ans r1a r2b p1 p2 lhsp k))
                           (* align ante conseq lhsp rhsp b1 s1 b2 s2 k *)
         | Elem (b1,s1),Elem (b2,s2) ->
            if equal s1 s2
            then
              entry_helper rest1 rest2 lhsp rhsp k              
            else
              let p1 = mkEq s1 s2 in
              let p2 = mkNeq s1 s2 in
              entry_helper ante (mkMatch (mkElem b2 s1) rest2) (p1::lhsp) (p1::rhsp)
                           (fun r1a ->
                             align ante conseq (p2::lhsp) (p2::rhsp) b1 s1 b2 s2
                                   (fun r2b ->
                                     combine_ans r1a r2b p1 p2 lhsp k))
                                
            (* if equal s1 s2 *)
            (* then entry_helper rest1 rest2 lhsp rhsp k *)
            (* else *)
            (*   align ante conseq lhsp rhsp b1 s1 b2 s2 k *)
         | Gap (b1,s1,e1),Elem (b2,s2) ->
            if equal s1 s2
            then
              let p1 = mkLt s1 e1 in
              let p2 = mkEq s1 e1 in
              entry_helper rest1 rest2 (p1::lhsp) (p1::rhsp)
                     (fun r1a ->
                       entry_helper rest1 conseq (p2::lhsp) (p2::rhsp)
                                    (fun r2b ->
                                      let r1a = extend_all_antiframe r1a [(mkElem b2 s2)] in
                                      let r2b = extend_all_antiframe r2b [(mkElem b2 s2)] in
                                      combine_ans r1a r2b p1 p2 lhsp k))
            else
              failwith "Gap vs. Elem: Not aligned"
         | Elem (b1,s1),Gap (b2,s2,e2) ->
            if equal s1 s2
            then
              let p1 = mkLt s2 e2 in
              let p2 = mkEq s2 e2 in
              entry_helper rest1 rest2 (p1::lhsp) (p1::rhsp)
                     (fun r1a ->
                       entry_helper ante rest2 (p2::lhsp) (p2::rhsp)
                                    (fun r2b ->
                                      let r1a = extend_all_frame r1a [(mkElem b1 s1)] in
                                      let r2b = extend_all_frame r2b [(mkElem b1 s1)] in
                                      combine_ans r1a r2b p1 p2 lhsp k))
                                
            else
              failwith "Elem vs. Gap: Not aligned"
          | _,_ -> failwith "TO BE IMPLEMENTED"           
         
         
         
         (* |  Gap _,Gap _ -> *)
         (*     failwith "Gap vs. Gap: Invalid input" *)
       )
    | Emp,Emp ->
       k [mkAns (mkABase (mkImply (mkAndlst lhsp) (mkAndlst rhsp)) []) (mkABase (mkAndlst (lhsp@rhsp)) [])]
    | Emp,_ ->
       helper Emp Emp lhsp rhsp 
              (fun ans ->
                let conseqlst = flatten_arrf conseq in
                k (extend_all_antiframe ans conseqlst))
    | _,Emp ->
       helper Emp Emp lhsp rhsp
              (fun ans ->
                let antelst = flatten_arrf ante in
                k (extend_all_frame ans antelst))               
    | _,_ ->
       sort ante
            (fun xlst1 ->
              sort conseq
                   (fun xlst2 ->
                     List.fold_left
                       (fun r1 (x1,p1) ->
                         (List.fold_left
                            (fun r2 (x2,p2) ->
                              (
                                (* let () = print_endline ((str_arrf x1)^" |= "^(str_arrf x2)^" "^(str_list !str_pformula (p1@p2@extend_pf))) in *)
                                if isSat (mkAndlst (p1@p2@lhsp))
                                then 
                                  helper x1 x2 (p1@p2@lhsp) rhsp k
                                else []
                              )@r2)
                            [] xlst2)
                         @r1)
                       [] xlst1))
  in
  
  entry_helper ante conseq [lhsp] [rhsp] (fun x->x)
;;

let norm_ans anslst =
  List.map
    (fun (alst,flst,plst) ->
      ((List.fold_left
          (fun r item ->
            if is_empty_apred equal item
            then r
            else item::r)
          [] alst
       ),
       (List.fold_left
          (fun r item ->
            if is_empty_apred equal item
            then r
            else item::r)
          [] flst
       ),
       plst))
    anslst
;;

let drop_empty_apred apredlst =
  List.fold_left
    (fun r item ->
      if is_empty_apred equal item
      then r
      else item::r)
    [] apredlst
;;

let normalize_one_ans ans =
  match ans with
  | ABase (p,h) ->
     mkABase (simplify p) (drop_empty_apred h)
  | _ -> ans
;;

let rec clean_ans anslst =
  let rec helper one lst =
    match lst with
    | [] -> [one]
    | h::tail ->
       let c = compare_ans h one in
       if c = 1                 (* h>one *)
       then lst
       else
         if c = 2               (* h<one *)
         then (helper one tail)
         else
           h::(helper one tail)
  in
  match anslst with
  | [] -> []
  | h::tail -> helper h (clean_ans tail)
;;
               

    
let biabduction_inferface ante_cf conseq_cf =
  let anteTrans = new arrPredTransformer_v2 ante_cf in
  let conseqTrans = new arrPredTransformer_v2 conseq_cf in
  let anslst = biabduction anteTrans#formula_to_arrf conseqTrans#formula_to_arrf anteTrans#get_pure conseqTrans#get_pure in
  let norm_anslst =
    List.map
      (fun (antiframe,frame) ->
        (normalize_one_ans antiframe,normalize_one_ans frame))
      anslst
  in
  let clean_anslst = clean_ans norm_anslst in
  let () =
    List.iter
      (fun ans ->
        print_endline (print_answer ans)
      )
      clean_anslst
  in
  (Cformula.SuccCtx (construct_context_lst_helper clean_anslst))
;;
