#include "xdebug.cppo"
open Arr_biabduction
       
type 'a arrf =
  | Match of (('a arrPred) * ('a arrf))
  | Basic of (('a arrPred))
  | Seq of (('a arrf) * ('a arrf))
  | Star of (('a arrf) * ('a arrf))
  | Emp
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
  | Emp,_ -> f1
  | _,Emp -> f2
  | _,_ -> Star (f1,f2)
;;

let equal e1 e2 =
  is_same_exp e1 e2
;;


class relMap = object(self)
                       
end

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

let biabduction ante conseq lhs_p rhs_p =
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
  
  let rec helper ante conseq extend_pf k =

    (* let () = print_endline ((str_arrf ante)^" |= "^(str_arrf conseq)^" "^(str_list !str_pformula extend_pf)) in *)
    let align ante conseq b1 s1 b2 s2 extend_pf k =
      let p1 = mkGt s1 s2 in
      let p2 = mkLte s1 s2 in
      helper (mkMatch (mkGap b1 s2 s1) ante) conseq (p1::extend_pf)
             (fun ans1 ->
               helper ante (mkMatch (mkGap b2 s1 s2) conseq) (p2::extend_pf)
                      (fun ans2 ->
                        k ((List.map (fun (a,f,p) -> (a,f,p)) ans1)@(List.map (fun (a,f,p) -> (a,f,p)) ans2))))
    in
    if isSat (mkAndlst extend_pf)
    then
      match ante,conseq with
      | Match (h1,rest1),Match (h2,rest2) ->
         (
           match h1,h2 with
           | Aseg (b1,s1,e1),Aseg (b2,s2,e2)->
              if equal s1 s2
              then
                let p1 = mkLt e1 e2 in
                let p2 = mkGte e1 e2 in
                helper rest1 (mkMatch (mkAseg b2 e1 e2) rest2) (p1::extend_pf)
                       (fun ans1 ->
                         helper (mkMatch (mkAseg b1 e2 e1) rest1) rest2 (p2::extend_pf)
                                (fun ans2 ->
                                  k ((List.map (fun (a,f,p) -> (a,f,p)) ans1)@(List.map (fun (a,f,p) -> (a,f,p)) ans2))))
              else
                align ante conseq b1 s1 b2 s2 extend_pf k
                      
           | Aseg (b1,s1,e1),Elem (b2,s2) ->
              if equal s1 s2
              then              
                let p1 = mkLt s1 e1 in
                let p2 = mkEq s1 e1 in
                helper (mkMatch (mkAseg b2 (incOne s1) e1) rest1) rest2 (p1::extend_pf)
                       (fun ans1 ->
                         helper rest1 conseq (p2::extend_pf)
                                (fun ans2 ->
                                  k ((List.map (fun (a,f,p) -> (a,f,p1::p)) ans1)@(List.map (fun (a,f,p) -> (a,f,p2::p)) ans2))))
              else
                align ante conseq b1 s1 b2 s2 extend_pf k
                      
           | Elem (b1,s1),Aseg (b2,s2,e2) ->
              if equal s1 s2
              then
                let p1 = mkLt s2 e2 in
                let p2 = mkEq s2 e2 in
                helper rest1 (mkMatch (mkAseg b2 (incOne s2) e2) rest2) (p1::extend_pf)
                       (fun ans1 ->
                         helper ante rest2 (p2::extend_pf)
                                (fun ans2 ->
                                  k ((List.map (fun (a,f,p) -> (a,f,p1::p)) ans1)@(List.map (fun (a,f,p) -> (a,f,p2::p)) ans2))))
              else
                align ante conseq b1 s1 b2 s2 extend_pf k
                      
           | Elem (b1,s1),Elem (b2,s2) ->
              if equal s1 s2
              then helper rest1 rest2 extend_pf k
              else
                align ante conseq b1 s1 b2 s2 extend_pf k
           | Aseg (b1,s1,e1),Gap (b2,s2,e2)->
              if equal s1 s2
              then
                let p1 = mkLte e1 e2 in
                let p2 = mkGt e1 e2 in
                helper rest1 rest2 (p1::extend_pf)
                       (fun ans1 ->
                         helper (mkMatch (mkAseg b1 e2 e1) rest1) rest2 (p2::extend_pf)
                                (fun ans2 ->
                                  k ((List.map (fun (a,f,p) -> (a,(mkAseg b1 s1 e1)::f,p1::p)) ans1)@(List.map (fun (a,f,p) -> (a,(mkAseg b1 s1 e2)::f,p2::p)) ans2))))
              else
                failwith "Aseg vs. Gap: Not aligned"
                         
           | Gap (b1,s1,e1),Aseg (b2,s2,e2) ->
              if equal s1 s2
              then
                let p1 = mkLt e1 e2 in
                let p2 = mkGte e1 e2 in
                helper rest1 (mkMatch (mkAseg b2 e1 e2) rest2) (p1::extend_pf)
                       (fun ans1 ->
                         helper rest1 rest2 (p2::extend_pf)
                                (fun ans2 ->
                                  k ((List.map (fun (a,f,p) -> ((mkAseg b1 s2 e1)::a,f,p1::p)) ans1)@(List.map (fun (a,f,p) -> ((mkAseg b1 s2 e2)::a,f,p2::p)) ans2))))
              else
                failwith "Gap vs. Aseg: Not aligned"
           | Gap (b1,s1,e1),Elem (b2,s2) ->
              if equal s1 s2
              then
                let p1 = mkLt s1 e1 in
                let p2 = mkEq s1 e1 in
                helper rest1 rest2 (p1::extend_pf)
                       (fun ans1 ->
                         helper rest1 conseq (p2::extend_pf)
                                (fun ans2 ->
                                  k ((List.map (fun (a,f,p) -> ((mkElem b2 s2)::a,f,p1::p)) ans1)@(List.map (fun (a,f,p) -> (a,f,p2::p)) ans2))))
              else
                failwith "Gap vs. Elem: Not aligned"
           | Elem (b1,s1),Gap (b2,s2,e2) ->
              if equal s1 s2
              then
                let p1 = mkLt s2 e2 in
                let p2 = mkEq s2 e2 in
                helper rest1 rest2 (p1::extend_pf)
                       (fun ans1 ->
                         helper ante rest2 (p2::extend_pf)
                                (fun ans2 ->
                                  k ((List.map (fun (a,f,p) -> (a,(mkElem b2 s2)::f,p1::p)) ans1)@(List.map (fun (a,f,p) -> (a,f,p2::p)) ans2))))
              else
                failwith "Elem vs. Gap: Not aligned"
           |  Gap _,Gap _ ->
               failwith "Gap vs. Gap: Invalid input"
         )
      | Emp,Emp ->
         let new_extend_pf = (mkOr (mkNot (mkAndlst extend_pf)) rhs_p)::extend_pf in
         if isSat (mkAndlst new_extend_pf)
         then k [([],[],new_extend_pf)]
         else k []
      | Emp,_ ->
         helper Emp Emp extend_pf
                (fun ans ->
                  k (List.map (fun (a,f,p) -> ((flatten_arrf conseq)@a,f,p)) ans))
      | _,Emp ->
         helper Emp Emp extend_pf
                (fun ans ->
                  k (List.map (fun (a,f,p) -> (a,(flatten_arrf ante)@f,p)) ans))
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
                                  helper x1 x2 (p1@p2@extend_pf) k)@r2)
                              [] xlst2)
                           @r1)
                         [] xlst1))
    else
      k []
  in
  helper ante conseq [lhs_p] (fun x->x)
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
                        

let biabduction_inferface ante_cf conseq_cf =
  let anteTrans = new arrPredTransformer_v2 ante_cf in
  let conseqTrans = new arrPredTransformer_v2 conseq_cf in
  let anslst = biabduction anteTrans#formula_to_arrf conseqTrans#formula_to_arrf anteTrans#get_orig_pure conseqTrans#get_orig_pure in
  List.iter
    (fun (a,f,plst) ->
      print_endline ("anti-frame: "^(str_seq a)^"\n frame: "^(str_seq f)^"\n puref:"^(str_list !str_pformula plst))
    )
    (norm_ans anslst)
;;
