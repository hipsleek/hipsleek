#include "xdebug.cppo"

open Cpure
open VarGen
open Cformula
       
type 'exp arrPred =
  | Aseg of ('exp * 'exp * 'exp)
  | Gap of ('exp * 'exp * 'exp)
  | Elem of ('exp * 'exp)
;;

  
let map_op_list (f:('a -> 'b)) (lst:('a option list)) =
  List.fold_right
    (fun item r ->
      match item with
      | Some a -> (f a)::r
      | None -> r)
    lst []
;;

let mkAseg b s e =
  Aseg (b,s,e)
;;


let mkGap b s e =
  Gap (b,s,e)
;;

let mkElem b s =
  Elem (b,s)
;;

let isEq s1 e1 pf =
  (* pf |= s1 == e1 *)
  let rhsf = mkEqExp s1 e1 no_pos in
  !tp_imply pf rhsf
;;

let isGt s1 e1 pf =
  (* pf |= s1 > e1 *)
  let rhsf = mkGtExp s1 e1 no_pos in
  !tp_imply pf rhsf
;;

let isGte s1 e1 pf =
  (* pf |= s1 >= e1 *)
  let rhsf = mkGteExp s1 e1 no_pos in
  !tp_imply pf rhsf
;;
  
let incOne e =
  Add (e,IConst (1,no_pos),no_pos)
;;

let isSat f=
(* Tpdispatcher.tp_is_sat f "111" *)
  true
;;

let str_exp = print_exp
;;

let str_cformula = Cformula.print_formula
;;

let str_pformula = Cpure.print_formula
;;
  
let str_arrPred apred =
  match apred with
  | Aseg (b,s,e) ->
     "Aseg("^(!str_exp b)^","^(!str_exp s)^","^(!str_exp e)^")"
  | Gap (b,s,e)->
     "Gap("^(!str_exp b)^","^(!str_exp s)^","^(!str_exp e)^")"
  | Elem (b,s) ->
     "Elem("^(!str_exp b)^","^(!str_exp s)^")"
;;
  
let str_list =
  Gen.Basic.pr_list
;;

let str_pair=
  Gen.Basic.pr_pair
;;

let str_seq seq =
  str_list str_arrPred seq
;;

let rec flatten_heap_star_formula cf =
  match cf with
  | Star f ->
     (flatten_heap_star_formula f.h_formula_star_h1)@(flatten_heap_star_formula f.h_formula_star_h2)
  | ViewNode _ -> [cf]
  | _ -> failwith "flatten_heap_star_formula: Invalid input"
;;

let isAsegPred cf =
  match cf with
  | ViewNode f ->
     String.equal f.h_formula_view_name "Aseg"
  | _ -> false
;;

let isElemPred cf =
  match cf with
  | ViewNode f ->
     String.equal f.h_formula_view_name "Elem"
  | _ -> false
;;

let isEmpty cf =
  false
;;

class arrPredTransformer initcf = object(self)
  val cf = initcf               (* cf is Cformula.formula *)
  val mutable eqmap = ([]: (spec_var * exp) list)
      
  method find_in_eqmap sv =
    try
      let (_,e1) = List.find (fun (v,e) -> (compare_sv sv v)=0) eqmap
      in
      Some e1
    with _ ->
      None
          
  method pred_var_to_arrPred_exp sv =
    match (self#find_in_eqmap sv) with
    | None ->
       Var (sv,no_pos)
    | Some e ->
       e
         
  method getAsegBase cf =
    match cf with
    | ViewNode f ->
       self#pred_var_to_arrPred_exp f.h_formula_view_node
    | _ -> failwith "getAsegBase: Invalid input"
    
  method getAsegStart cf =
    match cf with
    | ViewNode f ->
       self#pred_var_to_arrPred_exp (List.nth f.h_formula_view_arguments 0)
    | _ -> failwith "getAsegStart: Invalid input"

  method getAsegEnd cf =
    match cf with
    | ViewNode f ->
       self#pred_var_to_arrPred_exp (List.nth f.h_formula_view_arguments 1)
    | _ -> failwith "getAsegEnd: Invalid input"
  
  method getElemBase cf =
    match cf with
    | ViewNode f ->
       self#pred_var_to_arrPred_exp f.h_formula_view_node
    | _ -> failwith "getElemBase: Invalid input"
 
  method getElemStart cf =
    match cf with
    | ViewNode f ->
       self#pred_var_to_arrPred_exp (List.nth f.h_formula_view_arguments 0)
    | _ -> failwith "getElemStart: Invalid input"

  method formula_to_arrPred =
    let one_pred_to_arrPred hf=
      if isAsegPred hf
      then Some (mkAseg (self#getAsegBase hf) (self#getAsegStart hf) (self#getAsegEnd hf))
      else
        if isElemPred hf
        then Some (mkElem (self#getElemBase hf) (self#getElemStart hf))
        else
          if isEmpty hf
          then None
          else failwith "one_pred_to_arrPred: Invalid input"
    in    
    let build_eqmap pf evars=
      let eqlst = find_eq_at_toplevel pf in
      let evarsContains evars sv =
        try 
          List.exists (fun v -> (compare_sv v sv)=0) evars
        with _ ->
          false
      in
      let helper (e1,e2) =
        match e1,e2 with
        | Var (sv1,_) , Var (sv2,_) ->
           if evarsContains evars sv1 && evarsContains evars sv2
           then [(sv1,e2);(sv2,e1)]
           else
             if evarsContains evars sv1
             then [(sv1,e2)]
             else [(sv2,e1)]
        | Var (sv,_), e
          | e, Var (sv,_) ->
           if evarsContains evars sv
           then [(sv,e2)]
           else []
        | _,_ -> []
      in
      List.fold_left (fun r ee -> (helper ee)@r) [] eqlst
    in
    match cf with
    | Base f ->
       let pred_list = flatten_heap_star_formula f.formula_base_heap in
       map_op_list (fun x->x) (List.map one_pred_to_arrPred pred_list)       
    | Or f-> failwith "TO BE IMPLEMENTED"
    | Exists f ->
       let pf = Mcpure.pure_of_mix f.formula_exists_pure in
       let evars = f.formula_exists_qvars in
       let () = eqmap <- build_eqmap pf evars in
       let pred_list = flatten_heap_star_formula f.formula_exists_heap in
       map_op_list (fun x->x) (List.map one_pred_to_arrPred pred_list)

  method get_var_set =
    let get_var_from_one_pred hf=
      if isAsegPred hf
      then [(self#getAsegStart hf);(self#getAsegEnd hf);incOne (self#getAsegEnd hf)]
      else
        if isElemPred hf
        then [(self#getElemStart hf);incOne (self#getElemStart hf)]
        else
          if isEmpty hf
          then []
          else failwith "get_var_from_one_pred: Invalid input"
    in
    match cf with
    | Base f ->
       let pred_list = flatten_heap_star_formula f.formula_base_heap in
       (List.concat (List.map get_var_from_one_pred pred_list))
    | _ -> failwith "get_var_set: TO BE IMPLEMENTED"
   
end
;;
    
  
(* let formula_to_arrPred cf = *)
(*   Debug.no_1 "formula_to_arrPred" !str_cformula str_seq formula_to_arrPred cf *)
(* ;; *)
  
let biabduction (plhs,seqLHS) (prhs,seqRHS) =
  let rec helper seqLHS seqRHS antiframe frame prooftrace =
    let prooftrace = (seqLHS,seqRHS)::prooftrace in
    match seqLHS, seqRHS with
    | h1::tail1, h2::tail2 ->
       (
         match h1, h2 with
         | Aseg (b1, s1, e1), Aseg (b2, s2, e2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame prooftrace
            else
              if isEq s2 e2 plhs
              then helper seqLHS tail2 antiframe frame prooftrace
              else                (* Neither sides are empty *)
                if isEq s1 s2 plhs
                then
                  if isGt e1 e2 plhs  (* e1>e2 *)
                  then
                    helper ((mkAseg b1 e2 e1)::tail1) tail2 antiframe frame prooftrace
                  else            (* e1<e2 *)
                    helper tail1 ((mkAseg b1 e1 e2)::tail2) antiframe frame prooftrace
                else
                  if isGt s1 s2 plhs
                  then helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame prooftrace
                  else helper seqLHS ((mkGap b2 s1 s2)::seqRHS) antiframe frame prooftrace       
         | Aseg (b1, s1, e1), Elem (b2, s2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame prooftrace
            else
              if isEq s1 s2 plhs
              then
                helper ((mkAseg b1 (incOne s1) e1)::tail1) tail2 antiframe frame prooftrace
              else
                if isGt s1 s2 plhs  (* s1>s2 *)
                then
                  helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame prooftrace
                else            (* s1<s2 *)
                  helper seqLHS ((mkGap b1 s1 s2)::seqRHS) antiframe frame prooftrace
         | Aseg (b1, s1, e1), Gap (b2, s2, e2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame prooftrace
            else
              if isEq s1 s2 plhs
              then
                if isGt e1 e2 plhs  (* e1>e2 *)
                then helper ((mkAseg b1 e2 e1)::tail1) tail2 antiframe ((mkAseg b1 s1 e2)::frame) prooftrace
                else helper tail1 ((mkGap b2 e1 e2)::tail2) antiframe ((mkAseg b1 s1 e1)::frame) prooftrace
              else
                if isGt s1 s2 plhs  (* s1>s2 *)
                then helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame prooftrace
                else helper seqLHS ((mkGap b2 s1 e2)::tail2) antiframe frame prooftrace
         | Elem (b1, s1), Elem (b2, s2) ->
            if isEq s1 s2 plhs
            then helper tail1 tail2 antiframe frame prooftrace
            else
              if isGt s1 s2 plhs
              then helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame prooftrace
              else helper seqLHS ((mkGap b2 s1 s2)::seqRHS) antiframe frame prooftrace
         | Elem (b1, s1), Aseg (b2, s2, e2) ->
            if isEq s2 e2 plhs
            then helper seqLHS tail2 antiframe frame prooftrace
            else
              if isEq s1 s2 plhs
              then helper tail1 ((mkAseg b2 (incOne s2) e2)::tail2) antiframe frame prooftrace
              else
                if isGt s1 s2 plhs
                then helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame prooftrace
                else helper seqLHS ((mkGap b2 s1 s2)::seqRHS) antiframe frame prooftrace               
         | Elem (b1, s1), Gap (b2, s2, e2) ->
            if isEq s2 e2 plhs
            then helper seqLHS tail2 antiframe frame prooftrace
            else
              if isEq s1 s2 plhs
              then helper tail1 ((mkGap b2 (incOne s2) e2)::tail2) antiframe ((mkElem b1 s1)::frame) prooftrace
              else
                if isGt s1 s2 plhs
                then helper ((mkGap b1 s2 s1)::seqLHS) seqRHS antiframe frame prooftrace
                else helper seqLHS ((mkGap b2 s1 e2)::tail2) antiframe frame prooftrace(* Just make the gap bigger *)
         | Gap (b1, s1, e1), Gap (b2, s2, e2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame prooftrace
            else
              if isEq s2 e2 plhs
              then helper seqLHS tail2 antiframe frame prooftrace
              else                (* Neither sides are empty *)
                if isEq s1 s2 plhs
                then
                  if isGt e1 e2 plhs  (* e1>e2 *)
                  then
                    helper ((mkGap b1 e2 e1)::tail1) tail2 antiframe frame prooftrace
                  else            (* e1<e2 *)
                    helper tail1 ((mkGap b1 e1 e2)::tail2) antiframe frame prooftrace
                else
                  if isGt s1 s2 plhs
                  then helper ((mkGap b1 s2 e1)::tail1) seqRHS antiframe frame prooftrace
                  else helper seqLHS ((mkGap b2 s1 e2)::tail2) antiframe frame prooftrace       
         | Gap (b1, s1, e1), Elem (b2, s2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame prooftrace
            else
              if isEq s1 s2 plhs
              then helper ((mkGap b1 (incOne s1) e1)::tail1) tail2 ((mkElem b2 s2)::antiframe) frame prooftrace
              else
                if isGt s1 s2 plhs
                then helper ((mkGap b1 s2 e1)::tail1) seqRHS antiframe frame prooftrace(* Just make the gap bigger *)
                else helper seqLHS ((mkGap b2 s1 s2)::seqRHS) antiframe frame prooftrace
         | Gap (b1, s1, e1), Aseg (b2, s2, e2) ->
            if isEq s1 e1 plhs
            then helper tail1 seqRHS antiframe frame prooftrace
            else
              if isEq s2 e2 plhs
              then helper seqLHS tail2 antiframe frame prooftrace
              else
                if isEq s1 s2 plhs
                then
                  if isGt e1 e2 plhs
                  then helper ((mkGap b1 e2 e1)::tail1) tail2 ((mkAseg b2 s2 e2)::antiframe) frame prooftrace
                  else helper tail1 ((mkAseg b2 e1 e2)::tail2) ((mkAseg b2 s2 e1)::antiframe) frame prooftrace
                else
                  if isGt s1 s2 plhs
                  then helper ((mkGap b1 s2 e1)::tail1) seqRHS antiframe frame prooftrace
                  else helper seqLHS ((mkGap b2 s1 e2)::tail2) antiframe frame prooftrace
       )                              
    | h1::tail1, [] ->
       (
         match h1 with
           Aseg (b,s,e) 
         | Gap (b,s,e) when isEq s e plhs ->
            helper tail1 seqRHS antiframe frame prooftrace
         | _ ->
            (antiframe,seqLHS@frame,prooftrace)
       )
    | [], h2::tail2 ->
       (
         match h2 with
           Aseg (b,s,e)
         | Gap (b,s,e) when isEq s e plhs->
            helper seqLHS tail2 antiframe frame prooftrace
         | _ ->
            (seqRHS@antiframe,frame,prooftrace)            
       )       
    | [],[] ->
       (antiframe, frame,prooftrace)
  in
  helper seqLHS seqRHS [] [] []
;;

let biabduction (plhs,seqLHS) (prhs,seqRHS) =
  let pr_input = str_pair !str_pformula str_seq in
  let pr_result (a,f,t) =
    (str_pair str_seq str_seq) (a,f)
  in
  Debug.no_2 "biabduction" pr_input pr_input pr_result biabduction (plhs,seqLHS) (prhs,seqRHS)
;;

let rec clean_gap seq =
  match seq with
  | (Gap _)::tail ->
     clean_gap tail
  | h::tail ->
     h::(clean_gap tail)
  | [] -> []
;;

type 'a rect =
  | Rect of (unit -> ('a * ('a rect)) option)
;;
  
let enumerate_solution_seed vlst do_biabduction =
  let length = List.length vlst in
  let updateSeed seed seed_i = seed_i::seed in
  let empty_seed = [] in
  (* let do_biabduction seed = *)
  (*   print_endline (str_list (str_list string_of_int) seed) *)
  (* in *)
  let rec innerk_orig level curi seed ((Rect k):('a rect)) () =
    if level = length
    then
      Some (seed, Rect k)
    else
      if curi = 3
      then k ()        
      else
        innerk_orig (level+1) 0 (updateSeed seed curi) (Rect (innerk_orig level (curi+1) seed (Rect k))) ()
  in
  let rec helper cur seed (Rect innerk) k () =
    if cur = length
    then
      let _ = do_biabduction seed in
      k ()
    else
      match innerk () with
      | None ->
         k ()
      | Some (seed_i,Rect inner_i) ->
         let newseed = updateSeed seed seed_i in
         helper (cur+1) newseed (Rect (innerk_orig (cur+1) 0 empty_seed (Rect (fun ()->None)))) (helper cur seed (Rect inner_i) k) ()
  in
  helper 1 empty_seed (Rect (innerk_orig 1 0 empty_seed (Rect (fun ()->None)))) (fun x->x) ()
;;

(* map is the matrix of variables *)
let topological_base_enumerate vlst map =
  let rec degree_extract_zero queue degree =
    match degree with
    | (i,d)::tail ->
       if d=0
       then degree_extract_zero (i::queue) tail
       else
         let (queue_new,degree_new) = degree_extract_zero queue tail in
         (queue_new,(i,d)::degree_new)
    | [] ->
       (queue,[])
  in
  let rec degree_minus_one degree target map =
    List.map (fun (i,d) ->
        if pointto target i
        then (i,d-1)
        else (i,d)
      ) degree
  in             
  let rec helper queue degree seed =
    match queue with
    | h::tail ->
       let (queue, degree) = degree_extract_zero queue (degree_minus_one degree h map) in
       helper tail degree queue
    | [] ->
       if List.length degree = 0
       then do_biabduction seed
       else
         failwith "Cycle found!"
  in
  let segment_map = build_segment_map () in (* 1->(a,b);2->(c,c+1)... *)
  (* directly build a index matrix or edge table*)
  let degree =
    let degree_array = Array.make length 0 in
    let () = List.iter
               (fun item ->
                 (List.iter
                    (fun sub_item ->
                      degree_array.(sub_item)<-degree_array.(sub_item)+1
                    )
                    sub_item)
               ) segment_map
    in
    Array.fold_left
      (fun (i,d) item ->
        (i+1,(i,item)::d))
      (0,[]) degree_array
  in  
  let (queue,degree) = degree_extract_zero [] degree in
  helper queue degree []
        
  
let generate_mapping explst =  
  Array.of_list explst
;;

let get_map mapping index =
  Array.get mapping index
;;

let generate_seed_formula seed mapping =
  let rec inner_helper var index seed mapping =
    let new_var = get_map mapping index in
    match seed with
    | [h] ->
       if h=0
       then
         mkEqExp var new_var no_pos
       else
         if h=1
         then mkGtExp var new_var no_pos
         else mkLtExp var new_var no_pos
    | h::tail ->
       let newf =
         if h=0
         then
           mkEqExp var new_var no_pos
         else
           if h=1
           then mkGtExp var new_var no_pos
           else mkLtExp var new_var no_pos
       in
       mkAnd newf (inner_helper var (index+1) tail mapping) no_pos
    | [] -> failwith "generate_seed_formula: Invalid input"
  in
  let rec helper index seed mapping =
    let var = get_map mapping index in
    match seed with
    | h::tail ->
       let newf = inner_helper var (index+1) h mapping in
       mkAnd newf (helper (index+1) tail mapping) no_pos
    | [] -> Cpure.mkTrue no_pos
  in
  helper 0 seed mapping
;;
(* seed: list of list *)
let from_seed_to_map seed =
  let length = List.length seed in
  let map = object
      val m = Array.make_matrix length length (-1)
      method build_map =
        let mk_inner_array start seed =
          let array = Array.make length (-1) in
          let () = List.iteri (fun i item -> array.(i+start)<-item) seed in
          array
        in
        List.iteri
          (fun i item ->
            m.(i)<-(mk_inner_array i item))
          seed

      method get_map a b =
        if a<b
        then m.(a).(b)
        else
          if a>b
          then m.(b).(a)
          else 0
    end
  in
  let () = map#build_map in
  map
;;

let enumerate ante conseq =
  let lhs_p = get_pure ante in
  let rhs_p = get_pure conseq in
  let puref = mkAnd lhs_p rhs_p no_pos in
  let anteTrans = new arrPredTransformer ante in
  let conseqTrans = new arrPredTransformer conseq in
  let vlst = remove_dups_exp_lst ((anteTrans#get_var_set)@(conseqTrans#get_var_set)) in
  let () = print_endline (str_list !str_exp vlst) in
  let mapping = Array.of_list vlst in
  let do_biabduction seed =
    let seed = List.rev seed in
    (* let () = print_endline (str_list (str_list string_of_int) seed) in *)
    let seed_f = generate_seed_formula seed mapping in
    if isSat (mkAnd seed_f puref no_pos)
    then
      let () = print_endline ("seed_f: "^(!str_pformula seed_f)) in
      let () = print_endline ("puref: "^(!str_pformula puref)) in
      print_endline "Sat"
    else
      ()
      (* print_endline "Unsat" *)
  in
  let range =
    let rec range_gen i =
      if i<0
      then []
      else i::(range_gen (i-1))
    in
    range_gen ((List.length vlst)-1)
  in
  enumerate_solution_seed range do_biabduction
;;
             
  
let cf_biabduction ante conseq =
  let lhs_p = get_pure ante in
  let rhs_p = get_pure conseq in
  let ante_seq = (new arrPredTransformer ante)#formula_to_arrPred in
  let conseq_seq = (new arrPredTransformer conseq)#formula_to_arrPred in  
  let (antiframe,frame,prooftrace) = biabduction (lhs_p,ante_seq) (rhs_p,conseq_seq) in
  let (cantiframe,cframe) = (clean_gap antiframe,clean_gap frame) in
  let str_trace_pair (alst,clst) =
    "  "^(str_seq alst)^" |= "^(str_seq clst)
  in
  let str_trace trace =
    List.fold_left (fun r pair -> (str_trace_pair pair)^"\n"^r) "" trace
  in
  print_endline"############## Results of Bi-Abduction Inference ################";
  print_endline ("# pure: "^(!str_pformula lhs_p));
  print_endline ("# anti-frame: "^(str_seq cantiframe));
  print_endline ("# frame: "^(str_seq cframe));
  print_endline "############## ####### Proof Trace ###########  ################";
  print_endline (str_trace prooftrace);
  ()
  (* print_endline "############## ####### ########### ###########  ################"             *)
;;
