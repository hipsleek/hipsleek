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

let is_same_exp e1 e2 =
  check_eq_exp e1 e2
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
  Tpdispatcher.tp_is_sat f "111"
  
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
      then [(self#getAsegStart hf);(self#getAsegEnd hf)]
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

(* class biabduction_data (ante,conseq) = *)
(*   let build_var_rel_map = () in *)
(*   let build_segment_map vrmap = *)
(*   in *)
(*   object(self) *)
(*     val lhsp = ante#get_pure *)
(*     val rhsp = conseq#get_pure *)
(*     val lhshp = ante#get_heap *)
(*     val rhshp = conseq#get_heap *)
(*     val var_lst = remove_dups_exp_lst ((ante#get_var_set)@(conseq_get_var_set)) *)
(*     val segment_lst =  *)
(*     val var_num = 0 *)
(*     val segment_num = 0 *)
(*     val var_rel_map = Array.make_matrix var_num var_num (-1) *)
(*     val segment_map = Array.make_matrix segment_num segment_num (-1) *)
(*     method revised_var_rel_matrix_from_seed seed = *)
(*       let new_var_rel_map = Array.copy var_rel_map in *)
(*         let rec helper seed_head seed_tail = *)
(*           match seed_tail with *)
(*           | h::tail -> *)
(*              let () = update_var_rel_matrix new_matrix lt h in *)
(*              let () = update_var_rel_matrix new_matrix gt h in *)
(*              helper (h::seed_head) tail *)
(*           | [] -> new_matrix *)
(*         in *)
(*         helper [] seed *)

(*     method build_var_rel_map = *)
      

(*     method build_segment_map = *)
(*       let rec trans_helper slst smap index = *)
(*           match slst with *)
(*           | h::tail -> *)
(*              let rec update_one curi index smap = *)
(*                if curi<index *)
(*                then smap.(index).(curi) <- 2-smap.(curi).(index) *)
(*                else *)
(*                  let () = smap.(index).(curi) <- compare_seg index curi in *)
(*                  update_one (curi+1) index smap *)
(*              in *)
(*              let () = update_one 0 index smap in *)
(*              trans_helper tail smap (index+1) *)
(*           | [] -> () *)
(*         in *)
(*         trans_helper segmentlst segment_map 0 *)
(*   end *)
(* ;; *)
                
  
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

(* (\* map is the matrix of variables *\) *)
(* let topological_base_enumerate badata = *)
(*   let rec degree_minus_one degree target= *)
(*     List.map (fun (i,d) -> *)
(*         if badata#lt target i *)
(*         then (i,d-1) *)
(*         else (i,d) *)
(*       ) degree *)
(*   in *)
(*   let rec pick_degree_zero_orig head tail ()= *)
(*     match tail with *)
(*     | ((i,d) as h)::t -> *)
(*        if d=0 *)
(*        then *)
(*          Some ((i,d), degree_minus_one (head@tail), pick_degree_zero_orig (head@[h]) t) *)
(*        else *)
(*          pick_degree_zero_orig (head@[h]) tail () *)
(*     | [] -> *)
(*        None *)
(*   in *)
(*   let rec helper cur seed pick_degree_zero k () = *)
(*     if cur = badata#segment_num *)
(*     then *)
(*       do_biabduction seed *)
(*     else *)
(*       match pick_degree_zero () with *)
(*       | Some ((i,d),degree_i,pick_degree_zero_i) -> *)
(*          helper (cur+1) (i::seed) (pick_degree_zero_orig [] degree_i) (helper cur seed pick_degree_zero_i k) *)
(*       | None ->        *)
(*          k () *)
(*   in *)
(*   let degree = *)
(*     let degree_array = Array.make length 0 in *)
(*     let () = List.iter *)
(*                (fun item -> *)
(*                  (List.iter *)
(*                     (fun sub_item -> *)
(*                       degree_array.(sub_item)<-degree_array.(sub_item)+1 *)
(*                     ) *)
(*                     sub_item) *)
(*                ) segment_map *)
(*     in *)
(*     Array.fold_left *)
(*       (fun (i,d) item -> *)
(*         (i+1,(i,item)::d)) *)
(*       (0,[]) degree_array *)
(*   in     *)
(*   helper degree [] (pick_degree_zero_orig [] degree) (fun x -> ())   *)
(* ;; *)
  
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

let enumerate_order vlst do_biabduction =
  let length = List.length vlst in
  (* let rec inner_helper lst c eqlst k () = *)
  (*   match lst with *)
  (*   | h1::(h2::tail) -> *)
  (*      inner_helper (h2::tail) (fun l -> c l) ((h1,h2)::eqlst) (inner_helper (h2::tail) (fun l->c (h1::l)) eqlst k) () *)
  (*   | _ -> *)
  (*      k (do_biabduction (c lst,eqlst)) *)
  (* in *)
  let rec eq_inner_helper lst eqlst other_lst k do_something () =
    (* let () = print_endline ("eq_inner_helper: "^(str_list string_of_int lst)^", "^(str_list string_of_int eqlst)^", "^(str_list string_of_int other_lst)) in *)
    match lst with
    | h::tail ->
       eq_inner_helper tail (h::eqlst) other_lst (eq_inner_helper tail eqlst (h::other_lst) k do_something) do_something ()
    | [] ->
       do_something other_lst eqlst k
  in
  let rec eq_helper lst eqlst k do_something =
    (* let () = print_endline ("eq_helper: "^(str_list string_of_int lst)^", "^(str_list (str_list string_of_int) eqlst)) in *)
    match lst with
    | h::tail ->
       eq_inner_helper tail [h] [] k (fun other_lst sub_eqlst newk -> eq_helper other_lst (sub_eqlst::eqlst) newk do_something) ()
    | [] ->
       do_something eqlst k  
  in
  let sort_helper eqlst k =
    (* let () = print_endline (str_list (str_list string_of_int) eqlst) in *)
    let length = List.length eqlst in
    let rec helper vlsthead vlsttail (seed,eqlst) k ()  =
      match vlsttail with
      | h::tail ->
         helper [] (vlsthead@tail) (h::seed,eqlst) (helper (vlsthead@[h]) tail (seed, eqlst) k) ()
      | [] ->
         if List.length seed = length
         then
           k (do_biabduction (seed,eqlst))
             (* k (inner_helper seed (fun l->l) [] (fun x->()) ()) *)
         else
           k ()
    in
    let vlst = List.map
                 (fun lst ->
                   match lst with
                   | h::tail -> h
                   | [] -> failwith "sort_helper: Invalid input"
                 ) eqlst
    in
    helper [] vlst ([],eqlst) k ()
  in
  eq_helper vlst [] (fun x->()) sort_helper
;;

let generate_eq_formula eqlst vmap=
  let rec helper eqlst f =
    match eqlst with
    | e1::(e2::tail) ->
       helper (e2::tail) (mkAnd (mkEqExp (vmap#get_var e1) (vmap#get_var e2) no_pos) f no_pos)
    | _ -> f
  in
  List.fold_left (fun r item -> mkAnd (helper item (Cpure.mkTrue no_pos)) r no_pos) (Cpure.mkTrue no_pos) eqlst
;;  

let from_order_to_formula seed vmap =
  let rec helper lastv seed f=
    match seed with
    | [h] ->
       (mkAnd f (mkLtExp lastv (vmap#get_var h) no_pos) no_pos)       
    | h::tail ->
       let newv = vmap#get_var h in
       helper newv tail (mkAnd (mkLtExp lastv newv no_pos) f no_pos)    
    | [] ->
       failwith "from_order_to_formula: Invalid input"
  in
  match seed with
  | h1::((h2::t) as tail)->
     (helper (vmap#get_var h1) tail (Cpure.mkTrue no_pos))
  | _ ->
     Cpure.mkTrue no_pos
;;
  
let sort_seq sorted_var_lst seq =
  let cmp_end_point e1 e2 =
    let rec helper lst e1 e2 =
      match lst with
      | h::tail ->
         if is_same_exp h e1
         then -1
         else
           if is_same_exp h e2
           then 1
           else
             helper tail e1 e2
      | [] ->
         failwith "cmp_end_point: Invalid input"
    in
    if (is_same_exp e1 e2)
    then 0
    else helper sorted_var_lst e1 e2
  in
  let cmp_two_pred p1 p2 =
    match p1,p2 with
    | Aseg (_,f1,t1), Aseg (_,f2,t2)
      | Gap (_,f1,t1), Aseg (_,f2,t2)
      | Aseg (_,f1,t1), Gap (_,f2,t2)
      | Gap (_,f1,t1), Gap (_,f2,t2) ->
       if (cmp_end_point f1 f2 = 0 && cmp_end_point t1 t2 = 0)
       then 0
       else
         if (cmp_end_point f1 t2)=1 (* f1>t2 *)
         then 1
         else
           if (cmp_end_point f2 t2)=1 (* f2>t1 *)
           then -1
           else failwith "sort_seq: Invalid input"
                         
    | Aseg (_,f1,t1), Elem (_,f2)
      | Gap (_,f1,t1), Elem (_,f2) ->
       if (cmp_end_point f1 f2)=1 (* f1>f2 *)
       then 1
       else
         if (cmp_end_point f2 t1)=1 || (cmp_end_point f2 t1)=0 (* f2>=f1 *)
         then -1
         else failwith "sort_seq: Invalid input"
    | _,_ -> failwith "cmp_two_pred: TO BE IMPLEMENTED"
  in
  List.sort cmp_two_pred seq
;;

let print_biabduction_result antiframe frame puref prooftrace=
  let str_trace_pair (alst,clst) =
    "  "^(str_seq alst)^" |= "^(str_seq clst)
  in
  let str_trace trace =
    List.fold_left (fun r pair -> (str_trace_pair pair)^"\n"^r) "" trace
  in
  print_endline"############## Results of Bi-Abduction Inference ################";
  print_endline ("|| pure: "^(!str_pformula puref));
  print_endline ("|| anti-frame: "^(str_seq antiframe));
  print_endline ("|| frame: "^(str_seq frame));
  print_endline "############## ####### Proof Trace ###########  ################";
  print_endline (str_trace prooftrace);
  ()
;;

let enumerate ante conseq enumerate_method generate_seed_formula =
  let lhs_p = get_pure ante in
  let rhs_p = get_pure conseq in
  let puref = mkAnd lhs_p rhs_p no_pos in
  let anteTrans = new arrPredTransformer ante in
  let conseqTrans = new arrPredTransformer conseq in
  let anteseq = anteTrans#formula_to_arrPred in
  let conseqseq = conseqTrans#formula_to_arrPred in
  let vlst = remove_dups_exp_lst ((anteTrans#get_var_set)@(conseqTrans#get_var_set)) in
  let () = print_endline (str_list !str_exp vlst) in

  let mapping =
    object(self)
      val m = Array.of_list vlst
      method get_var index =
        Array.get m index

      method get_var_lst order =
        List.map (fun index -> self#get_var index) order

      method get_order_formula seed =
        from_order_to_formula seed self

      method get_eq_formula eqlst =        
        generate_eq_formula eqlst self

      method get_formula_from_order (seed, eqlst) =
        mkAnd (self#get_order_formula seed) (self#get_eq_formula eqlst) no_pos
    end
  in
  let do_biabduction (seed,eqlst) =
    let seed_f = mapping#get_formula_from_order (seed,eqlst) in
    (* let () = print_endline ("seed_f: "^(!str_pformula seed_f)) in *)
    if isSat (mkAnd seed_f puref no_pos)
    then
      let sorted_var_lst = mapping#get_var_lst seed in
      let () = print_endline (str_list !str_exp sorted_var_lst) in
      let sorted_ante_seq = sort_seq sorted_var_lst (anteTrans#formula_to_arrPred) in
      let sorted_conseq_seq = sort_seq sorted_var_lst (conseqTrans#formula_to_arrPred) in
      let (antiframe,frame,prooftrace) = biabduction (seed_f,sorted_ante_seq) (rhs_p,sorted_conseq_seq) in
      let (cantiframe,cframe) = (clean_gap antiframe,clean_gap frame) in
      print_biabduction_result cantiframe cframe seed_f prooftrace
                               (* let () = print_endline ("seed_f: "^(!str_pformula seed_f)) in *)
                               (* let () = print_endline ("puref: "^(!str_pformula puref)) in *)
                               (* print_endline "Sat" *)
    else
      ()
        
  in
  let range =
    let rec range_gen i =
      if i<0
      then []
      else i::(range_gen (i-1))
    in
    range_gen ((List.length vlst)-1)
  in
  enumerate_method range do_biabduction
;;

type 'a seq =
  | Basic of ('a arrPred)
  | Seq of (('a seq) * ('a seq))
  | Star of (('a seq) list)
  | Emp
;;

let mkAsegBasic b s e =
  Basic (Aseg (b,s,e))
;;


let mkGapBasic b s e =
  Basic (Gap (b,s,e))
;;
  

let mkSeq pred seq =
  Seq (pred, seq)
;;

let mkStar plst =
  Star plst
;;

type vrelation =
  | Gt
  | Eq
  | Lt
  | Unk
;;

(* let po_biabduction ante conseq = *)
(*   let checkSat vmap = *)
(*     true *)
(*   in *)
(*   let relation e1 e2 = *)
(*     Gt *)
(*   in *)
  (* let lazy_sort plst vmap k = *)
  (*   (\* The  k can also be configured here... *\) *)
  (*   (\* Actually all the k can has its own continuation *\) *)
  (*   let rec partition_one vmap item pivot k () = *)
  (*     match item with *)
  (*     | Basic p -> *)
  (*        ( match cmp_segment p pivot with *)
  (*          | Unk -> partition_one (add_vmap p<pivot) item pivot *)
  (*                                 (fun (llst,rlst) newk -> k (llst,rlst) (partition_one (add_vmap p>pivot) item pivot newk)) *)
  (*          | _ -> failwith "TO BE IMPLEMENTED" *)
  (*        ) *)
  (*     | Seq (l,r) -> *)
  (*        partition_one l pivot *)
  (*                      ( fun (leftlst,rightlst) newk1 -> *)
  (*                        match leftlst,rightlst with *)
  (*                        | _ , [] -> partition_one r pivot *)
  (*                                                  (fun (llst,rlst) newk2 -> *)
  (*                                                    k ((llst@leftlst),rlst) *)
  (*                                                      (fun r3 newk3 -> *)
  (*                                                        newk1 r3 *)
  (*                                                              (fun r4 newk4 -> *)
  (*                                                                newk2 r4 newk4))) *)
  (*                        | _ , _ -> k (leftlst,(rigthlst@r)) newk1 *)
  (*                      ) *)
  (*     | Star plst -> *)
  (*        partition_lst lst pivot k *)
  (*     | Emp -> k ([],[]) (fun x newk-> newk x) *)
  (*   and partition_lst lst pivot k () = *)
  (*     match lst with *)
  (*     | h::tail -> *)
  (*        partition_one h pivot (fun llst1 rlst1 newk1 -> partition_lst tail pivot (fun llst2 rlst2 -> k (llst1@llst2) (rlst1@rlst2))) *)
  (*     | [] -> k [] [] *)
  (*   in *)
  (*   let rec get_pivot h k = *)
  (*     match h with *)
  (*     | Basic _ -> k (h,None) *)
  (*     | Seq (l,r) -> get_pivot l *)
  (*                              (fun (p,rest) -> (p, Some (mkSeq rest r))) *)
  (*     | Star (p::tail) -> get_pivot p *)
  (*                                   (fun (newp,rest) -> (newp, Some (Star (rest::tail)))) *)
  (*   in *)
  (*   let rec lazy_sort_helper p k = *)
  (*     match p with *)
  (*     | Basic _ -> k (h,None) *)
  (*     | Seq (l,r) -> lazy_sort_helper l *)
  (*                                     (fun (h,rest_op) -> *)
  (*                                       match rest_op with *)
  (*                                       | None -> k (h,Some r) *)
  (*                                       | Some rest -> k (h, Some (mkSeq rest r)) *)
  (*                                     ) *)
  (*     | Star plst -> partition plst *)
  (*                              (fun (llst,rlst) -> (\* the pivot has to be in the left lst *\) *)
  (*                                match llst with *)
  (*                                | [h] -> mkSeq *)
    
  (* in *)
  (* let rec pick_min_one p k = *)
  (*   match p with *)
  (*   | Basic _ -> k p None *)
  (*   | Seq (l,r) -> pick_min l *)
  (*                           (fun m rest_op -> *)
  (*                             match rest_op with *)
  (*                             | Some rest -> (m,Some (mkSeq rest r)) *)
  (*                             | None -> (m, Some r) *)
  (*                           ) *)
  (*   | Star plst -> pick_min_lst plst k *)

  (* let one_line_k x k = *)
  (*   k Rect k *)
  (* in *)
  (* let test_k k newk =           (\* insert newk between k and k1 *\) *)
  (*   fun k1 -> *)
  (*   k (fun k2 -> newk (test_k k1 k2)) *)



                     
  (* let rec test_k newk1 newk2 = *)
  (*   fun k1 -> *)
  (*   newk1 *)
  (*     (fun k2 -> *)
  (*       newk2 k1) *)
  (* in *)
  (* let rec cmp_pred h1 h2 k = *)
  (*   match h1, h2 with *)
  (*   | Basic p1, Basic p2 -> *)
  (*   (\* cmp_helper p1 p2 k *\) *)
  (*      k (Gt,h1,h2) null_k *)
  (*   | Basic p, Seq (l,r) *)
  (*     | Seq (l,r) , Basic p -> *)
  (*      cmp_pred h1 l k *)
  (*   | Star plst , _ -> *)
  (*      bubble_push plst *)
  (*                  ( fun x1 newk1 -> *)
  (*                    cmp_pred x1 h2 *)
  (*                             ( fun x2 newk2 -> *)
  (*                               k x2 *)
  (*                                 ( fun x3 newk3 -> *)
  (*                                   newk1 x3 *)
  (*                                         ( fun x4 newk4 -> *)
  (*                                           newk2  *)

  (*   | _ , Star plst -> *)
  (*      cmp_pre h1 (bubble_push plst) *)
  (* and bubble_push plst k = *)
  (*   match plst with *)
  (*   | h::tail -> bubble_push tail *)
  (*                             ( *)
  (*                               fun lst newk1 -> *)
  (*                               match lst with *)
  (*                               | h1::tail1 -> *)
  (*                                  cmp_pred h h1 *)
  (*                                           ( fun (rel,newh,newh1) newk2 -> *)
  (*                                             let newk = *)
  (*                                               fun x3 newk3 -> *)
  (*                                               newk1 x3 *)
  (*                                                     (fun x4 newk4 -> *)
  (*                                                       newk2 x4 newk4) *)
  (*                                             in *)
  (*                                             match rel with *)
  (*                                             | Gt -> k (newh::(newh1::tail1)) newk *)
  (*                                             | Lt -> k (h::(h1::tail1)) newk *)
  (*                                           ) *)
  (*                             ) *)
  (*   | [] -> k [] plain_newk *)
(* in *)

  
let po_biabduction ante conseq =
  let checkSat vmap =
    true
  in
  let relation e1 e2 =
    Gt
  in
  let rec bubble_push p vmap k =
    let rec bubble_push_helper plst vmap k =
      match plst with
      | h::tail ->
         bubble_push_helper tail
                            vmap
                            ( fun (x,newvmap) ->
                              match x with
                              | h1::tail ->
                                 compare h h1 vmap
                                         ( fun (x1,p1,p2) ->
                                           match x1 with
                                           | Unk ->
                                              k ((h::(h1::tail)), newvmap#add_segment_gt p1 p2);
                                              k ((h1::(h::tail)), newvmap#add_segment_gt p2 p1);
                                              ()
                                           | Gt -> k ((h1::(h::tail)), newvmap)
                                           | _ -> failwith "bubble_push_helper: TO BE IMPLEMENTED"
                                                           
                                         )
                              | [] -> k ([h],vmap)
                            )
      | [] -> k ([],vmap)
    in
    match p with
    | Star plst ->
       bubble_push_helper plst vmap
                          ( fun (x,newvmap) ->
                            match x with
                            | h::tail -> k ((mkSeq h (mkStar tail)),newvmap)
                            | [] -> failwith "bubble_push: Invalid input"
                          )
    | Seq (l,r) ->
       bubble_push l vmap (fun (x,newvmap) -> k ((mkSeq x r),newvmap))
    | Basic _ -> k (p,vmap)
    | _ -> failwith "bubble_push: TO BE IMPLEMENTED"
  and compare h1 h2 vmap k =
    match h1, h2 with      
    | Basic p1, Basic p2 ->
       k ((vmap#compare_segment p1 p2),p1,p2)
    | Basic p, Seq (l,r)
      | Seq (l,r) , Basic p ->
       compare h1 l vmap k
    | Star plst , _ ->
       bubble_push h1 vmap
                   ( fun (x,newvmap)->
                     compare x h2 newvmap k
                   )
    | _ , _ -> failwith "compare: TO BE IMPLEMENTED"
  in
  let rec helper ante conseq vmap ((antiframe,frame,prooftrace) as ba) k =
    (* let split_case ante conseq vmap ba k e1 e2 = *)
    (*   let vmapgt = vmap#extend (Gt,e1,e2) in *)
    (*   let vmapeq = vmap#extend (Eq,e1,e2) in *)
    (*   let vmaplt = vmap#extend (Lt,e1,e2) in *)
    (*   helper ante conseq vmapgt ba *)
    (*          (fun _ _ -> *)
    (*            helper ante conseq vmapeq ba *)
    (*                   (fun _ _ -> helper ante conseq vmaplt ba k)) *)
    (* in *)
    if checkSat vmap            (* An incremental checking procedure here *)
    then
      match ante, conseq with
      | Basic h1, Basic h2 ->              
         ( match h1, h2 with
           | Aseg (b1, s1, e1), Aseg (b2, s2, e2) ->
              ( match vmap#compare_points s1 s2 with
                | Unk ->
                   helper ante conseq (vmap#extend (Gt,s1,s2)) ba k;
                   helper ante conseq (vmap#extend (Eq,s1,s2)) ba k;
                   helper ante conseq (vmap#extend (Lt,s1,s2)) ba k;
                   ()
                | Gt -> helper (mkSeq (mkGapBasic b1 s2 s1) ante) conseq vmap ba k
                | Lt -> helper ante (mkSeq (mkGapBasic b2 s1 s2) conseq) vmap ba k
                | Eq ->
                   (
                     match vmap#compare_points e1 e2 with
                     | Unk ->
                        helper ante conseq (vmap#extend (Gt,e1,e2)) ba k;
                        helper ante conseq (vmap#extend (Eq,e1,e2)) ba k;
                        helper ante conseq (vmap#extend (Lt,e1,e2)) ba k;
                        ()                     
                     | Gt -> k (mkAsegBasic b1 e2 e1) Emp ba vmap
                     | Lt -> k Emp (mkAsegBasic b2 e1 e2) ba vmap
                     | Eq -> k Emp Emp ba vmap
                   )
              )
           | _, _ -> failwith "TO BE IMPLEMENTED"
         )
      | Seq (l1,r1), Seq (l2,r2) ->
         let newk lefta leftc newba newvmap =
           match lefta, leftc with
           | Emp, Emp -> helper r1 r2 newvmap newba k
           | Emp, Basic _ -> helper r1 (mkSeq leftc r2) newvmap newba k
           | Basic _, Emp -> helper (mkSeq lefta r1) r2 newvmap newba k
           (* | Basic _, Basic _-> helper (mkSeq lefta r1) (mkSeq leftc r2) vmap newba k *)
           | _, _ -> failwith "Seq vs. Seq: Invalid input"
         in
         helper l1 l2 vmap ba newk
      | Emp, Emp -> k ante conseq ba vmap
      | Star plst, _ -> bubble_push ante vmap (fun (sorted_ante,newvmap) -> helper sorted_ante conseq newvmap ba k)
      | Seq _, Star plst -> bubble_push ante vmap (fun (sorted_conseq,newvmap) -> helper ante sorted_conseq newvmap ba k)
      | _, _ -> failwith "TO BE IMPLEMENTED"
    else
      failwith "TO BE IMPLEMENTED"
  in
  ()
  (* helper ante conseq vmap (antiframe,frame,prooftrace) (fun x->()) *)
;;
         
        
           (* | Aseg (b1, s1, e1), Elem (b2, s2) -> *)
         (*      ( match relation s1 s2 with *)
         (*        | Unk -> *)
         (*           split_case ante conseq vmap ba k s1 s2 *)
         (*        | Gt -> helper (mkSeq (mkGap b1 s2 s1) ante) conseq vmap ba k *)
         (*        | Lt -> helper ante (mkSeq (mkGap b2 s1 s2) conseq) vmap ba k *)
         (*        | Eq -> *)
         (*           ( *)
         (*             match relation s1 e1 with *)
         (*             | Unk -> *)
         (*                split_case ante conseq vmap ba k s1 e1 (\* can be optimized with two cases only *\) *)
         (*             | Lt -> helper (mkSeq (mkAseg b1 (incOne s1) e1) tail1) tail2 vmap ba k *)
         (*             | Eq -> helper tail1 conseq vmap ba k *)
         (*             | Gt -> failwith "Aseg vs. Elem: Invalid input" *)
         (*           ) *)
         (*      ) *)
         (*   | Aseg (b1, s1, e1), Gap (b2, s2, e2) -> *)
         (*      ( match relation s1 s2 with *)
         (*        | Eq -> *)
         (*           ( match relation e1 e2 with *)
         (*             | Unk -> *)
         (*                split_case ante conseq vmap ba k e1 e2                          *)
         (*             | Gt -> helper (mkSeq (mkAseg b1 e2 e1) tail1) tail2 vmap (antiframe,frame#add (mkAseg b1 s1 e2),prooftrace) k *)
         (*             | Lt -> helper tail1 (mkSeq (mkGap b2 e1 e2) tail2) vmap (antiframe,frame#add (mkAseg b1 s1 e1),prooftrace) k *)
         (*             | Eq -> helper tail1 tail2 vmap ba k *)
         (*           )                *)
         (*        | _ -> failwith "Aseg vs. Gap: TO BE IMPLEMENTED" *)
         (*      ) *)
         (*   | Elem (b1, s1), Elem (b2, s2) -> *)
         (*      ( match relation s1 s2 with *)
         (*        | Unk -> *)
         (*           split_case ante conseq vmap ba k s1 s2 *)
         (*        | Gt -> helper (mkSeq (mkGap b1 s2 s1) ante) conseq vmap ba k *)
         (*        | Lt -> helper ante (mkSeq (mkGap b2 s1 s2) conseq) vmap ba k *)
         (*        | Eq -> helper tail1 tail2 vmap ba k *)
         (*      ) *)
         (*   | Elem (b1, s1), Aseg (b2, s2, e2) -> *)
         (*      ( match relation s1 s2 with *)
         (*        | Unk -> *)
         (*           split_case ante conseq vmap ba k s1 s2 *)
         (*        | Gt -> helper (mkSeq (mkGap b1 s2 s1) ante) conseq vmap ba k *)
         (*        | Lt -> helper ante (mkSeq (mkGap b2 s1 s2) conseq) vmap ba k *)
         (*        | Eq -> *)
         (*           ( match relation s2 e2 with *)
         (*             | Unk -> *)
         (*                split_case ante conseq vmap ba k s1 e2 (\* can be optimized with two cases only *\) *)
         (*             | Lt -> helper tail1 (mkSeq (mkAseg b2 (incOne s2) e2) tail2) vmap ba k *)
         (*             | Eq -> helper ante tail2 vmap ba k *)
         (*             | Gt -> failwith "Elem vs. Aseg: Invalid input" *)
         (*           ) *)
         (*      ) *)
         (*   | Elem (b1, s1), Gap (b2, s2, e2) -> *)
         (*      ( match relation s1 s2 with *)
         (*        | Unk -> *)
         (*           split_case ante conseq vmap ba k s1 s2 *)
         (*        | Eq -> *)
         (*           ( match relation s2 e2 with *)
         (*             | Unk -> *)
         (*                split_case ante conseq vmap ba k s2 e2 (\* Is it possible that s2>e2? *\) *)
         (*             | Lt -> helper tail1 (mkSeq (mkGap b2 (incOne s2) e2) tail2) vmap (antiframe,(frame#add h1),prooftrace) k *)
         (*             | Eq -> helper ante tail2 vmap ba k *)
         (*             | Gt -> failwith "Elem vs. Aseg: TO BE IMPLEMENTED" *)
         (*           )                 *)
         (*        | Gt -> helper (mkSeq (mkGap b1 s2 s1) ante) conseq vmap ba k *)
         (*        | Lt -> helper ante (mkSeq (mkGap b2 s1 e2) tail2) vmap ba k (\* Just make the gap bigger instead of introducing one more gap *\) *)
         (*      ) *)
         (*   | Gap (b1, s1, e1), Gap (b2, s2, e2) -> *)
         (*      ( match relation s1 s2 with *)
         (*        | Unk -> *)
         (*           split_case ante conseq vmap ba k s1 s2  *)
         (*        | Gt -> helper (mkSeq (mkGap b1 s2 e1) tail1) conseq vmap ba k *)
         (*        | Lt -> helper ante (mkSeq (mkGap b2 s1 e2) tail2) vmap ba k *)
         (*        | Eq -> *)
         (*           ( *)
         (*             match relation e1 e2 with *)
         (*             | Unk -> *)
         (*                split_case ante conseq vmap ba k e1 e2                          *)
         (*             | Gt -> helper (mkSeq (mkGap b1 e2 e1) tail1) tail2 vmap ba k *)
         (*             | Lt -> helper tail1 (mkSeq (mkGap b2 e1 e2) tail2) vmap ba k *)
         (*             | Eq -> helper tail1 tail2 vmap ba k *)
         (*           ) *)
         (*      ) *)
         (*   | Gap (b1, s1, e1), Elem (b2, s2) -> *)
         (*      ( match relation s1 s2 with *)
         (*        | Unk -> *)
         (*           split_case ante conseq vmap ba k s1 s2 *)
         (*        | Eq -> *)
         (*           ( match relation s1 e1 with *)
         (*             | Unk -> *)
         (*                split_case ante conseq vmap ba k s1 e1 *)
         (*             | Lt -> helper (mkSeq (mkGap b1 (incOne s1) e1) tail1) tail2 vmap ((antiframe#add h2),frame,prooftrace) k *)
         (*             | Eq -> helper tail1 conseq vmap ba k *)
         (*             | Gt -> failwith "Elem vs. Aseg: Invalid input" *)
         (*           )                 *)
         (*        | Gt -> helper (mkSeq (mkGap b1 s2 e1) tail1) conseq vmap ba k (\* Just make the gap bigger instead of introducing one more gap *\) *)
         (*        | Lt -> helper ante (mkSeq (mkGap b2 s1 s2) conseq) vmap ba k *)
         (*      ) *)
         (*   | Gap (b1, s1, e1), Aseg (b2, s2, e2) -> *)
         (*      ( match relation s1 s2 with *)
         (*        | Eq -> *)
         (*           ( match relation e1 e2 with *)
         (*             | Unk -> *)
         (*                split_case ante conseq vmap ba k e1 e2 *)
         (*             | Gt -> helper (mkSeq (mkGap b1 e2 e1) tail1) tail2 vmap (antiframe#add (mkAseg b1 s2 e2),frame,prooftrace) k *)
         (*             | Lt -> helper tail1 (mkSeq (mkAseg b2 e1 e2) tail2) vmap (antiframe#add (mkAseg b1 s2 e1),frame,prooftrace) k *)
         (*             | Eq -> helper tail1 tail2 vmap ba k *)
         (*           ) *)
         (*        | _ -> failwith "Aseg vs. Gap: TO BE IMPLEMENTED" *)
         (*      ) *)
         (* ) *)  
(*   in *)
(*   helper ante conseq vmap (antiframe,frame,prooftrace) (fun x->()) *)
(* ;; *)
  
             
let enumerate_with_order ante conseq =
  enumerate ante conseq enumerate_order from_order_to_formula
;;
  
let cf_biabduction ante conseq =
  let lhs_p = get_pure ante in
  let rhs_p = get_pure conseq in 
  let ante_seq = (new arrPredTransformer ante)#formula_to_arrPred in
  let conseq_seq = (new arrPredTransformer conseq)#formula_to_arrPred in  
  let (antiframe,frame,prooftrace) = biabduction (lhs_p,ante_seq) (rhs_p,conseq_seq) in
  let (cantiframe,cframe) = (clean_gap antiframe,clean_gap frame) in
  print_biabduction_result cantiframe cframe lhs_p prooftrace
;;
