(* Randomly generate test cases *)
open Arr_biabduction_extend
open Arr_entailment_with_frame
open Random_util
       
let memory_map_to_asegPredplus dpointto daseg map =
  let rec trans_helper map =
    match map with
    | (f,t)::tail ->
       let to_asegNE_or_aseg f t =
         let fvar = global_get_new_var_public () in
         let tvar = global_get_new_var_public () in
         let binding = [mkEq (mkVar fvar) (mkConst f);mkEq (mkVar tvar) (mkConst t)] in
         let (newaseglst,newbindings) = trans_helper tail in
         if f=t
         then
           ((mkAseg_p fvar tvar)::newaseglst,binding@newbindings)
         else
           ((mkAsegNE_p fvar tvar)::newaseglst,binding@newbindings)
       in
       if f=t-1
       then
         if dpointto ()
         then failwith "to Pointsto_p: TO BE IMPLEMENTED"
         else
           to_asegNE_or_aseg f t
       else
         to_asegNE_or_aseg f t
    | [] -> ([],[])
  in
  trans_helper map
;;

let generate_formula_from_map map =
  let dpointto () =
    false
  in
  let daseg = yes_or_no
  in
  memory_map_to_asegPredplus dpointto daseg map  
;;

let generate_memory_map maxSize =
  let rec pick s e output =
    if s = e
    then List.rev output
    else
      let new_start = get_random s (e-1) in
      let new_end = get_random (new_start+1) e in      
      pick new_end e ((new_start,new_end)::output)
  in
  pick 0 maxSize []
;;

let chopping map =
  let rec chopping_helper s e output =
    if s = e
    then List.rev output
    else      
      let new_end = get_random (s+1) e in
      let () = print_endline (str_pair string_of_int string_of_int (s,new_end)) in
      chopping_helper new_end e ((s,new_end)::output)
  in
  List.concat
    (List.map
       (fun (f,t) ->
         let () = print_endline "***" in
         let () = print_endline (str_pair string_of_int string_of_int (f,t)) in
         chopping_helper f t []) map)
;;
  
(* let generate_random_formula seed = *)
(*   (seed*10) |> generate_random_formula |> chopping |> generate_formula_from_map *)
(* ;; *)

let generate_random_valid_entailment_relation_only seed =
  let map = generate_memory_map (seed*10) in
  let (lhs_h,lhs_p) = map|>chopping|>generate_formula_from_map in
  let (rhs_h,rhs_p) = map|>chopping|>generate_formula_from_map in  
  ((lhs_h,[simplify (mkAndlst (lhs_p@rhs_p))]),(rhs_h,[]))
;;
  
let generate_random_valid_entailment seed =
  let map = generate_memory_map (seed*10) in
  let (lhs_h,lhs_p) = map|>chopping|>generate_formula_from_map in
  let (rhs_h,rhs_p) = map|>chopping|>generate_formula_from_map in  
  ((lhs_h,lhs_p@rhs_p),(rhs_h,[]))
;;

let generator_random_valid_entailment_lst num =
  let rec generator_helper num output=
    if num = 0
    then output
    else
      generator_helper (num-1) ((generate_random_valid_entailment_relation_only num)::output)
  in
  generator_helper num []
;;
  

let generate_formatted_entailment_str lhs rhs =
  let generate_formula_str (hflst,pflst) =
    let hfstr = str_list_delimeter_raw (fun item -> "base::"^(str_asegPredplus item)) hflst "*" "emp" in
    let pfstr = str_list_delimeter_raw !str_pformula pflst "&" "true" in
    hfstr^"&"^pfstr
  in
  let generate_entailment_str lhs rhs =
    (generate_formula_str lhs)^" |- "^(generate_formula_str rhs)
  in
  let s = "infer[@arr_en] "^(generate_entailment_str lhs rhs)^"." in
  (* let () = print_endline s in *)
  s
;;

let _ = List.iter
          (fun (lhs,rhs) ->
            let () = print_endline (generate_formatted_entailment_str lhs rhs) in
            let () = print_endline "print residue." in
            let () = print_endline "expect Valid.\n" in
            ()
          )
          (generator_random_valid_entailment_lst 10)
;;
  


  
      
      
  
  

  
