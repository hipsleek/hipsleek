(* Randomly generate test cases *)
open Arr_biabduction_extend
open Arr_entailment_with_frame
open Random_util

let str_asegPredplus_input aseg =
  match aseg with
  | Aseg_p (s,e) ->
     "Aseg<"^(!str_sv s)^","^(!str_sv e)^">"
  | AsegNE_p (s,e) ->
     "AsegNE<"^(!str_sv s)^","^(!str_sv e)^">"
  | Gap_p (s,e)->
     "Gap<"^("_")^","^(!str_sv s)^","^(!str_sv e)^">"
  | Pointsto_p (s,v) ->
     "Elem<"^(!str_sv s)^","^(!str_sv v)^">"
;;


       
let memory_map_to_asegPredplus dpointto daseg map =
  let rec trans_helper map =
    match map with
    | (f,t)::tail ->
       let to_asegNE_or_aseg f t =
         let fvar = global_get_new_var_public () in
         let tvar = global_get_new_var_public () in
         let binding = [mkEq (mkVar fvar) (mkConst f);mkEq (mkVar tvar) (mkConst t)] in
         let (newaseglst,newbindings,ctnv) = trans_helper tail in
         if f=t
         then
           ((mkAseg_p fvar tvar)::newaseglst,binding@newbindings,ctnv)
         else
           ((mkAsegNE_p fvar tvar)::newaseglst,binding@newbindings,ctnv)
       in
       if f=t-1
       then
         if dpointto ()
         then
           let svar = global_get_new_var_public () in
           let uvar = global_get_new_var_public () in
           let (newaseglst,newbindings,ctnv) = trans_helper tail in
           ((mkPointsto_p svar uvar)::newaseglst,[mkEq (mkVar svar) (mkConst f)]@newbindings,[uvar]@ctnv)
         else
           to_asegNE_or_aseg f t
       else
         to_asegNE_or_aseg f t
    | [] -> ([],[],[])
  in
  trans_helper map
;;

let generate_formula_from_map map =
  let dpointto = yes_or_no in
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

let mutate_memory_map map =
  let mutate_one (f,t) =
    if f<t
    then
      let m = get_random f t in
      if f<m
      then
        [(f,m-1);(m,t)]
      else
        [(f,m);(m+1,t)]
    else
      []
  in
                        
  let rec mutate_helper pos i head tail =
    match tail with
    | h::t ->
       if pos=i
       then (List.rev head)@(mutate_one h)@t
       else
         mutate_helper pos (i+1) (h::head) t
    | [] -> failwith "mutate_memory_map: Invalid input"
  in
  let length = List.length map in
  mutate_helper (get_random 0 (length-1)) 0 [] map
;;

let chopping map =
  let rec chopping_helper s e output =
    if s = e
    then List.rev output
    else      
      let new_end = get_random (s+1) e in
      (* let () = print_endline (str_pair string_of_int string_of_int (s,new_end)) in *)
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
  let map = generate_memory_map (seed*5) in
  let (lhs_h,lhs_p,_) = map|>chopping|>generate_formula_from_map in
  let (rhs_h,rhs_p,rhs_cnv) = map|>chopping|>generate_formula_from_map in  
  ((lhs_h,[simplify (mkAndlst (lhs_p@rhs_p))],[]),(rhs_h,[],rhs_cnv))
;;

let generate_random_invalid_entailment seed =
  let map_lhs = generate_memory_map (seed*5) in
  let map_rhs = mutate_memory_map map_lhs in
  let (lhs_h,lhs_p,_) = map_lhs|>chopping|>generate_formula_from_map in
  let (rhs_h,rhs_p,rhs_cnv) = map_rhs|>chopping|>generate_formula_from_map in  
  ((lhs_h,[(mkAndlst (lhs_p@rhs_p))],[]),(rhs_h,[],rhs_cnv))
;;  
  
(* let generate_random_valid_entailment seed = *)
(*   let map = generate_memory_map (seed*10) in *)
(*   let (lhs_h,lhs_p) = map|>chopping|>generate_formula_from_map in *)
(*   let (rhs_h,rhs_p) = map|>chopping|>generate_formula_from_map in   *)
(*   ((lhs_h,lhs_p@rhs_p,[]),(rhs_h,[])) *)
(* ;; *)

let generator_random_entailment_lst generate_entailment num =
  let rec generator_helper num output=
    if num = 0
    then output
    else
      generator_helper (num-1) ((generate_entailment num)::output)
  in
  generator_helper num []
;;



let generate_formatted_entailment_str lhs rhs expect=
  let generate_formula_str (hflst,pflst,eset) =
    let hfstr = str_list_delimeter_raw (fun item -> "base::"^(str_asegPredplus_input item)) hflst "*" "emp" in
    let pfstr = str_list_delimeter_raw !str_pformula pflst "&" "true" in
    let inners = hfstr^"&"^pfstr in
    if List.length eset = 0
    then inners
    else
      "exists "^(str_list_delimeter_raw !str_sv eset "," "")^": "^inners
  in
  let generate_entailment_str lhs rhs =
    (generate_formula_str lhs)^" |- "^(generate_formula_str rhs)
  in
  let s = "infer[@arr_en] "^(generate_entailment_str lhs rhs)^"." in
  s^"\nprint residue.\nexpect "^(expect)^".\n"
;;

let test_aseg num (generator,expect)=
  let header = "pred_prim Aseg<start:int, end:int>.\npred_prim AsegNE<start:int, end:int>.\npred_prim Elem<start:int,value:int>."
  in
  let (entailments,_) =
    List.fold_left
      (fun (r,i) (lhs,rhs) ->
        (r^"\n"^(("// "^(string_of_int i))^"\n"^(generate_formatted_entailment_str lhs rhs expect)),i+1))
      ("",1) (generator_random_entailment_lst generator num)
  in
  header^entailments
;;

let generate_test_file name num expect =
  let file = open_out name in
  let generator =
    if expect = "Valid"
    then generate_random_valid_entailment_relation_only
    else
      if expect = "Fail"
      then generate_random_invalid_entailment
      else failwith "generate_test_file: Invalid input"
  in
  let test_cases = test_aseg num (generator,expect) in
  output_string file test_cases
;;

let () =
  let name = Sys.argv.(1) in
  let num = Sys.argv.(2) in
  let expect = Sys.argv.(3) in
  generate_test_file name (int_of_string num) expect
;;
