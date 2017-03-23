#include "xdebug.cppo"

open Cpure
open VarGen
open Cformula
       
type 'exp arrPred =
  | Aseg of ('exp * 'exp * 'exp)
  | Gap of ('exp * 'exp * 'exp)
  | Elem of ('exp * 'exp)
;;


(* Utility on formula and exp *)
let mkOr f1 f2 = Cpure.mkOr f1 f2 None no_pos
;;

let mkAnd f1 f2 = Cpure.mkAnd f1 f2 no_pos
;;

let mkTrue () = Cpure.mkTrue no_pos
;;
  
let rec mkAndlst lst =
  match lst with
  | [h] -> h
  | h::tail -> mkAnd h (mkAndlst tail)
  | [] -> mkTrue ()
;;

let mkGt e1 e2 =
  Cpure.mkGtExp e1 e2 no_pos
;;

let mkLt e1 e2 =
  Cpure.mkLtExp e1 e2 no_pos
;;

let mkLte e1 e2 =
  Cpure.mkLteExp e1 e2 no_pos
;;

let mkGte e1 e2 =
  Cpure.mkGteExp e1 e2 no_pos
;;

let mkEq e1 e2 =
  Cpure.mkEqExp e1 e2 no_pos
;;
  

(* end of Utility on formula and exp  *)
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
  let rhsf = mkEq s1 e1 in
  !tp_imply pf rhsf
;;

let isGt s1 e1 pf =
  (* pf |= s1 > e1 *)
  let rhsf = mkGt s1 e1 in
  !tp_imply pf rhsf
;;

let isGte s1 e1 pf =
  (* pf |= s1 >= e1 *)
  let rhsf = mkGte s1 e1 in
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
     (* "Aseg("^(!str_exp b)^","^(!str_exp s)^","^(!str_exp e)^")" *)
     "Aseg("^("_")^","^(!str_exp s)^","^(!str_exp e)^")"
  | Gap (b,s,e)->
     (* "Gap("^(!str_exp b)^","^(!str_exp s)^","^(!str_exp e)^")" *)
     "Gap("^("_")^","^(!str_exp s)^","^(!str_exp e)^")"
  | Elem (b,s) ->
     (* "Elem("^(!str_exp b)^","^(!str_exp s)^")" *)
     "Elem("^("_")^","^(!str_exp s)^")"
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


(* definition of seq-star  *)
type 'a seq =
  | Basic of ('a arrPred)
  | Seq of (('a seq) * ('a seq))
  | Star of (('a seq) list)
  | Emp
;;

(* Gap will be dropped! *)
let flatten_seq h =
  let rec helper h k =
    match h with
    | Basic p ->
       ( match p with
         | Gap _ -> k []
         | _ -> k [p]
       )
    | Seq (l,r) -> helper l (fun llst -> helper r (fun rlst -> llst@rlst))
    | Star plst -> k (List.concat (List.map (fun x -> helper x (fun a->a)) plst))
    | Emp -> failwith "flatten_seq: Invalid input"
  in
  helper h (fun x->x)
;;

let rec str_seq_star h inner_str =
  match h with
  | Basic p -> inner_str p  
  | Seq (l,r) -> "["^(str_seq_star l inner_str)^";"^(str_seq_star r inner_str)^"]"                  
  | Star plst -> "("^(str_seq_star_lst plst inner_str)^")"
  | Emp -> "Emp"
and str_seq_star_lst hlst inner_str =
  match hlst with
  | [h] -> str_seq_star h inner_str
  | h::tail -> (str_seq_star h inner_str)^"*"^(str_seq_star_lst tail inner_str)
  | [] -> ""
;;

let str_seq_star_arr h =
  str_seq_star h str_arrPred
;;
  
let mkAsegBasic b s e =
  Basic (Aseg (b,s,e))
;;


let mkGapBasic b s e =
  Basic (Gap (b,s,e))
;;
  

let mkSeq seq1 seq2 =
  match seq1, seq2 with
  | Emp, _ -> seq2
  | _, Emp -> seq1
  | _, _ -> Seq (seq1,seq2)
;;

let mkStar plst =
  let rec helper plst k =
    match plst with
    | h::tail ->
       helper tail
              (fun newplst ->
                match h, newplst with
                | Emp, _ -> k newplst
                | Star plst1, _ ->
                   helper plst1
                          (fun newplst1 ->
                            k (newplst1@newplst))
                | _, _ -> k (h::newplst))
    | [] -> k []
  in
  match helper plst (fun x->x) with
  | [] -> Emp
  | [h] -> h
  | newlst -> Star newlst
;;

let mkBasic p =
  Basic p
;;

(* ********** End of definition of seq-star **********  *)

class arrPredTransformer initcf = object(self)
  val cf = initcf               (* cf is Cformula.formula *)
  val mutable eqmap = ([]: (spec_var * exp) list)
  val mutable aseglst = None
  val mutable puref = None
                  
  method find_in_eqmap sv =
    try
      let (_,e1) = List.find (fun (v,e) -> (compare_sv sv v)=0) eqmap
      in
      Some e1
    with _ ->
      None


  method generate_pure =    
    let generate_disjoint_formula_with_two_pred p1 p2 =
      match p1, p2 with
      | Aseg (_,s1,e1), Aseg (_,s2,e2) ->
         mkOr (mkOr (mkGte s2 e1) (mkGte s1 e2)) (mkOr (mkEq s1 e1) (mkEq s2 e2))
      | Aseg (_,s1,e1), Elem (_,s2) ->
         mkOr (mkOr (mkGte s2 e1) (mkGt s1 s2)) (mkEq s1 e1)
      | Elem (_,s1), Aseg (_,s2,e2)  ->
         mkOr (mkOr (mkGte s1 e2) (mkGte s2 s1)) (mkEq s2 e2)
      | Elem (_,s1), Elem (_,s2) ->
         mkOr (mkGt s2 s1) (mkGt s1 s1)
      | _, _ -> mkTrue ()
    in
    let rec generate_disjoint_formula lst flst =
      match lst with
      | h::tail ->
         generate_disjoint_formula tail
                                   (List.map (fun item -> generate_disjoint_formula_with_two_pred h item) tail)
      | [] -> flst
    in
    let rec generate_segment_formula lst flst =
      List.fold_left
        (fun r item ->
          match item with
          | Some f -> f::r
          | None -> r
        )
        []         
        (List.map
           (fun item ->
             match item with
             | Aseg (_,s,e) -> Some (mkLte s e)
             | _ -> None)
           lst
        )
    in

    let lst = self#formula_to_arrPred in
    puref <- Some (mkAndlst ((Cformula.get_pure cf)
                             ::((generate_disjoint_formula lst [])
                                @(generate_segment_formula lst []))));
    ()

  method get_pure =
    match puref with
    | Some f -> f
    | None -> self#generate_pure;
              self#get_pure
          
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


  method generate_arrPred_lst =
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
    let aPrelst =
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
    in
    aseglst <- Some aPrelst

  method formula_to_arrPred =
    match aseglst with
    | Some lst -> lst
    | None ->
       self#generate_arrPred_lst;
       self#formula_to_arrPred
              
  method formula_to_seq =    
    mkStar (List.map mkBasic (self#formula_to_arrPred))
           
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


(* A very simple enumeration, not practical *)
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
         mkEq var new_var
       else
         if h=1
         then mkGt var new_var
         else mkLt var new_var
    | h::tail ->
       let newf =
         if h=0
         then
           mkEq var new_var
         else
           if h=1
           then mkGt var new_var
           else mkLt var new_var 
       in
       mkAnd newf (inner_helper var (index+1) tail mapping)
    | [] -> failwith "generate_seed_formula: Invalid input"
  in
  let rec helper index seed mapping =
    let var = get_map mapping index in
    match seed with
    | h::tail ->
       let newf = inner_helper var (index+1) h mapping in
       mkAnd newf (helper (index+1) tail mapping)
    | [] -> mkTrue ()
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
       helper (e2::tail) (mkAnd (mkEq (vmap#get_var e1) (vmap#get_var e2)) f)
    | _ -> f
  in
  List.fold_left (fun r item -> mkAnd (helper item (mkTrue ())) r) (mkTrue ()) eqlst
;;  

let from_order_to_formula seed vmap =
  let rec helper lastv seed f=
    match seed with
    | [h] ->
       (mkAnd f (mkLt lastv (vmap#get_var h) ) )       
    | h::tail ->
       let newv = vmap#get_var h in
       helper newv tail (mkAnd (mkLt lastv newv) f )    
    | [] ->
       failwith "from_order_to_formula: Invalid input"
  in
  match seed with
  | h1::((h2::t) as tail)->
     (helper (vmap#get_var h1) tail (mkTrue ()))
  | _ ->
     mkTrue ()
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
  print_endline "############## Results of Bi-Abduction Inference ################";
  print_endline ("|| pure: "^(!str_pformula puref));
  print_endline ("|| anti-frame: "^(str_seq antiframe));
  print_endline ("|| frame: "^(str_seq frame));
  print_endline "############## ####### Proof Trace ###########  #################";
  print_endline (str_trace prooftrace);
  ()
;;

let enumerate ante conseq enumerate_method generate_seed_formula =
  
  let anteTrans = new arrPredTransformer ante in
  let conseqTrans = new arrPredTransformer conseq in
  let anteseq = anteTrans#formula_to_arrPred in
  let conseqseq = conseqTrans#formula_to_arrPred in
  let lhs_p = anteTrans#get_pure in
  let rhs_p = conseqTrans#get_pure in
  let puref = mkAnd lhs_p rhs_p in
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
        mkAnd (self#get_order_formula seed) (self#get_eq_formula eqlst)
    end
  in
  let do_biabduction (seed,eqlst) =
    let seed_f = mapping#get_formula_from_order (seed,eqlst) in
    (* let () = print_endline ("seed_f: "^(!str_pformula seed_f)) in *)
    if isSat (mkAnd seed_f puref )
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

(* Lazy enumeration *)
type vrelation =
  | Gt
  | Gte
  | Eq
  | Lt
  | Lte
  | Neq
  | Unk
  | False
;;

let str_vrel vr =
  match vr with
  | Gt -> ">"
  | Gte -> ">="
  | Eq -> "="
  | Lt -> "<"
  | Lte -> "<="
  | Neq -> "!="
  | Unk -> "?"
  | False -> "FALSE"
(* < = > *)
let decode_vrelation i =
  match i with
  | 0 -> False
  | 7 -> Unk                  (* 111 *)
  | 1 -> Gt                     (* 001 *)
  | 2 -> Eq                     (* 010 *)
  | 3 -> Gte                    (* 011 *)
  | 4 -> Lt                     (* 100 *)
  | 5 -> Neq                    (* 101 *)
  | 6 -> Lte                    (* 110 *)
  | _ -> failwith ("decode_vrelation: Invalid input "^(string_of_int i))
;;

let get_opposite_rel i =
  match i with
  | 0 -> 0                  (* 000 -> 000 *)
  | 7 -> 7                  (* 111 -> 111 *)
  | 1 -> 4                  (* 001 -> 110*)
  | 2 -> 5                  (* 010 -> 101*)
  | 3 -> 6                  (* 011 -> 110*)
  | 4 -> 1                  (* 100 -> 001*)
  | 5 -> 2                  (* 101 -> 010*)
  | 6 -> 3                  (* 110 -> 011*)
  | _ -> failwith ("decode_vrelation: Invalid input "^(string_of_int i))

;;
  
let encode_vrelation rel =
  match rel with
  | Gt -> 1
  | Gte -> 3
  | Eq -> 2
  | Lt -> 4
  | Lte -> 6
  | Neq -> 5
  | Unk -> 7
  | False -> 0
;;
  
module Pair_index = struct
  type t = (int*int)
  let compare (t11,t12) (t21,t22) =
    if t11<t21
    then -1
    else
      if t11=t21
      then
        if t12<t22
        then -1
        else
          if t12=t22
          then 0
          else 1
      else
        1
end
;;

module Module_Rel_Matrix = Map.Make(Pair_index);;

(* ************ proof trace ************ *)
type 'a proof_trace =
  | Entry of ('a seq * 'a seq * int)
  | Match of (('a arrPred) * ('a arrPred) * int)
  | Sort of ('a seq * int * int)
  | Reach of (('a arrPred list) * ('a arrPred list) * Cpure.formula * int)
  | DecideSeg of (('a arrPred) * ('a arrPred) * int)
  | DecidePoints of ('a * 'a * int)
  | Branch of (vrelation * 'a * 'a * int)
;;
  

let global_prooftrace = ref []
;;

let prooftrace_depth = ref 0
;;

let push_prooftrace trace =
  global_prooftrace := trace::(!global_prooftrace)
;;

let pop_prooftrace () =
  match !global_prooftrace with
  | [] -> ()
  | h::tail -> global_prooftrace := tail
;;
  
let str_one_prooftrace trace =
  let rec print_indent depth str =
    if depth = 0
    then "   "^str
    else "   "^(print_indent (depth-1) str)
  in
  let print_biabduction antiframe frame puref depth =
    let indent = print_indent depth "   " in
    indent^("anti-frame: "^(str_seq antiframe))^"\n"
    ^indent^("frame: "^(str_seq frame))^"\n"
    ^indent^("pure: "^(!str_pformula puref))
  in
  match trace with
  | Entry (ante,conseq,depth) -> print_indent depth ("[Entry] " ^ (str_seq_star_arr ante) ^ " |= " ^ (str_seq_star_arr conseq))
  | Match (ante,conseq,depth) -> print_indent depth ("[Match] " ^ (str_arrPred ante) ^ " |= " ^ (str_arrPred conseq))
  | Sort (seq,side,depth) ->
     let str_side i =
       match i with
       | 0 -> "LHS"
       | 1 -> "RHS"
       | _ -> failwith "str_side: Invalid input"
     in
     print_indent depth ("[Sort "^(str_side side)^"] "^(str_seq_star_arr seq))
  | Reach (antiframe,frame,puref,depth) -> print_indent depth ("[Reach] \n"^(print_biabduction antiframe frame puref depth))
  | DecideSeg (seg1,seg2,depth) -> print_indent depth ("[To Decide] "^(str_arrPred seg1) ^" vs. "^(str_arrPred seg2))
  | DecidePoints (p1,p2,depth) -> print_indent depth ("[To Decide] "^(!str_exp p1) ^" vs. "^(!str_exp p2))
  | Branch (rel,s1,s2,depth) -> print_indent depth ("[Branch] "^(!str_exp s1)^" "^(str_vrel rel)^" "^(!str_exp s2))
;;
  
let print_prooftrace () =
  List.fold_left (fun r item -> (str_one_prooftrace item)^"\n"^r) "\n" !global_prooftrace
;;

(* ************ end of proof trace ************ *)  
  

class lazyVMap (puref,varlst,initmatrix) =
  object(self)
    val mutable formula = puref
    (* val rel_matrix = Module_Rel_Matrix.empty (\* (int, int) -> int *\) *)
    val rel_matrix = initmatrix (* Array.make_matrix (List.length varlst) 7 (\* all of them are 111 *\) *)
    val var_to_index = varlst
    method checkSat newf =
      isSat (mkAnd puref newf )

    (* What's the difference between val and method? *)
    (* val test= *)
    (*   fun a b -> 0 *)

    (* int , int -> int *)
    method get_rel i1 i2 =
      if i1=i2
      then 2                    (* 010 *)
      else
        if i1<i2
        then
          rel_matrix.(i1).(i2)        
        else
          get_opposite_rel rel_matrix.(i2).(i1)
          
    (* exp -> int option *)
    method get_index e =
      try
        snd (List.find (fun (item,index) -> is_same_exp item e) var_to_index)
      with Not_found ->
        failwith "lazyVMap.get_index: Not_found. It is possible that there is something wrong in get_var_set"
    (* ;; Not Inside Object!  *)

    method compare_points s1 s2 =      
      let c = decode_vrelation (self#get_rel (self#get_index s1) (self#get_index s2)) in
      (* let () = print_endline ("lazyVMap.compare_points: "^(!str_exp s1)^" "^(!str_exp s2)^" "^(str_vrel c)) in *)
      c

    method get_matrix =
      rel_matrix

    method update_matrix relcode e1 e2 =
      let i,j = self#get_index e1, self#get_index e2  in      
      if i<=j
      then (self#get_matrix).(i).(j) <- relcode
      else (self#get_matrix).(j).(i) <- get_opposite_rel relcode
                                             
    method copy lst puref =
      let newMatrix = Array.copy rel_matrix in
      let () = Array.iteri (fun index item -> newMatrix.(index) <- Array.copy rel_matrix.(index)) newMatrix in
      let newVmap = new lazyVMap (puref,var_to_index,newMatrix) in
      List.iter (fun (rel_code,e1,e2) -> newVmap#update_matrix rel_code e1 e2) lst;
      newVmap        

    method get_puref =
      puref
        
    method extend (rel,e1,e2) =
      (* let () = print_endline ("lazyVMap.extend: "^(!str_exp e1)^" "^(!str_exp e2)^" "^(str_vrel rel)) in *)
      let get_formula rel e1 e2 =
        match rel with
        | Gt -> mkGt e1 e2 
        | Lt -> mkLt e1 e2 
        | Eq -> mkEq e1 e2 
        | Lte -> mkLte e1 e2 
        | Gte -> mkGte e1 e2 
        | _ -> failwith "get_formula: TO BE IMPLEMENTED"
      in
      let rel_code = encode_vrelation rel in
      let orig_rel_code = encode_vrelation (self#compare_points e1 e2) in
      let new_rel_code = rel_code land orig_rel_code in
      (* let () = print_endline ("orig_rel_code: "^(string_of_int orig_rel_code)^" rel_code:"^(string_of_int rel_code)) in *)
      if new_rel_code = orig_rel_code
      then Some (self#copy [] puref)                   (* not changed *)
      else
        if new_rel_code = 0
        then
          None
        else
          let rel_f = get_formula (decode_vrelation new_rel_code) e1 e2 in
          if self#checkSat rel_f
          then
            Some (self#copy [(new_rel_code,e1,e2)] (mkAnd rel_f puref ))
          else
            None

    method extend_f (rel,e1,e2) k =
      match self#extend (rel,e1,e2) with
      | Some newvmap ->
         push_prooftrace (Branch (rel,e1,e2,!prooftrace_depth));
         let orig_prooftrace_depth = !prooftrace_depth in
         prooftrace_depth := !prooftrace_depth + 1;
         k newvmap;
         prooftrace_depth := orig_prooftrace_depth;
         ()
      | None -> ()

    (* For segments (Aseg, Gap or Elem), there are only Gt, Lt or Unk *)
    method add_segment_lt p1 p2 (k:lazyVMap -> unit) =
      match p1, p2 with
      | Aseg (b1,s1,e1), Aseg (b2,s2,e2)
        | Gap (b1,s1,e1), Gap (b2,s2,e2)
        | Aseg (b1,s1,e1), Gap (b2,s2,e2)
        | Gap (b1,s1,e1), Aseg (b2,s2,e2) ->        
         self#extend_f (Lte,e1,s2) k
      | Aseg (b1,_,e1), Elem (b2,s2)
        | Gap (b1,_,e1), Elem (b2,s2)
        | Elem (b2,e1), Gap (b1,s2,_)
        | Elem (b2,e1), Aseg (b1,s2,_) ->
         self#extend_f (Lte,e1,s2) k
      | Elem (b1,s1), Elem (b2,s2) ->
         self#extend_f (Lte,s1,s2) k

    method compare_segment p1 p2 =
      match p1, p2 with
      | Aseg (b1,s1,e1), Aseg (b2,s2,e2)
        | Gap (b1,s1,e1), Gap (b2,s2,e2)
        | Aseg (b1,s1,e1), Gap (b2,s2,e2)
        | Gap (b1,s1,e1), Aseg (b2,s2,e2) ->         
         ( match self#compare_points e1 s2 with
           | Unk
             | Gte
             | Neq->
              ( match self#compare_points e2 s1 with
                | Unk
                  | Gte
                  | Neq -> Unk
                | Gt -> Lt     (* A trick to force the order, but is it necessary to update the matrix? *)
                | Lt
                  | Lte
                  | Eq-> Gt
                | False -> failwith "helper: false relation detected"
              )
           | Lt
             | Lte
             | Eq -> Lt
           | Gt -> Gt
           | False -> failwith "helper: false relation detected"
         )
      | Aseg (b1,s1,e1), Elem (b2,s2)
        | Gap (b1,s1,e1), Elem (b2,s2)
        | Elem (b2,s2), Gap (b1,s1,e1)
        | Elem (b2,s2), Aseg (b1,s1,e1) ->
         ( match self#compare_points e1 s2 with
           | Unk
             | Gte
             | Neq ->
              ( match self#compare_points s1 s2 with
                | Unk
                  | Neq -> Unk
                | Gt
                  | Gte -> Gt      
                | Lt
                  | Lte -> Lt (* TO DO: need to force the relation *)
                | Eq -> failwith" compare_segment: Overlapping exists"
                | False -> failwith "helper: false relation detected"
              )
           | Lt
             | Lte
             | Eq-> Lt
           | Gt -> Gt (* TO DO: need to force the relation *)
           | False -> failwith "helper: false relation detected"
         )
      | Elem (b1,s1), Elem (b2,s2) ->
         ( match self#compare_points s1 s2 with
           | Unk
             | Neq-> Unk
           | Gt
             | Gte -> Gt
           | Lt
             | Lte -> Lt
           | Eq -> failwith "compare_segment: Overlapping exists"
           | False -> failwith "helper: false relation detected"
         )
  end
;;

  
  
class ['a] frame init  = object
  val plst:'a list = init
  method add p =
    new frame (p::plst)

  method add_lst lst =
    new frame (lst@plst)

  method get_lst =
    plst
end
;;

  
let po_biabduction ante conseq =
  
  let lazy_sort p vmap k =
    
    let rec bubble_push p vmap k =  
      (* let () = print_endline ("bubble_push "^(str_seq_star_arr p)) in *)
      let rec bubble_push_helper plst vmap k =
        (* return a list, with the min at the head, and the min will only be Basic *)
        match plst with
        | h::tail ->
           bubble_push_helper tail vmap
                              ( fun (x,restlst,newvmap) ->
                                match restlst with
                                | h1::tail1 ->
                                   (* TO DO: not enough cases here, need to handle empty cases. Only when overlapping exists, consider empty segment? *)
                                   compare h h1 vmap
                                           (fun (min, restlst, newvmap2) ->
                                             k (min,(restlst@tail1),newvmap2))
                                | [] ->
                                   ( match x with
                                     | Emp ->
                                        bubble_push h newvmap
                                                    (fun (x,rest,newvmap2) ->
                                                      k (x,rest@restlst,newvmap2))
                                     | h1 ->
                                        compare h h1 vmap
                                                (fun (min, restlst, newvmap2) ->
                                                  k (min,restlst,newvmap2))
                                   )
                              )
        | [] -> k (Emp,[],vmap)
      in
      match p with
      | Star plst -> bubble_push_helper plst vmap k         
      | Seq (l,r) ->
         bubble_push l vmap
                     (fun (x,xlst,newvmap) ->
                       k (x,r::xlst,newvmap))
      | Basic _ | Emp -> k (p, [], vmap)

    and compare h1 h2 vmap k =
      let () = print_endline ("compare "^(str_seq_star_arr h1)^" "^(str_seq_star_arr h2)) in
      match h1, h2 with
      | Emp, _
        | _ , Emp -> failwith "compare: Invalid Emp case"
      | Basic p1, Basic p2 ->
         ( match vmap#compare_segment p1 p2 with
           | Unk ->
              push_prooftrace (DecideSeg (p1,p2,!prooftrace_depth));
              vmap#add_segment_lt p1 p2 (fun newvmap -> k (h1,[h2],newvmap));
              vmap#add_segment_lt p1 p2 (fun newvmap -> k (h2,[h1],newvmap));
              ()
           | Gt -> k (h2,[h1],vmap)
           | Lt -> k (h1,[h2],vmap)
           | _ -> failwith "compare: Invalid output from compare_segment"
         )
      | Seq (l,r) , _ ->
         compare l h2 vmap
                 ( fun (min,restlst,newvmap) ->
                   k (min,r::restlst,newvmap))
      | Star plst , _ ->
         bubble_push h1 vmap
                     ( fun (x,rest,newvmap) ->
                       compare x h2 newvmap
                               ( fun (min,restlst,newvmap2) ->
                                 k (min,rest@restlst,newvmap2)))
      | Basic _ , Seq (l,r) ->
         compare h1 l vmap
                 ( fun (min,restlst,newvmap) ->
                   k (min,r::restlst,newvmap))
      | Basic _ , Star plst ->
         bubble_push h2 vmap
                     ( fun (x,rest,newvmap) ->
                       compare h1 x newvmap
                               ( fun (min,restlst,newvmap2) ->
                                 k (min,rest@restlst,newvmap2)))
    in
    bubble_push p vmap (fun (min,restlst,newvmap) -> k (min,mkStar restlst,newvmap))
  in
  let rec helper ante conseq vmap ((antiframe,frame,prooftrace) as ba) k =
    (* let () = print_endline ((str_seq_star_arr ante)^" |= "^(str_seq_star_arr conseq)) in *)    
    let () = push_prooftrace (Entry (ante,conseq,!prooftrace_depth)) in
      
    match ante, conseq with
    | Emp, _
      | _ ,Emp -> k ante conseq ba vmap
                    
    | Basic h1, Basic h2 ->

       let () = push_prooftrace (Match (h1,h2,!prooftrace_depth)) in
       
       let force_rel newvmap =
         helper ante conseq newvmap ba k
       in
       let align rel b1 b2 s1 s2 =
         (* let () = print_endline ("align: "^(!str_exp s1)^" "^(!str_exp s2)) in *)
         match rel with
         | Unk | Gte | Neq ->
            push_prooftrace (DecidePoints (s1,s2,!prooftrace_depth));
            vmap#extend_f (Gt,s1,s2) force_rel;
            vmap#extend_f (Lte,s1,s2) force_rel;
            ()                          
         | Gt -> helper (mkGapBasic b1 s2 s1) conseq vmap ba
                        (fun lefta leftc newba newvmap ->
                          helper (mkSeq lefta ante) leftc newvmap newba k)
         | Lt | Lte -> helper ante (mkGapBasic b2 s1 s2) vmap ba
                              (fun lefta leftc newba newvmap ->
                                helper lefta (mkSeq leftc conseq) newvmap newba k)
         | False -> failwith "helper: false relation detected"
         | Eq -> failwith "align: Invalid Eq relation"              
       in
       
       ( match h1, h2 with
         | Aseg (b1, s1, e1), Aseg (b2, s2, e2) ->
            ( match vmap#compare_points s1 s2 with
              | Eq ->
                 (
                   match vmap#compare_points e1 e2 with
                   | Unk | Neq->
                      push_prooftrace (DecidePoints (e1,e2,!prooftrace_depth));
                      vmap#extend_f (Gt,e1,e2) force_rel;
                      vmap#extend_f (Lte,e1,e2) force_rel;
                      ()                      
                   | Gt | Gte | Eq -> helper (mkAsegBasic b1 e2 e1) Emp vmap ba k
                   | Lt | Lte -> helper Emp (mkAsegBasic b2 e1 e2) vmap ba k
                   | False -> failwith "helper: false relation detected"
                 )
              | others -> align others b1 b2 s1 s2
            )

         | Aseg (b1, s1, e1), Elem (b2, s2) ->
            ( match vmap#compare_points s1 s2 with
              | Eq ->
                 (
                   match vmap#compare_points s1 e1 with
                   | Unk | Lte ->
                      vmap#extend_f (Eq,s1,e1) force_rel;
                      vmap#extend_f (Lt,s1,e1) force_rel;
                      ()                        
                   | Lt -> helper (mkAsegBasic b1 (incOne s1) e1) Emp vmap ba k (* TO DO: Is it ok to increase s1? Or it may be better to increase s2. *)
                   | Eq -> helper (mkAsegBasic b1 (incOne s1) e1) Emp vmap ba k
                   | Gt | Gte | Neq -> failwith "Aseg vs. Elem: Invalid input. The relation should be more specific"
                   | False -> failwith "helper: false relation detected"
                 )              
              | others -> align others b1 b2 s1 s2
            )

         | Aseg (b1, s1, e1), Gap (b2, s2, e2) ->
            ( match vmap#compare_points s1 s2 with
              | Eq ->
                 ( match vmap#compare_points e1 e2 with
                   | Unk | Neq ->
                      push_prooftrace (DecidePoints (e1,e2,!prooftrace_depth));
                      vmap#extend_f (Gt,e1,e2) force_rel;
                      vmap#extend_f (Lte,e1,e2) force_rel;                      
                      ()
                   | Eq-> helper Emp Emp vmap (antiframe,frame#add (mkAseg b1 s1 e2),prooftrace) k
                   | Gt | Gte -> helper (mkAsegBasic b1 e2 e1) Emp vmap (antiframe,frame#add (mkAseg b1 s1 e2),prooftrace) k
                   | Lt | Lte -> helper Emp (mkGapBasic b2 e1 e2) vmap (antiframe,frame#add (mkAseg b1 s1 e1),prooftrace) k                        
                   | False -> failwith "helper: false relation detected"
                 )
              | others -> align others b1 b2 s1 s2
            )
              
         | Elem (b1, s1), Elem (b2, s2) ->
            ( match vmap#compare_points s1 s2 with
              | Eq -> helper Emp Emp vmap ba k
              | others -> align others b1 b2 s1 s2
            )

         | Elem (b1, s1), Aseg (b2, s2, e2) ->
            ( match vmap#compare_points s1 s2 with
              | Eq ->
                 ( match vmap#compare_points s2 e2 with
                   | Unk | Lte  ->
                      vmap#extend_f (Eq,s2,e2) force_rel;
                      vmap#extend_f (Lt,s2,e2) force_rel;
                      ()                      
                   | Lt -> helper Emp (mkAsegBasic b2 (incOne s2) e2) vmap ba k
                   | Eq -> helper ante Emp vmap ba k
                   | Gt | Gte | Neq -> failwith "Elem vs. Aseg: Invalid input. The relation should be more specific"
                   | False -> failwith "helper: false relation detected"
                 )
              | others -> align others b1 b2 s1 s2
            )

         | Elem (b1, s1), Gap (b2, s2, e2) ->
            ( match vmap#compare_points s1 s2 with
              | Eq ->
                 ( match vmap#compare_points s2 e2 with
                   | Unk | Lte ->
                      vmap#extend_f (Eq,s2,e2) force_rel;
                      vmap#extend_f (Lt,s2,e2) force_rel;
                      ()                      
                   | Lt -> helper Emp (mkGapBasic b2 (incOne s2) e2) vmap (antiframe,(frame#add h1),prooftrace) k
                   | Eq -> helper ante Emp vmap ba k
                   | Gt | Gte | Neq -> failwith "Elem vs. Gap: Invalid input. The relation should be more specific"              
                   | False -> failwith "helper: false relation detected"
                 )                 
              | others -> align others b1 b2 s1 s2
            )
            
         | Gap (b1, s1, e1), Gap (b2, s2, e2) ->
            ( match vmap#compare_points s1 s2 with
              | Eq ->
                 (
                   match vmap#compare_points e1 e2 with
                   | Unk | Neq ->
                      vmap#extend_f (Gt,e1,e2) force_rel;
                      vmap#extend_f (Lt,e1,e2) force_rel;
                      ()
                   | Eq -> helper Emp Emp vmap ba k
                   | Gt | Gte -> helper (mkGapBasic b1 e2 e1) Emp vmap ba k
                   | Lt | Lte -> helper Emp (mkGapBasic b2 e1 e2) vmap ba k                   
                   | False -> failwith "helper: false relation detected"
                 )
              | others -> align others b1 b2 s1 s2
            )
              
         | Gap (b1, s1, e1), Elem (b2, s2) ->
            ( match vmap#compare_points s1 s2 with
              | Eq ->
                 ( match vmap#compare_points s1 e1 with
                   | Unk | Lte ->
                      vmap#extend_f (Eq,s1,e1) force_rel;
                      vmap#extend_f (Lt,s1,e1) force_rel;
                      ()                      
                   | Lt -> helper (mkGapBasic b1 (incOne s1) e1) Emp vmap ((antiframe#add h2),frame,prooftrace) k
                   | Eq -> helper Emp conseq vmap ba k
                   | Gt | Gte | Neq -> failwith "Elem vs. Aseg: Invalid input. The relation should be more specific"              
                   | False -> failwith "helper: false relation detected"
                 )                 
              | others -> align others b1 b2 s1 s2
            )

         | Gap (b1, s1, e1), Aseg (b2, s2, e2) ->
            ( match vmap#compare_points s1 s2 with
              | Eq ->
                 ( match vmap#compare_points e1 e2 with
                   | Unk | Neq ->
                      push_prooftrace (DecidePoints (e1,e2,!prooftrace_depth));
                      (* let () = print_endline ("After in vmap: "^(!str_exp e1)^" "^(!str_exp e2)^" "^(str_vrel (vmap#compare_points e1 e2))) in *)
                      vmap#extend_f (Gt,e1,e2) force_rel;
                      vmap#extend_f (Lte,e1,e2) force_rel;
                      ()
                   | Eq-> helper Emp Emp vmap (antiframe#add (mkAseg b1 s2 e2),frame,prooftrace) k
                   | Gt | Gte -> helper (mkGapBasic b1 e2 e1) Emp vmap (antiframe#add (mkAseg b1 s2 e2),frame,prooftrace) k
                   | Lt | Lte -> helper Emp (mkAsegBasic b2 e1 e2) vmap (antiframe#add (mkAseg b1 s2 e1),frame,prooftrace) k                        
                   | False -> failwith "helper: false relation detected"
                 )
              | others -> align others b1 b2 s1 s2
            )
       )
         
    | Seq (l,r), _ ->
       lazy_sort l vmap
                   (fun (x,rest,newvmap) ->
                     helper x conseq newvmap ba
                            (fun lefta leftc newba newvmap2 ->
                              helper (mkSeq lefta (mkSeq rest r)) leftc newvmap2 newba k))
    | Star plst, _ ->
       let () = push_prooftrace (Sort (ante,0,!prooftrace_depth)) in
       lazy_sort ante vmap
                   (fun (x,rest,newvmap) ->
                     helper x conseq newvmap ba
                            (fun lefta leftc newba newvmap2 ->
                              helper (mkSeq lefta rest) leftc newvmap2 newba k))
    | Basic _, Seq (l,r) ->       
       lazy_sort l vmap
                   (fun (x,rest,newvmap) ->
                     helper ante x newvmap ba
                            (fun lefta leftc newba newvmap2 ->
                              helper lefta (mkSeq leftc (mkSeq rest r)) newvmap2 newba k))
    | Basic _, Star plst ->
       let () = push_prooftrace (Sort (conseq,1,!prooftrace_depth)) in
       lazy_sort conseq vmap
                   (fun (x,rest,newvmap) ->
                     helper x conseq newvmap ba
                            (fun lefta leftc newba newvmap2 ->
                              helper lefta (mkSeq leftc rest) newvmap2 newba k))
  in
  
  let anteTrans = new arrPredTransformer ante in
  let conseqTrans = new arrPredTransformer conseq in
  let varlst = snd
                 (
                   List.fold_left
                     (fun (index,r) item ->
                       (index+1,(item,index)::r))
                     (0,[])
                     (remove_dups_exp_lst ((anteTrans#get_var_set)@(conseqTrans#get_var_set)))
                 )
  in

  let antiframe = new frame [] in
  let frame = new frame [] in

  let lhs_p = anteTrans#get_pure in
  let rhs_p = conseqTrans#get_pure in
  let puref = mkAnd lhs_p rhs_p  in
  
  let init_matrix = Array.make_matrix (List.length varlst) (List.length varlst) 7 in
  let vmap = new lazyVMap (puref,varlst,init_matrix) in
  
  helper (anteTrans#formula_to_seq) (conseqTrans#formula_to_seq) vmap (antiframe,frame,[])
         (fun lefta leftc (newantiframe,newframe,newprooftrace) newvmap ->
           let newantiframe, newframe =
             match lefta, leftc with
             | (Emp|Basic (Gap _)), (Emp|Basic (Gap _)) -> newantiframe, newframe
             | Emp, _ -> newantiframe#add_lst (flatten_seq leftc), newframe
             | _ , Emp -> newantiframe, newframe#add_lst (flatten_seq lefta)
             | _ , _ -> failwith "po_biabduction: Invalid input"
           in
           (* print_biabduction_result newantiframe#get_lst newframe#get_lst newvmap#get_puref newprooftrace *)
           (* print_biabduction_result newantiframe#get_lst newframe#get_lst newvmap#get_puref []; *)
           push_prooftrace (Reach (newantiframe#get_lst, newframe#get_lst,newvmap#get_puref,!prooftrace_depth));
           (* prooftrace_depth := !prooftrace_depth - 1 ; *)
           (* print_endline (print_prooftrace ()); *)
           ()
         )
;;

let po_biabduction_interface ante conseq =
  let () = po_biabduction ante conseq in
  print_endline (print_prooftrace ());
  ()
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
