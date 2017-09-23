#include "xdebug.cppo"

open Cpure
open VarGen
open Cformula
       

(* Utility on formula and exp *)

let split_list_3 lst =
  let (l1,l2,l3)=
    List.fold_left
      (fun (r1,r2,r3) (n1,n2,n3) ->
        (n1::r1,n2::r2,n3::r3))
      ([],[],[]) lst
  in
  (List.rev l1,List.rev l2,List.rev l3)
;;

let mkCformulaOr f1 f2 =
  Cformula.Or    
    {
      formula_or_f1 = f1;
      formula_or_f2 = f2;
      formula_or_pos = no_pos;
    }
;;
  
let get_fv_pure = Cpure.fv
;;

let mkSV = Cpure.mk_spec_var
;;
  
  
let mkVar sv =
  Cpure.Var (sv,no_pos)
;;

let mkConst i =
  Cpure.IConst (i,no_pos)
;;

  
let get_var_lst = Cpure.var_list_exp ;;

let exp_contains_var exp v =
  List.exists (fun item -> eq_spec_var item v) (get_var_lst exp)
;;
                                                            
  
let mkOr f1 f2 = Cpure.mkOr f1 f2 None no_pos
;;

let mkAnd f1 f2 = Cpure.mkAnd f1 f2 no_pos
;;

let mkExists svlst f =
  List.fold_left
    (fun r item ->
      Cpure.Exists (item,r,None,no_pos))
    f svlst
;;

let mkForall svlst f =
  List.fold_left
    (fun r item ->
      Cpure.Forall (item,r,None,no_pos))
    f svlst
;;

let mkNot f = Cpure.mkNot f None no_pos
;;

  
let mkTrue () = Cpure.mkTrue no_pos
;;

let isTrue = Cpure.is_True
;;
  
let mkFalse () = Cpure.mkFalse no_pos
;;

let isFalse = Cpure.is_False
;;

let mkViewNode ptr viewname args =
  Cformula.mkViewNode ptr viewname args no_pos
;;

let mkStarH h1 h2 =
  Cformula.mkStarH h1 h2 no_pos
      

(* Simplification related *)
let simplify = Tpdispatcher.simplify_omega
;;

let pairwisecheck = Tpdispatcher.tp_pairwisecheck
;;

let simplify_p f = pairwisecheck (simplify f)
;;

let get_gist = Omega.gist
;;
  
let rec mkAndlst lst =
  match lst with
  | [h] -> h
  | h::tail -> mkAnd h (mkAndlst tail)
  | [] -> mkTrue ()
;;

let rec mkOrlst lst =
  match lst with
  | [h] -> h
  | h::tail -> mkOr h (mkOrlst tail)
  | [] -> mkFalse ()
;;

  
let mkImply af cf =
  mkOr (mkNot af) cf
;;

let mkGt e1 e2 =
  Cpure.mkGtExp e1 e2 no_pos
;;

let mkLt e1 e2 =
  Cpure.mkLtExp e1 e2 no_pos
;;


let mkEq e1 e2 =
  Cpure.mkEqExp e1 e2 no_pos
;;

let mkLte e1 e2 =
  (* mkOr (mkLt e1 e2) (mkEq e1 e2) *)
  Cpure.mkLteExp e1 e2 no_pos
;;

let mkGte e1 e2 =
  (* mkOr (mkGt e1 e2) (mkEq e1 e2) *)
  Cpure.mkGteExp e1 e2 no_pos
;;
  

let mkNeq e1 e2 =
  Cpure.mkNeqExp e1 e2 no_pos
;;

let mkMin elst =
  match elst with
  | [h1;h2] ->
     Cpure.Min (h1,h2, no_pos)
  | [h] ->
     h
  | h1::h2::tail ->
     List.fold_left
       (fun r item ->
         Cpure.Min (item,r,no_pos))
       (Cpure.Min (h1,h2,no_pos)) tail
  | [] -> failwith "mkMin: empty list as input"

let mkMin_raw m elst =  
  (mkAndlst
     (List.fold_left
        (fun r item ->
          (mkLte m item)::r) [] elst))
;;

let mkEqSv a b =
  mkEq (mkVar a) (mkVar b)
;;

let mkNeqSv a b =
  mkNeq (mkVar a) (mkVar b)
;;  

let mkLtSv a b =
  mkLt (mkVar a) (mkVar b)
;;

let mkLteSv a b =
  mkLte (mkVar a) (mkVar b)
;;

let mkGtSv a b =
  mkGt (mkVar a) (mkVar b)
;;  

let mkGteSv a b =
  mkGte (mkVar a) (mkVar b)
;;

let is_same_exp e1 e2 =
  check_eq_exp e1 e2
;;

let is_same_sv =
  Cpure.is_same_sv
;;

let exp_to_var e =
  match Cpure.get_exp_var e with
  | None -> failwith "input is not a variable"
  | Some v -> v
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
  match e with
  | IConst (c,p) -> IConst (c+1,p)
  | _ ->
     Add (e,IConst (1,no_pos),no_pos)
;;

let decOne e =
  match e with
  | IConst (c,p) -> IConst (c-1,p)
  | _ ->
     Subtract (e,IConst (1,no_pos),no_pos)
;;

  
let isSat f=
  Tpdispatcher.tp_is_sat f "111"  
;;

let imply f1 f2 =
  !tp_imply f1 f2
;;

let isValid f =
  not (isSat (mkNot f))
;;

let print_endline_verbose str =
  if !Globals.array_verbose
  then print_endline str
  else ()
;;
      
let str_exp = print_exp
;;

let str_cformula = Cformula.print_formula
;;

let str_context = Cformula.print_context
;;
  
let str_pformula = Cpure.print_formula
;;

let str_sv = Cpure.print_sv
;;

  
let str_list =
  Gen.Basic.pr_list
;;

let str_pair=
  Gen.Basic.pr_pair
;;

let map_op_list (f:('a -> 'b)) (lst:('a option list)) =
  List.fold_right
    (fun item r ->
      match item with
      | Some a -> (f a)::r
      | None -> r)
    lst []
;;
  
(* end of Utility on formula and exp  *)


type 'exp arrPred =
  | Aseg of ('exp * 'exp * 'exp)
  | AsegNE of ('exp * 'exp * 'exp)
  | Gap of ('exp * 'exp * 'exp)
  | Elem of ('exp * 'exp * 'exp)
;;

  

let mkAseg b s e =
  Aseg (b,s,e)
;;

let mkAsegNE b s e =
  AsegNE (b,s,e)
;;
  

let mkGap b s e =
  Gap (b,s,e)
;;

let mkElem b s v =
  Elem (b,s,v)
;;

  
let str_arrPred apred =
  match apred with
  | Aseg (b,s,e) ->
     (* "Aseg("^(!str_exp b)^","^(!str_exp s)^","^(!str_exp e)^")" *)
     "Aseg("^("_")^","^(!str_exp s)^","^(!str_exp e)^")"
  | AsegNE (b,s,e) ->
     (* "Aseg("^(!str_exp b)^","^(!str_exp s)^","^(!str_exp e)^")" *)
     "AsegNE("^("_")^","^(!str_exp s)^","^(!str_exp e)^")"
  | Gap (b,s,e)->
     (* "Gap("^(!str_exp b)^","^(!str_exp s)^","^(!str_exp e)^")" *)
     "Gap("^("_")^","^(!str_exp s)^","^(!str_exp e)^")"
  | Elem (b,s,v) ->
     (* "Elem("^(!str_exp b)^","^(!str_exp s)^")" *)
     "Elem("^("_")^","^(!str_exp s)^")"
;;

let rec str_arrPred_star_lst lst =
  match lst with
  | [] -> "EMP"
  | [h] -> str_arrPred h
  | h::tail -> (str_arrPred h)^"*"^(str_arrPred_star_lst tail)
;;

let is_empty_apred p apred =
  match apred with
  | Aseg (b,s,e) | AsegNE (b,s,e) |  Gap (b,s,e) -> p s e
  | Elem _ -> false
;;


let str_seq seq =
  str_list str_arrPred seq
;;

let rec flatten_heap_star_formula cf =
  match cf with
  | Star f ->
     (flatten_heap_star_formula f.h_formula_star_h1)@(flatten_heap_star_formula f.h_formula_star_h2)
  | ViewNode _ -> [cf]
  | HEmp -> []
  | Phase f -> (flatten_heap_star_formula f.h_formula_phase_rd)@(flatten_heap_star_formula f.h_formula_phase_rw)
  | _ -> failwith ("flatten_heap_star_formula: Invalid input "^(!Cformula.print_h_formula cf))
;;

let isAsegPred cf =
  match cf with
  | ViewNode f ->
  (* String.equal f.h_formula_view_name "Aseg" *)
     f.h_formula_view_name = "Aseg"
  | _ -> false
;;

let isAsegNEPred cf =
  match cf with
  | ViewNode f ->
  (* String.equal f.h_formula_view_name "Aseg" *)
     f.h_formula_view_name = "AsegNE"
  | _ -> false
;;

  
let isElemPred cf =
  match cf with
  | ViewNode f ->
     (* String.equal f.h_formula_view_name "Elem" *)
     f.h_formula_view_name = "Elem"
  | _ -> false
;;

let isEmpty cf =
  match cf with
  | HEmp -> true
  | _ -> false
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
    | Seq (l,r) -> helper l (fun llst -> helper r (fun rlst -> k (llst@rlst)))
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

let vcount = ref 0;;
  
let  global_get_new_var_public () =
  let newv = mk_spec_var ("t"^(string_of_int !vcount)) in
  vcount := !vcount + 1;
  newv
;;
  
let  global_get_new_var () =
  let newv = mk_spec_var ("t_t"^(string_of_int !vcount)) in
  vcount := !vcount + 1;
  newv
;;

let arrPred_to_h_formula seq =
  let bind_exp_to_var exp =
    match exp with
    | Var (sv,_) -> (sv,[],[])                 
    | _ ->
       let newv = global_get_new_var () in
       (newv,[mkEq (mkVar newv) exp],[newv])
  in
  let one_arrPred_to_h_formula p =
    match p with
    | Aseg (b,s,e) ->
       let (news,sf_lst,svlst) = bind_exp_to_var s in
       let (newe,se_lst,evlst) = bind_exp_to_var e in
       (mkViewNode (Cpure.exp_to_spec_var b) "Aseg" [news;newe], sf_lst@se_lst,svlst@evlst)
    | Gap (b,s,e) ->
       let (news,sf_lst,svlst) = bind_exp_to_var s in
       let (newe,se_lst,evlst) = bind_exp_to_var e in
       (mkViewNode (Cpure.exp_to_spec_var b) "Gap" [news;newe], sf_lst@se_lst,svlst@evlst)
    | Elem (b,s,v) ->
       let (news,sf_lst,svlst) = bind_exp_to_var s in     
       (mkViewNode (Cpure.exp_to_spec_var b) "Elem" [news], sf_lst,svlst)
    | _ -> failwith "arrPred_to_h_formula: TO BE IMPLEMENTED"
  in
  let construct_h_formula plst =
    match (List.map (fun item -> one_arrPred_to_h_formula item) plst) with
    | h::tail -> List.fold_left (fun (h,p,v) (itemh,itemp,itemv) -> (mkStarH itemh h, itemp@p,itemv@v)) h tail
    | [] -> (HEmp,[],[])
  in
  construct_h_formula seq
;;

let construct_exists hf pf svlst =
  Cformula.mkExists svlst hf (Mcpure.mix_of_pure pf) CvpermUtils.empty_vperm_sets Cformula.TypeTrue (Cformula.mkTrueFlow ()) [] no_pos
;;

let construct_base hf pf =
  Cformula.mkBase hf (Mcpure.mix_of_pure pf) CvpermUtils.empty_vperm_sets Cformula.TypeTrue (Cformula.mkTrueFlow ()) [] no_pos
;;

let construct_false () =
  mkFalsePureTrueHeap ()
;;


let get_inferred_pure orig_pf new_pflst =
  let rec helper new_pflst lst =
    match new_pflst with
    | h::tail ->
       if imply orig_pf h
       then helper tail lst
       else helper tail (h::lst)
    | [] -> lst
  in
  simplify (mkAndlst (helper new_pflst []))
;;

let generic_get_permutation lst =
  let rec insert k lst =
    match lst with
    | h::tail -> 
       (k::lst)::(List.map (fun item -> h::item) (insert k tail))
    | [] -> [[k]]
  in
  let rec helper lst =
    (* let () = print_endline ("call helper here " ^ (str_list str_asegPred lst)) in *)
    match lst with
    | [] -> [[]]
    | h::tail -> List.flatten (List.map (insert h) (helper tail))
  in
  let r = helper lst in
  if List.length r = 0
  then failwith "empty list 2"
  else r
;;

let generic_get_disjointness helper_two pair_lst =
  let helper_h_lst h lst =
    match lst with
    | h1::tail ->
       List.fold_left
         (fun r item ->
           mkAnd (helper_two item h) r)
         (helper_two h1 h) tail
    | [] -> mkTrue ()
  in
  let rec helper_lst lst =
    match lst with
    | [_] | [] -> mkTrue ()
    | h::tail -> mkAnd (helper_h_lst h tail) (helper_lst tail)
  in
  helper_lst pair_lst
;;


type aseg_pred_plus =
  | Aseg_p of (Cpure.spec_var * Cpure.spec_var)
  | AsegNE_p of (Cpure.spec_var * Cpure.spec_var)
  | Pointsto_p of (Cpure.spec_var * Cpure.spec_var)
  | Gap_p of (Cpure.spec_var * Cpure.spec_var)
;;

let str_list_delimeter_raw str lst d emp =
    let helper lst =
      match lst with
      | [] -> emp
      | [h] -> str h
      | h::tail -> List.fold_left (fun r item -> r^d^(str item)) (str h) tail
    in
    helper lst
;;
  
let str_list_delimeter str lst d emp =
  "["^(str_list_delimeter_raw str lst d emp)^"]"
;;
  
let str_aseg_pred_plus aseg =
  match aseg with
  | Aseg_p (s,e) ->
     "Aseg<"^(!str_sv s)^","^(!str_sv e)^">"
  | AsegNE_p (s,e) ->
     "AsegNE<"^(!str_sv s)^","^(!str_sv e)^">"
  | Gap_p (s,e)->
     "Gap<"^("_")^","^(!str_sv s)^","^(!str_sv e)^">"
  | Pointsto_p (s,v) ->
     (!str_sv s)^" -> "^(!str_sv v)
;;

let str_aseg_pred_plus_lst hf =
  str_list_delimeter str_aseg_pred_plus hf "*" "EMP"
;;
let str_asegplusF (pf,hf) =
  (str_list !str_pformula pf)^"/\\"^(str_aseg_pred_plus_lst hf)
;;

  
let mkAsegNE_p a b =
  AsegNE_p (a,b)
;;

let mkAseg_p a b =
  Aseg_p (a,b)
;;

let mkGap_p a b =
  Gap_p (a,b)
;;

let mkPointsto_p t v =
  Pointsto_p (t,v)
;;

let is_same_asegPredplus a1 a2 =
  match a1, a2 with
  | Aseg_p (s1,e1), Aseg_p (s2,e2)
    | AsegNE_p (s1,e1), AsegNE_p (s2,e2)
    | Pointsto_p (s1,e1), Pointsto_p (s2,e2)
    | Gap_p (s1,e1), Gap_p (s2,e2) ->
     (is_same_sv s1 s2) && (is_same_sv e1 e2)
  | _, _ -> false
;;

let compare_list l1 l2 cmp =
  let rec compare_helper l1 l2 =
    match l1, l2 with
    | h1::tail1, h2::tail2 ->
       (cmp h1 h2)&&(compare_helper tail1 tail2)
    | [],h2::tail2 -> false
    | h1::tail1,[] -> false
    | [],[] -> true
  in
  compare_helper l1 l2
;;

let get_disjoint_pure hlst =
  let helper_two a1 a2 =
    match a1, a2 with
    | Aseg_p (s1,e1), Aseg_p (s2,e2)
      | AsegNE_p (s1,e1), AsegNE_p (s2,e2)
      | Aseg_p (s1,e1), AsegNE_p (s2,e2)
      | AsegNE_p (s1,e1), Aseg_p (s2,e2) ->
       mkOr (mkLteSv e1 s2) (mkLteSv e2 s1)
    | Pointsto_p (s1,_), Pointsto_p (s2,_) ->
       mkNeqSv s1 s2
    | Pointsto_p (s1,_), Aseg_p (s2,e2)
      | Pointsto_p (s1,_), AsegNE_p (s2,e2)
      | Aseg_p (s2,e2),Pointsto_p (s1,_)
      | AsegNE_p (s2,e2),Pointsto_p (s1,_) ->
       mkOr (mkLteSv e2 s1) (mkLtSv s1 s2)
    | _,_ ->
       failwith "get_disjoint_pure: TO BE IMPLEMENTED"
  in
  generic_get_disjointness helper_two hlst
;;

let get_segment_pure hlst =
  List.fold_left
    (fun r item ->
      match item with
      | Aseg_p (s,e) ->  (mkLteSv s e)::r
      | AsegNE_p (s,e) -> (mkLtSv s e)::r
      | _ -> r
    )
    [] hlst
;;

let compare_asegPredplus_lst l1 l2 =
  compare_list l1 l2 is_same_asegPredplus
;;

let compare_sv_lst svlst1 svlst2 =
  compare_list svlst2 svlst2 is_same_sv
;;

let aPredF_to_asegF aPredF =
  match aPredF with
  | [(evars, pf, hf)] -> (evars,pf,hf)
  | _ -> failwith "aPredF_to_asegF: Disjunctions"
;;
  
class arrPredTransformer_orig initcf = object(self)
  val cf = initcf               (* cf is Cformula.formula *)
  val mutable eqmap = ([]: (spec_var * exp) list)
  val mutable aseglst = None
  val mutable orig_puref = None
  val mutable puref = None      (* Extend with disjointness *)
  val mutable general_formula = None
                                  

  (* method generate_pure = *)
  (*   let generate_disjoint_formula_with_two_pred p1 p2 = *)
  (*     match p1, p2 with *)
  (*     | Aseg_p (_,s1,e1), Aseg_p (_,s2,e2) -> *)
  (*        mkOr (mkOr (mkGte s2 e1) (mkGte s1 e2)) (mkOr (mkEq s1 e1) (mkEq s2 e2)) *)
  (*     | Aseg_p (_,s1,e1), Elem (_,s2,_) -> *)
  (*        mkOr (mkOr (mkGte s2 e1) (mkGt s1 s2)) (mkEq s1 e1) *)
  (*     | Elem (_,s1,_), Aseg_p (_,s2,e2)  -> *)
  (*        mkOr (mkOr (mkGte s1 e2) (mkGte s2 s1)) (mkEq s2 e2) *)
  (*     | Elem (_,s1,_), Elem (_,s2,_) -> *)
  (*        mkOr (mkGt s2 s1) (mkGt s1 s2) *)
  (*     | _, _ -> mkTrue () *)
  (*   in *)
  (*   let rec generate_disjoint_formula lst flst = *)
  (*     match lst with *)
  (*     | h::tail -> *)
  (*        generate_disjoint_formula tail *)
  (*                                  ((List.map (fun item -> generate_disjoint_formula_with_two_pred h item) tail)@flst) *)
  (*     | [] -> flst *)
  (*   in *)
  (*   let rec generate_segment_formula lst flst = *)
  (*     List.fold_left *)
  (*       (fun r item -> *)
  (*         match item with *)
  (*         | Some f -> f::r *)
  (*         | None -> r *)
  (*       ) *)
  (*       []          *)
  (*       (List.map *)
  (*          (fun item -> *)
  (*            match item with *)
  (*            | Aseg_p (_,s,e) -> Some (mkLte s e) *)
  (*            | _ -> None) *)
  (*          lst *)
  (*       ) *)
  (*   in *)

  (*   let lst = self#formula_to_arrPred in *)
  (*   puref <- Some (mkAndlst ((self#get_orig_pure) *)
  (*                            ::((generate_disjoint_formula lst []) *)
  (*                               @(generate_segment_formula lst [])))); *)
  (*   () *)

  (* method get_pure = *)
  (*   match puref with *)
  (*   | Some f -> f *)
  (*   | None -> self#generate_pure; *)
  (*             self#get_pure *)
                
  (* method pred_var_to_arrPred_exp sv = *)
  (*   match (self#find_in_eqmap sv) with *)
  (*   | None -> *)
  (*      Var (sv,no_pos) *)
  (*   | Some e -> *)
  (*      e *)

  method pred_var_to_arrPred_exp sv =
    sv
         
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

  method getAsegNEBase cf =
    match cf with
    | ViewNode f ->
       self#pred_var_to_arrPred_exp f.h_formula_view_node
    | _ -> failwith "getAsegBase: Invalid input"
                    
  method getAsegNEStart cf =
    match cf with
    | ViewNode f ->
       self#pred_var_to_arrPred_exp (List.nth f.h_formula_view_arguments 0)
    | _ -> failwith "getAsegStart: Invalid input"

  method getAsegNEEnd cf =
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

  method getElemValue cf =
    match cf with
    | ViewNode f ->
       self#pred_var_to_arrPred_exp (List.nth f.h_formula_view_arguments 1)
    | _ -> failwith "getElemStart: Invalid input"

  method get_orig_pure =
    match orig_puref with
    | None -> 
       orig_puref <- Some (remove_termann (simplify (Cformula.get_pure_ignore_exists cf)));
       self#get_orig_pure
    | Some f -> f

  method generate_arrPred_lst =
    let one_pred_to_arrPred hf=
      if isAsegPred hf
      then Some (mkAseg_p (self#getAsegStart hf) (self#getAsegEnd hf))
      else
        if isAsegNEPred hf
        then Some (mkAsegNE_p (self#getAsegNEStart hf) (self#getAsegNEEnd hf))
        else
          if isElemPred hf
          then Some (mkPointsto_p (self#getElemStart hf) (self#getElemValue hf))
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
    let general_f =
      let rec get_general_f cf =
        match cf with
        | Base f ->
           let pred_list = flatten_heap_star_formula f.formula_base_heap in
           [[],[self#get_orig_pure],map_op_list (fun x->x) (List.map one_pred_to_arrPred pred_list)]
        | Or f->
           (get_general_f f.formula_or_f1)@(get_general_f f.formula_or_f2)
        | Exists f ->
           let pf = Mcpure.pure_of_mix f.formula_exists_pure in           
           let evars = f.formula_exists_qvars in
           let pred_list = flatten_heap_star_formula f.formula_exists_heap in
           [evars,[self#get_orig_pure],map_op_list (fun x->x) (List.map one_pred_to_arrPred pred_list)]
      in
      get_general_f cf
    in
    let aPrelst =
      match general_f with
      | (_,_,h)::_ -> h
      | _ -> failwith "aPrelst: Not constructed yet"
                      (* match cf with *)
                      (* | Base f -> *)
                      (*    let pred_list = flatten_heap_star_formula f.formula_base_heap in *)
                      (*    map_op_list (fun x->x) (List.map one_pred_to_arrPred pred_list)        *)
                      (* | Or f-> failwith "TO BE IMPLEMENTED" *)
                      (* | Exists f -> *)
                      (*    let pf = Mcpure.pure_of_mix f.formula_exists_pure in *)
                      (*    let evars = f.formula_exists_qvars in *)
                      (*    let () = eqmap <- build_eqmap pf evars in *)
                      (*    let pred_list = flatten_heap_star_formula f.formula_exists_heap in *)
                      (*    map_op_list (fun x->x) (List.map one_pred_to_arrPred pred_list) *)
    in
    general_formula <- Some general_f;
    aseglst <- Some aPrelst

  method formula_to_general_formula =
    match general_formula with
    | Some f ->
       (
         match f with
         | [nf] -> nf
         | _ -> failwith "formula_to_general_formula: TO BE IMPLEMENTED")
    | None ->
       self#generate_arrPred_lst;
       self#formula_to_general_formula
      
end
;;

let mkEmptyes () =
  empty_es (mkTrueFlow ()) Label_only.Lab2_List.unlabelled no_pos
;;

let mkCtx es =
  Ctx es
;;

let mkOCtx ctxlst =
  match ctxlst with
  | [h] -> h
  | h::tail ->
     List.fold_left
       (fun r item ->
         Cformula.OCtx (r,item))
       h tail
  | [] -> failwith "mkOCtx: Empty list as input"
;;

let mkSuccCtx ctxlst =
  SuccCtx ctxlst
;;
  
let mkEmptySuccCtx () =
  SuccCtx [Ctx (Cformula.empty_es (mkTrueFlow ()) Label_only.Lab2_List.unlabelled no_pos)]
;;

let mkEmptyFailCtx () =
  let empty_es = (Cformula.empty_es (mkTrueFlow ()) Label_only.Lab2_List.unlabelled no_pos) in
  mkFailCtx_simple "fail to prove" empty_es (Cformula.mkTrue_nf no_pos)  (mk_cex true) no_pos
;;

let mkCtxWithPure ip =
  let es = Cformula.empty_es (Cformula.mkTrueFlow ()) Label_only.Lab2_List.unlabelled VarGen.no_pos in
  SuccCtx
    [Ctx
       {
         es with
         (* es_formula = fp;     *)
         es_infer_pure = [ip];
       }
    ]
;;

let mkCtxWithFrame framep frameh =
  let state_f = construct_base frameh framep in
  let es = mkEmptyes () in
  let new_es =
    {es with
      es_formula = state_f;
    }
  in
  SuccCtx [Ctx new_es]
;;  


let rec print_indent depth str =
    if depth = 0
    then "   "^str
    else "   "^(print_indent (depth-1) str)
;;

