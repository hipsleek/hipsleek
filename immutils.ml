#include "xdebug.cppo"

(* extension of cpure, focused on imm related operations  *)

open Globals
open VarGen
open Gen.Basic
open Cpure
(* open Imminfer *)

(* assumption: f is in CNF *)
let build_eset_of_imm_formula f =
  let lst = split_conjunctions f in
  let emap = List.fold_left (fun acc f -> match f with
      | BForm (bf,_) ->
        (match bf with
         | (Eq (Var (v1,_), Var (v2,_), _),_) -> 
           if (is_bag_typ v1) then acc
           else EMapSV.add_equiv acc v1 v2
         | (Eq (ex, Var (v1,_), _),_) 
         | (Eq (Var (v1,_), ex, _),_) -> 
           (match conv_ann_exp_to_var ex with
            | Some (v2,_) -> EMapSV.add_equiv acc v1 v2
            | None -> acc)
         | (SubAnn (Var (v1,_), AConst(Mutable,_), _),_) -> (* bot *)
           let v2 = mkAnnSVar Mutable in EMapSV.add_equiv acc v1 v2
         | (SubAnn(AConst(Accs,_), Var (v1,_), _),_) -> (* top *)
           let v2 = mkAnnSVar Accs in EMapSV.add_equiv acc v1 v2
         | _ -> acc)
      | _ -> acc
    ) EMapSV.mkEmpty lst in 
  emap

module Poset =
  struct
    type t = spec_var
    let top = imm_top_sv
    let is_top a = eq_spec_var a top
    let bot = imm_bot_sv
    let is_bot a = eq_spec_var a bot 
  end;;

module GenImmSV = Gen.GenRel (SV) (PtrSV) (Poset);;

(* assumption: f is in CNF *)
let build_imm_genrel_of_formula f =
  let is_imm = is_exp_ann in
  let imm2sv = conv_ann_exp_to_var_exc in
  let f_bf irel bf =
    let pf, _ = bf in
    match pf with
    | Eq (e1, e2, _),_ -> 
      if (is_imm e1) && (is_imm e2) then Some (GenImmSV.add_eq irel (imm2sv e1) (imm2sv e2))
      else None
    | Neq (e1, e2, _),_ -> 
      if (is_imm e1) && (is_imm e2) then Some (GenImmSV.add_disj irel (imm2sv e1) (imm2sv e2))
      else None
    | SubAnn (e1, e2, _), _ -> 
      if (is_imm e1) && (is_imm e2) then Some (GenImmSV.add_sub irel (imm2sv e1) (imm2sv e2))
      else None
    | _ -> None
  in
  let irel = GenImmSV.mkEmpty in
  fold_formula_arg f irel (nonef2,nonef2,nonef2) (idf2, idf2, idf2) GenImmSV.merge_list

let build_eset_of_imm_formula f =
  let pr = !print_formula in
  let pr_out = EMapSV.string_of in
  Debug.no_1 "build_eset_of_imm_formula" pr pr_out build_eset_of_imm_formula f

let int_imm_to_exp i loc =
  mkExpAnnSymb (mkConstAnn (heap_ann_of_int i)) loc

let ann_sv_lst  = (name_for_imm_sv Mutable):: (name_for_imm_sv Imm):: (name_for_imm_sv Lend)::[(name_for_imm_sv Accs)]

let is_ann_const_sv sv = 
  match sv with
  | SpecVar(AnnT,a,_) -> List.exists (fun an -> an = a ) ann_sv_lst
  | _                 -> false

let is_ann_const_sv sv = 
  Debug.no_1 "is_ann_const_sv" !print_sv (fun b -> ite b "constant" "spec var")  is_ann_const_sv sv

let helper_is_const_ann_sv em sv test =
  let imm_const_sv = mkAnnSVar test in
  if not (is_ann_typ sv) then false
  else if eq_spec_var sv imm_const_sv then true
  else EMapSV.is_equiv em sv imm_const_sv 

let is_mut_sv ?emap:(em=[])  sv = helper_is_const_ann_sv em sv Mutable 

let is_imm_sv ?emap:(em=[])  sv = helper_is_const_ann_sv em sv Imm

let is_lend_sv ?emap:(em=[]) sv = helper_is_const_ann_sv em sv Lend

let is_abs_sv ?emap:(em=[])  sv = helper_is_const_ann_sv em sv Accs

let is_imm_const_sv ?emap:(em=[])  sv = 
  (is_abs_sv ~emap:em sv) ||   (is_mut_sv ~emap:em sv) ||   (is_lend_sv ~emap:em sv) ||   (is_imm_sv ~emap:em sv)

let get_imm_list ?loc:(l=no_pos) list =
  let elem_const = (mkAnnSVar Mutable)::(mkAnnSVar Imm)::(mkAnnSVar Lend)::[(mkAnnSVar Accs)] in
  let anns_ann =  (ConstAnn(Mutable))::(ConstAnn(Imm))::(ConstAnn(Lend))::[(ConstAnn(Accs))] in
  let anns_exp =  (AConst(Mutable,l))::(AConst(Imm,l))::(AConst(Lend,l))::[(AConst(Accs,l))] in
  let anns = List.combine anns_ann anns_exp in
  let lst = List.combine elem_const anns in
  let imm = 
    try
      Some (snd (List.find (fun (a,_) -> EMapSV.mem a list  ) lst ) )
    with Not_found -> None
  in imm

let get_imm_list ?loc:(l=no_pos) list =
  Debug.no_1 "get_imm_list" !print_svl (pr_opt (pr_pair string_of_imm !print_exp)) (get_imm_list ~loc:l) list

let get_imm_emap ?loc:(l=no_pos) sv emap =
  let aliases = EMapSV.find_equiv_all sv emap in
  get_imm_list ~loc:l (sv::aliases)

let get_imm_emap_exp_opt  ?loc:(l=no_pos) sv emap : exp option = map_opt snd (get_imm_emap ~loc:l sv emap)

let get_imm_emap_exp  ?loc:(l=no_pos) sv emap : exp  = 
  map_opt_def (mkVar sv l) (fun x -> x) (get_imm_emap_exp_opt ~loc:l sv emap)

let get_imm_emap_ann_opt  ?loc:(l=no_pos) sv emap : ann option = map_opt fst (get_imm_emap ~loc:l sv emap)

let get_imm_from_pure_ann_opt  ?loc:(l=no_pos) sv pure : ann option =  
  let emap = build_eset_of_imm_formula pure in
  get_imm_emap_ann_opt  ~loc:l sv emap 

let get_imm_from_pure_ann_list  ?loc:(l=no_pos) sv pure : ann list =
  map_opt_def [] (fun x -> [x]) (get_imm_from_pure_ann_opt  ~loc:l sv pure)

(* replace with imm constant, where exp is constant or variable *)
let norm_emap_imm_exp  ?loc:(l=no_pos) (e: exp) emap : exp  = 
  match e with
  | Var(sv,l) ->  get_imm_emap_exp ~loc:l sv emap
  | _ -> e

(* replace with imm constant, where a is constant or variable *)
let norm_emap_imm  (a: ann) emap : ann  = 
  match a with
  | ConstAnn _ -> a
  | PolyAnn sv -> map_opt_def a (fun x -> x) (get_imm_emap_ann_opt sv emap)
  | _ -> a

let norm_emap_imm  (a: ann) emap : ann  =
  let pr1 = string_of_imm in 
  let pr2 = EMapSV.string_of in 
  Debug.no_2 "norm_emap_imm" pr1 pr2 pr1  norm_emap_imm a emap

let eq_const_ann const_imm em sv = 
  match const_imm with
  | Mutable -> is_mut_sv ~emap:em sv
  | Imm     -> is_imm_sv ~emap:em sv
  | Lend    -> is_lend_sv ~emap:em sv
  | Accs    -> is_abs_sv ~emap:em sv

let helper_is_const_imm em (imm:ann) const_imm = 
  match imm with
  | ConstAnn a -> a == const_imm
  | PolyAnn sv -> eq_const_ann const_imm em sv 
  | _ -> false

(* below functions take into account the alias information while checking if imm is a certain const. *)
let is_abs ?emap:(em=[]) (imm:ann) = helper_is_const_imm em imm Accs
let is_abs_exp ?emap:(em=[]) (e: exp) = is_abs ~emap:em (exp_to_imm e)

let is_abs_list ?emap:(em=[]) imm_list = List.for_all (is_abs ~emap:em) imm_list

let is_mutable ?emap:(em=[]) (imm:ann) = helper_is_const_imm em imm Mutable 

let is_mutable_list ?emap:(em=[]) imm_list =  List.for_all (is_mutable ~emap:em) imm_list

let is_immutable ?emap:(em=[]) (imm:ann) = helper_is_const_imm em imm Imm

let is_immutable_list ?emap:(em=[]) imm_list =  List.for_all (is_immutable ~emap:em) imm_list

let is_lend ?emap:(em=[]) (imm:ann) = helper_is_const_imm em imm Lend

let is_lend_list ?emap:(em=[]) imm_list =  List.for_all (is_lend ~emap:em) imm_list

let isAccs (a : ann) : bool = is_abs a

let isLend(a : ann) : bool = is_lend a

let isMutable(a : ann) : bool = is_mutable a

let isImm(a : ann) : bool = is_immutable a

let isPoly(a : ann) : bool = 
  match a with
  | PolyAnn v -> true
  | _ -> false

let isNoAnn(a : ann) : bool = 
  match a with
  | NoAnn -> true
  | _ -> false

let is_const_imm ?emap:(em=[]) (a:ann) : bool =
  match a with
  | ConstAnn _ -> true
  | PolyAnn sv -> (is_mutable ~emap:em a) || (is_immutable ~emap:em a) || (is_lend ~emap:em a) || (is_abs ~emap:em a)
  | _ -> false

let is_const_imm_list ?emap:(em=[]) (alst:ann list) : bool =
  List.for_all (is_const_imm ~emap:em) alst

(* end imm utilities *)

let contains_imm (f:formula) =
  let f_e e =  Some (is_ann_type (get_exp_type e)) in
  fold_formula f (nonef,nonef, f_e)  (List.exists (fun b -> b) )

let contains_imm (f:formula) =
  Debug.no_1 "contains_imm" !print_formula string_of_bool contains_imm f

(* ===================== imm addition utils ========================= *)

let gen_subtype emap imm1 imm2 test_fnc =
  if (is_const_imm ~emap:emap imm1) && (is_const_imm ~emap:emap imm2) then
    match (norm_emap_imm imm1 emap), (norm_emap_imm imm2 emap) with
    | ConstAnn a1, ConstAnn a2 -> Some (test_fnc a1 a2)
    | _ -> None
  else None

let strict_subtype emap imm1 imm2 = 
  let res = gen_subtype emap imm1 imm2 (fun a b -> a < b) in
  map_opt_def false (fun x -> x) res

let simple_subtype emap imm1 imm2 =
  let res = gen_subtype emap imm1 imm2 (fun a b -> a <= b) in
  map_opt_def true (fun x -> x) res

(* norm of imml = max(immr1,immr2) 
   @A = max(immr1,@M)  ----> immr1 = @A
   @CONST = max(immr1,@CONST)  ----> immr1 <: @CONST
   @M = max(immr1,@A)  ----> false
   @v = max(immr1,@M) -----> @v=@immr1

 *)
let norm_eqmax emap imml immr1 immr2 def = 
  let immr1, immr2 = norm_emap_imm immr1 emap, norm_emap_imm immr2 emap in
  if not (is_const_imm ~emap:emap imml) then 
    match immr1, immr2 with
    | (ConstAnn Accs), v2
    | v2, (ConstAnn Accs) -> mkPure (mkEq (imm_to_exp imml no_pos) (imm_to_exp (ConstAnn Accs) no_pos) no_pos)
    | (ConstAnn Mutable), v2
    | v2, (ConstAnn Mutable) -> mkPure (mkEq (imm_to_exp imml no_pos) (imm_to_exp v2 no_pos) no_pos)
    | _ -> def
  else
    match immr1, immr2 with
    | ((ConstAnn a) as v1), v2
    | v2, ((ConstAnn a) as v1) -> 
        if (strict_subtype emap imml v1) then 
          let () = report_warning no_pos ("creating false ctx during max norm)" ) in
          mkFalse no_pos
        else if not(helper_is_const_imm emap imml a) then 
          mkPure (mkEq (imm_to_exp imml no_pos) (imm_to_exp v2 no_pos) no_pos) 
        else 
          (mkSubAnn (imm_to_exp v2 no_pos) (imm_to_exp imml no_pos) ) 
    | _ -> def

let norm_eqmax emap imml immr1 immr2 def = 
  if not(!Globals.imm_add)  then def
  else  norm_eqmax emap imml immr1 immr2 def

let norm_eqmax emap imml immr1 immr2 def = 
  let pr1 = EMapSV.string_of in
  let pr2 = string_of_imm in
  let pr3 = !print_formula in
  Debug.no_5 "norm_eqmax" pr1 pr2 pr2 pr2 pr3 pr3 norm_eqmax emap imml immr1 immr2 def

(* norm of imml = min(immr1,immr2) 
   imml = min(immr1,@M)  ----> imml = @M
   imml = min(immr1,@A)  ----> imml = immr1
   @L = min(immr1,@M)    ----> false
   @M = min(immr1,@L)    ----> immr1=@M

 *)
let norm_eqmin emap imml immr1 immr2 def = 
  let immr1, immr2 = norm_emap_imm immr1 emap, norm_emap_imm immr2 emap in
  if not (is_const_imm ~emap:emap imml) then 
    match immr1, immr2 with
    | (ConstAnn Mutable), v2
    | v2, (ConstAnn Mutable) -> mkPure (mkEq (imm_to_exp imml no_pos) (imm_to_exp (ConstAnn Mutable) no_pos) no_pos)
    | (ConstAnn Accs), v2
    | v2, (ConstAnn Accs) -> mkPure (mkEq (imm_to_exp imml no_pos) (imm_to_exp v2 no_pos) no_pos)
    | _ -> def
  else
    match immr1, immr2 with
    | ((ConstAnn a) as v1), v2
    | v2, ((ConstAnn a) as v1) -> 
        if (strict_subtype emap v1 imml) then 
          let () = report_warning no_pos ("creating false ctx during min norm)" ) in
          mkFalse no_pos
        else if not(helper_is_const_imm emap imml a) then 
          mkPure (mkEq (imm_to_exp v2 no_pos) (imm_to_exp imml no_pos) no_pos)
        else 
          (mkSubAnn (imm_to_exp imml no_pos) (imm_to_exp v2 no_pos) ) 
    | _ -> def

let norm_eqmin emap imml immr1 immr2 def = 
  if not(!Globals.imm_add)  then def
  else  norm_eqmin emap imml immr1 immr2 def

let norm_eqmin emap imml immr1 immr2 def = 
  let pr1 = EMapSV.string_of in
  let pr2 = string_of_imm in
  let pr3 = !print_formula in
  Debug.no_5 "norm_eqmin" pr1 pr2 pr2 pr2 pr3 pr3 norm_eqmin emap imml immr1 immr2 def

(* assume e is Add(..) *)
let get_imm_var_cts_operands e =
  let rec helper e =
    match e with
    | Add (a1,a2,_) -> (helper a1)@(helper a2)
    | Var (sv, _)   -> [sv]
    | AConst (a,l)  -> [mkAnnSVar a]
    | _             -> []               (* should never reach this point if sum is well defined *)
  in helper e

let get_imm_var_cts_operands e =
  Debug.no_1 "get_imm_var_cts_operands" !print_exp !print_svl get_imm_var_cts_operands e

let mkAdd_list exp_lst =  
  let rec helper exp_lst = 
    match exp_lst with
    | [] -> AConst (Accs, no_pos)
    | [(AConst _ as e)]
    | [(Var _ as e)]  ->  e
    | e::tail -> Add(e, helper tail, no_pos)
  in helper exp_lst

let sv_to_imm_exp_flag_change sv emap loc = 
  let return_same_sv = (mkVar sv loc, true) in
  if is_ann_const_sv sv then (get_imm_emap_exp ~loc:loc sv emap, true)
  else 
    let ne = get_imm_emap_exp_opt ~loc:loc sv emap in
    map_opt_def return_same_sv (fun x -> (x,false)) ne

(* prune @A's from imm summation and replace vars with their corresponding constants if the information exists *)
let imm_summation emap e =

  (* retrieve addition operands - constanst or sv only *)
  let sum_operands = get_imm_var_cts_operands e in 

  (* replace vars with their corresponding constants if this info exists in emap *)
  let sum_operands = List.map (fun sv -> sv_to_imm_exp_flag_change sv emap (pos_of_exp e)) sum_operands in
  let sum_operands, fixptaux = List.split sum_operands in
  let fixpt = List.for_all (fun x-> x) fixptaux in

  (* prune @A's  *)
  let nonA_sum_operands = List.filter (fun x -> not(is_abs_exp x)) sum_operands in
  let fixpt = fixpt && (List.length sum_operands == List.length nonA_sum_operands) in

  (* count the no of non@A constants in the sum  *)
  (* let constants = List.filter (fun x -> is_const_imm ~emap:emap (exp_to_imm x)) nonA_sum_operands in *)
  let constants = List.filter (fun x -> is_mutable ~emap:emap (exp_to_imm x)) nonA_sum_operands in
  if (List.length constants <= 1) then (Some (mkAdd_list  nonA_sum_operands),fixpt) (* zero or only one @M constant *)
  else (None, fixpt)

let imm_summation emap e =
  let pr = !print_exp in
  let pr2 b = ite b "exp is unchanged" "exp has changed" in
  Debug.no_2 "imm_summation" EMapSV.string_of pr (pr_pair (pr_opt pr) pr2) imm_summation emap e

let norm_eq_add lhs_exp emap e l =
  (* let new_var  = f_e emap (Var(sv,lv)) in *) (* without this we might have false ctx: eg b=@L  & b=@A+@M*)
  (* let new_var = Var(lhs_sv,lhs_l) in *)
  let new_sum, fixpt = imm_summation emap e in
  let new_eq rhs = Eq (lhs_exp, rhs, l) in 
  let new_pf = map_opt_def  (BConst (false, l)) (fun x -> new_eq x) new_sum in
  (new_pf, fixpt)

let norm_subann_add mksubann emap e l =
  let new_sum, fixpt = imm_summation emap e in
  let new_pf = map_opt_def  (BConst (false, l)) (fun x -> mksubann x) new_sum in
  (new_pf, fixpt)

(*
   identity element: @A
   exp = @ct1 + @ct2  ----> false for @M <: ct1,ct2 <: @L
   exp = @ct1 + @v    ----> exp = @ct1 + @ct2 if emap of f contains (v,ct2)
   exp = @ct1 + @v    unchanged  if f doesn't contain a constant def for v
*)
let simplify_imm_addition emap0 (f:formula) =
  let fixpt = ref true in

  let f_b_ann_exp_check exp lbl f_op l  =
    if is_ann_type (get_exp_type exp) then 
      let new_pf, fixpt0 = f_op l in
      let () = if not(fixpt0) then fixpt:= false in
      Some (new_pf, lbl)
    else None in

  let mk_SubAnn_4Add l lhs rhs =  SubAnn (lhs, rhs, l) in

  let f_b emap fb =
    (* need a helper because of local var emap *)
    let f_b_helper bf =
      let (p_f, lbl) = bf in
      match p_f with
      (* | Eq ((Add(e11,e12,la1) as ea1, (Add(e21,e22,la2) as ea2), l)  *)
      | Eq (exp, (Add(e1,e2,la) as ea), l) 
      | Eq ( (Add(e1,e2,la) as ea), exp, l) -> 
        let f_eq l = norm_eq_add exp emap ea l in
        f_b_ann_exp_check exp lbl f_eq l
      | SubAnn (Var(sv,lv), (Add(e1,e2,la) as ea), l) ->
        let f_subann l = norm_subann_add (mk_SubAnn_4Add la (Var(sv,lv)) ) emap ea l in
        f_b_ann_exp_check (Var(sv,lv)) lbl f_subann l
      | SubAnn ((Add(e1,e2,la) as ea),Var(sv,lv), l) ->
        let f_subann l = norm_subann_add (fun x -> mk_SubAnn_4Add la x (Var(sv,lv)) ) emap ea l in
        f_b_ann_exp_check (Var(sv,lv)) lbl f_subann l
      | _ -> None
    in 
    let fb = transform_b_formula (f_b_helper, somef) fb in
    fb
  in

  let f_b emap fb =
    let pr1 = EMapSV.string_of in
    let pr2 = !print_b_formula in
    Debug.no_2 "f_b_imm_addition" pr1 pr2 pr2 f_b emap fb in
 
  let rec f_f emap f =
    match f with
    | BForm (b1,b2) ->  Some (BForm (f_b emap b1, b2))
    | Or (e1,e2,lbl,l) ->
      let emap1 = EMapSV.merge_eset emap (build_eset_of_imm_formula e1) in
      let e1 = map_formula_arg e1 emap1 (f_f, somef2, somef2) (idf2, idf2, idf2) in
      let emap2 = EMapSV.merge_eset emap (build_eset_of_imm_formula e2) in
      let e2 = map_formula_arg e2 emap2 (f_f, somef2, somef2) (idf2, idf2, idf2) in
      Some (Or (e1,e2,lbl,l))
    | Not (f, lbl, l) ->
      let emap = EMapSV.merge_eset emap (build_eset_of_imm_formula f) in
      let f = map_formula_arg f emap (f_f, somef2, somef2) (idf2, idf2, idf2) in
     Some ( Not (f, lbl, l))
    | _ -> None
  in

  let fncs = (f_f, somef2, somef2) in
  let rec helper form = 
    let () = fixpt := true in
    let emap = build_eset_of_imm_formula form in
    let emap = EMapSV.merge_eset emap emap0 in
    let () =  x_tinfo_hp (add_str "form" !print_formula) form no_pos in
    let () =  x_tinfo_hp (add_str "emap" EMapSV.string_of) emap no_pos in
    let new_form = map_formula_arg form emap fncs (idf2, idf2, idf2) in
    (* let () = fixpt:=(equalFormula form new_form) in *) (* using equalFormula leads to loop *)
    if not(!fixpt) then helper new_form else new_form
  in 
  let helper form =
    let pr = !print_formula in
    Debug.no_1 "helper_simplify" pr pr helper form in
  let disj = split_disjunctions_deep f in
  let disj = List.map helper disj in
  join_disjunctions disj
  (* helper f *)

let simplify_imm_addition emap f =
  if not(!Globals.imm_add)  then f
  else simplify_imm_addition emap f

let simplify_imm_addition ?emap:(em=[]) (f:formula) =
  let pr = !print_formula in
  Debug.no_1 "simplify_imm_addition" pr pr (simplify_imm_addition em) f

(* let is_rel_containing_ann_typ rel : bool = *)
(*   match r *)
let simplify_imm_min_max f =
  let mk_min_expand i a b loc lbl  =
    mkOr (mkAnd (mkEqExp i a loc) (mkSubAnn a b) loc)
         (mkAnd (mkEqExp i b loc) (mkAnd (mkSubAnn b a) (mkNeqExp b a loc) loc) loc)
         lbl loc in
  let f_b b_formula lbl = match b_formula with
    | (EqMin (id, lhs, rhs, loc), _) ->
       if not (is_exp_ann lhs && is_exp_ann rhs) then BForm (b_formula, lbl)
       else mk_min_expand id lhs rhs loc lbl
    | (EqMax (id, lhs, rhs, loc), _) ->
       if not (is_exp_ann lhs && is_exp_ann rhs) then BForm (b_formula, lbl)
       else mk_min_expand id rhs lhs loc lbl
    | b_formula -> BForm (b_formula, lbl) in
  let f_f f = match f with
    | BForm (b_formula, lbl) -> Some (f_b b_formula lbl)
    | _ -> None in
  transform_formula (nonef, nonef, f_f, nonef, nonef) f

let simplify_imm_min_max (f:formula) =
  let pr = !print_formula in
  Debug.no_1 "simplify_imm_min_max" pr pr simplify_imm_min_max f

(* module SubAnnPoset0 = Gen.Make_POSET(SV) *)
module SubAnnPoset0 = Gen.Make_POSET(SV) (* Poset *)

let prune_imm_min_max_conjunct poset f =
  let f_b b_formula lbl = 
    let def = BForm (b_formula, lbl) in
    match b_formula with
    | (EqMin (id, lhs, rhs, loc), p) ->
      if (is_exp_ann lhs) && (is_exp_ann rhs) then 
        begin match SubAnnPoset0.is_lt_opt poset (conv_ann_exp_to_var_exc lhs) (conv_ann_exp_to_var_exc rhs) with
          | Some true -> mkEqExp id lhs loc
          | Some false -> mkEqExp id rhs loc
          | None -> def 
        end
      else def
    | (EqMax (id, lhs, rhs, loc), _) ->
      if (is_exp_ann lhs) && (is_exp_ann rhs) then 
        begin match SubAnnPoset0.is_lt_opt poset (conv_ann_exp_to_var_exc lhs) (conv_ann_exp_to_var_exc rhs) with
          | Some true -> mkEqExp id rhs loc
          | Some false -> mkEqExp id lhs loc
          | None -> def 
        end
      else def
    | b_formula -> def in
  let f_f f = match f with
    | BForm (b_formula, lbl) -> Some (f_b b_formula lbl)
    | _ -> None in
  transform_formula (nonef, nonef, f_f, somef, somef) f

(* Pruned Case
  1. a=min(b,c), given some ann subtyping relations, deduce a=b or a=c if possible
  2. a=top & a <: b & a != b
  3. a=bot & b <: a & a != b
*)
let prune_eq_top_bot_imm_disjunct f =
  let emap = build_eset_of_imm_formula f in 
  let collect_subann p_f =
    match p_f with
    | SubAnn (Var(sv1,_), Var(sv2,_),_) -> [(sv1, sv2)]
    | _ -> [] in
  let collect_eq_imm imm p_f = match p_f with
    | Eq (Var(sv,_), AConst(imm, _), _) -> [sv]
    | Eq (AConst(imm,_), Var(sv,_), _) -> [sv]
    | _ -> [] in
  let collect_eq_bot = collect_eq_imm imm_bot in
  let collect_eq_top = collect_eq_imm imm_top in
  let collect_neq_sv p_f = match p_f with
    | Neq (Var(sv1,_), Var(sv2, _), _) -> [(sv1, sv2)]
    | _ -> [] in
  let get4 p_f = (collect_subann p_f, collect_eq_bot p_f,
                  collect_eq_top p_f, collect_neq_sv p_f) in
  let concat4 xs = List.fold_right (fun (a,b,c,d) (e,f,g,h) -> (a@e, b@f, c@g, d@h)) xs
                                   ([],[],[],[]) in
  let (subanns, eq_bot, eq_top, neq_sv) =
    (fun (a,b,c,d) -> (a, SetSV.of_list b, SetSV.of_list c, d))
    (fold_formula f (nonef, (fun (p_f,_) -> Some (get4 p_f)), nonef) concat4) in
  let poset =
    (* let p = SVPoset.create () in *)
    (* (List.iter (SVPoset.add p) subanns; p) in *)
    let p = SubAnnPoset0.mkEmpty in
    let p = SubAnnPoset0.add_list p subanns in
    p in
  let ( <: ) a b = 
      (* let res = SVPoset.is_lt poset a b in *)
      let res = SubAnnPoset0.is_lt poset a b in
      (* let () = y_binfo_pp ((!print_sv a) ^ "<:" ^ (!print_sv b) ^ " " ^ (string_of_bool res)) in *)
      res in
  let ( := ) a b = eq_const_ann b emap a in(*TODOIMM: should use emap *)
    (* SetSV.mem a (if b = imm_top then eq_top else eq_bot) in *)
  let prune_if_top a b = 
    let res = ((a := imm_top) && (a <: b)) || ((b := imm_top) && (b <: a)) in
    (* let () = y_binfo_pp ("prune? "^(!print_sv a) ^ "," ^ (!print_sv b) ^ " " ^ (string_of_bool res)) in *)
    res in
  let prune_if_bot a b = ((a := imm_bot) && (b <: a)) || ((b := imm_bot) && (a <: b)) in
  let prune_if_match (sv1, sv2) =  prune_if_top sv1 sv2 || prune_if_bot sv1 sv2 in
  let res = List.fold_right (fun b acc -> acc || prune_if_match b) neq_sv false in
  res

let prune_eq_top_bot_imm_disjunct f =
  let pr = !print_formula in
  Debug.no_1 "prune_eq_top_bot_imm_disjunct" pr string_of_bool prune_eq_top_bot_imm_disjunct f

let improved_join_disjunctions old_ds new_ds = 
  if ((List.length new_ds == 0) && (List.length old_ds != 0)) then mkFalse no_pos 
  else join_disjunctions new_ds

let prune_eq_top_bot_imm f =
  let conj_lst = split_conjunctions f in
  let imm, non_imm = List.partition contains_imm conj_lst in
  let non_imm_part = join_conjunctions non_imm in
  let imm_part = join_conjunctions imm in
  let ds = split_disjunctions_deep imm_part in
  let new_disjunctions = List.filter (fun f -> not (prune_eq_top_bot_imm_disjunct f)) ds in
  join_conjunctions ([improved_join_disjunctions ds new_disjunctions]@[non_imm_part])

let wrapper_strip_exists f fnc =
  let strippedf, quantif = strip_out_quantif f in
  let new_f = fnc strippedf in
  let new_f = mkQuantif quantif new_f (get_pure_label f) (pos_of_formula f) in
  new_f 

let prune_eq_top_bot_imm_helper f = wrapper_strip_exists f prune_eq_top_bot_imm

let prune_eq_top_bot_imm f = prune_eq_top_bot_imm_helper f

let prune_eq_top_bot_imm f =
  let pr = !print_formula in
  Debug.no_1 "prune_eq_top_bot_imm" pr pr prune_eq_top_bot_imm f

let prune_eq_min_max_imm f =
  let collect_subann f =
    let is_subann p_f = match p_f with SubAnn _ -> true | _ -> false in
    let to_pair p_f = match p_f with
      | SubAnn (e1,e2,_) -> (conv_ann_exp_to_var_exc e1, conv_ann_exp_to_var_exc e2)
      | _ -> failwith "Not possible" in
    fold_formula f (nonef, (fun (p_f,_) ->
                            if is_subann p_f then Some [to_pair p_f]
                            else None), nonef) List.concat in
  let f_f f = match f with
    | BForm _ ->
       let poset = SubAnnPoset0.mkEmpty in
       (* let () = List.iter (SubAnnPoset.add poset) (collect_subann f) in *)
       let poset = SubAnnPoset0.add_list poset (collect_subann f) in
       Some (prune_imm_min_max_conjunct poset f)
    | And (f1, f2, pos) ->
       let poset = SubAnnPoset0.mkEmpty in
       (* let () = List.iter (SubAnnPoset.add poset) (collect_subann f1) in *)
       (* let () = List.iter (SubAnnPoset.add poset) (collect_subann f2) in *)
       let poset = SubAnnPoset0.add_list poset (collect_subann f1) in
       let poset = SubAnnPoset0.add_list poset (collect_subann f2) in
       (* -------- test 4 poset ------------  *)
       (* let afv1 = all_vars f1 in *)
       (* let afv2 = all_vars f2 in *)
       (* let afv = (afv1@afv2) in *)
       (* let afv_p = List.fold_left (fun acc sv -> (List.fold_left (fun acc0 sv0 -> (sv,sv0)::acc0) [] afv)@acc ) [] afv in *)
       (* let () = pr_list (fun (a1,a2) -> ((pr_pair !print_sv !print_sv) (a1,a2))^ (if SubAnnPoset.has_path poset a1 a2 then ": connected" else ": not connected")) afv_p in *)
       (* -------- test 4 poset ------------  *)
       Some (mkAnd (prune_imm_min_max_conjunct poset f1)
                   (prune_imm_min_max_conjunct poset f2) pos)
    | other -> None in
  transform_formula (nonef, nonef, f_f, somef, somef) f


let prune_eq_min_max_imm f =
  let pr = !print_formula in
  Debug.no_1 "prune_eq_min_max_imm" pr pr prune_eq_min_max_imm f

let simp_imm_min_max f = 
  let allv = all_vars f in
  if (List.exists is_ann_typ allv) then 
    (* a=min(b,c) & some subtyping *)
    let f_0 = prune_eq_min_max_imm f in
    (* a=min(b,c) --> (... | ...) *)
    let f_1 = simplify_imm_min_max f_0 in
    (* a=top & a <: b & a != b *)
    let f_2 = prune_eq_top_bot_imm f_1 in
    f_2
  else f

let simp_imm_min_max f = 
  Debug.no_1 "simp_imm_min_max" !print_formula !print_formula simp_imm_min_max f

(* let build_imm_utils f =  *)
(*   let emap = in *)
(*   let dset = in *)
(*   let subp = in *)
(*   let f_e = in *)
  
(*   fold_formula_arg f (emap, dset, subp) (nonef, nonef, f_e) f_comb *)
  
(* ===================== END imm addition utils ========================= *)

