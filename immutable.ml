#include "xdebug.cppo"
open VarGen
(*
2011: Immutability module:
  - utils for immutability
*)

open Globals
open Cast
open Prooftracer
open Gen.Basic
open Cformula

module CP = Cpure
module PR = Cprinter
module MCP = Mcpure
module Err = Error
module TP = Tpdispatcher
module IF = Iformula
module IP = Iprinter
module C  = Cast
module I  = Iast
module Imm = Immutils


(* let rec split_phase_debug_lhs h = Debug.no_1 "split_phase(lhs)" *)
(*   Cprinter.string_of_h_formula  *)
(*   (fun (a,b,c) -> "RD = " ^ (Cprinter.string_of_h_formula a) ^ "; WR = " ^ (Cprinter.string_of_h_formula b) ^ "; NEXT = " ^ (Cprinter.string_of_h_formula c) ^ "\n")  *)
(*   split_phase h *)

(* and split_phase_debug_rhs h = Debug.no_1 "split_phase(rhs)" *)
(*   Cprinter.string_of_h_formula  *)
(*   (fun (a,b,c) -> "RD = " ^ (Cprinter.string_of_h_formula a) ^ "; WR = " ^ (Cprinter.string_of_h_formula b) ^ "; NEXT = " ^ (Cprinter.string_of_h_formula c) ^ "\n")  *)
(*   split_phase 0 h *)

let isAccs = CP.isAccs 
let isLend = CP.isLend 
let isImm = CP.isImm 
let isMutable = CP.isMutable

let defCImm = ref (CP.ConstAnn Mutable)
let defIImm = ref (Ipure.ConstAnn Mutable)

let isAccsList (al : CP.ann list) : bool = List.for_all isAccs al
let isMutList (al : CP.ann list) : bool = List.for_all isMutable al

let isExistsLendList (al : CP.ann list) : bool = List.exists isLend al
let isExistsMutList (al : CP.ann list) : bool = List.exists isMutable al

let set_imm (f : h_formula) imm : h_formula =  match f with
  | DataNode h -> DataNode {h with h_formula_data_imm = imm; }
  | ViewNode h -> ViewNode {h with h_formula_view_imm = imm; }
  | _ -> f

let split_imm_pure_lst pf =
  let split_imm_pure_helper pf0 =
    let conjs = CP.split_conjunctions pf0 in
    let imm_f, pure_f = List.partition Imm.contains_imm conjs in
    (CP.conj_of_list imm_f no_pos), (CP.conj_of_list pure_f no_pos) in
  let disj = CP.split_disjunctions_deep pf in
  let disj_part = List.map split_imm_pure_helper disj in (* split each disj in imm formula + pure formula *)
  let () = x_tinfo_hp (add_str "imm + pure" (pr_list (pr_pair !CP.print_formula !CP.print_formula))) disj_part no_pos in
  let disj_part = List.map (fun (ximm,ypure) -> (TP.simplify_tp ximm, ypure)) disj_part in (* simplify the imm formula of each disjunct *)
  let () = x_tinfo_hp (add_str "imm + pure" (pr_list (pr_pair !CP.print_formula !CP.print_formula))) disj_part no_pos in
  let disj_part = List.filter (fun (ximm,ypure) -> not (CP.is_False ximm)) disj_part in  (* remove unsat disjuncts *)
  let imms, pures = List.split disj_part in
  (imms, pures)

let split_imm_pure pf =
  let imms, pures = split_imm_pure_lst pf in
  (CP.join_conjunctions imms, CP.join_disjunctions pures) (* weaken imm *)

let split_imm_pure pf =
  let pr = !CP.print_formula in
  Debug.no_1 "split_imm_pure" pr (pr_pair pr pr) split_imm_pure pf

let imm_unify (form:CP.formula): CP.formula = 
  let simp_immf, pure = split_imm_pure form in
  if not (CP.is_False simp_immf) then
    let immf = simp_immf in
    (* let pure = CP.join_disjunctions pures in *)
    let pr = !CP.print_formula in
    let () = x_tinfo_hp (add_str " vp_pos:" (pr_pair (add_str "imm" pr) (add_str "pure" pr) ) ) (immf, pure) no_pos in
    (* let pure = TP.simplify_tp pure in  *)  (* TODOIMM check if pure simplif is also mandatory? temp disabled*)
    CP.mkAnd immf pure no_pos 
  else form (* if we cannot strenghten the imm formula, return the initial formula *)

let imm_unify (form:CP.formula): CP.formula = 
  let pr = !CP.print_formula in
  Debug.no_1 "imm_unify" pr pr imm_unify form


(* if pure contains sv=AConst, then instantiate to AConst *)
let pick_equality_instantiation sv loc pure : CP.formula option =
  let p_aset = Imm.build_eset_of_imm_formula pure in
  let imm = Imm.get_imm_emap_exp_opt sv p_aset in
  map_opt (fun a ->  CP.BForm ((CP.Eq(CP.Var (sv, loc), a, no_pos), None), None)) imm

let pick_equality_instantiation sv loc pure : CP.formula option =
  let pr = Cprinter.string_of_pure_formula in
  Debug.no_1 "pick_equality_instantiation" pr (pr_opt pr) (fun _ -> pick_equality_instantiation sv loc pure) pure

(* if f contains sv=AConst, then instantiate to AConst *)
let pick_equality_instantiation_formula sv loc f =
  let pure = CF.get_pure f in
  pick_equality_instantiation sv loc pure

(* if f contains sv=AConst, then instantiate to AConst *)
let pick_equality_instantiation_formula sv loc f =
  let pr1 = Cprinter.string_of_spec_var in
  let pr2 = Cprinter.string_of_formula in
  let pr3 = pr_opt Cprinter.string_of_pure_formula in 
  Debug.no_2 "pick_equality_instantiation_formula" pr1 pr2 pr3 (fun _ _ -> pick_equality_instantiation_formula sv loc f) sv f

let upper_bounds aliases pure =
  let f_b_bormula f =
    let (p_f, _) = f in
    let res =
      match p_f with
      | CP.SubAnn(e1,e2,l) -> 
        if CP.EMapSV.mem (CP.imm_to_spec_var (CP.exp_to_imm e1)) aliases then [CP.exp_to_imm e2] else []
      | _ -> []
    in Some res
  in
  let fncs = (nonef,f_b_bormula,nonef) in
  let f_comb lst = List.flatten lst  in
  CP.fold_formula pure fncs f_comb

let is_global a quantif =
  match a with 
  | CP.ConstAnn _ -> true
  | CP.PolyAnn sv -> not (CP.EMapSV.mem sv quantif)
  | _ -> 
    failwith "TempRes/TempAnn not yet supported for instantiations"

let weakest_rels v a1 a2 loc = CP.mkEqMax v a1 a2 loc
let weakest_rel a1 a2 loc = CP.mkEq a1 a2 loc
let default_inst a1 a2 loc = CP.mkPure (CP.mkEq a1 a2 loc)
let weakest_inst a1 a2 loc = CP.mkSubAnn a1 a2 

let lhs_rhs_rel l r to_rhs = 
  if not (!Globals.imm_weak) then default_inst l r no_pos, [to_rhs] 
  else weakest_inst l r no_pos, [to_rhs]

let upper_bound_rel sv bound = CP.mkPure (CP.mkEq sv bound no_pos)

let conj_of_bounds rhs_sv ann1 ann2 lst loc =
  let rhs_exp = CP.Var (rhs_sv, loc) in
  let freshsv = CP.fresh_spec_var rhs_sv in
  let inst1 = [ (CP.Var(freshsv,loc), (CP.imm_to_exp ann1 loc, CP.imm_to_exp ann2 loc)) ] in
  let maxs = List.fold_right  (fun a acc -> 
      match acc with
      | [] -> acc
      | (v, (a1, a2))::_ -> 
        let freshv = CP.Var (CP.fresh_spec_var rhs_sv, loc) in
        (freshv, (v, CP.imm_to_exp a loc))::acc
    ) lst inst1 in
  let maxs = match maxs with
    | [] -> []
    | (h,(a1,a2))::tail -> (rhs_exp, (a1,a2))::tail in
  let conjs = List.map ( fun (v,(a1,a2)) -> CP.BForm ((weakest_rels v a1 a2 loc, None), None) ) maxs in
  CP.conj_of_list conjs loc


(* returns instantiation * proof obligation *)
let pick_bounds max_bounds var_to_be_instantiated sv_to_be_instantiated 
    qvars loc : CP.formula option * CP.formula list option = 
  (* filter out quantif *)
  let max_bounds = List.filter (fun a -> is_global a qvars) max_bounds in 
  let inst = 
    match max_bounds with
    | []    -> None, None
    | a::[] -> Some ( (* weakest_rel *) fst (lhs_rhs_rel var_to_be_instantiated (CP.imm_to_exp a loc) var_to_be_instantiated)), None
    | a1::a2::tail ->  
      let guards = conj_of_bounds sv_to_be_instantiated a1 a2 tail loc in
      Some guards, None
  in inst

let pick_bounds max_bounds var_to_be_instantiated sv_to_be_instantiated 
    qvars loc : CP.formula option * CP.formula list option = 
  let pr1 = pr_list Cprinter.string_of_imm in 
  let pr = Cprinter.string_of_pure_formula in 
  let pr_out = pr_pair (pr_opt pr) (pr_opt (pr_list pr)) in 
  Debug.no_1 "pick_bounds" pr1 pr_out (fun _ -> pick_bounds max_bounds var_to_be_instantiated sv_to_be_instantiated qvars loc) max_bounds 

(* ################# new algo ################### *)

let lhs_rhs_rel l r  = 
  if not (!Globals.imm_weak) then default_inst l r no_pos
  else weakest_inst l r no_pos

let upper_bound_rel sv bound = CP.mkPure (CP.mkEq sv bound no_pos)
let lower_bound_rel sv bound = CP.mkPure (CP.mkEq sv bound no_pos)
let alias_rel sv1 sv2 = CP.mkEqVar sv1 sv2 no_pos
let inst_to_top sv = upper_bound_rel sv CP.const_ann_top

let pr_out = pr_pair (pr_opt Cprinter.string_of_pure_formula) (pr_opt (pr_list Cprinter.string_of_pure_formula) )

let get_bounds ~upper:upper aliases pure  =
  let f_b_bormula f =
    let (p_f, _) = f in
    let res =
      match p_f with
      | CP.SubAnn(e1,e2,l) -> 
        if upper then if CP.EMapSV.mem (CP.imm_to_spec_var (CP.exp_to_imm e1)) aliases then [CP.exp_to_imm e2] else []
        else if CP.EMapSV.mem (CP.imm_to_spec_var (CP.exp_to_imm e2)) aliases then [CP.exp_to_imm e1] else []
      | _ -> []
    in Some res
  in
  let fncs = (nonef,f_b_bormula,nonef) in
  let f_comb lst = List.flatten lst  in
  CP.fold_formula pure fncs f_comb

(* returns instantiation * proof obligation *)
let pick_bounds ~upper:upper bounds var_to_be_instantiated sv_to_be_instantiated: CP.formula option * CP.formula list option = 
  let inst = 
    match bounds with
    | []    -> None, None
    | a::_ ->
      if upper then Some ( upper_bound_rel var_to_be_instantiated (CP.imm_to_exp a no_pos)), None 
      else Some ( lower_bound_rel var_to_be_instantiated (CP.imm_to_exp a no_pos)), None 
  in inst

let pick_bounds ~upper:upper bounds var_to_be_instantiated sv_to_be_instantiated : CP.formula option * CP.formula list option = 
  let pr1 = pr_list Cprinter.string_of_imm in 
  let pr = Cprinter.string_of_pure_formula in 
  let pr_out = pr_pair (pr_opt pr) (pr_opt (pr_list pr)) in 
  Debug.no_1 "pick_bounds" pr1 pr_out (fun _ -> pick_bounds upper bounds var_to_be_instantiated sv_to_be_instantiated) bounds 

let pick_weakest_instatiation_new lhs_exp rhs_sv loc lhs_f rhs_f ivars evars =
  let rhs_exp = CP.Var(rhs_sv,loc) in
  let lrsubtype = lhs_rhs_rel lhs_exp rhs_exp in
  let pure_lhs = CF.get_pure lhs_f in
  let pure_rhs = CF.get_pure rhs_f in
  let evars = Gen.BList.difference_eq CP.eq_spec_var evars [rhs_sv] in

  (* return lhs & rhs pures relevant to svl *)
  let get_relevant_lhs_rhs lhs rhs svl =
    (* TODOIMM to check if we need the rel for subsequent steps *)
    (* filter out rels *)
    let lhs = CP.drop_rel_formula lhs in
    let rhs = CP.drop_rel_formula rhs in
    let relevant_constr = CP.filter_var_new (CP.join_conjunctions [lhs;rhs]) svl in
    let relevant_vars = CP.fv relevant_constr in
    let lhs_p = CP.filter_var_new pure_lhs relevant_vars in
    let rhs_p = CP.filter_var_new pure_rhs relevant_vars in
    lhs_p, rhs_p in

  (* crop only the relevant constraints from both lhs and rhs pures *)
  let lhs_p, rhs_p = get_relevant_lhs_rhs pure_lhs pure_rhs (rhs_sv::(CP.afv lhs_exp)) in
  let lhs_p_restricted, rhs_p_restricted = get_relevant_lhs_rhs pure_lhs pure_rhs [rhs_sv] in

  let () = x_ninfo_hp (add_str "lhs_p:" !CP.print_formula) lhs_p no_pos in
  let () = x_ninfo_hp (add_str "lhs_restricted:" !CP.print_formula) lhs_p_restricted no_pos in
  let () = x_ninfo_hp (add_str "rhs_p:" !CP.print_formula) rhs_p no_pos in
  let () = x_ninfo_hp (add_str "rhs_p_restricted:" !CP.print_formula) lhs_p_restricted no_pos in

  let pick_eq p1 = (pick_equality_instantiation rhs_sv loc p1, None) in

  let instantiate_to_bounds_aux ~upper:upper pure aliases  =
    let candidates = get_bounds ~upper:upper (rhs_sv::aliases) pure in
    match candidates with
    | [] -> None, None
    | _  -> x_add (pick_bounds ~upper:upper) candidates rhs_exp rhs_sv  in
  
  let instantiate_to_bounds_aux ~upper:upper candidates pure =
    let pr1 b = ite b "seraching for upper bounds" "seraching for lower bounds" in
    Debug.no_1 "instantiate_to_bounds_aux" pr1 pr_out (fun _ -> instantiate_to_bounds_aux ~upper:upper candidates pure) upper  in

  (* check for upper/lower bounds and instantiate to that *)
  let instantiate_to_bounds pure =
    let aset = Imm.build_eset_of_imm_formula pure in
    let aliases = CP.EMapSV.find_equiv_all rhs_sv aset in
    let to_lhs_max_bound, to_rhs = instantiate_to_bounds_aux ~upper:true pure aliases in
    to_lhs_max_bound, to_rhs in
    (* avoid inst to lower bound *)
    (* let inst_to_min = instantiate_to_bounds_aux ~upper:false pure aliases in *)
    (* map_opt_def inst_to_min (fun x -> Some x, to_rhs) to_lhs_max_bound in *)

  let instantiate_to_bounds pure =
    Debug.no_1 "instantiate_to_bounds" !CP.print_formula pr_out instantiate_to_bounds pure in

  (* 3 find poly bounds and instantiate to global bound *)
  let pick_bounds_incl_global () =
    let qvars4 = evars in
    let form4 = CP.join_conjunctions [lhs_p;rhs_p] in
    let form4 = TP.simplify_tp (CP.wrap_exists_svl form4 qvars4) in
    if (CP.is_False form4) then Some (CP.mkTrue no_pos), None
    else
      let helper () = 
        (*5 pick poly bound *)
        let to_lhs, to_rhs = x_add_1 instantiate_to_bounds form4 in
        (* map_opt_def (None,None) (fun x -> (Some x, to_rhs)) to_lhs  *)
        (* instantiate to top (@A) if no explicit upper bound (constant or poly) found *)
        map_opt_def (Some (inst_to_top rhs_exp), to_rhs) (fun x -> (Some x, to_rhs)) to_lhs 
      in
      (*4 check for poly eq first *)
      let aset = Imm.build_eset_of_imm_formula form4 in
      let alias = CP.EMapSV.find_equiv rhs_sv aset in
      map_opt_def (helper () ) (fun x -> Some (alias_rel x rhs_sv), None) alias in

  (*2. check if rhs_p_restricted is true and if so, inst to lhs_imm<:rhs_imm *)
  let check4_empty rhs_p_restricted rhs_p = 
    let form = TP.simplify_tp (CP.wrap_exists_svl rhs_p_restricted evars) in
    let () = x_ninfo_hp (add_str "rhs simplified:" !CP.print_formula) form no_pos in
    if (CP.is_True form) then (* Some (inst_to_top rhs_exp) *) Some lrsubtype, None
    else
      (* 3 find constant bounds and instantiate to bound *)
      let qvars3 = Gen.BList.difference_eq CP.eq_spec_var ((CP.all_vars lhs_p)@(CP.all_vars rhs_p)) [rhs_sv] in
      let form3 = CP.join_conjunctions [lhs_p;rhs_p] in
      let form3 = TP.simplify_tp (CP.wrap_exists_svl form3 qvars3) in
      let to_lhs, to_rhs = x_add_1 instantiate_to_bounds form3 in
      map_opt_def (pick_bounds_incl_global ()) (fun x -> (Some x, to_rhs)) to_lhs in

  (* 1. check the proof that v=IConst in lhsp & rhs_p;*)
  let form = CP.join_conjunctions [lhs_p;rhs_p] in
  let to_lhs, to_rhs = pick_eq form in
  let to_lhs, to_rhs =  map_opt_def (check4_empty rhs_p_restricted rhs_p) (fun x -> Some x, to_rhs) to_lhs in
  
  (* final check for sat and empty rhs_relevant *)
  let to_lhs_lst = map_opt_def [] (fun x -> [x]) to_lhs in
  let to_chek_4_sat = CP.join_conjunctions ([lhs_p;(* rhs_p; *)lrsubtype]@to_lhs_lst) in
  if (CP.is_False (TP.simplify_tp to_chek_4_sat)) then Some (CP.mkTrue no_pos), None
  else 
    (* if the lhs relevant pure is empty, add lhs<:rhs to the  *)
    let lhs_rele = CP.filter_var_new lhs_p (CP.afv lhs_exp) in
    if ((CP.is_True lhs_rele) && !Globals.aggresive_imm_inst) then 
      Some (CP.join_conjunctions (lrsubtype::to_lhs_lst)), Some [] (* this is not very sound... *)
    else to_lhs, to_rhs 

let pick_weakest_instatiation lhs rhs loc lhs_f rhs_f ivars evars=
  let pr2 = Cprinter.string_of_formula in
  let pr3 = pr_pair (pr_opt Cprinter.string_of_pure_formula) (pr_opt (pr_list Cprinter.string_of_pure_formula) ) in
  Debug.no_2 "pick_weakest_instatiation" pr2 pr2 pr3 (fun _ _ -> pick_weakest_instatiation_new lhs rhs loc lhs_f rhs_f ivars evars) lhs_f rhs_f

let get_emaps lhs_f rhs_f elhs erhs =
  match elhs, erhs with  
  | [], [] -> 
    let elhs = Imm.build_eset_of_imm_formula (CF.get_pure lhs_f) in
    let erhs = Imm.build_eset_of_imm_formula (CF.get_pure rhs_f) in
    elhs,erhs 
  | _ -> elhs,erhs

let post_process_subtype_answer v emap unk_fnc rec_fnc =
  let imm_l = Imm.get_imm_emap_ann_opt v emap in
  map_opt_def (unk_fnc ()) (fun a -> 
      let _, rel = unk_fnc () in 
      let subtype, _ = rec_fnc a in
      (subtype,rel)
    ) imm_l  

(* result: res:bool * (ann constraint = relation between lhs_ann and rhs_ann) *)
let subtype_ann_pair_x  elhs erhs strong_subtype (imm1 : CP.ann) (imm2 : CP.ann) : bool * ((CP.exp * CP.exp) option) =
  let rec helper imm1 imm2 = 
    match imm1 with
    | CP.PolyAnn v1 ->
      let unk_sv () =
        match imm2 with
        | CP.PolyAnn v2 -> (true, Some (CP.Var(v1, no_pos), CP.Var(v2, no_pos)))
        | CP.ConstAnn k2 -> if strong_subtype then (false, None)
          else (true, Some (CP.Var(v1,no_pos), CP.AConst(k2,no_pos)))
        | CP.TempAnn _ | CP.NoAnn -> (helper imm1 (CP.ConstAnn(Accs)))
        | CP.TempRes (al,ar) -> (helper imm1 ar)  (* andreeac should it be Accs? *) in
      post_process_subtype_answer v1 elhs unk_sv (fun imm -> helper imm imm2 )
    | CP.ConstAnn k1 ->
      (match imm2 with
       | CP.PolyAnn v2 -> 
         let unk_sv () = 
           if strong_subtype then (true, None) 
           else (true, Some (CP.AConst(k1,no_pos), CP.Var(v2,no_pos))) in
         post_process_subtype_answer v2 erhs unk_sv (fun imm -> helper imm1 imm )
       | CP.ConstAnn k2 -> ((int_of_heap_ann k1)<=(int_of_heap_ann k2),None) 
       | CP.TempAnn _ | CP.NoAnn -> (helper imm1 (CP.ConstAnn(Accs)))
       | CP.TempRes (al,ar) -> (helper imm1 ar)  (* andreeac should it be Accs? *)
      ) 
    | CP.TempAnn _ | CP.NoAnn -> (helper (CP.ConstAnn(Accs)) imm2) 
    | CP.TempRes (l,ar) -> (helper (CP.ConstAnn(Accs)) imm2)  (* andreeac should it be ar-al? or Accs? *)
  in helper imm1 imm2

let subtype_ann_pair 
    ?emap_lhs:(elhs = CP.EMapSV.mkEmpty)
    ?emap_rhs:(erhs = CP.EMapSV.mkEmpty)
    ?strong_subtype:(ss=false)
    (imm1 : CP.ann) (imm2 : CP.ann) : bool * ((CP.exp * CP.exp) option) =
  let pr_imm = Cprinter.string_of_imm in
  let pr1 (imm1,imm2) =  (pr_imm imm1) ^ " <: " ^ (pr_imm imm2) ^ "?" in
  let pr2 = CP.EMapSV.string_of in
  let pr_exp = CP.ArithNormalizer.string_of_exp in
  let pr_out = pr_pair string_of_bool (pr_option (pr_pair (add_str "l(subtype)" pr_exp) (add_str "r(subtype_" pr_exp)) ) in
  Debug.no_3 "subtype_ann_pair" pr1 (add_str "emap_lhs" pr2) (add_str "emap_rhs" pr2) pr_out (fun _ _ _ -> subtype_ann_pair_x elhs erhs ss imm1 imm2) (imm1,imm2) elhs erhs

(* bool denotes possible subyping *)
(* return true if imm1 <: imm2 *)	
(* M <: I <: L <: A*)
let subtype_ann_x ?strong_subtype:(ss=false)  (imm1 : CP.ann) (imm2 : CP.ann) : bool =
  let (r,op) = x_add (subtype_ann_pair ~strong_subtype:ss) imm1 imm2 in r

(* return true if imm1 <: imm2 *)	
(* M <: I <: L <: A*)
let subtype_ann caller ?strong_subtype:(ss=false) (imm1 : CP.ann) (imm2 : CP.ann) : bool = 
  let pr_imm = Cprinter.string_of_imm in
  let pr1 (imm1,imm2) =  (pr_imm imm1) ^ " <: " ^ (pr_imm imm2) ^ "?" in
  Debug.no_1_num caller "subtype_ann"  pr1 string_of_bool (fun _ -> subtype_ann_x ~strong_subtype:ss imm1 imm2) (imm1,imm2)

let subtype_ann_gen_x lhs_f rhs_f elhs erhs impl_vars evars (imm1 : CP.ann) (imm2 : CP.ann): 
  bool * (CP.formula list) * (CP.formula list) * (CP.formula list) =
  let elhs, erhs = get_emaps lhs_f rhs_f elhs erhs in
  let (f,op) = x_add (subtype_ann_pair ~emap_lhs:elhs ~emap_rhs:erhs) imm1 imm2 in
  match op with
  | None -> (f,[],[],[])
  | Some (l,r) -> 
    let to_rhs = CP.BForm ((CP.SubAnn(l,r,no_pos),None), None) in
    (* implicit instantiation of @v made stronger into an equality *)
    (* two examples in ann1.slk fail otherwise; unsound when we have *)
    (* multiple implicit being instantiated ; use explicit if needed *)
    let to_lhs(* , to_rhs_impl *)  =  lhs_rhs_rel l r in
      (* if not (!Globals.imm_weak) then  *)
      (* default_inst l r no_pos, [to_rhs] else  *)
      (* weakest_inst l r no_pos, [] in *)
    (* CP.BForm ((CP.Eq(l,r,no_pos),None), None) in (\* i need equality for inference *\) *)
    (* let to_lhs = CP.BForm ((CP.SubAnn(l,r,no_pos),None), None) in *)
    (* let lhs = c in *)
    begin
      match r with
      | CP.Var(rhs_sv,loc) -> 
        let inst, to_rhs' = x_add pick_weakest_instatiation l rhs_sv loc lhs_f rhs_f impl_vars evars in
        let to_lhs = map_opt_def to_lhs (fun x -> x) inst in
        (* implicit var annotation on rhs *)
        if CP.mem rhs_sv impl_vars then 
          (* let inst, to_rhs' = x_add pick_weakest_instatiation l rhs_sv loc lhs_f rhs_f impl_vars evars in *)
          (* let to_lhs = map_opt_def to_lhs (fun x -> x) inst in *)
          let to_rhs = map_opt_def [to_rhs] (fun x ->  x) to_rhs' in
          (f, [to_lhs], to_rhs, [])
        else if CP.mem rhs_sv evars then
          (f,[to_lhs], [to_rhs], [to_rhs])
        else (f,[],[to_rhs], [])
      | _ -> (f,[],[to_rhs], [])
    end

let subtype_ann_gen 
    ?lhs:(lhs_f = CF.mkTrue (mkTrueFlow ()) no_pos )
    ?rhs:(rhs_f = CF.mkTrue (mkTrueFlow ()) no_pos )
    ?emap_lhs:(elhs = CP.EMapSV.mkEmpty)
    ?emap_rhs:(erhs = CP.EMapSV.mkEmpty)
    impl_vars evars (imm1 : CP.ann) (imm2 : CP.ann): 
  bool * (CP.formula list) * (CP.formula list) * (CP.formula list) =
  let pr1 = !CP.print_svl in
  let pr2 = (Cprinter.string_of_imm)  in
  let pr2a = pr_list !CP.print_formula in
  let prlst =  (pr_pair (pr_list Cprinter.string_of_spec_var) (pr_list Cprinter.string_of_spec_var)) in
  let pr3 = pr_quad string_of_bool pr2a pr2a pr2a  in
  let pr_f =  Cprinter.string_of_formula in
  Debug.no_6 "subtype_ann_gen" (add_str "impl" pr1) (add_str "evars" pr1) pr2 pr2 
    (add_str "lhs_f" pr_f) (add_str "rhs_f" pr_f) pr3 
    (fun _ _ _ _ _ _ -> subtype_ann_gen_x lhs_f rhs_f elhs erhs impl_vars evars (imm1 : CP.ann) (imm2 : CP.ann) )  impl_vars evars imm1 imm2 lhs_f rhs_f

let subtype_ann_list_x 
    ?lhs:(lhs_f = CF.mkTrue (mkTrueFlow ()) no_pos )
    ?rhs:(rhs_f = CF.mkTrue (mkTrueFlow ()) no_pos )
    ?emap_lhs:(elhs = CP.EMapSV.mkEmpty)
    ?emap_rhs:(erhs = CP.EMapSV.mkEmpty)
    impl_vars evars (ann1 : CP.ann list) (ann2 : CP.ann list) : bool * (CP.formula  list) * (CP.formula  list) * (CP.formula  list) =
  let elhs0,erhs0 = get_emaps lhs_f rhs_f [] [] in
  let elhs = CP.EMapSV.merge_eset elhs0 elhs in
  let erhs = CP.EMapSV.merge_eset erhs0 erhs in
  let rec helper impl_vars evars (ann1 : CP.ann list) (ann2 : CP.ann list) =
    match (ann1, ann2) with
    | ([], [])         -> (true, [], [], [])
    | (a1::[], a2::[]) -> 
      let (r, f1, f2, f3) = x_add (subtype_ann_gen ~rhs:rhs_f ~emap_lhs:elhs ~emap_rhs:erhs) impl_vars evars a1 a2 in
      (r, f1, f2, f3)
    | (a1::t1, a2::t2) -> 
      let (r, ann_lhs_new, ann_rhs_new, ann_rhs_new_ex) = x_add (subtype_ann_gen ~rhs:rhs_f ~emap_lhs:elhs ~emap_rhs:erhs) impl_vars evars a1 a2 in
      let (res, ann_lhs, ann_rhs,  ann_rhs_ex) = helper impl_vars evars t1 t2 in
      (r&&res, ann_lhs_new@ann_lhs, ann_rhs_new@ann_rhs, ann_rhs_new_ex@ann_rhs_ex)
    (* (r&&res, mkAndOpt ann_lhs ann_lhs_new, mkAndOpt ann_rhs ann_rhs_new) *)
    | _ ->      (false, [], [], [])                        (* different lengths *)
  in helper impl_vars evars ann1 ann2

let subtype_ann_list 
    ?lhs:(lhs_f = CF.mkTrue (mkTrueFlow ()) no_pos )
    ?rhs:(rhs_f = CF.mkTrue (mkTrueFlow ()) no_pos )
    ?emap_lhs:(elhs = CP.EMapSV.mkEmpty)
    ?emap_rhs:(erhs = CP.EMapSV.mkEmpty)
    impl_vars evars (ann1 : CP.ann list) (ann2 : CP.ann list) : bool * (CP.formula  list) * (CP.formula  list) * (CP.formula  list) =
  let pr1 = !CP.print_svl in
  let pr2 = pr_list (Cprinter.string_of_imm)  in
  let pr2a = pr_list !CP.print_formula in
  let prlst =  (pr_pair (pr_list Cprinter.string_of_spec_var) (pr_list Cprinter.string_of_spec_var)) in
  let pr3 = pr_quad string_of_bool pr2a pr2a pr2a  in
  let pr_f =  Cprinter.string_of_formula in
  Debug.no_6 "subtype_ann_list" (add_str "impl" pr1) (add_str "evars" pr1) pr2 pr2
    (add_str "lhs_f" pr_f) (add_str "rhs_f" pr_f) pr3 
    (fun _ _ _ _ _ _ -> subtype_ann_list_x ~lhs:lhs_f ~rhs:rhs_f ~emap_lhs:elhs ~emap_rhs:erhs impl_vars evars (ann1 : CP.ann list) (ann2 : CP.ann list) )  impl_vars evars ann1 ann2 lhs_f rhs_f


let get_strongest_imm  (ann_lst: CP.ann list): CP.ann option = 
  let rec helper ann ann_lst = 
    match ann_lst with
    | []   -> Some ann
    | (CP.ConstAnn(Mutable)) :: t -> Some (CP.ConstAnn(Mutable))
    | x::t -> if subtype_ann 3 x ann then helper x t else helper ann t
  in
  map_list_def None (fun lst -> helper (List.hd lst) (List.tl lst)) ann_lst

let get_strongest_imm  (ann_lst: CP.ann list): CP.ann option = 
  let pr =  Cprinter.string_of_imm in
  Debug.no_1 "get_strongest_imm" (pr_list pr) (pr_opt pr) get_strongest_imm ann_lst

let get_strongest_imm  (ann_lst: CP.ann list): CP.ann = 
  map_opt_def (CP.ConstAnn(Accs)) (fun x -> x) (get_strongest_imm ann_lst)

let get_weakest_imm  ?strong_subtype:(ss = false) (ann_lst: CP.ann list)  : CP.ann = 
  let rec helper ann ann_lst = 
    match ann_lst with
    | []   -> ann
    | (CP.ConstAnn(Accs)) :: t -> (CP.ConstAnn(Accs))
    | x::t -> if subtype_ann 4 ~strong_subtype:ss ann x  then helper x t else helper ann t
  in helper (CP.ConstAnn(Mutable)) ann_lst

let rec remove_true_rd_phase (h : h_formula) : h_formula = 
  match h with
  | Phase ({h_formula_phase_rd = h1;
            h_formula_phase_rw = h2;
            h_formula_phase_pos = pos
           }) -> 
    if (h1 == HEmp) then h2
    else if (h2 == HEmp) then h1
    else h
  | Star ({h_formula_star_h1 = h1;
           h_formula_star_h2 = h2;
           h_formula_star_pos = pos
          }) -> 
    let h1r = remove_true_rd_phase h1 in
    let h2r = remove_true_rd_phase h2 in
    mkStarH h1r h2r pos
  | _ -> h


let rec split_wr_phase (h : h_formula) : (h_formula * h_formula) = 
  match h with 
  | Star ({h_formula_star_h1 = h1;
           h_formula_star_h2 = h2;
           h_formula_star_pos = pos}) -> 
    (* let () = print_string("[cris]: split star " ^ (Cprinter.string_of_h_formula h) ^ "\n") in *)
    (match h2 with
     | Phase _ -> (h1, h2)
     | Star ({h_formula_star_h1 = sh1;
              h_formula_star_h2 = sh2;
              h_formula_star_pos = spos}) ->
       split_wr_phase (CF.mkStarH (CF.mkStarH h1 sh1 pos ) sh2 pos )
     (* | Conj _ ->  *)
     (*       if(!Globals.allow_field_ann) then  *)
     (*         split_wr_phase h2 *)
     (*       else *)
     | _ -> 
       (* if ((is_lend_h_formula h1) && is_lend_h_formula h2) then *)
       (*   (, h2) *)
       (* else  *)
       (h, HEmp)
    )
  | Conj _ 
  | ConjStar _ 	      
  | ConjConj _ -> report_error no_pos ("[solver.ml] : Conjunction should not appear at this level \n")
  | Phase({h_formula_phase_rd = h1;
           h_formula_phase_rw = h2;
           h_formula_phase_pos = pos}) ->
    (HEmp, h)
  | _ -> (h, HEmp)


let rec consume_heap_h_formula (f : h_formula) : bool =  match f with
  | DataNode (h1) -> 
    if (!Globals.allow_field_ann) then (isExistsMutList h1.h_formula_data_param_imm)
    else
      ((CP.isMutable h1.h_formula_data_imm) || (CP.isImm h1.h_formula_data_imm))
  | ViewNode (h1) -> 
    if (!Globals.allow_field_ann) then (isExistsMutList (CP.annot_arg_to_imm_ann_list_no_pos h1.h_formula_view_annot_arg))
    else
      ((CP.isMutable h1.h_formula_view_imm) || (CP.isImm h1.h_formula_view_imm))
  | Conj({h_formula_conj_h1 = h1;
          h_formula_conj_h2 = h2;
          h_formula_conj_pos = pos})
  | ConjStar({h_formula_conjstar_h1 = h1;
              h_formula_conjstar_h2 = h2;
              h_formula_conjstar_pos = pos})
  | ConjConj({h_formula_conjconj_h1 = h1;
              h_formula_conjconj_h2 = h2;
              h_formula_conjconj_pos = pos})		
  | Phase({h_formula_phase_rd = h1;
           h_formula_phase_rw = h2;
           h_formula_phase_pos = pos})
  | Star({h_formula_star_h1 = h1;
          h_formula_star_h2 = h2;
          h_formula_star_pos = pos}) -> (consume_heap_h_formula h1) || (consume_heap_h_formula h2)
  | _ -> false


let rec consume_heap (f : formula) : bool =  match f with
  | Base(bf) -> consume_heap_h_formula bf.formula_base_heap
  | Exists(ef) -> consume_heap_h_formula ef.formula_exists_heap
  | Or({formula_or_f1 = f1;
        formula_or_f2 = f2;
        formula_or_pos = pos}) ->
    (consume_heap f1) || (consume_heap f2)

let rec split_phase_x (h : h_formula) : (h_formula * h_formula * h_formula ) = 
  let h = remove_true_rd_phase h in
  match h with
  | Phase ({h_formula_phase_rd = h1;
            h_formula_phase_rw = h2;
            h_formula_phase_pos = pos}) -> 
    let h3, h4 = split_wr_phase h2 in
    (h1, h3, h4)
  | Star _ ->
    let h3, h4 = split_wr_phase h in
    (HEmp, h3, h4)
  (* | Conj({h_formula_conj_h1 = h1; *)
  (*   h_formula_conj_h2 = h2}) -> *)
  (*       if !Globals.allow_field_ann then *)
  (*         let h3, h4 = split_wr_phase h2 in *)
  (*         (h1, h3, h4) *)
  (*       else 	       *)
  (*         if (consume_heap_h_formula h) then *)
  (*           (HEmp, h, HEmp) *)
  (*         else *)
  (*           (h, HEmp, HEmp) *)
  | _ ->
    if (consume_heap_h_formula h) then
      (HEmp, h, HEmp)
    else
      (h, HEmp, HEmp)

let split_phase i (h : h_formula) : (h_formula * h_formula * h_formula )= 
  let pr = Cprinter.string_of_h_formula in
  let pr2 = pr_triple pr pr pr in
  Debug.no_1_num i "split_phase" pr pr2 split_phase_x h


(* should be the opposite of consumes produces_hole x = not(consumes x); 
   depending on the LHS CP.ann, PolyCP.Ann might consume after a match, but it is considered to
   initialy create a hole. *)
let produces_hole (a: CP.ann): bool = 
  if isLend a || isAccs  a (* || isPoly a *) then true
  else false

let maybe_replace_w_empty h =
  match h with
  | CF.DataNode dn -> 
    let node_imm = dn.CF.h_formula_data_imm in
    let param_imm = dn.CF.h_formula_data_param_imm in
    let new_h =  
      if (isAccs node_imm) && (!Globals.remove_abs) then HEmp 
      else if !Globals.allow_field_ann &&  (isAccsList param_imm) && (!Globals.remove_abs) then HEmp else h
      (* match !Globals.allow_field_ann, !Globals.allow_imm with *)
      (*   | true, _     -> if (isAccsList param_imm) then HEmp else h *)
      (*   | false, true -> if (isAccs node_imm) then HEmp else h *)
      (*   | _,_         -> if (isAccs node_imm) then HEmp else h *)
    in new_h
  | CF.ViewNode vn ->  
    let node_imm = vn.CF.h_formula_view_imm in
    if (isAccs node_imm)  && (!Globals.remove_abs) then HEmp else h 
  (* let param_imm = CP.annot_arg_to_imm_ann_list vn.CF.h_formula_view_annot_arg in *)
  (* let new_h =  *)
  (*   match !Globals.allow_field_ann, !Globals.allow_imm with *)
  (*     | true, _     -> if (isAccsList param_imm) then HEmp else h *)
  (*     | false, true -> if (isAccs node_imm) then HEmp else h *)
  (*     | _,_         -> HEmp *)
  (* in new_h *)
  | _ -> h

let maybe_replace_w_empty h =
  let pr = Cprinter.string_of_h_formula in
  Debug.no_1 "maybe_replace_w_empty" pr pr maybe_replace_w_empty h 

(* let maybe_replace_w_empty h = *)
(*   match h with *)
(*     | CF.DataNode dn ->  *)
(*           let node_imm = dn.CF.h_formula_data_imm in *)
(*           let param_imm = dn.CF.h_formula_data_param_imm in *)
(*           let new_h, xpure =  *)
(*             match !Globals.allow_field_ann, !Globals.allow_imm with *)
(*               | true, _     -> if (isAccsList param_imm) then (HEmp, Some (xpure) ) else (h,None) *)
(*               | false, true -> if (isAccs node_imm) then (HEmp, Some (xpure)) else (h,None) *)
(*               | _,_         -> (h, None) *)
(*           in new_h *)
(*     | CF.ViewNode vn -> h  *)
(*           (\* let node_imm = vn.CF.h_formula_view_imm in *\) *)
(*           (\* let param_imm = CP.annot_arg_to_imm_ann_list vn.CF.h_formula_view_annot_arg in *\) *)
(*           (\* let new_h =  *\) *)
(*           (\*   match !Globals.allow_field_ann, !Globals.allow_imm with *\) *)
(*           (\*     | true, _     -> if (isAccsList param_imm) then HEmp else h *\) *)
(*           (\*     | false, true -> if (isAccs node_imm) then HEmp else h *\) *)
(*           (\*     | _,_         -> HEmp *\) *)
(*           (\* in new_h *\) *)
(*     | _ -> h *)


let ann_opt_to_ann (ann_opt: Ipure.ann option) (default_ann: Ipure.ann): Ipure.ann = 
  match ann_opt with
  | Some ann0 -> ann0
  | None      -> default_ann

let rec ann_opt_to_ann_lst (ann_opt_lst: Ipure.ann option list) (default_ann: Ipure.ann): Ipure.ann list = 
  match ann_opt_lst with
  | [] -> []
  | ann0 :: t -> (ann_opt_to_ann ann0 default_ann) :: (ann_opt_to_ann_lst t default_ann)

let iformula_ann_to_cformula_ann (iann : Ipure.ann) : CP.ann = 
  match iann with
  | Ipure.NoAnn -> if not (!Globals.allow_noann) then !defCImm else CP.NoAnn 
  | Ipure.ConstAnn(x) -> CP.ConstAnn(x)
  | Ipure.PolyAnn((id,p), l) -> 
    CP.PolyAnn(CP.SpecVar (AnnT, id, p))

let iformula_ann_to_cformula_ann_lst (iann_lst : Ipure.ann list) : CP.ann list = 
  List.map iformula_ann_to_cformula_ann iann_lst

let iformula_ann_opt_to_cformula_ann_lst (iann_lst : Ipure.ann option list) : CP.ann list = 
  let def_ann = if not (!Globals.allow_noann) || not(!Globals.allow_field_ann) then !defIImm else Ipure.NoAnn in
  List.map iformula_ann_to_cformula_ann (ann_opt_to_ann_lst iann_lst def_ann)

let iformula_ann_to_cformula_ann_node_level (iann : Ipure.ann) : CP.ann = 
  (* if we are doing ifnerence at field level, translate node level NoAnn to @M *)
  Wrapper.wrap_one_bool (Globals.allow_noann) (not(!Globals.allow_field_ann) && !Globals.allow_noann)  iformula_ann_to_cformula_ann iann

(* check lending property (@L) in classic reasoning. Hole is treated like @L *)
let rec is_classic_lending_hformula (f: h_formula) : bool =
  match f with
  | DataNode dn -> isLend dn.h_formula_data_imm
  | ViewNode vn -> isLend vn.h_formula_view_imm
  | Hole _ | FrmHole _ -> true      (* a Hole behaves like @L *)
  | Conj ({h_formula_conj_h1 = h1;
           h_formula_conj_h2 = h2})
  | ConjStar ({h_formula_conjstar_h1 = h1;
               h_formula_conjstar_h2 = h2})
  | ConjConj ({h_formula_conjconj_h1 = h1;
               h_formula_conjconj_h2 = h2})
  | Phase ({h_formula_phase_rd = h1;
            h_formula_phase_rw = h2})
  | Star ({h_formula_star_h1 = h1;
           h_formula_star_h2 = h2}) ->
    ((is_classic_lending_hformula h1) && (is_classic_lending_hformula h2))
  | _ -> false

let rec is_lend_h_formula (f : h_formula) : bool =  match f with
  | DataNode (h1) -> 
    if (isLend h1.h_formula_data_imm) then
      (* let () = print_string("true for h = " ^ (!print_h_formula f) ^ "\n\n")  in *) true
    else
      false
  | ViewNode (h1) ->
    if (isLend h1.h_formula_view_imm) then
      (* let () = print_string("true for h = " ^ (!print_h_formula f) ^ "\n\n") in *) true
    else
      false

  | Conj({h_formula_conj_h1 = h1;
          h_formula_conj_h2 = h2;
          h_formula_conj_pos = pos})
  | ConjStar({h_formula_conjstar_h1 = h1;
              h_formula_conjstar_h2 = h2;
              h_formula_conjstar_pos = pos})
  | ConjConj({h_formula_conjconj_h1 = h1;
              h_formula_conjconj_h2 = h2;
              h_formula_conjconj_pos = pos})		
  | Phase({h_formula_phase_rd = h1;
           h_formula_phase_rw = h2;
           h_formula_phase_pos = pos}) -> true
  | Star({h_formula_star_h1 = h1;
          h_formula_star_h2 = h2;
          h_formula_star_pos = pos}) -> (is_lend_h_formula h1) || (is_lend_h_formula h2)
  | Hole _ -> false
  | _ -> false

let is_lend_h_formula_debug f = 
  Debug.no_1 "is_lend_h_formula"
    (!print_h_formula)
    (string_of_bool)
    is_lend_h_formula f

let rec is_lend (f : formula) : bool =  match f with
  | Base(bf) -> is_lend_h_formula bf.formula_base_heap
  | Exists(ef) -> is_lend_h_formula ef.formula_exists_heap
  | Or({formula_or_f1 = f1;
        formula_or_f2 = f2;
        formula_or_pos = pos}) ->
    (is_lend f1) || (is_lend f2)

let is_lend_debug f = 
  Debug.no_1 "is_lend"
    (!print_formula)
    (string_of_bool)
    is_lend f

let decide_where_to_add_constr constr1 constr2  impl_vars expl_vars evars sv fsv =
  if CP.mem sv impl_vars then (constr1::[constr2], [], [], [])
  else if CP.mem sv expl_vars then
    ([constr2], [constr1], (* [r_constr] *)[], [])
  else if CP.mem sv evars then
    ([constr2], [(* constr1 *)], [(* constr1 *)], [(sv,fsv)])
  else (constr1::[constr2], [], [], [])

let mkTempRes_x ann_l ann_r  impl_vars expl_vars evars =
  match ann_r with
  | CP.PolyAnn sv ->
    let fresh_v = "ann_" ^ (fresh_name ()) in
    let fresh_sv = (CP.SpecVar(AnnT, fresh_v, Unprimed)) in
    let fresh_var = CP.Var(fresh_sv, no_pos) in
    let poly_ann = CP.mkPolyAnn fresh_sv in
    let constr1 = CP.BForm ((CP.Eq(fresh_var,(CP.mkExpAnnSymb ann_r no_pos),no_pos),None), None) in
    let constr2 = CP.BForm ((CP.SubAnn((CP.mkExpAnnSymb ann_l no_pos),fresh_var,no_pos),None), None) in
    let to_lhs, to_rhs, to_rhs_ex, subst = decide_where_to_add_constr constr1 constr2  impl_vars expl_vars evars sv fresh_sv in
    ((CP.TempRes(ann_l,poly_ann),poly_ann), [fresh_sv], ((to_lhs, to_rhs, to_rhs_ex),subst))
  | _ -> ((CP.TempRes(ann_l, ann_r), ann_r), [], (([], [], []),[]))       (* should not reach this branch *)

let mkTempRes ann_l ann_r  impl_vars expl_vars evars =
  let pr = Cprinter.string_of_imm in
  let pr1 = pr_pair pr pr in
  let pr3a = pr_list !CP.print_formula in
  let pr3 = pr_pair (pr_triple pr3a pr3a pr3a) (add_str "\n\t subst" (pr_list (pr_pair Cprinter.string_of_spec_var Cprinter.string_of_spec_var) )) in 
  let pr_out = pr_triple (add_str "(residue,cosumed) = " pr1) 
      (add_str "\n\tnew var:" (pr_list Cprinter.string_of_spec_var))
      (add_str "\n\tconstraints: " pr3) in 
  Debug.no_2 "mkTempRes"  pr pr pr_out (fun _ _ -> mkTempRes_x ann_l ann_r  impl_vars expl_vars evars ) ann_l ann_r

(* and contains_phase_debug (f : h_formula) : bool =   *)
(*   Debug.no_1 "contains_phase" *)
(*       (!print_h_formula)  *)
(*       (string_of_bool) *)
(*       (contains_phase) *)
(*       f *)
(* normalization for iformula *)
(* normalization of the heap formula *)
(* emp & emp * K == K *)
(* KR: check there is only @L *)
(* KR & KR ==> KR ; (KR ; true) *)

let rec normalize_h_formula (h : IF.h_formula) (wr_phase : bool) : IF.h_formula =
  Debug.no_1 "normalize_h_formula"
    (IP.string_of_h_formula)
    (IP.string_of_h_formula)
    (fun _ -> normalize_h_formula_x h wr_phase) h

and normalize_h_formula_x (h : IF.h_formula) (wr_phase : bool) : IF.h_formula =
  let h = normalize_h_formula_phase h wr_phase in
  (* let h = normalize_field_ann_heap_node h in *)
  h

and normalize_h_formula_phase (h : IF.h_formula) (wr_phase : bool) : IF.h_formula =
  let get_imm (h : IF.h_formula) : CP.ann = 
    let iann =
      match h with
      | IF.HeapNode2 hf -> hf.IF.h_formula_heap2_imm
      | IF.HeapNode hf -> hf.IF.h_formula_heap_imm
      | _ -> failwith ("Error in  normalize_h_formula\n")
    in
    (iformula_ann_to_cformula_ann iann)
  in
  let rec extract_inner_phase f = match f with
    | IF.Phase _ -> (IF.HEmp, f)
    | IF.Star ({IF.h_formula_star_h1 = h1;
                IF.h_formula_star_h2 = h2;
                IF.h_formula_star_pos = pos
               }) ->
      let r11, r12 = extract_inner_phase h1 in
      let r21, r22 = extract_inner_phase h2 in
      (IF.mkStar r11 r21 pos, IF.mkStar r12 r22 pos)
    | _ -> (f,IF.HEmp)
  in
  let rec aux h wr_phase = 
    match h with
    | IF.Phase({IF.h_formula_phase_rd = h1;
                IF.h_formula_phase_rw = h2;
                IF.h_formula_phase_pos = pos
               }) ->
      let rd_phase = normalize_h_formula_rd_phase h1 in
      let wr_phase = aux h2 true in 
      let res = insert_wr_phase rd_phase wr_phase in
      res
    | IF.Star({IF.h_formula_star_h1 = h1;
               IF.h_formula_star_h2 = h2;
               IF.h_formula_star_pos = pos
              }) ->
      let r1, r2 = extract_inner_phase h2 in
      if (r1 == IF.HEmp) || (r2 == IF.HEmp) then 
        IF.Star({IF.h_formula_star_h1 = h1;
                 IF.h_formula_star_h2 = aux h2 false;
                 IF.h_formula_star_pos = pos
                }) 
      else
        (* isolate the inner phase *)
        IF.Star({IF.h_formula_star_h1 = IF.mkStar h1 r1 pos;
                 IF.h_formula_star_h2 = aux r2 false;
                 IF.h_formula_star_pos = pos
                }) 
    | IF.Conj({IF.h_formula_conj_h1 = h1;
               IF.h_formula_conj_h2 = h2;
               IF.h_formula_conj_pos = pos
              }) 
    | IF.ConjStar({IF.h_formula_conjstar_h1 = h1;
                   IF.h_formula_conjstar_h2 = h2;
                   IF.h_formula_conjstar_pos = pos
                  }) 
    | IF.ConjConj({IF.h_formula_conjconj_h1 = h1;
                   IF.h_formula_conjconj_h2 = h2;
                   IF.h_formula_conjconj_pos = pos
                  })               ->
      if (wr_phase) && ((!Globals.allow_mem) || (!Globals.allow_field_ann) || (!Globals.allow_ramify)) then h else
        normalize_h_formula_rd_phase h
    | IF.HeapNode2 hf -> 
      (let annv = get_imm h in
       match annv with
       | CP.ConstAnn(Lend)  | CP.ConstAnn(Imm)  | CP.ConstAnn(Accs) -> h
       | _ ->
         begin
           (* write phase *)
           if (wr_phase) then h
           else
             IF.Phase({IF.h_formula_phase_rd = IF.HEmp;
                       IF.h_formula_phase_rw = h;
                       IF.h_formula_phase_pos = no_pos;
                      })
         end)
    | IF.HeapNode hf ->
      (let annv = get_imm h in
       match annv with
       | CP.ConstAnn(Lend) | CP.ConstAnn(Imm)  | CP.ConstAnn(Accs) -> h
       | _ ->
         begin
           (* write phase *)
           if (wr_phase) then h
           else
             IF.Phase({IF.h_formula_phase_rd = IF.HEmp;
                       IF.h_formula_phase_rw = h;
                       IF.h_formula_phase_pos = no_pos;
                      })
         end)
    | _ ->  IF.Phase { IF.h_formula_phase_rd = IF.HEmp;
                       IF.h_formula_phase_rw = h;
                       IF.h_formula_phase_pos = no_pos }
  in aux h wr_phase

and contains_phase (h : IF.h_formula) : bool = match h with
  | IF.Phase _ -> true
  | IF.Conj ({IF.h_formula_conj_h1 = h1;
              IF.h_formula_conj_h2 = h2;
              IF.h_formula_conj_pos = pos;
             }) 
  | IF.ConjStar ({IF.h_formula_conjstar_h1 = h1;
                  IF.h_formula_conjstar_h2 = h2;
                  IF.h_formula_conjstar_pos = pos;
                 })
  | IF.ConjConj ({IF.h_formula_conjconj_h1 = h1;
                  IF.h_formula_conjconj_h2 = h2;
                  IF.h_formula_conjconj_pos = pos;
                 })        
  | IF.Star ({IF.h_formula_star_h1 = h1;
              IF.h_formula_star_h2 = h2;
              IF.h_formula_star_pos = pos}) ->
    (contains_phase h1) || (contains_phase h2)
  | _ -> false

(* conj in read phase -> split into two separate read phases *)
and normalize_h_formula_rd_phase (h : IF.h_formula) : IF.h_formula = match h with
  | IF.Conj({IF.h_formula_conj_h1 = h1;
             IF.h_formula_conj_h2 = h2;
             IF.h_formula_conj_pos = pos})
  | IF.ConjStar({IF.h_formula_conjstar_h1 = h1;
                 IF.h_formula_conjstar_h2 = h2;
                 IF.h_formula_conjstar_pos = pos})
  | IF.ConjConj({IF.h_formula_conjconj_h1 = h1;
                 IF.h_formula_conjconj_h2 = h2;
                 IF.h_formula_conjconj_pos = pos})	 	 
    ->
    (* conj in read phase -> split into two separate read phases *)
    let conj1 = normalize_h_formula_rd_phase h1 in
    insert_rd_phase conj1 h2 
  | IF.Phase _ -> failwith "Shouldn't have phases inside the reading phase\n"
  | _ -> IF.Phase({IF.h_formula_phase_rd = h;
                   IF.h_formula_phase_rw = IF.HEmp;
                   IF.h_formula_phase_pos = no_pos;
                  })

(* the read phase contains only pred with the annotation @L *)
and validate_rd_phase (h : IF.h_formula) : bool = match h with
  | IF.Star({IF.h_formula_star_h1 = h1;
             IF.h_formula_star_h2 = h2;
             IF.h_formula_star_pos = pos}) 
  | IF.Conj({IF.h_formula_conj_h1 = h1;
             IF.h_formula_conj_h2 = h2;
             IF.h_formula_conj_pos = pos}) 
  | IF.ConjStar({IF.h_formula_conjstar_h1 = h1;
                 IF.h_formula_conjstar_h2 = h2;
                 IF.h_formula_conjstar_pos = pos})
  | IF.ConjConj({IF.h_formula_conjconj_h1 = h1;
                 IF.h_formula_conjconj_h2 = h2;
                 IF.h_formula_conjconj_pos = pos})	 	 
    -> (validate_rd_phase h1) && (validate_rd_phase h2)
  | IF.Phase _ -> false (* Shouldn't have phases inside the reading phase *)
  | IF.HeapNode2 hf -> (IF.isLend hf.IF.h_formula_heap2_imm) 
  | IF.HeapNode hf -> (IF.isLend hf.IF.h_formula_heap_imm)
  | _ -> true

and insert_wr_phase_x (f : IF.h_formula) (wr_phase : IF.h_formula) : IF.h_formula = 
  match f with
  | IF.Phase ({IF.h_formula_phase_rd = h1;
               IF.h_formula_phase_rw = h2;
               IF.h_formula_phase_pos = pos}) ->
    let new_h2 = 
      match h2 with
      | IF.HEmp -> wr_phase (* insert the new phase *)
      | IF.Star({IF.h_formula_star_h1 = h1_star;
                 IF.h_formula_star_h2 = h2_star;
                 IF.h_formula_star_pos = pos_star
                }) ->
        (* when insert_wr_phase is called, f represents a reading phase ->
           		       all the writing phases whould be emp *)
        if (contains_phase h2_star) then
          (* insert in the nested phase *)
          IF.Star({
              IF.h_formula_star_h1 = h1_star;
              IF.h_formula_star_h2 = insert_wr_phase h2_star wr_phase;
              IF.h_formula_star_pos = pos_star
            })
        else failwith ("[iformula.ml] : should contain phase\n")

      | _ -> IF.Star({
          IF.h_formula_star_h1 = h2;
          IF.h_formula_star_h2 = wr_phase;
          IF.h_formula_star_pos = pos
        })
    in
    (* reconstruct the phase *)
    IF.Phase({IF.h_formula_phase_rd = h1;
              IF.h_formula_phase_rw = new_h2;
              IF.h_formula_phase_pos = pos})
  | _ -> failwith ("[iformula.ml] : There should be a phase at this point\n")

and insert_wr_phase (f : IF.h_formula) (wr_phase : IF.h_formula) : IF.h_formula =
  let pr_h = Iprinter.string_of_h_formula in
  Debug.no_2 "Immutable.insert_wr_phase" pr_h pr_h pr_h insert_wr_phase_x f wr_phase

and insert_rd_phase_x (f : IF.h_formula) (rd_phase : IF.h_formula) : IF.h_formula = 
  match f with
  | IF.Phase ({IF.h_formula_phase_rd = h1;
               IF.h_formula_phase_rw = h2;
               IF.h_formula_phase_pos = pos}) ->
    let new_h2 = 
      (match h2 with
       | IF.HEmp -> 
         (* construct the new phase *)
         let new_phase = IF.Phase({IF.h_formula_phase_rd = rd_phase; 
                                   IF.h_formula_phase_rw = IF.HEmp;
                                   IF.h_formula_phase_pos = pos})
         in
         (* input the new phase *)
         IF.Star({IF.h_formula_star_h1 = IF.HEmp;
                  IF.h_formula_star_h2 = new_phase;
                  IF.h_formula_star_pos = pos})

       | IF.Conj _ 
       | IF.ConjStar _ 
       | IF.ConjConj _ -> failwith ("[cformula.ml] : Should not have conj at this point\n") (* the write phase does not contain conj *)	     
       | IF.Star ({IF.h_formula_star_h1 = h1_star;
                   IF.h_formula_star_h2 = h2_star;
                   IF.h_formula_star_pos = pos_star
                  }) ->
         let new_phase = insert_rd_phase h2_star rd_phase in
         IF.Star({IF.h_formula_star_h1 = h1_star;
                  IF.h_formula_star_h2 = new_phase;
                  IF.h_formula_star_pos = pos_star})
       | _ ->
         let new_phase = IF.Phase({IF.h_formula_phase_rd = rd_phase; 
                                   IF.h_formula_phase_rw = IF.HEmp;
                                   IF.h_formula_phase_pos = pos})
         in
         IF.Star({IF.h_formula_star_h1 = h2;
                  IF.h_formula_star_h2 = new_phase;
                  IF.h_formula_star_pos = pos})
      )
    in
    IF.Phase({
        IF.h_formula_phase_rd = h1;
        IF.h_formula_phase_rw = new_h2;
        IF.h_formula_phase_pos = pos;
      })
  | IF.Conj _
  | IF.ConjStar _
  | IF.ConjConj _ -> failwith ("[cformula.ml] : Should not have conj at this point\n")	     
  | _ -> 
    let new_phase = IF.Phase({IF.h_formula_phase_rd = rd_phase; 
                              IF.h_formula_phase_rw = IF.HEmp;
                              IF.h_formula_phase_pos = no_pos})
    in
    let new_star = IF.Star({IF.h_formula_star_h1 = IF.HEmp;
                            IF.h_formula_star_h2 = new_phase;
                            IF.h_formula_star_pos = no_pos})
    in 
    IF.Phase({
        IF.h_formula_phase_rd = f;
        IF.h_formula_phase_rw = new_star;
        IF.h_formula_phase_pos = no_pos;
      })
and insert_rd_phase (f : IF.h_formula) (wr_phase : IF.h_formula) : IF.h_formula =
  let pr_h = Iprinter.string_of_h_formula in
  Debug.no_2 "Immutable.insert_rd_phase" pr_h pr_h pr_h insert_rd_phase_x f wr_phase

(* and propagate_imm_struc_formula e (imm : CP.ann)  (imm_p: (CP.annot_arg * CP.annot_arg) list) emap = *)
(*   (\* andreeac: to check why do we have all these constructs? *\) *)
(*   let f_e_f e = None  in *)
(*   let f_f e = None in *)
(*   let f_h_f  f = Some (propagate_imm_h_formula f imm imm_p emap) in *)
(*   let f_p_t1 e = Some e in *)
(*   let f_p_t2 e = Some e in *)
(*   let f_p_t3 e = Some e in *)
(*   let f_p_t4 e = Some e in *)
(*   let f_p_t5 e = Some e in *)
(*   let f=(f_e_f,f_f,f_h_f,(f_p_t1,f_p_t2,f_p_t3,f_p_t4,f_p_t5)) in *)
(*   transform_struc_formula f e *)

and propagate_imm_struc_formula sf view_name (imm : CP.ann)  (imm_p: (CP.annot_arg * CP.annot_arg) list) =
  let res = 
    match sf with
    | EBase f   -> EBase {f with 
                          formula_struc_base = propagate_imm_formula f.formula_struc_base view_name imm imm_p }
    | EList l   -> EList  (map_l_snd (fun c->  propagate_imm_struc_formula c view_name imm imm_p) l)
    | ECase f   -> ECase {f with formula_case_branches = map_l_snd (fun c->  propagate_imm_struc_formula c view_name imm imm_p) f.formula_case_branches;}
    | EAssume f -> EAssume {f with
                            formula_assume_simpl = propagate_imm_formula f.formula_assume_simpl view_name imm imm_p;
                            formula_assume_struc = propagate_imm_struc_formula  f.formula_assume_struc view_name imm imm_p;}
    | EInfer f  -> EInfer {f with formula_inf_continuation = propagate_imm_struc_formula f.formula_inf_continuation view_name imm imm_p} 
  in res

and propagate_imm_formula_x (f : formula) (view_name: ident) (imm : CP.ann) (imm_p: (CP.annot_arg * CP.annot_arg) list): formula = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
    let rf1 = propagate_imm_formula_x f1 view_name imm imm_p in
    let rf2 = propagate_imm_formula_x f2 view_name imm imm_p in
    let resform = mkOr rf1 rf2 pos in
    resform
  | Base f1 ->
    let emap = Imm.build_eset_of_imm_formula (MCP.pure_of_mix  f1.CF.formula_base_pure) in
    let f1_heap = propagate_imm_h_formula f1.formula_base_heap view_name imm imm_p emap in
    Base({f1 with formula_base_heap = f1_heap})
  | Exists f1 ->
    let emap = Imm.build_eset_of_imm_formula (MCP.pure_of_mix  f1.CF.formula_exists_pure) in
    let f1_heap = propagate_imm_h_formula f1.formula_exists_heap view_name imm imm_p emap in
    Exists({f1 with formula_exists_heap = f1_heap})

(* !!currently works just for view_name and self data nodes!! *)
and propagate_imm_formula (f : formula) (view_name: ident) (imm : CP.ann) (imm_p: (CP.annot_arg * CP.annot_arg) list): formula =
  Debug.no_4 "propagate_imm_formula" 
    (add_str "formula" (Cprinter.string_of_formula)) 
    (add_str "view_name" pr_id) 
    (add_str "imm" (Cprinter.string_of_imm_ann)) 
    (add_str "map" (pr_list (pr_pair Cprinter.string_of_annot_arg Cprinter.string_of_annot_arg ))) 
    (Cprinter.string_of_formula) 
    propagate_imm_formula_x f view_name imm imm_p

(* andreeac TODOIMM: to replace below so that it uses emap *)
and replace_imm imm map emap=
  match imm with
  | CP.ConstAnn _ -> imm
  | CP.PolyAnn sv -> 
    begin
      let new_imm = List.fold_left (fun acc (fr,t) ->
          if ( Gen.BList.mem_eq CP.eq_ann imm [CP.annot_arg_to_imm_ann fr]) 
          then [get_weakest_imm ((CP.annot_arg_to_imm_ann fr)::[(CP.annot_arg_to_imm_ann t)]) ] 
          else acc) [] map in
      match new_imm with
      | []   -> imm
      | h::_ -> h
    end
  | _ -> imm                          (* replace temp as well *)

(* andreeac TODOIMM: propagate for fields in view defs must be modified to behave as below:
   pred p(a) = ... self<_@a>@b;
   unfold(pred(@c)@d) = ... self<_@weakest(a,b,c,d)>
*)
and propagate_imm_h_formula_x (f : h_formula) view_name (imm : CP.ann)  (imm_p: (CP.annot_arg * CP.annot_arg) list) emap : h_formula = 
  match f with
  | ViewNode f1 -> 
    if not (f1.CF.h_formula_view_name = view_name) then
      (*Cristian: this causes a bug in the folding, e.g. when trying to prove a @L view node the system ends up trying to prove @M
        			nodes, which obviously fail. I believe that all the unfolded nodes need to take the original annotation not only the root.
        			e.g. bellow must succeed: 
        					pred p1<> ==  self::node<c>* c::t1<> .
        					pred t1<> == self::node<_>.
        					checkentail c::node2<cc>@L* cc::t1<>@L  |-  c::p1<>@L.
        			It should behave similar to the datanode...
        			*)
      (*f*)
      ViewNode({f1 with h_formula_view_imm = get_weakest_imm ~strong_subtype:true (imm::[f1.CF.h_formula_view_imm]);})
    else
      let new_node_imm = imm in
      let new_args_imm = List.fold_left (fun acc (fr,t) ->
          if (Gen.BList.mem_eq CP.eq_annot_arg fr (CF.get_node_annot_args f)) then acc@[t] else acc) []  imm_p in
      (* andreeac: why was below needed? *)
      (* match f1.Cformula.h_formula_view_imm with *)
      (*   | CP.ConstAnn _ -> imm *)
      (*   | _ ->  *)
      (*         begin *)
      (*           match imm with  *)
      (*             | CP.ConstAnn _ -> imm *)
      (*             | _ -> f1.Cformula.h_formula_view_imm  *)
      (*         end *)
      ViewNode({f1 with h_formula_view_imm = get_weakest_imm ~strong_subtype:true (imm::[f1.CF.h_formula_view_imm]);(* new_node_imm; <--- andreeac: this is not correct when field-ann is enabled, to adjust *)
                        h_formula_view_annot_arg = CP.update_positions_for_annot_view_params new_args_imm f1.h_formula_view_annot_arg;
               })
  | DataNode f1 -> 
    (* if not(CP.is_self_spec_var f1.CF.h_formula_data_node) then f *)
    (* else *)
    let new_param_imm = List.map (fun a -> replace_imm a imm_p emap) f1.CF.h_formula_data_param_imm in
    DataNode({f1 with h_formula_data_imm =  get_weakest_imm ~strong_subtype:true (imm::[f1.CF.h_formula_data_imm]);
                      h_formula_data_param_imm = new_param_imm;})

  (* andreeac: why was below needed? *)
  (* DataNode({f1 with h_formula_data_imm = *)
  (* (match f1.Cformula.h_formula_data_imm with *)
  (*   | CP.ConstAnn _ -> imm *)
  (*   | _ -> begin *)
  (*       match imm with  *)
  (*         | CP.ConstAnn _ -> imm *)
  (* (\*         | _ -> f1.Cformula.h_formula_data_imm  *\) *)
  (* (\*     end); *\) *)
  (*     h_formula_data_param_imm =  *)
  (*     List.map (fun c -> if (subtype_ann 1 imm c) then c else imm) f1.Cformula.h_formula_data_param_imm}) *)
  | Star f1 ->
    let h1 = propagate_imm_h_formula f1.h_formula_star_h1 view_name imm imm_p emap in
    let h2 = propagate_imm_h_formula f1.h_formula_star_h2 view_name imm imm_p emap in
    mkStarH h1 h2 f1.h_formula_star_pos 
  | Conj f1 ->
    let h1 = propagate_imm_h_formula f1.h_formula_conj_h1 view_name imm imm_p emap in
    let h2 = propagate_imm_h_formula f1.h_formula_conj_h2 view_name imm imm_p emap in
    mkConjH h1 h2 f1.h_formula_conj_pos
  | ConjStar f1 ->
    let h1 = propagate_imm_h_formula f1.h_formula_conjstar_h1 view_name imm imm_p emap in
    let h2 = propagate_imm_h_formula f1.h_formula_conjstar_h2 view_name imm imm_p emap in
    mkConjStarH h1 h2 f1.h_formula_conjstar_pos
  | ConjConj f1 ->
    let h1 = propagate_imm_h_formula f1.h_formula_conjconj_h1 view_name imm imm_p emap in
    let h2 = propagate_imm_h_formula f1.h_formula_conjconj_h2 view_name imm imm_p emap in
    mkConjConjH h1 h2 f1.h_formula_conjconj_pos	      	      
  | Phase f1 ->
    let h1 = propagate_imm_h_formula f1.h_formula_phase_rd view_name imm imm_p emap in
    let h2 = propagate_imm_h_formula f1.h_formula_phase_rw view_name imm imm_p emap in
    mkPhaseH h1 h2 f1.h_formula_phase_pos
  | _ -> f

and propagate_imm_h_formula (f : h_formula) view_name (imm : CP.ann)  (map: (CP.annot_arg * CP.annot_arg) list) emap: h_formula = 
  Debug.no_4 "propagate_imm_h_formula" 
    (Cprinter.string_of_h_formula) 
    (add_str "view_name" pr_id) 
    (add_str "imm" (Cprinter.string_of_imm)) 
    (add_str "map" (pr_list (pr_pair Cprinter.string_of_annot_arg Cprinter.string_of_annot_arg ))) 
    (Cprinter.string_of_h_formula) 
    (fun _ _ _ _ -> propagate_imm_h_formula_x f view_name imm map emap) f view_name imm map

and mkAndOpt (old_f: CP.formula option) (to_add: CP.formula option): CP.formula option =
  match (old_f, to_add) with
  | (None, None)       -> None
  | (Some f, None)
  | (None, Some f)     -> Some f 
  | (Some f1, Some f2) -> Some (CP.mkAnd f1 f2 no_pos)

(* and mkAnd (old_f: CP.formula list) (to_add: CP.formula list): CP.formula option = *)
(*   match (old_f, to_add) with *)
(*     | ([], [])       -> None *)
(*     | (f::[], []) *)
(*     | ([], f::[])     -> Some f  *)
(*     | (f1::[], f2::[]) -> Some (CP.mkAnd f1 f2 no_pos) *)

and param_ann_equals_node_ann (ann_lst : CP.ann list) (node_ann: CP.ann): bool =
  List.fold_left (fun res x -> res && (CP.eq_ann x node_ann)) true ann_lst

(* residue * consumed *)
and subtract_ann_x (ann_l: CP.ann) (ann_r: CP.ann)  impl_vars expl_vars evars norm (* : ann *) =
  match ann_r with
  | CP.ConstAnn(Mutable)
  | CP.NoAnn
  | CP.ConstAnn(Imm)     -> ((CP.ConstAnn(Accs), ann_r), [],(([],[],[]),[]))
  | CP.ConstAnn(Lend)    -> ((CP.TempAnn(ann_l), CP.ConstAnn(Accs)), [],(([],[],[]),[]))
  | CP.TempAnn _ 
  | CP.TempRes _  
  | CP.ConstAnn(Accs)    -> ((ann_l, CP.ConstAnn(Accs)), [],(([],[],[]),[]))
  | CP.PolyAnn(_)        ->
    match ann_l with
    | CP.ConstAnn(Mutable)
    | CP.NoAnn
    | CP.ConstAnn(Imm)
    | CP.PolyAnn(_) -> 
      if norm then 
        let (res_ann,cons_ann), fv, ((to_lhs, to_rhs, to_rhs_ex),subst) = mkTempRes ann_l ann_r  impl_vars expl_vars evars in
        ((res_ann, cons_ann),fv, ((to_lhs, to_rhs, to_rhs_ex),subst))
      else  ((CP.TempRes(ann_l, ann_r), ann_r), [], (([],[],[]),[]))
    (* TempRes(ann_l, ann_r) *)
    (* better use explicit patterns below .. *)
    | _          -> ((ann_l, CP.ConstAnn(Accs)), [],(([],[],[]),[]))

and subtract_ann (ann_l: CP.ann) (ann_r: CP.ann)  impl_vars expl_vars evars norm (* : ann *) =
  let  pr_imm = Cprinter.string_of_imm in
  let pr1 = pr_pair (add_str "left" pr_imm) (add_str "right" pr_imm) in
  let pr_sv_list =  Cprinter.string_of_spec_var_list in
  let pr2 = pr_triple (add_str "impl" pr_sv_list) (add_str "expl" pr_sv_list) (add_str "evars" pr_sv_list) in
  let pr_pure_list = pr_list Cprinter.string_of_pure_formula in
  let pr_out = pr_triple pr1 pr_sv_list (pr_pair (pr_triple pr_pure_list pr_pure_list pr_pure_list) (pr_list (pr_pair Cprinter.string_of_spec_var Cprinter.string_of_spec_var))) in
  Debug.no_3 "subtract_ann" pr1 pr2 (add_str "norm" string_of_bool) pr_out (fun _ _ _ -> subtract_ann_x (ann_l: CP.ann) (ann_r: CP.ann)  impl_vars expl_vars evars norm) (ann_l,ann_r) (impl_vars, expl_vars,evars) norm

(* during matching - for residue*)
and replace_list_ann_x (ann_lst_l: CP.ann list) (ann_lst_r: CP.ann list) es =
  let impl_vars = es.es_gen_impl_vars in
  let expl_vars = es.es_gen_expl_vars in
  let evars     = es.es_evars in
  let n_ann_lst, niv, constr = List.fold_left (fun ((res_ann_acc,cons_ann_acc), n_iv, ((to_lhsl, to_rhsl, to_rhs_exl),substl)) (ann_l,ann_r) -> 
      let (resid_ann, cons_ann), niv, ((to_lhs, to_rhs, to_rhs_ex),subst) = subtract_ann ann_l ann_r impl_vars expl_vars evars (* true *)false in 
      ((res_ann_acc@[resid_ann], cons_ann_acc@[cons_ann]), niv@n_iv, ((to_lhs@to_lhsl, to_rhs@to_rhsl, to_rhs_ex@to_rhs_exl),subst@substl))
    ) (([],[]), [], (([],[],[]),[])) (List.combine ann_lst_l ann_lst_r ) in
  n_ann_lst, niv, constr 

and replace_list_ann i (ann_lst_l: CP.ann list) (ann_lst_r: CP.ann list) es =
  let pr lst = "[" ^ (List.fold_left (fun y x-> (Cprinter.string_of_imm x) ^ ", " ^ y) "" lst) ^ "]; " in
  let pr_p =  pr_pair pr pr in 
  let pr_out = pr_triple pr_p pr_none pr_none in
  Debug.no_2_num i "replace_list_ann" pr pr pr_out (fun _ _-> replace_list_ann_x ann_lst_l ann_lst_r es) ann_lst_l ann_lst_r

and replace_list_ann_mem (ann_lst_l: CP.ann list) (ann_lst_r: CP.ann list) impl_vars expl_vars evars =
  let n_ann_lst, niv, constr = List.fold_left (fun ((res_ann_acc,cons_ann_acc), n_iv, (to_lhsl, to_rhsl, to_rhs_exl)) (ann_l,ann_r) -> 
      let (resid_ann, cons_ann), niv, ((to_lhs, to_rhs, to_rhs_ex),_) = subtract_ann ann_l ann_r impl_vars expl_vars evars (* true  *)false in 
      ((res_ann_acc@[resid_ann], cons_ann_acc@[cons_ann]), niv@n_iv, (to_lhs@to_lhsl, to_rhs@to_rhsl, to_rhs_ex@to_rhs_exl))
    ) (([],[]), [], ([],[],[])) (List.combine ann_lst_l ann_lst_r ) in
  n_ann_lst, niv, constr 

and consumed_ann (ann_l: CP.ann) (ann_r: CP.ann): CP.ann = 
  match ann_r with
  | CP.ConstAnn(Accs)    
  | CP.TempAnn _ | CP.NoAnn
  | CP.TempRes _
  | CP.ConstAnn(Lend)    -> (CP.ConstAnn(Accs)) 
  | CP.PolyAnn(_)        (* -> *)
  (* match ann_l with *)
  (*     (\*must check ann_l (probl cases: @M,@I,@v), decide between returning Accs or TempCons*\) *)
  (*   | CP.ConstAnn(Mutable) *)
  (*   | CP.ConstAnn(Imm) *)
  (*   | CP.PolyAnn() -> TempCons(ann_l) *)
  (*   | _         -> CP.ConstAnn(Accs) *)
  | CP.ConstAnn(Mutable) 
  | CP.ConstAnn(Imm)     -> ann_r


(* during matching *)
and consumed_list_ann_x (ann_lst_l: CP.ann list) (ann_lst_r: CP.ann list): CP.ann list =
  match (ann_lst_l, ann_lst_r) with
  | ([], []) -> []
  | (ann_l :: tl, ann_r :: tr ) -> (consumed_ann ann_l ann_r):: (consumed_list_ann_x tl tr)
  | (_, _) -> ann_lst_l (* report_error no_pos ("[immutable.ml] : nodes should have same no. of fields \n") *)

and consumed_list_ann (ann_lst_l: CP.ann list) (ann_lst_r: CP.ann list): CP.ann list =
  let pr lst = "[" ^ (List.fold_left (fun y x-> (Cprinter.string_of_imm x) ^ ", " ^ y) "" lst) ^ "]; " in
  Debug.no_2 "consumed_list_ann" pr pr pr (fun _ _-> consumed_list_ann_x ann_lst_l ann_lst_r) ann_lst_l ann_lst_r


and merge_ann_formula_list_x(conjs: CP.formula list): heap_ann option = 
  (* form a list with the constants on the lhs of "var=AConst.." formulae *)
  let rec helper conjs =
    match conjs with
    | []    -> []
    | x::xs -> 
      let acst = CP.get_aconst x in
      match acst with
      | Some ann -> ann::(helper xs)
      | None     -> helper xs
  in
  let anns = helper conjs in
  let ann = 
    (* merge the set of annotations anns as follows: 
       if all the annotations in the set are the same, eg. equal to ann0, 
       return Some ann0, otherwise return None *)
    match anns with
    | []     -> None
    | x::xs  -> List.fold_left (fun a1_opt a2 -> 
        match a1_opt with
        | Some a1 -> if not(CP.is_diff (CP.AConst(a1,no_pos)) (CP.AConst(a2,no_pos))) then Some a1 else None
        | None    -> None ) (Some x) xs
  in
  ann

and merge_ann_formula_list(conjs: CP.formula list): heap_ann option = 
  let pr1 = pr_list Cprinter.string_of_pure_formula in
  let pr_out = pr_opt string_of_heap_ann in
  Debug.no_1 "merge_ann_formula_list" pr1 pr_out merge_ann_formula_list_x conjs

and collect_ann_info_from_formula_x (a: CP.ann) (conjs: CP.formula list) (pure: CP.formula): heap_ann option =
  let lst = 
    match a with
    | CP.PolyAnn sv -> CP.find_closure_pure_formula sv pure 
    | _ -> []
  in
  x_tinfo_hp (add_str "conjs bef:" (pr_list Cprinter.string_of_pure_formula)) conjs no_pos;
  (* keep only Eq formulae of form var = AConst, where var is in lst *)
  let conjs = List.filter (fun f -> 
      (CP.is_eq_with_aconst f) && not(CP.disjoint (CP.fv f) lst )) conjs in
  x_tinfo_hp (add_str "conjs:" (pr_list Cprinter.string_of_pure_formula)) conjs no_pos;
  let ann = merge_ann_formula_list conjs in
  ann

and collect_ann_info_from_formula (a: CP.ann) (conjs: CP.formula list) (pure: CP.formula): heap_ann option =

  Debug.no_3 "collect_ann_info_from_formula" 
    Cprinter.string_of_imm 
    (pr_list Cprinter.string_of_pure_formula)
    Cprinter.string_of_pure_formula
    (pr_opt string_of_heap_ann)
    collect_ann_info_from_formula_x a conjs pure 

and remaining_ann_x (annl: CP.ann) emap: CP.ann=
  let elem_const = (CP.mkAnnSVar Mutable)::(CP.mkAnnSVar Imm)::(CP.mkAnnSVar Lend)::[(CP.mkAnnSVar Accs)] in
  let anns =  (CP.ConstAnn(Mutable))::(CP.ConstAnn(Imm))::(CP.ConstAnn(Lend))::[(CP.ConstAnn(Accs))] in
  let anns = List.combine elem_const anns in
  let getAnn aconst = snd (List.find (fun (a,_) -> CP.eq_spec_var a aconst)  anns) in    
  let normalize_imm ann = 
    match (CP.imm_to_spec_var_opt ann) with
    | Some v -> 
      begin
        let elst  =  CP.EMapSV.find_equiv_all v emap in
        let const =  Gen.BList.intersect_eq CP.eq_spec_var elst elem_const in
        match const with
        | []    -> ann
        | h::[] -> getAnn h 
        | _     -> failwith "an imm ann cannot be assigned to 2 different values (imm)"
      end
    | _ -> ann                        (* should never reach this branch *)
  in
  let res = match annl with
    (* | CP.TempAnn ann -> normalize_imm ann *)
    | CP.TempRes (ann_l,ann_r) -> (* ann_l *)
      let ann_l = normalize_imm ann_l in
      let ann_r = normalize_imm ann_r in
      let (res,_),_,_ = subtract_ann ann_l ann_r [] [] [] false in
      res
    | CP.PolyAnn ann -> normalize_imm annl 
    | _ -> annl in
  res

and remaining_ann (ann_l: CP.ann) emap(* : ann  *)=
  let pr = Cprinter.string_of_imm in
  let pr_out  = pr_triple  pr pr_none pr_none in
  Debug.no_1 "remaining_ann" pr pr (fun _-> remaining_ann_x ann_l emap) ann_l

(* restore ann for residue * consumed *)
and restore_tmp_res_ann_x (annl: CP.ann) (pure0: MCP.mix_formula): CP.ann =
  let pure = MCP.pure_of_mix pure0 in
  let emap = Imm.build_eset_of_imm_formula pure in 
  let res = remaining_ann annl emap  in
  res 

and restore_tmp_res_ann (annl: CP.ann)(pure0: MCP.mix_formula): CP.ann =
  let pr = Cprinter.string_of_imm in
  Debug.no_2 "restore_tmp_res_ann" pr  Cprinter.string_of_mix_formula pr (fun _ _ -> restore_tmp_res_ann_x annl pure0 ) annl  pure0 

and restore_tmp_ann_x (ann_lst: CP.ann list) (pure0: MCP.mix_formula): CP.ann list =
  match ann_lst with
  | [] -> []
  | ann_l::tl ->
    let ann_l = restore_tmp_res_ann ann_l pure0 in
    ann_l :: (restore_tmp_ann_x tl pure0)

and restore_tmp_ann (ann_lst: CP.ann list) (pure0: MCP.mix_formula): CP.ann list =
  let pr = pr_list Cprinter.string_of_imm in 
  Debug.no_2 "restore_tmp_ann" pr  (Cprinter.string_of_mix_formula) pr restore_tmp_ann_x ann_lst pure0

(* and update_field_ann (f : h_formula) (pimm1 : ann list) (pimm : ann list)  impl_vars evars: h_formula =  *)
(*   let pr lst = "[" ^ (List.fold_left (fun y x-> (Cprinter.string_of_imm x) ^ ", " ^ y) "" lst) ^ "]; " in *)
(*   Debug.no_3 "update_field_ann" (Cprinter.string_of_h_formula) pr pr  (Cprinter.string_of_h_formula) (fun _ _ _-> update_field_ann_x f pimm1 pimm impl_vars evars) f pimm1 pimm *)

(* and update_field_ann_x (f : h_formula) (pimm1 : ann list) (pimm : ann list) impl_vars evars: h_formula =  *)
(*   let new_field_ann_lnode = replace_list_ann pimm1 pimm impl_vars evars in *)
(*   (\* asankhs: If node has all field annotations as @A make it HEmp *\) *)
(*   if (isAccsList new_field_ann_lnode) then HEmp else (\*andreea temporarily allow nodes only with @A fields*\) *)
(*   let updated_f = match f with  *)
(*     | DataNode d -> DataNode ( {d with h_formula_data_param_imm = new_field_ann_lnode} ) *)
(*     | _          -> report_error no_pos ("[context.ml] : only data node should allow field annotations \n") *)
(*   in *)
(*   updated_f *)

(* and update_ann (f : h_formula) (ann_l: ann) (ann_r: ann) impl_vars evars: h_formula =  *)
(*   let pr = Cprinter.string_of_imm in *)
(*   Debug.no_3 "update_ann" (Cprinter.string_of_h_formula) pr pr  (Cprinter.string_of_h_formula) (fun _ _ _-> update_ann_x f ann_l ann_r impl_vars evars) f ann_l ann_r *)

(* and update_ann_x (f : h_formula) (ann_l: ann) (ann_r: ann) impl_vars evars : h_formula =  *)
(*   let new_ann_lnode = remaining_ann ann_l ann_r impl_vars evars in *)
(*   (\* asankhs: If node has all field annotations as @A make it HEmp *\) *)
(*   if (isAccs new_ann_lnode) then HEmp else  *)
(*   let updated_f = match f with  *)
(*     | DataNode d -> DataNode ( {d with h_formula_data_imm = new_ann_lnode} ) *)
(*     | ViewNode v -> ViewNode ( {v with h_formula_view_imm = new_ann_lnode} ) *)
(*     | _          -> report_error no_pos ("[context.ml] : only data node or view node should allow annotations \n") *)
(*   in *)
(*   updated_f *)

(* utilities for handling lhs heap state continuation *)
and push_cont_ctx (cont : h_formula) (ctx : Cformula.context) : Cformula.context =
  match ctx with
  | Ctx(es) -> Ctx(push_cont_es cont es)
  | OCtx(c1, c2) ->
    OCtx(push_cont_ctx cont c1, push_cont_ctx cont c2)

and push_cont_es (cont : h_formula) (es : entail_state) : entail_state =  
  {  es with
     es_cont = cont::es.es_cont;
  }

and pop_cont_es (es : entail_state) : (h_formula * entail_state) =  
  let cont = es.es_cont in
  let crt_cont, cont =
    match cont with
    | h::r -> (h, r)
    | [] -> (HEmp, [])
  in
  (crt_cont, 
   {  es with
      es_cont = cont;
   })

(* utilities for handling lhs holes *)
(* push *)
and push_crt_holes_list_ctx (ctx : list_context) (holes : (h_formula * int) list) : list_context = 
  let pr1 = Cprinter.string_of_list_context in
  let pr2 = pr_no (* pr_list (pr_pair string_of_h_formula string_of_int ) *) in
  Debug.no_2 "push_crt_holes_list_ctx" pr1 pr2 pr1 (fun _ _-> push_crt_holes_list_ctx_x ctx holes) ctx holes

and push_crt_holes_list_ctx_x (ctx : list_context) (holes : (h_formula * int) list) : list_context = 
  match ctx with
  | FailCtx _ -> ctx
  | SuccCtx(cl) ->
    SuccCtx(List.map (fun x -> push_crt_holes_ctx x holes) cl)

and push_crt_holes_ctx (ctx : context) (holes : (h_formula * int) list) : context = 
  match ctx with
  | Ctx(es) -> Ctx(push_crt_holes_es es holes)
  | OCtx(c1, c2) ->
    let nc1 = push_crt_holes_ctx c1 holes in
    let nc2 = push_crt_holes_ctx c2 holes in
    OCtx(nc1, nc2)

and push_crt_holes_es (es : Cformula.entail_state) (holes : (h_formula * int) list) : Cformula.entail_state =
  {
    es with
    es_crt_holes = holes @ es.es_crt_holes; 
  }

and push_holes (es : Cformula.entail_state) : Cformula.entail_state = 
  {  es with
     es_hole_stk   = es.es_crt_holes::es.es_hole_stk;
     es_crt_holes = [];
  }

(* pop *)

and pop_holes_es (es : Cformula.entail_state) : Cformula.entail_state = 
  match es.es_hole_stk with
  | [] -> es
  | c2::stk -> {  es with
                  es_hole_stk = stk;
                  es_crt_holes = es.es_crt_holes @ c2;
               }

(* substitute *)
and subs_crt_holes_list_ctx (ctx : list_context) : list_context = 
  match ctx with
  | FailCtx _ -> ctx
  | SuccCtx(cl) ->
    SuccCtx(List.map (subs_crt_holes_ctx 12 ) cl)

and subs_crt_holes_list_failesc_ctx ctx = 
  transform_list_failesc_context (idf, idf, (fun es -> Ctx (subs_holes_es es))) ctx

and subs_crt_holes_ctx_x (ctx : context) : context = 
  match ctx with
  | Ctx(es) -> Ctx(subs_holes_es es)
  | OCtx(c1, c2) ->
    let nc1 = subs_crt_holes_ctx_x c1 in
    let nc2 = subs_crt_holes_ctx_x c2 in
    OCtx(nc1, nc2)

and subs_crt_holes_ctx i (ctx : context) : context = 
  let pr = Cprinter.string_of_context in
  Debug.no_1_num i "subs_crt_holes_ctx" pr pr subs_crt_holes_ctx_x ctx

and subs_holes_es (es : Cformula.entail_state) : Cformula.entail_state = 
  (* subs away current hole list *)
  {  es with
     es_crt_holes   = [];
     es_formula = apply_subs es.es_crt_holes es.es_formula;
  }

and apply_subs (crt_holes : (h_formula * int) list) (f : formula) : formula =
  match f with
  | Base(bf) ->
    Base{bf with formula_base_heap = apply_subs_h_formula crt_holes bf.formula_base_heap;}
  | Exists(ef) ->
    Exists{ef with formula_exists_heap = apply_subs_h_formula crt_holes ef.formula_exists_heap;}
  | Or({formula_or_f1 = f1;
        formula_or_f2 = f2;
        formula_or_pos = pos}) ->
    let sf1 = apply_subs crt_holes f1 in
    let sf2 = apply_subs crt_holes f2 in
    mkOr sf1  sf2 pos

and apply_subs_h_formula crt_holes (h : h_formula) : h_formula = 
  let rec helper (i : int) crt_holes : h_formula = 
    (match crt_holes with
     | (h1, i1) :: rest -> 
       if i==i1 then h1
       else helper i rest
     | [] -> Hole(i))
  in
  match h with
  | Hole(i) -> helper i crt_holes
  | Star({h_formula_star_h1 = h1;
          h_formula_star_h2 = h2;
          h_formula_star_pos = pos}) ->
    let nh1 = apply_subs_h_formula crt_holes h1 in
    let nh2 = apply_subs_h_formula crt_holes h2 in
    Star({h_formula_star_h1 = nh1;
          h_formula_star_h2 = nh2;
          h_formula_star_pos = pos})
  | Conj({h_formula_conj_h1 = h1;
          h_formula_conj_h2 = h2;
          h_formula_conj_pos = pos}) ->
    let nh1 = apply_subs_h_formula crt_holes h1 in
    let nh2 = apply_subs_h_formula crt_holes h2 in
    Conj({h_formula_conj_h1 = nh1;
          h_formula_conj_h2 = nh2;
          h_formula_conj_pos = pos})
  | ConjStar({h_formula_conjstar_h1 = h1;
              h_formula_conjstar_h2 = h2;
              h_formula_conjstar_pos = pos}) ->
    let nh1 = apply_subs_h_formula crt_holes h1 in
    let nh2 = apply_subs_h_formula crt_holes h2 in
    ConjStar({h_formula_conjstar_h1 = nh1;
              h_formula_conjstar_h2 = nh2;
              h_formula_conjstar_pos = pos})
  | ConjConj({h_formula_conjconj_h1 = h1;
              h_formula_conjconj_h2 = h2;
              h_formula_conjconj_pos = pos}) ->
    let nh1 = apply_subs_h_formula crt_holes h1 in
    let nh2 = apply_subs_h_formula crt_holes h2 in
    ConjConj({h_formula_conjconj_h1 = nh1;
              h_formula_conjconj_h2 = nh2;
              h_formula_conjconj_pos = pos})	      	      
  | Phase({h_formula_phase_rd = h1;
           h_formula_phase_rw = h2;
           h_formula_phase_pos = pos}) ->
    let nh1 = apply_subs_h_formula crt_holes h1 in
    let nh2 = apply_subs_h_formula crt_holes h2 in
    Phase({h_formula_phase_rd = nh1;
           h_formula_phase_rw = nh2;
           h_formula_phase_pos = pos})
  | _ -> h

and get_imm (f : h_formula) : CP.ann =  match f with
  | DataNode (h1) -> h1.h_formula_data_imm
  | ViewNode (h1) -> h1.h_formula_view_imm
  | _ -> CP.ConstAnn(Mutable) (* we shouldn't get here *)


(* muatble or immutable annotations on the RHS consume the match on the LHS  *)
and consumes (a: CP.ann): bool = 
  if isMutable a || isImm a then true
  else false

and compute_ann_list all_fields (diff_fields : ident list) (default_ann : CP.ann) : CP.ann list =
  let pr1 ls =
    let helper i = match i with
      | ((_,h), _, _, _) -> h
    in
    List.fold_left (fun res id -> res ^ ", " ^ (helper id)) "" ls in
  let pr2 ls = List.fold_left (fun res id -> res ^ ", " ^ id ) "" ls in
  let pr_out ls = List.fold_left (fun res id ->  res ^ ", " ^ (Cprinter.string_of_imm id) ) "" ls in
  Debug.no_3 "compute_ann_list" pr1 pr2 (Cprinter.string_of_imm) pr_out
    (fun _ _ _ -> compute_ann_list_x all_fields diff_fields default_ann ) all_fields diff_fields default_ann

and compute_ann_list_x all_fields (diff_fields : ident list) (default_ann : CP.ann) : CP.ann list =
  match all_fields with
  | ((_,h),_,_,_) :: r ->
    if (List.mem h diff_fields) then default_ann :: (compute_ann_list_x r diff_fields default_ann)
    else let ann = if(!Globals.allow_field_ann) then (CP.ConstAnn(Accs)) else default_ann in ann:: (compute_ann_list_x r diff_fields default_ann)
  | [] -> []
;; 

(* ========= functions for transforming imm ============ *)

(* @a ---> f @a *)
let imm_transform_h_formula_helper f h =
  let f_unit, f_list = f in
  match h with
  | CF.DataNode dn -> 
    let h = CF.DataNode {dn with CF.h_formula_data_param_imm = f_list dn.CF.h_formula_data_param_imm;
                                 CF.h_formula_data_imm = f_unit dn.CF.h_formula_data_imm; } in
    (* let h = maybe_replace_w_empty h in *)
    Some h
  | ViewNode vn -> 
    let h = CF.ViewNode {vn with h_formula_view_imm = f_unit vn.CF.h_formula_view_imm;
                                 h_formula_view_annot_arg = CP.update_imm_args_in_view f_list vn.CF.h_formula_view_annot_arg} in
    (* let h = maybe_replace_w_empty h in *)
    Some h
  | _ -> None

(* @a ---> f @a *)
let imm_transform_h_formula f h =
  let fnct h = imm_transform_h_formula_helper f h in
  let h = CF.transform_h_formula fnct h in
  h

(* @a ---> f @a *)
let imm_transform_h_formula f h =
  let pr =  Cprinter.string_of_h_formula in 
  Debug.no_1 "imm_transform_h_formula" pr pr (imm_transform_h_formula f) h

(* @a ---> f @a *)
let imm_transform_struc_formula fncs sf =
  CF.transform_struc_formula fncs sf

(* @a ---> f @a *)
let imm_transform_formula fncs f =
  CF.transform_formula fncs f

(* @a ---> f @a *)
let imm_transform_entail_state fncs es =
  {es with 
   CF.es_formula = CF.transform_formula fncs es.CF.es_formula;
  }

(* @a ---> f @a *)
let imm_transform_entail_state fncs es =
  let pr = Cprinter.string_of_entail_state in
  Debug.no_1 "imm_transform_entail_state" pr pr (imm_transform_entail_state fncs) es

(* @a ---> f @a *)
let imm_transform_context fncs ctx = 
  let fnc es = Ctx (imm_transform_entail_state fncs es) in
  let ctx = CF.transform_context fnc ctx in
  ctx

(* @a ---> f @a *)
let imm_transform_list_context fncs ctx = 
  let scc_f es = Ctx (imm_transform_entail_state fncs es) in
  let fnc = (scc_f, fun x -> x) in
  let ctx = CF.transform_list_context fnc ctx in
  ctx

(* ========= END functions for transforming imm ============ *)

(* ========= restore temp ann functions ============ *)

let restore_tmp_res_unit p ann = restore_tmp_res_ann ann p

let restore_tmp_res_list p ann = restore_tmp_ann ann p

let f_restore_tmp_ann p = (restore_tmp_res_unit p, restore_tmp_res_list p)

let imm_transform_formula_tmp f formula =
  let rec helper f formula =
    match formula with
    | CF.Base(bf)   ->  CF.Base {bf with CF.formula_base_heap = imm_transform_h_formula (f bf.CF.formula_base_pure) bf.CF.formula_base_heap ;}
    | CF.Exists(ef) -> CF.Exists {ef with CF.formula_exists_heap = imm_transform_h_formula (f ef.CF.formula_exists_pure) ef.CF.formula_exists_heap;}
    | CF.Or(orf)    -> CF.Or {orf with CF.formula_or_f1 = helper f orf.CF.formula_or_f1; 
                                       CF.formula_or_f2 = helper f orf.CF.formula_or_f2;}
  in Some (helper f formula)

let f1 = imm_transform_formula_tmp f_restore_tmp_ann 

let fncs = (nonef, f1, nonef, (nonef,nonef,nonef,nonef,nonef))

let restore_tmp_ann_h_formula h p = imm_transform_h_formula (f_restore_tmp_ann p) h

let restore_tmp_ann_formula f = CF.transform_formula fncs f

let restore_tmp_ann_es es = imm_transform_entail_state fncs es

let restore_tmp_ann_list_ctx ctx = imm_transform_list_context fncs ctx

let restore_tmp_ann_ctx ctx = imm_transform_context fncs ctx

let restore_tmp_ann_formula f = 
  let pr = Cprinter.string_of_formula in 
  Debug.no_1 "restore_tmp_ann_formula" pr pr restore_tmp_ann_formula f

let restore_tmp_ann_ctx ctx = 
  let pr = Cprinter.string_of_context_short in 
  Debug.no_1 "restore_tmp_ann_ctx" pr pr restore_tmp_ann_ctx ctx 

(* ========= END restore temp ann functions ============*)

(* ========= restore @L functions ========== *)

(* should we allow nested TempAnn? if so, then we should recursively restore @L *)
let restore_lend a = 
  match a with
  | CP.TempAnn ann -> ann
  | _ -> a

let restore_lend_list lst = List.map restore_lend lst

let f_restore_lend = (restore_lend, restore_lend_list)

let f2 = imm_transform_h_formula_helper f_restore_lend

let fncs = (nonef, nonef, f2, (nonef,nonef,nonef,nonef,nonef))

let restore_lend_h_formula h = imm_transform_h_formula f_restore_lend h

let restore_lend_formula f = imm_transform_formula fncs f

let restore_lend_es es = imm_transform_entail_state fncs es

let restore_lend_ctx ctx = imm_transform_context fncs ctx

let restore_lend_list_ctx ctx = imm_transform_list_context fncs ctx

let restore_lend_h_formula h =
  let pr = Cprinter.string_of_h_formula in 
  Debug.no_1 "restore_lend_h_formula" pr pr restore_lend_h_formula h

let restore_lend_es es =
  let pr = Cprinter.string_of_entail_state_short in 
  Debug.no_1 "restore_lend_es" pr pr restore_lend_es es

let restore_lend_list_ctx ctx =
  let pr = Cprinter.string_of_list_context_short in 
  Debug.no_1 "restore_lend_list_ctx" pr pr restore_lend_list_ctx ctx

(* ========= END restore @L functions ========== *)

let rec normalize_h_formula_dn auxf (h : CF.h_formula) : CF.h_formula * (CP.formula list) * ((Globals.ident * VarGen.primed) list) = 
  match h with
  | CF.Star({CF.h_formula_star_h1 = h1;
             CF.h_formula_star_h2 = h2;
             CF.h_formula_star_pos = pos}) ->
    let nh1, lc1, nv1 = normalize_h_formula_dn auxf h1 in
    let nh2, lc2, nv2 = normalize_h_formula_dn auxf h2 in
    let h = CF.Star({CF.h_formula_star_h1 = nh1;
                     CF.h_formula_star_h2 = nh2;
                     CF.h_formula_star_pos = pos}) in
    (h, lc1@lc2, nv1@nv2)
  | CF.Conj({CF.h_formula_conj_h1 = h1;
             CF.h_formula_conj_h2 = h2;
             CF.h_formula_conj_pos = pos}) ->
    let nh1, lc1, nv1 = normalize_h_formula_dn auxf h1 in
    let nh2, lc2, nv2 = normalize_h_formula_dn auxf h2 in
    let h = CF.Conj({CF.h_formula_conj_h1 = nh1;
                     CF.h_formula_conj_h2 = nh2;
                     CF.h_formula_conj_pos = pos}) in
    (h, lc1@lc2, nv1@nv2)
  | CF.ConjStar({CF.h_formula_conjstar_h1 = h1;
                 CF.h_formula_conjstar_h2 = h2;
                 CF.h_formula_conjstar_pos = pos}) ->
    let nh1, lc1, nv1 = normalize_h_formula_dn auxf h1 in
    let nh2, lc2, nv2 = normalize_h_formula_dn auxf h2 in
    let h = CF.ConjStar({CF.h_formula_conjstar_h1 = nh1;
                         CF.h_formula_conjstar_h2 = nh2;
                         CF.h_formula_conjstar_pos = pos}) in
    (h, lc1@lc2, nv1@nv2)
  | CF.ConjConj({CF.h_formula_conjconj_h1 = h1;
                 CF.h_formula_conjconj_h2 = h2;
                 CF.h_formula_conjconj_pos = pos}) ->
    let nh1, lc1, nv1 = normalize_h_formula_dn auxf h1 in
    let nh2, lc2, nv2 = normalize_h_formula_dn auxf h2 in
    let h = CF.ConjConj({CF.h_formula_conjconj_h1 = nh1;
                         CF.h_formula_conjconj_h2 = nh2;
                         CF.h_formula_conjconj_pos = pos}) in
    (h, lc1@lc2, nv1@nv2)
  | CF.Phase({CF.h_formula_phase_rd = h1;
              CF.h_formula_phase_rw = h2;
              CF.h_formula_phase_pos = pos}) ->
    let nh1,lc1,nv1 = normalize_h_formula_dn auxf h1 in
    let nh2,lc2,nv2 = normalize_h_formula_dn auxf h2 in
    let h = CF.Phase({CF.h_formula_phase_rd = nh1;
                      CF.h_formula_phase_rw = nh2;
                      CF.h_formula_phase_pos = pos}) in 
    (h, lc1@lc2, nv1@nv2)
  | CF.DataNode dn -> auxf h 
  | CF.ViewNode vn -> auxf h 
  | _ -> (h,[],[])

let rec normalize_formula_dn aux_f (f : formula): formula = match f with
  | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
    let rf1 = normalize_formula_dn aux_f f1 in
    let rf2 = normalize_formula_dn aux_f f2 in
    let resform = mkOr rf1 rf2 pos in
    resform
  | Base f1 ->
    let f1_heap, f1_constr, nv = normalize_h_formula_dn aux_f f1.formula_base_heap in
    Base({f1 with formula_base_heap = f1_heap})
  | Exists f1 ->
    let f1_heap, f1_constr, nv = normalize_h_formula_dn aux_f f1.formula_exists_heap in
    Exists({f1 with formula_exists_heap = f1_heap})

let merge_imm_ann ann1 ann2 = 
  match ann1, ann2 with
  | CP.ConstAnn(Mutable), ann
  | ann, CP.ConstAnn(Mutable) -> (ann, [], [])
  | CP.ConstAnn(Accs), _
  | _, CP.ConstAnn(Accs)    -> (CP.ConstAnn(Accs), [], [])
  | CP.PolyAnn sv, ann
  | ann, CP.PolyAnn sv   -> 
    let fresh_v = "ann_" ^ (fresh_name ()) in
    let fresh_sv = (CP.SpecVar(AnnT, fresh_v, Unprimed)) in
    let fresh_var = CP.Var(fresh_sv, no_pos) in
    let poly_ann = CP.mkPolyAnn fresh_sv in
    (* let constr1 = CP.mkSubAnn (CP.mkExpAnnSymb ann no_pos) fresh_var in *)
    (* let constr2 = CP.mkSubAnn (CP.Var(sv, no_pos)) fresh_var in *)
    (* (poly_ann, (constr1)::[constr2], [(fresh_v, Unprimed)]) *)
    let constr = CP.mkEqMax fresh_var  (CP.mkExpAnnSymb ann no_pos) (CP.Var(sv, no_pos)) no_pos in
    let constr = CP.BForm ((constr, None), None) in
    (poly_ann, [constr], [(fresh_v, Unprimed)])
  | ann_n, _ -> let ann = if (subtype_ann 2  ann_n  ann2 ) then ann2 else  ann1 in
    (ann, [], [])

let push_node_imm_to_field_imm_x (h: CF.h_formula):  CF.h_formula  * (CP.formula list) * ((Globals.ident * VarGen.primed) list) =
  match h with
  | CF.DataNode dn -> 
    let ann_node = dn.CF.h_formula_data_imm in
    let new_ann_param, constr, new_vars =
      if (List.length  dn.CF.h_formula_data_param_imm == List.length  dn.CF.h_formula_data_arguments) then
        List.fold_left (fun (params, constr, vars) p_ann ->
            let new_p_ann,nc,nv = merge_imm_ann ann_node p_ann in
            (params@[new_p_ann], nc@constr, nv@vars)
          ) ([],[],[]) dn.CF.h_formula_data_param_imm
      else
        let () = report_warning no_pos ("data field imm not set. Setting it now to be the same as node lvl imm. ") in
        let new_ann_param = List.map (fun _ -> ann_node) dn.CF.h_formula_data_arguments in
        (new_ann_param, [], [])
    in 
    let new_ann_node =  if (List.length  dn.CF.h_formula_data_param_imm > 0) then CP.ConstAnn(Mutable) else ann_node in
    let n_dn = CF.DataNode{dn with  CF.h_formula_data_imm = new_ann_node;
                                    CF.h_formula_data_param_imm = new_ann_param;} in
    (n_dn, constr, new_vars)
  | CF.ViewNode vn ->
    let ann_node = vn.CF.h_formula_view_imm in
    let pimm = CP.annot_arg_to_imm_ann_list_no_pos vn.CF.h_formula_view_annot_arg in
    let new_imm, constr, new_vars = List.fold_left (fun (params, constr, vars) p_ann ->
        let new_p_ann,nc,nv = merge_imm_ann ann_node p_ann in
        (params@[new_p_ann], nc@constr, nv@vars)
      ) ([],[],[]) pimm in
    let new_vn = CF.ViewNode {vn with CF.h_formula_view_annot_arg = 
                                        CP.update_positions_for_imm_view_params  new_imm vn.h_formula_view_annot_arg;} in
    (new_vn, constr, new_vars)
  | _ -> (h, [], [])

let push_node_imm_to_field_imm caller (h:CF.h_formula) : CF.h_formula * (CP.formula list) * ((Globals.ident * VarGen.primed) list) =
  let pr = Cprinter.string_of_h_formula in
  let pr_out = pr_triple Cprinter.string_of_h_formula (pr_list !CP.print_formula) pr_none in
  Debug.no_1_num caller "push_node_imm_to_field_imm" pr pr_out push_node_imm_to_field_imm_x h 

let normalize_field_ann_heap_node_x (h:CF.h_formula): CF.h_formula  * (CP.formula list) * ((Globals.ident * VarGen.primed) list) =
  if (!Globals.allow_field_ann) then
    (* if false then *)
    let h, constr, new_vars = normalize_h_formula_dn (push_node_imm_to_field_imm 1) h in
    (h,constr,new_vars)
  else (h,[],[])

let normalize_field_ann_heap_node (h:CF.h_formula): CF.h_formula * (CP.formula list) * ((Globals.ident * VarGen.primed) list) =
  let pr = Cprinter.string_of_h_formula in
  let pr_out = pr_triple Cprinter.string_of_h_formula pr_none pr_none in
  Debug.no_1 "normalize_field_ann_heap_node" pr pr_out normalize_field_ann_heap_node_x h

let normalize_field_ann_formula_x (h:CF.formula): CF.formula =
  if (!Globals.allow_field_ann) then
    (* if (false) then *)
    normalize_formula_dn (push_node_imm_to_field_imm 2) h
  else h

let normalize_field_ann_formula (h:CF.formula): CF.formula =
  let pr = Cprinter.string_of_formula in
  Debug.no_1 "normalize_field_ann_formula" pr pr normalize_field_ann_formula_x h

let normalize_field_ann_struc_formula_x (sf:CF.struc_formula): CF.struc_formula =
  if (!Globals.allow_field_ann) then
    (* if (false) then *)
    let rec helper sf = 
      match sf with
      | EBase f   -> EBase {f with 
                            formula_struc_base = normalize_field_ann_formula f.formula_struc_base  }
      | EList l   -> EList  (map_l_snd (fun c->  helper c ) l)
      | ECase f   -> ECase {f with formula_case_branches = map_l_snd (fun c->  helper c) f.formula_case_branches;}
      | EAssume f -> EAssume {f with
                              formula_assume_simpl = normalize_field_ann_formula f.formula_assume_simpl;
                              formula_assume_struc = helper f.formula_assume_struc;}
      | EInfer f  -> EInfer {f with formula_inf_continuation = helper f.formula_inf_continuation } 
    in helper sf
  else sf

let normalize_field_ann_struc_formula (h:CF.struc_formula): CF.struc_formula =
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_1 "normalize_field_ann_struc_formula" pr pr normalize_field_ann_struc_formula_x h

let update_read_write_ann (ann_from: CP.ann) (ann_to: CP.ann): CP.ann  =
  match ann_from with
  | CP.ConstAnn(Mutable)	-> ann_from
  | CP.ConstAnn(Accs)    -> ann_to
  | CP.ConstAnn(Imm)
  | CP.ConstAnn(Lend)
  | CP.TempAnn _
  | CP.PolyAnn(_)        -> 
    if subtype_ann 5 ann_from ann_to then ann_from else ann_to
  | CP.TempRes _ | CP.NoAnn     -> ann_to

let read_write_exp_analysis (ex: C.exp)  (field_ann_lst: (ident * CP.ann) list) =
  let rec helper ex field_ann_lst  =
    match ex with
    | C.Block {C.exp_block_body = e} 
    | C.Catch { C.exp_catch_body = e} (* ->         helper cb field_ann_lst *)
    | C.Cast {C.exp_cast_body = e }
    | C.Label {C.exp_label_exp = e}  (* > helper e field_ann_lst *)
      -> helper e field_ann_lst
    | C.Assert {
        C.exp_assert_asserted_formula = assert_f_o;
        C.exp_assert_assumed_formula = assume_f_o } ->
      (* check assert_f_o and assume_f_o *)
      field_ann_lst
    | C.Assign  {
        C.exp_assign_lhs = lhs;
        C.exp_assign_rhs = rhs  } ->
      let field_ann_lst = 
        List.map (fun (f, ann) -> if (lhs == f) then (f, update_read_write_ann ann (CP.ConstAnn(Mutable))) else (f,ann) ) field_ann_lst in
      helper rhs field_ann_lst
    | C.Bind {
        C.exp_bind_bound_var = v;
        C.exp_bind_fields = vs;
        C.exp_bind_body = e } ->
      (* andreeac TODO: nested binds ---> is it supported? *)
      field_ann_lst
    | C.ICall {
        C.exp_icall_arguments = args } ->
      List.map (fun (f, ann) -> if (List.mem f args) then (f, update_read_write_ann ann (CP.ConstAnn(Lend))) else (f,ann) ) field_ann_lst
    | C.SCall {
        C.exp_scall_arguments = args } ->
      List.map (fun (f, ann) -> if (List.mem f args) then (f, update_read_write_ann ann (CP.ConstAnn(Lend))) else (f,ann) ) field_ann_lst
    | C.Cond {
        C.exp_cond_condition = cond;
        C.exp_cond_then_arm = e1;
        C.exp_cond_else_arm = e2 } ->
      let field_ann_lst = List.map (fun (f, ann) -> if (f == cond) then (f, update_read_write_ann ann (CP.ConstAnn(Lend))) else (f,ann) ) field_ann_lst in
      let field_ann_lst = helper e1 field_ann_lst in
      helper e2 field_ann_lst
    | C.New { C.exp_new_arguments = args } ->
      let args = List.map (fun (t, v) -> v) args in
      List.map (fun (f, ann) -> if (List.mem f args) then (f, update_read_write_ann ann (CP.ConstAnn(Lend))) else (f,ann) ) field_ann_lst
    | C.Try { C.exp_try_body = e1; C.exp_catch_clause = e2}
    | C.Seq { C.exp_seq_exp1 = e1; C.exp_seq_exp2 = e2 }->
      let field_ann_lst = helper e1 field_ann_lst in
      helper e2 field_ann_lst
    | C.Var { C.exp_var_name = v } ->
      List.map (fun (f, ann) -> if (f == v) then (f, update_read_write_ann ann (CP.ConstAnn(Lend))) else (f,ann) ) field_ann_lst
    | C.While{
        C.exp_while_condition = cond;
        C.exp_while_body = body } ->
      let field_ann_lst = List.map (fun (f, ann) -> if (f == cond) then (f, update_read_write_ann ann (CP.ConstAnn(Lend))) else (f,ann) ) field_ann_lst in
      helper body field_ann_lst
    | _  -> field_ann_lst

  in helper ex field_ann_lst

let merge_imm_for_view eq a1l a2l =
  match a1l,a2l with
  | [], []      -> []
  | [], t::_    -> a2l
  | t::_, []    -> a1l
  | t1::_,t2::_ -> if eq a1l a2l then a1l 
    else failwith "Imm: view should preserve the same imm map"

let update_arg_imm_for_view fimm dimm param_ann emap =
  let param_ann = List.fold_left (fun acc a -> acc@(CP.fv_ann a)) [] param_ann in
  match fimm with
  | CP.ConstAnn _ -> 
    let imm = 
      match dimm with
      | CP.PolyAnn _ -> dimm
      | _            -> fimm in 
    imm
  | CP.PolyAnn sv ->
    if (Gen.BList.mem_eq CP.eq_spec_var sv param_ann) then fimm
    else 
      let elist = sv::(CP.EMapSV.find_equiv_all sv emap) in 
      let plst  = Gen.BList.intersect_eq CP.eq_spec_var param_ann elist in
      if not (Gen.is_empty plst) then CP.mkPolyAnn (List.hd plst)
      else fimm
  | _ -> fimm

let collect_view_imm_from_h_formula f param_ann data_name emap = (* param_ann *)
  let rec helper  f param_ann data_name emap =
    match f with
    | CF.DataNode {h_formula_data_param_imm = pimm; h_formula_data_imm = imm; h_formula_data_name = name}-> 
      if name = data_name then
        List.map (fun p -> update_arg_imm_for_view p imm param_ann emap) pimm
      else []
    | CF.ViewNode h -> []
    | CF.Star {h_formula_star_h1 = h1; h_formula_star_h2 = h2}
    | CF.Conj {h_formula_conj_h1 = h1; h_formula_conj_h2 = h2}
    | CF.ConjStar {h_formula_conjstar_h1 = h1; h_formula_conjstar_h2 = h2}
    | CF.ConjConj {h_formula_conjconj_h1 = h1; h_formula_conjconj_h2 = h2}
    | CF.Phase    {h_formula_phase_rd = h1; h_formula_phase_rw = h2}
      -> 
      let a1 = helper h1 param_ann data_name emap in
      let a2 = helper h2 param_ann data_name emap in
      merge_imm_for_view CP.eq_ann_list a1 a2
    | _ -> []
  in  helper f param_ann data_name emap


let collect_view_imm_from_formula f param_ann data_name = (* param_ann *)
  let rec helper  f param_ann data_name = 
    match f with 
    | Or ({formula_or_f1 = f1; formula_or_f2 = f2; formula_or_pos = pos}) ->
      let a1 = helper f1 param_ann data_name in
      let a2 = helper f2 param_ann data_name in
      let anns = merge_imm_for_view CP.eq_ann_list a1 a2 in
      anns
    | Base   ({formula_base_heap   = h; formula_base_pure   = p})
    | Exists ({formula_exists_heap = h; formula_exists_pure = p}) ->
      let emap = Imm.build_eset_of_imm_formula (MCP.pure_of_mix p) in
      let anns = collect_view_imm_from_h_formula h param_ann data_name emap in
      anns
  in helper f param_ann data_name

let collect_view_imm_from_struc_formula sf param_ann data_name = 
  let rec helper sf param_ann data_name = 
    match sf with
    | EBase f   -> collect_view_imm_from_formula (f.formula_struc_base) param_ann data_name
    | EList l   -> List.fold_left (fun acc l ->  merge_imm_for_view CP.eq_ann_list acc l) [] (map_snd_only (fun c->  helper c param_ann data_name) l)
    | ECase f   -> List.fold_left (fun acc l ->  merge_imm_for_view CP.eq_ann_list acc l) [] (map_snd_only (fun c->  helper c param_ann data_name)  f.formula_case_branches)
    | EAssume f ->
      let v_imm_lst = collect_view_imm_from_formula f.formula_assume_simpl param_ann data_name in
      merge_imm_for_view CP.eq_ann_list [] (helper  f.formula_assume_struc param_ann data_name);
    | EInfer f  -> helper f.formula_inf_continuation param_ann data_name
  in helper sf param_ann data_name 

let collect_view_imm_from_case_struc_formula sf param_ann data_name def_ann = (* def_ann *)
  let f_lst = snd (List.split (sf.CF.formula_case_branches)) in
  let final_data_ann = List.fold_left (fun acc f->
      let data_ann = collect_view_imm_from_struc_formula f param_ann data_name in
      merge_imm_for_view CP.eq_ann_list acc data_ann
    ) [] f_lst in
  final_data_ann

(* andreeac TODOIMM use wrapper below *)
let collect_annot_imm_info_in_formula annot_args f data_name ddefs =
  let ddef = x_add I.look_up_data_def_raw ddefs data_name in
  let def_ann  = List.map (fun f -> CP.imm_ann_bot ) ddef.I.data_fields in
  let ann_final = 
    if not (!Globals.allow_field_ann) then def_ann
    else
      let ann_params = CP.annot_arg_to_imm_ann_list annot_args in
      let ann_params = collect_view_imm_from_struc_formula f ann_params data_name (* def_ann *) in
      ann_params
  in
  let annot_args = CP.imm_ann_to_annot_arg_list  ann_final in
  annot_args

let initialize_positions_for_args (aa: CP.annot_arg list) (wa: CP.view_arg list) cf data_name ddefs =
  let wa_pos = CP.initialize_positions_for_view_params wa in
  let aa = collect_annot_imm_info_in_formula aa cf data_name ddefs in
  let aa_pos = CP.update_positions_for_view_params_x aa wa_pos in
  aa_pos, wa_pos

(* let collect_view_imm_from_h_iformula f param_ann data_name emap = (\* param_ann *\) *)
(*   let rec helper  f param_ann data_name emap = *)
(*     match f with *)
(*       | IF.HeapNode2 {IF.h_formula_data_imm_param = pimm; IF.h_formula_heap_imm = imm; IF.h_formula_heap_name = name}->  *)
(*       | IF.HeapNode  {IF.h_formula_data_imm_param = pimm; IF.h_formula_heap_imm = imm; IF.h_formula_heap_name = name}->  *)
(*             if name = data_name then *)
(*               List.map (fun p -> update_arg_imm_for_view p imm param_ann emap) pimm *)
(*             else [] *)
(*       | IF.Star {IF.h_formula_star_h1 = h1; IF.h_formula_star_h2 = h2} *)
(*       | IF.Conj {IF.h_formula_conj_h1 = h1; IF.h_formula_conj_h2 = h2} *)
(*       | IF.ConjStar {IF.h_formula_conjstar_h1 = h1; IF.h_formula_conjstar_h2 = h2} *)
(*       | IF.ConjConj {IF.h_formula_conjconj_h1 = h1; IF.h_formula_conjconj_h2 = h2} *)
(*       | IF.Phase    {IF.h_formula_phase_rd = h1; IF.h_formula_phase_rw = h2} *)
(*           ->  *)
(*             let a1 = helper h1 param_ann data_name emap in *)
(*             let a2 = helper h2 param_ann data_name emap in *)
(*             merge_imm_for_view a1 a2 *)
(*       | _ -> [] *)
(*   in  helper f param_ann data_name emap *)


(* let collect_view_imm_from_iformula f param_ann data_name = (\* param_ann *\) *)
(*   let rec helper  f param_ann data_name =  *)
(*     match f with  *)
(*       | IF.Or ({IF.formula_or_f1 = f1; IF.formula_or_f2 = f2; IF.formula_or_pos = pos}) -> *)
(* 	    let a1 = helper f1 param_ann data_name in *)
(* 	    let a2 = helper f2 param_ann data_name in *)
(* 	    let anns = merge_imm_for_view a1 a2 in *)
(*             anns *)
(*       | IF.Base   ({IF.formula_base_heap   = h; IF.formula_base_pure   = p}) *)
(*       | IF.Exists ({IF.formula_exists_heap = h; IF.formula_exists_pure = p}) -> *)
(*             let emap = build_eset_of_conj_formula (MCP.pure_of_mix p) in *)
(*             let anns = collect_view_imm_from_h_iformula h param_ann data_name emap in *)
(*             anns *)
(*   in helper f param_ann data_name *)

(* let collect_view_imm_from_struc_iformula sf param_ann data_name =  *)
(*   let rec helper sf param_ann data_name =  *)
(*     match sf with *)
(*       | IF.EBase f   -> collect_view_imm_from_iformula (f.IF.formula_struc_base) param_ann data_name *)
(*       | IF.EList l   -> List.fold_left (fun acc l ->  merge_imm_for_view acc l) [] (map_snd_only (fun c->  helper c param_ann data_name) l) *)
(*       | IF.ECase f   -> List.fold_left (fun acc l ->  merge_imm_for_view acc l) [] (map_snd_only (fun c->  helper c param_ann data_name)  f.IF.formula_case_branches) *)
(*       | IF.EAssume f -> *)
(*             let v_imm_lst = collect_view_imm_from_iformula f.IF.formula_assume_simpl param_ann data_name in *)
(*             merge_imm_for_view [] (helper  f.IF.formula_assume_struc param_ann data_name); *)
(*       | IF.EInfer f  -> helper f.IF.formula_inf_continuation param_ann data_name *)
(*   in helper sf param_ann data_name  *)

(* andreeac TODOIMM use wrapper below *)
(* let collect_annot_imm_info_in_iformula annot_args f data_name ddefs = *)
(*   let ddef = I.look_up_data_def_raw ddefs data_name in *)
(*   let def_ann  = List.map (fun f -> CP.imm_ann_bot ) ddef.I.data_fields in *)
(*   let ann_final = *)
(*     if not (!Globals.allow_field_ann) then def_ann *)
(*     else *)
(*       let ann_params = CP.annot_arg_to_imm_ann_list annot_args in *)
(*       let ann_params = collect_view_imm_from_struc_iformula f ann_params data_name (\* def_ann *\) in *)
(*       ann_params *)
(*   in *)
(*   let annot_args = CP.imm_ann_to_annot_arg_list  ann_final in *)
(*   annot_args *)

let collect_view_imm_from_h_iformula h  data_name = (* [] *)
  let rec helper  f data_name =
    match f with
    | IF.HeapNode2 {IF.h_formula_heap2_imm_param = pimm; (* IF.h_formula_heap_imm = imm; *) IF.h_formula_heap2_name = name}
    | IF.HeapNode  {IF. h_formula_heap_imm_param = pimm; (* IF.h_formula_heap_imm = imm; *) IF.h_formula_heap_name = name}->
      if name = data_name then (ann_opt_to_ann_lst pimm Ipure.imm_ann_bot)
      (* List.map (fun p -> update_arg_imm_for_view p imm param_ann emap) pimm *)
      else []
    | IF.Star {IF.h_formula_star_h1 = h1; IF.h_formula_star_h2 = h2}
    | IF.Conj {IF.h_formula_conj_h1 = h1; IF.h_formula_conj_h2 = h2}
    | IF.ConjStar {IF.h_formula_conjstar_h1 = h1; IF.h_formula_conjstar_h2 = h2}
    | IF.ConjConj {IF.h_formula_conjconj_h1 = h1; IF.h_formula_conjconj_h2 = h2}
    | IF.Phase    {IF.h_formula_phase_rd = h1; IF.h_formula_phase_rw = h2}
      ->
      let a1 = helper h1 data_name in
      let a2 = helper h2 data_name in
      merge_imm_for_view Ipure.eq_ann_list a1 a2
    | _ -> []
  in  helper h data_name 

let collect_view_imm_from_iformula f data_name = 
  let rec helper  f data_name =
    match f with
    | IF.Or ({IF.formula_or_f1 = f1; IF.formula_or_f2 = f2; IF.formula_or_pos = pos}) ->
      let a1 = helper f1 data_name in
      let a2 = helper f2 data_name in
      let anns = merge_imm_for_view  Ipure.eq_ann_list a1 a2 in
      anns
    | IF.Base   ({IF.formula_base_heap   = h; IF.formula_base_pure   = p})
    | IF.Exists ({IF.formula_exists_heap = h; IF.formula_exists_pure = p}) ->
      (* let emap = build_eset_of_conj_formula (MCP.pure_of_mix p) in *)
      let anns = collect_view_imm_from_h_iformula h data_name in
      anns
  in helper f data_name

let collect_imm_from_struc_iformula sf data_name =
  let rec helper sf data_name =
    match sf with
    | IF.EBase f   -> collect_view_imm_from_iformula (f.IF.formula_struc_base) data_name
    | IF.EList l   -> List.fold_left (fun acc l ->  merge_imm_for_view Ipure.eq_ann_list acc l) [] (map_snd_only (fun c->  helper c data_name) l)
    | IF.ECase f   -> List.fold_left (fun acc l ->  merge_imm_for_view Ipure.eq_ann_list acc l) [] (map_snd_only (fun c->  helper c data_name)  f.IF.formula_case_branches)
    | IF.EAssume f ->
      let v_imm_lst = collect_view_imm_from_iformula f.IF.formula_assume_simpl data_name in
      merge_imm_for_view Ipure.eq_ann_list [] (helper  f.IF.formula_assume_struc data_name);
    | IF.EInfer f  -> helper f.IF.formula_inf_continuation data_name
  in helper sf data_name

let add_position_to_imm_ann (a: Ipure.ann) (vp_pos: (ident * int) list) = 
  let a_pos = 
    match a with
    | Ipure.NoAnn -> (a,0)
    | Ipure.ConstAnn _        -> (a,0)
    | Ipure.PolyAnn ((v,_),_) -> 
      let ff p = if (String.compare (fst p) v == 0) then Some (a,snd p) else None in
      let found = Gen.BList.list_find ff vp_pos in
      match found with
      | Some p -> p
      | None   -> (a,0)
  in
  a_pos

let icollect_imm f vparam data_name ddefs =
  try
    let ddef = x_add I.look_up_data_def_raw ddefs data_name in
    let def_ann  = List.map (fun f -> (Ipure.imm_ann_bot, 0) ) ddef.I.data_fields in
    let ann_final =
      if not (!Globals.allow_field_ann) then def_ann
      else
        let ann_params = collect_imm_from_struc_iformula f data_name (* def_ann *) in
        let vp_pos = CP.initialize_positions_for_view_params vparam in
        let ann_pos = List.map (fun a ->  add_position_to_imm_ann a vp_pos) ann_params in
        ann_pos
    in
    ann_final
  with Not_found -> [] (* this is for prim pred *)

let icollect_imm f vparam data_name ddefs =
  Debug.no_3 "icollect_imm" Iprinter.string_of_struc_formula 
    (pr_list pr_id) pr_id (pr_list (pr_pair Iprinter.string_of_imm string_of_int)) (fun _ _ _ -> icollect_imm f vparam data_name ddefs) f vparam data_name

let pr_label = (fun l -> if LO.is_common l then "" else (LO.string_of l)^":")
let pr_labels = (pr_list pr_label) 

let split_view_args view_args vdef:  CP.spec_var list * 'a list * (CP.annot_arg * int) list * (CP.view_arg * int) list  =
  (* TODO: normalize the unused ann consts  *)
  (* retrieve imm_map from I.view_decl *)
  (* let view_vars_gen = CP.sv_to_view_arg_list sv in *)
  let view_arg_lbl =  try (List.combine view_args (fst vdef.I.view_labels))
    with  Invalid_argument _ -> 
      List.map (fun v -> (v,LO.unlabelled)) view_args 
      (* failwith "Immutable.ml, split_view_args: error while combining view args with labels 1"  *)
  in
  let ann_map_pos = vdef.I.view_imm_map in
  (* let () = x_tinfo_hp (add_str "imm_map:" (pr_list (pr_pair Iprinter.string_of_imm string_of_int))) ann_map_pos no_pos in *)
  (* let () = x_tinfo_hp (add_str " view_arg_lbl:" (pr_list (pr_pair pr_none pr_label))) view_arg_lbl no_pos in *)
  (* create list of view_arg*pos  *)
  let vp_pos = CP.initialize_positions_for_view_params view_arg_lbl in
  (* let () = x_tinfo_hp (add_str " vp_pos:" (pr_list (pr_pair (pr_pair pr_none pr_label) string_of_int))) vp_pos no_pos in *)
  let view_args_pos = List.map (fun ((va,_),pos) -> (va,pos)) vp_pos in
  let annot_arg, vp_pos = List.partition (fun (vp,pos) -> List.exists (fun (_,p) -> p == pos ) ann_map_pos) vp_pos in
  let vp_lbl, _ = List.split vp_pos in  (* get rid of positions *)
  let vp, lbl   = List.split vp_lbl in  (* separate lbl from args *)
  let svp = CP.view_arg_to_sv_list vp in 
  let annot_arg_pos = List.map (fun ((a, _), pos) -> (a, pos)) annot_arg in (* get rid of lbl *)
  let annot_arg,pos = List.split annot_arg_pos in
  let imm_arg = CP.view_arg_to_imm_ann_list annot_arg in 
  let imm_arg_pos = try
      let imm_arg = 
        if imm_arg = [] then List.map (fun _ -> CP.ConstAnn Mutable) pos
        else imm_arg
      in
      List.combine imm_arg pos 
    with  Invalid_argument _ -> failwith "Immutable.ml, split_view_args: error while combining imm_arg with pos" in
  (* create an imm list following the imm_map, updated with proper values from the list of params *)
  let anns_pos = List.map (fun (a, pos) -> 
      try  List.find (fun (_, vpos) -> vpos == pos) imm_arg_pos
      with Not_found -> (iformula_ann_to_cformula_ann a, pos) )  ann_map_pos in
  let anns, pos = List.split anns_pos in
  let annot_arg = CP.imm_ann_to_annot_arg_list anns in
  let annot_args_pos = try List.combine annot_arg pos 
    with  Invalid_argument _ -> failwith "Immutable.ml, split_view_args: error while combining annot_arg with pos 2" in
  svp, lbl, annot_args_pos, view_args_pos

let split_view_args view_args vdef:  CP.spec_var list * 'a list * (CP.annot_arg * int) list * (CP.view_arg * int) list  =
  let pr = pr_quad  Cprinter.string_of_spec_var_list pr_labels (pr_list (pr_pair Cprinter.string_of_annot_arg string_of_int)) (pr_list (pr_pair Cprinter.string_of_view_arg string_of_int)) in 
  Debug.no_1 "split_view_args" Cprinter.string_of_view_arg_list pr (fun _ -> split_view_args view_args vdef) view_args

let split_sv sv vdef:  CP.spec_var list * 'a list * (CP.annot_arg * int) list * (CP.view_arg * int) list  =
  (* retrieve imm_map from I.view_decl *)
  let view_vars_gen = CP.sv_to_view_arg_list sv in
  split_view_args view_vars_gen vdef

let split_sv sv vdef:  CP.spec_var list * 'a list * (CP.annot_arg * int) list * (CP.view_arg * int) list  =
  let pr = pr_quad  Cprinter.string_of_spec_var_list pr_none (pr_list (pr_pair Cprinter.string_of_annot_arg string_of_int)) (pr_list (pr_pair Cprinter.string_of_view_arg string_of_int)) in 
  Debug.no_1 "split_sv" Cprinter.string_of_spec_var_list pr (fun _ -> split_sv sv vdef) sv

let initialize_imm_args args =
  List.map (fun _ -> Some (Ipure.ConstAnn(Mutable))) args

let propagate_imm_formula sf view_name (imm : CP.ann)  (imm_p: (CP.annot_arg * CP.annot_arg) list) =
  let res = propagate_imm_formula sf view_name imm imm_p in
  normalize_field_ann_formula res

let propagate_imm sf view_name (imm : CP.ann)  (imm_p: (CP.annot_arg * CP.annot_arg) list) =
  let res = propagate_imm_struc_formula sf view_name imm imm_p in
  normalize_field_ann_struc_formula res

(* ===============================  below is for merging aliased nodes ================================= *)
(* ================== ex: x::node<a,y>@A * y::node<b,z> & x=y ----> y::node<b,z> & x=y ================= *)

let crop_incompatible_disjuncts unfolded_f dn emap =
  let rec helper f = 
    match f with
    | Base   ({formula_base_heap = h; formula_base_pure = p; })
    | Exists ({formula_exists_heap = h; formula_exists_pure = p; }) ->
      let (subs,_) = CP.get_all_vv_eqs (MCP.pure_of_mix p) in
      let emap2 = CP.EMapSV.build_eset subs in
      let emap  = CP.EMapSV.merge_eset emap emap2 in
      let sv, ident = dn.h_formula_data_node, dn.h_formula_data_name in
      let aset  = sv::(CP.EMapSV.find_equiv_all sv emap) in
      if  h_formula_contains_node h aset ident then Some f
      else None
    | Or orf ->
      let f1 = helper orf.formula_or_f1 in
      let f2 = helper orf.formula_or_f2 in
      match f1,f2 with
      | Some f1, Some f2 -> Some (Or {orf with formula_or_f1 = f1; formula_or_f2 = f2})
      | Some f, None
      | None, Some f -> Some f
      | None, None   -> None

  in helper unfolded_f

let crop_incompatible_disjuncts unfolded_f dn emap =
  let pr = !CF.print_formula in
  let pr1 = CP.EMapSV.string_of in
  Debug.no_2 "crop_incompatible_disjuncts" pr pr1 (pr_opt pr) (fun _ _ -> crop_incompatible_disjuncts unfolded_f dn emap) unfolded_f emap

let unfold_and_norm vn vh dn emap unfold_fun qvars emap =
  let v =  vn.h_formula_view_node in
  let aset = v::(CP.EMapSV.find_equiv_all v emap) in           
  let uf = 0 in               (* is 0 ok or can it cause infinite unroll? *)
  let unfolded_f = unfold_fun vh v uf in
  (* let ret_f = push_exists qvars unfolded_f in *)
  (* let ret_f = crop_incompatible_disjuncts unfolded_f dn emap in *)
  Some unfolded_f (* ret_f *)

(*  @imm1=max(imm2,imm3) *)
let max_guard emap imm1 imm2 imm3 =
  let pure_max = CP.mkPure (CP.mkEqMax (CP.imm_to_exp imm1 no_pos) (CP.imm_to_exp imm2 no_pos) (CP.imm_to_exp imm3 no_pos) no_pos) in
  Immutils.norm_eqmax emap imm1 imm2 imm3 pure_max

(*  @imm1=min(imm2,imm3) *)
let min_guard emap imm1 imm2 imm3 =
  let pure_min = CP.mkPure (CP.mkEqMin (CP.imm_to_exp imm1 no_pos) (CP.imm_to_exp imm2 no_pos) (CP.imm_to_exp imm3 no_pos) no_pos) in
  Immutils.norm_eqmin emap imm1 imm2 imm3 pure_min

(* imm_bound<:max(immr1,immr2) *)
let bound_max_guard emap imm_bound immr1 immr2 =
  let fresh_ann_sv = CP.fresh_spec_var_ann ~old_name:"imm" () in
  let fresh_ann_var = CP.Var(fresh_ann_sv, no_pos) in
  let imm = CP.mkPolyAnn fresh_ann_sv in
  let min_lend = CP.mkPure (CP.mkEqMax fresh_ann_var (CP.imm_to_exp immr1 no_pos) (CP.imm_to_exp immr2 no_pos) no_pos) in
  let guard_max = Immutils.norm_eqmax emap imm immr1 immr2 min_lend in
  if (Immutils.strict_subtype emap imm imm_bound) then 
    let () = report_warning no_pos ("creating false ctx ("^(CP.string_of_imm imm)^"<:"^(CP.string_of_imm imm_bound)
                                    ^" but not("^(CP.string_of_imm imm_bound) ^"<:"^(CP.string_of_imm imm)^"))" ) in
    [CP.mkFalse no_pos]
  else 
    let guard1 = CP.mkSubAnn (CP.imm_to_exp imm_bound no_pos) fresh_ann_var in
    guard1::[guard_max]

let mk_imm_add emap imml immr1 immr2 = 
  let left_imm = CP.imm_to_exp imml no_pos in
  let guard = CP.mkEq left_imm (CP.mkAdd (CP.imm_to_exp immr1 no_pos) (CP.imm_to_exp immr2 no_pos) no_pos) no_pos in
  (* let guard = CP.mkEq left_imm (CP.mkAdd (CP.imm_to_exp immr1 no_pos) (CP.imm_to_exp immr2 no_pos) no_pos) no_pos in *)
  let guard = CP.mkPure guard in
  let guard = x_add_1 (Immutils.simplify_imm_addition ~emap:emap) guard in

  (* min guard  *)
  let guard_min = CP.mkPure (CP.mkEqMin  (CP.imm_to_exp imml no_pos)  (CP.imm_to_exp immr1 no_pos)  (CP.imm_to_exp immr2 no_pos) no_pos) in
  let guard_lst = if not(!Globals.imm_add) then [guard] 
    else [guard;guard_min] in

  (imml, guard_lst)

(* c=a-b ----> a=min(c,b) & @L<:max(c,b) *)
let subtraction_guards emap imm1 imm2 =
  (*  @L<:max(c,b) *)
  let guard_max = bound_max_guard emap (CP.mkConstAnn Lend) imm1 imm2 in

  (* a=min(c,b) *)
  let fresh_ann_sv = CP.fresh_spec_var_ann ~old_name:"imm" () in
  let fresh_ann =  (CP.mkPolyAnn fresh_ann_sv) in  
  let emap0 = Immutils.build_eset_of_imm_formula (CP.join_conjunctions guard_max) in
  let emap = CP.EMapSV.merge_eset emap0 emap in
  (* let _, guard_add = mk_imm_add emap imm1 fresh_ann imm2 in *)
  let guard_min = min_guard emap imm1 fresh_ann imm2 in

  fresh_ann, guard_max@[guard_min]

let subtraction_guards emap imm1 imm2 =
  let pr1 = CP.EMapSV.string_of in
  let pr2 = CP.string_of_ann in
  Debug.no_3 "subtraction_guards" pr1 pr2 pr2 (pr_pair pr2 (pr_list !CP.print_formula)) subtraction_guards emap imm1 imm2

(* tranform @[@a,@b] to @c, where a=b+c *)
let get_simpler_imm emap imm =
  match imm with
  | CP.TempRes (a1,a2) -> subtraction_guards emap a1 a2
  (*not sound to do this -  might get back the borrowed permission before solving the entailment*)
  (* | CP.TempAnn (a) -> subtraction_guards emap a (CP.mkConstAnn Lend) *) 
  | _ -> imm, []

let get_simpler_imm emap imm =
  let pr1 = CP.EMapSV.string_of in
  let pr2 = CP.string_of_imm in
  Debug.no_2 "get_simpler_imm" pr1 pr2 (pr_pair pr2 (pr_list !CP.print_formula)) get_simpler_imm emap imm

(* TODOIMM not safe to return @a from @[a]+@L *)
let check_for_trivial_merge emap imm1 imm2 =
  let helper def a1 a2 =  try
      if (CP.EMapSV.is_equiv emap (CP.imm_to_spec_var a1) (CP.imm_to_spec_var a2)) then Some def,[]
      else None, []
    with _ -> None, [] in

  (* check for a merge between <>@TempRes[a,b] * <>@b ---> @a*)
  match imm1, imm2 with
  | CP.TempRes (a1,a2), a
  | a, CP.TempRes (a1,a2) -> helper a1 a a2
  (* | a,  CP.TempAnn (at) *)
  (* | CP.TempAnn (at), a -> helper at a (CP.ConstAnn Lend)  *)
  | _ -> None, []  

let check_for_trivial_merge emap imm1 imm2 = 
  let pr1 = CP.EMapSV.string_of in
  let pr2 = CP.string_of_ann in
  Debug.no_3 "check_for_trivial_merge" pr1 pr2 pr2 (pr_pair (pr_opt pr2) (pr_list !CP.print_formula)) check_for_trivial_merge emap imm1 imm2

(* x::cell<>@imm1 * x::cell<>@imm2 ---> x::cell<>@imm & imm=imm1+imm2 & @A=max(imm1,imm2) *)
let merge_guards emap imm1 imm2 = 
  let imm, guards00 =  check_for_trivial_merge emap imm1 imm2 in
  match imm with
  | Some a -> a, guards00
  | None   ->
    let imm1, guard1 = get_simpler_imm emap imm1 in
    let imm2, guard2 = get_simpler_imm emap imm2 in

    (* @A=max(imm1,imm2) *)
    let min_one_abs = max_guard emap (CP.ConstAnn Accs) imm1 imm2 in

    (* fresh_sv=min(imm1,imm2) *)
    let emap0 = Immutils.build_eset_of_imm_formula min_one_abs in
    let emap = CP.EMapSV.merge_eset emap0 emap in
    let fresh_ann_sv = CP.fresh_spec_var_ann ~old_name:"imm" () in
    let imm = CP.mkPolyAnn fresh_ann_sv in
    let min_guard = min_guard emap imm imm1 imm2 in
    (* let imm, guard =  mk_imm_add emap (CP.mkPolyAnn fresh_ann_sv) imm1 imm2 in *)

    (imm, min_guard::guard1@guard2@[min_one_abs])

let merge_guards emap imm1 imm2 =
  match imm1, imm2 with
  | CP.TempAnn a, CP.TempAnn b ->
    let imm, guards = merge_guards emap a b in
    (CP.TempAnn imm, guards)
  | (CP.TempAnn a), imm
  | imm , (CP.TempAnn a) ->
    if (Immutils.is_lend ~emap:emap imm) then (a,[])
    else let imm_new, guards = merge_guards emap a imm in
      (CP.TempAnn imm_new, guards)
  | _ -> merge_guards emap imm1 imm2

let merge_guards emap imm1 imm2 = 
  let pr1 = CP.EMapSV.string_of in
  let pr2 = CP.string_of_imm in
  Debug.no_3 "merge_guards" pr1 pr2 pr2 (pr_pair pr2 (pr_list !CP.print_formula)) merge_guards emap imm1 imm2

(* return (compatible_flag, to_keep_node) *)
let compatible_at_field_lvl imm1 imm2 h1 h2 unfold_fun qvars emap = 
  let comp, ret_h, unfold_f, guards =
    match h1, h2 with
    | DataNode dn1, DataNode dn2 ->
      let p1, p2, imm, guards = 
        try
          let p1 = List.combine dn1.h_formula_data_arguments dn1.h_formula_data_param_imm in
          let p2 = List.combine dn2.h_formula_data_arguments dn2.h_formula_data_param_imm in
          let imm = List.combine p1 p2 in
          (p1,p2,imm,[])
        with Invalid_argument _ -> failwith "Immutable.ml, compatible_at_field_lvl" in
      let (comp, updated_elements, guards) = List.fold_left (fun (comp,lst,guard) ((a1,i1), (a2,i2)) ->
          match i1, i2 with
          | CP.ConstAnn(Accs), a -> (true && comp, lst@[(a2,i2)],guard)
          | a, CP.ConstAnn(Accs) -> (true && comp, lst@[(a1,i1)],guard)
          | _, _ ->  
            let imm, guards = merge_guards emap i1 i2 in
            (* Debug.print_info "Warning: " "possible unsoundess (\* between overlapping heaps) " no_pos; *)
            (true && comp, lst@[(a1,imm)],guard@guards)
        ) (true,[],[]) imm in
      let args, pimm = List.split updated_elements in
      (* !!!! Andreea: to check how to safely merge two data nodes. Origins and Original info (and other info) abt dn2 is lost *)
      let dn = DataNode {dn1 with h_formula_data_arguments = args; h_formula_data_param_imm = pimm;} in
      (comp, dn, None, guards)
    | ViewNode vn1, ViewNode vn2 -> (* Debug.print_info "Warning: " "combining two views not yet implemented" no_pos; *)
      (* needs revision *)
      let imm1 = get_node_param_imm h1 in
      let imm2 = get_node_param_imm h2 in
      let imm  = 
        try List.combine imm1 imm2 
        with Invalid_argument _ -> failwith "Immutable.ml, compatible_at_field_lvl" in
      let comp, pimm, guards = List.fold_left (fun (comp,lst,guard) (i1,i2) -> 
          match i1, i2 with
          | CP.ConstAnn(Accs), a 
          | a, CP.ConstAnn(Accs) -> true && comp, lst@[a], guard
          |  CP.ConstAnn _,  CP.ConstAnn _ -> (false, [], [])
          | _, _ -> let imm, guards = merge_guards emap i1 i2 in
            (* Debug.print_info "Warning: " "possible unsoundess (\* between overlapping heaps) " no_pos; *)
            (* false && comp *)
            (true && comp, lst@[imm],guard@guards)
        ) (true,[],[]) imm in 
      (comp, h1, None, guards)
    | DataNode dn, ((ViewNode vn) as vh)
    | ((ViewNode vn) as vh), DataNode dn ->
      let pimm = CP.annot_arg_to_imm_ann_list_no_pos vn.h_formula_view_annot_arg in
      let () = x_tinfo_hp (add_str "imm:" (pr_list Cprinter.string_of_imm)) pimm no_pos in
      let comp = 
        if (List.length dn.h_formula_data_param_imm == List.length (pimm) ) then 
          let imm = 
            try List.combine dn.h_formula_data_param_imm pimm 
            with Invalid_argument _ -> failwith "Immutable.ml, compatible_at_field_lvl" in
          let () = x_tinfo_hp (add_str "imm:" (pr_list (pr_pair Cprinter.string_of_imm Cprinter.string_of_imm))) imm no_pos in
          let comp = List.fold_left (fun acc (i1,i2) -> 
              match i1, i2 with
              | CP.ConstAnn(Accs), a -> true && acc
              | a, CP.ConstAnn(Accs) -> true && acc
              | _, _ -> false
            ) true imm in
          comp
        else false in
      let () = x_tinfo_hp (add_str "compatible for merging:" string_of_bool) comp no_pos in
      if comp then
        let ret_f = unfold_and_norm vn vh dn emap unfold_fun qvars emap in
        (comp, h1, ret_f, [])
        (* incompatible for merging *)
      else (comp, h1, None, [])
    | _, _ -> 
      Debug.print_info "Warning: " "combining different kind of nodes not yet implemented" no_pos; 
      (false, h1, None,[])
  in (comp, ret_h, unfold_f, guards)

let compatible_at_field_lvl imm1 imm2 h1 h2 unfold_fun qvars emap = 
  let pr = Cprinter.string_of_h_formula in
  let pr_out3 = pr_opt Cprinter.string_of_formula in
  let pr_guards = pr_list !CP.print_formula in
  Debug.no_2 "compatible_at_field_lvl" pr pr (pr_quad string_of_bool pr pr_out3 pr_guards) (fun _ _ -> compatible_at_field_lvl imm1 imm2 h1 h2 unfold_fun qvars emap) h1 h2 

(* return (compatible_flag, to_keep_node) *)
let compatible_at_node_lvl prog imm1 imm2 h1 h2 unfold_fun qvars emap =
  let comp, ret_h, guards =
    if (Imm.is_abs ~emap:emap imm2) then (true, h1, [])
    else  if (Imm.is_abs ~emap:emap imm1) then (true, h2, [])
    else  if (Imm.is_const_imm_list ~emap:emap [imm1;imm2]) then 
      (* imm1 & imm2 are imm constants, but none is @A *)
      let pr = Cprinter.string_of_h_formula in
      (* let () = print_endline "*** at overlapping location" in- *)
      (* TODO: ptr view and prim_view should be excluded *)
      let () = y_tinfo_hp (add_str "* between overlapping heaps" (pr_pair pr pr)) (h1, h2) in
      (false, h1, [])
      (* failwith ("* between overlapping heaps: " ^ (pr_pair pr pr (h1,h2))) *)
    else
      let imm, guards = merge_guards emap imm1 imm2 in
      let h = set_imm h1 imm in
      (true, h, guards) in
  let compatible, keep_h, struc, guards =
    (match h1, h2 with
     | DataNode _, DataNode _
     | ViewNode _, ViewNode _ -> (comp, ret_h, None, guards)
     | ((DataNode dn) as dh), ((ViewNode vn) as vh)
     | ((ViewNode vn) as vh), ((DataNode dn) as dh) ->
       if comp then
         let ret_f = unfold_and_norm vn vh dn emap unfold_fun qvars emap in
         (comp, dh, ret_f, guards)
         (* (comp, dh, None) *)
       else (comp, ret_h, None, guards)
     | _, _ -> (comp, ret_h, None, guards)) in
  (compatible, keep_h, struc, guards)

let compatible_nodes prog imm1 imm2 h1 h2 unfold_fun qvars emap = 
  if (!Globals.allow_field_ann) then compatible_at_field_lvl imm1 imm2 h1 h2 unfold_fun qvars emap
  else compatible_at_node_lvl prog imm1 imm2 h1 h2 unfold_fun qvars emap

let compatible_nodes prog imm1 imm2 h1 h2 unfold_fun qvars emap =
  let pr = Cprinter.string_of_h_formula in
  let pr_out3 = pr_opt Cprinter.string_of_formula in
  let pr_guards = pr_list !CP.print_formula in
  Debug.no_2 "compatible_nodes" pr pr (pr_quad string_of_bool pr pr_out3 pr_guards) (fun _ _ ->  compatible_nodes prog imm1 imm2 h1 h2 unfold_fun qvars emap ) h1 h2

let partition_eqs_subs lst1 lst2 quantif =
  let eqs_lst = 
    try List.combine lst1 lst2 
    with Invalid_argument _ -> failwith "Immutable.ml, compatible_at_field_lvl" in
  let eqs_lst = List.map (fun (a,b) -> 
      if Gen.BList.mem_eq CP.eq_spec_var a quantif then (a,b)
      else if Gen.BList.mem_eq CP.eq_spec_var b quantif then (b,a)
      else (a,b) ) eqs_lst in
  let eqs_lst = List.fold_left (fun acc (a,b) -> if CP.eq_spec_var a b then acc else acc@[(a,b)]) [] eqs_lst in
  let subs, eqs_lst = List.partition (fun (a,b) ->
      Gen.BList.mem_eq CP.eq_spec_var a quantif ||  Gen.BList.mem_eq CP.eq_spec_var b quantif 
    ) eqs_lst in 
  (* let eqs = List.map (fun (a,b) -> CP.mkEqVar a b no_pos) eqs_lst in *)
  (eqs_lst, subs)

let norm_abs_node h p xpure em =
  if (Imm.is_abs ~emap:em (get_imm h)) then
    let xpured, _, _ = x_add xpure h p 0 in (* 0 or 1? *)(* !!!! add the xpure to pure *)
    (HEmp, Some (MCP.pure_of_mix xpured))
  else
    (h, None)  

(* assume nodes are aliased *)
let merge_two_view_nodes prog vn1 vn2 h1 h2 quantif unfold_fun qvars emap =
  let comp, ret_h, _, guards = compatible_nodes prog vn1.h_formula_view_imm vn2.h_formula_view_imm h1 h2 unfold_fun qvars emap in
  let same_view = (String.compare vn1.h_formula_view_name vn2.h_formula_view_name = 0) in
  let comp_view =  same_view &&  not(Cfutil.is_view_node_segmented vn1 prog) in
  let () = x_tinfo_hp (add_str "view_is_segmented" string_of_bool) (Cfutil.is_view_node_segmented vn1 prog)  no_pos in
  (* comp_view ---> true when views are compatible (same view def + view def is not segmented) *)
  if comp  && comp_view then
    let (eqs, subs) = partition_eqs_subs vn1.h_formula_view_arguments vn2.h_formula_view_arguments quantif in
    ([ret_h], eqs, subs, [], [])                      (* should I also add the pure of merged (@A) node? *)
    (* ([], []) *)
  else
    (* let xpure1 =  *)
    (* remove node annotated with @A if it's not compatible for merging *)
  if (Imm.is_abs ~emap:emap vn1.h_formula_view_imm) then  ([h2], [], [], [], [])
  else if (Imm.is_abs ~emap:emap vn2.h_formula_view_imm) then  ([h1], [], [], [], [])
  else ([h1;h2], [], [], [], [])

(* assume nodes are aliased *)
let merge_data_node_w_view_node prog dn1 vn2 h1 h2 quantif unfold_fun qvars emap =
  let comp, ret_h, struc, guards = compatible_nodes prog dn1.h_formula_data_imm vn2.h_formula_view_imm h1 h2 unfold_fun qvars emap in
  if comp then
    (* let (eqs, subs) = partition_eqs_subs dn1.h_formula_data_arguments vn2.h_formula_view_arguments quantif in *)
    (* add here merge code *)
    match struc with
    | None   -> ([ret_h], [], [],[], [])  
    | Some s -> ([ret_h], [], [],[s], [])  
  else
  if (Imm.is_abs ~emap:emap dn1.h_formula_data_imm) then  ([h2], [], [], [], [])
  else if (Imm.is_abs ~emap:emap vn2.h_formula_view_imm) then  ([h1], [], [], [], [])
  else ([h1;h2], [], [], [], [])

let merge_data_node_w_view_node prog dn1 vn2 h1 h2 quantif unfold_fun qvars emap =
  let pr3 = Cprinter.string_of_h_formula in
  let pr1 d = pr3 (DataNode dn1) in
  let pr2 v = pr3 (ViewNode vn2) in
  let pr_out = pr_penta (pr_list pr3) pr_none pr_none pr_none pr_none in
  Debug.no_4 "merge_data_node_w_view_node" pr1 pr2 pr3 pr3 pr_out (fun _ _ _ _ -> merge_data_node_w_view_node prog dn1 vn2 h1 h2 quantif unfold_fun qvars emap) dn1 vn2 h1 h2

(* assume nodes are aliased *)
let merge_two_data_nodes prog dn1 dn2 h1 h2 quantif unfold_fun qvars emap =
  let comp, ret_h, _, guards = compatible_nodes prog dn1.h_formula_data_imm dn2.h_formula_data_imm h1 h2 unfold_fun qvars emap in
  let comp_data = comp && (String.compare dn1.h_formula_data_name dn2.h_formula_data_name = 0) in
  if comp_data then
    let (eqs, subs) = partition_eqs_subs dn1.h_formula_data_arguments dn2.h_formula_data_arguments quantif in
    ([ret_h], eqs, subs, [], guards)
  else
  if (Imm.is_abs ~emap:emap dn1.h_formula_data_imm) then  ([h2], [], [], [], [])
  else if (Imm.is_abs ~emap:emap dn2.h_formula_data_imm) then  ([h1], [], [], [],[])
  else ([h1;h2], [], [], [],[])

(* merged two nodes and return merged node and resulted equalities. *)
let merge_two_nodes h1 h2 prog quantif unfold_fun qvars emap =
  match h1, h2 with
  | [(DataNode dn1) as h1], DataNode dn2  -> merge_two_data_nodes prog dn1 dn2 h1 h2 quantif unfold_fun qvars emap
  | [(ViewNode vn) as h2], ((DataNode dn) as h1)
  | [(DataNode dn) as h1], ((ViewNode vn) as h2) ->  merge_data_node_w_view_node prog dn vn h1 h2 quantif unfold_fun qvars emap (* ([h1;h2], []) *)
  | [(ViewNode vn1) as h1], ViewNode vn2 -> merge_two_view_nodes prog vn1 vn2 h1 h2 quantif unfold_fun qvars emap
  (* ([h1;h2], []) *)
  | _, _ -> (h1@[h2], [], [], [],[])

(* let get_node_var h =  *)

let defined_node h1 = 
  match h1 with
  | DataNode _
  | ViewNode _
  | ThreadNode _ -> true
  | _ -> false

let aliased_nodes h1 h2 emap =
  if (defined_node h1) && (defined_node h2) then
    CP.EMapSV.is_equiv emap (get_node_var h1) (get_node_var h2)
  else
    false                               (* assume that if node is undefined, it does not have an aliased *)

let merge_list_w_node node lst emap prog quantif unfold_fun qvars = 
  let aliases, disj = List.partition (fun n -> aliased_nodes node n emap) lst in 
  let new_h, eqs, subs, structs, pfs = List.fold_left (fun (a, e, s, structs, pfs) n -> 
      let merged, eqs, subs, struc, pf =  merge_two_nodes a n prog quantif unfold_fun qvars emap in
      (merged, e@eqs, subs@s, struc@structs, pf@pfs)
    ) ([node],[], [], [], []) aliases in (* here!! *)
  (new_h, disj, eqs, subs, structs, pfs)

let merge_alias_nodes_h_formula_helper prog p lst emap quantif xpure unfold_fun qvars =
  let rec helper lst emap = 
    match lst with 
    | []   -> ([], [], [], true, [], [])
    (* | [h]  -> let new_h, pure = norm_abs_node h p xpure in  *)
    (*   ([new_h], (opt_to_list pure)) *)  (* andreeac: uncomment this 2 lines if you wnat to replace @A node with HEmp & xpure*)
    | h::t ->
      (* TODOIMM to merge tmpann as a special case *)
      let updated_head, updated_tail, eqs_lst, subs_lst, struc_lst, pf_lst = merge_list_w_node h t emap prog quantif unfold_fun qvars in
      let (fixpoint, emap) = List.fold_left 
          ( fun (fixpoint,emap) (a,b) -> 
             if CP.EMapSV.is_equiv emap a b then (fixpoint&&true,emap)
             else (fixpoint&&false, CP.EMapSV.add_equiv emap a b) 
          ) (true, emap) eqs_lst in
      let fixpoint = fixpoint && (is_empty subs_lst) in
      let merged_tail, eqs_lst_tail, subs_lst_tail, fixpoint_tail, struc_tail, pf_tail = helper updated_tail emap  in
      (updated_head@merged_tail, eqs_lst@eqs_lst_tail, subs_lst@subs_lst_tail, fixpoint&&fixpoint_tail, struc_lst@struc_tail, pf_lst@pf_tail) in
  helper lst emap

(* merge aliased nodes 
 * return merged node and resulted qualities. *)
let merge_alias_nodes_h_formula prog f p emap quantif xpure unfold_fun qvars = (* f *)
  match f with
  | Star _ ->
    let node_lst = split_star_h f in
    let node_lst, eqs, subs, fixpoint, struc, pf = merge_alias_nodes_h_formula_helper prog p node_lst emap quantif xpure unfold_fun qvars in
    let updated_f = combine_star_h node_lst in
    let eqs = List.map (fun (a,b) -> CP.mkEqVar a b no_pos) eqs in
    let aux_pure  = CP.join_conjunctions eqs in
    (* substitute non-global variables in conseq *)
    let fr, t = List.split subs in
    let updated_f = subst_avoid_capture_h fr t updated_f in
    let new_pure = MCP.memoise_add_pure p aux_pure in
    let new_pure = MCP.memoise_add_pure new_pure (CP.join_conjunctions pf) in
    let new_pure = MCP.subst_avoid_capture_memo fr t new_pure in
    (updated_f, new_pure, fixpoint, struc)
  (* | DataNode _ | ViewNode _ ->  *)   (* andreeac: uncommnet this line if you wnat to replace @A node with HEmp & xpure*)
  (*   let new_h, new_pf = norm_abs_node f p xpure emap in *)
  (*   let new_pf = map_opt_def p (MCP.memoise_add_pure p) new_pf in *)
  (*   (new_h, new_pf, true, []) *)
  | _ -> (f, p, true, [])

let merge_alias_nodes_h_formula prog f p emap quantif xpure unfold_fun qvars = 
  let pr1 = Cprinter.string_of_h_formula in
  let pr2 = Cprinter.string_of_mix_formula in
  let pr3 = Cprinter.string_of_formula in
  Debug.no_2 "merge_alias_nodes_h_formula"  pr1 pr2 
    (pr_quad (add_str "heap" pr1) (add_str "pure" pr2) string_of_bool ( add_str "unfold formula" (pr_list pr3))) 
    (fun _ _ -> merge_alias_nodes_h_formula prog f p emap quantif xpure unfold_fun qvars) f p

let merge_alias_nodes_formula_helper prog heapf puref quantif xpure unfold_fun qvars =
  let rec helper heapf puref = 
    let (subs,_) = CP.get_all_vv_eqs (MCP.pure_of_mix puref) in
    (* let emap = CP.EMapSV.build_eset subs in *)
    let emap = Imm.build_eset_of_imm_formula (MCP.pure_of_mix puref) in
    let new_f, new_p, fixpoint, struc = x_add merge_alias_nodes_h_formula prog heapf puref emap quantif xpure unfold_fun qvars in
    (* let new_p = *)
    (*   match new_p with *)
    (*     | Some p -> MCP.memoise_add_pure puref p *)
    (*     | None   -> puref in *)
    if not fixpoint then helper new_f new_p
    else (new_f, new_p, struc)
  in helper heapf puref

(* let merge_alias_h_formula prog heap pure quantif xpure unfold_fun qvars = *)
(*   merge_alias_nodes_formula_helper prog heap pure quantif xpure (unfold_fun fl) qvars *)

let merge_and_combine prog f heap pure quantif xpure unfold_fun qvars mk_new_f rec_fun =
  let _, _, vperm, fl, _, a = split_components f in
  let pos = pos_of_formula f in
  let new_h, new_p, unfold_f_lst = merge_alias_nodes_formula_helper prog heap pure quantif xpure (unfold_fun fl qvars vperm pure a) qvars in
  let new_f =  mk_new_f new_h new_p in
  let ret_f = match unfold_f_lst with
    | [] -> new_f
    | _  ->
      let f = List.fold_left (fun acc f-> normalize_combine_star acc f pos) new_f unfold_f_lst in
      rec_fun f
  in ret_f 

let merge_alias_nodes_formula prog f quantif xpure unfold_fun =
  let rec helper f =
    let fl  = flow_formula_of_formula f in 
    let pos = pos_of_formula f in
    match f with
    | Base bf ->
      let mk_base f p = Base { bf with formula_base_heap = f;  formula_base_pure = p; } in
      merge_and_combine prog f bf.formula_base_heap bf.formula_base_pure quantif xpure unfold_fun [] mk_base helper
    | Exists ef ->
      let qvars = ef.formula_exists_qvars in
      let mk_exists f p =  Exists{ef with formula_exists_heap = f;  formula_exists_pure = p; } in
      merge_and_combine prog f ef.formula_exists_heap ef.formula_exists_pure quantif xpure unfold_fun qvars mk_exists helper
    | Or orf -> 
      Or {orf with formula_or_f1 = helper orf.formula_or_f1;  formula_or_f2 = helper orf.formula_or_f2;}
  in
  if not ((* !Globals.allow_field_ann *) !Globals.imm_merge) then f
  else helper f

let merge_alias_nodes_formula prog f quantif xpure unfold_fun =
  let pr = Cprinter.string_of_formula in
  Debug.no_1 "merge_alias_nodes_formula" pr pr (fun _ -> merge_alias_nodes_formula prog f quantif xpure unfold_fun) f

let rec merge_alias_nodes_struc_formula prog f xpure conseq unfold_fun =
  let res =
    match f with
    | EBase f ->
      let (ee, ei) = (f.formula_struc_exists, f.formula_struc_explicit_inst) in
      let quantif = if conseq then ee@ei@f.formula_struc_implicit_inst else [] in
      EBase {f with
             formula_struc_base =  x_add merge_alias_nodes_formula prog f.formula_struc_base quantif xpure unfold_fun}
    | EList l   -> EList  (map_l_snd (fun c-> merge_alias_nodes_struc_formula prog c xpure conseq unfold_fun) l)
    | ECase f   -> ECase {f with formula_case_branches = map_l_snd (fun c-> merge_alias_nodes_struc_formula prog c xpure conseq unfold_fun) f.formula_case_branches;}
    | EAssume f -> 
      EAssume {f with
               formula_assume_simpl = x_add merge_alias_nodes_formula prog f.formula_assume_simpl [] xpure unfold_fun;
               formula_assume_struc = merge_alias_nodes_struc_formula prog f.formula_assume_struc xpure conseq unfold_fun;}
    | EInfer f  -> EInfer {f with formula_inf_continuation = merge_alias_nodes_struc_formula prog f.formula_inf_continuation xpure conseq unfold_fun }
  in if not ((* !Globals.allow_field_ann *) !Globals.imm_merge) then f
  else res

let merge_alias_nodes_struc_formula prog f xpure conseq  unfold_fun =
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_1 "merge_alias_nodes_struc_formula" pr pr (fun _ -> merge_alias_nodes_struc_formula prog f xpure conseq  unfold_fun) f

(* ===============================  end - merging aliased nodes ================================= *)

(* ==================== norm inferred pre/post ======================== *)

let f_norm_pre_imm_var e l = CP.mkEq e (CP.AConst (Lend, l)) l

let f_norm_post_imm_var e l = CP.mkEq e (CP.AConst (Accs, l)) l

let norm_candidate sv aset vars = (CP.is_ann_typ sv) (* && (CP.EMapSV.mem sv vars) *) && (Imm.is_lend_sv ~emap:aset sv) 

let is_post sv post_vars = CP.EMapSV.mem sv post_vars

let norm_post_formula_helper (sv1,l1) (sv2,l2) vars_post aset =
  (* check if var type is ann *)  (* check if is post var *)  (* check if var is equiv to @L *)
  let helper sv l =
    if norm_candidate sv aset vars_post then 
      if is_post sv vars_post then  [f_norm_post_imm_var (CP.Var (sv,l)) l]  (* post var ---> sv=@A *)
      else [f_norm_pre_imm_var (CP.Var (sv,l)) l]                            (* pre var  ---> sv=@L *)
    else [] in
  let sv1 = helper sv1 l1  in
  let sv2 = helper sv2 l2 in
  sv1@sv2

let norm_subann sv1 e1 e2 loc vars_post aset =
  match e2 with
  | CP.AConst (Lend, _) ->
    let pos_var = CP.EMapSV.mem sv1 vars_post in
    let res_ex = if pos_var then f_norm_post_imm_var e1 loc else f_norm_pre_imm_var e1 loc in
    ([res_ex], false)
  | CP.AConst _ ->
    let res_ex = CP.mkEq e1 e2 loc in
    ([res_ex], true)
  | CP.Var (sv, _) ->
    if (Imm.is_lend_sv ~emap:aset sv) then ([f_norm_pre_imm_var e1 loc], false)
    else ([], true)
  | _ -> ([], true)

let norm_eq e1 e2 loc vars_post aset =
  match e1,e2 with
  | CP.Var (sv1, loc1), CP.Var (sv2, loc2) ->
    let res = norm_post_formula_helper (sv1,loc1) (sv2,loc2) vars_post aset in
    map_list_def ([],true) (fun x -> (x,false)) res
  | (CP.Var (sv, loc) as e), CP.AConst (Lend, _) 
  | CP.AConst (Lend, _), (CP.Var (sv, loc) as e)->
    let pos_var = CP.EMapSV.mem sv vars_post in
    let res_ex, fix = if pos_var then (f_norm_post_imm_var e loc, false) 
      else (f_norm_pre_imm_var e loc, true) in
    ([res_ex], fix)
  | _ -> ([], true)

(* let norm_imm_rel_formula vars_post (rel:CP.formula) : CP.formula  = rel *)
(* a<:@L ---> a=@L (for pre vars) / @L<:a ---> a=@A (for post vars) *)
let norm_imm_rel_one_disj vars_post (rel:CP.formula) (rel_f:CP.formula): CP.formula  =
  (* let rel = TP.simplify_tp rel in *)
  let fixpt = ref true in

  let f_b aset b = 
    let (p_f, bf_ann) = b in
    let p_f = 
      match p_f with
      | CP.SubAnn (((CP.Var(sv1,l1)) as e1),((CP.AConst _) as e2),l) 
      | CP.SubAnn (((CP.AConst _) as e2),((CP.Var(sv1,l1)) as e1),l) ->
        let res_ex, fix = norm_subann sv1 e1 e2 l vars_post aset in
        let () = if not fix then fixpt := false else () in
        map_list_def [p_f] (fun x -> x) res_ex
      | CP.SubAnn (((CP.Var(sv1,l1)) as e1),((CP.Var(sv2,l2)) as e2),l) ->
        let res_ex, fix = if CP.EMapSV.mem sv1 vars_post then  norm_subann sv1 e1 e2 l2 vars_post aset 
          else if CP.EMapSV.mem sv2 vars_post then  norm_subann sv2 e2 e1 l2 vars_post aset 
          else [p_f], true
        in
        let () = if not fix then fixpt := false else () in
        map_list_def [p_f] (fun x -> x) res_ex
      | CP.Eq (e2,e1,l)-> 
        let res_ex, fix = norm_eq e1 e2 l vars_post aset in
        let () = if not fix then fixpt := false else () in
        map_list_def [p_f] (fun x -> x) res_ex
      | _ -> [p_f]
    in
    (p_f, bf_ann) in

  let rec f_f emap f =
    match f with
    | CP.BForm (b1,b2) ->  
      (* below is needed in case we need to transform [a=b] --> [a=@A & b=@L] *)
      let res_lst, bf_ann = f_b emap b1 in (* TODOIMM revise this *)
      let new_f = 
        match res_lst with
        | []   -> f
        | [b1] -> CP.BForm ((b1,bf_ann) ,b2)
        | h::t -> List.fold_left (fun acc b -> CP.And (acc, CP.BForm ((b,bf_ann), b2), no_pos )) (CP.BForm ((h,bf_ann),b2)) t in
      Some new_f
    | Or (e1,e2,lbl,l) ->
      let emap1 = CP.EMapSV.merge_eset emap (Imm.build_eset_of_imm_formula e1) in
      let e1 = CP.map_formula_arg e1 emap1 (f_f, somef2, somef2) (idf2, idf2, idf2) in
      let emap2 = CP.EMapSV.merge_eset emap (Imm.build_eset_of_imm_formula e2) in
      let e2 = CP.map_formula_arg e2 emap2 (f_f, somef2, somef2) (idf2, idf2, idf2) in
      Some (Or (e1,e2,lbl,l))
    | Not (f, lbl, l) ->
      let emap = CP.EMapSV.merge_eset emap (Imm.build_eset_of_imm_formula f) in
      let f = CP.map_formula_arg f emap (f_f, somef2, somef2) (idf2, idf2, idf2) in
      Some ( Not (f, lbl, l))
    | _ -> None
  in

  (* systematically transform formula until all a<:@L ---> a=@L *)
  let rec helper rel = 
    let p_aset = Imm.build_eset_of_imm_formula rel in
    let rel = CP.map_formula_arg rel p_aset (f_f, somef2, somef2) (idf2, idf2, idf2) in
    if not(!fixpt) then begin fixpt := true; helper rel end
    else rel in
  helper  rel_f

let norm_imm_rel_formula vars_post (rel:CP.formula) (rel_f:CP.formula): CP.formula  =
  let imm_p, pure = split_imm_pure_lst rel_f in
  let pure = CP.join_disjunctions pure in
  let imm_p = List.map TP.simplify_tp imm_p in
  let imm_p = List.map (norm_imm_rel_one_disj vars_post rel) imm_p in
  let new_imm_p = CP.join_conjunctions imm_p in
  let simp_imm_p = TP.simplify_tp new_imm_p in
  let final_imm_p = 
    if not(CP.is_False simp_imm_p) then simp_imm_p
    else (CP.join_disjunctions imm_p) in (* TODOIMM - revise here to weaken/streanghten *)
  CP.join_conjunctions [final_imm_p;pure]

let norm_imm_rel_formula ?post_vars:(vars_post=[]) ?rel_head:(rel=CP.mkTrue no_pos) (rel_f:CP.formula) : CP.formula  = 
  let pr = Cprinter.string_of_pure_formula in
  let pr_lst = Cprinter.string_of_spec_var_list in
  Debug.no_3 "norm_imm_rel_formula" pr_lst pr pr pr norm_imm_rel_formula vars_post rel rel_f

(* let weaken_imm_rel_formula ?post_vars:(vars_post=[]) (rel:CP.formula) : CP.formula  = *)
(*   let pr = Cprinter.string_of_pure_formula in *)
(*   let pr_lst = Cprinter.string_of_spec_var_list in *)
(*   Debug.no_2 "weaken_imm_rel_formula" pr_lst pr pr  weaken_imm_rel_formula vars_post rel *)

let norm_fn (rel_ct,rel1,rel2) =
      match rel_ct with
      | CP.RelAssume _ -> 
        let rel2 = (* x_add_1 *) norm_imm_rel_formula ~rel_head:rel1 rel2  in
        (rel_ct, rel1, rel2)
      | _ -> (rel_ct,rel1,rel2) 

let norm_rel_list lst =
  List.map norm_fn lst
    (* (fun (rel_ct,rel1,rel2) -> *)
    (*   match rel_ct with *)
    (*   | CP.RelAssume _ ->  *)
    (*     let rel2 = (\* x_add_1 *\) norm_imm_rel_formula ~rel_head:rel1 rel2  in *)
    (*     (rel_ct, rel1, rel2) *)
    (*   | _ -> (rel_ct,rel1,rel2)  *)
    (* ) lst *)

let weaken_infer_rel_in_es es =
  let () =  es.es_infer_rel # map norm_fn in
  es
(* below to move to immutable *)
let is_imm_relation pure = 
  if not(CP.is_RelForm pure) then false
  else 
    let fv = CP.fv_wo_rel pure in
    List.for_all CP.is_ann_typ fv

let is_imm_relation pure = 
   let pr = Cprinter.string_of_pure_formula in
   Debug.no_1 "is_imm_relation" pr string_of_bool is_imm_relation pure

let get_relevant rels oblg = (* true *)
  let fv = CP.fv rels in
  let oblg =  CP.filter_var_new oblg fv in
  oblg

(* splits an obligation which is a combination of pure and imm relation, 
   into pure obligations and imm obligations  *)
let split_rel rel =
  match rel with
    | CP.RelAssume svl, p1, p2  -> 
          if List.length svl > 1 then
            let p1_conj = CP.split_conjunctions p1 in
            let p1_imm, p1_pure = List.partition is_imm_relation p1_conj in
            if (List.length p1_imm == 0 || List.length p1_pure == 0) then [rel]
            else
              let p1_imm = CP.join_conjunctions p1_imm in
              let p1_pure = CP.join_conjunctions p1_pure in
              let p2_imm, p2_pure = split_imm_pure_lst p2 in
              let p2_imm_relev = List.map (get_relevant p1_imm) p2_imm in
              let p2_pure_relev = List.map (get_relevant p1_pure) p2_pure in
              let p2_imm = CP.join_disjunctions p2_imm_relev in 
              let p2_pure = CP.join_disjunctions p2_pure_relev in 
              let svl_imm, svl_pure = List.partition (fun x -> CP.EMapSV.mem x (CP.fv p1_imm)) svl in
              [CP.RelAssume svl_imm, p1_imm, p2_imm; CP.RelAssume svl_pure, p1_pure, p2_pure ]
          else [rel] 
    | _ -> [rel]

let split_rel rel =
  let pr = Cprinter.string_of_pure_formula in
  let pr_oblg = (fun (_,a,b) -> pr_pair pr pr (a,b)) in
  Debug.no_1 "split_rel"  pr_oblg (pr_list pr_oblg) split_rel rel

let norm_rel_oblgs reloblgs =
  let is_rel_eq rel1 rel2 = 
    (fun (r1,a1,_) (r2,a2,_) ->  
       if not(CP.is_RelForm a1 && CP.is_RelForm a2) then false
       else try
           let get_ids f = map_opt_def [] (fun (id, args) -> id::args) (CP.get_relargs_opt f) in
           let ids =  List.combine (get_ids a1) (get_ids a2) in 
           List.fold_left (fun acc (sv1, sv2) -> acc && (CP.eq_spec_var sv1 sv2 )) true ids
         with _ -> false
    ) rel1 rel2 in
  let rec update_acc ((a1,b1,c1) as rel) acc =
    match acc with
    | []   -> [rel]
    | ((a2,b2,c2) as h)::t -> if is_rel_eq rel h then (a1,b1, CP.mkAnd c1 c2 no_pos)::t
      else h::(update_acc rel t)
  in
  let rec helper lst acc = 
    let fnc acc lst = 
      let acc = update_acc (List.hd lst) acc in 
      helper (List.tl lst) acc in
    map_list_def acc (fnc acc) lst
  in
  let reloblgs_new = List.fold_left (fun acc rel -> (split_rel rel)@acc) [] reloblgs in (* split mixed rels *)
  let reloblgs_new = helper reloblgs_new [] in
  let reloblgs_new = List.map (fun ((rel_c,rel_n,rel_d) as rel) -> 
      if CP.contains_undef rel_d then rel 
      else (rel_c, rel_n, imm_unify ((* TP.simplify_tp *) rel_d))) reloblgs_new  in
  reloblgs_new

let norm_rel_oblgs reloblgs =
  let pr = Cprinter.string_of_pure_formula in
  let pr_oblg = pr_list (fun (_,a,b) -> pr_pair pr pr (a,b)) in
  Debug.no_1 "norm_rel_oblgs" pr_oblg pr_oblg norm_rel_oblgs reloblgs

let norm_reloblgs_and_init_defs reloblgs =
  (* norm *)
  let reloblgs = norm_rel_oblgs reloblgs in
  (* init defs *)
  let reloblgs_new, reldefs = List.partition (fun (_,_,rel_d) -> CP.contains_undef rel_d) reloblgs in 
  let reldefs = List.map (fun (_,a,b) -> (b,a)) reldefs in
  reloblgs, reldefs

let norm_reloblgs_and_init_defs reloblgs =
  let pr = Cprinter.string_of_pure_formula in
  let pr_def = pr_list (pr_pair pr pr) in
  let pr_oblg = pr_list (fun (_,a,b) -> pr_pair pr pr (a,b)) in
  Debug.no_1 "norm_reloblgs_and_init_defs" pr_oblg 
    (pr_pair (add_str "norm reloblgs:" pr_oblg) (add_str "new defs:" pr_def))
    norm_reloblgs_and_init_defs reloblgs

(* ==================== END norm inferred pre/post ======================== *)

(* imm related normalization before enatiling an empty heap rhs *)
let imm_norm_for_entail_empty_rhs lhs_h lhs_p es = 
  let lhs_h = x_add_1 restore_tmp_ann_h_formula lhs_h lhs_p in
  let es    = x_add_1 restore_tmp_ann_es es in
  let lhs_h = x_add_1 restore_lend_h_formula lhs_h in
  let es    = x_add_1 restore_lend_es es in
  (lhs_h, es)

let imm_norm_for_entail_empty_rhs lhs_h lhs_p es = 
  let pr1 = Cprinter.string_of_h_formula in
  let pr2 = Cprinter.string_of_mix_formula in
  let pr3 = Cprinter.string_of_entail_state_short in
  let pr_out = pr_pair (add_str "lhs_h" pr1) (add_str "lhs_p" pr3) in
  Debug.no_3 "imm_norm_for_entail_empty_rhs" (add_str "lhs_h" pr1) (add_str "lhs_p" pr2) (add_str "es" pr3) pr_out imm_norm_for_entail_empty_rhs lhs_h lhs_p es 

let imm_post_process_for_entail_empty_rhs ctx = 
  let ctx = x_add_1 restore_tmp_ann_list_ctx ctx in
  let ctx = x_add_1 restore_lend_list_ctx ctx in
  ctx

let imm_post_process_for_entail_empty_rhs ctx = 
  let pr = Cprinter.string_of_list_context_short in 
  Debug.no_1 "imm_post_process_for_entail_empty_rhs" pr pr imm_post_process_for_entail_empty_rhs ctx

let infer_specs_imm_post_process (spec: CF.struc_formula) : CF.struc_formula =
  (* define data struc functions *)

  let f_pre rel = Some (norm_imm_rel_formula rel)  in
  let f_post vars_post rel = Some (norm_imm_rel_formula ~post_vars:vars_post rel) in

  let f_none = fun _ -> None in
  let f_f = f_none in
  let f_h_f = f_none in
  let f_p_pre = (f_none, f_none, f_pre, f_none, f_none) in
  let f_p_post vars_post = (f_none, f_none, (f_post vars_post), f_none, f_none) in
  let fncs = (f_none, f_f, f_h_f, f_p_pre) in

  let rec helper fncs sf =
    match sf with 
    | CF.ECase f   -> 
      let br = List.map (fun (c1,c2)-> (c1, (helper fncs c2))) f.CF.formula_case_branches in
      CF.ECase {f with CF.formula_case_branches = br;}
    | CF.EBase f   -> 
      CF.EBase {f with 
                CF.formula_struc_base = CF.transform_formula fncs f.CF.formula_struc_base;
                CF.formula_struc_continuation = map_opt (helper fncs) f.CF.formula_struc_continuation;}
    | CF.EAssume f -> 
      (* from here onwards is the post spec formula *)
      let post_vars = Gen.BList.difference_eq (CP.eq_spec_var) (CF.struc_all_vars sf) (CF.struc_fv sf) in
      (* below is needed so that we first normalize everything to @L, before distinguishing between pre and post vars *)
      let simpl_f = CF.transform_formula fncs f.CF.formula_assume_simpl in
      let struc_f = helper fncs f.CF.formula_assume_struc in

      let fncs = (f_none, f_f, f_h_f, (f_p_post post_vars)) in
      CF.EAssume {f with 
                  CF.formula_assume_simpl = CF.transform_formula fncs simpl_f;
                  CF.formula_assume_struc = helper fncs struc_f;}
    | CF.EInfer f  -> 
      CF.EInfer {f with formula_inf_continuation = helper fncs f.CF.formula_inf_continuation;}
    | CF.EList f   -> CF.EList (map_l_snd (helper fncs) f)
  in
  let spec = helper fncs spec in
  spec

(* let strenghten_disj lst_disj = *)
(*   (\* all fv in the disjunctions *\) *)
(*   let fv_lst = List.fold_left (fun acc x -> acc@(CP.fv x)) [] lst_disj in *)
(*   let fv_lst = Gen.BList.remove_dups_eq CP.eq_spec_var fv_lst in *)
(*   (\* search for fv=const for all fv *\) *)
(*   let fv_guards = List.map (fun sv_x -> *)
(*       let eqs = List.fold_left (fun acc pure -> (get_imm_from_pure_ann_list sv_x pure)@acc) [] lst_disj in *)
(*       let imm = get_strongest_imm eqs in *)
(*       map_opt_def () (fun x -> ) imm *)
(*       (\* TODOIMM  *\) *)
(*     ) fv_lst in *)
  
let postprocess_post post post_f pre_vars = 
  let post_var = Gen.BList.difference_eq CP.eq_spec_var (CP.all_vars post) pre_vars in
  norm_imm_rel_formula ~post_vars:post_var ~rel_head:post post_f

let postprocess_post post post_f pre_vars = 
  let pr = !CP.print_formula in
  Debug.no_3 "postprocess_post" pr pr Cprinter.string_of_spec_var_list pr postprocess_post post post_f pre_vars

let postprocess_pre pre pre_f = norm_imm_rel_formula  ~rel_head:pre pre_f

let postprocess_pre pre pre_f =
  let pr = !CP.print_formula in
  Debug.no_2 "postprocess_pre" pr pr !CP.print_formula postprocess_pre pre pre_f

(* ======================= remove absent nodes ============================= *)
(* TODOIMM need to investigate if removing an absent node means i need to add its xpure to the pure part *)
(*
let remove_abs_nodes_h_formula emap h =
  let helper h =
    else
      match h with
      | CF.DataNode { CF.h_formula_data_imm = imm; CF.h_formula_data_param_imm = param_imm;} ->
        let heap = if (not !Globals.allow_field_ann) && (Imm.is_abs ~emap:emap imm) then HEmp 
          else if (!Globals.allow_field_ann) && (Imm.is_abs_list ~emap:emap param_imm) then HEmp else h
        in Some heap
      | CF.ViewNode { CF.h_formula_view_imm = imm; CF.h_formula_view_annot_arg = annot_arg; } ->
        let pimm = (CP.annot_arg_to_imm_ann_list_no_pos annot_arg) in
        let heap =  if (not !Globals.allow_field_ann) && (Imm.is_abs ~emap:emap imm) then HEmp 
          else if (!Globals.allow_field_ann) && (Imm.is_abs_list ~emap:emap pimm) then HEmp else h
        in Some heap
      |_ -> None in
  let h = CF.transform_h_formula helper h in h

let remove_abs_nodes_h_formula emap h =
  let pr = Cprinter.string_of_h_formula in
  let pr2 = CP.EMapSV.string_of in
  Debug.no_2 "remove_abs_nodes_h_formula" pr2 pr pr remove_abs_nodes_h_formula emap h
*)
let remove_abs_nodes_and_collect_imm_h_formula emap h =
  let helper _ h =
    let sv_of ann args =
      List.fold_right (fun ann acc -> match ann with CP.PolyAnn sv -> sv::acc | _ -> acc) (ann::(List.map CP.mkPolyAnn args)) [] in
    match h with
    | CF.DataNode { CF.h_formula_data_imm = imm; CF.h_formula_data_param_imm = param_imm; CF.h_formula_data_arguments = args } ->
       let (heap, ann) = if (not !Globals.allow_field_ann) && (Imm.is_abs ~emap:emap imm) then (HEmp, sv_of imm args)
                         else if (!Globals.allow_field_ann) && (Imm.is_abs_list ~emap:emap param_imm) then (HEmp, sv_of imm args) else (h, [])
       in Some (heap, ann)
    | CF.ViewNode { CF.h_formula_view_imm = imm; CF.h_formula_view_annot_arg = annot_arg; CF.h_formula_view_arguments = args } ->
       let pimm = (CP.annot_arg_to_imm_ann_list_no_pos annot_arg) in
       let (heap, ann) = if (not !Globals.allow_field_ann) && (Imm.is_abs ~emap:emap imm) then (HEmp, sv_of imm args)
                         else if (!Globals.allow_field_ann) && (Imm.is_abs_list ~emap:emap pimm) then (HEmp, sv_of imm args) else (h, [])
       in Some (heap, ann)
    |_ -> None in
  CF.trans_h_formula h [] helper (fun x _ -> x) List.concat

let remove_abs_nodes_and_collect_imm_h_formula emap h =
  let pr = Cprinter.string_of_h_formula in
  let pr2 = CP.EMapSV.string_of in
  let pr3 = pr_pair pr Cprinter.string_of_spec_var_list in
  Debug.no_2 "remove_abs_nodes_and_collect_imm_formula" pr2 pr pr3
             remove_abs_nodes_and_collect_imm_h_formula emap h

let remove_abs_nodes_formula_helper form =
  let emap = Imm.build_eset_of_imm_formula (CF.get_pure_ignore_exists form) in
  let exp_to_eq_a not_relevant e = match e with
    | CP.Var (sv, loc) -> Some (if CP.EMapSV.mem sv not_relevant then CP.AConst(Accs,loc) else e)
    | _ -> None in
  let prune_a_eq_a formula =
    let aux = function
      | CP.BForm ((CP.Eq (CP.AConst (Accs,_), CP.AConst (Accs, _), _),_),_) -> None
      | CP.BForm ((CP.Eq ((CP.AConst (Accs,_)) as a, ((CP.Var _) as b), x),y),z) ->
         Some (CP.BForm ((CP.Eq (b,a,x),y),z))
      | s -> Some s in
    let prune_a_eq_a_d disjunct =
      let conjuncts = CP.split_conjunctions disjunct in
      CP.join_conjunctions (List.fold_right (fun f acc -> map_opt_def acc (fun f -> f::acc) (aux f))
                                            conjuncts []) in
    let disjuncts = CP.split_disjunctions formula in
    CP.join_disjunctions (List.map prune_a_eq_a_d disjuncts) in
  let transform_heap_and_pure heap pure =
    let () = x_ninfo_hp (add_str "pure" (!CP.print_formula)) (CF.get_pure_ignore_exists form) no_pos in
    let (new_heap, not_relevant) = remove_abs_nodes_and_collect_imm_h_formula emap heap in
    let new_pure = MCP.update_pure_of_mix (fun pure ->
      let new_pure_1 = CP.transform_formula (nonef, nonef, nonef, nonef, exp_to_eq_a not_relevant) pure in
      Some(prune_a_eq_a new_pure_1)) pure in
    (new_heap, new_pure, not_relevant)
  in
  match form with
  | CF.Base b ->
     let (new_heap, new_pure, _) = transform_heap_and_pure b.CF.formula_base_heap b.CF.formula_base_pure in
     Some (CF.Base{ b with
                    CF.formula_base_heap = new_heap;
                    CF.formula_base_pure = new_pure })
  | CF.Exists e -> 
     let (new_heap, new_pure, svl) = transform_heap_and_pure e.CF.formula_exists_heap e.CF.formula_exists_pure in
     let removed_qvars = List.filter (fun s -> List.mem s svl) e.CF.formula_exists_qvars in
     (match (CF.remove_quantifiers removed_qvars form) with
      | CF.Base b ->
         Some (CF.Base { b with
                         CF.formula_base_heap = new_heap;
                         CF.formula_base_pure = new_pure})
      | CF.Exists e ->
         Some (CF.Exists { e with
                           CF.formula_exists_heap = new_heap;
                           CF.formula_exists_pure = new_pure })
      | CF.Or _ -> None)
  | CF.Or _ -> None

let remove_abs_nodes_formula formula =
  if (not !Globals.remove_abs) then formula else
  let fnc = (nonef, remove_abs_nodes_formula_helper, nonef, (somef,somef,somef,somef,somef)) in
  CF.transform_formula fnc formula

let remove_abs_nodes_struc struc =
  if (not !Globals.remove_abs) then struc else
  let fnc = (nonef, remove_abs_nodes_formula_helper, nonef, (somef,somef,somef,somef,somef)) in
  CF.transform_struc_formula fnc struc 

let remove_abs_nodes_struc struc = 
  let pr = Cprinter.string_of_struc_formula in
  Debug.no_1 "remove_abs_nodes_struc" pr pr remove_abs_nodes_struc struc

(* ======================= END remove absent nodes ============================= *)

(* ======================= prover pre/post-process  ============================= *)

let f_bf bf =
  let (pf, l) = bf in
  TP.cnv_imm_to_int_p_formula pf l

let f_e e = x_add_1 TP.cnv_imm_to_int_exp e

let fnc_pure = (nonef,nonef,nonef,f_bf,f_e)

let fnc = (nonef, nonef, nonef, fnc_pure )

let map_imm_to_int_pure_formula form = 
  (* let form = x_add_1 Immutils.simplify_imm_addition form in *)
  let form = x_add_1 Immutils.simplify_imm_min_max form in
  CP.transform_formula fnc_pure form

let map_imm_to_int_pure_formula form = 
  let pr = !CP.print_formula in
  Debug.no_1 "map_imm_to_int_pure_formula" pr pr map_imm_to_int_pure_formula form

let map_imm_to_int_formula form = CF.transform_formula fnc form

let map_imm_to_int_struc_formula form = CF.transform_struc_formula fnc form

let f_bf bf =
  let (pf, l) = bf in
  TP.change_to_imm_rel_b_formula pf l

let f_e e = Some e

let fnc_pure = (nonef,nonef,nonef,f_bf,f_e)

let fnc = (nonef, nonef, nonef, fnc_pure)

let map_int_to_imm_pure_formula form = CP.transform_formula fnc_pure form

let map_int_to_imm_pure_formula form =
  let pr = !CP.print_formula in
  Debug.no_1 "map_int_to_imm_pure_formula" pr pr map_int_to_imm_pure_formula form

let map_int_to_imm_formula form = CF.transform_formula fnc form

let map_int_to_imm_struc_formula form = CF.transform_struc_formula fnc form


(* ======================= END prover pre/post-process  ============================= *)


