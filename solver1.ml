open Globals

module CF = Cformula
module CP = Cpure
module MCP = Mcpure
module TP = Tpdispatcher

exception Solver_exception of string

(* 
 * The fragment of SL used in APLAS's paper is 
 *     next(x,y)  
 *     lseg(x,y,n) 
 * --------------
 * Data & predicate definition in Sleek 
 *     data node { 
 *       node next;
 *     } 
 *  
 *     pred lseg<x,n> == self = x & n = 0 
 *                       or sefl::node<p> * p::lseg<x,n-1> & self != x 
 *       inv n >= 0;
 * --------------
 * Translating APLAS paper's predicate to Sleek's predicate: 
 *    next(x,y)     ---->   x::node<y> 
 *    lseg(x,y,n)   ---->   x::lseg<y,n> 
 * 
 *)

(*
 * Obtain information of the primitive predicate "next(x,y)"
 * In Sleek it is modeled by a DataNode "x::node<y>"
 *)
let get_info_of_next (hf: CF.h_formula) : (CP.spec_var * CP.spec_var * loc) =
  match hf with
  | CF.DataNode dn ->
      let x = dn.CF.h_formula_data_node in
      let y = (match dn.CF.h_formula_data_arguments with
        | [v] -> v
        | _ -> let msg = "get_info_of_next: expect 1 argument in data node" in
               raise (Solver_exception msg)
      ) in 
      let pos = dn.CF.h_formula_data_pos in
      (x, y, pos)
  | _ ->
      let msg = "get_info_of_next: expect a data node" in
      raise (Solver_exception msg)
  
(*
 * Obtain information of the primitive predicate "lseg(x,y,n)"
 * In Sleek it is modeled by a ViewNode "x::lseg<y,n>"
 *)
let get_info_of_lseg (hf: CF.h_formula) : (CP.spec_var * CP.spec_var * CP.spec_var * loc) =
  match hf with
  | CF.ViewNode vn ->
      let x = vn.CF.h_formula_view_node in
      let (y,n) = (match vn.CF.h_formula_view_arguments with
        | [v1;v2] -> (v1,v2)
        | _ -> let msg = "get_info_of_next: expect 1 argument in data node" in
               raise (Solver_exception msg)
      ) in 
      let pos = vn.CF.h_formula_view_pos in
      (x, y, n, pos)
  | _ ->
      let msg = "get_info_of_next: expect a view node representing lseg(x,y,n)" in
      raise (Solver_exception msg)
  
(*
 * Compute address of primitive predicates 
 *   - consider: emp, next, lseg 
 *   - otherwise raise exception
 *)
let get_address (hf: CF.h_formula) : CP.exp =
  match hf with
  | CF.Star _ | CF.StarMinus _ | CF.Conj _ | CF.ConjStar _ | CF.ConjConj _
  | CF.Phase _ | CF.ThreadNode _ | CF.Hole _ | CF.HRel _ | CF.HTrue | CF.HFalse ->
      raise (Solver_exception "get_address: expecting primitive predicates") 
  | CF.DataNode _ -> 
      let (x,_,pos) = get_info_of_next hf in
      (CP.mkVar x pos)
  | CF.ViewNode _ ->
      let (x,_,_,pos) = get_info_of_lseg hf in
      (CP.mkVar x pos)
  | CF.HEmp -> (CP.Null no_pos)

(* 
 * Compute the sound condition of primitive predicates: 
 *   - consider: emp, next, lseg 
 *   - otherwise raise exception
 *)
let get_sound_condition (hf: CF.h_formula) : CP.formula =
  match hf with
  | CF.Star _ | CF.StarMinus _ | CF.Conj _ | CF.ConjStar _ | CF.ConjConj _
  | CF.Phase _ | CF.ThreadNode _ | CF.Hole _ | CF.HRel _ | CF.HTrue | CF.HFalse ->
      raise (Solver_exception "get_sound_condition: expecting primitive predicates")
  | CF.DataNode dn -> 
      let pos = dn.CF.h_formula_data_pos in
      (CP.mkTrue pos)
  | CF.ViewNode _ ->
      (* view must be in the form of x::lseg<y,n> *)
      let (x,y,n,pos) = get_info_of_lseg hf in
      let f1 = CP.mkGteExp (CP.mkVar n pos) (CP.mkIConst 0 pos) pos in
      let f21 = CP.mkEqExp (CP.mkVar n pos) (CP.mkIConst 0 pos) pos in
      let f22 = CP.mkEqExp (CP.mkVar x pos) (CP.mkVar y pos) pos in
      let f2 = CP.mkEquivalence f21 f22 None pos in
      (CP.mkAnd f1 f2 pos)
  | CF.HEmp -> (CP.mkTrue no_pos)


(* 
 * Compute the empty condition of primitive predicates: 
 *   - consider: emp, next, lseg 
 *   - otherwise raise exception
 *)
let get_empty_condition (hf: CF.h_formula) : CP.formula =
  match hf with
  | CF.Star _ | CF.StarMinus _ | CF.Conj _ | CF.ConjStar _ | CF.ConjConj _
  | CF.Phase _ | CF.ThreadNode _ | CF.Hole _ | CF.HRel _ | CF.HTrue | CF.HFalse ->
      raise (Solver_exception "get_empty_condition: expecting primitive predicates")
  | CF.DataNode dn -> 
      let pos = dn.CF.h_formula_data_pos in
      (CP.mkFalse pos)
  | CF.ViewNode _ ->
      (* view must be in the form of x::lseg<y,n> *)
      let (x,y,_,pos) = get_info_of_lseg hf in
      (CP.mkEqExp (CP.mkVar x pos) (CP.mkVar y pos) pos)
  | CF.HEmp -> (CP.mkTrue no_pos)

(* 
 * Compute the separated condition of two primitive predicates: 
 *   - consider: emp, next, lseg 
 *   - otherwise raise exception
 *)
let compute_separated_condition (hf1: CF.h_formula) (hf2: CF.h_formula) : CP.formula =
  let addr1 = get_address hf1 in
  let addr2 = get_address hf2 in
  let addr_constr = CP.mkEqExp addr1 addr2 no_pos in
  let empty1 = get_empty_condition hf1 in
  let empty2 = get_empty_condition hf2 in
  let empty_constr = CP.mkOr empty1 empty2 None no_pos in
  CP.mkImplication addr_constr empty_constr None no_pos
   
(* 
 * collect a list of primitve predicates in a h_formula
 *   - requirement: the input h_formula must be a conjunction of primitive predicates
 *)
let rec collect_primitive_preds (hf: CF.h_formula) : CF.h_formula list =
  match hf with
  | CF.Star sf ->
      let f1 = sf.CF.h_formula_star_h1 in
      let f2 = sf.CF.h_formula_star_h2 in
      let list1 = collect_primitive_preds f1 in 
      let list2 = collect_primitive_preds f2 in
      (list1 @ list2)
  | CF.StarMinus sf ->
      let f1 = sf.CF.h_formula_starminus_h1 in
      let f2 = sf.CF.h_formula_starminus_h2 in
      let list1 = collect_primitive_preds f1 in 
      let list2 = collect_primitive_preds f2 in
      (list1 @ list2)
  | CF.Conj cf ->
      let f1 = cf.CF.h_formula_conj_h1 in
      let f2 = cf.CF.h_formula_conj_h2 in
      let list1 = collect_primitive_preds f1 in 
      let list2 = collect_primitive_preds f2 in
      (list1 @ list2)
  | CF.ConjStar cf ->
      let f1 = cf.CF.h_formula_conjstar_h1 in
      let f2 = cf.CF.h_formula_conjstar_h2 in
      let list1 = collect_primitive_preds f1 in 
      let list2 = collect_primitive_preds f2 in
      (list1 @ list2)
  | CF.ConjConj cf ->
      let f1 = cf.CF.h_formula_conjconj_h1 in
      let f2 = cf.CF.h_formula_conjconj_h2 in
      let list1 = collect_primitive_preds f1 in 
      let list2 = collect_primitive_preds f2 in
      (list1 @ list2)
  | CF.Phase pf ->
      let f1 = pf.CF.h_formula_phase_rd in
      let f2 = pf.CF.h_formula_phase_rw in
      let list1 = collect_primitive_preds f1 in 
      let list2 = collect_primitive_preds f2 in
      (list1 @ list2)
  | CF.DataNode _ | CF.ViewNode _ | CF.HEmp -> [hf]
  | CF.ThreadNode _ | CF.Hole _ | CF.HRel _ | CF.HTrue | CF.HFalse ->
      let msg = "collect_primitive_preds: "
                ^ "ThreadNode, Hole, HRel, HTrue, HFalse are irrelevant!" in
      raise (Solver_exception msg)


(* 
 * Compute the separated condition of a spatial formula 
 *   - consider only conjunction (And, Exists formula)  
 *   - otherwise raise exception
 *)
let compute_wellformed_condition (hf: CF.formula) : CP.formula =
  let prim_preds = collect_primitive_preds hf in
  let sound_conds = List.map get_sound_condition prim_preds in
  let separated_conds = (
    let rec collect_pairs (l: 'a list) : ('a * 'a) list = (
      match l with
      | hd::tl -> 
          let list1 = List.map (fun x -> (hd, x)) tl in
          let list2 = collect_pairs tl in
          list1 @ list2
      | [] -> []
    ) in
    let pred_pairs = collect_pairs prim_preds in
    List.map (fun (x,y) -> compute_separated_condition x y) pred_pairs
  ) in
  List.fold_left (
    fun f cond -> CP.mkAnd f cond no_pos
  ) (CP.mkTrue no_pos) (sound_conds @ separated_conds) 

(* 
 * Compute the allocating function of a spatial formula 
 *   - consider only conjunction (And, Exists formula)  
 *   - otherwise raise exception
 *)
let compute_allocating_function (f: CF.formula) : (CP.spec_var -> CP.formula) =
  fun (x: CP.spec_var) -> 
    match f with
    | CF.Base bf ->
        let pos = bf.CF.formula_base_pos in
        let prim_preds = collect_primitive_preds (bf.CF.formula_base_heap) in
        let constraints = List.map (fun pred ->
          let empty = get_empty_condition pred in
          let not_empty = CP.mkNot empty None pos in
          let addr_constr = CP.mkEqExp (CP.mkVar x pos) (get_address pred) pos in
          CP.mkAnd not_empty addr_constr pos
        ) prim_preds in
        List.fold_left (fun u v ->
          CP.mkOr u v None pos
        ) (CP.mkFalse pos) constraints
    | CF.Exists _ ->
        let msg = "compute_wellformed_condition: handle Exists later" in
        raise (Solver_exception msg)
    | CF.Or _ ->
        let msg = "compute_wellformed_condition: "
                  ^ "expect conjunction (And, Exists formula)" in
        raise (Solver_exception msg)

(*
 * Subtract two non-empty predicates
 *   res = (hf, cond) with:   hf = hf1 - hf2
 *                            cond is and additional side condition  
 *)
let subtract_nonempty_predicate (hf1: CF.h_formula) (hf2: CF.h_formula) 
    (alloc_func: (CP.spec_var -> CP.formula)) : (CF.h_formula * CP.formula) =
  match (hf1, hf2) with
  | CF.ViewNode vn1, CF.ViewNode vn2 ->
      let (x1,y1,n1,pos1) = get_info_of_lseg hf1 in
      let (x2,y2,n2,pos2) = get_info_of_lseg hf2 in
      let n = CP.fresh_spec_var n1 in
      let n_exp = CP.mkVar n pos1 in
      let n1_exp = CP.mkVar n1 pos1 in
      let n2_exp = CP.mkVar n2 pos2 in
      let length_constr = CP.mkEqExp n_exp (CP.mkSubtract n1_exp n2_exp pos1) pos1 in
      (* The paper didn't check x1 & x2 *)
      let remained_heap = CF.ViewNode { vn1 with
        CF.h_formula_view_node = y2;
        h_formula_view_arguments = [y1;n];
      } in
      let side_condition = (
        let addr_constr = CP.mkNeqExp (CP.mkVar y1 pos1) (CP.mkVar y2 pos2) pos1 in
        let alloc_constr = alloc_func y1 in
        let constr1 = CP.mkImplication addr_constr alloc_constr None pos1 in
        let constr2 = CP.mkEqExp n2_exp (CP.mkIConst 1 pos1) pos1 in
        CP.mkAnd (CP.mkOr constr1 constr2 None pos1) length_constr pos1
      ) in
      (remained_heap, side_condition)
  | CF.ViewNode vn1, CF.DataNode dn2 ->
      let (x1,y1,n1,pos1) = get_info_of_lseg hf1 in
      let (x2,y2,pos2) = get_info_of_next hf2 in
      let n = CP.fresh_spec_var n1 in
      let n_exp = CP.mkVar n pos1 in
      let n1_exp = CP.mkVar n1 pos1 in
      let length_constr = CP.mkEqExp n_exp (CP.mkSubtract n1_exp (CP.mkIConst 1 pos1) pos1) pos1 in
      let remained_heap = CF.ViewNode { vn1 with
        CF.h_formula_view_node = y2;
        h_formula_view_arguments = [y1;n];
      } in
      let side_condition = length_constr in
      (remained_heap, side_condition)
  | CF.DataNode dn1, CF.ViewNode vn2 ->
      let (x1,y1,pos1) = get_info_of_next hf1 in
      let (x2,y2,n2,pos2) = get_info_of_lseg hf2 in
      let remained_heap = CF.HEmp in
      let n2_exp = CP.mkVar n2 pos2 in
      let side_condition = (
        let constr1 = CP.mkEqExp (CP.mkVar y1 pos1) (CP.mkVar y2 pos1) pos1 in
        let constr2 = CP.mkEqExp n2_exp (CP.mkIConst 1 pos2) pos2 in
        CP.mkAnd constr1 constr2 pos1  
      ) in
      (remained_heap, side_condition)
  | CF.DataNode dn1, CF.DataNode dn2 ->
      let (x1,y1,pos1) = get_info_of_next hf1 in
      let (x2,y2,pos2) = get_info_of_next hf2 in
      let remained_heap = CF.HEmp in
      let side_condition = CP.mkEqExp (CP.mkVar y1 pos1) (CP.mkVar y2 pos2) pos1 in
      (remained_heap, side_condition)
  | CF.HEmp, _ 
  | _, CF.HEmp ->
      let msg = "subtract_nonempty_predicate: empty heap is inapplicable!" in
      raise (Solver_exception msg)
  | _, _ ->
      let msg = "subtract_nonempty_predicate: consider only primitive predicates."
                ^ "Others are irrelevant!" in
      raise (Solver_exception msg)


(*
 * Substitue all vars of a formula by their value in the stack model
 *)
let substitute_formula (tbl_stack: (CP.spec_var, int) Hashtbl.t) (f: CP.formula) = 
  let f_f f = None in
  let f_b b = None in
  let f_e e = (
    match e with
    | CP.Var (sv, pos) -> (
        try 
          let sv_val = Hashtbl.find tbl_stack sv in
          Some (CP.mkIConst sv_val pos)
        with Not_found ->
          let msg = "substitue_var: variable " ^ (CP.string_of_spec_var sv)
                    ^ "is not defined in stack model" in
          raise (Solver_exception msg)
      )
    | _ -> None
  ) in
  CP.transform_formula ((fun _-> None),(fun _-> None), f_f,f_b,f_e) f
  
(*
 * Check satisfiablity of a pure formula against the stack model
 *)
let check_statifiablity (tbl_stack: (CP.spec_var, int) Hashtbl.t) (f: CP.formula) : bool =
  let subs_f = substitute_formula tbl_stack f in
  let mf = MCP.mix_of_pure subs_f in
  TP.is_sat_raw mf

(*
 * Find a empty heap in a spatial formula against a stack model
 *   Return: - remainder of the spatial formula (if the formula is HEmp, no need to split)
 *           - empty condition of the found empty heap 
 *)
let rec split_empty_heap (tbl_stack: (CP.spec_var, int) Hashtbl.t) (hf: CF.h_formula)
    : (CF.h_formula * CP.formula) option =
  match hf with
  | CF.Star sf -> (
      let f1 = sf.CF.h_formula_star_h1 in
      let f2 = sf.CF.h_formula_star_h2 in
      let pos = sf.CF.h_formula_star_pos in
      let split1 = split_empty_heap tbl_stack f1 in 
      let split2 = split_empty_heap tbl_stack f2 in
      match split1, split2 with
      | None, None -> None
      | Some (remainder1, empty_cond1), None ->
          let remainder = match remainder1 with
            | CF.HEmp -> f2
            | _ -> CF.mkStarH remainder1 f2 pos
          in
          Some (remainder, empty_cond1)
      | None, Some (remainder2, empty_cond2) ->
          let remainder = match remainder2 with
            | CF.HEmp -> f1
            | _ -> CF.mkStarH f1 remainder2 pos
          in
          Some (remainder, empty_cond2)
      | Some (remainder1, empty_cond1), Some (remainder2, empty_cond2) ->
          let remainder = match remainder1, remainder2 with
            | CF.HEmp, CF.HEmp -> CF.HEmp
            | CF.HEmp, _ -> remainder2
            | _, CF.HEmp -> remainder1
            | _, _ -> CF.mkStarH remainder1 remainder2 pos
          in
          let empty_cond = CP.mkAnd empty_cond1 empty_cond2 pos in
          Some (remainder, empty_cond)
    )
  | CF.DataNode _ | CF.ViewNode _ ->
      let empty_cond = get_empty_condition hf in
      if (check_statifiablity tbl_stack empty_cond) then
        Some (CF.HEmp, empty_cond)
      else None
  | CF.HEmp -> None
  | _ ->
      let msg = "split_empty_heap: allow only spatial conjunction "
                ^ "of primitive predicates " in
      raise (Solver_exception msg)


(*
 * Check separated condition of two primitive predicates
 *)
let check_separated_heaps (tbl_stack: (CP.spec_var, int) Hashtbl.t) 
    (f1: CF.h_formula) (f2: CF.h_formula) : bool =
  let separated_cond = compute_separated_condition f1 f2 in
  let f = substitute_formula tbl_stack separated_cond in
  let mf = MCP.mix_of_pure f in
  TP.is_sat_raw mf


(*
 * Split a spatial formula into a primitive predicate and the remainders
 *   Return: a list of possible splits. Each element of the list contains
 *           a primitive predicate and the remainder of spatial formula
 *)
let rec split_primitive_heap (hf: CF.h_formula)
    : (CF.h_formula * CF.h_formula) list =
  match hf with
  | CF.Star sf ->
      let f1 = sf.CF.h_formula_star_h1 in
      let f2 = sf.CF.h_formula_star_h2 in
      let pos = sf.CF.h_formula_star_pos in
      let split_f1 = split_primitive_heap f1 in
      let res1 = List.map (fun (prim_pred, remainder) ->
        let full_remainder = match remainder with
          | CF.HEmp -> f2
          | _ -> (CF.mkStarH remainder f2 pos) in
        (prim_pred, full_remainder) 
      ) split_f1 in
      let split_f2 = split_primitive_heap f2 in
      let res2 = List.map (fun (prim_pred, remainder) ->
        let full_remainder = match remainder with
          | CF.HEmp -> f1
          | _ -> (CF.mkStarH f1 remainder pos) in
        (prim_pred, full_remainder) 
      ) split_f2 in
      res1 @ res2
  | CF.DataNode _ | CF.ViewNode _ | CF.HEmp ->
      [(hf, CF.HEmp)]
  | _ ->
      let msg = "split_primitive_heap: allow only spatial conjunction "
                ^ "of primitive predicates" in
      raise (Solver_exception msg)


let rec match_spatial_formula (tbl_stack: (CP.spec_var, int) Hashtbl.t) 
    (alloc: (CP.spec_var -> CP.formula)) (f1: CF.h_formula) (f2: CF.h_formula)
    : CP.formula =
  match (split_empty_heap tbl_stack f1) with
  | Some (newf1, empty_cond1) ->
      let match_res = match_spatial_formula tbl_stack alloc newf1 f2 in
      (CP.mkAnd empty_cond1 match_res no_pos) 
  | None -> (
      match (split_empty_heap tbl_stack f2) with
      | Some (newf2, empty_cond2) ->
          let match_res = match_spatial_formula tbl_stack alloc f1 newf2 in
          (CP.mkAnd empty_cond2 match_res no_pos)
      | None ->
          let split1 = split_primitive_heap f1 in
          let split2 = split_primitive_heap f2 in
          let pred1 = ref CF.HEmp in 
          let rest1 = ref CF.HEmp in
          let pred2 = ref CF.HEmp in
          let rest2 = ref CF.HEmp in
          if (List.exists (fun (p1, r1) ->
                List.exists (fun (p2, r2) ->
                  pred1 := p1; rest1 := r1;
                  pred2 := p2; rest2 := r2;
                  not (check_separated_heaps tbl_stack p1 p2)
                ) split2 
              ) split1 ) then (
            let (remainder, subtract_cond) =
                subtract_nonempty_predicate !pred1 !pred2 alloc in
            let sound_cond = get_sound_condition remainder in
            if (check_statifiablity tbl_stack sound_cond) then (
              let separated_cond = compute_separated_condition !pred1 !pred2 in
              let not_separated = CP.mkNot separated_cond None no_pos in
              let match_res = match_spatial_formula tbl_stack alloc !rest1 !rest2 in
              let temp1 = CP.mkAnd not_separated sound_cond no_pos in
              let temp2 = CP.mkAnd temp1 subtract_cond no_pos in
              CP.mkAnd temp2 match_res no_pos
            )
            else (CP.mkFalse no_pos)
          )
          else if ((f1 = CF.HEmp) && (f2 = CF.HEmp)) then
            CP.mkTrue no_pos
          else CP.mkFalse no_pos
    )

let prove_entailment (f1: CF.formula) (f2: CF.formula) : bool =
  match f1, f2 with
  | CF.Base bf1, CF.Base bf2 ->
      let pf1 = MCP.pure_of_mix (bf1.CF.formula_base_pure) in
      let hf1 = bf1.CF.formula_base_heap in
      let pf2 = MCP.pure_of_mix (bf2.CF.formula_base_pure) in
      let hf2 = bf2.CF.formula_base_heap in
      let hf1_wellformed = compute_wellformed_condition hf1 in
      let ante_approx = CP.mkAnd pf1 hf1_wellformed no_pos in
      let not_pf2 = CP.mkNot pf2 None no_pos in
      let temp = CP.mkAnd ante_approx not_pf2 no_pos in
      let mtemp = MCP.mix_of_pure subs_f in
      if (TP.is_sat_raw mtemp) then false  (* return invalid *)
      else (
        let alloc = compute_allocating_function hf1 in
        let ante = ref ante_approx in
        (* TODO: if a formula is SAT, collect its model *)
      )
  | _, _ ->
      let msg = "prove_entailment: unexpected formula!" in
      raise (Solver_exception msg) 

(*
 * Preprocess to check the validity of input formula
 * Allow only a conjunction of primitive predicates
 * Primitive prediates: x::node<y>, x::lseg<y,n>, emp
 *)
let rec preprocess_hformula (hf: CF.h_formula) : bool =
  match hf with
  | CF.Star sf ->
      let f1 = sf.CF.h_formula_star_h1 in
      let f2 = sf.CF.h_formula_star_h2 in
      (preprocess_hformula f1) && (preprocess_hformula f2)
  | CF.ViewNode _ -> true
  | CF.DataNode _ -> true
  | CF.HEmp -> true
  | _ -> false
  

let preprocess_formula (f: CF.formula) : bool =
  match f with
  | CF.Base bf ->
      let hf = bf.CF.formula_base_heap in
      preprocess_hformula hf
  | CF.Or _ -> false
  | CF. Exists _ -> false


(* 
 * Checking the validity of an entailment.
 * The antecedent and consequent must be conjunctive formula. 
 *)
let prove_entailment (ante: CF.formula) (conseq: CF.formula) : bool =
  
  
  true
