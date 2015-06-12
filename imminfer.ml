(**
Created 12-June-2015
Program transformations related to immutability annotations inference.
**)

#include "xdebug.cppo"
open VarGen
open Globals
open Gen

module C = Cast
module CF = Cformula
module CP = Cpure

let fresh_pred loc = fresh_any_name rel_default_prefix_name
let fresh loc = fresh_any_name imm_var_prefix
let fresh_ann loc = CP.SpecVar (AnnT, fresh loc, Unprimed)

let infer_imm_ann_proc (proc_static_specs: CF.struc_formula) : (CF.struc_formula * C.rel_decl option * C.rel_decl option) =
  let open Cformula in
  (* Will be set to false later when @imm_pre or @imm_post is set *)
  let use_mutable = ref true in
  let imm_post_is_set = ref false in
  let imm_pre_is_set = ref false in
  (* Stack of added fresh variables in both pre && post *)
  let v_stack = new Gen.stack in
  let n_stack = new Gen.stack in
  (* Stack of added fresh variables in both pre *)
  let pre_stack = new Gen.stack in
  (* Stack of added constant anot normalization *)
  let pre_norm_stack = new Gen.stack in
  (* Relation added on pre and post *)
  let pre_rel = ref None in
  let post_rel = ref None in
  let assign_ann_or_var ann loc = match ann with
    | CP.NoAnn -> if !use_mutable then (CP.ConstAnn Mutable, None)
                  else (let f = fresh_ann loc in (CP.PolyAnn f, Some (f, false)))
    | CP.ConstAnn _ -> if !use_mutable || (not !Globals.allow_imm_norm) then (ann, None)
                       else (let f = fresh_ann loc in (ann, Some (f, true)))
    | CP.PolyAnn f -> (ann, Some (f, false))
    | _ -> (CP.NoAnn, None) in
  let update_v_stack v = map_opt_def () (fun (v,_) -> v_stack # push v) v in
  let update_n_stack v ann =
    map_opt_def () (fun (v,norm) -> if norm then n_stack # push (v, ann)) v in
  let ann_heap = function
    | DataNode hp ->
       let loc = hp.h_formula_data_pos in
       let (h_imm, v) = assign_ann_or_var hp.h_formula_data_imm loc in
       let () = update_v_stack v in
       let () = update_n_stack v h_imm in
       let h_imm = match v with
         | Some (_, false) -> h_imm
         | Some (v, true) -> CP.PolyAnn v
         | None -> h_imm in
       Some (DataNode { hp with h_formula_data_imm = h_imm })
    | ViewNode hp ->
       let loc = hp.h_formula_view_pos in
       let (h_imm, v) = assign_ann_or_var hp.h_formula_view_imm loc in
       let () = update_v_stack v in
       let () = update_n_stack v h_imm in
       let h_imm = match v with
         | Some (_, false) -> h_imm
         | Some (v, true) -> CP.PolyAnn v
         | None -> h_imm in
       Some (ViewNode { hp with h_formula_view_imm = h_imm })
    | _ -> None
  in
  let and_pure_with_eqs vars formula loc =
    let eq_v (v, ann) =
      match ann with
      | CP.ConstAnn h_ann ->
         let p_formula = CP.Eq (CP.Var (v,loc), CP.AConst (h_ann, loc), loc) in
         let b_formula = (p_formula, None) in
         CP.BForm (b_formula, None)
      | _ -> failwith "Not possible"
    in
    List.fold_right (fun pure acc -> add_pure_formula_to_formula pure acc) (List.map eq_v vars) formula in
  let and_pure_with_rel relname rel_params formula loc =
    let rel_pure =
      let args = List.map (fun i -> CP.Var (i, loc)) rel_params in
      let p_formula = CP.RelForm (CP.SpecVar (AnnT, relname, Unprimed), args, loc) in
      let b_formula = (p_formula, None) in
      CP.BForm (b_formula, None)
    in add_pure_formula_to_formula rel_pure formula in
  let mk_rel rel_params loc =
    let rn = fresh_pred loc in
    match rel_params with
    | [] -> None
    | rel_params -> Some ({
                             C.rel_name = rn;
                             C.rel_vars = List.map (fun _ -> Cpure.SpecVar (AnnT, fresh loc, Unprimed)) rel_params;
                             C.rel_formula = CP.mkTrue no_pos })
  in
  let rec ann_struc_formula_1 = function
    | EInfer ff ->
       imm_pre_is_set := ff.formula_inf_obj # is_pre_imm;
       imm_post_is_set := ff.formula_inf_obj # is_post_imm;
       use_mutable := (not !imm_pre_is_set && not !imm_post_is_set);
       None
    | EAssume ff ->
       pre_stack # push_list (v_stack # get_stk);
       pre_norm_stack # push_list (n_stack # get_stk_and_reset);
       if !use_mutable then Some (EAssume ff) else
         Some (EAssume { ff with formula_assume_simpl = transform_formula transform_1 ff.formula_assume_simpl })
    | _ -> None
  and transform_1 = (ann_struc_formula_1, nonef, ann_heap, (somef, somef, somef, somef, somef)) in
  let ann_postcondition = function
    | EAssume ff ->
       let loc = pos_of_formula ff.formula_assume_simpl in
       (* Normalize postcondition *)
       let postcondition =
         if (not (n_stack # is_empty)) then
           and_pure_with_eqs (n_stack # get_stk) ff.formula_assume_simpl loc
         else ff.formula_assume_simpl in
       (* And the pure part with relation *)
       if ((not (v_stack # is_empty)) && (not (!post_rel = None))) then
         let post_rel = match !post_rel with Some p -> p | None -> failwith "Not possible (infer_imm_ann_proc)" in
         let rel_params = v_stack # get_stk in
         let postcondition_with_rel = and_pure_with_rel post_rel.C.rel_name rel_params postcondition loc in
         Some (EAssume { ff with formula_assume_simpl = postcondition_with_rel })
       else Some (EAssume {ff with formula_assume_simpl = postcondition })
    | _ -> None
  in
  let ann_struc_formula_2 = function
    | EInfer ff ->
       begin
         match ff.formula_inf_continuation with
         | EBase ({ formula_struc_base = precondition; formula_struc_pos = loc } as ebase) ->
            let new_ebase =
              (* Normalize precondition *)
              let precondition =
                if (not (pre_norm_stack # is_empty)) then
                  and_pure_with_eqs (pre_norm_stack # get_stk) precondition loc
                else precondition in
              if (not (pre_stack # is_empty) && not (!pre_rel = None)) then
                let pre_rel = match !pre_rel with Some p -> p | None -> failwith "Not possible (infer_imm_ann_proc)" in
                let rel_params = pre_stack # get_stk in
                let precondition_with_rel = and_pure_with_rel pre_rel.C.rel_name rel_params precondition loc in
                { ebase with formula_struc_base = precondition_with_rel }
              else { ebase with formula_struc_base = precondition } in
            let new_continuation =
              if (not (v_stack # is_empty)) then
                let transform = (ann_postcondition, nonef, nonef, (nonef, nonef, nonef, nonef, nonef)) in
                let base_continuation = map_opt (transform_struc_formula transform) ebase.formula_struc_continuation in
                EBase { new_ebase with formula_struc_continuation = base_continuation }
              else EBase new_ebase in
            let new_inf_vars =
              if (not (v_stack # is_empty)) then
                let rel_to_var rel = match rel with
                  | Some p -> [CP.SpecVar (AnnT, p.C.rel_name, Unprimed)]
                  | None -> [] in
                (rel_to_var !post_rel)@(rel_to_var !pre_rel)@ff.formula_inf_vars
              else ff.formula_inf_vars in
            Some (EInfer { ff with formula_inf_continuation = new_continuation;
                                   formula_inf_vars = new_inf_vars })
         | _ -> None
       end
    | other -> Some other
  in
  let transform_2 = (ann_struc_formula_2, somef, somef, (somef, somef, somef, somef, somef)) in
  let pss =
    let pss_1 = transform_struc_formula transform_1 proc_static_specs in
    if !use_mutable then pss_1
    else
      (if !imm_pre_is_set then pre_rel := mk_rel (pre_stack # get_stk) no_pos;
       if !imm_post_is_set then post_rel := mk_rel (v_stack # get_stk) no_pos;
       transform_struc_formula transform_2 pss_1) in
  (pss, !pre_rel, !post_rel)

let infer_imm_ann_proc (proc_static_specs: CF.struc_formula) : (CF.struc_formula * C.rel_decl option * C.rel_decl option) =
  Debug.no_1 "infer_imm_ann_proc"
             Cprinter.string_of_struc_formula
             (fun (f,_,_) -> Cprinter.string_of_struc_formula f)
             infer_imm_ann_proc
             proc_static_specs

let infer_imm_ann (prog: C.prog_decl) (proc_decls: C.proc_decl list) : C.proc_decl list =
  (** Infer immutability annotation variables for one proc,
      @return (new proc, precondition relation, postcondition relation) **)
  let (new_proc_decls, rel_list) =
    let helper proc (proc_decls, rel_list) =
      let (pss, pre_rel, post_rel) = infer_imm_ann_proc proc.C.proc_static_specs in
      let rel_list_1 = map_opt_def rel_list (fun r -> r::rel_list) pre_rel in
      let rel_list_2 = map_opt_def rel_list_1 (fun r -> r::rel_list) post_rel in
      (({proc with C.proc_static_specs = pss })::proc_decls, rel_list_2) in
    List.fold_right helper proc_decls ([], []) in
  prog.C.prog_rel_decls <- prog.C.prog_rel_decls @ rel_list;
  new_proc_decls
