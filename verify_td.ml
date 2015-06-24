#include "xdebug.cppo"
open VarGen


(*
this module tranform an cast to pred
*)

open Globals
open Gen.Basic
open Wrapper
open Others
open Exc.GTable
open Printf
open Gen.Basic
open Gen.BList
open Mcpure_D
open Mcpure
open Label_only
open Typeinfer
open Slsat

module E = Env
module Err = Error
module IA = Iast
module CA = Cast
module CF = Cformula
module CP = Cpure
module LO = Label_only.LOne
module MCP = Mcpure


type assert_err=
  | VTD_Safe
  | VTD_Unsafe
  | VTD_Unk
  | VTD_NotApp

let string_of_assert_err res= match res with
    | VTD_Safe -> "safe"
    | VTD_Unsafe -> "unsafe"
    | VTD_Unk -> "unknown"
    | VTD_NotApp -> "not applicable"


let exists_assert_error_x prog e0=
  let rec helper e=
    (* let () = Debug.info_zprint (lazy  (" helper: " ^ (!print_exp e)  )) no_pos in *)
    match e with
      | CA.SCall sc -> begin
            let mn = CA.unmingle_name sc.CA.exp_scall_method_name in
            let () = Debug.ninfo_hprint (add_str "SCall"
                                 (pr_id)
                              ) sc.CA.exp_scall_method_name no_pos in
            if String.compare mn assert_err_fn = 0 then
              Some true
            else
              let mn_decl = CA.look_up_proc_def_raw prog.CA.new_proc_decls sc.exp_scall_method_name in
              let is_assert= mn_decl.CA.proc_has_assert_err in
              Some is_assert
              end
      | _ -> None
  in
  helper e0

let exists_assert_error prog e0=
  let pr1 = !C.print_prog_exp in
  Debug.no_1 "exists_assert_error" pr1 (pr_opt string_of_bool)
    (fun _ -> exists_assert_error_x prog e0) e0


let exam_ass_error_proc prog proc=
  let exist_ass_err = match proc.C.proc_body with
    | Some e -> CA.fold_exp e (exists_assert_error prog) (List.exists (fun b -> b)) false
    | None -> false
  in
  let () = proc.CA.proc_has_assert_err <- exist_ass_err in
  exist_ass_err

let exam_ass_error_proc prog proc=
  let pr1 p = pr_id p.C.proc_name in
  Debug.no_1 "exam_ass_error_proc" pr1 string_of_bool
      (fun _ -> exam_ass_error_proc prog proc) proc

let exam_ass_error_scc iprog scc=
  (*func call error*)
  List.exists (exam_ass_error_proc iprog) scc

let simplify_symex_trace_x prog v_args fs=
  let f_pf p0=
    let ps = CP.list_of_conjs p0 in
    (* elim bool vars *)
    let ps1 = List.filter (fun p -> not (CP.is_bool_formula p)) ps in
    let p1 = (CP.conj_of_list ps1 (CP.pos_of_formula p0)) in
    let eqs = (MCP.ptr_equations_without_null (MCP.mix_of_pure p1)) in
    let sel_eqs = List.fold_left (fun acc (sv1,sv2) ->
        match CP.mem_svl sv1 v_args, CP.mem_svl sv2 v_args with
          | true, false -> acc@[(sv2,sv1)]
          | false, true -> acc@[(sv1,sv2)]
          | _ -> acc
    ) [] eqs in
    Some (CP.remove_redundant (CP.subst sel_eqs p1))
  in
  let f_ef _ = None in
  let f_f _ = None in
  let f_hf _ = None in
  let f_m mp = Some mp in
  let f_a a = Some a in
  let f_b bf= Some bf in
  let f_e e = Some e in
  let simplify_pure f = CF.transform_formula (f_ef, f_f, f_hf, (f_m, f_a, f_pf, f_b, f_e)) f in
  (* let fs1 = Gen.BList.remove_dups_eq (Syn_checkeq.check_relaxeq_formula v_args) fs in *)
  let fs1 = List.map simplify_pure fs in
  fs1

let simplify_symex_trace prog v_args fs=
  let pr1 = !CP.print_svl in
  let pr2 = pr_list_ln !CF.print_formula in
  Debug.no_2 "simplify_symex_trace" pr1 pr2 pr2
      (fun _ _ -> simplify_symex_trace_x prog v_args fs) v_args fs


let symex_gen_view iprog prog proc vname proc_args v_args body pos=
  let eqs = List.fold_left (fun acc (CP.SpecVar (t,id,p) as sv) ->
      match p with
        | Unprimed ->
              let eq = CP.mkEqVar (CP.SpecVar (t,id,Primed)) sv no_pos in
              acc@[(eq)]
        | Primed -> acc
  ) [] proc_args in
  let init_p = List.fold_left (fun p p1 -> CP.mkAnd p p1 no_pos) (CP.mkTrue pos) eqs in
  let empty_es = CF.empty_es (CF.mkTrueFlow ()) Lab2_List.unlabelled proc.C.proc_loc in
  let ctx0 = CF.Ctx {empty_es with CF.es_formula = CF.formula_of_pure_formula init_p no_pos} in
  let ctx1 = CF.set_flow_in_context_override
    { CF.formula_flow_interval = !norm_flow_int; CF.formula_flow_link = None} ctx0 in
  let label = (fresh_formula_label "") in
  let ctx1 = CF.add_path_id ctx1 (Some label,-1) (-1) in
  (* need to add initial esc_stack *)
  let init_esc = [((0,""),[])] in
  let lfe = [CF.mk_failesc_context ctx1 [] init_esc] in
  let old_symex_td = !symex_td in
  let () = symex_td := true in
  let () = Td_utils.func_call_no := 0 in
  let res_ctx = x_add Typechecker.check_exp prog proc lfe body label in
  let () = symex_td := old_symex_td in
  let () = x_tinfo_hp (add_str ("symex_gen_view:" ^ proc.C.proc_name) (Cprinter.string_of_list_failesc_context_short)) res_ctx no_pos in
  let br_ctxs = List.fold_left (fun acc (_,esc, brs) -> acc@(List.fold_left (fun eacc (_, ebrs) -> eacc@ebrs) [] esc)@brs ) [] res_ctx in
  let rec collect_es c = match c with
    | CF.Ctx es ->
          let f = CF.substitute_flow_in_f !norm_flow_int !ret_flow_int es.CF.es_formula in
          let f1 = Immutable.apply_subs es.CF.es_crt_holes f in
          [f1]
    | CF.OCtx (c1,c2) -> (collect_es c1)@(collect_es c2)
  in
  let brs0 = List.fold_left (fun acc (_,ctx,_) -> acc@(collect_es ctx)) [] br_ctxs in
  let () = x_tinfo_hp (add_str ("brs0") (pr_list_ln !CF.print_formula)) brs0 no_pos in
  let e = CP.SpecVar (Int, err_var, Unprimed) in
  let safe_fl = MCP.mix_of_pure (CP.mkEqExp (CP.Var (e, no_pos)) (CP.IConst (0, no_pos)) no_pos) in
  let brs1 = List.fold_left (fun fs f ->
      let new_f = if CF.is_error_flow f then
        let f1 = CF.substitute_flow_in_f !norm_flow_int !error_flow_int f in
        CF.mkAnd_pure f1 (MCP.mix_of_pure CP.err_p) no_pos
      else CF.mkAnd_pure f safe_fl no_pos  in
      fs@[new_f]
  ) [] brs0 in
  let brs2 = simplify_symex_trace prog v_args brs1 in
  let () = x_binfo_hp (add_str ("brs2") (pr_list_ln !CF.print_formula)) brs2 no_pos in
  (* generate new iview *)
  let f_body = List.fold_left (fun acc f -> CF.mkOr acc f pos) (List.hd brs2) (List.tl brs2) in
  let vars = List.map CP.name_of_spec_var v_args in
  let tvars = List.map (fun (CP.SpecVar (t,id,_)) -> (t,id)) v_args in
  let f_body1,tis = Cfutil.norm_free_vars f_body (v_args) in
  let () = Debug.info_hprint (add_str "f_body1: " Cprinter.prtt_string_of_formula) f_body1 no_pos in
  let no_prm_body = CF.elim_prm f_body1 in
  let new_body = CF.set_flow_in_formula_override {CF.formula_flow_interval = !top_flow_int; CF.formula_flow_link =None} no_prm_body in
  let i_body = Rev_ast.rev_trans_formula new_body in
  (* let i_body = IF.subst [((slf,Unprimed),(self,Unprimed))] i_body in *)
  let () = Debug.ninfo_hprint (add_str "i_body1: " Iprinter.string_of_formula) i_body no_pos in
  let struc_body = IF.mkEBase [] [] [] i_body None (* false *) no_pos in
  let data_name = "" in
  let imm_map = Immutable.icollect_imm struc_body vars data_name iprog.I.prog_data_decls in
  let n_iview = {  I.view_name = vname;
  IA.view_pos = pos;
  IA.view_data_name = data_name;
  IA.view_type_of_self = None;
  IA.view_vars = vars;
  IA.view_ho_vars = [];
  IA.view_imm_map = imm_map;
  IA.view_labels = List.map (fun _ -> LO.unlabelled) vars, false;
  IA.view_modes = List.map (fun _ -> ModeOut) vars ;
  IA.view_typed_vars =  tvars;
  IA.view_kind = I.View_NORM;
  IA.view_derv = false;
  IA.view_parent_name = None;
  IA.view_prop_extns = [];
  IA.view_derv_info = [];
  IA.view_pt_by_self  = [];
  IA.view_formula = struc_body;
  IA.view_inv_lock = None;
  IA.view_is_prim = false;
  IA.view_invariant = IP.mkTrue no_pos;
  IA.view_baga_inv = None;
  IA.view_baga_over_inv = None;
  IA.view_baga_under_inv = None;
  IA.view_mem = None;
  IA.view_materialized_vars = [];
  IA.try_case_inference = false; }
  in
  ((vname,tis), n_iview)

let symex_gen_view iprog prog proc vname proc_args v_args body pos=
  let pr = (pr_pair (pr_pair pr_id Typeinfer.string_of_tlist) Iprinter.string_of_view_decl) in
  Debug.no_2 "symex_gen_view" pr_id !CP.print_svl pr
      (fun _ _ -> symex_gen_view iprog prog proc vname proc_args v_args body pos) vname  v_args

let symex_gen_view_from_proc iprog prog proc=
  (*
    - pred name
    - parameter list = method.para + option res + #e
    - parse body
  *)
  let pred_name = (C.unmingle_name proc.CA.proc_name) ^ "_v" in
  let r_args = (* match proc.CA.proc_return with *)
    (* | Void -> [] *)
    (* | _ -> let r_arg =  res_name in *)
      [CP.SpecVar (proc.CA.proc_return, res_name,Unprimed)]
  in
  let e_arg = CP.SpecVar (Int, err_var, Unprimed) in
  let proc_args = (List.map (fun (t,arg) -> CP.SpecVar (t,arg,Unprimed)) proc.CA.proc_args) in
  let pred_args = proc_args @ r_args @ [e_arg] in
  let iviews = match proc.CA.proc_body with
    | Some body -> begin
        try
          let iview = symex_gen_view iprog prog proc pred_name proc_args pred_args body no_pos in
          [iview]
        with _ -> []
      end
    | None -> []
  in
  iviews

let symex_gen_view_from_scc iprog prog scc=
  let vdecls = List.fold_left ( fun acc p ->
      acc@(symex_gen_view_from_proc iprog prog p)
  ) [] scc in
  vdecls

(* main_v(..) /\ e=1*)
let verify_td_scc iprog prog scc=
  let build_f_from_method mdecl=
    let view_args =
      List.map (fun (t, form) -> CP.SpecVar (t, form, Unprimed)) mdecl.CA.proc_args in
    let res = CP.SpecVar (mdecl.CA.proc_return, res_name, Unprimed) in
    let e = CP.SpecVar (Int, err_var, Unprimed) in
    let view_args_extra = view_args@[res; e] in
    let hv = CF.mkViewNode Td_utils.dump_self (method2pred (CA.unmingle_name mdecl.CA.proc_name)) view_args_extra no_pos in
    let hv_f = CF.formula_of_heap_fl hv (CF.mkNormalFlow ()) no_pos in
    CF.mkAnd_pure hv_f (MCP.mix_of_pure CP.err_p) no_pos
  in
  let rec build_sat_query procs=
    match procs with
      | [] -> VTD_Unk
      | [mdecl] -> begin
          let query = build_f_from_method mdecl in
          let () = Debug.info_hprint (add_str "query"
                                 (!CF.print_formula)
                              ) query no_pos in
          let r = Slsat.check_sat_topdown_x prog false query in
          match r with
            | 0 -> VTD_Safe
            | 1 -> VTD_Unsafe
            | _ -> VTD_Unk
        end
      | _::rest -> build_sat_query rest
  in
  build_sat_query scc

let verify_td_sccs iprog prog fast_return scc_procs=
  let combine_res ls_res=
    if List.exists (fun r -> r == VTD_Unsafe) ls_res then VTD_Unsafe
    else if List.for_all (fun r -> r == VTD_Safe) ls_res then VTD_Safe
    else VTD_Unk
  in
  let rec recf_trans_views ls_scc=
    match ls_scc with
      | [] -> ()
      | scc::rest ->
            let pair_iviews = symex_gen_view_from_scc iprog prog scc in
            (*transform to cviews *)
            let pairs,ivdecls = List.split pair_iviews in
            let () = List.iter (Astsimp.process_pred_def_4_iast iprog false) ivdecls in
            let old_inv_gen = !Globals.do_infer_inv in
            let () = Globals.do_infer_inv := true in
            let cviews = (Astsimp.convert_pred_to_cast pairs false iprog prog false) in
            let () = Globals.do_infer_inv := old_inv_gen in
            let () = Debug.info_hprint (add_str " predicated generated"
                (pr_list_ln Cprinter.string_of_view_decl_short)
            ) cviews no_pos in
            (* let r = verify_td_scc iprog prog scc in *)
            (* let n_res = res@[r] in *)
            (* if fast_return && r == VTD_Unsafe then *)
            (*   (n_res,VTD_Unsafe) *)
            (* else recf rest n_res *)
            recf_trans_views rest
  in
  let () = recf_trans_views scc_procs in
  let scc = List.concat scc_procs in
  verify_td_scc iprog prog scc

(* O: safe,
   1: unsafe,
   2: unknown,
   3: not applicaple (all method donot have assert error)
 *)
let verify_as_sat iprog prog iprims=
  (* Sort the proc_decls by proc_call_order *)
  let () = if (!Globals.print_core_all) then print_string (Cprinter.string_of_program prog)  
    else if(!Globals.print_core) then
      print_string (Cprinter.string_of_program_separate_prelude prog iprims)
    else ()
  in
  let l_proc = Cast.list_of_procs prog in
  let proc_prim, proc_main = List.partition Cast.is_primitive_proc l_proc in
  let sorted_proc_main = Cast.sort_proc_decls proc_main in
  let () = Debug.ninfo_hprint (add_str "sorted_proc_main"
                                 (pr_list Astsimp.pr_proc_call_order)
                              ) sorted_proc_main no_pos in
  (* this computes a list of scc mutual-recursive methods for processing *)
  let proc_scc = List.fold_left (fun a x -> match a with
      | [] -> [[x]]
      | xs::xss ->
        let i=(List.hd xs).CA.proc_call_order in
        if i==x.CA.proc_call_order then (x::xs)::xss
        else [x]::a
    ) [] sorted_proc_main in
  let proc_scc0 = List.rev proc_scc in
  let () = Debug.ninfo_hprint (add_str "proc_scc0"
      (pr_list_ln (pr_list Astsimp.pr_proc_call_order))
  ) proc_scc0 no_pos in
  (* look up assert error location *)
  if List.exists (exam_ass_error_scc prog) proc_scc0 then
    (* transform *)
    let res = verify_td_sccs iprog prog true proc_scc0 in
    (* check sat *)
    res
  else
    VTD_NotApp
