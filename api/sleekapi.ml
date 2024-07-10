open Hipsleek
open Hipsleek_common
open Exc.GTable

module C = Cast
module I = Iast
module VG = VarGen
module SC = Sleekcommons
module SE = Sleekengine
module CF = Cformula
module IF = Iformula
module IP = Ipure_D
module NF = Nativefront

type pe = IP.exp
type pf = IP.formula
type hf = IF.h_formula
type mf = SC.meta_formula
type dd = I.data_decl
type lfe = CF.list_failesc_context
type sf = CF.struc_formula

type typ =
  | Void
  | Bool
  | Float
  | Int
  | Named of string

type param_modifier = 
  | NoMod
  | RefMod
  | CopyMod

type param = {
  param_type : typ;
  param_name : string;
  param_mod : param_modifier;
}

(* Prelude of api *)
let init () = 
  let () = print_string "Initializing sleek api" in
  (* Prelude file contains some data declarations like int_ptr to support the api
     Declarations in this prelude file will be parsed and stored in a global
     variable, iprog, in sleekengine.ml
  *)
  let () = Sleekmain.parse_file Nativefront.list_parse "./sleekapi_prelude.slk" in
  (*Referenced from sleekmain.ml main()*)
  let iprog = { I.prog_include_decls =[];
                I.prog_data_decls = [SE.iobj_def;SE.ithrd_def];
                I.prog_global_var_decls = [];
                I.prog_logical_var_decls = [];
                I.prog_enum_decls = [];
                I.prog_view_decls = [];
                I.prog_func_decls = [];
                I.prog_rel_decls = [];
                I.prog_rel_ids = [];
                I.prog_templ_decls = [];
                I.prog_ut_decls = [];
                I.prog_ui_decls = [];
                I.prog_hp_decls = [];
                I.prog_hp_ids = [];
                I.prog_axiom_decls = [];
                I.prog_proc_decls = [];
                I.prog_coercion_decls = [];
                I.prog_hopred_decls = [];
                I.prog_barrier_decls = [];
                I.prog_test_comps = [];
              } in
  let () = I.inbuilt_build_exc_hierarchy () in (* for inbuilt control flows *)
  let () = I.build_exc_hierarchy true iprog in
  let () = exlist # compute_hierarchy  in  
  ()

(* Used as placeholder for pos since no file is parsed *)
let no_pos : VG.loc =
  let no_pos1 = { Lexing.pos_fname = "";
                  Lexing.pos_lnum = 0;
                  Lexing.pos_bol = 0; 
                  Lexing.pos_cnum = 0 } in
  {VG.start_pos = no_pos1; VG.mid_pos = no_pos1; VG.end_pos = no_pos1;}

let param_to_typed_ident (p : I.param) = (p.I.param_type, p.I.param_name)

let typ_to_globals_typ (t: typ) : Globals.typ =
  match t with
  | Void -> Void
  | Bool -> Bool
  | Float -> Float
  | Int -> Int
  | Named(s) -> Named(s)

let param_mod_to_iast_param_mod (pm : param_modifier) : I.param_modifier =
  match pm with
  | NoMod -> NoMod
  | RefMod -> RefMod
  | CopyMod -> CopyMod

let param_to_iast_param (p: param) : I.param =
  {
    param_type = typ_to_globals_typ p.param_type;
    param_name = p.param_name;
    param_mod = param_mod_to_iast_param_mod p.param_mod;
    param_loc = no_pos
  }

let check_anon var_name f = 
  match var_name with 
    | "_" -> ("Anon" ^ Globals.fresh_trailer ())
    | "" -> raise (Invalid_argument (f ^ ": name is empty"))
    | _ -> var_name

(* Check whether is a variable primed by variable name *)
(* Might need error handling if var has len 0*)
let check_prime var_name =
  let len = String.length var_name in
    let last = String.get var_name (len - 1) in
    match last with 
    | '\'' -> VG.Primed
    | _ -> VG.Unprimed

(* Returns the truncated variable if variable is primed*)
(* Might also need error handling if var has len 0*)
let truncate_var var_name primed = 
  match primed with 
  | VG.Primed -> String.sub var_name 0 ((String.length var_name) - 1)
  | VG.Unprimed -> var_name

(* Building pure expressions *)
let null_pure_exp = IP.Null no_pos

let var_pure_exp (ident : string) = 
  let ident = check_anon ident "var_pure_exp" in
  let p = check_prime ident in
  let t_ident = truncate_var ident p in
  IP.Var ((t_ident, p), no_pos)

let int_pure_exp int = IP.IConst (int, no_pos)
let float_pure_exp float = IP.FConst (float, no_pos)

let add_pure_exp lhs rhs = IP.Add (lhs, rhs, no_pos)
let sub_pure_exp lhs rhs = IP.Subtract (lhs, rhs, no_pos)
let mul_pure_exp lhs rhs = IP.Mult (lhs, rhs, no_pos)
let div_pure_exp lhs rhs = IP.Div (lhs, rhs, no_pos)

(* Building pure formula *)
let bool_pure_f bool = IP.BForm ((IP.BConst (bool, no_pos), None), None)
let false_f          = bool_pure_f false
let true_f           = bool_pure_f true

(* terms *)
let gt_pure_f  lhs rhs = IP.BForm ((IP.Gt (lhs, rhs, no_pos), None), None)
let gte_pure_f lhs rhs = IP.BForm ((IP.Gte (lhs, rhs, no_pos), None), None)
let lt_pure_f  lhs rhs = IP.BForm ((IP.Lt (lhs, rhs, no_pos), None), None)
let lte_pure_f lhs rhs = IP.BForm ((IP.Lte (lhs, rhs, no_pos), None), None)
let eq_pure_f  lhs rhs = IP.BForm ((IP.Eq (lhs, rhs, no_pos), None), None)

(* connectives *)
let not_f           f = IP.Not (f, None, no_pos)
let and_f     lhs rhs = IP.And (lhs, rhs, no_pos)
let or_f      lhs rhs = IP.Or (lhs, rhs, None, no_pos)
let implies_f lhs rhs = or_f (not_f lhs) rhs
let iff_f     lhs rhs = and_f (implies_f lhs rhs) (implies_f rhs lhs)

(* Building heap formula *)
let empty_heap_f = IF.HEmp
let false_heap_f = IF.HFalse
let true_heap_f  = IF.HTrue

let sep_conj_f h1 h2 = IF.mkStar h1 h2 no_pos

let points_to_int_f var_name int =
  let var_name = check_anon var_name "points_to_int_f" in
  let p = check_prime var_name in
  let t_var_name = truncate_var var_name p in
  IF.mkHeapNode_x (t_var_name, p) "int_ptr" []  0 false Globals.SPLIT0 IP.NoAnn false false false None [(int_pure_exp int)] [None] None no_pos

(*Parses string of data def, pred def or lemma def*)
let top_level_decl sleek_str =  
  let sleek_cmd = NF.parse_slk sleek_str in
  match sleek_cmd with
  | SC.DataDef data_def ->
    (* Stores predicate definition into SE.iprog *)
    let () = SE.process_data_def data_def in
    SE.convert_data_and_pred_to_cast_x () 
  | SC.PredDef pred_def ->
    (* Stores predicate definition into SE.iprog *)
    let () = SE.process_pred_def_4_iast pred_def in
    SE.convert_data_and_pred_to_cast_x ()
  | SC.LemmaDef lemma_def ->
    if I.is_lemma_decl_ahead lemma_def then
      let () = SE.process_list_lemma lemma_def in
      ()
    else ()
  | _ -> ()    

let data_decl_cons data_name data_fields =
  let df = List.map (fun (t, s) -> (((typ_to_globals_typ t), s), no_pos, false, [])) data_fields in

  (* Stores data definition into SE.iprog *)
  let () = SE.process_data_def {
    I.data_name = data_name;
    I.data_fields = df;
    I.data_parent_name = "Object";
    I.data_invs = [];
    I.data_pos = no_pos;
    I.data_pure_inv = None;
    I.data_is_template = false;
    I.data_methods = [];
  } in
  let () = I.annotate_field_pure_ext SE.iprog in (* Can be improved to not re-annotatepreviously annotated data decls in SE.iprog *)
  let c_data_decl = Astsimp.trans_data_x SE.iprog (List.hd SE.iprog.I.prog_data_decls) in
  let () = !SE.cprog.Cast.prog_data_decls <- c_data_decl :: !SE.cprog.Cast.prog_data_decls in
  let () = Cf_ext.add_data_tags_to_obj !SE.cprog.Cast.prog_data_decls in (* To mark recursive data declarations *)
  (* print_string ("\n Cprog after data_decl : " ^ (Cprinter.string_of_program !SE.cprog)) *)
  ()

let data_decl sleek_str =
  let sleek_cmd = NF.parse_slk sleek_str in
  match sleek_cmd with
  | SC.DataDef data_def ->
    (* Stores data definition into SE.iprog *)
    let () = SE.process_data_def data_def in
    SE.convert_data_and_pred_to_cast_x () (* Can be improved to not re-convert previously converted data and predidcates *)
  | _ -> ()                               (* Possible error handling here *)


let predicate_decl sleek_str =
  let sleek_cmd = NF.parse_slk sleek_str in
  match sleek_cmd with
  | SC.PredDef pred_def ->
    (* Stores predicate definition into SE.iprog *)
    let () = SE.process_pred_def_4_iast pred_def in
    SE.convert_data_and_pred_to_cast_x () (* Can be improved to not re-convert previously converted data and predidcates *)
  | _ -> ()                               (* Possible error handling here *)

let lemma_decl sleek_str =
  let sleek_cmd = NF.parse_slk sleek_str in
  match sleek_cmd with
  | SC.LemmaDef lemma_def ->
    if I.is_lemma_decl_ahead lemma_def then
      let () = SE.process_list_lemma lemma_def in
      ()
    else ()
  | _ -> ()                               (* Possible error handling here *)

(* Transform I_struc_formula to C_struc_formula
   Follows trans_proc_x
*)
let trans_I_to_C istruc_form (args: I.param list)  =
  (* Normalize struc formula
     Follows case_normalize_proc_x
  *)
  let gl_v_l = List.map (fun c-> List.map (fun (v,_,_)-> (c.I.exp_var_decl_type,v)) c.I.exp_var_decl_decls) SE.iprog.I.prog_global_var_decls in
  let gl_v =  List.map (fun (c1,c2)-> {I.param_type = c1; I.param_name = c2; I.param_mod = I.RefMod; I.param_loc = no_pos })(List.concat gl_v_l) in
  let gl_proc_args = gl_v @ args in
  let gl_proc_args = gl_proc_args @ (match None with | None -> [] | Some ha -> [ha]) in

  let h = (List.map (fun c1 -> (c1.Iast.param_name, VG.Unprimed)) gl_proc_args) in 
  let p = ((Globals.eres_name, VG.Unprimed)::(Globals.res_name, VG.Unprimed)::
           (List.map (fun c1-> (c1.I.param_name, VG.Primed))
              (List.filter (fun c-> c.I.param_mod == Iast.RefMod) gl_proc_args))) in

  let strad_s =
    let pr,pst = IF.struc_split_fv istruc_form false in
    Gen.BList.intersect_eq (=) pr pst in
  let istruc_form, _ = Astsimp.case_normalize_struc_formula 5 SE.iprog h p istruc_form false false false strad_s in
  let n_tl = [] in                      (* Probably shouldn't be empty *)
  let free_vars = List.map (fun p -> p.I.param_name) args in
  let (n_tl, c_struc_form) = Astsimp.trans_I2C_struc_formula 2 SE.iprog false true free_vars istruc_form n_tl true true in
  let cf = CF.add_inf_cmd_struc true c_struc_form in
  let cf = Astsimp.set_pre_flow_x cf in
  let cf =
    if not !Globals.dis_term_chk then
      CF.norm_struc_with_lexvar true false None cf
    else cf
  in
  cf

let spec_decl func_name func_spec args =
  match Parser.parse_spec (func_name ^ " " ^ func_spec) with
  | x::_ -> trans_I_to_C (snd x) (List.map param_to_iast_param args)
  | _ -> raise (Invalid_argument ("Syntax error with function specifications"))

let points_to_f var_name ident exps =
  let var_name = check_anon var_name "points_to_f" in 
  let primed = check_prime var_name in
  let t_var_name = truncate_var var_name primed in
  let imm_param = List.map (fun _ -> None) exps in
  IF.mkHeapNode_x (t_var_name, primed) ident [] 0 false Globals.SPLIT0 IP.NoAnn false false false None exps imm_param None no_pos
  
(* Functions to build meta_formulae *)

let ante_f heap_f pure_f  =
  let formula_base = {
    IF.formula_base_heap = heap_f;
    IF.formula_base_pure = pure_f;
    IF.formula_base_vperm = IvpermUtils.empty_vperm_sets;
    IF.formula_base_flow = "__norm";
    IF.formula_base_and = [];
    IF.formula_base_pos = no_pos
  } in
  SC.MetaForm(IF.Base(formula_base))

let conseq_f heap_f pure_f =
  let formula_base = {
    IF.formula_base_heap = heap_f;
    IF.formula_base_pure = pure_f;
    IF.formula_base_vperm = IvpermUtils.empty_vperm_sets;
    IF.formula_base_flow = "__norm";
    IF.formula_base_and = [];
    IF.formula_base_pos = no_pos
  } in
  let struc_base_formula = {
    IF.formula_struc_explicit_inst = [];
    IF.formula_struc_implicit_inst = [];
    IF.formula_struc_exists = [];
    IF.formula_struc_base = Base(formula_base);
    IF.formula_struc_is_requires = false; (* Not sure what this is *)
    IF.formula_struc_continuation = None;
    IF.formula_struc_pos = no_pos
  } in
  SC.MetaEForm(IF.EBase(struc_base_formula))

(* Antecedent and consequent are IF.formula and IF.struc_formula respectively *)
let entail ante conseq : bool =
  SE.process_entail_check ante conseq (Some false)
  (* residue can actually be accessed from CF.residues after run_entail_check *)
  (* let validity, (residue: CF.list_context), _ = SE.run_entail_check ante conseq (Some false) in *)
  (* let () = print_string ("\n Residue : " ^ (Cprinter.string_of_list_context residue)) in *)
  (* SE.print_entail_result [] validity residue "\nEntail " false *)

let ante_printer xs =
  let rec helper i xs =
    match xs with
    | [] -> ""
    | x::xs' -> "Ante 1 : " ^ (SC.string_of_meta_formula x) ^ "\n" ^ (helper (i+1) xs')
  in
  helper 1 [xs]

let conseq_printer x =
  "Conseq : " ^ (SC.string_of_meta_formula x)

(* Converts meta_formulae to cformulae
   This conversion is done by closely following SE.run_infer_one_pass
*)
let mf_to_cform iante iconseq =
  let ivars = [] in
  let _ = CF.residues := None in
  let _ = Infer.rel_ass_stk # reset in
  let _ = CF.rel_def_stk # reset in
  let (n_tl,ante) = SE.meta_to_formula iante false [] [] in
  let xpure_all f =
    let lst = CF.split_components_all f in
    let disj = List.map (fun (h,p,_,_,_,_) ->
        let (mf,_,_) = Cvutil.xpure_heap_symbolic 999 !SE.cprog h p 0 in
        (Mcpure.pure_of_mix mf)) lst in
    Cpure.join_disjunctions disj in
  let f = xpure_all ante in
  let mf = Mcpure.mix_of_pure f in
  let () = SE.last_entail_lhs_xpure := Some mf in
  let ante = Cvutil.prune_preds !SE.cprog true ante in
  let ante = (*important for permissions*)
    if (Perm.allow_perm ()) then
      CF.add_mix_formula_to_formula (Perm.full_perm_constraint ()) ante
    else ante
  in
  let vk = Typeinfer.fresh_proc_var_kind n_tl Float in
  let n_tl = Typeinfer.type_list_add  (Perm.full_perm_name ()) vk n_tl in
  let fvs = CF.fv ante in
  let _ = SC.fv_meta_formula iante in
  let ivars_new = List.map (fun v -> (v,VG.Unprimed)) ivars in
  let fv_idents = (List.map Cpure.name_of_spec_var fvs)@ivars in
  let fv_idents_new = (List.map Cpure.primed_ident_of_spec_var fvs)@ivars_new in
  let _ =
    if !Globals.dis_impl_var then
      let conseq_idents = List.map (fun (v, _) -> v) (SC.fv_meta_formula iconseq) in
      Gen.BList.remove_dups_eq (fun v1 v2 -> String.compare v1 v2 == 0) (fv_idents @ conseq_idents)
    else fv_idents
  in
  let fv_idents_new =
    if !Globals.dis_impl_var then
      let conseq_idents =(SC.fv_meta_formula iconseq) in
      Gen.BList.remove_dups_eq (fun (v1,p1) (v2,p2) -> String.compare v1 v2 == 0 && p1==p2) (fv_idents_new @ conseq_idents)
    else fv_idents_new
  in

  let (n_tl,conseq) = SE.meta_to_struc_formula iconseq false fv_idents_new  n_tl in
  let conseq_fvs = CF.struc_fv ~vartype:Vartypes.var_with_implicit_explicit conseq in
  let vs = Cpure.remove_dups_svl (fvs@conseq_fvs) in
  let () = Global_var.set_stk_vars vs in

  let sst0 = List.map (fun (Cpure.SpecVar (t,i,p) as sv) ->
      let sv2 = (Typeinfer.get_spec_var_type_list_infer ~d_tt:n_tl) (i,p) [] no_pos
      in (sv,sv2)) fvs in
  let sst = List.filter (fun (Cpure.SpecVar (t1,_,_), Cpure.SpecVar (t2,_,_)) -> not(t1=t2) ) sst0 in
  let ante1 = if sst==[] then ante else CF.subst sst ante in
  let ante = Cfutil.transform_bexpr ante1 in
  let conseq = CF.struc_formula_trans_heap_node [] Cfutil.transform_bexpr conseq in
  (ante, conseq)

(* Converts meta_formulae to context and cformula
   Building the context closely follows sleek_entail_check_x and mkEmp_list_failesc_context
 *)
let new_context iante iconseq =
  let isvl = [] in
  let itype = [] in
  let proof_traces = [] in
  let cante, cconseq = mf_to_cform iante iconseq in

  let es = CF.empty_es (CF.mkTrueFlow ()) Label_only.Lab2_List.unlabelled no_pos in
  let es = {es with CF.es_proof_traces = proof_traces} in
  let lem = Lem_store.all_lemma # get_left_coercion in
  let cante = Solver.normalize_formula_w_coers 11 !SE.cprog es cante lem in

  let ectx = CF.empty_ctx (CF.mkTrueFlow ()) Label_only.Lab2_List.unlabelled no_pos in
  let ctx = CF.build_context ectx cante no_pos in
  let ctx = Solver.elim_exists_ctx ctx in
  let ctx = CF.add_proof_traces_ctx ctx proof_traces in

  let ctx = CF.add_path_id ctx (None, 0) 0 in
  let ctx = CF.set_flow_in_context_override
      { CF.formula_flow_interval = !Exc.ETABLE_NFLOW.norm_flow_int; CF.formula_flow_link = None} ctx in

  let orig_vars = CF.fv cante @ CF.struc_fv cconseq in
  let (vrel, vtempl, v_hp_rel, iv) = List.fold_left (fun (vr, vt, vh, iv) v ->
      let typ = Cpure.type_of_spec_var v in
      if Globals.is_RelT typ then (vr@[v], vt, vh, iv)
      else if Cpure.is_hprel_typ v then (vr, vt, vh@[v], iv)
      else if Globals.is_FuncT typ then (vr, vt@[v], vh, iv)
      else (vr, vt, vh, iv@[v])) ([], [], [], []) isvl in
  let ctx = Infer.init_vars ctx iv vrel vtempl v_hp_rel orig_vars in
  let ctx = Infer.init_infer_type ctx itype in
  (ctx, cconseq)
(* The following is done in sleek_entail *)
  (* let init_esc = [((0,""),[])] in *)
  (* let lfe = [CF.mk_failesc_context ctx [] init_esc] in *)
  (* let () = print_string ("\n lfe : " ^ (Cprinter.string_of_list_failesc_context lfe)) in *)
  (* (lfe, cconseq) *)

let entail iante iconseq =
  let ante_ctx, conseq = new_context iante iconseq in
  (* let rs, pf = Solver.heap_entail_struc_list_failesc_context_init 12 !SE.cprog false true ante_ctx conseq None None None no_pos None in *)
  let rs, prf = Sleekcore.sleek_entail !SE.cprog ante_ctx conseq no_pos in
(*   let () = print_string ("\n Residue 1 : " ^ (Cprinter.string_of_list_failesc_context rs)) in *)
(*   (\* entail [iante] iconseq *\) *)
  let res = CF.isSuccessListFailescCtx_new rs in
  let () = print_string ("\n" ^ (string_of_bool res)) in
  res

let init_ctx cstruc_form args =
  (* Build an initial context
     Follows check_proc
  *)
  let args = List.map param_to_iast_param args in
    
  let ftypes, fnames = List.split (List.map param_to_typed_ident args) in
  let fsvars = List.map2 (fun t -> fun v -> Cpure.SpecVar (t, v, Unprimed)) ftypes fnames in
  let pf = (CF.no_change fsvars no_pos) in (*init(V) := v'=v*)
  let nox = CF.formula_of_pure_N pf no_pos in
  let init_form = nox in
  let init_ctx = CF.empty_ctx (CF.mkTrueFlow ()) Label_only.Lab2_List.unlabelled no_pos in
  let init_form =
    if (Perm.allow_perm ()) then
      CF.add_mix_formula_to_formula (Perm.full_perm_constraint ()) init_form
    else
      init_form
  in
  let init_ctx = CF.build_context init_ctx init_form no_pos in
  (* Termination: Add the set of logical variables into the initial context  *)
  let init_ctx =
    if !Globals.dis_term_chk then init_ctx
    else Infer.restore_infer_vars_ctx [] [] init_ctx in

  (* Tranform context to include the pre-condition in cstruc_form 
     Follows check_specs_infer_a
  *)
  let rec helper ctx cstruc_form =
    match cstruc_form with
    | CF.EBase b ->
      let vs = b.CF.formula_struc_explicit_inst @ b.CF.formula_struc_implicit_inst in
      let () = Global_var.stk_vars # push_list vs in

      (* ext_base should be the precondition *)
      let ctx,ext_base = (ctx,b.CF.formula_struc_base) in

      let nctx =
        if !Globals.max_renaming
        then (CF.transform_context (CF.normalize_es ext_base b.CF.formula_struc_pos false) ctx) (*apply normalize_es into ctx.es_state*)
        else (CF.transform_context (CF.normalize_clash_es ext_base b.CF.formula_struc_pos false) ctx) in

      let res =
        match b.CF.formula_struc_continuation with
        | None -> nctx
        | Some l -> helper nctx l
      in
      res
    | CF.EAssume {
        CF.formula_assume_vars = var_ref;
        CF.formula_assume_simpl = post_cond;
        CF.formula_assume_lbl = post_label;
        CF.formula_assume_ensures_type = etype0;
        CF.formula_assume_struc = post_struc
      } ->
      (* Follows check_specs_infer_a EAssume *)
      let ctx1 = CF.add_path_id ctx (None,0) 0 in
      let () = Typechecker.flow_store := [] in
      let ctx1 = CF.set_flow_in_context_override
          { CF.formula_flow_interval = !Exc.ETABLE_NFLOW.norm_flow_int; CF.formula_flow_link = None} ctx1 in
      let ctx1 = CF.add_path_id ctx1 (Some post_label,-1) (-1) in
      ctx1
    | _ -> ctx
  in

  let (cstruc_form, _, _) = Imminfer.infer_imm_ann_proc cstruc_form in
  let ctx = helper init_ctx cstruc_form in
  (* What is label  *)
  (* need to add initial esc_stack *)
  let init_esc = [((0,""),[])] in
  let lfe = [CF.mk_failesc_context ctx [] init_esc] in
  lfe

let check_pre_post lfe specs is_rec args call_args =
  let args = List.map (fun x -> param_to_typed_ident (param_to_iast_param x)) args in

  let ctx = CF.clear_entailment_history_failesc_list (fun x -> None) lfe in

  let farg_types, farg_names = List.split args in
  let farg_spec_vars = List.map2 (fun n t -> Cpure.SpecVar (t, n, VG.Unprimed)) farg_names farg_types in
  let actual_spec_vars = List.map2 (fun n t -> Cpure.SpecVar (t, n, VG.Unprimed)) call_args farg_types in

  let check_pre_post_orig specs ctx =
    let org_spec = if !Globals.change_flow then CF.change_spec_flow specs else specs in
    let lbl_ctx = Typechecker.store_label # get in
    let org_spec2 =
      if is_rec && !Globals.auto_number then match org_spec with
        | CF.EList b ->
          let l = CF.Label_Spec.filter_label_rec lbl_ctx b in
          CF.EList l
        | _ -> org_spec
      else org_spec in
    let stripped_spec = org_spec2 in
    let pre_free_vars = Gen.BList.difference_eq Cpure.eq_spec_var
        (Gen.BList.difference_eq Cpure.eq_spec_var (CF.struc_fv stripped_spec(*org_spec*))
           (CF.struc_post_fv stripped_spec(*org_spec*))) (farg_spec_vars@ (!SE.cprog.C.prog_logical_vars)) in

    let pre_free_vars = List.filter (fun v -> let t = Cpure.type_of_spec_var v in not(Globals.is_RelT t) && t != HpT) pre_free_vars in

    let ls_var = [(Cpure.mkLsVar VG.Unprimed)] in
    let lsmu_var = [(Cpure.mkLsmuVar VG.Unprimed)] in
    let waitlevel_var = [(Cpure.mkWaitlevelVar VG.Unprimed)] in
    let pre_free_vars = List.filter (fun v -> Cpure.name_of_spec_var v <> Globals.ls_name && Cpure.name_of_spec_var v <> Globals.lsmu_name && Cpure.name_of_spec_var v <> Globals.waitlevel_name) pre_free_vars in
    let pre_free_vars_fresh = Cpure.fresh_spec_vars pre_free_vars in
    let renamed_spec =
      if !Globals.max_renaming then (CF.rename_struc_bound_vars stripped_spec(*org_spec*))
      else (CF.rename_struc_clash_bound_vars stripped_spec(*org_spec*) (CF.formula_of_list_failesc_context ctx))
    in
    let st1 = List.combine pre_free_vars pre_free_vars_fresh in
    let fr_vars = farg_spec_vars @ (List.map Cpure.to_primed farg_spec_vars) in
    let to_vars = actual_spec_vars @ (List.map Cpure.to_primed actual_spec_vars) in

    let renamed_spec = CF.subst_struc st1 renamed_spec in
    let renamed_spec = CF.subst_struc_avoid_capture fr_vars to_vars renamed_spec in

    let renamed_spec =
      match None, None (* proc.proc_ho_arg, ha *) with
      | Some hv, Some ha ->
        let ht, hn = hv in
        let hsv = Cpure.SpecVar (ht, hn, Unprimed) in
        CF.subst_hvar_struc renamed_spec [(hsv, ha)]
      | _ -> renamed_spec
    in

    let st2 = List.map (fun v -> (Cpure.to_unprimed v, Cpure.to_primed v)) actual_spec_vars in
    let st_ls = List.map (fun v -> (Cpure.to_unprimed v, Cpure.to_primed v)) ls_var in
    let st_lsmu = List.map (fun v -> (Cpure.to_unprimed v, Cpure.to_primed v)) lsmu_var in
    let st_waitlevel = List.map (fun v -> (Cpure.to_unprimed v, Cpure.to_primed v)) waitlevel_var in
    let st3= st2@st_ls@st_lsmu@st_waitlevel in
    let pre2 = CF.subst_struc_pre st3 renamed_spec in
    (* Termination: Store unreachable state *)
    let _ =
      if is_rec then (* Only check termination of a recursive call *)
        if not (CF.isNonFalseListFailescCtx ctx) then
          let todo_unk = Term.add_unreachable_res ctx no_pos in ()
        else ()
      else ()
    in

    let rs, _ = Solver.heap_entail_struc_list_failesc_context_init 6 !SE.cprog false true lfe pre2 None None None no_pos None in
    rs
  in
  
  let res = if (CF.isFailListFailescCtx_new ctx) then
      let () = print_string "\nProgram state is unreachable." in
      ctx
    else
      check_pre_post_orig specs ctx
  in

  if (Globals.global_efa_exc () || (CF.isSuccessListFailescCtx_new res)) then
    let idf x = x in
    let err_kind_msg = if CF.is_infer_pre_must specs then "must" else "may" in
    let to_print = "Proving precondition in method failed:" ^ err_kind_msg in
    let res = CF.transform_list_failesc_context (idf,idf,
                                                 (fun es -> CF.Ctx{es with CF.es_formula =
                                                                             Norm.imm_norm_formula !SE.cprog es.CF.es_formula Solver.unfold_for_abs_merge no_pos;
                                                                           CF.es_final_error = CF.acc_error_msg es.CF.es_final_error to_print})) res in
    Some res
  else 
    let s,_,_ = CF.get_failure_list_failesc_context res in
    let () = print_string ("\nProving precondition in method failed:" ^ s) in
    None

(* Follows check_specs_infer and check_post
   Assuming that lfe is returned from check_exp
*)
(* Residue here is a list of partial_context.
   To return this residue, we might have to introduce a new type. But residue from check_entail_post should not be very useful.
*)
let check_entail_post lfe specs args =
  let args = List.map (fun x -> param_to_typed_ident (param_to_iast_param x)) args in

  let rec get_post_from_specs specs =
    match specs with
    | CF.EBase b ->
      let res =
        match b.CF.formula_struc_continuation with
        | None -> raise (Invalid_argument ("No post condition found in specs"))
        | Some l -> get_post_from_specs l
      in
      res
    | CF.EAssume b -> b
    | _ -> raise (Invalid_argument ("This form of specification is not yet supported"))
  in
  let post_struc_form = get_post_from_specs specs in
  let post_cond = post_struc_form.CF.formula_assume_simpl in
  let post_struc = post_struc_form.CF.formula_assume_struc in
  (* Follows check_specs_infer *)
  let idf x = x in
  let lfe = CF.transform_list_failesc_context (idf,idf, (fun es -> CF.Ctx (CF.clear_entailment_es_pure es))) lfe in
  let res_ctx = CF.list_failesc_to_partial lfe in
  let res_ctx = CF.change_ret_flow_partial_ctx res_ctx in
  if (CF.isFailListPartialCtx_new res_ctx) then false (* Failure state*)
  else 
    let (impl_vs,post_cond,post_struc) =
      if Typechecker.pre_ctr # get > 0 then
        let (impl_vs,new_post) =
          if !Globals.old_post_conv_impl then CF.lax_impl_of_post post_cond
          else ([],post_cond) in
        let new_post_struc, impl_struc =
          if !Globals.old_post_conv_impl then CF.lax_impl_of_struc_post post_struc
          else (post_struc,[]) in
        if (Gen.BList.list_setequal_eq Cpure.eq_spec_var_ident impl_struc impl_vs) then
          (impl_vs,new_post,new_post_struc)
        else (*temp fixing*)
          let sst = try List.combine impl_struc impl_vs
            with _ -> []
          in
          let new_post_struc = CF.subst_struc sst new_post_struc in
          (impl_vs,new_post,new_post_struc)
      else ([],post_cond,post_struc) in
    Global_var.stk_evars # push_list impl_vs;
    let pres, posts = CF.get_pre_post_vars_simp [] specs in
    let pre_vars = Cpure.remove_dups_svl (pres @ (List.map
                                                 (fun (t,id) -> Cpure.SpecVar (t,id,Unprimed)) args)) in
    let impl_vs, expl_vs = List.partition (fun v -> Cpure.mem_svl v (pre_vars@posts)) impl_vs in
    let res_ctx = Infer.add_impl_expl_vars_list_partial_context impl_vs expl_vs res_ctx in
    (* let () = if !Globals.dis_term_chk then () else *)
    (*     let log_vars = prog.Cast.prog_logical_vars in *)
    (*     let cl = List.filter (fun f -> *)
    (*         Gen.BList.overlap_eq Cpure.eq_spec_var (Cpure.fv f) log_vars) lp in *)
    (*     let () = Term.add_phase_constr_by_scc proc (List.map TP.simplify_raw cl) in () *)
    (* in *)
    let elim_unsat e =
      let already_unsat_flag = e.CF.es_unsat_flag in
      if already_unsat_flag then e
      else
        let (b,_,e) = Solver.elim_unsat_estate !SE.cprog e in
        e
    in
    let res_ctx = CF.map_list_partial_context res_ctx elim_unsat in
    (* Follows check_post *)
    let fn_state = CF.fresh_view_list_partial_context res_ctx in
    let f1 = CF.formula_is_eq_flow post_cond !error_flow_int in
    (* let rs, prf = *)
    (*   if not(Globals.global_efa_exc ()) && f1 then *)
    (*     begin *)
    (*       let flat_post = (CF.formula_subst_flow post_cond (CF.mkNormalFlow())) in *)
    (*       let (\*struc_post*\)_ = (CF.struc_formula_subst_flow post_struc (CF.mkNormalFlow())) in *)
    (*       (\*possibly change to flat post here as well??*\) *)
    (*       let (ans,prf) = Solver.heap_entail_list_partial_context_init !SE.cprog false fn_state flat_post None None None no_pos (Some post_struc_form.CF.formula_assume_lbl) in *)
    (*       let ans1 = if !mem_leak_detect then *)
    (*           Soutil.detect_mem_leak prog proc ans *)
    (*         else ans *)
    (*       in *)
    (*       (CF.invert_list_partial_context_outcome CF.invert_ctx_branch_must_fail CF.invert_fail_branch_must_fail ans1,prf) *)
    (*     end *)
    (*   else *)
    let rs, _ = Solver.heap_entail_struc_list_partial_context_init !SE.cprog false false fn_state post_struc None None None no_pos (Some post_struc_form.CF.formula_assume_lbl) in
    let is_succ = CF.isSuccessListPartialCtx_new rs in
    let is_reachable_succ = if not f1 then
        is_succ
      else
        (*if error post, check reachable *)
        is_succ && (CF.exist_reachable_states rs)
    in
    if ((* CF.isSuccessListPartialCtx_new rs *) is_reachable_succ) then
      true
    else
      let rs = if Globals.global_efa_exc () then
          List.fold_left (fun acc (fs, brs) ->
              let ex_fs, rest = List.fold_left (fun (acc_fs, acc_rest) ((lbl,c, oft) as br) ->
                  match oft with
                  | Some ft -> (acc_fs@[(lbl, ft)], acc_rest)
                  | None -> (acc_fs, acc_rest@[br])
                ) ([],[]) brs in
              acc@[(fs@ex_fs, rest)]
            ) [] rs
        else rs in
      let s,fk,ets= CF.get_failure_list_partial_context rs in
      let failure_str = if List.exists (fun et -> et = Globals.Mem 1) ets then
          "memory leak failure" else
          "Post condition cannot be derived"
      in
      let () = print_string ("\n"^failure_str ^ ":\n" ^s^"\n") in
      false

(* Follows check_exp Cond case *)
let disj_of_ctx ctx1 ctx2 =
  CF.list_failesc_context_or (Cprinter.string_of_esc_stack) ctx1 ctx2

(* Follows check_exp Cond case *)
let add_cond_to_ctx ctx ident b =
  let pure_cond = (Cpure.BForm ((Cpure.mkBVar ident VG.Primed no_pos, None), None)) in
  let cond = 
    if b then
      Mcpure.mix_of_pure pure_cond
    else
      Mcpure.mix_of_pure (Cpure.mkNot pure_cond None no_pos) in
  let ctx = Solver.combine_list_failesc_context_and_unsat_now !SE.cprog ctx cond in
  CF.add_path_id_ctx_failesc_list ctx (None, -1) (if b then 1 else 2)

(* Follows check_exp Var case *)
let upd_result_with_var ctx t ident =
  let t = typ_to_globals_typ t in
  let tmp = CF.formula_of_mix_formula (Mcpure.mix_of_pure (Cpure.mkEqVar (Cpure.mkRes t) (Cpure.SpecVar (t, ident, Primed)) no_pos)) no_pos in
  CF.normalize_max_renaming_list_failesc_context tmp no_pos true ctx

(* Follows check_exp IConst case *)
let upd_result_with_int ctx i =
  let c_e = Cpure.IConst (i, no_pos) in
  let res_v = Cpure.Var (Cpure.mkRes C.int_type, no_pos) in
  let c = Cpure.mkEqExp res_v c_e no_pos in
  let c =
    if !Globals.infer_lvar_slicing then
      Cpure.set_il_formula c (Some (false, Globals.fresh_int(), [res_v]))
    else c
  in
  let f = CF.formula_of_mix_formula (Mcpure.mix_of_pure c) no_pos in
  CF.normalize_max_renaming_list_failesc_context f no_pos true ctx

(* Follows check_exp BConst case *)
let upd_result_with_bool ctx b =
  let res_v = Cpure.mkRes C.bool_type in
  let tmp = Cpure.BForm ((Cpure.BVar (res_v, no_pos), None), None) in
  let tmp =
    if b then tmp
    else
      Cpure.Not (tmp, None, no_pos) in
  let f = CF.formula_of_pure_N tmp no_pos in
  CF.normalize_max_renaming_list_failesc_context f no_pos true ctx

(* Follows check_exp Assign case *)
let add_assign_to_ctx ctx t ident =
  let t = typ_to_globals_typ t in
  let idf x = x in
  let fct c1 =
    let res = if (CF.subsume_flow_f !norm_flow_int (CF.flow_formula_of_formula c1.CF.es_formula)) then
        let vsv = Cpure.SpecVar (t, ident, Primed) in (* rhs must be non-void *)
        let tmp_vsv = Cpure.fresh_spec_var vsv in
        let compose_es = CF.subst [(vsv, tmp_vsv); ((Cpure.mkRes t), vsv)] c1.CF.es_formula in
        let compose_ctx = (CF.Ctx ({c1 with CF.es_formula = compose_es})) in
        compose_ctx
      else (CF.Ctx c1) in
    res
  in
  let res = CF.transform_list_failesc_context (idf,idf,fct) ctx in
  res

let bind_data_to_names ctx t ident lvars read_only =
  let idf x = x in
  let t = typ_to_globals_typ t in
  let lvars = List.map (fun (t, i) -> (typ_to_globals_typ t, i)) lvars in

  let lsv = List.map (fun (t,i) -> Cpure.SpecVar(t,i,Unprimed)) lvars in
  let field_types, vs = List.split lvars in
  let v_prim = Cpure.SpecVar (t, ident, Primed) in
  let vs_prim = List.map2 (fun v -> fun t -> Cpure.SpecVar (t, v, Primed)) vs field_types in
  let p = Cpure.fresh_spec_var v_prim in
  let link_pv = CF.formula_of_pure_N
      (Cpure.mkAnd (Cpure.mkEqVar v_prim p no_pos) (Cpure.BForm ((Cpure.mkNeq (Cpure.Var (p, no_pos)) (Cpure.Null no_pos) no_pos, None), None)) no_pos) no_pos in

  let tmp_ctx =
    if !Globals.large_bind then
      CF.normalize_max_renaming_list_failesc_context link_pv no_pos false ctx
    else ctx in

  let () = CF.must_consistent_list_failesc_context "bind 1" ctx  in

  let unfolded = tmp_ctx in
  let unfolded =  CF.transform_list_failesc_context (idf,idf, (fun es -> CF.Ctx (CF.clear_entailment_es_pure es))) unfolded in

  let () = CF.must_consistent_list_failesc_context "bind 2" unfolded  in

  let unfolded =
    let idf = (fun c -> c) in
    CF.transform_list_failesc_context (idf,idf,
                                       (fun es -> CF.Ctx{es with CF.es_formula = Norm.imm_norm_formula !SE.cprog es.CF.es_formula Solver.unfold_for_abs_merge no_pos;})) unfolded
  in
  let c = Globals.string_of_typ t in
  let fresh_perm_exp,perm_vars =
    (match !Globals.perm with
     | Bperm ->
       let c_name = Cpure.fresh_old_name "cbperm" in
       let t_name = Cpure.fresh_old_name "tbperm" in
       let a_name = Cpure.fresh_old_name "abperm" in
       let c_var = Cpure.SpecVar (Globals.Int,c_name, VG.Unprimed) in
       let t_var = Cpure.SpecVar (Globals.Int,t_name, VG.Unprimed) in
       let a_var = Cpure.SpecVar (Globals.Int,a_name, VG.Unprimed) in
       Cpure.Bptriple ((c_var,t_var,a_var), no_pos), [c_var;t_var;a_var]
     | _ ->
       let fresh_perm_name = Cpure.fresh_old_name "f" in
       let perm_t = Perm.cperm_typ () in
       let perm_var = Cpure.SpecVar (perm_t,fresh_perm_name, VG.Unprimed) in (*LDK TO CHECK*)
       Cpure.Var (perm_var,no_pos),[perm_var])
  in

  let bind_ptr = if !Globals.large_bind then p else v_prim in
  let vdatanode = CF.DataNode ({
      CF.h_formula_data_node = bind_ptr;
      CF.h_formula_data_name = c;
      CF.h_formula_data_derv = false; (*TO CHECK: assume false*)
      CF.h_formula_data_split = SPLIT0; (*TO CHECK: assume false*)
      CF.h_formula_data_imm = if read_only then Cpure.ConstAnn(Lend) else Cpure.ConstAnn(Mutable);
      CF.h_formula_data_param_imm = [];
      CF.h_formula_data_perm = if (Perm.allow_perm ()) then Some fresh_perm_exp else None; (*LDK: belong to HIP, deal later ???*)
      CF.h_formula_data_origins = []; (*deal later ???*)
      CF.h_formula_data_original = true; (*deal later ???*)
      CF.h_formula_data_arguments = (*t_var :: ext_var ::*) vs_prim;
      CF.h_formula_data_holes = []; (* An Hoa : Don't know what to do *)
      CF.h_formula_data_label = None;
      CF.h_formula_data_remaining_branches = None;
      CF.h_formula_data_pruning_conditions = [];
      CF.h_formula_data_pos = no_pos}) in
  let vheap = CF.formula_of_heap vdatanode no_pos in
  let vheap =
    if Globals.infer_const_obj # is_ana_ni then CF.mk_bind_ptr_f bind_ptr else vheap in

  let vheap =
    if (Perm.allow_perm ()) then
      (*there exists fresh_perm_exp statisfy ... *)
      if (read_only)
      then
        let read_f = Perm.mkPermInv () fresh_perm_exp in
        CF.mkBase vdatanode (Mcpure.memoise_add_pure_N (Mcpure.mkMTrue no_pos) read_f) CvpermUtils.empty_vperm_sets CF.TypeTrue (CF.mkTrueFlow ()) [] no_pos
      else
        let write_f = Perm.mkPermWrite () fresh_perm_exp in
        CF.mkBase vdatanode (Mcpure.memoise_add_pure_N (Mcpure.mkMTrue no_pos) write_f) CvpermUtils.empty_vperm_sets CF.TypeTrue (CF.mkTrueFlow ()) [] no_pos
    else
      vheap
  in

  let vheap = Immutable.normalize_field_ann_formula vheap in
  let vheap = Cvutil.prune_preds !SE.cprog false vheap in

  let struc_vheap = CF.EBase {
      CF.formula_struc_explicit_inst = [];
      CF.formula_struc_implicit_inst = (if (Perm.allow_perm ()) then perm_vars else [])@vs_prim;  (*need to instantiate f*)
      CF.formula_struc_exists = [] ;
      CF.formula_struc_base = vheap;
      CF.formula_struc_is_requires = false;
      CF.formula_struc_continuation = None;
      CF.formula_struc_pos = no_pos} in

  if (Gen.is_empty unfolded) then
    unfolded
  else
    let () = Globals.consume_all := true in
    (* let () = print_string ("\nBefore : " ^ (Cprinter.string_of_list_failesc_context unfolded)) in *)
    (* let () = print_string ("\nStruc_vheap : " ^ (Cprinter.string_of_struc_formula struc_vheap)) in *)
    let rs_prim, _ = Solver.heap_entail_struc_list_failesc_context_init 5 !SE.cprog false true unfolded struc_vheap None None None no_pos None in
    (* let () = print_string ("\nAfter : " ^ (Cprinter.string_of_list_failesc_context rs_prim)) in *)
    let () = Globals.consume_all := false in
    let () = CF.must_consistent_list_failesc_context "bind 3" rs_prim  in

    let rs = CF.clear_entailment_history_failesc_list (fun x -> None) rs_prim in
    let () = CF.must_consistent_list_failesc_context "bind 4" rs  in

    if (CF.isSuccessListFailescCtx_new unfolded) && (not(CF.isSuccessListFailescCtx_new rs))then
      begin
        if Globals.is_en_efa_exc () && (Globals.global_efa_exc ()) then

          let to_print = ("bind 3: node " ^ (Cprinter.string_of_formula vheap (*vdatanode*)) ^
                          " cannot be derived from context") in
          CF.transform_list_failesc_context (idf,idf,
                                             (fun es -> CF.Ctx{es with CF.es_final_error = CF.acc_error_msg es.CF.es_final_error to_print}))
            rs
        else
          let s =  ("\n("^(Cprinter.string_of_label_list_failesc_context rs)^") ")^
                   ("bind: node " ^ (Cprinter.string_of_formula vheap (* vdatanode *)) ^
                    " cannot be derived from context\n") ^
                   ("(Cause of Bind Failure)") ^
                   (Cprinter.string_of_failure_list_failesc_context rs ) in
          raise (Error.Ppf ({
              Error.error_loc = no_pos;
              Error.error_text = (s (* ^ "\n" ^ (pr hprel_assumptions) *))
            }, (*Failure_Must*) 1, 0))
      end
    else
      rs

(* Testing API *)
let%expect_test "Entailment checking" =
  
  let () = init () in

  let entail_1 () =
    (* true |- true *)
    let true_f = true_f in
    let empty_heap_f = empty_heap_f in
    let ante_f = ante_f empty_heap_f true_f in
    let conseq_f = conseq_f empty_heap_f true_f in
    (* let () = print_string (ante_printer ante_f) in *)
    (* let () = print_string (conseq_printer conseq_f) in *)
    let _ = entail ante_f conseq_f in
    ()
  in

  let entail_2 () =
    (* x |-> 1 |- x |-> 1 *)
    let ante_f = ante_f (points_to_int_f "x" 1)
        (true_f) in
    let conseq_f = conseq_f (points_to_int_f "x" 1)
        (true_f) in
    let _ = entail ante_f conseq_f in
    ()
  in

  let entail_3 () =
    (* x > 0 /\ x' = x + 1 |- x' > 1 *)
    let ante_f = ante_f empty_heap_f
        (and_f
           (gt_pure_f
              (var_pure_exp "x")
              (int_pure_exp 0))
           (eq_pure_f
              (var_pure_exp "x'")
              (add_pure_exp
                 (var_pure_exp "x")
                 (int_pure_exp 1)))) in
    let conseq_f = conseq_f empty_heap_f
        (gt_pure_f
           (var_pure_exp "x'")
           (int_pure_exp 1)) in
    let _ = entail ante_f conseq_f in
    ()
  in

  let entail_4 () =
    (* x::node<0,null> |- x != null *)
    (* let () = data_decl_cons "node" [(Int, "val"); (Named("node"), "next")] in *)
    let () = data_decl "data node { int val ; node next }." in
    let ante_f = ante_f 
        (points_to_f "x" "node" [(int_pure_exp 0); (null_pure_exp)]) true_f in
    let conseq_f = conseq_f empty_heap_f
        (not_f (eq_pure_f
                  (var_pure_exp "x")
                  null_pure_exp)) in
    let _ = entail ante_f conseq_f in
    ()
  in
    
  let entail_5 () =  
    (* x=null |- x::ll<0> *)
    let ll = "pred ll<n> == self = null & n = 0
or self::node<next = r> * r::ll<n - 1>
inv n >= 0." in
    let () = predicate_decl ll in
    let ante_f = ante_f empty_heap_f
        (eq_pure_f
           (var_pure_exp "x")
           null_pure_exp) in
    let conseq_f = conseq_f
        (points_to_f "x" "ll" [(int_pure_exp 0)])
        true_f in
    let _ = entail ante_f conseq_f in
    ()
  in

  let entail_6 () =
    (* x::ll<n> |- x::ll<n+1> *)
    let ante_f = ante_f
        (points_to_f "x" "ll" [(var_pure_exp "n")])
        true_f in
    let conseq_f = conseq_f
        (points_to_f "x" "ll" [(add_pure_exp
                                  (var_pure_exp "n")
                                  (int_pure_exp 1)
                               )])
        true_f in
    let _ = entail ante_f conseq_f in
    ()
  in

  let entail_7 () =
    (* x |-> 1 * y |-> 2 |- x -> 1 *) (* maybe need to find a better test case to test the star *)
    let h1 = points_to_int_f "x" 1 in
    let h2 = points_to_int_f "y" 2 in 
    let astar = sep_conj_f h1 h2 in
    let ante_f = ante_f astar true_f in
    let conseq_f = conseq_f (points_to_int_f "x" 1) true_f in
    let _ = entail ante_f conseq_f in
    ()
  in

  let entail_8 () =
    let sort = "pred sortl<n, mi> == self = null & n = 0
or self::node<mi, r> * r::sortl<n - 1, k> & mi <= k
inv n >= 0." in
    let () = predicate_decl sort in
    let lemma = "lemma self::sortl<n, mi> -> self::ll<n>." in
    let () = lemma_decl lemma in
    let ante_f = ante_f
        (points_to_f "x" "sortl" [(var_pure_exp "a");
                                  (var_pure_exp "b")])
        true_f in
    let conseq_f = conseq_f
        (points_to_f "x" "ll" [(var_pure_exp "a")])
        true_f in
    let _ = entail ante_f conseq_f in
    ()
  in

  let entail_9 () =
    (* x:: node(_, r1) * r1:: node(_, null) |-> x:: ll<c> *)
    let h1 = points_to_f "x" "node" [(var_pure_exp "_"); var_pure_exp "r1"] in
    let h2 = points_to_f "r1" "node" [(var_pure_exp "_"); (null_pure_exp)] in 
    let astar = sep_conj_f h1 h2 in
    let ante_f = ante_f astar true_f in
    let conseq_f = conseq_f (points_to_f "x" "ll" [(var_pure_exp "c")]) true_f in
    let _ = entail ante_f conseq_f in
    ()
  in

  let spec_decl_1 () =
    let cstruc_form = spec_decl "foo" "requires true ensures true;" [] in
    let lfe = init_ctx cstruc_form [] in
    print_string (Cprinter.string_of_list_failesc_context lfe)
  in

  let spec_decl_2 () =
    let cstruc_form = spec_decl "foo" "requires x::ll<n> & n > 0 ensures x::ll<1> * res::ll<n-1>;" [] in
    let lfe = init_ctx cstruc_form [] in
    print_string (Cprinter.string_of_list_failesc_context lfe)
  in
  
  let spec_decl_3 () =
    let cstruc_form = spec_decl "foo" "requires x::ll<m> ensures x::ll<m>;" [] in
    let lfe = init_ctx cstruc_form [] in
    print_string (Cprinter.string_of_list_failesc_context lfe);
    print_string (string_of_bool (check_entail_post lfe cstruc_form []));
  in

  let spec_decl_4 () = 
    let cstruc_form = spec_decl "foo" "requires true
    ensures 
        case {
            i > 0 -> [] i' = i + 1;
            i <= 0 -> [] i' = i;
        };" [{param_type = Int; param_name = "i"; param_mod = RefMod;}] in
    let lfe = init_ctx cstruc_form [{param_type = Int; param_name = "i"; param_mod = RefMod;}] in
    print_string (Cprinter.string_of_struc_formula cstruc_form);
    print_string (Cprinter.string_of_list_failesc_context lfe)
  in

  let verify_1 () =
    (* requires true
       ensures res = 0;

       int foo() {
           return 0;
       }
    *)
    let cstruc_form = spec_decl "foo" "requires true ensures res = 0;" [] in
    let lfe = init_ctx cstruc_form [] in
    let lfe = upd_result_with_int lfe 0 in

    print_string ("\n" ^ (string_of_bool (check_entail_post lfe cstruc_form [])))
  in
    
  let verify_2 () =
    (* 
       int foo()
       requires true
       ensures res 1;
       {
       if (true)
       return 1;
       else
       return 2;
       }

       {(boolean v_bool_5_2020;
       (v_bool_5_2020 = true;
       if (v_bool_5_2020) [LABEL! 144,0: (int v_int_6_2018;
       (v_int_6_2018 = 1;
       ret# v_int_6_2018))]
       else [LABEL! 144,1: (int v_int_8_2019;
       (v_int_8_2019 = 2;
       ret# v_int_8_2019))]
       ))}
    *)
    let cstruc_form = spec_decl "foo" "requires true ensures res = 1;" [] in
    let lfe = init_ctx cstruc_form [] in
    (* VarDecl : do nothing *)
    (* Assignment : check rhs exp  *)
    let lfe = upd_result_with_bool lfe true in
    (* Assignment : update res *)
    let lfe = add_assign_to_ctx lfe Bool "v_bool_5_2020" in

    (* Cond : then branch *)
    let then_lfe = add_cond_to_ctx lfe "v_bool_5_2020" true in
    let then_lfe = upd_result_with_int then_lfe 1 in
    let then_lfe = add_assign_to_ctx then_lfe Int "v_int_6_2018" in
    let then_lfe = upd_result_with_var then_lfe Int "v_int_6_2018" in
    (* Cond : else branch *)
    let else_lfe = add_cond_to_ctx lfe "v_bool_5_2020" false in
    let else_lfe = upd_result_with_int else_lfe 2 in
    let else_lfe = add_assign_to_ctx else_lfe Int "v_int_8_2019" in
    let else_lfe = upd_result_with_var else_lfe Int "v_int_8_2019" in

    let lfe = disj_of_ctx then_lfe else_lfe in
    print_string ("\n" ^ (string_of_bool (check_entail_post lfe cstruc_form [])))
  in

  let verify_3 () =
    let add_param_list = [{param_type = Int; param_name = "a"; param_mod = RefMod;};
                          {param_type = Int; param_name = "b"; param_mod = RefMod;}] in
    let add_specs = spec_decl "add__" "requires true ensures res = a + b;"
        add_param_list in
    (* 
       int foo(int i)
         requires true
         ensures res=i+1;
       {
         return i + 1;
       }

       {(int v_int_22_2043;
       (v_int_22_2043 = {((int v_int_22_2042;
       v_int_22_2042 = 1);
       add___$int~int(i,v_int_22_2042))};
       ret# v_int_22_2043))}    
    *)
    let cstruc_form = spec_decl "foo" "requires true ensures res=i + 1;"
        [{param_type = Int; param_name = "i"; param_mod = RefMod;}] in
    let lfe = init_ctx cstruc_form 
        [{param_type = Int; param_name = "i"; param_mod = RefMod;}] in
    (* VarDecl : do nothing *)
    (* Assignment : check rhs exp *)
    (*   VarDecl : do nothing *)
    (*   Assignment : check rhs exp *)
    let lfe = upd_result_with_int lfe 1 in
    (*   Assignment : assign *)
    let lfe = add_assign_to_ctx lfe Int "v_int_22_2042" in
    (*   Call : check pre cond *)
    let lfe = check_pre_post lfe add_specs false add_param_list ["i"; "v_int_22_2042"] in
    (* Assignment : assign *)
    let lfe = add_assign_to_ctx (Gen.unsome lfe) Int "v_int_22_2043" in
    (* ret : update res *)
    let lfe = upd_result_with_var lfe Int "v_int_22_2043" in

    print_string ("\n" ^ (string_of_bool (check_entail_post lfe cstruc_form
                                            [{param_type = Int; param_name = "i"; param_mod = RefMod;}]))) in

  let verify_4 () =
    let add_param_list = [{param_type = Int; param_name = "a"; param_mod = RefMod;};
                          {param_type = Int; param_name = "b"; param_mod = RefMod;}] in
    let add_specs = spec_decl "add__" "requires true ensures res = a + b;"
        add_param_list in

    let is_null_param_list = [{param_type = Named("node"); param_name = "a"; param_mod = CopyMod;}] in
    let is_null_specs = spec_decl "is_null__" "case { a=null -> requires true ensures res ; a!=null -> requires true ensures !res;}" is_null_param_list in

    let count_param_list = [{param_type = Named("node"); param_name = "x"; param_mod = CopyMod;}] in
    let cstruc_form = spec_decl "count" "  requires x::ll<n> ensures x::ll<n> & res=n;" count_param_list in
    let lfe = init_ctx cstruc_form count_param_list in
    (* 
     {(boolean v_bool_46_2101;
     (v_bool_46_2101 = {is_null___$node(x)};
     if (v_bool_46_2101) [LABEL! 150,0: (int v_int_47_2092;
     (v_int_47_2092 = 0;
     ret# v_int_47_2092))]
     else [LABEL! 150,1: (int v_int_49_2100;
     (v_int_49_2100 = {((int v_int_49_2099;
     (v_int_49_2099 = 1;
     (int v_int_49_2098;
     v_int_49_2098 = {((node v_node_49_2096;
     v_node_49_2096 = bind x to (val_49_2093,next_49_2094) [read] in 
     next_49_2094);
     count$node(v_node_49_2096) rec)})));
     add___$int~int(v_int_49_2099,v_int_49_2098))};
     ret# v_int_49_2100))]
     ))}
 *)
    let lfe = check_pre_post lfe is_null_specs false is_null_param_list ["x"] in
    let lfe = add_assign_to_ctx (Gen.unsome lfe) Bool "v_bool_46_2101" in
    
    let then_lfe = add_cond_to_ctx lfe "v_bool_46_2101" true in
    let then_lfe = upd_result_with_int then_lfe 0 in
    let then_lfe = add_assign_to_ctx then_lfe Int "v_int_47_2092" in
    let then_lfe = upd_result_with_var then_lfe Int "v_int_47_2092" in

    let else_lfe = add_cond_to_ctx lfe "v_bool_46_2101" false in
    let else_lfe = upd_result_with_int else_lfe 1 in
    let else_lfe = add_assign_to_ctx else_lfe Int "v_int_49_2099" in
    let else_lfe = bind_data_to_names else_lfe (Named("node")) "x" [(Int, "val_49_2093"); (Named("node"), "next_49_2094")] true in
    let else_lfe = upd_result_with_var else_lfe (Named("node")) "next_49_2094" in
    let else_lfe = add_assign_to_ctx else_lfe (Named("node")) "v_node_49_2096" in
    let else_lfe = check_pre_post else_lfe cstruc_form true count_param_list ["v_node_49_2096"] in
    let else_lfe = add_assign_to_ctx (Gen.unsome else_lfe) Int "v_int_49_2098" in
    let else_lfe = check_pre_post else_lfe add_specs false add_param_list ["v_int_49_2099"; "v_int_49_2098"] in
    let else_lfe = add_assign_to_ctx (Gen.unsome else_lfe) Int "v_int_49_2100" in
    let else_lfe = upd_result_with_var else_lfe Int "v_int_49_2100" in

    let lfe = disj_of_ctx then_lfe else_lfe in
    (* let () = print_string ("\n" ^ (Cprinter.string_of_list_failesc_context lfe)) in *)
    print_string ("\n" ^ (string_of_bool (check_entail_post lfe cstruc_form count_param_list)))
  in

  let verify_5 () =
    let is_null_param_list = [{param_type = Named("node"); param_name = "a"; param_mod = CopyMod;}] in
    let is_null_specs = spec_decl "is_null__" "case { a=null -> requires true ensures res ; a!=null -> requires true ensures !res;}" is_null_param_list in
    (* 
      {(boolean v_bool_36_2099;
        (v_bool_36_2099 = {((node v_node_36_2091;
        v_node_36_2091 = bind x to (val_36_2087,next_36_2088) [read] in
        next_36_2088);
        is_null___$node(v_node_36_2091))};
        if (v_bool_36_2099) [LABEL! 147,0: bind x to (val_37_2092,next_37_2093) [write] in
        next_37_2093 = y]
        else [LABEL! 147,1: {((node v_node_39_2098;
        v_node_39_2098 = bind x to (val_39_2094,next_39_2095) [read] in
        next_39_2095);
        append2$node~node(v_node_39_2098,y) rec)}]
        ))}
 *)
    let param_list = [{param_type = Named("node"); param_name = "x"; param_mod = RefMod;}; {param_type = Named("node"); param_name = "y"; param_mod = RefMod;}] in
    let cstruc_form = spec_decl "append" "requires x::ll<n1> * y::ll<n2> & x!=null 
  ensures x::ll<n1+n2>;" param_list in
    let lfe = init_ctx cstruc_form param_list in

    let lfe = bind_data_to_names lfe (Named("node")) "x" [(Int, "val_36_2087"); (Named("node"), "next_36_2088")] true in
    let lfe = upd_result_with_var lfe (Named("node")) "next_36_2088" in
    let lfe = add_assign_to_ctx lfe (Named("node")) "v_node_36_2091" in
    let lfe = check_pre_post lfe is_null_specs false is_null_param_list ["v_node_36_2091"] in
    let lfe = add_assign_to_ctx (Gen.unsome lfe) Bool "v_bool_36_2099" in

    let then_lfe = add_cond_to_ctx lfe "v_bool_36_2099" true in
    let then_lfe = bind_data_to_names then_lfe (Named("node")) "x" [(Int, "val_37_2092"); (Named("node"), "next_37_2093")] false in
    let then_lfe = upd_result_with_var then_lfe (Named("node")) "y" in
    let then_lfe = add_assign_to_ctx then_lfe (Named("node")) "next_37_2093" in

    let else_lfe = add_cond_to_ctx lfe "v_bool_36_2099" false in
    let else_lfe = bind_data_to_names else_lfe (Named("node")) "x" [(Int, "val_39_2094"); (Named("node"), "next_39_2095")] true in
    let else_lfe = upd_result_with_var else_lfe (Named("node")) "next_39_2095" in
    let else_lfe = add_assign_to_ctx else_lfe (Named("node")) "v_node_39_2098" in
    let else_lfe = check_pre_post else_lfe cstruc_form true param_list ["v_node_39_2098"; "y"] in
    let else_lfe = Gen.unsome else_lfe in

    let lfe = disj_of_ctx then_lfe else_lfe in
    let () = print_string ("\n MARKER : " ^ (Cprinter.string_of_list_failesc_context lfe)) in
    print_string ("\n" ^ (string_of_bool (check_entail_post lfe cstruc_form param_list)))
  in    

  print_string "\nEntailment";
  entail_1 ();
  entail_2 ();
  entail_3 ();
  entail_4 ();
  entail_5 ();
  entail_6 ();
  entail_7 ();
  entail_8 ();
  entail_9 ();
  print_string "\nVerification";
  verify_1 ();
  verify_2 ();
  verify_3 ();
  verify_4 ();
  [%expect]

